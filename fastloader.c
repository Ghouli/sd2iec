/* sd2iec - SD/MMC to Commodore serial bus interface/controller
   Copyright (C) 2007-2009  Ingo Korb <ingo@akana.de>
   Final Cartridge III, DreamLoad fastloader support:
   Copyright (C) 2008  Thomas Giesel <skoe@directbox.com>
   Fast Serial protocol and Burst Command Instruction Set:
   Copyright (C) 2011  Robert Willie <hydradix@yahoo.com>

   Inspiration and low-level SD/MMC access based on code from MMC2IEC
     by Lars Pontoppidan et al., see sdcard.c|h and config.h.

   FAT filesystem access based on code from ChaN and Jim Brain, see ff.c|h.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; version 2 of the License only.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA


   fastloader.c: High level handling of fastloader protocols

*/

#include <avr/io.h>
#include <avr/interrupt.h>
#include <util/delay.h>
#include <util/atomic.h>
#include <string.h>
#include "config.h"
#include "buffers.h"
#include "doscmd.h"
#include "errormsg.h"
#include "fileops.h"
#include "d64ops.h"
#include "parser.h"
#include "wrapops.h"
#include "iec-ll.h"
#include "fastloader-ll.h"
#include "fastloader.h"
#include "led.h"
#include "timer.h"
#include "diskchange.h"

uint8_t detected_loader;

/* track to load, used as a kind of jobcode */
volatile uint8_t fl_track;

/* sector to load, used as a kind of jobcode */
volatile uint8_t fl_sector;

#ifdef CONFIG_LOADER_TURBODISK
void load_turbodisk(void) {
  uint8_t i,len,firstsector;
  buffer_t *buf;

  set_clock(0);

  /* Copy filename to beginning of buffer */
  // FIXME: Das ist daemlich. fat_open um Zeiger auf Dateinamen erweitern?
  len = command_buffer[9];
  for (i=0;i<len;i++)
    command_buffer[i] = command_buffer[10+i];

  command_buffer[len] = 0;
  command_length = len;

  // FIXME: Rueckgabewert mit Status, evtl. direkt fat_open_read nehmen
  file_open(0);
  buf = find_buffer(0);
  if (!buf) {
    ATOMIC_BLOCK( ATOMIC_FORCEON ) {
      turbodisk_byte(0xff);
      set_clock(1);
      set_data(1);
    }
    return;
  }

  firstsector = 1;

  ATOMIC_BLOCK( ATOMIC_FORCEON ) {
    while (1) {
      /* Send the status byte */
      if (buf->sendeoi) {
        turbodisk_byte(0);
      } else {
        turbodisk_byte(1);
      }

      if (firstsector) {
        /* Load address is transferred seperately */
        i = buf->position;
        turbodisk_byte(buf->data[i++]);
        turbodisk_byte(buf->data[i++]);
        buf->position  = i;
        firstsector    = 0;
      }

      if (buf->sendeoi) {
        /* Last sector is sent byte-by-byte */
        turbodisk_byte(buf->lastused - buf->position + 2);

        i = buf->position;
        do {
          turbodisk_byte(buf->data[i]);
        } while (i++ < buf->lastused);

        break;
      } else {
        /* Send the complete 254 byte buffer */
        turbodisk_buffer(buf->data + buf->position, 254);
        if (buf->refill(buf)) {
          /* Some error, abort */
          turbodisk_byte(0xff);
          break;
        }
      }
    }
  }
  buf->cleanup(buf);
  free_buffer(buf);

  set_clock(1);
}
#endif

#ifdef CONFIG_LOADER_FC3
void load_fc3(uint8_t freezed) {
  buffer_t *buf;
  unsigned char step,pos;
  unsigned char sector_counter = 0;
  unsigned char block[4];

  buf = find_buffer(0);

  if (!buf) {
    /* error, abort and pull down CLOCK and DATA to inform the host */
    IEC_OUT |= IEC_OBIT_CLOCK | IEC_OBIT_DATA;
    return;
  }

  /* to make sure the C64 VIC DMA is off */
  _delay_ms(20);

  for(;;) {
    clk_data_handshake();

    /* Starting buffer position */
    /* Rewinds by 2 bytes for the first sector and normal loader */
    pos = 2;

    /* construct first 4-byte block */
    /* The 0x07 in the first byte is never used */
    block[1] = sector_counter++;
    if (buf->sendeoi) {
      /* Last sector, send number of bytes */
      block[2] = buf->lastused;
    } else {
      /* Send 0 for full sector */
      block[2] = 0;
    }
    /* First data byte */
    block[3] = buf->data[pos++];

    if (!freezed)
      _delay_ms(0.19);
    fastloader_fc3_send_block(block);

    /* send the next 64 4-byte-blocks, the last 3 bytes are read behind
       the buffer, good that we don't have an MMU ;) */
    for (step = 0; step < 64; step++) {
      if (!IEC_ATN)
        goto cleanup;

      if (freezed)
        clk_data_handshake();
      else
        _delay_ms(0.19);
      fastloader_fc3_send_block(buf->data + pos);
      pos += 4;
    }

    if (buf->sendeoi) {
      /* pull down DATA to inform the host about the last sector */
      set_data(0);
      break;
    } else {
      if (buf->refill(buf)) {
        /* error, abort and pull down CLOCK and DATA to inform the host */
        IEC_OUT |= IEC_OBIT_CLOCK | IEC_OBIT_DATA;
        break;
      }
    }
  }

 cleanup:
  buf->cleanup(buf);

  free_buffer(buf);
}

void save_fc3(void) {
  unsigned char n;
  unsigned char size;
  unsigned char eof = 0;
  buffer_t *buf;

  buf = find_buffer(1);
  /* Check if this is a writable file */
  if (!buf || !buf->write)
      return;

  /* to make sure the host pulled DATA low and is ready */
  _delay_ms(5);

  do {
    set_data(0);

    size = fc3_get_byte();

    if (size == 0) {
      /* a full block is coming, no EOF */
      size = 254;
    }
    else {
      /* this will be the last block */
      size--;
      eof = 1;
    }

    for (n = 0; n < size; n++) {
      /* Flush buffer if full */
      if (buf->mustflush) {
        buf->refill(buf);
        /* the FC3 just ignores things like "disk full", so do we */
      }

      buf->data[buf->position] = fc3_get_byte();

      if (buf->lastused < buf->position)
        buf->lastused = buf->position;
      buf->position++;

      /* Mark buffer for flushing if position wrapped */
      if (buf->position == 0)
        buf->mustflush = 1;
    }
  }
  while (!eof);

  buf->cleanup(buf);
  free_buffer(buf);
}
#endif


uint8_t b_out_burstload(uint8_t flags, uint8_t val) {
	ATOMIC_BLOCK( ATOMIC_FORCEON ) {
	  val = fserial_out(flags, val);
	}
	return val;
}

int16_t b_in_burstload(uint8_t flags) {
	int16_t val;
	ATOMIC_BLOCK( ATOMIC_FORCEON ) {
	  val = fserial_in(flags);
	}
	return val;
}

void s_out_burstload(uint8_t n_sec) {
  /* send status byte and sector(s) of data from fl_track $8371 */
  /* command_buffer[2] contains special flags */
  /* fl_sector is the first sector, n_sec is the number of sectors */
  /* bcis_interleave is used if n_sec > 1 */
  uint8_t flags;     /* fast-serial desired CLOCK state */
  uint8_t stop = 0;  /* ok, not found ATN */
  uint16_t size, i;  /* sector size, index */
  buffer_t *buf;

 ATOMIC_BLOCK( ATOMIC_FORCEON ) {
	// release everything
	IEC_OUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);

	/* there is an option to ignore errors,
	but the 1571 will disregard that and send 1 status byte
	if the error is 'disk change' (0xb)
	We use that if we need to abort ... */
  
  if (bcis_status == 0xb) 
	  set_error(ERROR_DISK_ID_MISMATCH); /* disk change detected */

  switch(partition[current_part].imagetype) {
  case D64_TYPE_D41:
  case D64_TYPE_D71:
	  size = 256;
	  break;
  case D64_TYPE_NONE: /* FAT */
  case D64_TYPE_D81:
	  size = 512;
	  set_error(ERROR_SYNTAX_UNABLE); /* TODO ... FIXME */
	  bcis_status = 0x2b; /* disk change (abort) */
	  break;
  default:                /* DNP, M2I */
	  size = 256;
	  set_error(ERROR_SYNTAX_UNABLE); /* TODO ... FIXME */
	  bcis_status = 0x1b; /* disk change (abort) */
  }

  if ((bcis_status & 0xf) != 0xb) {
	  /* not abort */
	  if (size == 256)
		buf = alloc_buffer();
	  else /* only 512 for now */
		buf = alloc_linked_buffers(2);
	  if (buf == NULL)
		  bcis_status = 0xb; /* disk change (abort) */
  } else
	  buf = NULL; /* make GCC happy */
  if ((bcis_status & 0xf) == 0xb) {
	  fserial_out(0, bcis_status);
	  return;
  }
  /* set_busy_led(1); <-- not work because of CLI */
  DIRTY_LED_ON(); /* works for me */
  flags = 1; /* current CLOCK high because of Unlisten */
  /* bcis_status = 1; 1571 doesn't clear error, neither do we */
  
  do {
	  if (!(command_buffer[2] & 0x20)) {
		  /* not buffer transfer only (really read disk) $83A4 */
	      read_sector(buf, current_part, fl_track, fl_sector);
		  if (current_error == 0)
			  bcis_status = (bcis_status & 0xf0) | 1; /* okay */
		  else if (current_error == ERROR_ILLEGAL_TS_COMMAND
			  || current_error == ERROR_ILLEGAL_TS_LINK)
			  bcis_status = (bcis_status & 0xf0) | 2; /* sector not found */
		  else
			  bcis_status = (bcis_status & 0xf0) | 5; /* data checksum error */

		  if (fserial_out(flags ^= 1, bcis_status))
			  break; /* found ATN */
		  if ((bcis_status & 0xf) != 1 && !(command_buffer[2] & 0x40))
			  break; /* error and not 'ignore error' ($83c1) */
	  }

	  if (command_buffer[2] & 0x20 || !(command_buffer[2] & 0x80)) {
		  /* 'transfer only' or not 'no transfer' ($83cc) */
		  for (i=0; i<size; ++i) {
		    stop = fserial_out(flags ^= 1, buf->data[i]);
		    if (stop)
			  break; /* found ATN */
		  }
	  }
	  if (stop)
		  break; /* found ATN */
	  /* Next GCR sector ($861e)
	  Note 1571 does not use Mod() and more importantly
	  this can re-read the same sectors if the interleave
	  and the # sector/track have a common factor.
	  For example, track 25 has 18 sectors, so with an interleave of 6
	  there would be trouble because 18 and 6 have common factors.
	  The default interleave of 5 is not a factor for any 1571 track,
	  but is a common factor for every 1581 track (10 or 40 sectors) ... */
	  /* TODO: next sector for FAT */
	  if (fl_track == 0 || fl_track > partition[current_part].d64data.last_track)
		  stop = 255; /* whatever, bad track */
	  else
		  stop = sectors_per_track(current_part, fl_track);
	  fl_sector += bcis_interleave;
	  if (fl_sector >= stop)
		  fl_sector -= stop; /* maybe we should use Mod() */
  } while (--n_sec);
 } /* end ATOMIC_BLOCK */
  buf->cleanup(buf);
  free_buffer(buf);
  update_leds();
}

void s_in_burstload(uint8_t n_sec) {
  /* get sector(s) of data & write to fl_track $83EC */
  /* command_buffer[2] contains special flags */
  /* fl_sector is the first sector, n_sec is the number of sectors */
  /* bcis_interleave is used if n_sec > 1 */
  uint8_t flags;     /* fast-serial next ~CLOCK (primary) */
  uint16_t size, i;  /* sector size, index */
  int16_t val = 0;   /* received ok, not found ATN */
  buffer_t *buf;

  if (!IEC_CLOCK) { /* should be high because of Unlisten */
	  set_error(ERROR_BUS);
	  return;
  }

 ATOMIC_BLOCK( ATOMIC_FORCEON ) {
	// release everything
	IEC_OUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);
 }
	/* The C128 is waiting in a loop and we have no way
	   to signal abort until we send a status byte
	   which may be never! (depending on command flags)
	   So we use 2 bits of 'flags' to let us know what to do
	   bit 7 = have buffer
	   bit 6 = okay (not abort)
	   bits 0,1 are normal CLOCK control for assembly code
	*/
  flags = 0xc0; /* buf + okay + first CLOCK low */

  size = 256;
  switch(partition[current_part].imagetype) {
  case D64_TYPE_D41:
  case D64_TYPE_D71:
	  break;
  case D64_TYPE_NONE: /* FAT */
  case D64_TYPE_D81:
	  size = 512;     /* FIXME */
  default:            /* DNP, M2I ... FIXME */
	  flags &= 0xbf;  /* not okay (abort) */
	  bcis_status = 2; /* sector not found */
	  set_error(ERROR_SYNTAX_UNABLE);
	  break;
  }

  if (size == 256)
	buf = alloc_buffer();
  else /* only 512 for now */
	buf = alloc_linked_buffers(2);

  if (bcis_status == 0xb || buf == NULL)  {
	/* disk change detected or no buffer */
	flags &= 0xbf; /* not okay (abort) $83f8 */
	if (buf == NULL) {
		flags &= 0x7f; /* no buffer */
		bcis_status = 0xb; /* the 'abort' error */
	} else
		set_error(ERROR_DISK_ID_MISMATCH);
  }

  set_busy_led(1);
  
  do {
	  if (!(command_buffer[2] & 0x80)) {
		  /* not 'no transfer' ($840e) */
		  for (i=0; i<size; ++i) {
            ATOMIC_BLOCK( ATOMIC_FORCEON ) {
 		        val = fserial_in(flags ^= 1);
			}
			if (flags & 0x80) /* have buffer */
				buf->data[i] = val & 0xff;
		    if (val < 0)
			  break; /* found ATN */
		  }
		  if (val < 0)
			  break; /* found ATN */
          ATOMIC_BLOCK( ATOMIC_FORCEON ) {
		     IEC_OUT &= (uint8_t)~IEC_OBIT_CLOCK; /* release CLOCK ($8438) */
		  }
	  }

	  if (!(command_buffer[2] & 0x20)) {
		  /* not 'buffer transfer only' (really write disk) $8442 */
		  uint8_t tmp;
		  if (flags & 0x40) { /* ok (not abort) */
			  write_sector(buf, current_part, fl_track, fl_sector);
			  if (current_error == 0)
				  bcis_status = (bcis_status & 0xf0) | 1; /* okay */
			  else if (current_error == ERROR_ILLEGAL_TS_COMMAND
				  || current_error == ERROR_ILLEGAL_TS_LINK)
				  bcis_status = (bcis_status & 0xf0) | 2; /* sector not found */
			  else if (current_error == ERROR_WRITE_PROTECT)
				  bcis_status = (bcis_status & 0xf0) | 8; /* write protect */
			  else
				  bcis_status = (bcis_status & 0xf0) | 7; /* verify error */
		  }
          ATOMIC_BLOCK( ATOMIC_FORCEON ) {
			  if (fserial_out(0, bcis_status))
				  break; /* found ATN */
		  }
		  /* wait for byte received (CLOCK high) $846a */
		  do {
			  tmp = IEC_PIN & (IEC_BIT_CLOCK | IEC_BIT_ATN);
		  } while (tmp == IEC_BIT_ATN);
		  if (!(tmp & IEC_BIT_ATN))
			  break; /* found ATN */

		  if (!(flags & 0x40) || ((bcis_status & 0xf) != 1 && !(command_buffer[2] & 0x40)))
			  break; /* abort or (error and not 'ignore error') $8471 */
	  }
	  /* Next GCR sector ($8479)
	  Note 1571 does not use Mod() and more importantly
	  this can re-write the same sectors if the interleave
	  and the # sector/track have a common factor.
	  For example, track 25 has 18 sectors, so with an interleave of 6
	  there would be trouble because 18 and 6 have common factors.
	  The default interleave of 5 is not a factor for any 1571 track,
	  but is a common factor for every 1581 track (10 or 40 sectors) ... */
	  /* TODO: handle FAT access */
	  if (!(flags & 0x40) || fl_track == 0 || fl_track > partition[current_part].d64data.last_track)
		  val = 255; /* whatever, bad track or not supported type */
	  else
		  val = sectors_per_track(current_part, fl_track);
	  fl_sector += bcis_interleave;
	  if (fl_sector >= (val & 0xff))
		  fl_sector -= (val & 0xff); /* maybe we should use Mod() */
  } while (--n_sec);

  buf->cleanup(buf);
  free_buffer(buf);
  update_leds();
}

void f_out_burstload(void) {
  /* send a complete file using fast serial bus  */
  uint8_t flags;
  uint8_t stop = 0; /* ok, not found ATN */
  buffer_t *buf;
  uint8_t len;
  uint8_t* buf_data; /* because GCC didn't optimize buf->data[i] */

 ATOMIC_BLOCK( ATOMIC_FORCEON ) {
	// release everything
	IEC_OUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);

  flags = command_buffer[2]; /* save command flags (bit 7) */

  /* abuse 'stop' for buffer index */
  len = command_length - 3; /* remove U0x before filename*/
  for (stop=0; stop<len; stop++)
    command_buffer[stop] = command_buffer[3+stop];

  command_buffer[len] = 0;
  command_length = len;

  /* 1571 totally ignores standard file parser
  but we use it because that is stupid.  ($9083)
  We do honor bit 7 which means 'not PRG only' */
  if (!(flags & 0x80)) {
    command_buffer[len++] = ',';
    command_buffer[len++] = 'P';
  }

  flags = 1; /* current CLOCK (high from Unlisten) */

  file_open(0); /* secondary address 0 */
  buf = find_buffer(0);
  if (!buf) {                /* $90DF */
	  if (current_error == ERROR_FILE_NOT_FOUND)
		  bcis_status = 0x2; /* sector (file) not found */
	  else
		  bcis_status = 0xf; /* drive not ready */
	  fserial_out(flags ^= 1, bcis_status);
	  return;
  }

  /* set_busy_led(1); <-- not work because of CLI */
  DIRTY_LED_ON(); /* works for me */
  bcis_status = 1; /* ok ... assume not last sector */
  flags |= 0x80; /* flag 'first sector' */

  do {
	  if (buf->sendeoi) /* last sector */
		  bcis_status = 0x1f;

	  if (fserial_out(flags ^= 1, bcis_status))
		  break; /* found ATN */
	  
	  len = buf->lastused - 1;
	  if (bcis_status == 0x1f) {
		  /* last block ($914e) or 1-block file ($9159) */
		  if (fserial_out(flags ^= 1, flags & 0x80 ? len-2 : len))
			  break; /* found ATN */
	  }
	  flags &= 0x7f; /* clear 'first sector' */

	  buf_data = &buf->data[2];
	  do {    /* send block $9184 */
		  stop = fserial_out(flags ^= 1, *buf_data);
		  ++buf_data;
		  if (stop)
			  break; /* found ATN */
	  } while (--len);
	  if (stop)
		  break; /* found ATN */

	  if (bcis_status == 1 && buf->refill(buf)) {   /* $919a */
		  if (current_error == ERROR_ILLEGAL_TS_LINK)
			  bcis_status = 2; /* sector not found */
		  else
			  bcis_status = 5; /* guess -- data block checksum error */
		  fserial_out(flags ^= 1, bcis_status);
	  }
  } while (bcis_status == 1);

 } /* end ATOMIC_BLOCK */

  buf->cleanup(buf);
  free_buffer(buf);
  update_leds();
}

#ifdef CONFIG_LOADER_DREAMLOAD
#ifndef set_clock_irq
#  error "Sorry, DreamLoad is only supported on platforms with a CLK interrupt"
#endif

static void dreamload_send_block(const uint8_t* p) {
  uint8_t checksum = 0;
  int     n;

  ATOMIC_BLOCK( ATOMIC_FORCEON ) {

    // checksum is EOR of all bytes
    for (n = 0; n < 256; n++)
      checksum ^= p[n];

    // send status, data bytes and checksum
    dreamload_send_byte(0);
    for (n = 0; n < 256; n++) {
      dreamload_send_byte(*p);
      p++;
    }
    dreamload_send_byte(checksum);

    // release CLOCK and DATA
    IEC_OUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);
  }
}

void load_dreamload(void) {
  uint16_t n;
  uint8_t  type;
  buffer_t *buf;

  /* disable IRQs while loading the final code, so no jobcodes are read */
  ATOMIC_BLOCK( ATOMIC_FORCEON ) {
    set_clock_irq(0);
    set_atn_irq(0);

    // Release clock and data
    IEC_OUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);

    /* load final drive code, fixed length */
    type = 0;
    for (n = 4 * 256; n != 0; --n) {
      type ^= dreamload_get_byte();
    }

    if ((type == 0xac) || (type == 0xdc)) {
      set_atn_irq(1);
      detected_loader = FL_DREAMLOAD_OLD;
    } else {
      set_clock_irq(1);
    }

    /* mark no job waiting, enable IRQs to get job codes */
    fl_track = 0xff;
  }

  buf = alloc_system_buffer();
  if (!buf) {
    /* &�$% :-( */
    goto error;
  }

  for (;;) {

    while (fl_track == 0xff) {
      if (key_pressed(KEY_NEXT | KEY_PREV | KEY_HOME)) {
        change_disk();
      }
      if (key_pressed(KEY_SLEEP)) {
        reset_key(KEY_SLEEP);
        set_busy_led(0);
        set_dirty_led(1);
        fl_track = 0;
        fl_sector = 0;
        break;
      }
    }

    set_busy_led(1);

    /* Output the track/sector for debugging purposes */
    uart_puthex(fl_track);
    uart_putc('/');
    uart_puthex(fl_sector);
    uart_putcrlf();

    if (fl_track == 0) {
      // check special commands first
      if (fl_sector == 0) {
        // end loader
        set_busy_led(0);
        break;
      } else if (fl_sector == 1) {
        // command: load first sector of directory
        // slow down 18/1 loading, so diskswap has a higher chance
        tick_t targettime = ticks + MS_TO_TICKS(1000);
        while (time_before(ticks,targettime)) ;
        read_sector(buf, current_part,
                    partition[current_part].d64data.dir_track,
                    partition[current_part].d64data.dir_start_sector);
        dreamload_send_block(buf->data);
      }
      else {
        // fl_sector == 2 is canonical
        set_busy_led(0);
      }
    } else {
      read_sector(buf, current_part, fl_track, fl_sector);
      dreamload_send_block(buf->data);
    }
    fl_track = 0xff;
  }

error:
  free_buffer(buf);
  set_clock_irq(0);
  set_atn_irq(0);
}
#endif

#ifdef CONFIG_LOADER_ULOAD3
static uint8_t uload3_transferchain(uint8_t track, uint8_t sector, uint8_t saving) {
  buffer_t *buf;
  uint8_t i,bytecount,first;

  first = 1;

  buf = alloc_buffer();
  if (!buf) {
    uload3_send_byte(0xff);
    return 0;
  }

  do {
    /* read current sector */
    read_sector(buf, current_part, track, sector);
    if (current_error != 0) {
      uload3_send_byte(0xff);
      return 0;
    }

    /* send number of bytes in sector */
    if (buf->data[0] == 0) {
      bytecount = buf->data[1]-1;
    } else {
      bytecount = 254;
    }
    uload3_send_byte(bytecount);

    if (saving) {
      if (first) {
        /* send load address */
        first = 0;
        uload3_send_byte(buf->data[2]);
        uload3_send_byte(buf->data[3]);
        i = 2;
      } else
        i = 0;

      /* receive sector contents */
      for (;i<bytecount;i++) {
        int16_t tmp = uload3_get_byte();
        if (tmp < 0)
          return 1;

        buf->data[i+2] = tmp;
      }

      /* write sector */
      write_sector(buf, current_part, track, sector);
      if (current_error != 0) {
        uload3_send_byte(0xff);
        return 0;
      }
    } else {
      /* reading: send sector contents */
      for (i=0;i<bytecount;i++)
        uload3_send_byte(buf->data[i+2]);
    }

    track  = buf->data[0];
    sector = buf->data[1];
  } while (track != 0);

  /* send end marker */
  uload3_send_byte(0);

  free_buffer(buf);
  return 0;
}

void load_uload3(void) {
  int16_t cmd,tmp;
  uint8_t t,s;

  while (1) {
    /* read command */
    cmd = uload3_get_byte();
    if (cmd < 0) {
      /* ATN received */
      break;
    }

    switch (cmd) {
    case 1: /* load a file */
    case 2: /* save and replace a file */
      tmp = uload3_get_byte();
      if (tmp < 0)
        return;
      t = tmp;

      tmp = uload3_get_byte();
      if (tmp < 0)
        /* ATN received */
        return;
      s = tmp;

      if (uload3_transferchain(t,s, (cmd == 2)))
        return;

      break;

    case '$':
      /* read directory */
      uload3_transferchain(partition[current_part].d64data.dir_track,
                           partition[current_part].d64data.dir_start_sector, 0);
      break;

    default:
      /* unknown command */
      uload3_send_byte(0xff);
      break;
    }
  }
}
#endif
