/* sd2iec - SD/MMC to Commodore serial bus interface/controller
   Copyright (C) 2007-2017  Ingo Korb <ingo@akana.de>
   Final Cartridge III, DreamLoad, ELoad fastloader support:
   Copyright (C) 2008-2011  Thomas Giesel <skoe@directbox.com>
   Nippon Loader support:
   Copyright (C) 2010  Joerg Jungermann <abra@borkum.net>

   Inspired by MMC2IEC by Lars Pontoppidan et al.

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

#include <stdbool.h>
#include <string.h>
#include "config.h"
#include "diskchange.h"
#include "fastloader-ll.h"
#include "iec-bus.h"
#include "iec.h"
#include "led.h"
#include "timer.h"
#include "buffers.h"
#include "doscmd.h"
#include "errormsg.h"
#include "fileops.h"
#include "d64ops.h"
#include "parser.h"
#include "wrapops.h"
#include "avr/arch-config.h"
#include "fastloader.h"

uint8_t detected_loader;

/* Function pointer to the current byte transmit/receive functions */
/* (to simplify loaders with multiple variations of these)         */
uint8_t (*fast_send_byte)(uint8_t byte);
uint8_t (*fast_get_byte)(void);

/* track to load, used as a kind of jobcode */
volatile uint8_t fl_track;

/* sector to load, used as a kind of jobcode */
volatile uint8_t fl_sector;

#ifdef PARALLEL_ENABLED
/* parallel byte received */
volatile uint8_t parallel_rxflag;
#endif

/* Small helper for fastloaders that need to detect disk changes */
uint8_t check_keys(void) {
  /* Check for disk changes etc. */
  if (key_pressed(KEY_NEXT | KEY_PREV | KEY_HOME)) {
    change_disk();
  }
  if (key_pressed(KEY_SLEEP)) {
    reset_key(KEY_SLEEP);
    set_busy_led(0);
    set_dirty_led(1);

    /* wait for release */
    while (key_pressed(IGNORE_KEYS)) ;

    return 1;
  }

  return 0;
}


/*
 *
 *  GIJoe/EPYX common code
 *
 */
#if defined(CONFIG_LOADER_GIJOE) || defined(CONFIG_LOADER_EPYXCART)
/* Returns the byte read or <0 if the user aborts */
/* Aborting on ATN is not reliable for at least one version */
int16_t gijoe_read_byte(void) {
  uint8_t i;
  uint8_t value = 0;

  for (i=0;i<4;i++) {
    while (IEC_CLOCK)
      if (check_keys())
        return -1;

    value >>= 1;

    delay_us(3);
    if (!IEC_DATA)
      value |= 0x80;

    while (!IEC_CLOCK)
      if (check_keys())
        return -1;

    value >>= 1;

    delay_us(3);
    if (!IEC_DATA)
      value |= 0x80;
  }

  return value;
}
#endif

/* -----------------------*/
/* Burst loader functions */
/* -- move these later ---*/
uint8_t b_out_burstload(uint8_t flags, uint8_t val) {
  uart_put_str("b_out\n\r");
  ATOMIC_BLOCK( ATOMIC_FORCEON ) {
    val = fserial_out(flags, val);
  }
  return val;
}

int16_t b_in_burstload(uint8_t flags) {
  uart_put_str("b_in\n\r");
  int16_t val;
  ATOMIC_BLOCK( ATOMIC_FORCEON ) {
    val = fserial_in(flags);
  }
  return val;
}

void s_out_burstload(uint8_t n_sec) {
  uart_put_str("s_out\n\r");
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
  IEC_OUTPUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);

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
  /* FIXME
  DIRTY_LED_ON(); */ /* works for me */
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
  uart_put_str("s_in\n\r");
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
  IEC_OUTPUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);
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
         IEC_OUTPUT &= (uint8_t)~IEC_OBIT_CLOCK; /* release CLOCK ($8438) */
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
        tmp = IEC_INPUT & (IEC_BIT_CLOCK | IEC_BIT_ATN);
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
  uart_put_str("f_out\n\r");
  /* send a complete file using fast serial bus  */
  uint8_t flags;
  uint8_t stop = 0; /* ok, not found ATN */
  buffer_t *buf;
  uint8_t len;
  uint8_t* buf_data; /* because GCC didn't optimize buf->data[i] */

 ATOMIC_BLOCK( ATOMIC_FORCEON ) {
  // release everything
  IEC_OUTPUT &= (uint8_t)~(IEC_OBIT_ATN|IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_SRQ);

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
  /* FIXME
  DIRTY_LED_ON(); */ /* works for me */

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
      
      /*if (fserial_out(flags ^= 1, flags & 0x80 ? len-2 : len)) <- gcc disapproves */
      flags ^= 1;
      if (fserial_out(flags, flags & 0x80 ? len-2 : len))
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

/*
 *
 *  Generic parallel speeder
 *
 */

#ifdef PARALLEL_ENABLED
/* parallel handshake interrupt handler */
PARALLEL_HANDLER {
  parallel_rxflag = 1;
}
#endif
