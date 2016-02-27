/* sd2iec - SD/MMC to Commodore serial bus interface/controller
   Copyright (C) 2007-2016  Ingo Korb <ingo@akana.de>
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

#ifdef __AVR__
# include <avr/boot.h>
#endif
#include <stdbool.h>
#include <string.h>
#include "config.h"
#include "atomic.h"
#include "buffers.h"
#include "d64ops.h"
#include "diskchange.h"
#include "display.h"
#include "doscmd.h"
#include "errormsg.h"
#include "fastloader-ll.h"
#include "fileops.h"
#include "iec-bus.h"
#include "iec.h"
#include "led.h"
#include "parser.h"
#include "timer.h"
#include "ustring.h"
#include "wrapops.h"
#include "fastloader.h"

#define UNUSED_PARAMETER uint8_t __attribute__((unused)) unused__

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
static uint8_t __attribute__((unused)) check_keys(void) {
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
 *  Turbodisk
 *
 */
#ifdef CONFIG_LOADER_TURBODISK
void load_turbodisk(UNUSED_PARAMETER) {
  uint8_t i,len,firstsector;
  buffer_t *buf;

#if defined __AVR_ATmega644__   || \
    defined __AVR_ATmega644P__  || \
    defined __AVR_ATmega1284P__ || \
    defined __AVR_ATmega1281__
  /* Lock out clock sources that aren't stable enough for this protocol */
  uint8_t tmp = boot_lock_fuse_bits_get(GET_LOW_FUSE_BITS) & 0x0f;
  if (tmp == 2) {
    set_error(ERROR_CLOCK_UNSTABLE);
    return;
  }
#endif

  set_clock(0);
  uart_flush();

  /* Copy filename to beginning of buffer */
  len = command_buffer[9];
  for (i=0;i<len;i++)
    command_buffer[i] = command_buffer[10+i];

  command_buffer[len] = 0;
  command_length = len;

  /* Open the file */
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
  cleanup_and_free_buffer(buf);

  set_clock(1);
}
#endif


/*
 *
 *  Final Cartridge 3 / EXOS
 *
 */
#ifdef CONFIG_LOADER_FC3
void load_fc3(uint8_t freezed) {
  buffer_t *buf;
  unsigned char step,pos;
  unsigned char sector_counter = 0;
  unsigned char block[4];

  buf = find_buffer(0);

  if (!buf) {
    /* error, abort and pull down CLOCK and DATA to inform the host */
    set_data(0);
    set_clock(0);
    return;
  }

  /* to make sure the C64 VIC DMA is off */
  delay_ms(20);

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
      delay_us(190);
    fastloader_fc3_send_block(block);

    /* send the next 64 4-byte-blocks, the last 3 bytes are read behind
       the buffer, good that we don't have an MMU ;) */
    for (step = 0; step < 64; step++) {
      if (!IEC_ATN)
        goto cleanup;

      if (freezed)
        clk_data_handshake();
      else
        delay_us(190);
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
        set_data(0);
        set_clock(0);
        break;
      }
    }
  }

 cleanup:
  cleanup_and_free_buffer(buf);
}

void save_fc3(UNUSED_PARAMETER) {
  unsigned char n;
  unsigned char size;
  unsigned char eof = 0;
  buffer_t *buf;

  buf = find_buffer(1);
  /* Check if this is a writable file */
  if (!buf || !buf->write)
      return;

  /* to make sure the host pulled DATA low and is ready */
  delay_ms(5);

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

  cleanup_and_free_buffer(buf);
}

void load_fc3oldfreeze(UNUSED_PARAMETER) {
  buffer_t *buf;
  uint16_t i;

  /* mark as busy */
  set_srq(0);
  set_clock(1);
  set_data(0);

  /* wait until C64 has finished UNLISTEN */
  delay_us(1);
  start_timeout(100);
  while (!IEC_CLOCK && !has_timed_out()) ;

  buf = find_buffer(0);

  if (!buf) {
    /* error */
    return;
  }

  /* sector loop */
  while (1) {
    /* send sector data */
    for (i = 2; i <= buf->lastused; i++) {
      if (fast_send_byte(buf->data[i])) {
        /* ATN active, abort */
        goto done;
      }
    }

    /* check for end of file */
    if (buf->sendeoi)
      break;

    /* read next sector */
    if (buf->refill(buf)) {
      /* error */
      break;
    }
  }

 done:
  cleanup_and_free_buffer(buf);
}

#endif


/*
 *
 *  Dreamload
 *
 */
#ifdef CONFIG_LOADER_DREAMLOAD
#ifndef HAVE_CLOCK_IRQ
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
    set_clock(1);
    set_data(1);
  }
}

void load_dreamload(UNUSED_PARAMETER) {
  uint16_t n;
  uint8_t  type;
  buffer_t *buf;

  /* disable IRQs while loading the final code, so no jobcodes are read */
  ATOMIC_BLOCK( ATOMIC_FORCEON ) {
    set_clock_irq(0);
    set_atn_irq(0);

    /* Release clock and data */
    set_clock(1);
    set_data(1);

    /* wait until the C64 has released clock */
    while (!IEC_CLOCK) ;

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
    /* &@$% :-( */
    goto error;
  }

  /* Find the start sector of the current directory */
  dh_t dh;
  path_t curpath;

  curpath.part = current_part;
  curpath.dir  = partition[current_part].current_dir;
  opendir(&dh, &curpath);

  for (;;) {

    while (fl_track == 0xff) {
      if (check_keys()) {
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

        read_sector(buf, current_part, dh.dir.d64.track, dh.dir.d64.sector);
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


/*
 *
 * ULoad Model 3
 *
 */
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

void load_uload3(UNUSED_PARAMETER) {
  int16_t cmd,tmp;
  uint8_t t,s;
  dh_t dh;
  path_t curpath;

  curpath.part = current_part;
  curpath.dir  = partition[current_part].current_dir;
  opendir(&dh, &curpath);

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
      uload3_transferchain(dh.dir.d64.track, dh.dir.d64.sector, 0);
      break;

    default:
      /* unknown command */
      uload3_send_byte(0xff);
      break;
    }
  }
}
#endif


/*
 *
 * eload
 *
 */
#ifdef CONFIG_LOADER_ELOAD1
void load_eload1(UNUSED_PARAMETER) {
  buffer_t *buf;
  int16_t cmd;
  uint8_t count, pos, end;

  while (1) {
    /* read command */
    cmd = uload3_get_byte();
    if (cmd < 0) {
      /* ATN received */
      break;
    }

    switch (cmd) {
    case 1: /* load a file */
      buf = find_buffer(0);

      if (!buf) {
        if (!IEC_ATN)
          return;
        uload3_send_byte(0xff); /* error */
        return;
      }

      end = 0;
      do {
        count = buf->lastused - 1;
        if (!IEC_ATN)
          return;
        uload3_send_byte(count);
        pos = 2;
        while (count--) {
          if (!IEC_ATN)
            return;
          uload3_send_byte(buf->data[pos++]);
        }
        if (buf->sendeoi) {
          uload3_send_byte(0); /* EOF */
          end = 1;
        }
        else if (buf->refill(buf)) {
          uload3_send_byte(0xff); /* error */
          end = 1;
        }
      } while (!end);
      break;

    default:
      /* unknown command */
      uload3_send_byte(0xff);
      break;
    }
  }
}

#endif


/*
 *
 *  GIJoe/EPYX common code
 *
 */
#if defined(CONFIG_LOADER_GIJOE) || defined(CONFIG_LOADER_EPYXCART)
/* Returns the byte read or <0 if the user aborts */
/* Aborting on ATN is not reliable for at least one version */
static int16_t gijoe_read_byte(void) {
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


/*
 *
 * GI Joe
 *
 */
#ifdef CONFIG_LOADER_GIJOE
static void gijoe_send_byte(uint8_t value) {
  uint8_t i;

  ATOMIC_BLOCK( ATOMIC_FORCEON ) {
    for (i=0;i<4;i++) {
      /* Wait for clock high */
      while (!IEC_CLOCK) ;

      set_data(value & 1);
      value >>= 1;

      /* Wait for clock low */
      while (IEC_CLOCK) ;

      set_data(value & 1);
      value >>= 1;
    }
  }
}

void load_gijoe(UNUSED_PARAMETER) {
  buffer_t *buf;

  set_data(1);
  set_clock(1);
  set_atn_irq(0);

  /* Wait until the bus has settled */
  delay_ms(10);
  while (!IEC_DATA || !IEC_CLOCK) ;

  while (1) {
    /* Handshake */
    set_clock(0);

    while (IEC_DATA)
      if (check_keys())
        return;

    set_clock(1);
    uart_flush();

    /* First byte is ignored */
    if (gijoe_read_byte() < 0)
      return;

    /* Read two file name characters */
    command_buffer[0] = gijoe_read_byte();
    command_buffer[1] = gijoe_read_byte();

    set_clock(0);

    command_buffer[2] = '*';
    command_buffer[3] = 0;
    command_length = 3;

    /* Open the file */
    file_open(0);
    uart_flush();
    buf = find_buffer(0);
    if (!buf) {
      set_clock(1);
      gijoe_send_byte(0xfe);
      gijoe_send_byte(0xfe);
      gijoe_send_byte(0xac);
      gijoe_send_byte(0xf7);
      continue;
    }

    /* file is open, transfer */
    while (1) {
      uint8_t i = buf->position;

      set_clock(1);
      delay_us(2);

      do {
        if (buf->data[i] == 0xac)
          gijoe_send_byte(0xac);

        gijoe_send_byte(buf->data[i]);
      } while (i++ < buf->lastused);

      /* Send end marker and wait for the next name */
      if (buf->sendeoi) {
        gijoe_send_byte(0xac);
        gijoe_send_byte(0xff);

        cleanup_and_free_buffer(buf);
        break;
      }

      /* Send "another sector following" marker */
      gijoe_send_byte(0xac);
      gijoe_send_byte(0xc3);
      delay_us(50);
      set_clock(0);

      /* Read next block */
      if (buf->refill(buf)) {
        /* Send error marker */
        gijoe_send_byte(0xfe);
        gijoe_send_byte(0xfe);
        gijoe_send_byte(0xac);
        gijoe_send_byte(0xf7);

        cleanup_and_free_buffer(buf);
        break;
      }
    }
  }
}
#endif


/*
 *
 * Epyx Fast Load Cartridge
 *
 */
#ifdef CONFIG_LOADER_EPYXCART
void load_epyxcart(UNUSED_PARAMETER) {
  uint8_t checksum = 0;
  int16_t b,i;

  uart_flush(); // Pending output can mess up our timing

  /* Initial handshake */
  set_data(1);
  set_clock(0);
  set_atn_irq(0);

  while (IEC_DATA)
    if (!IEC_ATN)
      return;

  set_clock(1);

  /* Receive and checksum stage 2 */
  for (i=0;i<256;i++) {
    b = gijoe_read_byte();

    if (b < 0)
      return;

    if (i < 237)
      /* Stage 2 has some junk bytes at the end, ignore them */
      checksum ^= b;
  }

  /* Check for known stage2 loaders */
  if (checksum != 0x91 && checksum != 0x5b) {
    return;
  }

  /* Receive file name */
  i = gijoe_read_byte();
  if (i < 0) {
    return;
  }

  command_length = i;

  do {
    b = gijoe_read_byte();
    if (b < 0)
      return;

    command_buffer[--i] = b;
  } while (i > 0);

  set_clock(0);

  /* Open the file */
  file_open(0);

  buffer_t *buf = find_buffer(0);
  if (buf == NULL) {
    set_clock(1);
    return;
  }

  /* Transfer data */
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    while (1) {
      set_clock(1);
      set_data(1);

      /* send number of bytes in sector */
      if (epyxcart_send_byte(buf->lastused-1)) {
        break;
      }

      /* send data */
      for (i=2;i<=buf->lastused;i++) {
        if (epyxcart_send_byte(buf->data[i])) {
          break;
        }
      }

      if (!IEC_ATN)
        break;

      /* exit after final sector */
      if (buf->sendeoi)
        break;

      /* read next sector */
      set_clock(0);
      if (buf->refill(buf))
        break;
    }
  }

  set_clock(1);
  set_data(1);
  cleanup_and_free_buffer(buf);
}
#endif


/*
 *
 *  GEOS
 *
 */
#ifdef CONFIG_LOADER_GEOS

/* Receive a fixed-length data block */
static void geos_receive_datablock(void *data_, uint16_t length) {
  uint8_t *data = (uint8_t*)data_;

  data += length-1;

  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    while (!IEC_CLOCK);
    set_data(1);
    while (length--)
      *data-- = fast_get_byte();
    set_data(0);
  }
}

/* Receive a data block from the computer */
static void geos_receive_lenblock(uint8_t *data) {
  uint8_t exitflag = 0;
  uint16_t length = 0;

  /* Receive data length */
  while (!IEC_CLOCK && IEC_ATN)
    if (check_keys()) {
      /* User-requested exit */
      exitflag = 1;
      break;
    }

  /* Exit if ATN is low */
  if (!IEC_ATN || exitflag) {
    *data++ = 0;
    *data   = 0;
    return;
  }

  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    set_data(1);
    length = fast_get_byte();
    set_data(0);
  }

  if (length == 0)
    length = 256;

  geos_receive_datablock(data, length);
}

/* Send a single byte to the computer after waiting for CLOCK high */
static void geos_transmit_byte_wait(uint8_t byte) {
  ATOMIC_BLOCK(ATOMIC_RESTORESTATE) {
    /* Wait until clock is high */
    while (!IEC_CLOCK) ;
    set_data(1);

    /* Send byte */
    fast_send_byte(byte);
    set_clock(1);
    set_data(0);
  }

  delay_us(25); // educated guess
}

/* Send data block to computer */
static void geos_transmit_buffer_s3(uint8_t *data, uint16_t len) {
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    /* Wait until clock is high */
    while (!IEC_CLOCK) ;
    set_data(1);

    /* Send data block */
    uint16_t i = len;
    data += len - 1;

    while (i--) {
      fast_send_byte(*data--);
    }

    set_clock(1);
    set_data(0);

    delay_us(15); // guessed
  }
}

static void geos_transmit_buffer_s2(uint8_t *data, uint16_t len) {
  /* Send length byte */
  geos_transmit_byte_wait(len);

  /* the rest is the same as in stage 3 */
  geos_transmit_buffer_s3(data, len);
}

/* Send job status to computer */
static void geos_transmit_status(void) {
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    /* Send a single 1 byte as length indicator */
    geos_transmit_byte_wait(1);

    /* Send (faked) job result code */
    if (current_error == 0)
      geos_transmit_byte_wait(1);
    else
      if (current_error == ERROR_WRITE_PROTECT)
        geos_transmit_byte_wait(8);
      else
        geos_transmit_byte_wait(2); // random non-ok job status
  }
}

/* GEOS READ operation */
static void geos_read_sector(uint8_t track, uint8_t sector, buffer_t *buf) {
  uart_putc('R');
  uart_puthex(track);
  uart_putc('/');
  uart_puthex(sector);
  uart_putcrlf();

  read_sector(buf, current_part, track, sector);
}

/* GEOS WRITE operation */
static void geos_write_sector_41(uint8_t track, uint8_t sector, buffer_t *buf) {
  uart_putc('W');
  uart_puthex(track);
  uart_putc('/');
  uart_puthex(sector);
  uart_putcrlf();

  /* Provide "unwritten data present" feedback */
  mark_buffer_dirty(buf);

  /* Receive data */
  geos_receive_lenblock(buf->data);

  /* Write to image */
  write_sector(buf, current_part, track, sector);

  /* Reset "unwritten data" feedback */
  mark_buffer_clean(buf);
}

/* GEOS WRITE_71 operation */
static void geos_write_sector_71(uint8_t track, uint8_t sector, buffer_t *buf) {
  uart_putc('W');
  uart_puthex(track);
  uart_putc('/');
  uart_puthex(sector);
  uart_putcrlf();

  /* Provide "unwritten data present" feedback */
  mark_buffer_dirty(buf);

  /* Receive data */
  geos_receive_datablock(buf->data, 256);

  /* Write to image */
  write_sector(buf, current_part, track, sector);

  /* Send status */
  geos_transmit_status();

  /* Reset "unwritten data" feedback */
  mark_buffer_clean(buf);
}


/* GEOS stage 2/3 loader */
void load_geos(UNUSED_PARAMETER) {
  buffer_t *cmdbuf = alloc_system_buffer();
  buffer_t *databuf = alloc_system_buffer();
  uint8_t *cmddata;
  uint16_t cmd;

  if (!cmdbuf || !databuf)
    return;

  cmddata = cmdbuf->data;

  /* Initial handshake */
  uart_flush();
  delay_ms(1);
  set_data(0);
  while (IEC_CLOCK) ;

  while (1) {
    /* Receive command block */
    set_busy_led(0);
    geos_receive_lenblock(cmddata);
    set_busy_led(1);

    //uart_trace(cmddata, 0, 4);

    cmd = cmddata[0] | (cmddata[1] << 8);

    switch (cmd) {
    case 0x0320: // 1541 stage 3 transmit
      geos_transmit_buffer_s3(databuf->data, 256);
      geos_transmit_status();
      break;

    case 0x031f: // 1571; 1541 stage 2 status (only seen in GEOS 1.3)
                 // 1581 transmit
      if (detected_loader == FL_GEOS_S23_1581) {
        if (cmddata[2] & 0x80) {
          geos_transmit_buffer_s3(databuf->data, 2);
        } else {
          geos_transmit_buffer_s3(databuf->data, 256);
        }
      }
      geos_transmit_status();
      break;

    case 0x0325: // 1541 stage 3 status
    case 0x032b: // 1581 status
      geos_transmit_status();
      break;

    case 0x0000: // internal QUIT
    case 0x0412: // 1541 stage 2 quit
    case 0x0420: // 1541 stage 3 quit
    case 0x0457: // 1581 quit
    case 0x0475: // 1571 stage 3 quit
      while (!IEC_CLOCK) ;
      set_data(1);
      return;

    case 0x0432: // 1541 stage 2 transmit
      if (current_error != 0) {
        geos_transmit_status();
      } else {
        geos_transmit_buffer_s2(databuf->data, 256);
      }
      break;

    case 0x0439: // 1541 stage 3 set address
    case 0x04a5: // 1571 stage 3 set address
      // Note: identical in stage 2, address 0428, probably unused
      device_address = cmddata[2] & 0x1f;
      display_address(device_address);
      break;

    case 0x049b: // 1581 initialize
    case 0x04b9: // 1581 flush
    case 0x04dc: // 1541 stage 3 initialize
    case 0x0504: // 1541 stage 2 initialize - only seen in GEOS 1.3
    case 0x057e: // 1571 initialize
      /* Doesn't do anything that needs to be reimplemented */
      break;

    case 0x057c: // 1541 stage 2/3 write
      geos_write_sector_41(cmddata[2], cmddata[3], databuf);
      break;

    case 0x058e: // 1541 stage 2/3 read
    case 0x04cc: // 1581 read
      geos_read_sector(cmddata[2], cmddata[3], databuf);
      break;

    case 0x04af: // 1571 read_and_send
      geos_read_sector(cmddata[2], cmddata[3], databuf);
      geos_transmit_buffer_s3(databuf->data, 256);
      geos_transmit_status();
      break;

    case 0x047c: // 1581 write
    case 0x05fe: // 1571 write
      geos_write_sector_71(cmddata[2], cmddata[3], databuf);
      break;

    default:
      uart_puts_P(PSTR("unknown:\r\n"));
      uart_trace(cmddata, 0, 4);
      return;
    }
  }
}

/* Stage 1 only - send a sector chain to the computer */
static void geos_send_chain(uint8_t track, uint8_t sector,
                            buffer_t *buf, uint8_t *key) {
  uint8_t bytes;
  uint8_t *keyptr,*dataptr;

  do {
    /* Read sector - no error recovery on computer side */
    read_sector(buf, current_part, track, sector);

    /* Decrypt contents if we have a key */
    if (key != NULL) {
      keyptr = key;
      dataptr = buf->data + 2;
      bytes = 254;
      while (bytes--)
        *dataptr++ ^= *keyptr++;
    }

    /* Read link pointer */
    track = buf->data[0];
    sector = buf->data[1];

    if (track == 0) {
      bytes = sector - 1;
    } else {
      bytes = 254;
    }

    /* Send buffer contents */
    geos_transmit_buffer_s2(buf->data + 2, bytes);
  } while (track != 0);

  geos_transmit_byte_wait(0);
}

static const PROGMEM uint8_t geos64_chains[] = {
  19, 13,
  20, 15,
  20, 17,
  0
};

static const PROGMEM uint8_t geos128_chains[] = {
  19, 12,
  20, 15,
  23, 6,
  24, 4,
  0
};

/* GEOS 64 stage 1 loader */
void load_geos_s1(uint8_t version) {
  buffer_t *encrbuf = find_buffer(BUFFER_SYS_CAPTURE1);
  buffer_t *databuf = alloc_buffer();
  uint8_t *encdata = NULL;
  uint8_t track, sector;
  const uint8_t *chainptr;

  if (!encrbuf || !databuf)
    return;

  if (version == 0) {
    chainptr = geos64_chains;
  } else {
    chainptr = geos128_chains;
  }

  /* Initial handshake */
  uart_flush();
  delay_ms(1);
  set_data(0);
  while (IEC_CLOCK) ;

  /* Send sector chains */
  while (1) {
    track = pgm_read_byte(chainptr++);

    if (track == 0)
      break;

    sector = pgm_read_byte(chainptr++);

    /* Transfer sector chain */
    geos_send_chain(track, sector, databuf, encdata);

    /* Turn on decryption after the first chain */
    encdata = encrbuf->data;
  }

  /* Done! */
  free_buffer(encrbuf);
  set_data(1);
}

#endif

/*
 *
 *  Wheels
 *
 */
#ifdef CONFIG_LOADER_WHEELS

/* Send data block to computer */
static void wheels44_transmit_buffer(uint8_t *data, uint16_t len) {
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    /* Wait until clock is high */
    while (!IEC_CLOCK) ;
    set_data(1);

    /* Send data block */
    uint16_t i = len;
    data += len - 1;

    while (i--) {
      fast_send_byte(*data--);
    }

    set_clock(1);
    set_data(1);

    delay_us(5);
    while (IEC_CLOCK) ;

    set_data(0);
    delay_us(15); // guessed
  }
}

/* Send a single byte to the computer after waiting for CLOCK high */
static void wheels_transmit_byte_wait(uint8_t byte) {
  if (detected_loader == FL_WHEELS44_S2_1581) {
    ATOMIC_BLOCK(ATOMIC_RESTORESTATE) {
      /* Wait until clock is high */
      while (!IEC_CLOCK) ;
      set_data(1);

      /* Send byte */
      fast_send_byte(byte);
      set_clock(1);
      set_data(1);

      delay_us(5);
      while (IEC_CLOCK) ;
      set_data(0);
    }

    delay_us(15); // educated guess
  } else {
    geos_transmit_byte_wait(byte);
    delay_us(15); // educated guess
    while (IEC_CLOCK) ;
  }
}

/* Send a fixed-length data block */
static void wheels_transmit_datablock(void *data_, uint16_t length) {
  uint8_t *data = (uint8_t*)data_;

  if (detected_loader == FL_WHEELS44_S2_1581) {
    wheels44_transmit_buffer(data, length);
  } else {
    geos_transmit_buffer_s3(data, length);

    while (IEC_CLOCK) ;
  }
}

/* Receive a fixed-length data block */
static void wheels_receive_datablock(void *data_, uint16_t length) {
  uint8_t *data = (uint8_t*)data_;

  data += length-1;

  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    while (!IEC_CLOCK) ;
    set_data(1);
    while (length--)
      *data-- = fast_get_byte();

    if (detected_loader == FL_WHEELS44_S2 ||
        detected_loader == FL_WHEELS44_S2_1581)
      while (IEC_CLOCK) ;

    set_data(0);
  }
}

/* Wheels STATUS operation (030f) */
static void wheels_transmit_status(void) {
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    /* Send (faked) job result code */
    if (current_error == 0)
      wheels_transmit_byte_wait(1);
    else
      if (current_error == ERROR_WRITE_PROTECT)
        wheels_transmit_byte_wait(8);
      else
        wheels_transmit_byte_wait(2); // random non-ok job status
  }
}

/* Wheels CHECK_CHANGE operation (031b) */
static void wheels_check_diskchange(void) {
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    if (dir_changed) {
      /* Disk has changed */
      wheels_transmit_byte_wait(3);
    } else {
      /* Disk not changed */
      if (detected_loader == FL_WHEELS44_S2 &&
          (partition[current_part].imagetype & D64_TYPE_MASK) == D64_TYPE_D71) {
        wheels_transmit_byte_wait(0x80);
      } else {
        wheels_transmit_byte_wait(0);
      }
    }

    dir_changed = 0;
    while (IEC_CLOCK) ;
  }
}

/* Wheels WRITE operation (0306) */
static void wheels_write_sector(uint8_t track, uint8_t sector, buffer_t *buf) {
  uart_putc('W');
  uart_puthex(track);
  uart_putc('/');
  uart_puthex(sector);
  uart_putcrlf();

  /* Provide "unwritten data present" feedback */
  mark_buffer_dirty(buf);

  /* Receive data */
  wheels_receive_datablock(buf->data, 256);

  /* Write to image */
  write_sector(buf, current_part, track, sector);

  /* Send status */
  wheels_transmit_status();

  /* Reset "unwritten data" feedback */
  mark_buffer_clean(buf);
}

/* Wheels READ operation (0309) */
static void wheels_read_sector(uint8_t track, uint8_t sector, buffer_t *buf, uint16_t bytes) {
  uart_putc('R');
  uart_puthex(track);
  uart_putc('/');
  uart_puthex(sector);
  uart_putcrlf();

  read_sector(buf, current_part, track, sector);
  wheels_transmit_datablock(buf->data, bytes);
  wheels_transmit_status();
}

/* Wheels NATIVE_FREE operation (0312) */
static void wheels_native_free(void) {
  /* Cheat: Ignore the limits set by the C64 */
  uint16_t freeblocks;

  freeblocks = disk_free(current_part);
  wheels_transmit_datablock(&freeblocks, 2);
  wheels_transmit_status();
}

/* Wheels GET_CURRENT_PART_DIR (0315) */
static void wheels_get_current_part_dir(void) {
  uint8_t data[3];

  data[0] = partition[current_part].current_dir.dxx.track;
  data[1] = partition[current_part].current_dir.dxx.sector;
  data[2] = current_part+1;
  wheels_transmit_datablock(&data, 3);
}

/* Wheels SET_CURRENT_PART_DIR operation (0318) */
static void wheels_set_current_part_dir(void) {
  uint8_t data[3];

  wheels_receive_datablock(&data, 3);

  if (data[2] != 0)
    current_part = data[2]-1;

  partition[current_part].current_dir.dxx.track  = data[0];
  partition[current_part].current_dir.dxx.sector = data[1];
}

/* -------- */

/* Wheels stage 1 loader */
void load_wheels_s1(const uint8_t version) {
  buffer_t *buf;

  uart_flush();
  delay_ms(2);
  while (IEC_CLOCK) ;
  set_data(0);

  /* copy file name to command buffer */
  if (version == 0) {
    ustrcpy_P(command_buffer, PSTR("SYSTEM1"));
  } else {
    ustrcpy_P(command_buffer, PSTR("128SYSTEM1"));
  }
  command_length = ustrlen(command_buffer);

  /* open file */
  file_open(0);
  buf = find_buffer(0);
  if (!buf)
    goto wheels_exit;

  while (1) {
    /* Transmit current sector */
    wheels_transmit_datablock(buf->data, 256);

    /* Check for last sector */
    if (buf->sendeoi)
      break;

    /* Advance to next sector */
    if (buf->refill(buf)) {
      /* Error, abort - original loader doesn't handle this */
      break;
    }
  }

 wheels_exit:
  while (!IEC_CLOCK) ;
  set_data(1);
  set_clock(1);
  if (buf) {
    cleanup_and_free_buffer(buf);
  }
}

/* Wheels stage 2 loader */
void load_wheels_s2(UNUSED_PARAMETER) {
  struct {
    uint16_t address;
    uint8_t  track;
    uint8_t  sector;
  } cmdbuffer;
  buffer_t *databuf = alloc_system_buffer();

  if (!databuf)
    return;

  /* Initial handshake */
  uart_flush();
  delay_ms(1);
  while (IEC_CLOCK) ;
  set_data(0);
  set_clock(1);
  delay_us(3);

  while (1) {
    /* Receive command block - redundant clock line check for check_keys */
    while (!IEC_CLOCK && IEC_ATN) {
      if (check_keys()) {
        /* User-requested exit */
        return;
      }
    }

    wheels_receive_datablock(&cmdbuffer, 4);
    set_busy_led(1);
    //uart_trace(&cmdbuffer, 0, 4);

    switch (cmdbuffer.address & 0xff) {
    case 0x03: // QUIT
      while (!IEC_CLOCK) ;
      set_data(1);
      return;

    case 0x06: // WRITE
      wheels_write_sector(cmdbuffer.track, cmdbuffer.sector, databuf);
      break;

    case 0x09: // READ
      wheels_read_sector(cmdbuffer.track, cmdbuffer.sector, databuf, 256);
      break;

    case 0x0c: // READLINK
      wheels_read_sector(cmdbuffer.track, cmdbuffer.sector, databuf, 2);
      break;

    case 0x0f: // STATUS
      wheels_transmit_status();
      break;

    case 0x12: // NATIVE_FREE
      wheels_native_free();
      break;

    case 0x15: // GET_CURRENT_PART_DIR
      wheels_get_current_part_dir();
      break;

    case 0x18: // SET_CURRENT_PART_DIR
      wheels_set_current_part_dir();
      break;

    case 0x1b: // CHECK_CHANGE
      wheels_check_diskchange();
      break;

    default:
      uart_puts_P(PSTR("unknown:\r\n"));
      uart_trace(&cmdbuffer, 0, 4);
      return;
    }

    set_busy_led(0);

    /* wait until clock is low */
    while (IEC_CLOCK && IEC_ATN) {
      if (check_keys()) {
        /* User-requested exit */
        return;
      }
    }
  }
}

#endif


/*
 *
 * Nippon Loader
 *
 */
#ifdef CONFIG_LOADER_NIPPON

/* protocol sync: wait for Clock low, if ATN is also low, then return signal to resync */
static uint8_t nippon_atn_clock_handshake(void) {
  if (IEC_ATN) {
    while(IEC_CLOCK) ;
    return 1;
  } else {
    set_clock(0);
    while(IEC_ATN) ;
    return 0;
  }
}


/* reads a byte from IEC, if loader is out of sync return false */
static uint8_t nippon_read_byte(uint8_t *b) {
  uint8_t tmp = 0, i;

  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    set_clock(1);
    set_data(1);
    delay_us(3); // allow for slow rise times
    for (i=8; i; i--) {
      if (! nippon_atn_clock_handshake())
        return 0;
      tmp = (tmp >> 1) | (IEC_DATA ? 0 : 128);
      while(!IEC_CLOCK) ;
    }
    set_clock(0);
    set_data(1);
    *b = tmp;
    return 1;
  }
  return 1; // not reached
}

/* sends a byte via IEC, if loader is out of sync return false */
static uint8_t nippon_send_byte(uint8_t b) {
  uint8_t i;

  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    set_clock(1);
    delay_us(3); // allow for slow rise times
    for (i=8; i; i--) {
      if (! nippon_atn_clock_handshake())
        return 0;
      set_data(b & 1);
      b = b >> 1;
      while(!IEC_CLOCK) ;
    }
    set_clock(0);
    set_data(1);
    return 1;
  }
  return 1; // not reached
}

/* nippon idle loop */
void load_nippon(UNUSED_PARAMETER) {
  uint8_t t, s, i=0, j;
  buffer_t *buf;

  /* init */
  uart_puts_P(PSTR("NIPPON"));
  set_atn_irq(0);
  buf = alloc_system_buffer();
  if (!buf) {
    uart_puts_P(PSTR("BUF ERR")); uart_putcrlf();
    return;
  }

  /* loop until IEC master sends a track greater than $80 = exit code */
  while (1) {

    /* initial state */
    /* timing is critical for ATN/CLK here, endless loop in $0bf0 at the cevi
     * raise ATN CLK quick, before setting LEDs output to serial console
     */
    set_data(1);
    set_clock(1);
    set_busy_led(0);
    uart_putcrlf(); uart_putc('L'); // idle loop entered

    /* wait for IEC master or human master to command us something */
    while(IEC_ATN && !(i = check_keys())) ;
    if (i)
      break; /* user requested exit */
    set_clock(0);
    set_busy_led(1);

    /* fetch command, sector and track, on failure resync/reinit protocol
     * if track > 128 exit loader
     * if sector > 128 read sector, else write */
    while(!IEC_ATN) ;
    if (! nippon_read_byte(&t))
      continue;
    uart_putc('T');
    uart_puthex(t);
    if (t & 128)
      break;

    if (! nippon_read_byte(&s))
      continue;
    uart_putc('S');
    uart_puthex(s & 0x7f);

    if (s & 128) {
      /* read sector */
      s &= 0x7f;
      uart_putc('R');
      read_sector(buf, current_part, t, s);
      i = 0;
      do {
        if (! nippon_send_byte(buf->data[i]))
          break;
        i++;
      } while (i);
    }
    else {
      /* write sector */
      uart_putc('W');
      i = 0;
      do {
        if (! (j = nippon_read_byte(&(buf->data[i]))))
          break;
        i++;
      } while (i);
      if (!j)
        break;
      write_sector(buf, current_part, t, s);
    }
  }

  /* exit */

  free_buffer(buf);
  uart_puts_P(PSTR("NEXT")); uart_putcrlf();
}
#endif

#ifdef CONFIG_LOADER_AR6
/*
 *
 * Action Replay 6 loaders/savers
 *
 */

/* 1581 loader */
void load_ar6_1581(UNUSED_PARAMETER) {
  buffer_t *buf;
  uint16_t i;

  buf = find_buffer(0);
  if (!buf) {
    /* The file should've been open? */
    return;
  }

  set_clock(0);
  set_data(1);
  delay_ms(1);

  while (1) {
    /* Send number of bytes in sector */
    ar6_1581_send_byte(buf->lastused-1);

    /* Send bytes in sector */
    for (i=2; i<=buf->lastused; i++)
      ar6_1581_send_byte(buf->data[i]);

    /* Check for end of file */
    if (buf->sendeoi)
      break;

    /* Read next sector */
    if (buf->refill(buf)) {
      /* Error, end transmission */
      break;
    }
  }

  /* Send end marker */
  ar6_1581_send_byte(0);
  delay_ms(1);
  set_clock(1);
  set_data(1);
}

/* 1581 saver */
void save_ar6_1581(UNUSED_PARAMETER) {
  buffer_t *buf;
  uint8_t i;

  buf = find_buffer(1);

  if (!buf) {
    /* File isn't open */
    return;
  }

  set_clock(0);
  set_data(1);
  delay_ms(1);

  do {
    mark_buffer_dirty(buf);

    /* Receive sector */
    i = 0;
    do {
      buf->data[i] = ar6_1581p_get_byte();
      i++;
    } while (i != 0);

    /* Set end */
    // FIXME: Although this works, it is not exactly clean:
    //        The code here should update lastused and mustflush.
    if (buf->data[0] == 0) {
      buf->position = buf->data[1];
    } else
      buf->position = 0;

    /* Write data */
    if (buf->refill(buf))
      break;
  } while (buf->data[0] != 0);

  cleanup_and_free_buffer(buf);
}

#endif


#ifdef PARALLEL_ENABLED
/*
 *
 *  Generic parallel speeder
 *
 */

/* parallel handshake interrupt handler */
PARALLEL_HANDLER {
  parallel_rxflag = 1;
}
#endif


#ifdef CONFIG_PARALLEL_DOLPHIN
/*
 *
 *  DolphinDOS
 *
 */

/**
 * _dolphin_getc - receive one byte from the parallel port (DD A816)
 *
 * This function tries to receive one byte via parallel and returns
 * it if successful. Returns -1 instead if the device state has
 * changed.
 */
static int16_t _dolphin_getc(void) {
  /* wait until CLOCK is high */
  while (!IEC_CLOCK)   // A818
    if (iec_check_atn())
      return -1;

  set_data(1);         // A81F

  /* start EOI timeout */
  start_timeout(86);

  /* wait until CLOCK is low or 86 microseconds passed */
  uint8_t tmp;
  do {
    if (iec_check_atn())
      return -1;
    tmp = has_timed_out();
  } while (!tmp && IEC_CLOCK);

  if (tmp) { // A835
    /* acknowledge EOI */
    set_data(0);
    delay_us(57);
    set_data(1);

    uart_putc('E');
    iec_data.iecflags |= EOI_RECVD;

    /* wait until CLOCK is low - A849 */
    while (IEC_CLOCK)
      if (iec_check_atn())
        return -1;
  }

  /* read byte */
  uint8_t b = parallel_read();
  parallel_send_handshake();

  set_data(0);
  return b;
}

/* disable interrupts in _dolphin_getc */
int16_t dolphin_getc(void) {
  int16_t val;

  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    val = _dolphin_getc();
  }
  return val;
}

/**
 * dolphin_putc - send a byte over parallel for DolphinDOS (A866)
 * @data    : byte to be sent
 * @with_eoi: Flags if the byte should be send with an EOI condition
 *
 * This is the DolphinDOS parallel byte transfer function.
 * Returns 0 normally or -1 if ATN is low.
 */
/* DolphinDOS parallel byte transfer - A866 */
uint8_t dolphin_putc(uint8_t data, uint8_t with_eoi) {
  set_clock(1);

  /* wait until DATA is high */
  while (!IEC_DATA)   // A870
    if (iec_check_atn())
      return -1;

  if (with_eoi) {
    /* signal EOI by waiting for a pulse on DATA */
    while (IEC_DATA)  // A87C
      if (iec_check_atn())
        return -1;

    while (!IEC_DATA) // A883
      if (iec_check_atn())
        return -1;
  }

  /* send byte - A88A */
  parallel_write(data);
  parallel_send_handshake();
  set_clock(0);

  /* wait until DATA is low */
  while (IEC_DATA)    // A89A
    if (iec_check_atn())
      return -1;

  return 0;
}

/* send a byte with hardware handshaking */
static void dolphin_write_hs(uint8_t value) {
  parallel_write(value);
  parallel_clear_rxflag();
  parallel_send_handshake();
  while (!parallel_rxflag) ;
}

/* DolphinDOS XQ command */
void load_dolphin(void) {
  /* find the already open buffer */
  buffer_t *buf = find_buffer(0);

  if (!buf)
    return;

  buf->position = 2;

  /* initial handshaking */
  // note about the delays: 100us work, not optimized
  // (doesn't matter much outside the loop)
  delay_us(100); // experimental delay
  parallel_set_dir(PARALLEL_DIR_OUT);
  set_clock(0);
  parallel_clear_rxflag();
  delay_us(100); // experimental delay
  parallel_send_handshake();
  uart_flush();
  delay_us(100); // experimental delay

  /* every sector except the last */
  uint8_t i;

  while (!buf->sendeoi) {
    iec_bus_t bus_state = iec_bus_read();

    /* transmit first byte */
    dolphin_write_hs(buf->data[2]);

    /* check DATA state before transmission */
    if (bus_state & IEC_BIT_DATA) {
      cleanup_and_free_buffer(buf);
      return;
    }

    /* transmit the rest of the sector */
    for (i = 3; i != 0; i++)
      dolphin_write_hs(buf->data[i]);

    /* read next sector */
    if (buf->refill(buf)) {
      cleanup_and_free_buffer(buf);
      return;
    }
  }

  /* last sector */
  i = 2;
  do {
    dolphin_write_hs(buf->data[i]);
  } while (i++ < buf->lastused);

  /* final handshake */
  set_clock(1);
  while (!IEC_DATA) ;
  parallel_send_handshake();
  parallel_set_dir(PARALLEL_DIR_IN);

  cleanup_and_free_buffer(buf);
}

/* DolphinDOS XZ command */
void save_dolphin(void) {
  buffer_t *buf;
  uint8_t eoi;

  /* find the already open file */
  buf = find_buffer(1);

  if (!buf)
    return;

  /* reset buffer position */
  buf->position = 2;
  buf->lastused = 2;

  /* experimental delay to avoid hangs */
  delay_us(100);

  /* handshaking */
  parallel_set_dir(PARALLEL_DIR_IN);
  set_data(0);
  parallel_clear_rxflag();
  parallel_send_handshake();
  uart_flush();

  /* receive data */
  do {
    /* flush buffer if full */
    if (buf->mustflush)
      if (buf->refill(buf))
        return; // FIXME: check error handling in Dolphin

    while (!parallel_rxflag) ;

    buf->data[buf->position] = parallel_read();
    mark_buffer_dirty(buf);

    if (buf->lastused < buf->position)
      buf->lastused = buf->position;
    buf->position++;

    /* mark for flushing on wrap */
    if (buf->position == 0)
      buf->mustflush = 1;

    eoi = !!IEC_CLOCK;

    parallel_clear_rxflag();
    parallel_send_handshake();
  } while (!eoi);

  /* the file will be closed with ATN+0xe1 by DolphinDOS */
}
#endif

#ifdef CONFIG_LOADER_MMZAK
/*
 *
 *  Maniac Mansion / Zak McKracken
 *
 */

/**
 * mmzak_send_byte - send one byte
 * @byte: value to transmit
 *
 * This function sends one byte with the MM/Zak protocol.
 * Returns false if successful, true if user aborted.
 */
static bool mmzak_send_byte(uint8_t byte) {
  for (uint8_t i = 0; i < 4; i++) {
    /* wait until ready */
    while (!IEC_CLOCK)
      if (check_keys())
        return true;

    /* send top bit */
    if (byte & 0x80)
      set_data(1);
    else
      set_data(0);

    byte <<= 1;

    /* wait until ready */
    while (IEC_CLOCK)
      if (check_keys())
        return true;

    /* send top bit */
    if (byte & 0x80)
      set_data(1);
    else
      set_data(0);

    byte <<= 1;
  }

  return false;
}

/**
 * mmzak_read_byte - receive one byte
 *
 * This function receives one byte with the MM/Zak protocol and
 * returns it if successful. Returns -1 instead if user aborted.
 */
static int16_t mmzak_read_byte(void) {
  uint8_t value = 0;

  for (uint8_t i = 0; i < 4; i++) {
    /* wait until clock is low */
    while (IEC_CLOCK)
      if (check_keys())
        return -1;

    value <<= 1;

    delay_us(3);
    if (!IEC_DATA)
      value |= 1;

    /* wait until clock is high */
    while (!IEC_CLOCK)
      if (check_keys())
        return -1;

    value <<= 1;

    delay_us(3);
    if (!IEC_DATA)
      value |= 1;
  }

  return value;
}

/**
 * mmzak_send_error - signal an error to the C64
 *
 * This function sends an error result to the C64.
 * Returns false if successful, true on user abort.
 */
static bool mmzak_send_error(void) {
  set_clock(1);
  set_data(1);
  if (mmzak_send_byte(0x01))
    return true;

  if (mmzak_send_byte(0x11))
    return true;

  return false;
}

/**
 * mmzak_read_sector - read and transmit a sector
 * @track : track number
 * @sector: sector number
 * @buf   : buffer to use
 *
 * This function reads the given sector and transmits it to the C64.
 * Returns false if successful, true on user abort.
 */
static bool mmzak_read_sector(uint8_t track, uint8_t sector, buffer_t *buf) {
  read_sector(buf, current_part, track, sector);
  if (current_error != 0) {
    /* read failed, send error */
    return mmzak_send_error();
  }

  set_clock(1);
  set_data(1);
  delay_us(3);

  /* send contents */
  uint8_t *ptr = buf->data;

  for (uint16_t i = 0; i < 256; i++) {
    if (*ptr == 0x01)
      if (mmzak_send_byte(0x01))
        return true;

    if (mmzak_send_byte(*ptr++))
      return true;
  }

  /* send status */
  if (mmzak_send_byte(0x01))
    return true;

  if (mmzak_send_byte(0x81))
    return true;

  set_clock(0);
  set_data(1);
    
  return false;
}

/**
 * mmzak_write_sector - receive and write a sector
 * @track : track number
 * @sector: sector number
 * @buf   : buffer to use
 *
 * This function receives a sector from the C64 and writes it to disk.
 * Returns false if successful, true on user abort.
 */
static bool mmzak_write_sector(uint8_t track, uint8_t sector, buffer_t *buf) {
  set_clock(1);
  set_data(1);
  delay_us(3);

  /* receive data */
  uint8_t *ptr = buf->data;
  mark_buffer_dirty(buf);

  for (uint16_t i = 0; i < 256; i++) {
    int16_t v = mmzak_read_byte();

    if (v < 0)
      return true;

    *ptr++ = v;
  }

  set_clock(0);

  /* write data */
  write_sector(buf, current_part, track, sector);
  mark_buffer_clean(buf);

  if (current_error != 0) {
    return mmzak_send_error();
  }

  return false;
}

void load_mmzak(UNUSED_PARAMETER) {
  buffer_t *buf = alloc_system_buffer();

  if (buf == NULL)
    return;

  set_atn_irq(0);

  /* initial handshake */
  /* FIXME: Not sure if needed, actually uses the ATN-ACK HW on a 1541 */
  for (uint8_t i = 0; i < 8; i++) {
    set_clock(1);
    set_data(0);
    delay_us(1285);
    set_data(1);
    delay_us(1290);
  }

  /* wait until bus is released */
  while ((iec_bus_read() & (IEC_BIT_CLOCK | IEC_BIT_DATA)) !=
         (IEC_BIT_CLOCK | IEC_BIT_DATA)) {
    if (check_keys())
      return;
  }

  /* command loop */
  bool done = false;

  while (!done) {
    int16_t v;
    uint8_t track, sector, command;

    /* signal our readyness */
    set_clock(0);
    set_data(1);
    set_busy_led(0);
    delay_us(3);

    /* wait for C64 */
    while (IEC_DATA) { // wait until data is low
      if (check_keys()) {
        done = true;
        break;
      }
    }

    if (done)
      break;

    set_clock(1);

    /* receive command block */
    v = mmzak_read_byte();
    if (v < 0)
      break;
    track = v;

    v = mmzak_read_byte();
    if (v < 0)
      break;
    sector = v;

    v = mmzak_read_byte();
    if (v < 0)
      break;
    command = v;

    set_busy_led(1);
    set_clock(0);

    /* check command */
    switch (command) {
    case 0x20:
      /* exit loader */
      done = true;
      break;

    case 0x30:
      /* read sector */
      if (mmzak_read_sector(track, sector, buf))
        done = true;
      break;

    case 0x40:
      /* write sector */
      if (mmzak_write_sector(track, sector, buf))
        done = true;
      break;

    default:
      /* unknown, signal error */
      if (mmzak_send_error())
        done = true;
      break;
    }
  }

  set_busy_led(0);
}
#endif // CONFIG_LOADER_MMZAK
