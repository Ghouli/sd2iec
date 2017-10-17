/* sd2iec - SD/MMC to Commodore serial bus interface/controller
   Copyright (C) 2007-2009  Ingo Korb <ingo@akana.de>
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


   doscmd.c: Command channel parser

*/

#include <util/delay.h>
#include <avr/eeprom.h>
#include <avr/wdt.h>
#include <avr/interrupt.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <util/crc16.h>
#include "config.h"
#include "dirent.h"
#include "diskchange.h"
#include "diskio.h"
#include "display.h"
#include "eeprom.h"
#include "errormsg.h"
#include "fastloader.h"
#include "d64ops.h"
#include "fatops.h"
#include "flags.h"
#include "iec.h"
#include "m2iops.h"
#include "parser.h"
#include "time.h"
#include "rtc.h"
#include "uart.h"
#include "ustring.h"
#include "utils.h"
#include "wrapops.h"
#include "doscmd.h"

#define CURSOR_RIGHT 0x1d

static void (*restart_call)(void) = 0;

typedef struct magic_value_s {
  uint16_t address;
  uint8_t  val[2];
} magic_value_t;

/* These are address/value pairs used by some programs to detect a 1541. */
/* Currently we remember two bytes per address since that's the longest  */
/* block required. */
static const PROGMEM magic_value_t c1541_magics[] = {
  { 0xfea0, { 0x0d, 0xed } }, /* used by DreamLoad and ULoad Model 3 */
  { 0xe5c6, { 0x34, 0xb1 } }, /* used by DreamLoad and ULoad Model 3 */
  { 0xfffe, { 0x00, 0x00 } }, /* Disable AR6 fastloader */
  { 0,      { 0, 0 } }        /* end mark */
};

#ifndef __AVR__
/* AVR uses GPIOR for this */
uint8_t globalflags;
#endif

uint8_t command_buffer[CONFIG_COMMAND_BUFFER_SIZE+2];
uint8_t command_length;

date_t date_match_start;
date_t date_match_end;

uint16_t datacrc = 0xffff;
uint8_t bcis_status = 0x0f; /* drive not ready */
uint8_t bcis_interleave = 5;

#ifdef CONFIG_STACK_TRACKING
uint16_t minstack = RAMEND;

void __cyg_profile_func_enter (void *this_fn, void *call_site) __attribute__((no_instrument_function));
void __cyg_profile_func_exit  (void *this_fn, void *call_site) __attribute__((alias("__cyg_profile_func_enter")));

void __cyg_profile_func_enter (void *this_fn, void *call_site) {
  if (SP < minstack) minstack = SP;
}
#endif

#if CONFIG_RTC_VARIANT > 0
/* Days of the week as used by the CMD FD */
static PROGMEM uint8_t downames[] = "SUN.MON.TUESWED.THURFRI.SAT.";

/* Skeleton of the ASCII time format */
static PROGMEM uint8_t asciitime_skel[] = " xx/xx/xx xx:xx:xx xM\r";
#endif

/* ------------------------------------------------------------------------- */
/*  Parsing helpers                                                          */
/* ------------------------------------------------------------------------- */

/* Fill the end of the command buffer with 0x00  */
/* so C string functions can work on file names. */

static void clean_cmdbuffer(void) {
  memset(command_buffer+command_length, 0, sizeof(command_buffer)-command_length);
}


/* Parse parameters of block commands in the command buffer */
/* Returns number of parameters (up to 4) or <0 on error    */
static int8_t parse_blockparam(uint8_t values[]) {
  uint8_t paramcount = 0;
  uint8_t *str;

  str = ustrchr(command_buffer, ':');
  if (!str) {
    if (ustrlen(command_buffer) < 3)
      return -1;
    str = command_buffer + 2;
  }

  str++;

  while (*str && paramcount < 4) {
    /* Skip all spaces, cursor-rights and commas - CC7C */
    while (*str == ' ' || *str == 0x1d || *str == ',') str++;
    if (!*str)
      break;

    values[paramcount++] = parse_number(&str);
  }

  return paramcount;
}

static uint8_t parse_bool(void) {
  switch (command_buffer[2]) {
  case '+':
    return 1;

  case '-':
    return 0;

  default:
    set_error(ERROR_SYNTAX_UNKNOWN);
    return 255;
  }
}

/* ------------------------------------------------------------------------- */
/*  Command handlers                                                         */
/* ------------------------------------------------------------------------- */

/* ------------------- */
/*  CD/MD/RD commands  */
/* ------------------- */

/* --- MD --- */
static void parse_mkdir(void) {
  path_t  path;
  uint8_t *name;

  /* MD requires a colon */
  if (!ustrchr(command_buffer, ':')) {
    set_error(ERROR_SYNTAX_NONAME);
    return;
  }
  if (parse_path(command_buffer+2, &path, &name, 0))
    return;
  mkdir(&path,name);
}

/* --- CD --- */
static void parse_chdir(void) {
  path_t  path;
  uint8_t *name;
  struct cbmdirent dent;

  if (parse_path(command_buffer+2, &path, &name, 1))
    return;

  if (ustrlen(name) != 0) {
    /* Path component after the : */
    if (name[0] == '_') {
      /* Going up a level - let chdir handle it. */
      if (chdir(&path,name))
        return;
    } else {
      /* A directory name - try to match it */
      if (first_match(&path, name, FLAG_HIDDEN, &dent))
        return;

      /* Move into it if it's a directory, use chdir if it's a file. */
      if ((dent.typeflags & TYPE_MASK) != TYPE_DIR) {
        if (chdir(&path, dent.name))
          return;
      } else {
        partition[path.part].current_dir = dent.fatcluster;
        display_current_directory(path.part, ustrlen(dent.name), dent.name);
      }
    }
  } else {
    if (ustrchr(command_buffer, '/')) {
      partition[path.part].current_dir = path.fat;
      if (display_found) {
        fat_getdirname(&path, dent.name);
        display_current_directory(path.part, ustrlen(dent.name), dent.name);
      }
    } else {
      set_error(ERROR_FILE_NOT_FOUND_39);
      return;
    }
  }

  if (globalflags & AUTOSWAP_ACTIVE)
    set_changelist(NULL, NULLSTRING);
}

/* --- RD --- */
static void parse_rmdir(void) {
  uint8_t *str;
  uint8_t res;
  uint8_t part;
  path_t  path;
  struct cbmdirent dent;

  /* No deletion across subdirectories */
  if (ustrchr(command_buffer, '/')) {
    set_error(ERROR_SYNTAX_NONAME);
    return;
  }

  /* Parse partition number */
  str = command_buffer+2;
  part = parse_partition(&str);
  if (*str != ':') {
    set_error(ERROR_SYNTAX_NONAME);
  } else {
    path.part = part;
    path.fat  = partition[part].current_dir;
    ustrcpy(dent.name, str+1);
    res = file_delete(&path, &dent);
    if (res != 255)
      set_error_ts(ERROR_SCRATCHED,res,0);
  }
}

/* --- CD/MD/RD subparser --- */
static void parse_dircommand(void) {
  clean_cmdbuffer();

  switch (command_buffer[0]) {
  case 'M':
    parse_mkdir();
    break;

  case 'C':
    parse_chdir();
    break;

  case 'R':
    parse_rmdir();
    break;

  default:
    set_error(ERROR_SYNTAX_UNKNOWN);
    break;
  }
}


/* ------------ */
/*  B commands  */
/* ------------ */
static void parse_block(void) {
  uint8_t  *str;
  buffer_t *buf;
  uint8_t  params[4];
  int8_t   pcount;

  str = ustrchr(command_buffer, '-');
  if (!str) {
    set_error(ERROR_SYNTAX_UNABLE);
    return;
  }

  memset(params,0,sizeof(params));
  pcount = parse_blockparam(params);
  if (pcount < 0)
    return;

  str++;
  switch (*str) {
  case 'R':
  case 'W':
    /* Block-Read  - CD56 */
    /* Block-Write - CD73 */
    buf = find_buffer(params[0]);
    if (!buf) {
      set_error(ERROR_NO_CHANNEL);
      return;
    }

    /* Use current partition for 0 */
    if (params[1] == 0)
      params[1] = current_part;

    if (*str == 'R') {
      read_sector(buf,params[1],params[2],params[3]);
      if (command_buffer[0] == 'B') {
        buf->position = 1;
        buf->lastused = buf->data[0];
      } else {
        buf->position = 0;
        buf->lastused = 255;
      }
    } else {
      if (command_buffer[0] == 'B')
        buf->data[0] = buf->position-1; // FIXME: Untested, verify!
      write_sector(buf,params[1],params[2],params[3]);
    }
    break;

  case 'P':
    /* Buffer-Position - CDBD */
    buf = find_buffer(params[0]);
    if (!buf) {
      set_error(ERROR_NO_CHANNEL);
      return;
    }
    if (buf->pvt.buffer.size != 1) {
      /* Extended position for large buffers */
      uint8_t count = params[2];

      /* Walk the chain, wrap whenever necessary */
      buf->secondary = BUFFER_SEC_CHAIN - params[0];
      buf = buf->pvt.buffer.first;
      while (count--) {
        if (buf->pvt.buffer.next != NULL)
          buf = buf->pvt.buffer.next;
        else
          buf = buf->pvt.buffer.first;
      }
      buf->secondary = params[0];
      buf->mustflush = 0;
    }
    buf->position = params[1];
    break;

  default:
    set_error(ERROR_SYNTAX_UNABLE);
    return;
  }
}


/* ---------- */
/*  C - Copy  */
/* ---------- */
static void parse_copy(void) {
  path_t srcpath,dstpath;
  uint8_t *srcname,*dstname,*tmp;
  uint8_t savedtype;
  int8_t res;
  buffer_t *srcbuf,*dstbuf;
  struct cbmdirent dent;

  clean_cmdbuffer();

  /* Find the = */
  srcname = ustrchr(command_buffer,'=');
  if (srcname == NULL) {
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }
  *srcname++ = 0;

  /* Parse the destination name */
  if (parse_path(command_buffer+1, &dstpath, &dstname, 0))
    return;

  if (ustrlen(dstname) == 0) {
    set_error(ERROR_SYNTAX_NONAME);
    return;
  }

  /* Check for invalid characters in the destination name */
  if (check_invalid_name(dstname)) {
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }

  /* Check if the destination file exists */
  res = first_match(&dstpath, dstname, FLAG_HIDDEN, &dent);
  if (res == 0) {
    set_error(ERROR_FILE_EXISTS);
    return;
  }

  if (res > 0)
    return;

  set_error(ERROR_OK);

  srcbuf = alloc_buffer();
  dstbuf = alloc_buffer();
  if (srcbuf == NULL || dstbuf == NULL)
    return;

  savedtype = 0;
  srcname = ustr1tok(srcname,',',&tmp);
  while (srcname != NULL) {
    /* Parse the source path */
    if (parse_path(srcname, &srcpath, &srcname, 0))
      goto cleanup;

    /* Open the current source file */
    res = first_match(&srcpath, srcname, FLAG_HIDDEN, &dent);
    if (res != 0)
      goto cleanup;

    /* Note: A 1541 can't copy REL files. We try to do better. */
    if ((dent.typeflags & TYPE_MASK) == TYPE_REL) {
      if (savedtype != 0 && savedtype != TYPE_REL) {
        set_error(ERROR_FILE_TYPE_MISMATCH);
        goto cleanup;
      }
      open_rel(&srcpath, &dent, srcbuf, 0, 1);
    } else {
      if (savedtype != 0 && savedtype == TYPE_REL) {
        set_error(ERROR_FILE_TYPE_MISMATCH);
        goto cleanup;
      }
      open_read(&srcpath, &dent, srcbuf);
    }

    if (current_error != 0)
      goto cleanup;

    /* Open the destination file (first source only) */
    if (savedtype == 0) {
      savedtype = dent.typeflags & TYPE_MASK;
      memset(&dent, 0, sizeof(dent));
      ustrncpy(dent.name, dstname, CBM_NAME_LENGTH);
      if (savedtype == TYPE_REL)
        open_rel(&dstpath, &dent, dstbuf, srcbuf->recordlen, 1);
      else
        open_write(&dstpath, &dent, savedtype, dstbuf, 0);
    }

    while (1) {
      uint8_t tocopy;

      if (savedtype == TYPE_REL)
        tocopy = srcbuf->recordlen;
      else
        tocopy = 256-dstbuf->position;

      if (tocopy > (srcbuf->lastused - srcbuf->position+1))
        tocopy = srcbuf->lastused - srcbuf->position + 1;

      if (tocopy > 256-dstbuf->position)
        tocopy = 256-dstbuf->position;

      memcpy(dstbuf->data + dstbuf->position,
             srcbuf->data + srcbuf->position,
             tocopy);
      dstbuf->dirty     = 1;
      srcbuf->position += tocopy-1;  /* add 1 less, simplifies the test later */
      dstbuf->position += tocopy;
      dstbuf->lastused  = dstbuf->position-1;

      /* End if we just copied the last data block */
      if (srcbuf->sendeoi && srcbuf->position == srcbuf->lastused)
        break;

      /* Refill the buffers if required */
      if (srcbuf->recordlen || srcbuf->position++ == srcbuf->lastused)
        if (srcbuf->refill(srcbuf))
          goto cleanup;

      if (dstbuf->recordlen || dstbuf->position == 0)
        if (dstbuf->refill(dstbuf))
          goto cleanup;
    }

    /* Close current source file */
    srcbuf->cleanup(srcbuf);

    /* Free and reallocate the buffer. This is required because most of the  */
    /* file_open code assumes that it will get a "pristine" buffer with      */
    /* 0 is most of the fields. Allocation cannot fail at this point because */
    /* there is at least one free buffer.                                    */
    free_buffer(srcbuf);
    srcbuf = alloc_buffer();

    /* Next file */
    srcname = ustr1tok(NULL,',',&tmp);
  }

  cleanup:
  /* Close the buffers */
  dstbuf->cleanup(dstbuf);
  srcbuf->cleanup(srcbuf);
}


/* ----------------------- */
/*  CP - Change Partition  */
/* ----------------------- */
static void parse_changepart(void) {
  uint8_t *str;
  uint8_t part;

  switch(command_buffer[1]) {
  case 'P':
    clean_cmdbuffer();
    str  = command_buffer + 2;
    part = parse_partition(&str);
    break;

  case 0xd0: /* Shift-P */
    /* binary version */
    part = command_buffer[2] - 1;
    break;
  }

  if(part>=max_part) {
    set_error_ts(ERROR_PARTITION_ILLEGAL,part+1,0);
    return;
  }

  current_part=part;
  if (globalflags & AUTOSWAP_ACTIVE)
    set_changelist(NULL, NULLSTRING);

  display_current_part(current_part);

  set_error_ts(ERROR_PARTITION_SELECTED, part+1, 0);
}


/* ------------ */
/*  D commands  */
/* ------------ */
static void parse_direct(void) {
  buffer_t *buf;
  uint8_t drive;
  uint32_t sector;
  DRESULT res;

  /* This also guards against attempts to use the old Duplicate command. */
  /* Its syntax is D1=0, so buffer[2] would never have a value that is   */
  /* a valid secondary address.                                          */
  buf = find_buffer(command_buffer[2]);
  if (!buf) {
    set_error(ERROR_NO_CHANNEL);
    return;
  }

  if (buf->pvt.buffer.size > 1) {
    uint8_t oldsec = buf->secondary;
    buf->secondary = BUFFER_SEC_CHAIN - oldsec;
    buf = buf->pvt.buffer.first;
    buf->secondary = oldsec;
  }

  buf->position = 0;
  buf->lastused = 255;

  drive = command_buffer[3];
  sector = *((uint32_t *)(command_buffer+4));

  switch (command_buffer[1]) {
  case 'I':
    /* Get information */
    memset(buf->data,0,256);
    if (disk_getinfo(drive, command_buffer[4], buf->data) != RES_OK) {
      set_error(ERROR_DRIVE_NOT_READY);
      return;
    }
    break;

  case 'R':
    /* Read sector */
    if (buf->pvt.buffer.size < 2) { // FIXME: Assumes 512-byte sectors
      set_error(ERROR_BUFFER_TOO_SMALL);
      return;
    }
    res = disk_read(drive, buf->data, sector, 1);
    switch (res) {
    case RES_OK:
      return;

    case RES_ERROR:
      set_error(ERROR_READ_NOHEADER); // Any random READ ERROR
      return;

    case RES_PARERR:
    case RES_NOTRDY:
    default:
      set_error_ts(ERROR_DRIVE_NOT_READY,res,0);
      return;
    }

  case 'W':
    /* Write sector */
    if (buf->pvt.buffer.size < 2) { // FIXME: Assumes 512-byte sectors
      set_error(ERROR_BUFFER_TOO_SMALL);
      return;
    }
    res = disk_write(drive, buf->data, sector, 1);
    switch(res) {
    case RES_OK:
      return;

    case RES_WRPRT:
      set_error(ERROR_WRITE_PROTECT);
      return;

    case RES_ERROR:
      set_error(ERROR_WRITE_VERIFY);
      return;

    case RES_NOTRDY:
    case RES_PARERR:
    default:
      set_error_ts(ERROR_DRIVE_NOT_READY,res,0);
      return;
    }

  default:
    set_error(ERROR_SYNTAX_UNABLE);
    break;
  }
}


/* ------------ */
/*  E commands  */
/* ------------ */

/* --- E-R --- */
static void handle_eeread(uint16_t address, uint8_t length) {
  if (length > CONFIG_ERROR_BUFFER_SIZE) {
    set_error(ERROR_SYNTAX_TOOLONG);
    return;
  }

  buffers[CONFIG_BUFFER_COUNT].position = 0;
  buffers[CONFIG_BUFFER_COUNT].lastused = length-1;

  uint8_t *ptr = error_buffer;
  while (length--)
    *ptr++ = eeprom_read_byte((uint8_t *)(CONFIG_EEPROM_OFFSET + address++));
}

/* --- E-W --- */
static void handle_eewrite(uint16_t address, uint8_t length) {
  uint8_t *ptr = command_buffer+6;
  while (length--)
    eeprom_write_byte((uint8_t *)(CONFIG_EEPROM_OFFSET + address++), *ptr++);
}

/* --- E subparser --- */
static void parse_eeprom(void) {
  uint16_t address = command_buffer[3] + (command_buffer[4] << 8);
  uint8_t  length  = command_buffer[5];

  if (command_length < 6) {
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }

  if (command_buffer[1] != '-' || (command_buffer[2] != 'W' && command_buffer[2] != 'R'))
    set_error(ERROR_SYNTAX_UNKNOWN);

  if (address > CONFIG_EEPROM_SIZE || address+length > CONFIG_EEPROM_SIZE) {
    set_error(ERROR_SYNTAX_TOOLONG);
    return;
  }

  if (command_buffer[2] == 'W')
    handle_eewrite(address, length);
  else
    handle_eeread(address, length);
}


/* -------------------------- */
/*  G-P - Get Partition info  */
/* -------------------------- */
static void parse_getpartition(void) {
  uint8_t *ptr;
  path_t path;

  if (command_length < 3) /* FIXME: should this set an error? */
    return;

  if (command_buffer[1] != '-' || command_buffer[2] != 'P') {
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }

  if (command_length == 3)
    path.part = current_part+1;
  else
    path.part = command_buffer[3];

  /* Valid partition number? */
  if (path.part >= max_part) {
    set_error(ERROR_PARTITION_ILLEGAL);
    return;
  }

  buffers[CONFIG_BUFFER_COUNT].position = 0;
  buffers[CONFIG_BUFFER_COUNT].lastused = 31;
  ptr=buffers[CONFIG_BUFFER_COUNT].data;
  memset(ptr,0,32);
  *(ptr++) = 1; /* Partition type: native */
  ptr++;

  *(ptr++) = path.part+1;
  path.fat=0;
  if (disk_label(&path,ptr))
    return;
  ptr += 16;
  *(ptr++) = partition[path.part].fatfs.fatbase>>16;
  *(ptr++) = partition[path.part].fatfs.fatbase>>8;
  *(ptr++) = (partition[path.part].fatfs.fatbase & 0xff);
  ptr++;

  uint32_t size = (partition[path.part].fatfs.max_clust - 1) * partition[path.part].fatfs.csize;
  *(ptr++) = size>>16;
  *(ptr++) = size>>8;
  *(ptr++) = size;
  *ptr = 13;
}


/* ---------------- */
/*  I - Initialize  */
/* ---------------- */
static void parse_initialize(void) {
  if (disk_state != DISK_OK)
    set_error_ts(ERROR_READ_NOSYNC,18,0);
  else
    free_multiple_buffers(FMB_USER_CLEAN);
}


/* ------------ */
/*  M commands  */
/* ------------ */

/* --- M-E --- */
static void handle_memexec(void) {
  uint16_t address;

  if (command_length < 5)
    return;

  if (detected_loader == FL_NONE) {
    uart_puts_P(PSTR("M-E at "));
    uart_puthex(command_buffer[4]);
    uart_puthex(command_buffer[3]);
    uart_puts_P(PSTR(", CRC "));
    uart_puthex(datacrc >> 8);
    uart_puthex(datacrc & 0xff);
    uart_putcrlf();
  }
  datacrc = 0xffff;

  address = command_buffer[3] + (command_buffer[4]<<8);
#ifdef CONFIG_LOADER_TURBODISK
  if (detected_loader == FL_TURBODISK && address == 0x0303) {
    /* Looks like Turbodisk */
    load_turbodisk();
  }
#endif
#ifdef CONFIG_LOADER_FC3
  if (detected_loader == FL_FC3_LOAD &&
      (address == 0x059a || address == 0x0400)) {
    /* FC3 LOAD uses 0x059a, EXOS uses 0x0400 */
    load_fc3(0);
  }
  if (detected_loader == FL_FC3_SAVE && address == 0x059c) {
    save_fc3();
  }
  if (detected_loader == FL_FC3_FREEZED && address == 0x0403) {
    load_fc3(1);
  }
#endif
#ifdef CONFIG_LOADER_DREAMLOAD
  if (detected_loader == FL_DREAMLOAD && address == 0x0700) {
    load_dreamload();
  }
#endif
#ifdef CONFIG_LOADER_ULOAD3
  if (detected_loader == FL_ULOAD3 && address == 0x0336) {
    load_uload3();
  }
#endif

  detected_loader = FL_NONE;
}

/* --- M-R --- */
static void handle_memread(void) {
  uint16_t address, check;
  magic_value_t *p;

  if (command_length < 6)
    return;

  address = command_buffer[3] + (command_buffer[4]<<8);

  /* Check some special addresses used for drive detection. */
  p = (magic_value_t*) c1541_magics;
  while ( (check = pgm_read_word(&p->address)) ) {
    if (check == address) {
      error_buffer[0] = pgm_read_byte(p->val);
      error_buffer[1] = pgm_read_byte(p->val + 1);
      break;
    }
    p++;
  }

  /* possibly the host wants to read more bytes than error_buffer size */
  /* we ignore this knowing that we return nonsense in this case       */
  buffers[CONFIG_BUFFER_COUNT].data     = error_buffer;
  buffers[CONFIG_BUFFER_COUNT].position = 0;
  buffers[CONFIG_BUFFER_COUNT].lastused = command_buffer[5]-1;
}

/* --- M-W --- */
static void handle_memwrite(void) {
  uint16_t address;
  uint8_t  length,i;

  if (command_length < 6)
    return;

  address = command_buffer[3] + (command_buffer[4]<<8);
  length  = command_buffer[5];

  if (address == 119) {
    /* Change device address, 1541 style */
    device_address = command_buffer[6] & 0x1f;
    display_address(device_address);
    return;
  }

  if (address == 0x1c06 || address == 0x1c07) {
    /* Ignore attempts to increase the VIA timer frequency */
    return;
  }

#ifdef CONFIG_LOADER_TURBODISK
  /* Turbodisk sends the filename in the last M-W, check the previous CRC */
  if (datacrc == 0x9c9f) {
    detected_loader = FL_TURBODISK;
  } else
#endif
    detected_loader = FL_NONE;


  for (i=0;i<command_buffer[5];i++)
    datacrc = _crc16_update(datacrc, command_buffer[i+6]);

#ifdef CONFIG_LOADER_FC3
  if (datacrc == 0x6510 || datacrc == 0x7e38) {
    /* 0x6510 is a FC3 cart, 0x7e38 is a protocol-compatible EXOS v3 kernal */
    detected_loader = FL_FC3_LOAD;
  }
  else if (datacrc == 0x2c86) {
    detected_loader = FL_FC3_SAVE;
  }
  else if (datacrc == 0x9930) {
    /* Feel free to change the CRC to 0x9e56 or 0xdf44 if you find a version */
    /* that doesn't upload as much junk at the end as the one I analyzed.    */
    detected_loader = FL_FC3_FREEZED;
  }
#endif

#ifdef CONFIG_LOADER_DREAMLOAD
  if (datacrc == 0x2e69) {
    detected_loader = FL_DREAMLOAD;
  }
#endif

#ifdef CONFIG_LOADER_ULOAD3
  if (datacrc == 0xdd81) {
    detected_loader = FL_ULOAD3;
  }
#endif

  if (detected_loader == FL_NONE) {
    uart_puts_P(PSTR("M-W CRC result: "));
    uart_puthex(datacrc >> 8);
    uart_puthex(datacrc & 0xff);
    uart_putcrlf();
  }
}

/* --- M subparser --- */
static void parse_memory(void) {
  if (command_buffer[2] == 'W')
    handle_memwrite();
  else if (command_buffer[2] == 'E')
    handle_memexec();
  else if (command_buffer[2] == 'R')
    handle_memread();
  else
    set_error(ERROR_SYNTAX_UNKNOWN);
}

/* --------- */
/*  N - New  */
/* --------- */
static void parse_new(void) {
  uint8_t *name, *id;
  uint8_t part;

  clean_cmdbuffer();

  name = command_buffer+1;
  part = parse_partition(&name);
  name = ustrchr(command_buffer, ':');
  if (name++ == NULL) {
    set_error(ERROR_SYNTAX_NONAME);
    return;
  }

  id = ustrchr(name, ',');
  if (id != NULL) {
    *id = 0;
    id++;
  }

  format(part, name, id);
}


/* -------------- */
/*  P - Position  */
/* -------------- */
static void parse_position(void) {
  buffer_t *buf;
  uint8_t hi = 0, lo, pos;

  if(command_length < 2 || (buf = find_buffer(command_buffer[1] & 0x0f)) == NULL) {
    set_error(ERROR_NO_CHANNEL);
    return;
  }

  lo = pos = (buf->recordlen? 1:0); // REL file start indexes at one.

  if(command_length > 1)
    lo = command_buffer[2];
  if(command_length > 2)
    hi = command_buffer[3];
  if(command_length > 3) {
    pos = command_buffer[4];
    if(buf->recordlen && pos >= buf->recordlen) {
      set_error(ERROR_RECORD_OVERFLOW);
      return;
    }
  }

  if (buf->seek == NULL) {
    set_error(ERROR_SYNTAX_UNABLE);
    return;
  }

  if(buf->recordlen) { // REL files start indexes at 1.
    lo--;
    pos--;
  }
  buf->seek(buf,(hi * 256UL + lo) * (uint32_t)(buf->recordlen ? buf->recordlen : 256),pos);
}


/* ------------ */
/*  R - Rename  */
/* ------------ */
static void parse_rename(void) {
  path_t oldpath,newpath;
  uint8_t *oldname,*newname;
  struct cbmdirent dent;
  int8_t res;

  clean_cmdbuffer();

  /* Find the boundary between the names */
  oldname = ustrchr(command_buffer,'=');
  if (oldname == NULL) {
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }
  *oldname++ = 0;

  /* Parse both names */
  if (parse_path(command_buffer+1, &newpath, &newname, 0))
    return;

  if (parse_path(oldname, &oldpath, &oldname, 0))
    return;

  /* Rename can't move files across directories */
  if (oldpath.fat != newpath.fat) {
    set_error(ERROR_FILE_NOT_FOUND);
    return;
  }

  /* Check for invalid characters in the new name */
  if (check_invalid_name(newname)) {
    /* This isn't correct for all cases, but for most. */
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }

  /* Don't allow an empty new name */
  /* The 1541 renames the file to "=" in this case, but I consider that a bug. */
  if (ustrlen(newname) == 0) {
    set_error(ERROR_SYNTAX_NONAME);
    return;
  }

  /* Check if the new name already exists */
  res = first_match(&newpath, newname, FLAG_HIDDEN, &dent);
  if (res == 0) {
    set_error(ERROR_FILE_EXISTS);
    return;
  }

  if (res > 0)
    /* first_match generated an error other than File Not Found, abort */
    return;

  /* Clear the FNF */
  set_error(ERROR_OK);

  /* Check if the old name exists */
  if (first_match(&oldpath, oldname, FLAG_HIDDEN, &dent))
    return;

  rename(&oldpath, &dent, newname);
}


/* ------------- */
/*  S - Scratch  */
/* ------------- */
static void parse_scratch(void) {
  struct cbmdirent dent;
  int8_t  res;
  uint8_t count,cnt;
  uint8_t *filename,*tmp,*name;
  path_t  path;

  clean_cmdbuffer();

  filename = ustr1tok(command_buffer+1,',',&tmp);

  count = 0;
  /* Loop over all file names */
  while (filename != NULL) {
    parse_path(filename, &path, &name, 0);

    if (opendir(&matchdh, &path))
      return;

    while (1) {
      res = next_match(&matchdh, name, NULL, NULL, FLAG_HIDDEN, &dent);
      if (res < 0)
        break;
      if (res > 0)
        return;

      /* Skip directories */
      if ((dent.typeflags & TYPE_MASK) == TYPE_DIR)
        continue;
      cnt = file_delete(&path, &dent);
      if (cnt != 255)
        count += cnt;
      else
        return;
    }

    filename = ustr1tok(NULL,',',&tmp);
  }

  set_error_ts(ERROR_SCRATCHED,count,0);
}


#if CONFIG_RTC_VARIANT > 0
/* ------------------ */
/*  T - Time commands */
/* ------------------ */

/* --- T-R --- */
static void parse_timeread(void) {
  struct tm time;
  uint8_t *ptr = error_buffer;
  uint8_t hour;

  if (rtc_state != RTC_OK) {
    set_error(ERROR_SYNTAX_UNABLE);
    return;
  }

  read_rtc(&time);
  hour = time.tm_hour % 12;
  if (hour == 0) hour = 12;

  switch (command_buffer[3]) {
  case 'A': /* ASCII format */
    buffers[CONFIG_BUFFER_COUNT].lastused = 25;
    memcpy_P(error_buffer+4, asciitime_skel, sizeof(asciitime_skel));
    memcpy_P(error_buffer, downames + 4*time.tm_wday, 4);
    appendnumber(error_buffer+5, time.tm_mon+1);
    appendnumber(error_buffer+8, time.tm_mday);
    appendnumber(error_buffer+11, time.tm_year % 100);
    appendnumber(error_buffer+14, hour);
    appendnumber(error_buffer+17, time.tm_min);
    appendnumber(error_buffer+20, time.tm_sec);
    if (time.tm_hour < 12)
      error_buffer[23] = 'A';
    else
      error_buffer[23] = 'P';
    break;

  case 'B': /* BCD format */
    buffers[CONFIG_BUFFER_COUNT].lastused = 8;
    *ptr++ = time.tm_wday;
    *ptr++ = int2bcd(time.tm_year % 100);
    *ptr++ = int2bcd(time.tm_mon+1);
    *ptr++ = int2bcd(time.tm_mday);
    *ptr++ = int2bcd(hour);
    *ptr++ = int2bcd(time.tm_min);
    *ptr++ = int2bcd(time.tm_sec);
    *ptr++ = (time.tm_hour >= 12);
    *ptr   = 13;
    break;

  case 'D': /* Decimal format */
    buffers[CONFIG_BUFFER_COUNT].lastused = 8;
    *ptr++ = time.tm_wday;
    *ptr++ = time.tm_year;
    *ptr++ = time.tm_mon+1;
    *ptr++ = time.tm_mday;
    *ptr++ = hour;
    *ptr++ = time.tm_min;
    *ptr++ = time.tm_sec;
    *ptr++ = (time.tm_hour >= 12);
    *ptr   = 13;
    break;

  default: /* Unknown format */
    set_error(ERROR_SYNTAX_UNKNOWN);
    break;
  }
}

/* --- T-W --- */
static void parse_timewrite(void) {
  struct tm time;
  uint8_t i, *ptr;

  switch (command_buffer[3]) {
  case 'A': /* ASCII format */
    if (command_length < 27) { // Allow dropping the AM/PM marker for 24h format
      set_error(ERROR_SYNTAX_UNABLE);
      return;
    }
    for (i=0;i<7;i++) {
      if (memcmp_P(command_buffer+4, downames + 4*i, 4) == 0)
        break;
    }
    if (i == 7) {
      set_error(ERROR_SYNTAX_UNKNOWN); // FIXME: Check the real error
      return;
    }
    time.tm_wday = i;
    ptr = command_buffer + 9;
    time.tm_mon  = parse_number(&ptr)-1;
    ptr++;
    time.tm_mday = parse_number(&ptr);
    ptr++;
    time.tm_year = parse_number(&ptr);
    ptr++;
    time.tm_hour = parse_number(&ptr);
    ptr++;
    time.tm_min  = parse_number(&ptr);
    ptr++;
    time.tm_sec  = parse_number(&ptr);
    if (command_buffer[28] == 'M') {
      /* Adjust for AM/PM only if AM/PM is actually supplied */
      if (time.tm_hour == 12)
        time.tm_hour = 0;
      if (command_buffer[27] == 'P')
        time.tm_hour += 12;
    }
    break;

  case 'B': /* BCD format */
    if (command_length < 12) {
      set_error(ERROR_SYNTAX_UNABLE);
      return;
    }
    time.tm_wday = command_buffer[4];
    time.tm_year = bcd2int(command_buffer[5]);
    time.tm_mon  = bcd2int(command_buffer[6])-1;
    time.tm_mday = bcd2int(command_buffer[7]);
    time.tm_hour = bcd2int(command_buffer[8]);
    /* Hour range is 1-12, change 12:xx to 0:xx for easier conversion */
    if (time.tm_hour == 12)
      time.tm_hour = 0;
    time.tm_min  = bcd2int(command_buffer[9]);
    time.tm_sec  = bcd2int(command_buffer[10]);
    if (command_buffer[11])
      time.tm_hour += 12;
    break;

  case 'D': /* Decimal format */
    if (command_length < 12) {
      set_error(ERROR_SYNTAX_UNABLE);
      return;
    }
    time.tm_wday = command_buffer[4];
    time.tm_year = command_buffer[5];
    time.tm_mon  = command_buffer[6]-1;
    time.tm_mday = command_buffer[7];
    time.tm_hour = command_buffer[8];
    /* Hour range is 1-12, change 12:xx to 0:xx for easier conversion */
    if (time.tm_hour == 12)
      time.tm_hour = 0;
    time.tm_min  = command_buffer[9];
    time.tm_sec  = command_buffer[10];
    if (command_buffer[11])
      time.tm_hour += 12;
    break;

  default: /* Unknown format */
    set_error(ERROR_SYNTAX_UNKNOWN);
    return;
  }

  /* Y2K fix for legacy apps */
  if (time.tm_year < 80)
    time.tm_year += 100;

  /* The CMD drives don't check for validity, we do - partially */
  if (time.tm_mday ==  0 || time.tm_mday >  31 ||
      time.tm_mon  >  11 ||
      time.tm_wday >   6 ||
      time.tm_hour >  23 ||
      time.tm_min  >  59 ||
      time.tm_sec  >  59) {
    set_error(ERROR_SYNTAX_UNABLE);
    return;
  }

  set_rtc(&time);
}

/* --- T subparser --- */
static void parse_time(void) {
  if (rtc_state == RTC_NOT_FOUND)
    set_error(ERROR_SYNTAX_UNKNOWN);
  else {
    if (command_buffer[2] == 'R') {
      parse_timeread();
    } else if (command_buffer[2] == 'W') {
      parse_timewrite();
    } else
      set_error(ERROR_SYNTAX_UNKNOWN);
  }
}
#endif /* CONFIG_RTC_VARIANT */


/* ------------ */
/*  U commands  */
/* ------------ */
static void parse_user(void) {
  switch (command_buffer[1]) {
  case 'A':
  case '1':
    /* Tiny little hack: Rewrite as (B)-R and call that                */
    /* This will always work because there is either a : in the string */
    /* or the drive will start parsing at buf[3].                      */
    command_buffer[0] = '-';
    command_buffer[1] = 'R';
    parse_block();
    break;

  case 'B':
  case '2':
    /* Tiny little hack: see above case for rationale */
    command_buffer[0] = '-';
    command_buffer[1] = 'W';
    parse_block();
    break;

  case 'I':
  case '9':
    if (command_length == 2) {
      /* Soft-reset - just return the dos version */
      set_error(ERROR_DOSVERSION);
      return;
    }
    switch (command_buffer[2]) {
    case '+':
      globalflags &= (uint8_t)~VC20MODE;
      break;

    case '-':
      globalflags |= VC20MODE;
      break;

    default:
      set_error(ERROR_SYNTAX_UNKNOWN);
      break;
    }
    break;

  case 'J':
  case ':':
    /* Reset - technically hard-reset */
    /* Faked because Ultima 5 sends UJ. */
    free_multiple_buffers(FMB_USER);
    set_error(ERROR_DOSVERSION);
    break;

  case 202: /* Shift-J */
    /* The real hard reset command */
    cli();
    restart_call();
    break;

  case '0':
    /* U0 Commands -- FIXME a seperate parser ?
      all parameters quoted from 1571 source code "Fastutl.src" */
    switch (command_buffer[2] & 0x1f) {
    case 0:
    case 0x10: /* Burst Read Sector(s) ($8371)
       02	T	E	B	S	0	0	0   N
       03   DESTINATION TRACK
       04	DESTINATION SECTOR
       05	NUMBER OF SECTORS
       06	NEXT TRACK (OPTIONAL)
    	T - TRANSFER DATA (1=NO TRANSFER)
	    E - IGNORE ERROR (1=IGNORE)
	    B - BUFFER TRANSFER ONLY (1=BUFFER TRANSFER ONLY)
	    S - SIDE SELECT (MFM ONLY)
	    N - DRIVE NUMBER */
		/* We only get here if N (drive#) = 0
			Ignore T (no transfer) until buffer open ('#0') is fixed
			Ignore B (transfer only) until buffer open ('#0') is fixed
			Ignore E ... FIXME
			Ignore S until MFM disk images supported ... FIXME .D81 ??
			Ignore 06 (next track) because we do not have a head to move
		*/
		if (command_length < 6) {
			/* FIXME ? 1571 doesn't check, we do */
			b_out_burstload(0, (bcis_status & 0xf0) | 0xe); /* syntax error */
		    set_error(ERROR_SYNTAX_UNABLE);
		} else {
			fl_track = command_buffer[3];
			fl_sector = command_buffer[4];
			s_out_burstload(command_buffer[5]);
		}
        break;
    case 0x2:
    case 0x12: /* Burst Write Sector(s) ($83EC)
       02	T	E	B	S	0	0	1   N
       03	DESTINATION TRACK
       04	DESTINATION SECTOR
       05	NUMBER OF SECTORS
       06	NEXT TRACK (OPTIONAL)
    	T - TRANSFER DATA (1=NO TRANSFER)
    	E - IGNORE ERROR (1=IGNORE)
    	B - BUFFER TRANSFER ONLY (1=BUFFER TRANSFER ONLY)
    	S - SIDE SELECT (MFM ONLY)
    	N - DRIVE NUMBER */
		if (command_length < 6) {
			/* FIXME ? 1571 doesn't check, we do */
			b_out_burstload(0, (bcis_status & 0xf0) | 0xe); /* syntax error */
		    set_error(ERROR_SYNTAX_UNABLE);
		} else {
			fl_track = command_buffer[3];
			fl_sector = command_buffer[4];
			s_in_burstload(command_buffer[5]);
		}
		break;
    case 0x4:
    case 0x14: /* Burst Inquire Disk ($848B)
       02	X	X	X	S	0	1	0   N
    	S - SIDE SELECT (MFM ONLY)
    	N - DRIVE NUMBER 
    	X - DON'T CARE */
      switch (partition[current_part].imagetype & D64_TYPE_MASK) {
		  /* this assumes a readable card is in the device! */
		  /* FIXME: 512 sectors for FAT and D81 */
	  case D64_TYPE_D41:
	  case D64_TYPE_D71:
	      bcis_status = 0x01; /* okay, native CBM disk (implied sector size 256) */
		  break;
	  case D64_TYPE_D81:      /* FIXME */
	      bcis_status = 0x2F; /* error, native CBM disk + 512 sector size */
		  break;
	  case D64_TYPE_NONE:     /* FAT - FIXME */
	      bcis_status = 0xAF; /* error, foreign disk + 512 sector size */
		  break;
	  default:                /* DNP, M2I ... FIXME */
	      bcis_status = 0x9F; /* error, foreign disk + 256 sector size */
	  }
      b_out_burstload(0, bcis_status); /* send status only */
      break;
    case 0x6:
    case 0x16: /* Burst Format ($84B7)
       02	P	I	D	S	0	1	1   N
       03   M   T   LOGICAL STARTING SECTOR
       04	-INTERLEAVE (OPTIONAL DEF-0)-
       05   SECTOR SIZE	 * (OPTIONAL 01 for 256 Byte Sectors)
       06   LAST TRACK NUMBER      (OPTIONAL DEF-39)
       07   NUMBER OF SECTORS      (OPTIONAL DEPENDS ON BYTE 05)
       08	LOGICAL STARTING TRACK (OPTIONAL DEF-0)
       09   STARTING TRACK OFFSET  (OPTIONAL DEF-0)
       0A   FILL BYTE              (OPTIONAL DEF-$E5)
       0B-?? SECTOR TABLE          (OPTIONAL T-BIT SET)
        M - MFM (not CBM)
    	P - PARTIAL FORMAT (1=PARTIAL)
    	I - INDEX ADDRESS MARK WRITTEN (1=WRITTEN)
    	D - DOUBLE SIDED FLAG (1=FORMAT DOUBLE SIDED)
    	S - SIDE SELECT 
    	T - SECTOR TABLE INCLUDED (ALL OTHER PARMS MUST BE INCLUDED)
    	N - DRIVE NUMBER
       Notes: If M=0 then remainder of 03 is ignored
              and byte 04,05 = Disk ID
              and all other parameters ignored. */
        set_error(ERROR_SYNTAX_UNABLE);
        b_out_burstload(0, (bcis_status & 0xf0) | 0xe); /* status = syntax error */
        break;
    case 0x8: /* Sector Interleave ($84f1)
       02	W	X	X	0	1	0	0   N
       03	-------  INTERLEAVE ---------
    	W - WRITE SWITCH
    	N - DRIVE NUMBER
    	X - DON'T CARE */
		/* 'W' actualy means Read (not Write) ... silly CBM */
		if (command_buffer[2] & 0x80) 
	        b_out_burstload(0, bcis_interleave); /* read value */
		else { /* write sector interleave */
			if (command_length < 4)
		        set_error(ERROR_SYNTAX_UNABLE);
			else
				bcis_interleave = command_buffer[3]; /* no value test! ($8511) */
		}
        break;
    case 0xa:
    case 0x1a: {/* Query Disk Format ($8517)
       02	F	X	T	S	1	0	1   N
       03   -OFFSET (OPTIONAL F-BIT SET)-
    	F - FORCE FLAG (F=1, WILL STEP THE HEAD)
    	T - END SECTOR TABLE (T=1, SEND)
    	N - DRIVE NUMBER
    	X - DON'T CARE.
        OUTPUT:
        	BURST STATUS BYTE (IF THERE WAS AN ERROR OR IF THE 
			   FORMAT IS GCR NO BYTES WILL FOLLOW)
        	BURST STATUS BYTE (IF THERE WAS AN ERROR IN COMPILING 
	           MFM FORMAT INFORMATION NO BYTES WILL FOLLOW)
        	NUMBER OF SECTORS (THE NUMBER OF SECTORS ON A PARTICULAR TRACK)
        	LOGICAL TRACK	  (LOGICAL TRACK NUMBER FOUND IN THE DISK HEADER)
        	MINIMUM SECTOR 	  (THE LOGICAL SECTOR WITH THE LOWEST VALUE)
        	MAXIMUM SECTOR	  (THE LOGICAL SECTOR WITH THE HIGHEST VALUE)
        	CP/M INTERLEAVE	  (THE HARD INTERLEAVE FOUND ON THE TRACK) */
		uint8_t smin, smax;
		buffer_t* buf;
		uint8_t stop;  /* flag ATN found */
		uint8_t flags = 1; /* current CLOCK value because of Unlisten */
		buf = alloc_buffer();
		if (!buf) {
			b_out_burstload(flags ^= 1, (bcis_status & 0xf0) | 0xf); /* drive not ready */
			break; /* end */
		}
        switch (partition[current_part].imagetype & D64_TYPE_MASK) {
			/* this assumes a readable card is in the device! */
			/* FIXME ... 1581 should return 'physical' 10 sectors/track */
		case D64_TYPE_D41:
		case D64_TYPE_D71:
			bcis_status = 0x01; /* okay, native CBM disk (implied sector size 256) */
			break;
		case D64_TYPE_D81:
			bcis_status = 0x20; /* okay, native CBM disk + 512 sector size */
			break;
		case D64_TYPE_NONE:	  /* FAT */
			bcis_status = 0xAF; /* error, foreign disk + 512 sector size */
			break;
		default:				  /* DNP, M2I ... FIXME? */
			bcis_status = 0x9F; /* error, foreign disk + 256 sector size */
		}
		fl_track = 1;
		if (command_buffer[2] & 0x80) { /* seek to track */
			if (command_length < 4) {
				 /* silly user */
				set_error(ERROR_SYNTAX_UNABLE);
				bcis_status = (bcis_status & 0xf0) | 0x0e; /* syntax error */
			} else if ((bcis_status & 0x0f) < 2) {
				/* seek any sector of track, but only supported image types */
				/* use sector 1 until we have 'seek' for fileops_t */
				fl_track = 1 + command_buffer[3];
				read_sector(buf, current_part, fl_track, 1);
				if (current_error)
					bcis_status = (bcis_status & 0xf0) | 2; /* sector not found */
			}
		}
        stop = b_out_burstload(flags ^= 1, bcis_status); /* sector size, type, error status */
		if (stop || bcis_status == 1 || (bcis_status & 0xf) > 1) {
			free_buffer(buf);
			break; /* found ATN or no further info */
		}
		/* the following is overkill until we support .GCR or .MFM images */
		smin = 0 ;
		current_error = 0; /* '00,OK' should be set, but just to be safe */
		do {
			read_sector(buf, current_part, fl_track, smin);
			if (current_error == 0)
				break;
			++smin;
		} while (smin);
		smax = smin + 1;
		current_error = 0;
		do {
			read_sector(buf, current_part, fl_track, smax);
			if (current_error != 0)
				break;
			++smax;
		} while (smax);
		/* note smax is really max+1 */

		do {/* send results, break if ATN found */
			if (b_out_burstload(flags ^= 1, smax - smin)) /* # sectors */
				break;
			if (b_out_burstload(flags ^= 1, fl_track -1)) /* logical track -- FIXME ? */
				break;
			if (b_out_burstload(flags ^= 1, smin))        /* lowest sector# */
				break;
			if (b_out_burstload(flags ^= 1, smax - 1))    /* highest sector# */
				break;
			/* fake the sector interleave and sector table */
			if (b_out_burstload(flags ^= 1, 1))           /* hard sector interleave */
				break;
			if (command_buffer[2] & 0x20) { 
				/* send sector table */
				do {
					if (b_out_burstload(flags ^= 1, smin))
						break; /* found ATN */
					++smin;
				} while (smin != smax);
			}
		} while(0);
		free_buffer(buf);
		set_error(ERROR_OK);
        break;
	}
    case 0xc: /* Inquire Status ($856b)
       02	W	C	X	0	1	1	0   N
       03   -- NEW STATUS (W-BIT SET) ---
    	W - WRITE SWITCH
    	C - CHANGE (C=1 & W=0 - FORCE LOGIN DISK,
		    C=1 & W=1 - RETURN WHETHER DISK WAS LOGGED 
		    IE. $XB ERROR OR OLD STATUS)
	    N - DRIVE NUMBER
    	X - DON'T CARE  */
		/* note the 'W' bit is really Read (not Write) ... silly CBM
		   also, 1571 does not check command length, we do
		   the 'C' bit is for disk change hardware flag, nothing for us
		   this is reported by code 0xb when disk is (un)mounted */
/*		if (!IEC_CLOCK) {
		  set_error(ERROR_BUS);
		  break;
		}
*/
		if (command_buffer[2] & 0x80)  /* Read status */
	        b_out_burstload(0, bcis_status);
		else { /* write status */
			if (command_length < 4) {
				 /* silly user */
				set_error(ERROR_SYNTAX_UNABLE);
			} else /* FIXME ? changes sector size for 1571, but not us */
				bcis_status = command_buffer[3];
		}
        break;
	case 0x0e: /* Duplicate Disk ($85a5) */
        b_out_burstload(0, (bcis_status & 0xf0) | 0x0e); /* status = syntax error */
        set_error(ERROR_SYNTAX_UNKNOWN);
		break;
    case 0x1e: /* Change Utility ($8FE5) */
        if (command_length <4) {
            set_error(ERROR_SYNTAX_UNABLE);
			break;
		}
		switch(command_buffer[3]) {
		case 'R':  /* retries */
		case 'T':  /* test ROM */
		case 'V':  /* disable verify */
			break; /* okay -- ignore */
		case 'H':  /* head select */
		case 'M':  /* 1541/71 mode select */
			set_error(ERROR_SYNTAX_UNABLE);
			break;
		case 'S':  /* sector interleave $8fa4 */
			if (command_length <5)
				set_error(ERROR_SYNTAX_UNABLE);
			else
				partition[current_part].d64data.file_interleave = command_buffer[4];
				/* FIXME: the above gets reset on disk swap,
				but it is stored ($69) seperate from bcis_interleave ($3c) */
			break;
		default:  /* device# */
			if (command_buffer[3] >= 4 && command_buffer[3] <= 30) {
			  device_address = command_buffer[3];
			  display_address(device_address);
			} else
				set_error(ERROR_SYNTAX_UNABLE);
		}
        break;
    case 0x1f: /* Burst Load File ($9080)
       02	P	X	X	1	1	1	1	1
       03+  FILE NAME
		P - SEQUENTIAL FILE BIT (P=1, DOES NOT HAVE TO BE A PRG FILE)
		X - DON'T CARE. */
/*		if (!IEC_CLOCK) {
		  set_error(ERROR_BUS);
		  break;
		}
*/		f_out_burstload();
        break;
    default:
        if (command_buffer[1] & 1)
            set_error(ERROR_DRIVE_NOT_READY);
        else
            set_error(ERROR_SYNTAX_UNKNOWN);
        break; /* fall through */
    }
    break; /* End U0 Command */

  default:
    set_error(ERROR_SYNTAX_UNKNOWN);
    break;
  }
}


/* ------------ */
/*  X commands  */
/* ------------ */
static void parse_xcommand(void) {
  uint8_t num;
  uint8_t *str;
  path_t path;

  clean_cmdbuffer();

  switch (command_buffer[1]) {
  case 'B':
    /* Free-block count faking */
    num = parse_bool();
    if (num != 255) {
      if (num)
        globalflags |= FAT32_FREEBLOCKS;
      else
        globalflags &= (uint8_t)~FAT32_FREEBLOCKS;

      set_error_ts(ERROR_STATUS,device_address,0);
    }
    break;

  case 'E':
    /* Change file extension mode */
    str = command_buffer+2;
    if (*str == '+') {
      globalflags |= EXTENSION_HIDING;
    } else if (*str == '-') {
      globalflags &= (uint8_t)~EXTENSION_HIDING;
    } else {
      num = parse_number(&str);
      if (num > 4) {
        set_error(ERROR_SYNTAX_UNKNOWN);
      } else {
        file_extension_mode = num;
        if (num >= 3)
          globalflags |= EXTENSION_HIDING;
      }
    }
    set_error_ts(ERROR_STATUS,device_address,0);
    break;

  case 'J':
    /* Jiffy enable/disable */
    num = parse_bool();
    if (num != 255) {
      if (num)
        globalflags |= JIFFY_ENABLED;
      else
        globalflags &= (uint8_t)~JIFFY_ENABLED;

      set_error_ts(ERROR_STATUS,device_address,0);
    }
    break;

  case 'D':
    /* drive config */
#ifdef NEED_DISKMUX
    str = command_buffer+2;
    if(*str == '?') {
      set_error_ts(ERROR_STATUS,device_address,1);
      break;
    }
    num = parse_number(&str);
    if(num < 8) {
      while(*str == ' ')
        str++;
      if(*str == '=') {
        uint8_t val, i;
        str++;
        val = parse_number(&str);
        if(val <= 0x0f) {
          for(i = 0;(val != 0x0f) && i < 8; i++) {
            if(i != num && map_drive(num) == val) {
              /* Trying to set the same drive mapping in two places. */
              set_error(ERROR_SYNTAX_UNKNOWN);
              break;
            }
          }
          switch(val >> DRIVE_BITS) {
          case DISK_TYPE_NONE:
#ifdef HAVE_DF
          case DISK_TYPE_DF:
#endif
#ifdef HAVE_SD
          case DISK_TYPE_SD:
#endif
#ifdef HAVE_ATA
          case DISK_TYPE_ATA:
#endif
            if(map_drive(num) != val) {
              set_map_drive(num,val);
              /* sanity check.  If the user has truly turned off all drives, turn the
               * defaults back on
               */
              if(drive_config == 0xffffffff)
                set_drive_config(get_default_driveconfig());
              fatops_init(0);
            }
            break;
          default:
            set_error(ERROR_SYNTAX_UNKNOWN);
            break;
          }
          break;
        }
      }
    } else
      set_error(ERROR_SYNTAX_UNKNOWN);
#else
    // return error for units without MUX support
    set_error(ERROR_SYNTAX_UNKNOWN);
#endif
    break;

  case 'W':
    /* Write configuration */
    write_configuration();
    set_error_ts(ERROR_STATUS,device_address,0);
    break;

  case 'S':
    /* Swaplist */
    if (parse_path(command_buffer+2, &path, &str, 0))
      return;

    set_changelist(&path, str);
    break;

  case '*':
    /* Post-* matching */
    num = parse_bool();
    if (num != 255) {
      if (num)
        globalflags |= POSTMATCH;
      else
        globalflags &= (uint8_t)~POSTMATCH;

      set_error_ts(ERROR_STATUS,device_address,0);
    }
    break;

#ifdef CONFIG_STACK_TRACKING
  case '?':
    /* Output the largest stack size seen */
    set_error_ts(ERROR_LONGVERSION,(RAMEND-minstack)>>8,(RAMEND-minstack)&0xff);
    break;
#else
  case '?':
    /* Output the long version string */
    set_error(ERROR_LONGVERSION);
    break;
#endif

  default:
    /* Unknown command, just show the status */
    set_error_ts(ERROR_STATUS,device_address,0);
    break;
  }
}


/* ------------------------------------------------------------------------- */
/*  Main command parser function                                             */
/* ------------------------------------------------------------------------- */

void parse_doscommand(void) {
  /* Set default message: Everything ok */
  set_error(ERROR_OK);

  /* Abort if the command is too long */
  if (command_length == CONFIG_COMMAND_BUFFER_SIZE) {
    set_error(ERROR_SYNTAX_TOOLONG);
    return;
  }

#ifdef CONFIG_COMMAND_CHANNEL_DUMP
  /* Debugging aid: Dump the whole command via serial */
  if (detected_loader == FL_NONE) {
    /* Dump only if no loader was detected because it may ruin the timing */
    uart_flush();
    uart_trace(command_buffer,0,command_length);
  }
#endif

  /* Remove one CR or CR+LF at end of command, unless "U0" command
     see $C2B3 in 1541 or 1571 ROM (U0 exception only for 1571) */
  if (command_length < 2 
   || command_buffer[0] !=0x55 || command_buffer[1] !=0x30) {
      if (command_length > 0 && command_buffer[command_length-1] == 0x0d)
        command_length--;
      else if (command_length > 1 && command_buffer[command_length-2] == 0x0d)
        command_length -= 2;
  }

  /* Abort if there is no command */
  if (command_length == 0) {
    set_error(ERROR_SYNTAX_UNABLE);
    return;
  }

  /* Send command to display */
  display_doscommand(command_length, command_buffer);

  /* MD/CD/RD clash with other commands, so they're checked first */
  if (command_buffer[0] != 'X' && command_buffer[1] == 'D') {
    parse_dircommand();
    return;
  }

  switch (command_buffer[0]) {
  case 'B':
    /* Block-Something */
    parse_block();
    break;

  case 'C':
    /* Copy or Change Partition */
    if (command_buffer[1] == 'P' || command_buffer[1] == 0xd0)
      parse_changepart();
    else
      /* Copy a file */
      parse_copy();
    break;

  case 'D':
    /* Direct sector access (was duplicate in CBM drives) */
    parse_direct();
    break;

  case 'E':
    /* EEPROM-something */
    parse_eeprom();
    break;

  case 'G':
    /* Get-Partition */
    parse_getpartition();
    break;

  case 'I':
    /* Initialize */
    parse_initialize();
    break;

  case 'M':
    /* Memory-something */
    parse_memory();
    break;

  case 'N':
    /* New */
    parse_new();
    break;

  case 'P':
    /* Position */
    parse_position();
    break;

  case 'R':
    /* Rename */
    parse_rename();
    break;

  case 'S':
    if(command_length == 3 && command_buffer[1] == '-') {
      /* Swap drive number */
      set_error(ERROR_SYNTAX_UNABLE);
      break;
    }
    /* Scratch */
    parse_scratch();
    break;

#if CONFIG_RTC_VARIANT > 0
  case 'T':
    parse_time();
    break;
#endif

  case 'U':
    parse_user();
    break;

  case 'X':
    parse_xcommand();
    break;

  default:
    set_error(ERROR_SYNTAX_UNKNOWN);
    break;
  }
}
