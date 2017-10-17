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


   fastloader.h: Definitions for the high level fast loader handling

*/

#ifndef FASTLOADER_H
#define FASTLOADER_H

#define FL_NONE          0
#define FL_TURBODISK     1
#define FL_FC3_LOAD      2
#define FL_FC3_SAVE      3
#define FL_DREAMLOAD     4
#define FL_DREAMLOAD_OLD 5
#define FL_FC3_FREEZED   6
#define FL_ULOAD3        7
#define FL_BURSTLOAD     8

#ifndef __ASSEMBLER__

extern uint8_t detected_loader;
extern volatile uint8_t fl_track;
extern volatile uint8_t fl_sector;

void load_turbodisk(void);
void load_fc3(uint8_t freezed);
void save_fc3(void);
void load_dreamload(void);
void load_uload3(void);
uint8_t b_out_burstload(uint8_t flags, uint8_t val);
int16_t b_in_burstload(uint8_t flags);
void s_out_burstload(uint8_t n_sec);
void s_in_burstload(uint8_t n_sec);
void f_out_burstload(void);

#endif
#endif
