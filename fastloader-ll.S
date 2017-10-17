/* sd2iec - SD/MMC to Commodore serial bus interface/controller
   Copyright (C) 2007-2009  Ingo Korb <ingo@akana.de>
   Copyright (C) 2007-2009  M.Kiesel <mayne@users.sourceforge.net>
   Final Cartridge III, DreamLoad fastloader support:
   Copyright (C) 2008  Thomas Giesel <skoe@directbox.com>
   Fast Serial protocol and Burst Command Instruction Set:
   Copyright (C) 2011  Robert Willie <hydradix@yahoo.com>

   Inspiration and low-level SD/MMC access based on code from MMC2IEC
     by Lars Pontoppidan et al., see sdcard.c|h and config.h.

   FAT filesystem access based on code from ChaN, see tff.c|h.

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


   fastloader.S: Low level fastloader transfer routines.

   Thanks to Jochen Adler for his Jiffy docs at http://www.nlq.de/

*/


#include "config.h"
#include "fastloader.h"
#include <avr/io.h>

/* Timing offsets for JiffyDos read/write */
/* These values are added to the delayloop counter before the first      */
/* bitpair read/write. They were determined experimentally to center the */
/* range of working OSCCAL values around the default value.              */
#define JIFFY_OFFSET_WRITE 30
#define JIFFY_OFFSET_READ  30

        .section .text

#ifdef IEC_ATN_INT_VECT
        ;; ===================================================================
        ;; ATN(+CLK) Interrupt service routine for IEC bus
        ;; ===================================================================
        ;
        ; Functions called from here may change these registers:
        ; r0, r18, r19, r24
        ; Other registers must be saved and restored by the called functions
        ;
        .global IEC_ATN_INT_VECT
IEC_ATN_INT_VECT:
        ; functions called from here must only change these registers:
        push    r18
        in      r18, _SFR_IO_ADDR(SREG)
        push    r18
        push    r19
        push    r24
        push    r0

#ifdef IEC_PCMSK
        lds     r18, _SFR_ADDR(IEC_PCMSK)
        bst     r18, IEC_PIN_ATN        ; only check ATN
        brtc    iiv_atn_irq_end         ; if it is an IRQ source
#endif

        ; check if ATN is low
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN
        rjmp    iiv_atn_irq_end

        ; ATN is low, continue depending from active fast loader
#ifdef CONFIG_LOADER_DREAMLOAD
        lds     r18, detected_loader
        cpi     r18, FL_DREAMLOAD_OLD
        brne    iiv_not_fl_dreamload_old
        ; dreamload (old), receive a command code
        rcall   dreamload_get_command_old
        rjmp    iiv_atn_irq_end         ; no other ATN action needed
iiv_not_fl_dreamload_old:
#endif
        ; no custom behaviour, this is ATN ACK
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA    ; DATA low

iiv_atn_irq_end:
#ifdef IEC_PCMSK
        lds     r18, _SFR_ADDR(IEC_PCMSK)
        bst     r18, IEC_PIN_CLOCK      ; only check CLOCK
        brtc    iiv_clock_irq_end       ; if it is an IRQ source

        ; check if CLOCK is low
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    iiv_clock_irq_end

        ; CLOCK is low, continue depending from active fast loader
#ifdef CONFIG_LOADER_DREAMLOAD
        lds     r18, detected_loader
        cpi     r18, FL_DREAMLOAD
        brne    iiv_not_fl_dreamload
        ; dreamload, receive a command code
        rcall   dreamload_get_command
        rjmp    iiv_clock_irq_end       ; no other CLOCK action needed
iiv_not_fl_dreamload:
#endif // ifdef CONFIG_LOADER_DREAMLOAD
#endif // ifdef IEC_PCMSK

iiv_clock_irq_end:

        pop     r0
        pop     r24
        pop     r19
        pop     r18
        out     _SFR_IO_ADDR(SREG), r18
        pop     r18
        reti
#endif // ifdef IEC_ATN_INT_VECT


#ifdef IEC_CLK_INT_VECT
        ;; ===================================================================
        ;; CLK Interrupt service routine for IEC bus
        ;; ===================================================================
        ;
        ; Functions called from here may change these registers:
        ; r0, r18, r19, r24
        ; Other registers must be saved and restored by the called functions
        ;
        .global IEC_CLK_INT_VECT
IEC_CLK_INT_VECT:
        ; functions called from here must only change these registers:
        push    r18
        in      r18, _SFR_IO_ADDR(SREG)
        push    r18
        push    r19
        push    r24
        push    r0

        ; check if CLOCK is low
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    clk_irq_end

        ; CLOCK is low, continue depending from active fast loader
#ifdef CONFIG_LOADER_DREAMLOAD
        lds     r18, detected_loader
        cpi     r18, FL_DREAMLOAD
        brne    clk_not_fl_dreamload
        ; dreamload, receive a command code
        rcall   dreamload_get_command
        rjmp    clk_irq_end       ; no other CLOCK action needed
clk_not_fl_dreamload:
#endif // ifdef CONFIG_LOADER_DREAMLOAD

clk_irq_end:

        pop     r0
        pop     r24
        pop     r19
        pop     r18
        out     _SFR_IO_ADDR(SREG), r18
        pop     r18
        reti
#endif // ifdef IEC_CLK_INT_VECT


#if defined(CONFIG_JIFFY_ASM) || defined(CONFIG_LOADER_TURBODISK) || defined(CONFIG_LOADER_FC3)
        ;; ===================================================================
        ;;  Utility routines
        ;; ===================================================================

        ;;  Used by the macro below, don't call directly
cycleloop2:
        nop                     ; 1
cycleloop1:
        nop                     ; 1
cycleloop0:
        dec     r18             ; 1
        brne    cycleloop0      ; 2/1
        ret                     ; 4

        ;; This macro waits for the specified number of cycles
        ;;  Uses r18
        .macro delay_cycles num
        ldi     r18, 1 + (\num - 10) / 3 ; 1
        .if (\num - 10) % 3 == 0
        rcall   cycleloop0      ; 3
        .elseif (\num - 10) % 3 == 1
        rcall   cycleloop1      ; 3
        .else
        rcall   cycleloop2      ; 3
        .endif
        .endm


        ;; Including the rcall this will delay for 8 cycles
delay1us:
        nop                     ; 1
        ret                     ; 4

        ;; wait for ATN high
wait_atn_high:
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN
        rjmp    wait_atn_high
        ret

        ;; wait for ATN low
wait_atn_low:
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN
        rjmp    wait_atn_low
        ret

#endif // ifdef any fast loader

#ifdef CONFIG_JIFFY_ASM
        ;; ====================================================================
        ;;  JiffyDOS
        ;; ====================================================================

        ;;
        ;; Receives a single byte using the JiffyDOS protocol
        ;; return uint8_t reveicedbyte (r24)
        ;;
        .global jiffy_receive
jiffy_receive:
        ;; Disable interrupts
        cli

        ;; Move pointer to EOF variable into Z
        movw    r30,r24
        clr     r24             ; clear output register
        clr     r25             ; clear high byte of return value

        ;; Set clock+data high
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_CLOCK
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA

        ;; Wait until clock is high and emulate ATN-Ack
0:      sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA ; Data low if ATN is low
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    0b

        ;; Wait for 13us from clock high -> 104 cycles
        delay_cycles 104 + JIFFY_OFFSET_READ ; 104 + Offset

        ;; Read bit 5+4
        in      r0, _SFR_IO_ADDR(IEC_PIN) ; 1

        ;; Store bits in r24
        bst     r0, IEC_PIN_DATA  ; 1 - get data bit
        bld     r24, 5            ; 1 - store as bit 5
        bst     r0, IEC_PIN_CLOCK ; 1 - get clock bit
        bld     r24, 4            ; 1 - store as bit 4

        ;; Wait 13us -> 104-5=99 cycles
        delay_cycles 99         ; 99

        ;; Read bit 7+6
        in      r0, _SFR_IO_ADDR(IEC_PIN) ; 1

        ;; Store bits in r24
        bst     r0, IEC_PIN_DATA  ; 1 - get data bit
        bld     r24, 7            ; 1 - store as bit 7
        bst     r0, IEC_PIN_CLOCK ; 1 - get clock bit
        bld     r24, 6            ; 1 - store as bit 6

        ;; Wait 11us -> 88-5=83 cycles
        delay_cycles 83         ; 83

        ;; Read bit 1+3 [sic]
        in      r0, _SFR_IO_ADDR(IEC_PIN) ; 1
        bst     r0, IEC_PIN_DATA  ; 1 - get data bit
        bld     r24, 1            ; 1 - store as bit 1
        bst     r0, IEC_PIN_CLOCK ; 1 - get clock bit
        bld     r24, 3            ; 1 - store as bit 3

        ;; Wait 13us -> 104-5=99 cycles
        delay_cycles 99         ; 99

        ;; Read Bit 0+2
        in      r0, _SFR_IO_ADDR(IEC_PIN) ; 1
        bst     r0, IEC_PIN_DATA  ; 1 - get data bit
        bld     r24, 0            ; 1 - store as bit 0
        bst     r0, IEC_PIN_CLOCK ; 1 - get clock bit
        bld     r24, 2            ; 1 - store as bit 2

        ;; Wait 13us -> 104-5=99 cycles
        delay_cycles 99         ; 99

        ;; Read EOI mark
        in      r19, _SFR_IO_ADDR(IEC_PIN) ; 1

        ;; Wait 6us -> 48-1=47 cycles
        delay_cycles 47         ; 47

        ;; Data low
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA ; 1

        ;; Post-process data and store last bus state
        com     r24             ; invert received data (result)
        st      Z, r19          ; store last bus state
        sei                     ; enable interrupts
        ret



        ;; Shifts the lowest two bits from r0 to r19
        ;; and sends then on the bus at cycle 12
        ;; Needs 16 cycles including the rcall
jiffy_sendbits:
        in      r19, _SFR_IO_ADDR(IEC_OUT) ; 1 - read port
        andi    r19, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
                                    ; 1 - mask IEC bits
        bst     r0, 0               ; 1 - get bit 0
        bld     r19, IEC_OPIN_CLOCK ; 1 - send on the clock line
        bst     r0, 1               ; 1 - get bit 1
        bld     r19, IEC_OPIN_DATA  ; 1 - send on the data line
        lsr     r0                  ; 1 - remove source bits
        lsr     r0                  ; 1
        out     _SFR_IO_ADDR(IEC_OUT), r19 ; 1 - output the bit pair
        ret                         ; 4

        ;;
        ;; Sends a single byte using the Jiffy protocol
        ;; uint8_t value (r24), uint8_t eoi (r22), uint8_t loadflags (r20)
        ;; return uint8_t atnactive (r24)
        ;;
        ;; eoi should always be 0 for LOAD because the eoi marker is
        ;; transmitted in a different way there (see C code).
        ;;
        ;; Loadflags has a dual purpose:
        ;;  - if it's != 0, the start condition will be modified for Jiffy-LOAD
        ;;  - bit 7 will be cleared after that
        ;;  - if it's still != 0, the function will exit after sending
        ;;    the last bitpair - required for all but the final byte of a block
        ;;    during LOAD
        .global jiffy_send
jiffy_send:
        cli                     ; Disable interrupts

        ;; Calculate bus wait condition based on current state
        ;; The loop below will spin while ATN and Clock are high and
        ;; - Data is low  (single-byte transfer)
        ;; - Data is high (LOAD)
        ldi     r21, IEC_BIT_CLOCK | IEC_BIT_ATN
        tst     r20             ; loadflag set?
        breq    0f              ; Yes, skip
                ; No: Set data bit
        ori     r21, IEC_BIT_DATA

0:      andi    r20, 0x7f       ; Clear bit 7 of loadflags

        ;; Calculate bus state for EOI/not-EOI mark
        tst     r22             ; EOI flag set?
        breq    0f              ; No, branch

        in      r22, _SFR_IO_ADDR(IEC_OUT)
        andi    r22, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        ori     r22, IEC_OBIT_DATA ; Data low, Clock hi on EOI
        rjmp    1f

0:      in      r22, _SFR_IO_ADDR(IEC_OUT)
        andi    r22, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        ori     r22, IEC_OBIT_CLOCK ; Data hi, Clock low on non-EOI

1:
        ;; Set clock and data high/inactive - FFB5
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA
                ; this is the actual ready signal for the C64
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_CLOCK

        ;; Wait 1us to allow the bus to settle (J1541 needs 4us here)
        rcall   delay1us

        ;; Set up a few registers
        mov     r0, r24         ; move data byte to r0
        com     r0              ; invert data byte

        ;; Wait for start condition (calculated above) from C64 - FFB8
0:      in      r24, _SFR_IO_ADDR(IEC_PIN)
        andi    r24, IEC_BIT_CLOCK | IEC_BIT_DATA | IEC_BIT_ATN ; 1
        cp      r24, r21        ; 1
        breq    0b              ; 1

        ;; Check for ATN (J1541 doesn't do this, but I'm paranoid)
        ;; Doesn't work, further analysis required
        andi    r24, IEC_BIT_ATN ; 1
        breq    js_finish        ; 1 - jump if ATN is low

        ;; Output the first bitpair 6us (48 cycles) after the start
        ;; 6us is the best-case time from bus check to transmission in J1541
        delay_cycles 31 + JIFFY_OFFSET_WRITE
                                ; 31 = 48-17
        rcall   jiffy_sendbits  ; 12+4 - [FFBD]

        ;; Output the second bitpair 10us (80 cycles) after the first
        delay_cycles 64         ; 64 = 80-16

        rcall   jiffy_sendbits  ; 12+4 - [FFC4]

        ;; Output the third bitpair 11us (88 cycles) after the second
        delay_cycles 72         ; 72 = 88-16

        rcall   jiffy_sendbits  ; 12+4 - [FFCC]

        ;; Output the fourth bitpair 10us (80 cycles) after the third
        delay_cycles 64         ; 64 = 80-16

        rcall   jiffy_sendbits  ; 12+4 - [FFD3]

        ;; Skip sending EOI for LOAD code path
        tst     r20             ; 1
        brne    js_finish       ; 1

        ;; Output EOI marker 11us (88 cycles) after the last bitpair
        delay_cycles 81         ; 81 = 88-7

        out     _SFR_IO_ADDR(IEC_OUT), r22 ; 1 - output EOI marker [FFDB]

        ;; Wait 1us to allow the bus to settle (J1541 needs 4us here)
        rcall   delay1us

        ;; Wait until data is low, check ATN [FFDE]
        ;; This loop won't wait when EOI is signalled.
0:      in      r24, _SFR_IO_ADDR(IEC_PIN) ; Read bus
        sbrs    r24, IEC_PIN_ATN           ; Skip if ATN is high
        rjmp    js_finish                  ; ATN low, exit loop
        sbrc    r24, IEC_PIN_DATA          ; Skip if Data is low
        rjmp    0b                         ; No Data, no ATN -> loop

js_finish:
        com     r24             ; invert port state (ATN low returns true)
        andi    r24, IEC_BIT_ATN ; single out ATN bit

        sei                     ; re-enable interrupts
        ret

#endif  // CONFIG_JIFFY_ASM

        ;; ====================================================================
        ;;  Fast Serial
        ;; ====================================================================
	.global fserial_out
fserial_out:
        ;;
        ;; Sends a single byte over the fast serial bus (SRQ and DATA)
        ;; uint8_t fast_flags (r24), uint8_t value (r22)
        ;; return uint8_t atnactive (r24)
        ;;
        ;; fast_flags.0 is the 'ready' signal we want to see on CLOCK
        ;; fast_flags.1 is flag to send without checking (debug)
        ;;

	com	r22		; invert value

	;; check flag to ignore CLOCK * debug *
	mov	r23, r24	; save fast_flags
	andi	r24, 2		; ignore CLOCK ?
	brne	1f		; yes

	;; setup wait condition
	ldi	r19, IEC_BIT_CLOCK | IEC_BIT_ATN
	mov	r24, r23	; get fast_flags
	andi	r24, 1		; want CLOCK active / low ?
	breq	0f              ; yes
	ldi	r24, IEC_BIT_CLOCK
	eor	r19, r24        ; want CLOCK released / high
0:
	;; wait for desired CLOCK or ATN active
	in	r24, _SFR_IO_ADDR(IEC_PIN)
	andi	r24, IEC_BIT_CLOCK | IEC_BIT_ATN
	cp	r24, r19
	breq	0b

	;; check for ATN
	andi	r24, IEC_BIT_ATN
	breq	5f
1:
	;; setup output loop
	ldi	r25, 8		; 8 bits to send
	in	r19, _SFR_IO_ADDR(IEC_OUT)
	andi    r19, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN)
	rjmp	3f		; send byte

	;; Each bit is 7us = 3us of notice/delay + 4us data hold.
	;; The CIA is symetrical = send same data and same delay
	;; but because we send faster than CIA of 128/1571/1581,
	;; we keep the data a little bit longer.
	;; The CIA receiving data does not care much about delay,
	;; the speed is limited by capacitance/inducance/resistance
	;; of the physical serial cable(s) connected to the system.
2:
	;; loop to send
	lsl	r22		; 1 - next bit
	delay_cycles 24		; 24 = 32 - 8
3:
	ori	r19, IEC_OBIT_SRQ ; 1 - activate SRQ
	bst	r22, 7		; 1 - get bit to send
	bld	r19, IEC_OPIN_DATA ; 1 - put it on DATA line
	out	_SFR_IO_ADDR(IEC_OUT), r19 ; 1 - output on serial bus

	delay_cycles 22		; 22 = 24 - 2
	andi	r19, ~IEC_OBIT_SRQ ; 1 - release SRQ
	out	_SFR_IO_ADDR(IEC_OUT), r19 ; 1 - output on serial bus
	dec	r25		; 1 - count bits
	brne	2b		; 2 - next bit

	;; hold last bit
	delay_cycles 27		; 27 = 32 - 5
4:
	;; test ATN and release DATA
	in	r24, _SFR_IO_ADDR(IEC_PIN) ; 1
	andi	r19, ~IEC_OBIT_DATA        ; 1
	out	_SFR_IO_ADDR(IEC_OUT), r19 ; 1
5:
	;; exit
        com     r24             ; invert port state (ATN low returns true)
        andi    r24, IEC_BIT_ATN ; single out ATN bit
	ret

	.global fserial_in
fserial_in:
        ;;
        ;; Receive a single byte over the fast serial bus (SRQ and DATA)
        ;; uint8_t fast_flags (r24)
        ;; return int16_t data or -1 if ATN active
        ;;
        ;; fast_flags.0 is ~CLOCK to send (if no toggle)
        ;; fast_flags.1 is flag to toggle CLOCK
        ;;

	;; setup for output
	in	r19, _SFR_IO_ADDR(IEC_OUT)
	andi    r19, ~(IEC_OBIT_DATA|IEC_OBIT_SRQ|IEC_OBIT_ATN)

	;; check flag to toggle CLOCK
	sbrs	r24, 1		; test fast_flags
	rjmp	0f              ; set specific value
	ldi	r21, IEC_OBIT_CLOCK
	eor	r19, r21	; toggle CLOCK
	rjmp	1f

0:	;; set specific CLOCK
	bst	r24, 0		; get ~CLOCK from fast_flags
	bld	r19, IEC_OPIN_CLOCK ; set for output

1:	;; check ATN and setup loop condition
	in	r20, _SFR_IO_ADDR(IEC_PIN)
	andi	r20, IEC_BIT_ATN
	breq	3f
	out	_SFR_IO_ADDR(IEC_OUT), r19 ; set output, ready for input
	clr	r25		; clear return high
	ldi	r21, 8		; bit counter

0:	;; loop for bits
	lsl	r24

1:	;; wait for SRQ or ATN to go low
	in	r20, _SFR_IO_ADDR(IEC_PIN)
	sbrs	r20, IEC_PIN_ATN
	rjmp	3f
	sbrc	r20, IEC_PIN_SRQ
	rjmp	1b

2:	;; capture DATA on rising edge of SRQ
	in	r20, _SFR_IO_ADDR(IEC_PIN)
	sbrs	r20, IEC_PIN_ATN
	rjmp	3f
	sbrs	r20, IEC_PIN_SRQ
	rjmp	2b

	;; save bit and test loop
	bst	r20, IEC_PIN_DATA
	bld	r24, 0
	dec	r21
	brne	0b

	;; set return value
;;	com	r24		; invert bits received
	ret

3:	;; ATN active
	ldi	r25,0xff	; negative return value
	andi	r19, ~IEC_OBIT_CLOCK ; release CLOCK
	ori	r19, IEC_OBIT_DATA   ; emulate ATN acknowledge
	out	_SFR_IO_ADDR(IEC_OUT), r19
	ret

#ifdef CONFIG_LOADER_TURBODISK
        ;; ====================================================================
        ;;  Turbodisk
        ;; ====================================================================

        ;;
        ;; Sends a single byte in r24 using the Turbodisk protocol
        ;;
        .global turbodisk_byte
turbodisk_byte:
        ;; Wait until data is low
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_DATA
        rjmp    turbodisk_byte

        ;; Byte preparation
        com     r24             ; Invert the data byte

        ;; All bus lines high
        in      r18, _SFR_IO_ADDR(IEC_OUT)
        andi    r18, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        out     _SFR_IO_ADDR(IEC_OUT), r18

        ;; Wait until data is high
0:      sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_DATA ; 2
        rjmp    0b

        rcall   delay1us        ; Move the timing window slightly

        ldi     r20, 4          ; 1 - Bitpair counter

tdbitloop:
        in      r19, _SFR_IO_ADDR(IEC_OUT) ; 1 - read & mask unused IEC port lines
        andi    r19, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ) ; 1
        bst     r24, 7              ; 1 - grab bit 7
        bld     r19, IEC_OPIN_CLOCK ; 1 - store in clock bit
        bst     r24, 6              ; 1 - grab bit 6
        bld     r19, IEC_OPIN_DATA  ; 1 - store in data bit
        lsl     r24                 ; 1 - remove source bits
        lsl     r24                 ; 1

        ;; Wait for 28us from data high -> 224-9=215 cycles
        delay_cycles 215        ; 215

        out     _SFR_IO_ADDR(IEC_OUT), r19      ; 1 - output the bit pair

        rcall   delay1us        ; 8 - additional us for loops 2-4

        dec     r20             ; 1 - Decrement bitpair counter
        brne    tdbitloop       ; 2/1 - loop until done

        ;; Wait for 26us from last bitpair -> 208-12=196 cycles
        delay_cycles 196        ; 196

        ;; Data high, Clock low
        in      r18, _SFR_IO_ADDR(IEC_OUT)
        andi    r18, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        ori     r18, IEC_OBIT_CLOCK
        out     _SFR_IO_ADDR(IEC_OUT), r18

        ret


        ;;
        ;; Sends a complete buffer of r22 bytes at r24/r25 using the Turbodisk protocol
        ;;
        .global turbodisk_buffer
turbodisk_buffer:
        ;; Wait until data is low
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_DATA
        rjmp    turbodisk_buffer

        ;; All bus lines high
        in      r18, _SFR_IO_ADDR(IEC_OUT)
        andi    r18, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        out     _SFR_IO_ADDR(IEC_OUT), r18

        movw    r30,r24         ; output pointer

        ;; Wait until data is high
0:      sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_DATA ; 2
        rjmp    0b

        ;; Initial delay of 4 us + move the timing window by 1 us for stability
        delay_cycles (4+1)*8    ; 40

        ;; 287 AVR cycles from here to first LDA $DD00 on C64 side ($F822)
tdbyteloop:
        ld      r0, Z+          ; 2 - load byte
        ldi     r20, 4          ; 1 - bitpair counter
        com     r0              ; 1 - invert data byte

        ;; Waste another 12 us -> 96-4=92 cycles
        delay_cycles 92         ; 92

tdbitloop2:
        in      r19, _SFR_IO_ADDR(IEC_OUT) ; 1 - read & mask unused IEC port lines
        andi    r19, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ) ; 1
        bst     r0, 7               ; 1 - grab bit 7
        bld     r19, IEC_OPIN_CLOCK ; 1 - store in clock bit
        bst     r0, 6               ; 1 - grab bit 6
        bld     r19, IEC_OPIN_DATA  ; 1 - store in data bit
        lsl     r0                  ; 1 - remove source bits
        lsl     r0                  ; 1

        ;; Wait another 24 us -> 192-9=183 cycles
        delay_cycles 183        ; 183

        out     _SFR_IO_ADDR(IEC_OUT), r19      ; 1 - output the bit pair

        ;; 5 us -> 40-3=37 cycles
        delay_cycles 37         ; 37

        dec     r20             ; 1 - Decrement bitpair counter
        brne    tdbitloop2      ; 2/1 - loop until done

        ;; Wait 10 us -> 80-3+1=78 cycles
        delay_cycles 78         ; 78

        dec     r22             ; 1 - Decrement byte counter
        brne    tdbyteloop      ; 2/1 - loop until done

        ;; Final delay: 11 us -> 88 cycles
        delay_cycles 88         ; 88

        ;; Data high, Clock low
        in      r18, _SFR_IO_ADDR(IEC_OUT)
        andi    r18, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        ori     r18, IEC_OBIT_CLOCK
        out     _SFR_IO_ADDR(IEC_OUT), r18

        ret
#endif

#if defined(CONFIG_LOADER_DREAMLOAD) || defined(CONFIG_LOADER_FC3) || defined(CONFIG_LOADER_ULOAD3)
        ;;
        ;; Set bit 0 of r0 on CLOCK and bit 1 on DATA
        ;; A bit value of one means pull down
        ;; After sending these two bits r0 is shifted right two bits
        ;;
        ;; r19 is used as scratch reg here
        ;;
        ;; Takes 10 cycles before OUT (incl. rcall)
        ;; Takes 6 cycles to return after OUT
        ;;
send_bits_to_clk_data:
        ; rcall                  ; 3
        in   r19, _SFR_IO_ADDR(IEC_OUT) ; 1 - read & mask unused IEC port lines
        andi r19, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ) ; 1
        bst  r0, 0               ; 1 - take bit 0 (lsb)
        bld  r19, IEC_OPIN_CLOCK ; 1 - for CLOCK line
        bst  r0, 1               ; 1 - take bit 1
        bld  r19, IEC_OPIN_DATA  ; 1 - for DATA line
        out  _SFR_IO_ADDR(IEC_OUT), r19 ; 1 - output the bit pair

        lsr  r0                  ; 1
        lsr  r0                  ; 1 - prepare next two bits

        ret                      ; 4

        ;;
        ;; Get DATA  => bit 0
        ;; and CLOCK => bit 2 of r24
        ;; Low level means value 0 here
        ;;
        ;; r19 is used as scratch reg here
        ;;
        ;; Takes 4 cycles before IN (incl. rcall)
        ;; Takes 8 cycles to return after IN
        ;;
get_bits_from_clk_data:
        ; rcall                         ; 3
        in      r19, _SFR_IO_ADDR(IEC_PIN)  ; 1
        sbi     _SFR_IO_ADDR(IEC_PIN), IEC_OPIN_SRQ
        bst     r19, IEC_PIN_DATA       ; 1
        bld     r24, 0                  ; 1
        bst     r19, IEC_PIN_CLOCK      ; 1
        bld     r24, 2                  ; 1
        ret                             ; 4

#endif

#if defined(CONFIG_LOADER_FC3) || defined(CONFIG_LOADER_ULOAD3)
        ;;
        ;; Do this kind of handshake:
        ;; set CLOCK low, wait for DATA going low,
        ;; release CLOCK, wait for DATA going high
        ;; returns without waiting if ATN is low
        ;;
        ;; cycles from DATA high to return to caller: 5-10
        ;;
        .global clk_data_handshake
clk_data_handshake:
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_CLOCK
1:
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN
        rjmp    2f
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_DATA
        rjmp    1b
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_CLOCK
1:
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN
        rjmp    2f
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_DATA
        rjmp    1b
2:
        ret
#endif

#ifdef CONFIG_LOADER_FC3
        ;;
        ;; Sends four bytes at r24/r25 using the FC3 protocol
        ;;
        .global fastloader_fc3_send_block
fastloader_fc3_send_block:
        cli
        movw    r30,r24         ; Z = output pointer

        ; pull CLOCK low for sync
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_CLOCK ; 1

        ; 12 us between sync and bitpair
        delay_cycles 12 * 8 - 14 ; 83

        ldi     r21, 4          ; 1 - byte counter
fc3_byteloop:
        ld      r0, Z+          ; 2 - load byte

        com     r0              ; 1 - negate all bits

        ldi     r20, 4          ; 1 - bitpair counter
fc3_bitloop:
        ; send r0[0,1] to CLOCK and DATA, shift r0 right two times
        ; changes r19
        rcall   send_bits_to_clk_data ; 10 + 6

        ; wait 12 us between bitpair
        delay_cycles 12*8-19

        dec     r20             ; 1 - decrement bitpair counter
        brne    fc3_bitloop     ; 2/1 - loop until done
fc3_next_byte:
        ; wait 2 us more between two bytes (16 cycles = -1 + 17)
        rcall   delay1us        ; 8
        rjmp    0f              ; 2
0:
        dec     r21             ; 1 - decrement byte counter
        brne    fc3_byteloop    ; 2/1 - loop until done

        ; release CLOCK and DATA
        in      r19, _SFR_IO_ADDR(IEC_OUT) ; read & mask unused IEC port lines
        andi    r19, ~(IEC_OBIT_DATA|IEC_OBIT_CLOCK|IEC_OBIT_ATN|IEC_OBIT_SRQ)
        out     _SFR_IO_ADDR(IEC_OUT), r19 ; release CLOCK and DATA

        sei
        ret

        ;;
        ;; Receive one byte using the FC3 save protocol
        ;;
        .global fc3_get_byte
fc3_get_byte:
        cli

        clr     r24     ; clear data byte

        ; wait a moment before releasing data, otherwise the loop would run
        ; too fast. I confess that this value is guessed.
        delay_cycles 10 * 8

        ; release DATA
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA

        ; wait until CLOCK goes high
1:
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK ; 1/2?
        rjmp    1b

        ; 17 us later...
        delay_cycles 17 * 8 - 6

        ; get bits 5,7 @ 0,2 - changes r19
        rcall   get_bits_from_clk_data  ; 4 + 8 r24 = .....7.5
        lsl     r24                     ; 1     r24 = ....7.5.

        ; 13 us later...
        delay_cycles 13 * 8 - 13

        ; get bits 4,6 @ 0,2 - changes r19
        rcall   get_bits_from_clk_data  ; 4 + 8 r24 = ....7654
        swap    r24                     ; 1     r24 = 7654....
        lsr     r24                     ; 1     r24 = .7654...

        ; 12 us later...
        delay_cycles 12 * 8 - 14

        ; get bits 1,3 @ 0,2 - changes r19
        rcall   get_bits_from_clk_data  ; 4 + 8 r24 = .76543.1
        lsl     r24                     ; 1     r24 = 76543.1.

        ; 10 us later...
        delay_cycles 10 * 8 - 13

        ; get bits 0,2 @ 0,2 - changes r19
        rcall   get_bits_from_clk_data  ; 4 + 8 r24 = 76543210

        ; Pull DATA down
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA

        sei
        com     r24     ; negate all bits
        clr     r25     ; clear hi-byte of return val
        ret
#endif

#ifdef CONFIG_LOADER_DREAMLOAD
        ;;
        ;; Receive a command (track/sector) using the DreamLoad protocol
        ;;
dreamload_get_command:
        rcall   dreamload_get_byte
        sts     fl_track, r24
        rcall   dreamload_get_byte
        sts     fl_sector, r24
        ret

        ;;
        ;; Receive a byte using the DreamLoad protocol
        ;;
        .global dreamload_get_byte
dreamload_get_byte:

        ldi     r18, 4  ; 4 * 2 bits to load
dl_bitloop:
        ; wait until clock goes low
1:
        sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    1b

        lsl     r24

        ; read data a short time later
        in      r19, _SFR_IO_ADDR(IEC_PIN)
        bst     r19, IEC_PIN_DATA
        bld     r24, 0

        ; wait until clock goes high
2:
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    2b

        lsl     r24

        ; read data a short time later
        in      r19, _SFR_IO_ADDR(IEC_PIN)
        bst     r19, IEC_PIN_DATA
        bld     r24, 0

        dec     r18
        brne     dl_bitloop

        com     r24     ; negate all bits
        ret

        ;;
        ;; Receive a command (track/sector) using the old DreamLoad protocol
        ;;
dreamload_get_command_old:
        rcall   dreamload_get_byte_old
        sts     fl_track, r24
        rcall   dreamload_get_byte_old
        sts     fl_sector, r24
        ret

        ;;
        ;; Receive a byte using the old DreamLoad protocol
        ;;
dreamload_get_byte_old:
        ; 2 nibbles
        ldi     r18, 2
dlgb_nibble:
        swap    r24                     ; 2nd loop: r24 = 7654....
        lsr     r24                     ; 2nd loop: r24 = .7654...

        rcall   wait_atn_low
        ; 1st: get bits 5,7 @ 0,2 / 2nd: get bits 1,3 @ 0,2 - changes r19
        rcall   get_bits_from_clk_data  ; 1st: r24 = .....7.5 / 2nd: .76543.1
        lsl     r24                     ; 1st: r24 = ....7.5. / 2nd: 76543.1.

        rcall   wait_atn_high
        ; 1st: get bits 4,6 @ 0,2 / 2nd: get bits 0,2 @ 0,2 - changes r19
        rcall   get_bits_from_clk_data  ; 1st: r24 = ....7654 / 2nd: 76543210

        dec     r18
        brne    dlgb_nibble

        com     r24     ; negate all bits
        ret

        ;;
        ;; Send the byte in r24 using the DreamLoad protocol
        ;;
        .global dreamload_send_byte
dreamload_send_byte:

        ; inverse all bits
        mov     r0, r24
        com     r0

        ldi     r18, 2          ; loop counter

dsb_bitloop:
        ; send r0[0,1] to CLOCK and DATA, shift r0 right two times
        ; changes r19
        rcall   send_bits_to_clk_data
        rcall   wait_atn_low

        ; send r0[0,1] to CLOCK and DATA, shift r0 right two times
        ; changes r19
        rcall   send_bits_to_clk_data
        rcall   wait_atn_high

        dec     r18             ; decrement bitpair counter
        brne    dsb_bitloop     ; loop until done
        ret
#endif

#ifdef CONFIG_LOADER_ULOAD3
        ;;
        ;; Receive a byte using the ULoad Model 3 protocol
        ;;
        .global uload3_get_byte
uload3_get_byte:
        cli
        ldi     r25, 0xff       ; prepare a negative return value
        clr     r24
        rcall   clk_data_handshake
        sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_ATN ;skip ret if ATN is high
        rjmp    uload3_abort                       ;return if ATN is low

        ;; assuming an average of 10 cycles between DATA high and the following instruction
        delay_cycles 14 * 8 - 10 - 4

        ;; read bits 7/5
        rcall   get_bits_from_clk_data ;4+8 r24 = _____7_5
        lsl     r24                    ;1   r24 = ____7_5_

        delay_cycles 10 * 8 - 13

        ;; read bits 6/4
        rcall   get_bits_from_clk_data ;4+8 r24 = ____7654
        swap    r24                    ;1   r24 = 7654____
        lsr     r24                    ;1   r24 = _7654___

        delay_cycles 14 * 8 - 14

        ;; read bits 3/1
        rcall   get_bits_from_clk_data ;4+8 r24 = _76543_1
        lsl     r24                    ;1   r24 = 76543_1_

        delay_cycles 10 * 8 - 13

        ;; read bits 2/0
        rcall   get_bits_from_clk_data ;4+8 r24 = 76543210

        delay_cycles 20*8       ; wait a bit so the C64 can return the bus to idle state

        clr     r25             ; clear upper byte of return value
        com     r24             ; invert data byte

uload3_abort:
        sei
        ret


        ;;
        ;; Send a byte using the ULoad Model 3 protocol
        ;;
        .global uload3_send_byte
uload3_send_byte:
        cli

        ;; DATA low
        sbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA

        ;; wait for CLOCK low
1:      sbic    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    1b

        ;; DATA high
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA

        ;; wait for CLOCK high - 2 to 5 cycles, assuming 3
1:      sbis    _SFR_IO_ADDR(IEC_PIN), IEC_PIN_CLOCK
        rjmp    1b

        ;; prepare transmission
        mov     r0, r24         ;1 - move data to output register
        com     r0              ;1 - invert byte
        ldi     r24, 4          ;1 - number of loops
        delay_cycles (14-8) * 8 - 6 + 6 + 3 ; initial delay before first bit pair

uload3_bitloop:
        delay_cycles 8 * 8 - 16 - 3   ; delay between bit pairs
        rcall   send_bits_to_clk_data ;10+6
        dec     r24                   ;1 - decrement pair counter
        brne    uload3_bitloop        ;2 - continue loop

        delay_cycles 10*8 - 9   ; delay before releasing clock/data

        ;; release CLOCK+DATA
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_CLOCK
        cbi     _SFR_IO_ADDR(IEC_OUT), IEC_OPIN_DATA
        rcall   delay1us        ; safety

        sei
        ret
#endif

        .end
