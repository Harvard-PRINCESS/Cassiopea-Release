def interrupts_are_on  -> bool =  *irqen == 0b1
let f: 1 bit = *fpuen
let e: 1 bit = *bigendian
let l: 1 bit = *longmode
frame:
  reg-modify: r0
pre: interrupts_are_on() == false
post: interrupts_are_on() == true &&
   *fpuen == f &&
   *bigendian == e &&
   *longmode == l
