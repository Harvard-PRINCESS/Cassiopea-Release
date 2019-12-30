letstate BASE : 32 bit 4 len 32 ref  memory
letstate dcb_struct : 32 bit 1 len 32 ref  memory
let basereg : gpreg = r4
let dispreg : gpreg = r28
let dcb_current_idx : word = 0b00000000000000000000000000000000
let dcb_disp : word = 0b00000000000000000000000000001000
let DCBLEN : int = 4
def check_base (base : word) (dcb_offset : word) -> bool = 
let addr : word =  ( base ) b+ ( dcb_offset )  in  (  ( base ) == ( [BASE, 0] )  ) && (  ( fetch[addr,32] ) == ( [dcb_struct, 0] )  ) 
def get_dcb (base : word) (dcb_offset : word) -> word = 
let addr : word =  ( base ) b+ ( dcb_offset )  in fetch[fetch[addr,32],32]
def get_disp (addr : word) -> word = 
fetch[addr,32]
letstate dcb : 32 bit 4 len 32 ref memory
let base : 32 bit = *basereg
let dispaddr : 32 bit =  ( [dcb, 0] ) b+ ( dcb_disp ) 
let val : 32 bit = fetch[dispaddr,32]

frame:



pre:
(  ( check_base ( base, dcb_current_idx ) ) && (  ( get_dcb ( base, dcb_current_idx ) ) == ( [dcb, 0] )  )  )  &&  ( *r0 ) == ( 0b00000000000000000000000000000000 ) 
post:
(  ( *dispreg ) == ( val )  ) &&  ( *r0 ) == ( 0b00000000000000000000000000000000 ) 
