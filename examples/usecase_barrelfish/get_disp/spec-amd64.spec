letstate BASE : 64 bit 4 len 64 ref  memory
let basereg : register = RIP
let dispreg : register = RDI
let dcb_current_idx : word = 0b0000000000000000000000000000000000000000000000000000000000000000
let dcb_disp : word = 0b0000000000000000000000000000000000000000000000000000000000001000
let DCBLEN : int = 4
def check_base (base : word) (dcb_offset : word) -> bool = 
 ( base ) == ( [BASE, 0] ) 
def get_dcb (base : word) (dcb_offset : word) -> word = 
let addr : word =  ( base ) b+ ( dcb_offset )  in fetch[addr,64]
def get_disp (addr : word) -> word = 
fetch[addr,64]
letstate dcb : 64 bit 4 len 64 ref memory
let base : 64 bit = *basereg
let dispaddr : 64 bit =  ( [dcb, 0] ) b+ ( dcb_disp ) 
let val : 64 bit = fetch[dispaddr,64]

frame:



pre:
(  ( check_base ( base, dcb_current_idx ) ) && (  ( get_dcb ( base, dcb_current_idx ) ) == ( [dcb, 0] )  )  ) 
post:
(  ( *dispreg ) == ( val )  )
