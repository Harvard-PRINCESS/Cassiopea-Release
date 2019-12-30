letstate BASE : 32 bit 4 len 32 ref  memory
let stackreg : gpreg = r29
let basereg : gpreg = r4
let kernel_stack : word = 0b00000000000000000000000000000000
let kernel_stack_size : word = 0b00000000000000000000000000001000
let STACKLEN : int = 4
def check_base (base : word) -> bool = 
 ( base ) == ( [BASE, 0] ) 
def get_stack (base : word) (stack_offset : word) -> word = 
let addr : word =  ( base ) b+ ( stack_offset )  in fetch[addr,32]
letstate stack : 32 bit 4 len 32 ref memory
let base : 32 bit = *basereg

frame:



pre:
(  ( check_base ( base ) ) && (  ( get_stack ( base, kernel_stack ) ) == ( [stack, 0] )  )  )  &&  ( *r0 ) == ( 0b00000000000000000000000000000000 ) 
post:
(  ( *stackreg ) == (  ( [stack, 0] ) b+ ( kernel_stack_size )  )  ) &&  ( *r0 ) == ( 0b00000000000000000000000000000000 ) 
