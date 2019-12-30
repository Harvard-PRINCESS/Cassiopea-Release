let stackreg : register = RSP
let basereg : register = RIP
let kernel_stack : word = 0b0000000000000000000000000000000000000000000000000000000000000000
let kernel_stack_size : word = 0b0000000000000000000000000000000000000000000000000000000000001000
let STACKLEN : int = 4
def check_base (base : word) -> bool = 
true
def get_stack (base : word) (stack_offset : word) -> word = 
 ( base ) b+ ( stack_offset ) 
letstate stack : 64 bit 4 len 64 ref memory
let base : 64 bit = *basereg

frame:



pre:
(  ( check_base ( base ) ) && (  ( get_stack ( base, kernel_stack ) ) == ( [stack, 0] )  )  ) 
post:
(  ( *stackreg ) == (  ( [stack, 0] ) b+ ( kernel_stack_size )  )  )
