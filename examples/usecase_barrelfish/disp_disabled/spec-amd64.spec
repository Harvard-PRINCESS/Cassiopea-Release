letstate Mem : 64 bit 1 len 64 ref  memory
let dispreg : register = RCX
let outreg : register = RBX
def disp_disabled  -> word = 
[Mem, 0]
def disabled_flgT  -> bool = 
 ( *C ) == ( 0b0 ) 
def disabled_flgF  -> bool = 
 (  ( *C ) == ( 0b0 )  ) && (  ( *Z ) == ( 0b1 )  ) 
def disabled_rescheck (rreg : register) (rbv : word) -> bool = 
true
let mp : 64 bit = disp_disabled (  )
let out : 64 bit = fetch[mp,64]
let b_not_zero : bool = ! (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000000 ) )  )

frame:
reg-modify :  C Z


pre:
(  (  ( *dispreg ) == ( mp )  ) && (  (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000000 ) )  ) || (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000001 ) )  )  )  ) 
post:
(  (  ( disabled_rescheck ( outreg, out ) ) && (  ( ! ( b_not_zero ) ) || ( disabled_flgT (  ) )  )  ) && (  ( b_not_zero ) || ( disabled_flgF (  ) )  )  )
