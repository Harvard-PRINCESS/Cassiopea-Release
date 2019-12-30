letstate Mem : 32 bit 1 len 32 ref  memory
let outreg : gpreg = r4
let dispreg : gpreg = r28
def disp_disabled  -> word = 
[Mem, 0]
def disabled_flgT  -> bool = 
 ( *r2 ) == ( 0b00000000000000000000000000000000 ) 
def disabled_flgF  -> bool = 
 ( *r2 ) == ( 0b00000000000000000000000000000001 ) 
def disabled_rescheck (rreg : gpreg) (rbv : word) -> bool = 
 ( rbv ) == ( *rreg ) 
let mp : 32 bit = disp_disabled (  )
let out : 32 bit = fetch[mp,32]
let b_not_zero : bool = ! (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000000 ) )  )

frame:
reg-modify :  r2


pre:
(  (  ( *dispreg ) == ( mp )  ) && (  (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000000 ) )  ) || (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000001 ) )  )  )  )  &&  ( *r0 ) == ( 0b00000000000000000000000000000000 ) 
post:
(  (  ( disabled_rescheck ( outreg, out ) ) && (  ( ! ( b_not_zero ) ) || ( disabled_flgT (  ) )  )  ) && (  ( b_not_zero ) || ( disabled_flgF (  ) )  )  ) &&  ( *r0 ) == ( 0b00000000000000000000000000000000 ) 
