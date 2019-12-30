let outreg : register = R1
let dispreg : register = R2
let pcreg : register = R14
def disabled_flgT  -> bool = 
 ( *C ) == ( 0b1 ) 
def disabled_flgF  -> bool = 
 ( *C ) == ( 0b0 ) 
def critlow_flgT  -> bool = 
! (  (  ( *Z ) == ( 0b0 )  ) && (  ( *C ) == ( 0b1 )  )  )
def critlow_flgF  -> bool = 
 (  ( *Z ) == ( 0b0 )  ) && (  ( *C ) == ( 0b1 )  ) 
def crithigh_flgT  -> bool = 
 ( *C ) == ( 0b0 ) 
def crithigh_flgF  -> bool = 
! (  ( *C ) == ( 0b0 )  )
def enabled_flag  -> bool = 
 ( *Z ) == ( 0b1 ) 
def disabled_flag  -> bool = 
 ( *Z ) == ( 0b0 ) 
letstate Mem : 32 bit 1 len 32 ref  memory
def disp_disabled  -> word = 
[Mem, 0]
def disabled_rescheck (rreg : register) (rbv : word) -> bool = 
 ( rbv ) == ( *rreg ) 
let mp : 32 bit = disp_disabled (  )
let out : 32 bit = fetch[mp,32]
let b_not_zero : bool = ! (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000000 ) )  )

frame:
reg-modify :  N Z C V


pre:
(  (  ( *dispreg ) == ( mp )  ) && (  (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000000 ) )  ) || (  ( out ) == ( bv_to_len ( wordsize, 0b0000000000000000000000000000000000000000000000000000000000000001 ) )  )  )  ) 
post:
(  (  ( disabled_rescheck ( outreg, out ) ) && (  ( ! ( b_not_zero ) ) || ( disabled_flgT (  ) )  )  ) && (  ( b_not_zero ) || ( disabled_flgF (  ) )  )  )
