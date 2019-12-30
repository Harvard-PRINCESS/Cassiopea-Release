(* github issue #159, failure case *)
let ptr: 32 bit = [allmem, 0]
frame:
  reg-modify: r
pre: true
post:
   fetch[ptr, 32] == 0x00000001

