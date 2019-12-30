(* github issue #159, base case *)
let ptr: 32 bit = [allmem, 0]
frame:
pre: true
post:
   *r == 0x00000001
