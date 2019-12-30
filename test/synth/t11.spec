(* this is the same as verify/t02.spec *)
let x0: 8 bit = *r0
let x1: 8 bit = *r1
let x2: 8 bit = *r2
let x3: 8 bit = *r3
frame:
pre: true
post: *r0 == x0 b+ x1 b+ x2 b+ x3
