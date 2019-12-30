letstate Mem : 32 bit 5 len 32 ref  memory
let reg1 : register = R0
let reg2 : register = R1
let reg3 : register = R2
let reg4 : register = R3
let reg5 : register = R4
let base : word = [Mem, 0]
let v1 : word = fetch[ ( base ) b+ ( 0b00000000000000000000000000000000 ) ,32]
let v2 : word = fetch[ ( base ) b+ ( 0b00000000000000000000000000000100 ) ,32]
let v3 : word = fetch[ ( base ) b+ ( 0b00000000000000000000000000001000 ) ,32]
let v4 : word = fetch[ ( base ) b+ ( 0b00000000000000000000000000001100 ) ,32]
let v5 : word = fetch[ ( base ) b+ ( 0b00000000000000000000000000010000 ) ,32]

frame:
reg-modify :  N Z C V R5


pre:
(  ( *reg1 ) == ( base )  ) 
post:
(  (  (  (  (  ( *reg1 ) == ( v1 )  ) && (  ( *reg2 ) == ( v2 )  )  ) && (  ( *reg3 ) == ( v3 )  )  ) && (  ( *reg4 ) == ( v4 )  )  ) && (  ( *reg5 ) == ( v5 )  )  )
