(****************************************************************************************
BSD License

Copyright (c) 2016-2019, Harvard University
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

    Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.

    Neither the name of the copyright holder nor the names of its
    contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
****************************************************************************************)



(* bit vector interface to Big_int *)

type t

val bits_compare : t -> t -> int
val compare : t -> t -> int
val extend : t -> int -> t

val zero: int(*width*) -> t

val width: t -> int

val add: t -> t -> t
val sub : t -> t -> t
val mul: t -> t -> t
val ult: t -> t -> bool
val ugt: t -> t -> bool
val slt: t -> t -> bool
val sgt: t -> t -> bool
val get: t -> Big_int.big_int -> bool
val getbit: t -> t -> bool
val getfield: t -> Big_int.big_int -> Big_int.big_int -> Big_int.big_int -> t
val set: t -> Big_int.big_int -> t
val unset: t -> Big_int.big_int -> t
val not: t -> t
val and_: t -> t -> t
val or_: t -> t -> t
val xor: t -> t -> t
val lshift: t -> Big_int.big_int -> t
val rshift: t -> Big_int.big_int -> t
val rotl: t -> Big_int.big_int -> t
val rotr: t -> Big_int.big_int -> t
val concat: t -> t -> t
val check_byte_align: t -> int -> bool
val check_boundary: t -> int -> bool
val get_max: int -> t

val of_int: int(*width*) -> int -> t
val of_big_int : int(*width*) -> Big_int.big_int -> t

val to_int : t -> int
val to_big_int : t -> Big_int.big_int
val to_big_int_signed : t -> Big_int.big_int

val of_string : string -> t
val to_string : t -> string
val to_hexstring: t -> string
val to_bitstring: t -> string
val to_hexdecimalstring: t -> string
val to_binarystring: t -> string
val to_xstring: t -> string
val to_bstring: t -> string
