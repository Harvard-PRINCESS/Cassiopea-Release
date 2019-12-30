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


open Util

(* interface to a value domain *)

module type Value = sig
  type t_int
  type t_bool
  type t_vec
  type t_ptr
  type t_loc

  type word =
  | BitVec of t_vec
  | BitPtr of t_ptr

  type t_word

  (* type witness *)
  type 'a ref_t =
  | IsInt : t_int ref_t
  | IsBool : t_bool ref_t
  | IsWord : int -> t_word ref_t
  | IsLoc : int -> t_loc ref_t

  (* additional context to carry in state *)
  type t_ctx

  val ctx_init : t_ctx
  val ctx_branch : t_ctx -> t_ctx   (* inform context of branch *)
  val ctx_unbranch : t_ctx -> t_ctx (* inform context of branch end without merge *)
  val ctx_merge : t_bool -> t_ctx -> t_ctx -> t_ctx (* merge branched contexts *)
  val ctx_to_string : t_ctx -> string

  (* operations that can fail *)
  (* operation failure would be due to type system limitations:
     1. bitvector index out of bounds
     2. bitvector/pointer word type mismatch
     3. load/store memory region size mismatch *)
  type 'a fallible = t_ctx -> ('a * t_ctx, string) result

  (* relating this value domain to the concrete value domain *)
  (* concrete -> this *)
  val lift_int : bint -> t_int
  val lift_bool : bool -> t_bool
  val lift_loc : id -> int -> t_loc
  val lift_vec : bits -> int -> t_vec
  val lift_ptr : id * bits -> int -> t_ptr
  val lift_word : word -> int -> t_word
  (* this -> concrete *)
  val lower_int : t_int -> bint
  val lower_bool : t_bool -> bool
  val lower_loc : t_loc -> id
  val lower_vec : t_vec -> bits
  val lower_ptr : t_ptr -> id * bits
  val lower_word : t_word -> word

  (* printing *)
  val string_of : 'a ref_t -> 'a -> string

  (* word functor map *)
  val word_lift : 'a ref_t ->
    (word -> 'a fallible) -> t_word -> 'a fallible

  val word_lift2 : 'a ref_t ->
    (word * word -> 'a fallible) -> t_word * t_word -> 'a fallible

  (* statement operations *)
  val assert_ : string -> t_bool -> unit fallible
  val assign :
    t_loc (*loc to assign to*) ->
    t_word (*value to assign*) -> int (*value length*) ->
    id * int (*one register, len*) ->
    t_word (*current value*) ->
    t_word fallible (*new value*)
  val store :
    t_ptr (*ptr to store to*) ->
    t_word (*value to store*) -> int (*value length*) ->
    id * int * int (*one region, word len, size*) -> bits (*one offset*) ->
    t_word -> (*current value*)
    t_word fallible (*new value*)

  (* expressions *)
  val deref : t_loc -> int (*length*) ->
    (t_word * int) SM.t (*registers*) ->
    t_word fallible
  val fetch : t_ptr -> int (*length*) ->
    (int * int * (t_word BM.t)) SM.t (*memory*) ->
    t_word fallible
  val index_bit : t_vec -> int -> t_vec -> t_bool fallible
  val index_int : t_vec -> int -> t_int -> t_bool fallible
  val slice : t_vec -> int -> int -> t_vec
  val ife : 'a ref_t -> t_bool -> 'a -> 'a -> 'a

  (* built-ins *)
  val app_bv_to_len : bint -> t_vec -> int -> t_vec
  val app_bv_to_uint : t_vec -> int -> t_int
  val app_uint_to_bv_l : bint -> t_int -> t_vec
  val app_checkbit : t_vec -> t_vec -> int -> t_bool fallible
  val app_checkfield : t_vec -> int -> bint -> bint -> t_vec fallible
  val app_flag_set : t_vec -> int -> t_int -> t_vec fallible
  val app_flag_unset : t_vec -> int -> t_int -> t_vec fallible
  val app_rotate_left : t_vec -> t_vec -> int -> t_vec
  val app_rotate_right : t_vec -> t_vec -> int -> t_vec

  (* unops *)
  val neg : t_int -> t_int
  val log_not : t_bool -> t_bool
  val bit_not : t_vec -> t_vec

  (* binops *)
  val add : t_int -> t_int -> t_int
  val sub : t_int -> t_int -> t_int
  val mul : t_int -> t_int -> t_int
  val div : t_int -> t_int -> t_int
  val pow : t_int -> t_int -> t_int
  val eq_int : t_int -> t_int -> t_bool
  val eq_bool : t_bool -> t_bool -> t_bool
  val eq_vec : t_vec -> t_vec -> t_bool
  val eq_ptr : t_ptr -> t_ptr -> t_bool
  val eq_loc : t_loc -> t_loc -> t_bool
  (* neq is defined: negate the output of eq *)
  val lt : t_int -> t_int -> t_bool
  val gt : t_int -> t_int -> t_bool
  val badd_vec : t_vec -> t_vec -> t_vec
  val badd_ptr : t_ptr -> t_vec -> t_ptr
  val bsub_vec : t_vec -> t_vec -> t_vec
  val bsub_ptr : t_ptr -> t_vec -> t_ptr
  val bmul : t_vec -> t_vec -> t_vec
  val blt : t_vec -> t_vec -> t_bool
  val bgt : t_vec -> t_vec -> t_bool
  val bslt : t_vec -> t_vec -> t_bool
  val bsgt : t_vec -> t_vec -> t_bool
  val lshift : t_vec -> t_vec -> t_vec
  val rshift : t_vec -> t_vec -> t_vec
  val log_and : t_bool -> t_bool -> t_bool
  val log_or : t_bool -> t_bool -> t_bool
  val log_xor : t_bool -> t_bool -> t_bool
  val bit_and : t_vec -> t_vec -> t_vec
  val bit_or : t_vec -> t_vec -> t_vec
  val bit_xor : t_vec -> t_vec -> t_vec
end
