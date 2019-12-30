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

open Monad

(* value type for normal cassiopeia concrete evaluation *)
type t_int = bint
type t_vec = bits
type t_ptr = id * bits
type t_lbl = id
type t_bool = bool
type t_loc = id

type word =
| BitVec    of t_vec
| BitPtr    of t_ptr

type t_word = word

type 'a ref_t =
| IsInt : t_int ref_t
| IsBool : t_bool ref_t
| IsWord : int -> t_word ref_t
| IsLoc : int -> t_loc ref_t

(* shorthand for registers and memory *)
type t_reg = (t_word * int) SM.t
type t_mem = (int * int * int * (t_word * int) IM.t) SM.t

type t_ctx = unit

type 'a ret = t_ctx -> 'a
type 'a fallible = t_ctx -> ('a * t_ctx, string) result

let ctx_init = ()
let ctx_to_string _c = ""
let ctx_branch _ = ()
let ctx_unbranch _ = ()
let ctx_merge _ _ _ = ()

let id x = x
let lift_int = id
let lift_bool = id
let lift_vec v _ = v
let lift_ptr p _ = p
let lift_loc i _ = i
let lift_word w _ = w

let lower_int = id
let lower_bool = id
let lower_vec = id
let lower_ptr = id
let lower_loc = id
let lower_word = id

let string_of : type a. a ref_t -> a -> string =
  fun e v ->
  match e with
  | IsInt -> "int:"^(string_of_bint v)
  | IsBool -> if v then "bool:true" else "bool:false"
  | IsWord _ ->
    (match v with
    | BitVec v -> "bv:"^(Bits.to_hexstring v)
    | BitPtr (i, o) -> "ptr:"^i^"["^(Bits.to_hexstring o)^"]")
  | IsLoc _ -> "loc:&"^v

let word_lift _ f w = f w

let word_lift2 _ f (w1, w2) = f (w1, w2)

(* stmt operations *)
let assert_ s (b: t_bool) =
  if b then
    ok ()
  else
    error s

let assign s new_val len (i, sz) old_val =
  if s = i then
    (* length check *)
    if len <> sz then
      failwith ("assign: size mismatch: register "^
                i^" holds values of size "^
                (string_of_int sz)^" but got "^
                (string_of_int len))
    else
      ok new_val
  else
    ok old_val

let store p new_val len (region, wordsz, maxoff) off old_val =
  let (i, o) = p in (* i: id, o: bits (should be correct size) *)
  if i <> region then
    ok old_val
  else if len <> wordsz then
    (* length check *)
    error ("store: length mismatch: length "^
            (string_of_int len)^" does not match region "^
            region^" which holds word length "^(string_of_int wordsz))
  else if not (Bits.check_byte_align o (wordsz / 8)) then (* alignment check *)
    error ("store: misalignment: offset "^(string_of_int (Bits.to_int o))^
            " is not aligned (byte index) for region "^i)
  else
    (* boundary check *) (* o < 0 || maxoff <= o *)
    if not (Bits.check_boundary o (maxoff * (wordsz / 8))) then
      error ("store: boundary violation: offset "^
              (string_of_int (Bits.to_int o))^" is out of bounds for region "^
              region^" with size "^(string_of_int (maxoff * (wordsz / 8))))
    else if (Bits.compare o off) <> 0 then
      ok old_val
    else
      ok new_val

(* expr operations *)
let deref s len reg =
  match SM.find_opt s reg with
  | None ->
    failwith ("deref: deref of nonexistent state "^s)
  | Some (h, l) ->
    (* length check *)
    if len <> l then
      failwith ("deref: size mismatch: register "^
                s^" holds values of size "^
                (string_of_int l)^" but deref expected "^
                (string_of_int len))
    else
      ok h

let fetch p len mem =
  let (i, o) = p in
  match SM.find_opt i mem with
  | None ->
    error ("fetch: memory region "^i^" does not exist")
  | Some (wordsz, maxoff, region) ->
    (* length check *)
    if len <> wordsz then
      error ("fetch: length mismatch: length "^
              (string_of_int len)^" does not match region "^
              i^" which holds word length "^(string_of_int wordsz))
    (* alignment check *)
    else if not (Bits.check_byte_align o (wordsz / 8)) then
      error ("fetch: misalignment: offset "^
              (string_of_int (Bits.to_int o))^
              " is not aligned (byte index) for region "^i)
    (* boundary check *)
    else if not (Bits.check_boundary o (maxoff * (wordsz / 8))) then
      error ("fetch: boundary violation: offset "^
              (string_of_int (Bits.to_int o))^
              " is out of bounds for region "^
              i^" with size "^(string_of_int (maxoff * (wordsz / 8))))
    else
      match BM.find_opt o region with
      | None ->
        failwith ("fetch: missing offset "^(Bits.to_bitstring o)^" in region "^i)
      | Some h ->
      ok h

let index_bit h l d =
  let d = Bits.to_big_int d in
  if 0 > int_of_bint d || l <= int_of_bint d then
    error "index: out of range"
  else
    ok (Bits.get h d)

let index_int h l d =
  if 0 > int_of_bint d || l <= int_of_bint d then
    error "index: out of range"
  else
    ok (Bits.get h d)

let slice h d1 d2 =
  let w = d2 - d1 in
  Bits.of_big_int w (Bits.to_big_int (Bits.rshift h (bint_of_int d1)))

let ife : type a. a ref_t -> _ =
  fun e b v1 v2 ->
  match e with
  | IsInt -> if b then v1 else v2
  | IsBool -> if b then v1 else v2
  | IsWord _ -> if b then v1 else v2
  | IsLoc _ -> if b then v1 else v2

let app_bv_to_len len h _ =
  Bits.of_big_int (int_of_bint len) (Bits.to_big_int h)

let app_bv_to_uint h _ =
  Bits.to_big_int h

let app_uint_to_bv_l len i =
  Bits.of_big_int (int_of_bint len) i

let app_checkbit h i _ =
  ok (Bits.getbit h i)

let app_checkfield h l i1 i2 =
  ok (Bits.getfield h (bint_of_int l) i1 i2)

let app_flag_set h _ i =
  ok (Bits.set h i)

let app_flag_unset h _ i =
  ok (Bits.unset h i)

let app_rotate_left h1 h2 _ =
  Bits.rotl h1 (Bits.to_big_int h2)

let app_rotate_right h1 h2 _ =
  Bits.rotr h1 (Bits.to_big_int h2)

(* unops *)
let neg = BI.minus_big_int
let log_not = not
let bit_not = Bits.not

(* binops *)
let add = BI.add_big_int
let sub = BI.sub_big_int
let mul = BI.mult_big_int
let div = BI.div_big_int
let pow = BI.power_big_int_positive_big_int
let eq_int = BI.eq_big_int
let eq_vec h1 h2 = Bits.bits_compare h1 h2 = 0
let eq_ptr (i1, o1) (i2, o2) = i1 = i2 && (Bits.compare o1 o2 == 0)
let eq_bool = (=)
let eq_loc = (=)
let lt = BI.lt_big_int
let gt = BI.gt_big_int

let badd_vec = Bits.add
let bsub_vec = Bits.sub
let bmul = Bits.mul
let blt = Bits.ult
let bgt = Bits.ugt
let bslt = Bits.slt
let bsgt = Bits.sgt
let lshift h1 h2 = Bits.lshift h1 (Bits.to_big_int h2)
let rshift h1 h2 = Bits.rshift h1 (Bits.to_big_int h2)
let log_and = (&&)
let log_or = (||)
let log_xor = (<>)
let bit_and = Bits.and_
let bit_or = Bits.or_
let bit_xor = Bits.xor

let badd_ptr h1 h2 =
  (* h1: memory pointer, h2: bitvector *)
  let (i, o) = h1 in
  (i, Bits.add o h2)

let bsub_ptr h1 h2 =
  (* h1: memory pointer, h2: bitvector *)
  let (i, o) = h1 in
  (i, Bits.sub o h2)
