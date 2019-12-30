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

(* register read/write set analysis by abstract interpretation *)

type t_int = bint * SS.t (* a "sane" value and dependencies *)
type t_bool = SS.t  (* dependencies *)
type t_loc = SS.t * SS.t (* possible values and dependencies *)
type t_vec = SS.t (* dependencies *)
type t_lbl = SS.t (* dependencies *)
type t_ptr = SS.t (* dependencies *)

type word =
| BitVec of t_vec
| BitPtr of t_ptr

type t_word = SS.t (* dependencies *)

type 'a ref_t =
| IsInt : t_int ref_t
| IsBool : t_bool ref_t
| IsWord : int -> t_word ref_t
| IsLoc : int -> t_loc ref_t

type t_ctx = {
  rd : SS.t; (* read locations *)
  wt : SS.t; (* wrote locations *)
}

type 'a fallible = t_ctx -> ('a * t_ctx, string) result

let ctx_init = {
  rd = SS.empty;
  wt = SS.empty;
}

let ctx_branch ctx = ctx
let ctx_unbranch ctx = ctx
let ctx_merge _ ctx1 ctx2 = {
  rd = SS.union ctx1.rd ctx2.rd;
  wt = SS.union ctx1.wt ctx2.wt;
}
let ctx_to_string ctx =
  "rd: "^(SS.elements ctx.rd |> String.concat " ")^"\n"^
  "wt: "^(SS.elements ctx.wt |> String.concat " ")

let lift_int x = (x, SS.empty)
let lift_bool _ = SS.empty
let lift_vec _ _ = SS.empty
let lift_ptr _ _ = SS.empty
let lift_loc x _ = (SS.singleton x, SS.empty)
let lift_word x _ =
  match x with
  | BitVec x -> x
  | BitPtr x -> x

let lower_int x = fst x
let lower_bool _ = failwith "rw: cannot lower bool"
let lower_loc _ = failwith "rw: cannot lower loc"
let lower_vec _ = failwith "rw: cannot lower vec"
let lower_ptr _ = failwith "rw: cannot lower ptr"
let lower_word _ = failwith "rw: cannot lower word"

let string_of : type a. a ref_t -> a -> string =
  fun e v ->
  match e with
  | IsInt -> SS.elements (snd v) |> String.concat " "
  | IsBool -> SS.elements v |> String.concat " "
  | IsWord _ -> SS.elements v |> String.concat " "
  | IsLoc _ -> SS.elements (snd v) |> String.concat " "

let word_lift : type a. a ref_t -> _ -> t_word -> a fallible =
  fun e _ w ctx ->
  match e with
  | IsInt -> Ok ((BI.zero_big_int, w), ctx)
  | IsBool -> Ok (w, ctx)
  | IsWord _ -> Ok (w, ctx)
  | IsLoc _ -> failwith "word_lift does not expect loc output"

let word_lift2 : type a. a ref_t -> _ -> t_word * t_word -> a fallible =
  fun e _ (w1, w2) ctx ->
  let r = SS.union w1 w2 in
  match e with
  | IsInt -> Ok ((BI.zero_big_int, r), ctx)
  | IsBool -> Ok (r, ctx)
  | IsWord _ -> Ok (r, ctx)
  | IsLoc _ -> failwith "word_lift2 does not expect loc output"

(* stmt operations *)
let assert_ _ _ = ok ()

let assign s new_val _ (i, _) old_val ctx =
  if SS.mem i (fst s) then
    (* might write here *)
    let rd = SS.union (snd s) (SS.union new_val old_val) in
    Ok (rd, { ctx with wt = SS.add i ctx.wt })
  else
    (* cannot affect this loc *)
    Ok (old_val, ctx)

let store p new_val _ (_, _, _) _ old_val =
  ok (SS.union p (SS.union new_val old_val))

(* expr operations *)
let deref s _ _ ctx =
  let rd = SS.union (fst s) (snd s) in
  Ok (rd, { ctx with rd = SS.union (fst s) ctx.rd })

let fetch p _ _ = ok p

let index_bit h _ d = ok (SS.union h d)

let index_int h _ d = ok (SS.union h (snd d))

let slice h _ _ = h

let ife : type a. a ref_t -> t_bool -> a -> a -> a =
  fun e b v1 v2 ->
  match e with
  | IsInt -> (fst v1, SS.union b (SS.union (snd v1) (snd v2)))
  | IsBool -> SS.union b (SS.union v1 v2)
  | IsWord _ -> SS.union b (SS.union v1 v2)
  | IsLoc _ -> (SS.union (fst v1) (fst v2),
                SS.union b (SS.union (snd v1) (snd v2)))

let app_bv_to_len _ h _ = h
let app_bv_to_uint h _ = (BI.zero_big_int, h)
let app_uint_to_bv_l _ i = snd i
let app_checkbit h i _ = ok (SS.union h i)
let app_checkfield h _ _ _ = ok h
let app_flag_set h _ i = ok (SS.union h (snd i))
let app_flag_unset h _ i = ok (SS.union h (snd i))
let app_rotate_left h1 h2 _ = SS.union h1 h2
let app_rotate_right h1 h2 _ = SS.union h1 h2

(* unops *)
let neg x = x
let log_not x = x
let bit_not x = x

(* binops *)
let add x1 x2 = (fst x1, SS.union (snd x1) (snd x2))
let sub x1 x2 = (fst x1, SS.union (snd x1) (snd x2))
let mul x1 x2 = (fst x1, SS.union (snd x1) (snd x2))
let div x1 x2 = (fst x1, SS.union (snd x1) (snd x2))
let pow x1 x2 = (fst x1, SS.union (snd x1) (snd x2))
let eq_int x1 x2 = SS.union (snd x1) (snd x2)
let eq_bool x1 x2 = SS.union x1 x2
let eq_loc x1 x2 = SS.union (snd x1) (snd x2)
let eq_vec x1 x2 = SS.union x1 x2
let eq_ptr x1 x2 = SS.union x1 x2
let lt x1 x2 = SS.union (snd x1) (snd x2)
let gt x1 x2 = SS.union (snd x1) (snd x2)
let badd_vec x1 x2 = SS.union x1 x2
let badd_ptr x1 x2 = SS.union x1 x2
let bsub_vec x1 x2 = SS.union x1 x2
let bsub_ptr x1 x2 = SS.union x1 x2
let bmul x1 x2 = SS.union x1 x2
let blt x1 x2 = SS.union x1 x2
let bgt x1 x2 = SS.union x1 x2
let bslt x1 x2 = SS.union x1 x2
let bsgt x1 x2 = SS.union x1 x2
let lshift x1 x2 = SS.union x1 x2
let rshift x1 x2 = SS.union x1 x2
let log_and x1 x2 = SS.union x1 x2
let log_or x1 x2 = SS.union x1 x2
let log_xor x1 x2 = SS.union x1 x2
let bit_and x1 x2 = SS.union x1 x2
let bit_or x1 x2 = SS.union x1 x2
let bit_xor x1 x2 = SS.union x1 x2
