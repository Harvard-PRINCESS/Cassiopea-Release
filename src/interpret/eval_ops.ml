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
open Reps
open Casp_ast

open Monad
open Value
open Config

(* unop, binop, and builtin-function helpers for Eval *)

module EvalOps = functor
  (V : Value)
  (C : module type of Config(V)) ->
struct
  open V
  open C

  let app_unop pos u v =
    match (u, v) with
    | (Neg, ValInt d) ->
      ok_int (V.neg d)
    | (Neg, _) ->
      failat pos "type error: attempted negation of non-integer"
    | (LogNot, ValBool b) ->
      ok_bool (V.log_not b)
    | (LogNot, _) ->
      failat pos "type error: attempted logical not of non-boolean"
    | (BitNot, ValWord (h, l)) ->
      let do_bitnot w =
        match w with
        | V.BitVec h ->
          word_of_vec (ok (V.bit_not h)) l
        | _ ->
          error "bnot: got a pointer"
      in
      get_word pos (V.word_lift (V.IsWord l) do_bitnot h) l
    | (BitNot, _) ->
      failat pos "type error: attempted bitwise not of non-bitvector"

  let app_binop pos b (v1, v2) =
    let check_len b l1 l2 =
      if l1 <> l2 then
        failat pos ("type error: attempted "^(name_of_binop b)^
                    " of different lengths: "^
                    (string_of_int l1)^" and "^
                    (string_of_int l2))
      else
        ()
    in
    match (b, v1, v2) with
    | (Add, ValInt d1, ValInt d2) ->
      ok_int (V.add d1 d2)
    | (Add, _, _) ->
      failat pos "type error: attempted add of non-integer"
    | (Sub, ValInt d1, ValInt d2) ->
      ok_int (V.sub d1 d2)
    | (Sub, _, _) ->
      failat pos "type error: attempted sub of non-integer"
    | (Mul, ValInt d1, ValInt d2) ->
      ok_int (V.mul d1 d2)
    | (Mul, _, _) ->
      failat pos "type error: attempted mul of non-integer"
    | (Div, ValInt d1, ValInt d2) ->
      ok_int (V.div d1 d2)
    | (Div, _, _) ->
      failat pos "type error: attempted div of non-integer"
    | (Pow, ValInt d1, ValInt d2) ->
      ok_int (V.pow d1 d2)
    | (Pow, _, _) ->
      failat pos "type error: attempted pow of non-integer"
    | (Eq, ValInt d1, ValInt d2) ->
      ok_bool (V.eq_int d1 d2)
    | (Eq, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_eq w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          ok (V.eq_vec h1 h2)
        | (V.BitPtr m1, V.BitPtr m2) ->
          ok (V.eq_ptr m1 m2)
        | _ ->
          ok (V.lift_bool false)
      in
      check_len Eq l1 l2;
      get_bool pos (V.word_lift2 V.IsBool do_eq (w1, w2))
    | (Eq, ValBool b1, ValBool b2) ->
      ok_bool (V.eq_bool b1 b2)
    | (Eq, ValLoc (s1, l1), ValLoc (s2, l2)) ->
      check_len Eq l1 l2;
      ok_bool (V.eq_loc s1 s2)
    | (Eq, _, _) ->
      failat pos "type error: attempted eq of two different types"
    | (Neq, ValInt d1, ValInt d2) ->
      ok_bool (V.log_not (V.eq_int d1 d2))
    | (Neq, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_neq w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          ok (V.log_not (V.eq_vec h1 h2))
        | (V.BitPtr m1, V.BitPtr m2) ->
          ok (V.log_not (V.eq_ptr m1 m2))
        | _ ->
          ok (V.lift_bool true)
      in
      check_len Neq l1 l2;
      get_bool pos (V.word_lift2 V.IsBool do_neq (w1, w2))
    | (Neq, ValBool b1, ValBool b2) ->
      ok_bool (V.log_not (V.eq_bool b1 b2))
    | (Neq, ValLoc (s1, l1), ValLoc (s2, l2)) ->
      check_len Neq l1 l2;
      ok_bool (V.log_not (V.eq_loc s1 s2))
    | (Neq, _, _) ->
      failat pos "type error: attempted neq of two different types"
    | (Lt, ValInt d1, ValInt d2) ->
      ok_bool (V.lt d1 d2)
    | (Lt, _, _) ->
      failat pos "type error: attempted lt of non-integer"
    | (Gt, ValInt d1, ValInt d2) ->
      ok_bool (V.gt d1 d2)
    | (Gt, _, _) ->
      failat pos "type error: attempted gt of non-integer"
    | (BAdd, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_badd w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.badd_vec h1 h2)) l1
        | (V.BitPtr h1, V.BitVec h2) ->
          word_of_ptr (ok (V.badd_ptr h1 h2)) l1
        | _ ->
          error "badd: got two pointers"
      in
      check_len BAdd l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_badd (w1, w2)) l1
    | (BAdd, _, _) ->
      failat pos "type error: attempted b+ of non-bitvector"
    | (BSub, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bsub w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.bsub_vec h1 h2)) l1
        | (V.BitPtr h1, V.BitVec h2) ->
          word_of_ptr (ok (V.bsub_ptr h1 h2)) l1
        | _ ->
          error "bsub: got a pointer"
      in
      check_len BSub l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_bsub (w1, w2)) l1
    | (BSub, _, _) ->
      failat pos "type error: attempted b- of non-bitvector"
    | (BMul, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bmul w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.bmul h1 h2)) l1
        | _ ->
          error "bmul: got a pointer"
      in
      check_len BMul l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_bmul (w1, w2)) l1
    | (BMul, _, _) ->
      failat pos "type error: attempted b* of non-bitvector"
    | (BLt, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_blt w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          ok (V.blt h1 h2)
        | _ ->
          error "blt: got a pointer"
      in
      check_len BLt l1 l2;
      get_bool pos (V.word_lift2 V.IsBool do_blt (w1, w2))
    | (BLt, _, _) ->
      failat pos "type error: attempted b< of non-bitvector"
    | (BGt, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bgt w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          ok (V.bgt h1 h2)
        | _ ->
          error "bgt: got a pointer"
      in
      check_len BGt l1 l2;
      get_bool pos (V.word_lift2 V.IsBool do_bgt (w1, w2))
    | (BGt, _, _) ->
      failat pos "type error: attempted b> of non-bitvector"
    | (BSLt, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bslt w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          ok (V.bslt h1 h2)
        | _ ->
          error "bslt: got a pointer"
      in
      check_len BSLt l1 l2;
      get_bool pos (V.word_lift2 V.IsBool do_bslt (w1, w2))
    | (BSLt, _, _) ->
      failat pos "type error: attempted bs< of non-bitvector"
    | (BSGt, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bsgt w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          ok (V.bsgt h1 h2)
        | _ ->
          error "bsgt: got a pointer"
      in
      check_len BSGt l1 l2;
      get_bool pos (V.word_lift2 V.IsBool do_bsgt (w1, w2))
    | (BSGt, _, _) ->
      failat pos "type error: attempted bs> of non-bitvector"
    | (LShift, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_lshift w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.lshift h1 h2)) l1
        | _ ->
          error "lshift: got a pointer"
      in
      check_len LShift l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_lshift (w1, w2)) l1
    | (LShift, _, _) ->
      failat pos "type error: attempted << of non-bitvector"
    | (RShift, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_rshift w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.rshift h1 h2)) l1
        | _ ->
          error "rshift: got a pointer"
      in
      check_len RShift l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_rshift (w1, w2)) l1
    | (RShift, _, _) ->
      failat pos "type error: attempted >> of non-bitvector"
    | (LogAnd, ValBool b1, ValBool b2) ->
      ok_bool (V.log_and b1 b2)
    | (LogAnd, _, _) ->
      failat pos "type error: attempted && of non-boolean"
    | (LogOr, ValBool b1, ValBool b2) ->
      ok_bool (V.log_or b1 b2)
    | (LogOr, _, _) ->
      failat pos "type error: attempted || of non-boolean"
    | (LogXor, ValBool b1, ValBool b2) ->
      ok_bool (V.log_xor b1 b2)
    | (LogXor, _, _) ->
      failat pos "type error: attempted ^^ of non-boolean"
    | (BitAnd, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bit_and w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.bit_and h1 h2)) l1
        | _ ->
          error "bitand: got a pointer"
      in
      check_len BitAnd l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_bit_and (w1, w2)) l1
    | (BitAnd, _, _) ->
      failat pos "type error: attempting & of non-bitvector"
    | (BitOr, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bit_or w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.bit_or h1 h2)) l1
        | _ ->
          error "bitor: got a pointer"
      in
      check_len BitOr l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_bit_or (w1, w2)) l1
    | (BitOr, _, _) ->
      failat pos "type error: attempted | of non-bitvector"
    | (BitXor, ValWord (w1, l1), ValWord (w2, l2)) ->
      let do_bit_xor w =
        match w with
        | (V.BitVec h1, V.BitVec h2) ->
          word_of_vec (ok (V.bit_xor h1 h2)) l1
        | _ ->
          error "bitxor: got a pointer"
      in
      check_len BitXor l1 l2;
      get_word pos (V.word_lift2 (V.IsWord l1) do_bit_xor (w1, w2)) l1
    | (BitXor, _, _) ->
      failat pos "type error: attempted ^ of non-bitvector"

  let app_builtin casp pos i vv =
    let check_len name l1 l2 =
      if l1 <> l2 then
        failat pos ("type error: attempted to "^name^
                    " with bitvectors of different lengths: "^
                    (string_of_int l1)^" and "^
                    (string_of_int l2))
      else
        ()
    in
    if i = "isptr" then
      match vv with
      | [ValWord (h, _)] ->
        let do_isptr w =
          match w with
          | V.BitVec _ -> ok (V.lift_bool false)
          | V.BitPtr _ -> ok (V.lift_bool true)
        in
        Some (get_bool pos (V.word_lift V.IsBool do_isptr h))
      | _ ->
        failat pos "type error: isptr takes one word (vec/ptr)"
    else if i = "bv_to_len" then
      match vv with
      (* length, bitvector: returns bitvector of length len *)
      | [ValInt len; ValWord (h, l)] ->
        let len = V.lower_int len in
        let len' = int_of_bint len in
        let do_bv_to_len w =
          match w with
          | V.BitVec h ->
            word_of_vec (ok (V.app_bv_to_len len h l)) len'
          | _ ->
            error "bv_to_len: got a pointer"
        in
        Some (get_word pos (V.word_lift (V.IsWord len') do_bv_to_len h) len')
      | _ ->
        failat pos "type error: bv_to_len takes one integer (length) and one bitvector (vec)"
    else if i = "bv_to_uint" then
      (* bitvector: returns corresponding uint *)
      match vv with
      | [ValWord (h, l)] ->
        let do_bv_to_uint w =
          match w with
          | V.BitVec h ->
            ok (V.app_bv_to_uint h l)
          | _ ->
            error "bv_to_uint: got a pointer"
        in
        Some (get_int pos (V.word_lift V.IsInt do_bv_to_uint h))
      | _ ->
        failat pos "type error: bv_to_uint takes one bitvector (vec)"
    else if i = "uint_to_bv_l" then
      (* length, integer: returns bitvector of length len with value i *)
      match vv with
      | [ValInt len; ValInt i] ->
        let len = V.lower_int len in
        let l = int_of_bint len in
        Some (get_word pos (word_of_vec (ok (V.app_uint_to_bv_l len i)) l) l)
      | _ ->
        failat pos "type error: uint_to_bv_l takes two integers"
    else if i = "checkbit" then
      (* get bit at bitvector and index *)
      match vv with
      | [ValWord (h1, l1); ValWord (h2, l2)] ->
        let do_checkbit w =
          match w with
          | (V.BitVec h1, V.BitVec h2) ->
            V.app_checkbit h1 h2 l1
          | _ ->
            error "checkbit: got a pointer"
        in
        check_len "checkbit" l1 l2;
        Some (get_bool pos (V.word_lift2 V.IsBool do_checkbit (h1, h2)))
      | _ ->
        failat pos "type error: checkbit takes two bitvectors"
    else if i = "checkfield" then
      match vv with
      | [ValWord (h, l); ValInt len; ValInt i1; ValInt i2] ->
        let len = int_of_bint (V.lower_int len) in
        let i1 = V.lower_int i1 in
        let i2 = V.lower_int i2 in
        let do_checkfield w =
          match w with
          | V.BitVec h ->
            word_of_vec (V.app_checkfield h l i1 i2) len
          | _ ->
            error "checkfield: got a pointer"
        in
        Some (get_word pos (V.word_lift (V.IsWord len) do_checkfield h) len)
      | _ ->
        failat pos "type error: checkfield takes one bitvector (vec) and three integers"
    else if i = "flag_set" then
      match vv with
      | [ValWord (h, l); ValInt i] ->
        let do_flag_set w =
          match w with
          | V.BitVec h ->
            word_of_vec (V.app_flag_set h l i) l
          | _ ->
            error "flag_set: got a pointer"
        in
        Some (get_word pos (V.word_lift (V.IsWord l) do_flag_set h) l)
      | _ ->
        failat pos "type error: flag_set takes one bitvector (vec) and one integer"
    else if i = "flag_unset" then
      match vv with
      | [ValWord (h, l); ValInt i] ->
        let do_flag_unset w =
          match w with
          | V.BitVec h ->
            word_of_vec (V.app_flag_unset h l i) l
          | _ ->
            error "flag_unset: got a pointer"
        in
        Some (get_word pos (V.word_lift (V.IsWord l) do_flag_unset h) l)
      | _ ->
        failat pos "type error: flag_unset takes one bitvector (vec) and one integer"
    else if i = "rotate_left" then
      match vv with
      | [ValWord (h1, l1); ValWord (h2, l2)] ->
        let do_rotate_left w =
          match w with
          | (V.BitVec h1, V.BitVec h2) ->
            word_of_vec (ok (V.app_rotate_left h1 h2 l1)) l1
          | _ ->
            error "rotate_left: got a pointer"
        in
        check_len "rotate_left" l1 l2;
        Some (get_word pos (V.word_lift2 (V.IsWord l1) do_rotate_left (h1, h2)) l1)
      | _ ->
        failat pos "type error: rotate_left takes two bitvectors (vec)"
    else if i = "rotate_right" then
      match vv with
      | [ValWord (h1, l1); ValWord (h2, l2)] ->
        let do_rotate_right w =
          match w with
          | (V.BitVec h1, V.BitVec h2) ->
            word_of_vec (ok (V.app_rotate_right h1 h2 l1)) l1
          | _ ->
            error "rotate_right: got a pointer"
        in
        check_len "rotate_right" l1 l2;
        Some (get_word pos (V.word_lift2 (V.IsWord l1) do_rotate_right (h1, h2)) l1)
      | _ ->
        failat pos "type error: rotate_right takes two bitvectors (vec)"
    else if i = "format" then
      match List.hd vv with
      | ValStr s ->
        let parsed = Formatstring.parse pos s in
        let format_args = List.tl vv in
        let get_formal_args v =
          begin match v with
          | ValStr s -> s
          | y -> failat pos ("type error: format expected Str arg, got "^(string_of_value y))
          end
        in
        let format_argstrs = List.map (get_formal_args) format_args in
        let applied = Formatstring.apply pos parsed format_argstrs in
        Some (ok_string (Formatstring.finish pos applied))
      | y -> failat pos ("type error: format expected format string as first arg, got "^(string_of_value y))

    else if i = "txt" then
      match vv with
      | [ValLoc (v, _)] ->
        let vloc = V.lower_loc v in
        begin match SM.find_opt vloc casp.txts with
        | Some s -> Some (ok_string s)
        | None -> failat pos ("txt: "^vloc^" no format string binding")
        end
      | [y] -> failat pos ("type error: .txt expected Loc arg, got "^(string_of_value y))
      | _ -> failat pos ("type error: .txt expected 1 arg, got "^(string_of_int (List.length vv)))
    else if i = "lbl" then
      match vv with
      | [ValWord (v, _)] ->
        begin match (V.lower_word v) with
        | BitPtr p ->
          let (pi, po) = V.lower_ptr p in
          begin match SM.find_opt pi casp.mems with
          | Some (_, _, _, Some x) ->
            if BI.equal (Bits.to_big_int po) BI.zero then Some (ok_string x)
            else failat pos ("type error: .lbl expected region "^pi^" with offset 0, got "^(Bits.to_bitstring po))
          | Some _ -> failat pos ("type error: .lbl expected region "^pi^" with a label")
          | None -> failat pos ("type error: .lbl not found region "^pi)
          end
        | _ -> failat pos ("type error: .lbl expected Ptr, got Vec")
        end
      | [y] -> failat pos ("type error: .lbl expected Word_Ptr arg, got "^(string_of_value y))
      | _ -> failat pos ("type error: .lbl expect 1 arg, got "^(string_of_int (List.length vv)))
    else if i = "dec" then
      match vv with
      | [ValWord (v, _)] ->
        let vword = V.lower_word v in
        begin match vword with
        | BitVec v ->
          let vvec = V.lower_vec v in
          Some (ok_string (string_of_bint (Bits.to_big_int_signed vvec)))
        | _ -> failat pos ("type error: .hex expected Vec, got Ptr")
        end
      | [ValInt v] ->
        let vint = V.lower_int v in
        Some (ok_string (string_of_bint vint))
      | [y] -> failat pos ("type error: .dec expected Vec/Int arg, got "^(string_of_value y))
      | _ -> failat pos ("type error: .dec expected 1 arg, got "^(string_of_int (List.length vv)))
    else if i = "hex" then
      match vv with
      | [ValWord (v, _)] ->
        let vword = V.lower_word v in
        begin match vword with
        | BitVec v ->
          let vvec = V.lower_vec v in
          Some (ok_string (Bits.to_hexdecimalstring vvec))
        | _ -> failat pos ("type error: .hex expected Vec, got Ptr")
        end
      | [ValInt v] ->
        let vint = V.lower_int v in
        Some (ok_string (hexstring_of_bint vint))
      | [y] -> failat pos ("type error: .hex expected Vec/Int arg, got "^(string_of_value y))
      | _ -> failat pos ("type error: .hex expected 1 arg, got "^(string_of_int (List.length vv)))
    else if i = "bin" then
      match vv with
      | [ValWord (v, _)] ->
        let vword = V.lower_word v in
        begin match vword with
        | BitVec v ->
          let vvec = V.lower_vec v in
          Some (ok_string (Bits.to_binarystring vvec))
        | _ -> failat pos ("type error: .hex expected Vec, got Ptr")
        end
      | [ValInt v] ->
        let vint = V.lower_int v in
        Some (ok_string (bitstring_of_bint vint))
      | [y] -> failat pos ("type error: .bin expected Vec/Int arg, got "^(string_of_value y))
      | _ -> failat pos ("type error: .bin expected 1 arg, got "^(string_of_int (List.length vv)))
    else None
end
