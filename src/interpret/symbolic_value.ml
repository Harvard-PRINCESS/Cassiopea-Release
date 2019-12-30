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
open Symbolic

open Monad

(* a value domain for execution with symbolic values *)

type t_int = bint sym_value
type t_bool = bool sym_value
type t_vec = bits sym_value
type t_ptr = (id * t_vec) sym_value
type t_loc = id sym_value
type t_word = word_t sym_value

type word = Symbolic.word_t =
  | BitVec of bits sym_value
  | BitPtr of (id * t_vec) sym_value

type t_ctx = SBS.t * (SBS.t list)

type 'a ret = t_ctx -> 'a
type 'a fallible = t_ctx -> ('a * t_ctx, string) result

type 'a ref_t =
  | IsInt : t_int ref_t
  | IsBool : t_bool ref_t
  | IsWord : int -> t_word ref_t
  | IsLoc : int -> t_loc ref_t

(* assertion context handling *)

let string_of_frame f =
  "(" ^ (SBS.elements f
  |> List.map string_of_sym_value
  |> String.concat " , ") ^ ")"

let ctx_to_string (top, rest) =
  ((top :: rest)
  |> List.map string_of_frame
  |> String.concat "\n")

let frame_to_bool f =
  SBS.elements f |>
  List.fold_left
    (fun v1 v2 -> simpl (mk_binop LogAnd v1 v2))
    (mk_bool true)

let ctx_add_assert b (top, rest) = (SBS.add b top, rest)
let ctx_to_bool (top, rest) =
  List.fold_left SBS.union top rest |> frame_to_bool

let ctx_init = (SBS.empty, [])

let ctx_merge b (top1, rest1) (top2, rest2) : t_ctx =
  if rest1 != rest2 then
    failwith "ctx_merge: contexts did not branch from same parent"
  else
    let set1 = frame_to_bool (SBS.diff top1 top2) in
    let set2 = frame_to_bool (SBS.diff top2 top1) in
    let ite = simpl (mk_ite b set1 set2) in
    let both = SBS.inter top1 top2 in
    match rest1 with
    | h :: t ->
      (SBS.add ite (SBS.union both h), t)
    | [] ->
      (SBS.add ite both, [])

let ctx_branch (top, rest) : t_ctx = (SBS.empty, top :: rest)

let ctx_unbranch (top, rest) : t_ctx =
  match rest with
  | h :: t -> (SBS.union top h, t)
  | _ -> failwith "ctx_unbranch: context unbranched without parent"

let assert_ _ b ctx =
  Ok ((), ctx_add_assert b ctx)

let lift_int d = simpl (mk_int d)
let lift_bool b = simpl (mk_bool b)
let lift_vec h _ = simpl (mk_vec h)
let lift_ptr (i, o) l = simpl (mk_ptr (i, simpl (mk_vec o)) l)
let lift_word w l = simpl (mk_word w l)
let lift_loc i l = simpl (mk_loc i l)

let lower_int v =
  match v.node with
  | SymVal (IsInt, d) -> d
  | _ -> failwith "lowering symbolic int!"

let lower_bool v =
  match v.node with
  | SymVal (IsBool, b) -> b
  | _ -> failwith "lowering symbolic boolean!"

let lower_vec v =
  match v.node with
  | SymVal (IsVec _, h) -> h
  | _ -> failwith "lowering symbolic bitvector!"

let lower_ptr p =
  match p.node with
  | SymVal (IsPtr _, (i, o)) -> (i, lower_vec o)
  | _ -> failwith "lowering symbolic pointer!"

let lower_word w =
  match w.node with
  | SymVal (IsWord _, w) -> w
  | _ -> failwith "lowering symbolic word!"

let lower_loc v =
  match v.node with
  | SymVal (IsLoc _, i) -> i
  | _ -> failwith ("lowering symbolic state!"^(string_of_sym_value v))

let string_of : type a. a ref_t -> a -> string =
  fun e v ->
  match e with
  | IsInt -> string_of_sym_value v
  | IsBool -> string_of_sym_value v
  | IsLoc _ -> string_of_sym_value v
  | IsWord _ -> string_of_sym_value v

(* unops *)
let neg d = simpl (mk_unop Neg d)
let log_not b = simpl (mk_unop LogNot b)
let bit_not h = simpl (mk_unop BitNot h)

(* binops *)
let add d1 d2 = simpl (mk_binop Add d1 d2)
let sub d1 d2 = simpl (mk_binop Add d1 (mk_unop Neg d2))
let mul d1 d2 = simpl (mk_binop Mul d1 d2)
let div d1 d2 = simpl (mk_binop Div d1 d2)
let pow d1 d2 = simpl (mk_binop Pow d1 d2)
let lt d1 d2 = simpl (mk_binop Lt d1 d2)
let gt d1 d2 = simpl (mk_binop Gt d1 d2)
let badd_vec h1 h2 = simpl (mk_binop BAdd h1 h2)
let bsub_vec h1 h2 = simpl (mk_binop BAdd h1 (mk_unop BNeg h2))
let bmul h1 h2 = simpl (mk_binop BMul h1 h2)
let blt h1 h2 = simpl (mk_binop BLt h1 h2)
let bgt h1 h2 = simpl (mk_binop BGt h1 h2)
let bslt h1 h2 = simpl (mk_binop BSLt h1 h2)
let bsgt h1 h2 = simpl (mk_binop BSGt h1 h2)
let lshift h1 h2 = simpl (mk_binop LShift h1 h2)
let rshift h1 h2 = simpl (mk_binop RShift h1 h2)
let log_and b1 b2 = simpl (mk_binop LogAnd b1 b2)
let log_or b1 b2 = simpl (mk_binop LogOr b1 b2)
let log_xor b1 b2 = simpl (mk_binop LogXor b1 b2)
let bit_and b1 b2 = simpl (mk_binop BitAnd b1 b2)
let bit_or b1 b2 = simpl (mk_binop BitOr b1 b2)
let bit_xor b1 b2 = simpl (mk_binop BitXor b1 b2)

let rec badd_ptr h1 h2 =
  match h1.node with
  | SymVal (IsPtr l, (i, o)) ->
    simpl (mk_ptr (i, badd_vec o h2) l)
  | SymIte (b, p1, p2) ->
    simpl (mk_ite b (badd_ptr p1 h2) (badd_ptr p2 h2))
  | SymChoose (ls, tl) ->
    let badd_pair (b, p) = (b, badd_ptr p h2) in
    simpl (mk_choose (List.map badd_pair ls) (badd_ptr tl h2))
  | _ -> failwith "symbolic_value: badd_ptr: invalid pointer"

let rec bsub_ptr h1 h2 =
  match h1.node with
  | SymVal (IsPtr l, (i, o)) ->
    simpl (mk_ptr (i, bsub_vec o h2) l)
  | SymIte (b, p1, p2) ->
    simpl (mk_ite b (bsub_ptr p1 h2) (bsub_ptr p2 h2))
  | SymChoose (ls, tl) ->
    let bsub_pair (b, p) = (b, bsub_ptr p h2) in
    simpl (mk_choose (List.map bsub_pair ls) (bsub_ptr tl h2))
  | _ -> failwith "symbolic_value: bsub_ptr: invalid pointer"

let eq_int d1 d2 = simpl (mk_binop EqInt d1 d2)
let eq_bool b1 b2 = simpl (mk_binop EqBool b1 b2)
let eq_vec h1 h2 = simpl (mk_binop EqVec h1 h2)

let rec eq_ptr p1 p2 =
  match (p1.node, p2.node) with
  | (SymVal (IsPtr _, (i1, o1)), SymVal (IsPtr _, (i2, o2))) ->
    log_and (mk_bool (i1 = i2)) (eq_vec o1 o2)
  | (SymIte (b, p1', p2'), _) ->
    simpl (mk_ite b (eq_ptr p1' p2) (eq_ptr p2' p2))
  | (_, SymIte (b, p1', p2')) ->
    simpl (mk_ite b (eq_ptr p1 p1') (eq_ptr p1 p2'))
  | (SymChoose (ls, tl), _) ->
    let eq_pair (b, p) = (b, eq_ptr p p2) in
    simpl (mk_choose (List.map eq_pair ls) (eq_ptr tl p2))
  | (_, SymChoose (ls, tl)) ->
    let eq_pair (b, p) = (b, eq_ptr p1 p) in
    simpl (mk_choose (List.map eq_pair ls) (eq_ptr p1 tl))
  | _, _ -> failwith "symbolic_value: eq_ptr: Invalid pointer"

let rec eq_loc s1 s2 =
  match (s1.node, s2.node) with
  | (SymVal (IsLoc _, s1), SymVal (IsLoc _, s2)) ->
    mk_bool (s1 = s2)
  | (SymIte (b, s1', s2'), _) ->
    simpl (mk_ite b (eq_loc s1' s2) (eq_loc s2' s2))
  | (_, SymIte (b, s1', s2')) ->
    simpl (mk_ite b (eq_loc s1 s1') (eq_loc s1 s2'))
  | (SymChoose (ls, tl), _) ->
    let eq_pair (b, s) = (b, eq_loc s s2) in
    simpl (mk_choose (List.map eq_pair ls) (eq_loc tl s2))
  | (_, SymChoose (ls, tl)) ->
    let eq_pair (b, s) = (b, eq_loc s1 s) in
    simpl (mk_choose (List.map eq_pair ls) (eq_loc s1 tl))
  | _, _ -> failwith "symbolic_value: eq_ptr: Invalid location"

let ife : type a. a ref_t -> t_bool -> a -> a -> a =
  fun t b v1 v2 ->
  (* compare v1 and v2 before making anything *)
  match t with
  | IsInt -> if v1.tag = v2.tag then v1
    else simpl (mk_ite b v1 v2)
  | IsBool -> if v1.tag = v2.tag then v1
    else simpl (mk_ite b v1 v2)
  | IsWord _ -> if v1.tag = v2.tag then v1
    else simpl (mk_ite b v1 v2)
  | IsLoc _ -> if v1.tag = v2.tag then v1
    else simpl (mk_ite b v1 v2)

(* lift a function (f : a -> b fallible) to operate on an a-typed ite
   (imprecisely, (ite condition a1 a2) -> (ite condition (f a1) (f a2))) *)
(* TODO ITE merge *)
let ife_lift :
  type a b.
    b ref_t ->
    (a -> b fallible) ->
    bool sym_value -> a -> a -> b fallible =
  fun e f b v1 v2 ctx ->
  let ctx = ctx_branch ctx in
  match (f v1 ctx, f v2 ctx) with
  | (Ok (v1, ctx1), Ok (v2, ctx2)) ->
    let ctx = ctx_merge b ctx1 ctx2 in
    Ok (ife e b v1 v2, ctx)
  | (Ok (v, ctx), Error s) ->
    let ctx = ctx_unbranch ctx in
    begin match assert_ "" b ctx with
    | Ok ((), ctx) -> Ok (v, ctx)
    | Error _ -> Error s
    end
  | (Error s, Ok (v, ctx)) ->
    let ctx = ctx_unbranch ctx in
    begin match assert_ "" (log_not b) ctx with
    | Ok ((), ctx) -> Ok (v, ctx)
    | Error _ -> Error s
    end
  | (Error _, Error _) ->
    Error "ite double failure"

let rec choose_lift :
  type a b.
    b ref_t ->
    (a -> b fallible) ->
    (bool sym_value * a) list -> a -> b fallible =
  fun e f ls tl ctx ->
  match ls with
  | (b, v) :: ls ->
    let ctx = ctx_branch ctx in
    begin match (f v ctx, choose_lift e f ls tl ctx) with
    | (Ok (v1, ctx1), Ok (v2, ctx2)) ->
      let ctx = ctx_merge b ctx1 ctx2 in
      Ok (ife e b v1 v2, ctx)
    | (Ok (v, ctx), Error s) ->
      let ctx = ctx_unbranch ctx in
      begin match assert_ "" b ctx with
      | Ok ((), ctx) -> Ok (v, ctx)
      | Error _ -> Error s
      end
    | (Error s, Ok (v, ctx)) ->
      let ctx = ctx_unbranch ctx in
      begin match assert_ "" (log_not b) ctx with
      | Ok ((), ctx) -> Ok (v, ctx)
      | Error _ -> Error s
      end
    | (Error _, Error _) ->
      Error "ite double failure"
    end
  | [] -> f tl ctx

let rec word_lift e f w =
  match w.node with
  | SymVal (IsWord _, h) ->
    f h
  | SymIte (b, w1, w2) ->
    ife_lift e (word_lift e f) b w1 w2
  | SymChoose (ls, tl) ->
    choose_lift e (word_lift e f) ls tl
  | _ -> failwith "symbolic_value: word_lift: invalid word"

let rec word_lift2 e f (w1, w2) =
  match (w1.node, w2.node) with
  | (SymVal (IsWord l1, h1), SymVal (IsWord l2, h2)) ->
    if l1 <> l2 then
      failwith "word_lift2: got words of different lengths!"
    else
      f (h1, h2)
  | (SymIte (b, w1', w2'), _) ->
    ife_lift e (fun v -> word_lift2 e f (v, w2)) b w1' w2'
  | (_, SymIte (b, w1', w2')) ->
    ife_lift e (fun v -> word_lift2 e f (w1, v)) b w1' w2'
  | (SymChoose (ls, tl), _) ->
    choose_lift e (fun v -> word_lift2 e f (v, w2)) ls tl
  | (_, SymChoose (ls, tl)) ->
    choose_lift e (fun v -> word_lift2 e f (w1, v)) ls tl
  | (_, _) -> failwith "symbolic_value: word_lift2: invalid word(s)"

(* TODO some kind of profiling support *)
(* count the number of nodes generated by each call? though this is awful *)

(* check 0 <= i < max with ints *)
let check_bound_int i max =
  let zero = mk_int BI.zero in
  let lower = log_or (lt zero i) (eq_int zero i) in
  let upper = lt i (mk_int (bint_of_int max)) in
  assert_ "" (log_and lower upper)

(* check 0 <= i < max with bitvecs *)
let check_bound i max width =
  let zero = mk_vec (Bits.zero width) in
  let lower = log_or (blt zero i) (eq_vec zero i) in
  let upper = blt i (mk_vec (Bits.of_int width max)) in
  assert_ "" (log_and lower upper)

let check_align i width times =
  let last_two = bit_and i (mk_vec (Bits.of_int width (times - 1))) in
  let zero = mk_vec (Bits.zero width) in
  assert_ "" (eq_vec last_two zero)

let assign s new_val len (i, sz) old_val =
  let rec assign' s =
    match s.node with
    | SymVal (IsLoc l, s) ->
      if len <> l then
        (* length check: mistyped pointer branch *)
        failwith "assign: pointer length mistyped"
      else if s <> i then
        ok old_val
      else if l <> sz then
        failwith ("assign: pointer length "^(string_of_int l)^
                  " not the same as reg size "^(string_of_int sz))
      else
        ok new_val
    | SymIte (b, s1, s2) ->
      ife_lift (IsWord len) assign' b s1 s2
    | SymChoose (ls, tl) ->
      choose_lift (IsWord len) assign' ls tl
    | _ -> failwith "symbolic_value: assign: invalid destination"
  in
  assign' s

let store p new_val len (region, wordsz, maxoff) off old_val =
  let rec store' p =
    match p.node with
    | SymVal (IsPtr olen, (i, o)) ->
      if i <> region then
        ok old_val
      else if len <> wordsz then
        (* length check: storing wrong of word size *)
        error "store: length mismatch"
      else if (width_of_vec o) <> olen then
        error ("store: pointer offset "^(string_of_sym_value o)^
                " doesn't match pointer length")
      else
        (* boundary checking assertion *)
        bind2
        (check_align o olen (wordsz / 8))
        (* XXX assumes 32-bit word size *)
        (check_bound o (maxoff * (wordsz / 8)) olen)
        (fun ((), ()) ->
          ok (simpl (mk_ite (eq_vec o (mk_vec off))
          new_val old_val)))
    | SymIte (b, p1, p2) ->
      ife_lift (IsWord wordsz) store' b p1 p2
    | SymChoose (ls, tl) ->
      choose_lift (IsWord wordsz) store' ls tl
    | _ -> failwith "symbolic_value: store: invalid destination"
  in
  store' p

(* expr operations *)
let deref s len reg =
  let rec deref' s =
    match s.node with
    | SymVal (IsLoc l, i) ->
      if len <> l then
        (* length check: mistyped location branch *)
        failwith "deref: length mismatch"
      else
        begin match SM.find_opt i reg with
        | None ->
          failwith ("deref: nonexistent register "^i)
        | Some (h, l) ->
          if len <> l then
            (* length check: wrong length found in a register *)
            failwith "BUG: found wrong length in register"
          else
            ok h
        end
    | SymIte (b, s1, s2) ->
      (* simpl (mk_ite b (deref' s1) (deref' s2)) *)
      ife_lift (IsWord len) deref' b s1 s2
    | SymChoose (ls, tl) ->
      choose_lift (IsWord len) deref' ls tl
    | _ -> failwith "symbolic_value: deref: invalid register"
  in
  deref' s

let fetch p len mem =
  let rec fetch' p =
    match p.node with
    | SymVal (IsPtr olen, (i, o)) ->
      let fetch_mem exto off w res =
        match res with
        | None -> Some w
        | Some w' ->
          Some (simpl (mk_ite (eq_vec (mk_vec off) exto) w w'))
      in
      begin match SM.find_opt i mem with
      | None ->
        failwith ("fetch: memory region "^i^" does not exist")
      | Some (wordsz, maxoff, mem) ->
        (* length check: storing word of wrong size *)
        if len <> wordsz then
          error "fetch: length mismatch"
        else if width_of_vec o <> olen then
          error ("fetch: pointer offset "^(string_of_sym_value o)^" too large")
        else
          bind2
          (check_align o olen (wordsz / 8))
          (* XXX assumes 32-bit word size *)
          (check_bound o (maxoff * (wordsz / 8)) olen)
          (fun ((), ()) ->
          match BM.fold (fetch_mem o) mem None with
          | Some w -> ok w
          | None -> error "fetch: mem is empty")
      end
    | SymIte (b, p1, p2) ->
      ife_lift (IsWord len) fetch' b p1 p2
    | SymChoose (ls, tl) ->
      choose_lift (IsWord len) fetch' ls tl
    | _ -> failwith "symbolic_value: fetch: Invalid pointer"
  in
  fetch' p

let index_bit h l d =
  let next_index e i =
    let i' = mk_vec (Bits.of_int l i) in
    simpl (mk_ite (eq_vec d i') (mk_unop (BitIndex i) h) e)
  in
  bind
  (check_bound d l l)
  (fun () -> ok
  (List.init (l - 1) (fun i -> i)
  |> List.rev
  |> List.fold_left next_index (simpl (mk_unop (BitIndex (l - 1)) h))
  |> simpl))

let index_int h l d =
  let next_index e i =
    let i' = mk_int (bint_of_int i) in
    simpl (mk_ite (eq_int d i') (mk_unop (BitIndex i) h) e)
  in
  bind
  (check_bound_int d l)
  (fun () -> ok
  (List.init (l - 1) (fun i -> i)
  |> List.rev
  |> List.fold_left next_index (simpl (mk_unop (BitIndex (l - 1)) h))
  |> simpl))

(* slice may also need to be a big ITE for index checking
   if we ever decide to permit dynamic bounds *)
let slice h d1 d2 =
  simpl (mk_unop (BitSlice (d1, d2)) h)

let app_bv_to_len len h l =
  let len = int_of_bint len in
  if len < l then
    simpl (mk_unop (BitSlice (0, len)) h)
  else if len > l then
    simpl (mk_unop (BitZeroExtend (len - l)) h)
  else
    h

let app_bv_to_uint h _ =
  simpl (mk_unop BitToUInt h)

let app_uint_to_bv_l len h =
  let len = int_of_bint len in
  simpl (mk_unop (UIntToBit len) h)

let app_checkbit h i l =
  index_bit h l i

let app_checkfield h _ i1 i2 =
  ok (slice h (int_of_bint i1) ((int_of_bint i2) + 1))

let app_flag_set h l i =
  let i = lower_int i in
  let mask = mk_vec (Bits.set (Bits.zero l) i) in
  ok (bit_or h mask)

let app_flag_unset h l i =
  let i = lower_int i in
  let mask = mk_vec (Bits.set (Bits.zero l) i) in
  ok (bit_and h (bit_not mask))

let app_rotate_left h1 h2 _ =
  simpl (mk_binop LRotate h1 h2)

let app_rotate_right h1 h2 _ =
  simpl (mk_binop RRotate h1 h2)
