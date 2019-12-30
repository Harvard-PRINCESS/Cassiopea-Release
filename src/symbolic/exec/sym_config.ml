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
open Symvars

open Sym_exec

(* methods for handling symbolic configurations *)

let eq_word w1 w2 =
  let do_eq w =
    match w with
    | (BitVec h1, BitVec h2) ->
      ok (eq_vec h1 h2)
    | (BitPtr m1, BitPtr m2) ->
      ok (eq_ptr m1 m2)
    | _ ->
      ok (lift_bool false)
  in
  match word_lift2 IsBool do_eq (w1, w2) ctx_init with
  | Ok (v, _) -> v
  | Error s -> failwith ("eq_word somehow erred: "^s)

(* generate a symbolic ite of the right-length register names *)
let next_sym_loc (c : casp) len =
  (* regs: register list in conf *)
  let next_reg ss (i, l) =
    if l = len then
      match ss with
      | None ->
        Some (simpl (mk_loc i l))
      | Some ss ->
        let sb = next_sym_bool () in
        Some (simpl (mk_ite sb (mk_loc i l) ss))
    else
      ss
  in
  let regs =
    if will_whiten "args" then
      SM.bindings c.regs |> shuffle
    else
      List.rev (SM.bindings c.regs)
  in
  List.fold_left next_reg None regs

(* generate a symbolic ite of the right-length labels *)
let next_sym_lbl (c : casp) l =
  let ptr_of_lbl i l w = mk_ptr (i, mk_vec (Bits.zero w)) l in
  let next_lbl ss (_, m) =
    match SM.find_opt m c.mems with
    | Some (_, _, r, _) ->
      if r == l then
        match ss with
        | None ->
          Some (lift_word (BitPtr (ptr_of_lbl m l r)) l)
        | Some ss ->
          let sb = next_sym_bool () in
          Some (simpl (mk_ite sb (lift_word (BitPtr (ptr_of_lbl m l r)) l) ss))
      else ss
    | None -> failwith ("no memory region for label "^m)
  in
  List.fold_left next_lbl None (List.rev (SM.bindings c.lbls))

(* symbolic vec for starting state *)
let next_sym_word_vec l =
  lift_word (BitVec (next_sym_vec l)) l

(* symbolic pointer -- one region, any index *)
(* also returns an index bound assertion *)
let next_sym_word_ptr m len maxlen =
  let idx = next_sym_vec len in
  let bound_min = simpl
    (mk_binop LogOr
      (mk_binop BLt (mk_vec (Bits.zero len)) idx)
      (mk_binop EqVec (mk_vec (Bits.zero len)) idx))
  in
  let bound_max = simpl
    (mk_binop BLt idx (mk_vec (Bits.of_int len (maxlen * (len / 8)))))
  in
  let ptr = lift_word (BitPtr (mk_ptr (m, idx) len)) len in
  let bounds = simpl (mk_binop LogAnd bound_min bound_max) in
  (ptr, bounds)

(* generate a word that could be a vec or a ptr *)
(* also returns index bound assertions *)
let next_sym_word (c : casp) l : word sym_value * bool sym_value =
  let get_ptr (ptr, bounds) (i, (_, n, r, _)) =
    if r == l then
      let (ptr', bounds') = next_sym_word_ptr i l n in
      let ptr' =
        match ptr with
        | Some ptr ->
          Some (simpl (mk_ite (next_sym_bool ()) ptr' ptr))
        | None -> Some ptr'
      in
      (ptr', mk_binop LogAnd bounds' bounds)
    else
      (ptr, bounds)
  in
  let vec = lift_word (BitVec (next_sym_vec l)) l in
  let ptr = List.fold_left get_ptr
    (None, mk_bool true)
    (List.rev (SM.bindings c.mems))
  in
  match ptr with
  | (Some ptr, b) ->
    (simpl (mk_ite (next_sym_bool ()) vec ptr), b)
  | (None, b) ->
    (vec, b)

(* generate a state where all locations contain symbolic words *)
(* TODO accept argument suppressing pointer output *)
(* TODO accept used variable set *)
let next_sym_config (c : casp) : config =
  (* TODO accumulate contexts from next_sym_word *)
  (* TODO don't forget to guard these assertions! *)
  (* symbolic register contents *)
  let mk_reg l = (fst (next_sym_word c l), l) in
  (* symbolic memory contents *)
  let mk_mem (l, n, r, _) =
    let add_entry region o =
      let bvo = Bits.of_int r (o * (l / 8)) in
      BM.add bvo (fst (next_sym_word c l)) region
    in
    (l, n, List.fold_left add_entry BM.empty (range 0 n))
  in
  let init_env = eval_env c in
  let init_reg = SM.map mk_reg c.regs in
  let init_mem = SM.map mk_mem c.mems in
  let init_ctx = ctx_init in
  let init_jmp = mk_int BI.zero_big_int in
  { c = c;
    top = init_env;
    env = init_env;
    reg = init_reg;
    mem = init_mem;
    ctx = init_ctx;
    jmp = init_jmp; }

let vars_of_env env =
  let vars_of_one (_, v) =
    match v with
    | ValInt v -> vars_of_sym_value v
    | ValBool v -> vars_of_sym_value v
    | ValWord (v, _) -> vars_of_sym_value v
    | ValLoc (v, _) -> vars_of_sym_value v
    | ValStr _ -> vars_empty
  in
  SM.bindings env
  |> List.map vars_of_one
  |> List.fold_left vars_union vars_empty

let vars_of_reg reg =
  let vars_of_one (_, (w, _)) = vars_of_sym_value w in
  SM.bindings reg
  |> List.map vars_of_one
  |> List.fold_left vars_union vars_empty

let vars_of_mem mem =
  let vars_of_one (_, w) = vars_of_sym_value w in
  let vars_of_region (_, (_, _, region)) =
    BM.bindings region
    |> List.map vars_of_one
    |> List.fold_left vars_union vars_empty
  in
  SM.bindings mem
  |> List.map vars_of_region
  |> List.fold_left vars_union vars_empty

let vars_of_ctx ctx =
  ctx_to_bool ctx |> vars_of_sym_value

(* get symbolic variables in memory and registers *)
let vars_of_config (conf : config) =
  (vars_empty
  |> vars_union (vars_of_env conf.env)
  |> vars_union (vars_of_reg conf.reg)
  |> vars_union (vars_of_mem conf.mem)
  |> vars_union (vars_of_ctx conf.ctx)
  |> vars_union (vars_of_sym_value conf.jmp))

let subst_env' tbl model env =
  let subst_one v =
    match v with
    | ValInt v -> ValInt (subst' tbl model v)
    | ValBool v -> ValBool (subst' tbl model v)
    | ValWord (v, l) -> ValWord (subst' tbl model v, l)
    | ValLoc (v, l) -> ValLoc (subst' tbl model v, l)
    | ValStr s -> ValStr s
  in
  SM.map subst_one env

let subst_reg' tbl model reg =
  let subst_one (w, l) =
    (subst' tbl model w, l)
  in
  SM.map subst_one reg

let subst_mem' tbl model mem =
  let subst_one w =
    subst' tbl model w
  in
  let subst_region (b, l, region) =
    (b, l, BM.map subst_one region)
  in
  SM.map subst_region mem

let subst_ctx' tbl model (top, rest) =
  let subst_one v =
    subst' tbl model v
  in
  let subst_frame f =
    SBS.map subst_one f
  in
  (subst_frame top, List.map subst_frame rest)

let subst_env model env =
  let tbl = mk_memo_tmap () in
  subst_env' tbl model env

let subst_reg model reg =
  let tbl = mk_memo_tmap () in
  subst_reg' tbl model reg

let subst_mem model mem =
  let tbl = mk_memo_tmap () in
  subst_mem' tbl model mem

let subst_ctx model ctx =
  let tbl = mk_memo_tmap () in
  subst_ctx' tbl model ctx

(* apply substitution in given model to memory and registers *)
let subst_config model (conf : config) =
  (* use a single memoization table for all values *)
  let tbl = mk_memo_tmap () in
  { c = conf.c;
    top = subst_env' tbl model conf.top;
    env = subst_env' tbl model conf.env;
    reg = subst_reg' tbl model conf.reg;
    mem = subst_mem' tbl model conf.mem;
    ctx = subst_ctx' tbl model conf.ctx;
    jmp = subst' tbl model conf.jmp; }

(* generate predicate for config equality *)
let eq_reg reg1 reg2 =
  let eqs = reg_merge (fun _ _ -> eq_word) reg1 reg2 in
  SM.fold (fun _ -> log_and) eqs (mk_bool true)

let eq_mem mem1 mem2 =
  let eqs = mem_merge (fun _ _ _ -> eq_word) mem1 mem2 in
  let region_eq _ (_, _, m) v =
    BM.fold (fun _ -> log_and) m v
  in
  SM.fold region_eq eqs (mk_bool true)

let eq_config (conf1 : config) (conf2 : config) : bool sym_value =
  log_and (eq_reg conf1.reg conf2.reg) (eq_mem conf1.mem conf2.mem)

(* actually check value equality between configs *)
let equal_reg reg1 reg2 =
  let eqs = reg_merge (fun _ _ v1 v2 -> v1.tag = v2.tag) reg1 reg2 in
  SM.fold (fun _ -> (&&)) eqs true

let equal_mem mem1 mem2 =
  let eqs = mem_merge (fun _ _ _ v1 v2 -> v1.tag = v2.tag) mem1 mem2 in
  let region_eq _ (_, _, m) v =
    BM.fold (fun _ -> (&&)) m v
  in
  SM.fold region_eq eqs true

let equal_config (conf1 : config) (conf2 : config) : bool =
  (equal_reg conf1.reg conf2.reg) && (equal_mem conf1.mem conf2.mem)
