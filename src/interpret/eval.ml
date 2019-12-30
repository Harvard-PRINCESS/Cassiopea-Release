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

module PA = Prettyast

open Monad
open Value
open Config

(* evaluating Cassiopeia expressions and statements over a value domain *)

module Eval = functor
  (V : Value)
  (C : module type of Config(V)) ->
struct
  open V
  open C

  open Eval_ops
  include EvalOps(V)(C)

  let collect_args pos env args vv =
    (* add the next arg to an environment *)
    let add_arg env ((i, _), v) = SM.add i v env in
    try
      List.combine args vv
      |> List.fold_left add_arg env
    with Invalid_argument _ ->
      failat pos ("type error: wrong number of arguments: got "^
                  (string_of_int (List.length vv))^", expected "^
                  (string_of_int (List.length args)))

  let eval_atomic (c : casp) env (pos, a) =
    match a with
    | Int d -> ValInt (lift_int d)
    | Bool b -> ValBool (lift_bool b)
    | Vec h ->
      let l = Bits.width h in
      let v = lift_vec h l in
      ValWord (lift_word (BitVec v) l, l)
    | Ptr (i, o) ->
      begin match SM.find_opt i c.mems with
      | Some (_, _, l, _) ->
        let o = Bits.of_big_int l o in
        let p = lift_ptr (i, o) l in
        ValWord (lift_word (BitPtr p) l, l)
      | None ->
        failat pos ("type error: could not find memory "^i)
      end
    | Id s ->
      (match SM.find_opt s env with
      | None ->
        failat pos ("type error: variable "^s^" undefined")
      | Some v -> v)
    | Str s -> ValStr s

  (* build toplevel binding environment *)
  let eval_env (c : casp) =
    let add_let i (a, _) env = SM.add i (eval_atomic c env (Pos.none, a)) env in
    let add_reg i l env = SM.add i (ValLoc (lift_loc i l, l)) env in
    let add_lbl i m env =
      let l = match SM.find_opt m c.mems with
        | Some (_, _, r, _) -> r
        | None -> failwith ("env error: could not find memory "^m)
      in
      let w = lift_word (BitPtr (lift_ptr (m, Bits.zero l) l)) l in
      SM.add i (ValWord (w, l)) env
    in
    SM.empty
    |> SM.fold add_reg c.regs
    |> SM.fold add_let c.lets
    |> SM.fold add_lbl c.lbls

  (* build starting config *)
  let eval_config (c : casp) =
    let zero_of_length l =
      lift_word (BitVec (lift_vec (Bits.zero l) l)) l
    in
    (* zero all registers *)
    let mk_reg l = (zero_of_length l, l) in
    (* zero all memory *)
    let mk_mem (l, n, r, _) =
      let add_entry region o =
        let o = Bits.of_int r (o * (l / 8)) in
        BM.add o (zero_of_length l) region
      in
      (l, n, List.fold_left add_entry BM.empty (range 0 n))
    in
    let init_env = eval_env c in
    let init_reg = SM.map mk_reg c.regs in
    let init_mem = SM.map mk_mem c.mems in
    let init_ctx = ctx_init in
    let init_jmp = lift_int BI.zero_big_int in
    { c = c ;
      top = init_env;
      env = init_env;
      reg = init_reg;
      mem = init_mem;
      ctx = init_ctx;
      jmp = init_jmp; }

  let eval_start (init : (atomic * atomic) list) (c: config) =
    let get_value (c: casp) v =
      match v with
      | Vec h ->
        let l = Bits.width h in
        let v = lift_vec h l in
        lift_word (BitVec v) l
      | Ptr (i, o) ->
        begin match SM.find_opt i c.mems with
        | Some (_, _, l, _) ->
          let o = Bits.of_big_int l o in
          let p = lift_ptr (i, o) l in
          lift_word (BitPtr p) l
        | None -> failwith ("type error: region "^i^" not found")
        end
      | _ -> failwith "type error: eval_start got non-word value"
    in
    let get_start conf (a, v) =
      let v = get_value conf.c v in
      match a with
      | Id i ->
        begin match SM.find_opt i conf.reg with
        | Some (_, l) ->
          { conf with reg = SM.add i (v, l) conf.reg }
        | None ->
          failwith ("type error: register "^i^" not found")
        end
      | Ptr (i, o) ->
        begin match SM.find_opt i conf.mem with
        | Some (b, w, im) ->
          let (_, _, r, _) = SM.find i conf.c.mems in (* must exist *)
          let o = Bits.of_big_int r o in
          let region = BM.add o v im in
          { conf with mem = SM.add i (b, w, region) conf.mem }
        | None ->
          failwith ("type error: region "^i^" not found")
        end
      | _ ->
        failwith ("type error: eval_start got non-address")
    in
    List.fold_left get_start c init

  let rec eval_expr (pos, e) conf : (value * t_ctx, Pos.t * string) result =
    (if !settings.dump_interp then
      print_log "eval_expr: %s\n" (PA.string_of_expr (pos, e)));
    let result =
      match e with
      | Atomic a -> Ok (eval_atomic conf.c conf.env (pos, a), conf.ctx)
      | Deref e -> eval_deref pos e conf
      | Fetch (e1, e2) -> eval_fetch pos e1 e2 conf
      | Index (e1, e2) -> eval_index pos e1 e2 conf
      | Slice (e1, e2, e3) -> eval_slice pos e1 e2 e3 conf
      | Unop (u, e) -> eval_unop pos u e conf
      | Binop (e1, b, e2) -> eval_binop pos e1 b e2 conf
      | App (i, args) -> eval_app conf.c pos i args conf
      | LetE (i, _, e1, e2) -> eval_lete pos i e1 e2 conf
      | IfE (e, e1, e2) -> eval_ife pos e e1 e2 conf
    in
    begin if !settings.dump_interp then
      match result with
      | Ok (v, ctx) ->
        print_log "result: <value> %s <ctx> %s\n"
          (string_of_value v) (ctx_to_string ctx);
        flush_log ()
      | Error (pos, s) ->
        print_log "result: <error> %s:%s\n"
          (Pos.string_of pos) s;
        flush_log ()
    end;
    result

  and eval_deref pos e = bindE
    (eval_expr e)
    (function
    | ValLoc (s, l) -> fun conf ->
      get_word pos (deref s l conf.reg) l conf
    | _ -> failat pos "type error: attempted deref of non-ref")

  and eval_fetch pos e1 e2 = bindE2
    (eval_expr e1)
    (eval_expr e2)
    (function
    | (ValWord (h, _), ValInt l) -> fun conf ->
      let l = int_of_bint (lower_int l) in
      let do_fetch w =
        match w with
        | BitPtr p ->
          fetch p l conf.mem
        | BitVec _ ->
          error "fetch: got a bitvector address"
      in
      get_word pos (word_lift (IsWord l) do_fetch h) l conf
    | _ ->
      failat pos "type error: Fetch expects pointer and int len")

  and eval_index pos e1 e2 = bindE2
    (eval_expr e1)
    (eval_expr e2)
    (function
    | (ValWord (h, l), ValInt i) ->
      let do_index_int w =
        match w with
        | BitVec h ->
          index_int h l i
        | _ ->
          error "index: attempted index of pointer"
      in
      get_bool pos (word_lift IsBool do_index_int h)
    | (ValWord (h1, l1), ValWord (h2, l2)) ->
      let do_index_bit w =
        match w with
        | (BitVec h1, BitVec h2) ->
          index_bit h1 l1 h2
        | _ ->
          error "index: attempted index of pointer"
      in
      if l1 <> l2 then
        failat pos ("type error: attempted index of different lengths: "^
                    (string_of_int l1)^" and "^
                    (string_of_int l2))
      else
        get_bool pos (word_lift2 IsBool do_index_bit (h1, h2))
    | (ValWord _, _) ->
      failat pos "type error: attempted index by non-integer, non-bitvector"
    | (_, _) ->
      failat pos "type error: attempted index of non-bitvector")

  and eval_slice pos e1 e2 e3 = bindE3
    (eval_expr e1)
    (eval_expr e2)
    (eval_expr e3)
    (function
    | (ValWord (h, l), ValInt d1, ValInt d2) ->
      let i1 = BI.int_of_big_int (lower_int d1) in
      let i2 = BI.int_of_big_int (lower_int d2) in
      let do_slice w =
        match w with
        | BitVec h ->
          word_of_vec (ok (slice h i1 i2)) (i2 - i1)
        | _ ->
          error "slice: attempted slice of pointer"
      in
      if i1 < 0 then
        failat pos "slice start is negative"
      else if i2 < 0 then
        failat pos "slice end is negative"
      else if i1 > l then
        failat pos "slice start is out of range"
      else if i2 > l then
        failat pos "slice end is out of range"
      else if i1 > i2 then
        failat pos "slice start is after slice end"
      else
        get_word pos (word_lift (IsWord (i2 - i1)) do_slice h) (i2 - i1)
    | (ValWord _, _, _) ->
      failat pos "type error: slice range not two integers"
    | _ ->
      failat pos "type error: attempted slice of non-bitvector")

  and eval_unop pos u e = bindE
    (eval_expr e)
    (app_unop pos u)

  and eval_binop pos e1 b e2 = bindE2
    (eval_expr e1)
    (eval_expr e2)
    (app_binop pos b)

  and eval_app casp pos i ee = bindE
    (eval_args ee)
    (fun vv ->
    match app_builtin casp pos i vv with
    (* built-in functions *)
    | Some f -> f
    (* user-defined functions *)
    | None ->
      fun conf ->
      let (args, _, body) = match SM.find_opt i conf.c.defs with
        | None -> failat pos ("type error: no such function "^i)
        | Some op -> op
      in
      let env = collect_args pos conf.top args vv in
      eval_expr body { conf with env = env })

  and eval_lete _ i e1 e2 = bindE_let i
    (eval_expr e1)
    (eval_expr e2)

  and eval_ife pos e e1 e2 = bindE
    (eval_expr e)
    (function
    | ValBool b -> mergeE (val_merge pos) b (eval_expr e1) (eval_expr e2)
    | _ -> failat pos "type error: conditioning on non-boolean")

  and eval_args ee =
    (* thread state through arg eval *)
    let eval_next vv e =
      bindE2 vv (eval_expr e)
      (fun (vv, v) -> returnE (v :: vv))
    in
    bindE
      (List.fold_left eval_next (returnE []) ee)
      (fun vv -> returnE (List.rev vv))

  let rec eval_stmt (pos, s) : config -> (config, Pos.t * string) result =
    (if !settings.dump_interp then
      print_log "eval_stmt: %s\n" (PA.string_of_stmt (pos, s)));
    match s with
    | Skip -> returnS
    | Err -> get pos (error "encountered error statement")
    | Assert (e, s) -> eval_assert pos e s
    | Seq (s1, s2) -> eval_seq pos s1 s2
    | Assign (e1, e2) -> eval_assign pos e1 e2
    | Store (e1, e2, e) -> eval_store pos e1 e2 e
    | For (i, e1, e2, s) -> eval_for pos i e1 e2 s
    | Call (i, ee) -> eval_call pos i ee
    | LetS (i, _, e, s) -> eval_lets pos i e s
    | IfS (e, s1, s2) -> eval_ifs pos e s1 s2

  and eval_assert pos e s = bindE
    (eval_expr e)
    (function
    | ValBool b ->
      get pos (assert_ s b)
    | _ ->
      failat pos ("type error: assert got non-boolean"))

  and eval_seq _ s1 s2 = bindS
    (eval_stmt s1)
    (eval_stmt s2)

  and eval_assign pos e1 e2 = bindE2
    (eval_expr e1)
    (eval_expr e2)
    (function
    | (ValLoc (s, l1), ValWord (h, l2)) -> fun conf ->
      if l1 <> l2 then
        failat pos ("type error: Assign of different lengths: "^
                    (string_of_int l1)^" and "^(string_of_int l2))
      else
        (* map assign across locations *)
        let reg =
          reg_map
            (fun (i, l) v -> assign s h l1 (i, l) v)
            conf.reg
          |> reg_flatten
        in
        begin match reg conf.ctx with
        | Ok (reg, ctx) -> Ok { conf with reg = reg; ctx = ctx }
        | Error s -> Error (pos, s)
        end
    | (ValWord (_, _), _) ->
      failat pos "type error: Assign to non-location"
    | _ ->
      failat pos "type error: Assign got non-bitvector")

  and eval_store pos e1 e2 e = bindE3
    (eval_expr e1)
    (eval_expr e2)
    (eval_expr e)
    (function
    | (ValWord (h1, _), ValInt len, ValWord (h2, l)) -> fun conf ->
      let len = int_of_bint (lower_int len) in
      if len <> l then
        failat pos ("type error: Store intended length: "^
                    (string_of_int len)^" but got: "^(string_of_int l))
      else if SM.is_empty conf.mem then
        Error (pos, "store: no memory defined")
      else
        (* map store across locations *)
        (* this might be blowing up:
           1. need to deal with each extant location (needs approach-level fix)
           2. store disassembles pointer ITEs: this happens per-location;
              possibly gains in permuting this order *)
        let mem =
          mem_map (fun (i, l, n) o cur ->
            let do_store p =
              match p with
              | BitPtr p ->
                store p h2 len (i, l, n) o cur
              | _ ->
                error "store: got a bitvector address"
            in
            word_lift (IsWord l) do_store h1)
            conf.mem
          |> mem_flatten
        in
        begin match mem conf.ctx with
        | Ok (mem, ctx) -> Ok { conf with mem = mem; ctx = ctx }
        | Error s -> Error (pos, s)
        end
    | (ValWord _, ValInt _, _) ->
      failat pos "type error: Store got non-bitvector value to store"
    | (ValWord _, _, _) ->
      failat pos "type error: Store got non-integer length"
    | (_, _, _) ->
      failat pos "type error: Store got non-bitvector address")

  and eval_for pos i e1 e2 s = bindE2
    (eval_expr e1)
    (eval_expr e2)
    (function
    | (ValInt i1, ValInt i2) ->
      let i1 = lower_int i1 in
      let i2 = lower_int i2 in
      (* run the body on idx'th iteration *)
      (* conf tracks has-failed *)
      let body conf idx = bindS conf
        (fun conf ->
        let env = SM.add i (ValInt (lift_int idx)) conf.env in
        bindS_env env (eval_stmt s) conf)
      in
      List.fold_left body returnS (range_big i1 i2)
    | _ -> failat pos "type error: For loop with non-integer limits")

  and eval_call pos i ee = bindE
    (eval_args ee)
    (fun vv conf ->
    if i = "BRANCH" then
      match vv with
      | [ValInt dest] -> returnS { conf with jmp = add conf.jmp dest }
      | _ -> failat pos "type error: BRANCH expects one int argument"
    else
      let (args, body) = match SM.find_opt i conf.c.defss with
        | None -> failat pos ("no such subroutine "^i)
        | Some op -> op
      in
      let env = collect_args pos conf.top args vv in
      bindS_env env (eval_stmt body) conf)

  and eval_lets _ i e s = bindE
    (eval_expr e)
    (fun v conf ->
    let env = SM.add i v conf.env in
    bindS_env env (eval_stmt s) conf)

  and eval_ifs pos e s1 s2 = bindE
    (eval_expr e)
    (function
    | ValBool b -> mergeS conf_merge b (eval_stmt s1) (eval_stmt s2)
    | _ -> failat pos "type error: IfS got non-boolean value in condition")

  (* apply operation to value-typed operands *)
  let eval_op pos i vv conf =
    (if !settings.dump_interp then
      print_log "eval_op: %s\n" i);
    let (args, body) = match SM.find_opt i conf.c.defops with
      | None -> failwith ("no such op "^i)
      | Some op -> op
    in
    let env = collect_args pos conf.top args vv in
    bindS_env env (eval_stmt body) conf
end

module CV = Concrete_value
module CC = Config(CV)
module CE = Eval(CV)(CC)

module SV = Symbolic_value
module SC = Config(SV)
module SE = Eval(SV)(SC)
