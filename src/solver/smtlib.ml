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

module SA = Smtlib_ast

type env = {
  smt_i2var : string IM.t;    (* map unique ID to smtlib varname *)
  smt_var2sv : sym_ex_t SM.t; (* map smtlib varname to symbolic value *)
  smt_var2def : string SM.t;  (* map smtlib varname to smtlib string def *)
  smt_sv2var : string SVM.t;  (* map symbolic value to smtlib variable name *)
  smt_sv2cnt : int SVM.t;     (* map symbolic value to usage counter *)
  counter : int;              (* counter for first unused smtlib variable ID *)
}

let env_empty = {
  smt_i2var = IM.empty;
  smt_var2sv = SM.empty;
  smt_var2def = SM.empty;
  smt_sv2var = SVM.empty;
  smt_sv2cnt = SVM.empty;
  counter = 0
}

let declare_const (i: id) (typ: string) =
  P.sprintf "(declare-fun %s () %s)" i typ

let declare_fun (i: id) (dom: string) (rang: string) =
  P.sprintf "(declare-fun %s %s %s)" i dom rang

let define_const (i: id) (typ: string) (body: string) =
  P.sprintf "(define-fun %s () %s %s)" i typ body

let define_fun (i: id) (args: string) (typ: string) (body: string) =
  P.sprintf "(define-fun %s (%s) %s %s)" i args typ body

let add_decl var x e =
  { e with
    smt_i2var = IM.add e.counter var e.smt_i2var;
    smt_sv2var = SVM.add x var e.smt_sv2var;
    smt_var2sv = SM.add var x e.smt_var2sv;
    counter = e.counter + 1
  }

let add_def var def x e =
  { e with
    smt_i2var = IM.add e.counter var e.smt_i2var;
    smt_sv2var = SVM.add x var e.smt_sv2var;
    smt_var2sv = SM.add var x e.smt_var2sv;
    smt_var2def = SM.add var def e.smt_var2def;
    counter = e.counter + 1
  }

(* width for bitvector representations of integers *)
let int_width = 32

let rec encode_unop : type a b. a sym_ref_t -> (a, b) sym_unop -> string -> string =
  fun t u v ->
  match u with
  | Neg -> "(bvneg "^v^")" (* - *)
  | BNeg -> "(bvneg "^v^")"
  | LogNot -> "(not "^v^")"
  | BitNot -> "(bvnot "^v^")"
  | BitSlice (d1, d2) ->
    "((_ extract "^(string_of_int (d2 - 1))^" "^(string_of_int d1)^") "^v^")"
  | BitIndex d ->
    (* special handling since the result is a width-1 bitvector rather than a bool *)
    "(= ((_ extract "^(string_of_int d)^" "^(string_of_int d)^") "^v^") (_ bv1 1))"
  | BitZeroExtend d ->
    "((_ zero_extend "^(string_of_int d)^") "^v^")"
  | BitToUInt ->
    (*"(bv2int "^v^")"*)
    begin match t with
    | IsVec l ->
      if l < int_width then
        encode_unop (IsVec l) (BitZeroExtend (int_width - l)) v
      else if l = int_width then v
      else
        encode_unop (IsVec l) (BitSlice (0, int_width)) v
    | _ -> failwith "got BitToUInt of non-vec"
    end
  | UIntToBit l ->
    (*"((_ int2bv "^(string_of_int l)^") "^v^")"*)
    if l < int_width then
      encode_unop (IsVec int_width) (BitSlice (0, l)) v
    else if l = int_width then v
    else
      encode_unop (IsVec int_width) (BitZeroExtend (l - int_width)) v

let encode_binop : type a b c. (a, b, c) sym_binop -> string -> string -> string =
  fun b v1 v2 ->
  match b with
  | Add -> "(bvadd "^v1^" "^v2^")" (* + *)
  | Mul -> "(bvmul "^v1^" "^v2^")" (* * *)
  | Div -> "(bvudiv "^v1^" "^v2^")" (* / *)
  | Pow -> failwith "nobody supports pow"
  | EqInt -> "(= "^v1^" "^v2^")"
  | EqVec -> "(= "^v1^" "^v2^")"
  | EqBool -> "(= "^v1^" "^v2^")"
  | Lt  -> "(bvult "^v1^" "^v2^")" (* < *)
  | Gt  -> "(bvugt "^v1^" "^v2^")" (* > *)
  | BAdd -> "(bvadd "^v1^" "^v2^")"
  | BMul -> "(bvmul "^v1^" "^v2^")"
  | BLt -> "(bvult "^v1^" "^v2^")"
  | BGt -> "(bvugt "^v1^" "^v2^")"
  | BSLt -> "(bvslt "^v1^" "^v2^")"
  | BSGt -> "(bvsgt "^v1^" "^v2^")"
  | LShift -> "(bvshl "^v1^" "^v2^")"
  | RShift -> "(bvlshr "^v1^" "^v2^")"
  | LRotate -> "((_ rotate_left "^v2^") "^v1^")"
  | RRotate -> "((_ rotate_right "^v2^") "^v1^")"
  | LogAnd -> "(and "^v1^" "^v2^")"
  | LogOr  -> "(or "^v1^" "^v2^")"
  | LogXor -> "(xor "^v1^" "^v2^")"
  | BitAnd -> "(bvand "^v1^" "^v2^")"
  | BitOr  -> "(bvor "^v1^" "^v2^")"
  | BitXor -> "(bvxor "^v1^" "^v2^")"

(* generate a random five-letter string prefix *)
let rand_prefix () =
  let gen_char () =
    let c = Random.int(26) in
    String.make 1 (char_of_int (int_of_char 'a' + c))
  in
  if will_whiten "solver" then
    (String.concat "" ((range 0 5) |> List.map (fun _ -> gen_char ())))^"_"
  else ""

let rec encode : type a. a sym_value -> env -> (id * env) =
  fun (sv : a sym_value) (e : env) ->
  let x = ex_of_sym_value sv in
  match SVM.find_opt x e.smt_sv2var with
  (* value already exists: return varname and unchanged env *)
  | Some v -> (v, e)
  (* value does not exist: add encoding *)
  | None ->
    begin match sv.node with
    | SymVal (IsInt, d) ->
      (Bits.to_bstring (Bits.of_big_int int_width d), e)
      (* (BI.string_of_big_int d, e) *)
    | SymVal (IsBool, b) ->
      if b then ("true", e) else ("false", e)
    | SymVal (IsLoc _, _) ->
      failwith "encode: encountered location"
    | SymVal (IsVec _, h) ->
      (Bits.to_bstring h, e)
    | SymVal (IsPtr _, _) ->
      failwith "encode: encountered pointer"
    | SymVal (IsWord _, BitVec _) ->
      failwith "encode: encountered word (BitVec)"
    | SymVal (IsWord _, BitPtr _) ->
      failwith "encode: encountered word (BitPtr)"
    | SymInt i ->
      let var = rand_prefix ()^"x"^(string_of_int e.counter)^"_int"^(string_of_int i) in
      (var, add_decl var x e)
    | SymBool i ->
      let var = rand_prefix ()^"x"^(string_of_int e.counter)^"_bool"^(string_of_int i) in
      (var, add_decl var x e)
    | SymVec (i, _l) ->
      let var = rand_prefix ()^"x"^(string_of_int e.counter)^"_vec"^(string_of_int i) in
      (var, add_decl var x e)
    | SymIte (b, v1, v2) ->
      let (b, e) = encode b e in
      let (v1, e) = encode v1 e in
      let (v2, e) = encode v2 e in
      let def = "(ite "^b^" "^v1^" "^v2^")" in
      let var = rand_prefix ()^"x"^(string_of_int e.counter)^"_ite" in
      (var, add_def var def x e)
    | SymUnop (u, v) ->
      let t = typ_of_sym_value v in
      let (v, e) = encode v e in
      let def = encode_unop t u v in
      let var = rand_prefix ()^"x"^(string_of_int e.counter)^"_unop" in
      (var, add_def var def x e)
    | SymBinop (b, v1, v2) ->
      let (v1, e) = encode v1 e in
      let (v2, e) = encode v2 e in
      let def = encode_binop b v1 v2 in
      let var = rand_prefix ()^"x"^(string_of_int e.counter)^"_binop" in
      (var, add_def var def x e)
    | SymMultiop (b, ls, t, k) ->
      (* naive encoding *)
      (* TODO op canonicalization for improved sharing *)
      (* see Armando Solar-Lezama's thesis, section 5.2, subsection
         "Canonicalization of Associative-Commutative Operations" *)
      let v =
        List.rev ls
        |> List.fold_left (fun v' v -> mk_binop b v v') (symbolicize t k)
      in
      encode v e
    | SymChoose (ls, tl) ->
      let v =
        List.rev ls
        |> List.fold_left (fun v' (b, v) -> mk_ite b v v') tl
      in
      encode v e
    end

let decode : (id * SA.atom) list -> env -> model =
  fun (sol : (id * SA.atom) list) (e : env) ->
  let fail s = failwith ("SMTlib decode: "^s) in
  let add_value model (var, v) =
    match SM.find_opt var e.smt_var2sv with
    | None ->
      fail ("no symbolic variable found for returned varname "^var)
    | Some x ->
      match x.node with Ex (_, symval) ->
      match (symval.node, v) with
      | (SymInt i, SA.Int v) ->
        model_add_int i (mk_int v) model
      | (SymInt i, SA.Bool _) ->
        fail ("wrong type: got bool for SymInt "^(string_of_int i))
      | (SymInt i, SA.Bit (w, v)) ->
        (* we use fixed-width bitvectors as integer standins *)
        if Bits.width v <> BI.to_int w then
          fail ("got bitvector length mismatch in int var "^var)
        else if Bits.width v <> int_width then
          fail ("wrong type: got "^(string_of_int (Bits.width v))^
                " bitvec for SymInt "^(string_of_int i))
        else
          model_add_int i (mk_int (Bits.to_big_int v)) model

      | (SymBool i, SA.Int _) ->
        fail ("wrong type: got int for SymBool "^(string_of_int i))
      | (SymBool i, SA.Bool v') ->
        model_add_bool i (mk_bool v') model
      | (SymBool i, SA.Bit (w, v)) ->
        (* some solvers provide width-1 bitvectors for booleans *)
        if Bits.width v <> BI.to_int w then
          fail ("got bitvector length mismatch in bool var "^var)
        else if Bits.width v <> 1 then
          fail ("wrong type: got "^(string_of_int (Bits.width v))^
                " bitvec for SymBool "^(string_of_int i))
        else if BI.to_int (Bits.to_big_int v) = 0 then
          model_add_bool i (mk_bool false) model
        else
          model_add_bool i (mk_bool true) model

      | (SymVec (i, _), SA.Int _) ->
        fail ("wrong type: got int for SymVec "^(string_of_int i))
      | (SymVec (i, _), SA.Bool _) ->
        fail ("wrong type: got bool for SymVec "^(string_of_int i))
      | (SymVec (i, l), SA.Bit (w, v)) ->
        if Bits.width v <> BI.to_int w then
          fail ("got bitvector length mismatch in vec var "^var^": "^
                "expected "^(string_of_int (Bits.width v))^"; "^
                "got "^(string_of_int (BI.to_int w))^"\n")
        else if l <> BI.to_int w then
          fail ("wrong type: got "^(string_of_bint w)^
                " bitvec for SymVec "^(string_of_int i)^
                " with length "^(string_of_int l))
        else
          model_add_vec i (mk_vec v) model

      (* ignore assignments to smtlib variables other than leaf symbolic variables *)
      | _ -> model
  in
  List.fold_left add_value model_empty sol

let encode_typ : type a. a sym_ref_t -> string =
  fun t ->
  match t with
  | IsInt -> "(_ BitVec "^(string_of_int int_width)^")" (*"Int"*)
  | IsVec l -> "(_ BitVec "^(string_of_int l)^")"
  | IsBool -> "Bool"
  | _ -> failwith "encode_typ: invalid type made it to encode"

(* look up encoding for variable *)
let encode_one e (id, var) =
  match SM.find_opt var e.smt_var2sv with
  | None -> failwith ("couldn't find mapping for UID "^(string_of_int id))
  | Some x ->
    match x.node with Ex (t, sv) ->
    let typ = encode_typ t in
    begin match sv.node with
    | SymVal (_, _) ->
      failwith "encode_one: encountered constant in variable defs"
    | SymInt _ -> declare_const var typ
    | SymBool _ -> declare_const var typ
    | SymVec (_, _) -> declare_const var typ
    | _ ->
      let def =
        match SM.find_opt var e.smt_var2def with
        | None -> failwith ("no encoded string def for "^var)
        | Some def -> def
      in
      define_const var typ def
    end

(* get encoding of environment *)
let string_of_env (e : env) =
  IM.bindings e.smt_i2var
  |> List.fold_left (fun l x -> (encode_one e x) :: l) []
  |> List.rev
  |> String.concat "\n"

(* get encoding of NEW items in environment: *)
(* variables defined in e and not in e' *)
let string_of_env_new (e : env) (e' : env) =
  let encode_new (id, var) =
    match IM.find_opt id e'.smt_i2var with
    (* if id is in the old env, it's already defined *)
    | Some _ -> []
    (* otherwise, add new declarations *)
    | None -> [encode_one e (id, var)]
  in
  IM.bindings e.smt_i2var
  |> List.fold_left (fun l x -> (encode_new x) @ l) []
  |> List.rev
  |> String.concat "\n"
