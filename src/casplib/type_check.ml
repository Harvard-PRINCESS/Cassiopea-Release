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
open Casp_ast

module PA = Prettyast

let print_verbose: (string -> unit) ref = ref (fun _ -> ())
let print_dump: (string -> unit) ref = ref (fun _ -> ())

(* TODO add error locations back *)

(* very simple type inference logic *)
(* easier since users cannot construct polymorphic terms *)
(* TODO make type inference more sophisticated *)

(* concrete type equality *)
let eq_typ t1 t2 =
  match (t1, t2) with
  | (IntType, IntType) -> true
  | (BoolType, BoolType) -> true
  | (StringType, StringType) -> true
  | (LocType i1, LocType i2) -> i1 == i2
  | (BitType i1, BitType i2) -> i1 == i2
  | (LabelType i1, LabelType i2) -> i1 == i2
  | (LabelType i1, BitType i2) -> i1 == i2
  | (BitType i1, LabelType i2) -> i1 == i2
  | (MemType (i1, i2, i3), MemType (i1', i2', i3')) ->
    (i1 == i1') && (i2 == i2') && (i3 == i3')
  | _ -> false

(* "types" used internally by the checker *)
(* (actually IntTerm is a term) *)
(* free variables are implicitly quantified *)
type metatyp =
  | UnitType
  | ConcreteType of typ
  | VariableType of id
  (* index argument for types varying with length *)
  | IntIndex of id
  | IntTerm of BI.t
  (* variable-length bitvecs and locations *)
  | BitFamily of id
  | LocFamily of id
  (* function is recursively defined but
     we currently avoid higher-order functions *)
  | FunctionType of metatyp list * metatyp

let rec string_of_metatyp = function
  | UnitType -> "()"
  | ConcreteType t -> PA.string_of_typ t
  | VariableType s -> "weak("^s^")"
  | IntIndex s -> "("^s^" : int)"
  | IntTerm i -> BI.string_of_big_int i
  | BitFamily s -> s^" bit"
  | LocFamily s -> s^" bit loc"
  | FunctionType (tt, t) ->
    let s = tt @ [t]
      |> List.map string_of_metatyp
      |> String.concat "->"
    in
    "function "^s

(* lift concrete typ to metatyp: convenient shorthands *)
let lift t = ConcreteType t

(* try to turn metatyp back into concrete typ *)
let lower t =
  match t with
  | ConcreteType t' -> t'
  | IntTerm _ -> IntType
  | _ -> failwith ("BUG: could not lower metatype "^(string_of_metatyp t))

(* get the set of free variables appearing in t *)
let rec free t =
  match t with
  | VariableType s -> SS.singleton s
  | IntIndex i -> SS.singleton i
  | BitFamily s -> SS.singleton s
  | LocFamily s -> SS.singleton s
  | FunctionType (tt, t) -> tt
    |> List.map free
    |> List.fold_left SS.union SS.empty
    |> SS.union (free t)
  | _ -> SS.empty

(* get a variable name not appearing in a set of free variables *)
let rec fresh f n =
  let next = "id"^(string_of_int n) in
  if SS.mem next f then
    fresh f (n + 1)
  else next

(* type variable environment *)
type subst = {
  typs : metatyp StringMap.t;
  lens : BI.t StringMap.t
}

let sub_empty = { typs = SM.empty; lens = SM.empty }

let bind m k =
  match m with
  | Ok v -> k v
  | Error s -> Error s

let bind2 m1 m2 k =
  match (m1, m2) with
  | (Ok v1, Ok v2) -> k v1 v2
  | (Error s, _) -> Error s
  | (_, Error s) -> Error s

(* apply a substitution in a type *)
let rec subst_apply (sub : subst) (t : metatyp) =
  match t with
  | UnitType -> UnitType
  | ConcreteType _ -> t
  | VariableType i ->
    let found = SM.find_opt i sub.typs in
    begin match found with
    | Some (IntIndex _ as t')
    | Some (IntTerm _ as t')
    | Some (FunctionType _ as t') ->
      failwith ("cannot substitute "^(string_of_metatyp t')^" for "^
                (string_of_metatyp t))
    | Some t' -> t'
    | _ -> t
    end
  | IntIndex i ->
    begin match SM.find_opt i sub.lens with
    | Some l -> IntTerm l
    | _ -> t
    end
  | IntTerm _ -> t
  | BitFamily i ->
    begin match SM.find_opt i sub.lens with
    | Some l -> lift (BitType (BI.int_of_big_int l))
    | _ -> t
    end
  | LocFamily i ->
    begin match SM.find_opt i sub.lens with
    | Some l -> lift (LocType (BI.int_of_big_int l))
    | _ -> t
    end
  | FunctionType (tt, t) ->
    FunctionType (List.map (subst_apply sub) tt, subst_apply sub t)

(* combine two substitutions *)
let subst_compose (sub1 : subst) (sub2 : subst) =
  let check map i v =
    match SM.find_opt i map with
    | Some v' -> v = v'
    | None -> false
  in
  if (SM.exists (check sub2.typs) sub1.typs) ||
     (SM.exists (check sub2.lens) sub1.lens) then
    Error "subst_compose conflict"
  else
    let union _ v1 v2 =
      if v1 = v2 then Some v1 else None
    in
    Ok { typs = SM.union union sub1.typs sub2.typs;
         lens = SM.union union sub1.lens sub2.lens }

(* returns: a substitution rendering the given types identical *)
let rec unify t1 t2 =
  let fail () =
    Error ("cannot unify "^(string_of_metatyp t1)^
           " and "^(string_of_metatyp t2))
  in
  match (t1, t2) with
  | (UnitType, UnitType) -> Ok sub_empty

  (* dependent indices should be specialized by application *)
  | (IntIndex _, _)
  | (_, IntIndex _) ->
    Error "caught dependent product in unify"
  | (IntTerm _, _)
  | (_, IntTerm _) ->
    Error "caught term in unify"

  (* avoid higher order functions *)
  | (VariableType _, FunctionType _)
  | (FunctionType _, VariableType _) -> fail ()

  (* otherwise anything is more constraining; unify arbitrarily *)
  | (VariableType i, t)
  | (t, VariableType i) ->
    Ok { sub_empty with typs = SM.singleton i t }

  (* bitvec and location types: unify only with concrete versions *)
  | (BitFamily i, ConcreteType (BitType l))
  | (ConcreteType (BitType l), BitFamily i)
  | (BitFamily i, ConcreteType (LabelType l))
  | (ConcreteType (LabelType l), BitFamily i) ->
    Ok { sub_empty with lens = SM.singleton i (BI.big_int_of_int l) }
  | (LocFamily i, ConcreteType (LocType l))
  | (ConcreteType (LocType l), LocFamily i) ->
    Ok { sub_empty with lens = SM.singleton i (BI.big_int_of_int l) }
  (* concrete types unify if identical *)
  | (ConcreteType t1', ConcreteType t2') ->
    if eq_typ t1' t2' then Ok sub_empty
    else fail ()

  (* functions: args then return type *)
  | (FunctionType (tt1, rt1), FunctionType (tt2, rt2)) ->
    (* unify function args pairwise *)
    let unify_next (sub : (subst, string) result) (t1, t2) =
      bind sub (fun sub ->
      let t1' = subst_apply sub t1 in
      let t2' = subst_apply sub t2 in
      bind (unify t1' t2') (fun s ->
      subst_compose s sub))
    in
    let s1 =
      try
        List.combine tt1 tt2
        |> List.fold_left unify_next (Ok sub_empty)
      with Invalid_argument _ ->
        Error ("could not unify functions "^(string_of_metatyp t1)^
               " and "^(string_of_metatyp t2)^": arg count differs")
    in
    (* unify function return type *)
    let s2 = bind s1 (fun s1 ->
      unify (subst_apply s1 rt1) (subst_apply s1 rt2))
    in
    bind2 s1 s2 subst_compose
  | _ -> fail ()

(* typing context construction and lookup *)
let tenv_find tenv pos i =
  match SM.find_opt i tenv with
  | None -> failat pos ("id "^i^" not found in type env")
  | Some t -> t

(* returns: type of this atomic *)
let type_check_atomic tenv (pos, a) =
  match a with
  | Id i -> tenv_find tenv pos i
  | Int i -> IntTerm i
  | Bool _ -> lift BoolType
  | Vec b -> lift (BitType (Bits.width b))
  | Ptr (i, _) ->
    begin match tenv_find tenv pos i with
    | ConcreteType (MemType (_, _, r)) -> lift (LabelType r)
    | _ -> failat pos ("could not find memory region "^i)
    end
  | Str _ -> lift StringType

(* returns: type obtained from applying term of type t against
   atomic args aa *)
(* TODO error message catch and handle: esp. with List.combine *)
let rec type_check_app pos ft tt =
  (* construct a specialized fxn type for unify *)
  let spec (at', tt', sub) (a, t) =
    match (a, t) with
    (* sanity-check argument types *)
    | (IntTerm _, _) ->
      failat pos "encountered int term in applicative signature"
    | (_, IntIndex _) ->
      failat pos "encountered index as type of atomic"
    (* specialize an index *)
    | (IntIndex i, IntTerm l) ->
      (at', tt', { sub with lens = SM.add i l sub.lens })
    | (IntIndex _, ConcreteType IntType) ->
      failat pos "cannot specialize dependent index without value"
    | (IntIndex _, _) ->
      failat pos "cannot specialize dependent index with non-int"
    (* replace int terms with int type *)
    | (_, IntTerm _) ->
      (a :: at', (ConcreteType IntType) :: tt', sub)
    (* pass other values through *)
    | _ -> (a :: at', t :: tt', sub)
  in
  match ft with
  | FunctionType (at, rt) ->
    (* first, specialize dependent indices *)
    let (at', tt', sub) =
      try
        List.combine at tt
        |> List.fold_left spec ([], [], sub_empty)
      with Invalid_argument _s ->
        failat pos ("wrong number of arguments to "^
                  (string_of_metatyp ft)^": got "^
                  (string_of_int (List.length tt))^", expected "^
                  (string_of_int (List.length at)))
    in
    let fresh_t = fresh (free ft) 0 in
    let spec_ft = subst_apply sub (FunctionType (at', rt)) in
    (* now, unify remaining free variables *)
    let free_ft = FunctionType (tt', VariableType fresh_t) in
    begin match unify spec_ft free_ft with
    | Ok sub -> subst_apply sub (VariableType fresh_t)
    | Error s -> failat pos s
    end
  | _ ->
    let st = tt
      |> List.map string_of_metatyp
      |> String.concat ","
    in
    failat pos ("cannot apply "^(string_of_metatyp ft)^" to ("^st^")")

(* returns: type of this expr *)
and type_check_expr tenv (pos, e) =
  let result = match e with
    | Atomic a -> type_check_atomic tenv (pos, a)
    | Deref e -> type_check_expr_deref tenv pos e
    | Fetch (e1, e2) -> type_check_expr_load tenv pos e1 e2
    | Index (e1, e2) -> type_check_expr_index tenv pos e1 e2
    | Slice (e1, e2, e3) -> type_check_expr_slice tenv pos e1 e2 e3
    | Unop (u, e) -> type_check_expr_unop tenv pos u e
    | Binop (e1, b, e2) -> type_check_expr_binop tenv pos e1 b e2
    | App (i, ee) -> type_check_expr_app tenv pos i ee
    | LetE (i, t, e1, e2) -> type_check_expr_lete tenv pos i t e1 e2
    | IfE (e1, e2, e3) -> type_check_expr_ife tenv pos e1 e2 e3
  in
  begin match result with
  | ConcreteType (BitType l)
  | ConcreteType (LabelType l)
  | ConcreteType (LocType l) ->
    if l = 0 then
      failat pos "encountered 0 bit: 0 bit is forbidden!"
  | _ -> ()
  end;
  result

and type_check_expr_deref tenv pos e =
  let t = type_check_expr tenv e in
  match t with
  | ConcreteType (LocType l) -> lift (BitType l)
  | _ ->
    failat pos ("Deref expected location but got "^
                (PA.string_of_typ (lower t)))

and type_check_expr_load tenv pos e1 e2 =
  let t1 = type_check_expr tenv e1 in
  let t2 = type_check_expr tenv e2 in
  match (lower t1, t2) with
  | (BitType _, IntTerm i)
  | (LabelType _, IntTerm i) ->
    lift (BitType (BI.int_of_big_int i))
  | (BitType _, ConcreteType IntType)
  | (LabelType _, ConcreteType IntType) ->
    failat pos "could not statically determine Load length: sorry!"
  | (_, _) ->
    failat pos ("Load expected [bitvector, int] but got ["^
                (PA.string_of_typ (lower t1))^","^
                (PA.string_of_typ (lower t2))^"]")

and type_check_expr_index tenv pos e1 e2 =
  let t = type_check_expr tenv e1 in
  let t' = type_check_expr tenv e2 in
  match (t, t') with
  | (ConcreteType (BitType l), IntTerm i) ->
    let i = BI.int_of_big_int i in
    if 0 <= i && i < l then
      lift BoolType
    else
      failat pos ("Index by out-of-bounds constant: bit "^
                  (string_of_int i)^" of "^(string_of_int l)^" bits")
  (* index not always statically determined: slight danger *)
  | (ConcreteType (BitType _), ConcreteType IntType) ->
    lift BoolType
  | (ConcreteType (BitType _), _) ->
    failat pos ("Index expected integer but got "^
                (PA.string_of_typ (lower t')))
  | (_, _) ->
    failat pos ("Index expected bitvector but got "^
                (PA.string_of_typ (lower t)))

and type_check_expr_slice tenv pos e1 e2 e3 =
  let t = type_check_expr tenv e1 in
  let t1 = type_check_expr tenv e2 in
  let t2 = type_check_expr tenv e3 in
  match (t, t1, t2) with
  | (ConcreteType (BitType l), IntTerm i1, IntTerm i2) ->
    (* type depends on length -- we only handle constants *)
    let i1 = BI.int_of_big_int i1 in
    let i2 = BI.int_of_big_int i2 in
    if 0 <= i1 && i1 < i2 && i2 <= l then
      lift (BitType (i2 - i1))
    else
      failat pos ("Slice got invalid constant args: "^
                  "["^(string_of_int i1)^":"^(string_of_int i2)^"]")
  | (ConcreteType (BitType _), IntTerm _, ConcreteType IntType)
  | (ConcreteType (BitType _), ConcreteType IntType, IntTerm _)
  | (ConcreteType (BitType _), ConcreteType IntType, ConcreteType IntType) ->
    failat pos ("could not statically determine Slice length: sorry!")
  | (ConcreteType (BitType _), _, _) ->
    failat pos ("Slice expected integer bounds but got "^
                "["^(PA.string_of_typ (lower t1))^":"^
                (PA.string_of_typ (lower t2))^"]")
  | (_, _, _) ->
    failat pos ("Slice expected bitvector but got "^
                (PA.string_of_typ (lower t)))

and type_check_expr_unop tenv pos u e =
  let t = type_check_expr tenv e in
  let check t' rt = type_check_app pos (FunctionType ([t'], rt)) [t] in
  let check_arith f =
    match t with
    | IntTerm i -> IntTerm (f i)
    | ConcreteType IntType -> lift IntType
    | _ -> failat pos ("expected [int]; got ["^
                      (PA.string_of_typ (lower t))^"]")
  in
  match u with
  | Neg -> check_arith BI.minus_big_int
  | LogNot -> check (lift BoolType) (lift BoolType)
  | BitNot -> check (BitFamily "n") (BitFamily "n")

and type_check_expr_binop tenv pos e1 b e2 =
  let t1 = type_check_expr tenv e1 in
  let t2 = type_check_expr tenv e2 in
  let check (t1', t2') rt =
    type_check_app pos (FunctionType ([t1'; t2'], rt)) [t1; t2]
  in
  (* check integer op, permit constant folding *)
  let check_arith f =
    match (t1, t2) with
    | (IntTerm i1, IntTerm i2) -> IntTerm (f i1 i2)
    | (ConcreteType IntType, IntTerm _) -> lift IntType
    | (IntTerm _, ConcreteType IntType) -> lift IntType
    | (ConcreteType IntType, ConcreteType IntType) -> lift IntType
    | _ -> failat pos ("expected [int; int]; got ["^
                      (PA.string_of_typ (lower t1))^";"^
                      (PA.string_of_typ (lower t2))^"]")
  in
  match b with
  (* integer operations *)
  | Add -> check_arith BI.add_big_int
  | Sub -> check_arith BI.sub_big_int
  | Mul -> check_arith BI.mult_big_int
  | Div -> check_arith BI.div_big_int
  | Pow -> check_arith BI.power_big_int_positive_big_int
  (* equality comparisons need same type *)
  | Eq
  | Neq -> check (VariableType "t", VariableType "t") (lift BoolType)
  (* inequalities operate on integers *)
  | Lt
  | Gt -> check (lift IntType, lift IntType) (lift BoolType)
  (* bitvector operations need same length *)
  | BAdd -> check (BitFamily "n", BitFamily "n") (BitFamily "n")
  | BSub -> check (BitFamily "n", BitFamily "n") (BitFamily "n")
  | BMul -> check (BitFamily "n", BitFamily "n") (BitFamily "n")
  | BLt -> check (BitFamily "n", BitFamily "n") (lift BoolType)
  | BGt -> check (BitFamily "n", BitFamily "n") (lift BoolType)
  | BSLt -> check (BitFamily "n", BitFamily "n") (lift BoolType)
  | BSGt -> check (BitFamily "n", BitFamily "n") (lift BoolType)
  (* shifts type as their left operand *)
  | LShift
  | RShift -> check (BitFamily "n", BitFamily "n") (BitFamily "n")
  (* logical boolean operations *)
  | LogAnd
  | LogOr
  | LogXor -> check (lift BoolType, lift BoolType) (lift BoolType)
  (* bitwise boolean operations need same length *)
  | BitAnd
  | BitOr
  | BitXor -> check (BitFamily "n", BitFamily "n") (BitFamily "n")

and type_check_expr_app tenv pos i ee =
  (* type the arguments *)
  let tt = List.map (type_check_expr tenv) ee in
  if i = "format" then
    match List.hd ee with
    | (_, Atomic (Str s)) ->
      if Formatstring.is_format s then
        let parsed = Formatstring.parse pos s in
        let expected_argnum = Formatstring.getnumargs parsed in
        let t = FunctionType (List.init (expected_argnum + 1) (fun _ -> lift StringType), lift StringType) in
        type_check_app pos t tt
      else failat pos ("String Format: first param is not a format string")
    | _ -> failat pos ("String Format: only accepts string as first param")
  else if i = "dec" || i = "hex" || i = "bin" then
    match tt with
    | [t] ->
      begin match (unify t (BitFamily "n"), unify t (lift IntType)) with
      | (Ok _, _) -> lift StringType
      | (_, Ok _) -> lift StringType
      | _ -> failat pos ("String Format: expected Int/Vec arg, but got "^
                        (string_of_metatyp t))
      end
    | _ -> failat pos ("String Format: expected ONE Int/Vec arg, but got "^
                      (string_of_int (List.length ee))^" args")
  else
    let t = tenv_find tenv pos i in
    type_check_app pos t tt

and type_check_expr_lete tenv pos i t e1 e2 =
  (* 1. type of e1 should match t *)
  (* 2. e2 should typecheck with extended typing context *)
  let t' = type_check_expr tenv e1 in
  if eq_typ t (lower t') then
    type_check_expr (SM.add i t' tenv) e2
  else
    failat pos ("LetE declared with type "^(PA.string_of_typ t)^" "^
                "but got "^(PA.string_of_typ (lower t')))

and type_check_expr_ife tenv pos e1 e2 e3 =
  let t = lower (type_check_expr tenv e1) in
  let t1 = type_check_expr tenv e2 in
  let t2 = type_check_expr tenv e3 in
  match t with
  | BoolType ->
    if eq_typ (lower t1) (lower t2) then lift (lower t1)
    else
      failat pos ("IfE requires same-type branches but got "^
                  (PA.string_of_typ (lower t1))^" and "^
                  (PA.string_of_typ (lower t2)))
  | _ ->
    failat pos ("IfE expected boolean condition but got "^
                (PA.string_of_typ t))

(* Type check a stmt against a typing context. *)
let rec type_check_stmt tenv (pos, s) =
  match s with
  | Skip -> ()
  | Err -> ()
  | Assert (e, _) -> type_check_stmt_assert tenv pos e
  | Seq (s1, s2) -> type_check_stmt tenv s1; type_check_stmt tenv s2; ()
  | Assign (e1, e2) -> type_check_stmt_assign tenv pos e1 e2
  | Store (e1, e2, e) -> type_check_stmt_store tenv pos e1 e2 e
  | For (i, e1, e2, s) -> type_check_stmt_for tenv pos i e1 e2 s
  | Call (i, ee) -> type_check_stmt_call tenv pos i ee
  | LetS (i, t, e, s) -> type_check_stmt_lets tenv pos i t e s
  | IfS (e, s1, s2) -> type_check_stmt_ifs tenv pos e s1 s2

and type_check_stmt_assert tenv pos e =
  let t = type_check_expr tenv e in
  match t with
  | ConcreteType BoolType -> ()
  | _ ->
    failat pos ("Assert of a non-boolean: got "^
                (PA.string_of_typ (lower t)))

and type_check_stmt_assign tenv pos e1 e2 =
  let t = type_check_expr tenv e1 in
  let t' = type_check_expr tenv e2 in
  match (t, t') with
  | (ConcreteType (LocType l1), ConcreteType (BitType l2))
  | (ConcreteType (LocType l1), ConcreteType (LabelType l2)) ->
    if l1 = l2 then ()
    else
      failat pos ("len of state does not match len of expr in assign: "^
                  "state "^(string_of_int l1)^", "^
                  "expr "^(string_of_int l2))
  | (ConcreteType (LocType _), _) ->
    failat pos ("Assign of a non-bitvector: "^
                "state "^(PA.string_of_typ (lower t))^", "^
                "expr "^(PA.string_of_typ (lower t')))
  | _ ->
    failat pos ("Assign to a non-location: got "^
                (PA.string_of_typ (lower t)))

and type_check_stmt_store tenv pos e1 e2 e =
  let t1 = lower (type_check_expr tenv e1) in
  let t2 = type_check_expr tenv e2 in
  let t' = lower (type_check_expr tenv e) in
  match (t1, t2, t') with
  (* XXX slot-wise addressing *)
  | (BitType _, IntTerm i, BitType l)
  | (BitType _, IntTerm i, LabelType l)
  | (LabelType _, IntTerm i, BitType l)
  | (LabelType _, IntTerm i, LabelType l) ->
    let i = BI.int_of_big_int i in
    if i = l then ()
    else
      failat pos ("len of store does not match len of bitvec: "^
                  "expected "^(string_of_int i)^
                  ", got "^(string_of_int l))
  | (BitType _, IntTerm _, _)
  | (LabelType _, IntTerm _, _) ->
    failat pos ("Store expected bitvector, got "^
                (PA.string_of_typ (lower t2)))
  | (BitType _, ConcreteType IntType, _)
  | (LabelType _, ConcreteType IntType, _) ->
    failat pos "could not statically determine Store length: sorry!"
  | (_, _, _) ->
    failat pos ("Store expected [bitvec, int], got ["^
                (PA.string_of_typ t1)^","^
                (PA.string_of_typ (lower t2))^"]")

and type_check_stmt_for tenv pos i e1 e2 s =
  let t1 = lower (type_check_expr tenv e1) in
  let t2 = lower (type_check_expr tenv e2) in
  match (t1, t2) with
  | (IntType, IntType) ->
    type_check_stmt (SM.add i (lift IntType) tenv) s
  | _ ->
    failat pos ("for loop requires integer limits but got ["^
                (PA.string_of_typ t1)^"..."^
                (PA.string_of_typ t2)^"]")

and type_check_stmt_call tenv pos i ee =
  let t = tenv_find tenv pos i in
  let tt = List.map (type_check_expr tenv) ee in
  if type_check_app pos t tt = UnitType then ()
  else
    failat pos ("called identifier "^i^" is not bound to a subroutine")

and type_check_stmt_lets tenv pos i t e s =
  let t' = type_check_expr tenv e in
  if eq_typ t (lower t') then
    type_check_stmt (SM.add i t' tenv) s
  else
    failat pos ("LetS declared with type "^(PA.string_of_typ t)^" "^
                "but got "^(PA.string_of_typ (lower t')))

and type_check_stmt_ifs tenv pos e s1 s2 =
  let t = lower (type_check_expr tenv e) in
  match t with
  | BoolType ->
    type_check_stmt tenv s1; type_check_stmt tenv s2
  | _ ->
    failat pos ("IfS expected boolean condition but got "^
                (PA.string_of_typ t))

(* types of builtins *)
let tenv_empty = SM.empty
  |> SM.add "true" (lift BoolType)
  |> SM.add "false" (lift BoolType)
  |> SM.add "bv_to_len"
    (FunctionType ([IntIndex "i"; BitFamily "n"], BitFamily "i"))
  |> SM.add "bv_to_uint"
    (FunctionType ([BitFamily "n"], lift IntType))
  |> SM.add "uint_to_bv_l"
    (FunctionType ([IntIndex "i"; lift IntType], BitFamily "i"))
  |> SM.add "checkbit"
    (FunctionType ([BitFamily "n"; BitFamily "n"], lift BoolType))
  |> SM.add "checkfield"
    (FunctionType ([BitFamily "n"; IntIndex "l"; lift IntType; lift IntType], BitFamily "l"))
  |> SM.add "flag_set"
    (FunctionType ([BitFamily "n"; IntIndex "i"], BitFamily "n"))
  |> SM.add "flag_unset"
    (FunctionType ([BitFamily "n"; IntIndex "i"], BitFamily "n"))
  |> SM.add "rotate_left"
    (FunctionType ([BitFamily "n"; BitFamily "n"], BitFamily "n"))
  |> SM.add "rotate_right"
    (FunctionType ([BitFamily "n"; BitFamily "n"], BitFamily "n"))
  |> SM.add "isptr"
    (FunctionType ([BitFamily "n"], lift BoolType))
  |> SM.add "txt"
    (FunctionType ([LocFamily "n"], lift StringType))
  |> SM.add "lbl"
    (FunctionType ([BitFamily "n"], lift StringType))
  |> SM.add "BRANCH"
    (FunctionType ([lift IntType], UnitType))
  (* |> SM.add "armcc"
    (FunctionType ([BitFamily "n"], lift StringType)) *)

let type_check_let tenv pos t e =
  let t' = type_check_expr tenv e in
  if eq_typ t (lower t') then
    t'
  else
    failat pos ("let declared of type "^(PA.string_of_typ t)^
                " but got "^(string_of_metatyp t'))

let type_check_letstate _tenv pos t =
  match t with
  | LocType l -> lift (LocType l)
  | MemType (b, l, r) -> lift (MemType (b, l, r))
  | _ ->
    failat pos ("letstate expected location type or memory type, got "^(PA.string_of_typ t))

let type_check_invariant tenv pos e =
  let t' = type_check_expr tenv e in
  match t' with
  | ConcreteType BoolType -> ()
  | _ ->
    failat pos ("invariant requires boolean expression, but resolved as "^(string_of_metatyp t'))

let type_check_def tenv pos aa t e =
  let add tenv (i, t) = SM.add i (lift t) tenv in
  let tenv = List.fold_left add tenv aa in
  let t' = type_check_expr tenv e in
  if eq_typ t (lower t') then
    FunctionType (List.map (fun (_, t) -> lift t) aa, t')
  else
    failat pos ("def declared to return "^(PA.string_of_typ t)^" "^
                "but resolved as "^(string_of_metatyp t'))

let type_check_defs tenv _pos aa s =
  let add tenv (i, t) = SM.add i (lift t) tenv in
  let tenv = List.fold_left add tenv aa in
  let _ = type_check_stmt tenv s in
  FunctionType (List.map (fun (_, t) -> lift t) aa, UnitType)

let type_check_defop tenv _ aa s =
  let add tenv (i, t) = SM.add i (lift t) tenv in
  let tenv = List.fold_left add tenv aa in
  type_check_stmt tenv s
