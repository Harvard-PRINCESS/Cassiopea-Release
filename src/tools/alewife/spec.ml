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
open Ale_ast
open Reps
module C = Casp_ast
module PA = Prettyast

type env = {
  abstyp : (unit SM.t) list;
  absvalue : (typ SM.t) list; 
  absfunc : (typ SM.t) list;
  absmem : ((width * width * width * id option) SM.t) list;
  typ : (C.typ SM.t) list; 
  value : ((C.expr * C.typ) SM.t) list;
  func : ((C.arg list * C.typ * C.expr) SM.t) list;
  arg : (C.typ SM.t) list;
  mem : ((int * int * int) SM.t) list;
  l2m : (string SM.t) list; (* label - memory mapping *)
}

let env_empty = {
  abstyp = [SM.empty];
  absvalue = [SM.empty];
  absfunc = [SM.empty];
  absmem = [SM.empty];
  typ = [SM.empty];
  value = [SM.empty];
  func = [SM.empty];
  arg = [SM.empty];
  mem = [SM.empty];
  l2m = [SM.empty];
}

let env_new_stack env = 
  { abstyp = List.cons (List.hd env.abstyp) env.abstyp;
    absvalue = List.cons (List.hd env.absvalue) env.absvalue;
    absfunc = List.cons (List.hd env.absfunc) env.absfunc;
    absmem = List.cons (List.hd env.absmem) env.absmem;
    typ = List.cons (List.hd env.typ) env.typ;
    value = List.cons (List.hd env.value) env.value;
    func = List.cons (List.hd env.func) env.func;
    arg = List.cons (List.hd env.arg) env.arg;
    mem = List.cons (List.hd env.mem) env.mem;
    l2m = List.cons (List.hd env.l2m) env.l2m;
  }

let valid_id env i =
  if (SM.mem i (List.hd env.value)) || (SM.mem i (List.hd env.func)) || 
      (SM.mem i (List.hd env.arg)) || (SM.mem i (List.hd env.mem)) || 
      (SM.mem i (List.hd env.l2m)) then i
  else failwith ("Name error: id "^i^" not declared or defined")

let pre_check_id env i =
  if SM.mem i (List.hd env.abstyp) then 
    failwith ("id "^i^" is already bound to a abstract type")
  else if SM.mem i (List.hd env.absvalue) then 
    failwith ("id "^i^" is already bound to a abstract value")
  else if SM.mem i (List.hd env.absfunc) then 
    failwith ("id "^i^" is already bound to a abstract function")
  else if SM.mem i (List.hd env.absmem) then
    failwith ("id "^i^" is already bound to a abstract memory region")
  else ()

let check_id env i =
  if SM.mem i (List.hd env.typ) then
    failwith ("id "^i^" is already bound to a concret type")
  else if SM.mem i (List.hd env.value) then
    failwith ("id "^i^" is already bound to a concret value")
  else if SM.mem i (List.hd env.func) then
    failwith ("id "^i^" is already bound to a concret function")
  else if SM.mem i (List.hd env.mem) then
    failwith ("id "^i^" is already bound to a concret memory region")
  else if SM.mem i (List.hd env.l2m) then
    failwith ("id "^i^" is already bound to a memory label")
  else ()

let getwidth (c: casp_file) (oenv: env option) (w: width) =
  match w with
  | ConcWidth c -> BI.int_of_big_int c
  | SymWidth x ->
      let x =
        (* compat for old alewife files; remove sometime *)
        match x with
        | "word" ->
            prerr_string "Warning: bitsize \"word\" should be \"wordsize\"\n";
            "wordsize"
        | _ -> x
      in
      match oenv with
      | None -> begin
          match SM.find_opt x c.lets with
          | None -> 99 (* placeholder for first pass *)
          | Some (Int k, _t) -> BI.int_of_big_int k
          | Some _ -> failwith ("Invalid type width " ^ x ^ " (preprocess)")
        end
      | Some env -> begin
          match SM.find_opt x (List.hd env.value) with
          | None -> failwith ("Unbound type width " ^ x)
          | Some ((_pos, Atomic (Int k)), _t) -> BI.int_of_big_int k
          | Some _ -> failwith ("Invalid type width " ^ x)
       end

let concrete_type (c: casp_file) (t: typ) : C.typ = 
  match t with 
  | BoolType -> C.BoolType
  | IntType -> C.IntType
  | LblType w -> C.LabelType (getwidth c None w)
  | BitType -> C.BitType 1
  | VecType w -> C.BitType (getwidth c None w)
  | PtrType w -> C.BitType (getwidth c None w)
  | RegType w -> C.LocType (getwidth c None w)
  | AbsType i ->
    ( match SM.find_opt i c.types with
      | Some i -> i
      | None -> failwith ("Type error: undeclared abstract type "^i^" in casp during pre-processing") )
  | _ -> failwith ("Type error: function type cannot be converted during pre-processing")

let convert_type env (c: casp_file) (t: typ) : C.typ =
  match t with 
  | BoolType -> C.BoolType
  | IntType -> C.IntType
  | LblType w -> C.LabelType (getwidth c (Some env) w)
  | BitType -> C.BitType 1
  | VecType w -> C.BitType (getwidth c (Some env) w)
  | PtrType w -> C.BitType (getwidth c (Some env) w)
  | RegType w -> C.LocType (getwidth c (Some env) w)
  | AbsType i ->
    ( match SM.find_opt i (List.hd env.typ) with
      | Some i -> i
      | None -> failwith ("Type error: undeclared abstract type "^i^" in casp") )
  | _ -> failwith ("Type error: function type cannot be converted")

let convert_atomic env a =
  match a with
  | Id i -> C.Id (valid_id env i)
  | Int i -> C.Int i
  | Bool b -> C.Bool b
  | Vec v -> C.Vec v
  | Ptr (i, o) -> C.Ptr ((valid_id env i), o)

let convert_unop = function
  | Neg -> C.Neg
  | LogNot -> C.LogNot
  | BitNot -> C.BitNot

let convert_binop = function
  | Add -> C.Add
  | Sub -> C.Sub
  | Mul -> C.Mul
  | Div -> C.Div
  | Eq -> C.Eq
  | Neq -> C.Neq
  | Lt -> C.Lt
  | Gt -> C.Gt
  | LShift -> C.LShift
  | RShift -> C.RShift
  | LogAnd -> C.LogAnd
  | LogOr -> C.LogOr
  | LogXor -> C.LogXor
  | BitAnd -> C.BitAnd
  | BitOr -> C.BitOr
  | BitXor -> C.BitXor

let rec convert_expr env (c: casp_file) (ee: expr) : (env * C.expr) =
  match ee with 
  | Atomic a -> (env, (Pos.none, C.Atomic (convert_atomic env a)))
  | Deref e -> 
    let (env, i) = convert_expr env c e in 
    (env, (Pos.none, C.Deref i))
  | Fetch e -> 
    let (env, i) = convert_expr env c e in 
    (env, (Pos.none, C.Fetch (i, (Pos.none, C.Atomic (C.Int (BI.of_int c.wordsize))))))
  | Index (e1, e2) -> 
    let (env, i1) = convert_expr env c e1 in 
    let (env, i2) = convert_expr env c e2 in 
    (env, (Pos.none, C.Index (i1, i2)))
  | Slice (e1, e2, e3) -> 
    let (env, i1) = convert_expr env c e1 in 
    let (env, i2) = convert_expr env c e2 in 
    let (env, i3) = convert_expr env c e3 in 
    (env, (Pos.none, C.Slice (i1, i2, i3)))
  | LetE (i, t, e1, e2) -> 
    let _ = check_id env i in
    let t = convert_type env c t in
    let (env, i1) = convert_expr env c e1 in 
    let env = { env with value = (SM.add i (i1, t) (List.hd env.value)) :: List.tl env.value } in
    let (env, i2) = convert_expr env c e2 in 
    (env, (Pos.none, C.LetE (i, t, i1, i2)))
  | IfE (e1, e2, e3) -> 
    let (env, i1) = convert_expr env c e1 in 
    let (env, i2) = convert_expr env c e2 in 
    let (env, i3) = convert_expr env c e3 in 
    (env, (Pos.none, C.IfE (i1, i2, i3)))
  | App (i, args) -> 
    let one_arg (e, exprs) a =
      let (e, i) = convert_expr e c a in (e, exprs @ [i])
    in
    let (env, argsls) = List.fold_left one_arg (env, []) args in
    (env, (Pos.none, C.App (valid_id env i, argsls)))
  | Implies (e1, e2) -> 
    let (env, i1) = convert_expr env c e1 in 
    let (env, i2) = convert_expr env c e2 in 
    (env, (Pos.none, C.Binop ((Pos.none, C.Unop (C.LogNot, i1)), C.LogOr, i2)))
  | Unop (u, e) ->
    let u = convert_unop u in
    let (env, i) = convert_expr env c e in 
    (env, (Pos.none, C.Unop (u, i)))
  | Binop (e1, b, e2) ->
    let b = convert_binop b in
    let (env, i1) = convert_expr env c e1 in 
    let (env, i2) = convert_expr env c e2 in 
    (env, (Pos.none, C.Binop (i1, b, i2)))
  (* | Label i -> (env, (Pos.none, C.Label i)) *)

let pre_process_require env rs = 
  let one_require e r =
    match r with 
    | RequireType i -> 
      { e with abstyp = (SM.add i () (List.hd e.abstyp)) :: (List.tl e.abstyp) }
    | RequireVal (i, t)  -> 
      { e with absvalue = (SM.add i t (List.hd e.absvalue)) :: (List.tl e.absvalue) }
    | RequireFunc (i, t) -> 
      { e with absfunc = (SM.add i t (List.hd e.absfunc)) :: (List.tl e.absfunc) }
  in
  List.fold_left one_require env rs

let pre_process_provide env ps = 
  let one_provide e p =
    match p with 
    | ProvideType (i, _) -> 
      let _ = pre_check_id e i in
      { e with abstyp = (SM.add i () (List.hd e.abstyp)) :: (List.tl e.abstyp) }
    | ProvideVal (i, t, _)  -> 
      let _ = pre_check_id e i in
      { e with absvalue = (SM.add i t (List.hd e.absvalue)) :: (List.tl e.absvalue) }
    | ProvideFunc (i, ps, rt, _) -> 
      let _ = pre_check_id e i in
      let t = FunType ((List.map snd ps), rt) in
      { e with absfunc = (SM.add i t (List.hd e.absfunc)) :: (List.tl e.absfunc) }
  in
  List.fold_left one_provide env ps

let pre_process_block env (_i, (frames, blocklets, _pre, _post)) = 
  let one_frame e f = 
    match f with 
    | FrameLabel (i1, b, l, r, i2) -> 
      let _ = pre_check_id e i1 in
      let _ = pre_check_id e i2 in
      { e with absmem = (SM.add i1 (b, l, r, Some i2) (List.hd e.absmem)) :: (List.tl e.absmem); l2m = (SM.add i2 i1 (List.hd e.l2m)) :: (List.tl e.l2m) }
    | FrameRegion (i, b, l, r) ->
      let _ = pre_check_id e i in
      { e with absmem = (SM.add i (b, l, r, None) (List.hd e.absmem)) :: (List.tl e.absmem) }
    | FrameAccess _ -> e
    | FrameModify _ -> e
    | FrameInvariant _ -> e
  in
  let one_blocklet e (i, t, _) = 
    let _ = pre_check_id e i in
    { e with absvalue = ( SM.add i t (List.hd e.absvalue)) :: (List.tl e.absvalue) }
  in
  let env = env_new_stack env in
  let env = List.fold_left one_frame env frames in
  List.fold_left one_blocklet env blocklets

let pre_process_ale (rs, ps, bl) =
  let env = pre_process_require env_empty rs in
  let env = pre_process_provide env ps in
  pre_process_block env bl

let tenv_of_ale (c: casp_file) tenv env = 
  let add_mem i (b, l, r, lbl) (c, te, e) =
     (*
      * XXX: for symbolic widths defined in the mapping (as opposed to
      * the machine) this will get the placeholder "99" value. This
      * does not get replaced with the real value later and fails
      * miserably downstream. This should be fixed, and you'll know
      * you've hit the problem if you see 99-bit pointers or 99-long
      * memory regions in the output casp. Sigh.
      *)
     let b' = getwidth c None b in
     let l' = getwidth c None l in
     let r' = getwidth c None r in
     match lbl with 
     | Some lbl -> 
         ( { c with mems = SM.add i (b', l', r', Some lbl) c.mems; lbls = SM.add lbl i c.lbls }, 
            SM.add i (Type_check.lift (MemType (b', l', r'))) te,
            { e with l2m = (SM.add lbl i (List.hd e.l2m)) :: (List.tl e.l2m); mem = (SM.add i (b', l', r') (List.hd e.mem)) :: (List.tl e.mem)} )
     | None -> 
         ( { c with mems = SM.add i (b', l', r', None) c.mems }, 
            SM.add i (Type_check.lift (MemType (b', l', r'))) te,
            { e with mem = (SM.add i (b', l', r') (List.hd e.mem)) :: (List.tl e.mem)})
  in
  let add_let i t (c, te, e) = 
    (c, SM.add i (Type_check.lift (concrete_type c t)) te, e) in
  (* XXX: add abstract functions into type env? *)
  (c, tenv, env) 
  |> SM.fold add_mem (List.hd env.absmem)
  |> SM.fold add_let (List.hd env.absvalue)

let pre_process_casp casp = 
  List.fold_left Process.process_decl (casp_file_empty, Type_check.tenv_empty) casp

let process_mapdecl ((c, tenv), lets) (pos, decl) =
  match decl with
  | C.DeclType (i, t) -> 
    (Process.process_type c tenv pos i t, lets)
  | C.DeclLet (i, t, e) ->
    (Process.process_speclet c tenv pos i t e, lets @ [(i, (t, e))])
  | C.DeclString (i, s) ->
    (Process.process_string c tenv pos i s, lets)
  | C.DeclLetstate (i1, t, i2) ->
    (Process.process_letstate c tenv pos i1 t i2, lets)
  | C.DeclInvariant e -> 
    (Process.process_invariant c tenv pos e, lets)
  | C.DeclDef (i, aa, t, e) ->
    (Process.process_def c tenv pos i aa t e, lets)
  | C.DeclDefs (i, aa, s) ->
    (Process.process_defs c tenv pos i aa s, lets)
  | C.DeclDefop (_i, _aa, _se, _ot, _s) ->((c, tenv), lets)

let process_mapping casp tenv (_pos, _i, decls, modifies) = 
  let ((casp, _), lets) = 
    List.fold_left process_mapdecl ((casp, tenv), []) decls 
  in
  (casp, lets, modifies)

let process_require (c: casp_file) env lets rs = 
  let one_require (e, str, ls) r =
    match r with 
    | RequireType i -> 
      ( match SM.find_opt i c.types with 
        | Some ct -> 
          ( {e with typ = (SM.add i ct (List.hd e.typ)) :: (List.tl e.typ)}, str, ls )
        | None -> failwith ("Ale: require type "^i^" undefined in mapping casp") )
    | RequireVal (i, t)  -> 
      ( match SM.find_opt i c.lets with 
        | Some (ca, ct) -> 
          let typ_cmp = Type_check.eq_typ (Process.alias_resolve c Pos.none ct) (Process.alias_resolve c Pos.none (convert_type e c t)) in
          if typ_cmp then 
            ( {e with value = (SM.add i ((Pos.none, C.Atomic ca), ct) (List.hd e.value)) :: List.tl e.value}, str, List.remove_assoc i ls )
          else failwith ("Ale: require value "^i^" with unconsistent type "^(string_of_typ t))
        | None -> (* check lets list *)
          ( match List.find_opt (fun (li, (_lt, _le)) -> li = i) ls with
            | Some (li, (lt, le)) ->
              ( {e with value = (SM.add li (le, lt) (List.hd e.value)) :: (List.tl e.value)}, str^"let "^i^" : "^(PA.string_of_typ lt)^" = "^(PA.string_of_expr le)^"\n", List.remove_assoc i ls )
            | None -> failwith ("Ale: require value "^i^" undefined in mapping casp") ) )
    | RequireFunc (i, t) -> 
      ( match SM.find_opt i c.defs with 
        | Some (cargs, crt, cexpr) ->
          ( match t with 
            | FunType (ts, rt) -> 
            if List.length cargs == List.length ts then
              let rt_cmp = Type_check.eq_typ (Process.alias_resolve c Pos.none crt) (Process.alias_resolve c Pos.none (convert_type e c rt)) in
              if rt_cmp then (* consistent return type *)
                let args = List.combine cargs ts in 
                let check_arg (res: bool) ((a1: C.arg), (a2: typ)) = 
                  res && Type_check.eq_typ (Process.alias_resolve c Pos.none (snd a1)) (Process.alias_resolve c Pos.none (convert_type e c a2))
                in
                let args_cmp = List.fold_left check_arg true args in
                if args_cmp then (* consistent argument type(s) *)
                  ( {e with func = (SM.add i (cargs, crt, cexpr) (List.hd e.func)) :: List.tl e.func}, str^"def "^i^" "^(PA.string_of_typed_args cargs)^" -> "^(PA.string_of_typ crt)^" = \n"^(PA.string_of_expr cexpr)^"\n", ls )
                else failwith ("Ale: require func "^i^" with unconsistent arg type")
              else failwith ("Ale: require func "^i^" with unconsistent ret type"^(string_of_typ rt))
            else failwith ("Ale: require func "^i^" with different arg length")
            | _ -> failwith ("Ale: require func "^i^" with non-func type") )
        | None -> failwith ("Ale: require func "^i^" undefined in mapping casp") )
  in
  List.fold_left one_require (env, "", lets) rs

let process_provide (c: casp_file) env ps = 
  let one_provide (e, str) p = 
    match p with 
    | ProvideType (i, t) -> 
      let t2c = convert_type e c t in
      ( { e with typ =  (SM.add i t2c (List.hd e.typ)) :: (List.tl e.typ) }, 
        str^ "type  "^i^" = "^ (PA.string_of_typ t2c)^"\n" )
    | ProvideVal (i, t, exp) -> 
      let _ = check_id e i in
      let t2c = convert_type e c t in
      let (_, e2c) = convert_expr e c exp in
      ( { e with value = (SM.add i (e2c, t2c) (List.hd e.value)) :: (List.tl e.value) }, 
        str^ "let "^i^" : "^(PA.string_of_typ t2c)^" = "^ (PA.string_of_expr e2c)^"\n" )
    | ProvideFunc (i, ps, rt, exp) -> 
      let _ = check_id e i in
      let rt2c = convert_type e c rt in
      let env_for_func = env_new_stack e in
      let one_param (pe, args) (v, t) =
        let _ = check_id pe v in
        let t2c = convert_type pe c t in
        ( { pe with arg = (SM.add v t2c (List.hd pe.arg)) :: (List.tl pe.arg) }, 
          args @ [(v, t2c)] )
      in
      let (env_for_func, params) = List.fold_left one_param (env_for_func, []) ps in
      let (_, e2c) = convert_expr env_for_func c exp in
      ( { e with func = (SM.add i (params, rt2c, e2c) (List.hd e.func)) :: (List.tl e.func) }, 
        str^"def "^i^" "^(PA.string_of_typed_args params)^" -> "^(PA.string_of_typ rt2c)^" = \n"^(PA.string_of_expr e2c)^"\n" )
  in
  List.fold_left one_provide (env, "") ps

let process_frame (c: casp_file) env fs ms invs =
  let scratch ms = 
    match ms with 
    | [] -> ""
    | _ -> List.fold_left (fun s i -> s^" "^i) "modify :" ms 
  in
  let one_frame (e, str, inv) f = 
    match f with 
    | FrameLabel _ -> (e, str, inv)
    | FrameRegion _ -> (e, str, inv)
    | FrameAccess ii -> 
      let one_access s i = let _ = valid_id e i in s^" "^i in
      (e, (List.fold_left one_access (str^"access :") ii)^"\n", inv)
    | FrameModify ii -> 
      let one_modify s i = let _ = valid_id e i in s^" "^i in
      (e, (List.fold_left one_modify (str^"modify :") ii)^"\n", inv)
    | FrameInvariant i ->
      let (_, i2c) = convert_expr e c i in
      (e, str, inv @ [i2c])
  in
  List.fold_left one_frame (env, ((scratch ms)^"\n"), invs) fs

let process_blocklet (c: casp_file) env bls = 
  let one_let (e, str) (i, t, exp) = 
    let env_for_let = env_new_stack e in
    let _ = check_id env_for_let i in
    let t2c = convert_type env_for_let c t in
    let (_, e2c) = convert_expr env_for_let c exp in
    ( {e with value = (SM.add i (e2c, t2c) (List.hd e.value)) :: (List.tl e.value)}, 
      str^"let "^i^" : "^(PA.string_of_typ t2c)^" = "^(PA.string_of_expr e2c)^"\n" )
  in
  List.fold_left one_let (env, "") bls

let process_maplet (_c: casp_file) env mls = 
  let one_let (e, str) (i, (t, exp)) = 
    ( {e with value = (SM.add i (exp, t) (List.hd e.value)) :: (List.tl e.value)}, 
      str^"let "^i^" : "^(PA.string_of_typ t)^" = "^(PA.string_of_expr exp)^"\n" )
  in
  List.fold_left one_let (env, "") mls

let process_block (c: casp_file) env modifies (_i, (frames, blocklets, pre, post)) = 
  let env = env_new_stack env in
  let (env, frames, invariants) = process_frame c env frames modifies c.invs in
  let (env, blocklets) = process_blocklet c env blocklets in
  let (_, pre_expr) = convert_expr (env_new_stack env) c pre in
  let (_, post_expr) = convert_expr (env_new_stack env) c post in
  let invariants = List.fold_left (fun s i -> s^" && "^(PA.string_of_expr i)) "" invariants in
  let pre = (PA.string_of_expr pre_expr)^invariants in
  let post = (PA.string_of_expr post_expr)^invariants in
  (blocklets, frames, pre, post)

let process_mapmem (c: casp_file) =
  let find_label m = SM.filter (fun _k v -> v = m) c.lbls in
  let keep_mem k (b, l, r, _) str = 
    let lblmap = find_label k in 
    if SM.is_empty lblmap then 
      str^"letstate "^k^" : "^(string_of_int b)^" bit "^(string_of_int l)^" len "^(string_of_int r)^" ref memory\n"
    else 
      let lblls = SM.bindings lblmap in
      str^"letstate "^k^" : "^(string_of_int b)^" bit "^(string_of_int l)^" len "^(string_of_int r)^" ref memory with "^(fst (List.hd lblls))^"\n"
  in
  SM.fold keep_mem c.mems ""

let process_spec (casp: casp_file) env (rs, ps, bl) lets modifies = 
  let memmaps = process_mapmem casp in
  let (env, requires, lets) = process_require casp env lets rs in
  let (env, lets') = process_maplet casp env lets in
  let (env, provides) = process_provide casp env ps in
  let (blocklets, frames, pre, post) = process_block casp env modifies bl in
  memmaps^"\n"^lets'^"\n"^
  requires^"\n"^
  provides^"\n"^
  blocklets^"\n"^
  "frame: \n"^frames^"\n"^
  "pre: \n"^pre^"\n"^
  "post: \n"^post^"\n"

let process_ale ((rs: require list), (ps: provide list), (bl: block option)) (casp: C.decl list) (mappings: C.submodule list) =
  let (block_name, bl) = match bl with
    | None -> failwith "Ale: no block exist!"
    | Some (i, s) -> (i, (i, s))
  in
  let get_block_module (_pos, module_name, _decls, _modifies) = 
    if module_name = block_name then true else false in
  let mappings = List.filter get_block_module mappings in
  let mappings = 
    ( if mappings == [] then 
        failwith ("Map: block "^block_name^" doesn't exist in mapping file") 
      else List.hd mappings ) 
  in
  let (casp, tenv) = pre_process_casp casp in
  let env = pre_process_ale (rs, ps, bl) in 
  let (casp, tenv, env) = tenv_of_ale casp tenv env in
  (* print_string "Pre-process alewife finished...\n"; *)
  let (casp, lets, modifies) = process_mapping casp tenv mappings in
  (* print_string "Collect mapping finished...\n"; *)
  process_spec casp env (rs, ps, bl) lets modifies
