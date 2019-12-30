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
open Interpret

module PA = Prettyast

open Type_check

let print_verbose: (string -> unit) ref = ref (fun _s -> ())
let print_dump: (string -> unit) ref = ref (fun _s -> ())

let alias_resolve c pos t =
  match t with
  | IntType
  | BoolType
  | StringType -> t
  | LocType l
  | BitType l
  | LabelType l ->
    if l = 0 then
      failat pos "encountered 0 bit: 0 bit is forbidden!"
    else
      t
  | MemType (l, _, r) ->
    if l = 0 then
      failat pos "encountered 0 bit: 0 bit is forbidden!"
    else if r = 0 then
      failat pos "encountered 0 bit: 0 bit is forbidden!"
    else
      t
  | AliasType i ->
    begin match SM.find_opt i c.types with
    | Some t -> t
    | None -> failat pos ("unknown type alias "^i)
    end
  | AliasLocType i ->
    begin match SM.find_opt i c.types with
    | Some (BitType l) -> LocType l
    | Some t ->
      failat pos ("location type alias expected bitvector but "^
                  "type alias "^i^" is of type "^(PA.string_of_typ t))
    | None ->
      failat pos ("unknown type alias "^i)
    end

let rec alias_resolve_expr c (pos, e) =
  let e = match e with
    | Atomic _ -> e
    | Deref e ->
      Deref (alias_resolve_expr c e)
    | Fetch (e1, e2) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      Fetch (e1, e2)
    | Index (e1, e2) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      Index (e1, e2)
    | Slice (e1, e2, e3) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      let e3 = alias_resolve_expr c e3 in
      Slice (e1, e2, e3)
    | Unop (u, e) ->
      Unop (u, alias_resolve_expr c e)
    | Binop (e1, b, e2) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      Binop (e1, b, e2)
    | App (i, ee) ->
      let ee = List.map (alias_resolve_expr c) ee in
      App (i, ee)
    | LetE (i, t, e1, e2) ->
      let t = alias_resolve c pos t in
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      LetE (i, t, e1, e2)
    | IfE (e1, e2, e3) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      let e3 = alias_resolve_expr c e3 in
      IfE (e1, e2, e3)
  in
  (pos, e)

let rec alias_resolve_stmt c (pos, s) =
  let s = match s with
    | Skip -> Skip
    | Err -> Err
    | Assert (e, s) ->
      Assert (alias_resolve_expr c e, s)
    | Seq (s1, s2) ->
      let s1 = alias_resolve_stmt c s1 in
      let s2 = alias_resolve_stmt c s2 in
      Seq (s1, s2)
    | Store (e1, e2, e) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      let e = alias_resolve_expr c e in
      Store (e1, e2, e)
    | Assign (e1, e2) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      Assign (e1, e2)
    | For (i, e1, e2, s) ->
      let e1 = alias_resolve_expr c e1 in
      let e2 = alias_resolve_expr c e2 in
      let s = alias_resolve_stmt c s in
      For (i, e1, e2, s)
    | Call (i, ee) ->
      let ee = List.map (alias_resolve_expr c) ee in
      Call (i, ee)
    | LetS (i, t, e, s) ->
      let t = alias_resolve c pos t in
      let e = alias_resolve_expr c e in
      let s = alias_resolve_stmt c s in
      LetS (i, t, e, s)
    | IfS (e, s1, s2) ->
      let e = alias_resolve_expr c e in
      let s1 = alias_resolve_stmt c s1 in
      let s2 = alias_resolve_stmt c s2 in
      IfS (e, s1, s2)
  in
  (pos, s)

let builtin_ids =
  (SM.bindings tenv_empty |> List.map fst) @
  ["format"; "dec"; "hex"; "bin"]

let check_id (c: casp_file) pos i =
  if SM.mem i c.lets then
    failat pos ("id "^i^" is already bound to a value")
  else if SM.mem i c.regs then
    failat pos ("id "^i^" is already bound to a register")
  else if SM.mem i c.mems then
    failat pos ("id "^i^" is already bound to a memory region")
  else if SM.mem i c.defs then
    failat pos ("id "^i^" is already bound to a function")
  else if SM.mem i c.defss then
    failat pos ("id "^i^" is already bound to a subroutine")
  else if SM.mem i c.defops then
    failat pos ("id "^i^" is already bound to an operation")
  else if List.mem i builtin_ids then
    failat pos ("id "^i^" conflicts with a built-in")
  else ()

(* resolve a new type alias to a concrete type
   and store in type alias mapping *)
let process_type c tenv pos i t =
  let t = alias_resolve c pos t in
  (* get the word size and keep it in casp struct *)
  if i = "word" then
    match t with
    | BitType l ->
      ({ c with types = SM.add i t c.types; wordsize = l }, tenv)
    | _ -> failwith "type word should be defined as an n bit"
  else
    ({ c with types = SM.add i t c.types }, tenv)

let resolve_let _ c e =
  (* evaluate let expression in current environment *)
  (* registers and memory omitted: desc let bindings should not reference *)
  let conf = CE.eval_config c in
  let conf =
    { conf with
      reg = SM.empty;
      mem = SM.empty; }
  in
  match CE.eval_expr e conf with
  | Ok (v, _) ->
    (* then down-convert to atomic *)
    let res =
      match v with
      | ValInt d -> Int (CV.lower_int d)
      | ValWord (b, _) ->
        begin match CV.lower_word b with
        | BitVec h ->
          Vec (CV.lower_vec h)
        | BitPtr p ->
          let (i, o) = CV.lower_ptr p in
          Ptr (i, Bits.to_big_int o)
        end
      | ValBool b -> Bool (CV.lower_bool b)
      | ValLoc (i, _) -> Id (CV.lower_loc i)
      | ValStr s -> Str s
    in
    Some res
  | Error _ -> None

(* resolve let against current environment
   and store final value in let mapping;
   update type environment to contain new value *)
let process_let c tenv pos i t e =
  let _ = check_id c pos i in
  let t = alias_resolve c pos t in
  let e = alias_resolve_expr c e in
  let t' = Type_check.type_check_let tenv pos t e in
  let v = resolve_let pos c e in
  match v with
  | Some v ->
    ({ c with lets = SM.add i (v, t) c.lets }, SM.add i t' tenv)
  | None ->
    (c, SM.add i t' tenv)

(* add a register/memory region to the machine description *)
let process_letstate c tenv pos i t lbl =
  let _ = check_id c pos i in
  let t = alias_resolve c pos t in
  let t' = Type_check.type_check_letstate tenv pos t in
  match t with
  | LocType l ->
    ({ c with regs = SM.add i l c.regs }, SM.add i t' tenv)
  | MemType (l, n, r) ->
    let tenv = SM.add i t' tenv in
    let c = { c with mems = SM.add i (l, n, r, lbl) c.mems } in
    begin match lbl with
    | Some lbl ->
      let t' = Type_check.lift (BitType r) in
      ({ c with lbls = SM.add lbl i c.lbls }, SM.add lbl t' tenv)
    | None -> (c, tenv)
    end
  | _ -> failat pos "BUG: non-state type found after letstate type checking!"

let process_invariant c tenv pos e =
  let e = alias_resolve_expr c e in
  let _ = Type_check.type_check_invariant tenv pos e in
  ({ c with invs = c.invs @ [e] }, tenv)

let process_def c tenv pos i aa t e =
  let _ = check_id c pos i in
  let aa = List.map (fun (i, t) -> (i, alias_resolve c pos t)) aa in
  let t = alias_resolve c pos t in
  let e = alias_resolve_expr c e in
  let t' = Type_check.type_check_def tenv pos aa t e in
  ({ c with defs = SM.add i (aa, t, e) c.defs }, SM.add i t' tenv)

let process_defs c tenv pos i aa s =
  let _ = check_id c pos i in
  let aa = List.map (fun (i, t) -> (i, alias_resolve c pos t)) aa in
  let s = alias_resolve_stmt c s in
  let t' = Type_check.type_check_defs tenv pos aa s in
  ({ c with defss = SM.add i (aa, s) c.defss }, SM.add i t' tenv)

let process_defop c tenv pos i aa se ot s =
  let _ = check_id c pos i in
  let aa = List.map (fun (i, t) -> (i, alias_resolve c pos t)) aa in
  let s = alias_resolve_stmt c s in
  let _ = Type_check.type_check_defop tenv pos aa s in
  let add tenv (i, t) = SM.add i (lift t) tenv in
  let tenv' = List.fold_left add tenv aa in
  let se = alias_resolve_expr c se in
  let _ = Type_check.type_check_expr tenv' se in
  let (opi, ops) =
    match ot with
    | Typed (ott, ost) ->
      begin match SM.find_opt ott c.opcategory with
      | Some opsm ->
        let new_opss = begin match SM.find_opt ost opsm with
          | Some opss -> SS.add i opss
          | None -> SS.singleton i
          end
        in
        (ott, SM.add ost new_opss opsm)
      | None ->
        (ott, SM.add ost (SS.singleton i) SM.empty)
      end
    | NoTyped ->
      let s = "NoTyped" in
      begin match SM.find_opt s c.opcategory with
      | Some opsm ->
        let new_opss = begin match SM.find_opt s opsm with
          | Some opss -> SS.add i opss
          | None -> SS.singleton i
          end
        in
        (s, SM.add s new_opss opsm)
      | None ->
        (s, SM.add s (SS.singleton i) SM.empty)
      end
  in
  ({ c with
    defops = SM.add i (aa, s) c.defops;
    defstr = SM.add i (aa, se) c.defstr;
    opcategory = SM.add opi ops c.opcategory}, tenv)

let process_string c tenv pos i s =
  if SM.mem i c.regs then
    ({ c with txts = SM.add i s c.txts }, tenv)
  else
    failat pos ("id "^i^" doesn't exist as a register")

let process_decl (c, tenv) (pos, decl) =
  (*let _ =
    (!print_verbose) (P.sprintf "process_decl: %s\n" (PA.string_of_decl decl))
  in*)
  match decl with
  | DeclType (i, t) -> process_type c tenv pos i t
  | DeclLet (i, t, e) -> process_let c tenv pos i t e
  | DeclString (i, s) -> process_string c tenv pos i s
  | DeclLetstate (i1, t, i2) -> process_letstate c tenv pos i1 t i2
  | DeclInvariant e -> process_invariant c tenv pos e
  | DeclDef (i, aa, t, e) -> process_def c tenv pos i aa t e
  | DeclDefs (i, aa, s) -> process_defs c tenv pos i aa s
  | DeclDefop (i, aa, se, ot, s) -> process_defop c tenv pos i aa se ot s

(* incrementally build cassiopeia program definition *)
let process_casp (decls : decl list) =
  fst (List.fold_left process_decl (casp_file_empty, Type_check.tenv_empty) decls)

(* get top-level typing environment *)
let tenv_of_casp (c : casp_file) =
  let add_let i (a, t) =
    let t = match a with
      | Int i -> IntTerm i
      | _ -> Type_check.lift t
    in
    SM.add i t
  in
  let add_reg i t =
    SM.add i (Type_check.lift (LocType t))
  in
  let add_mem i (b, l, r, _) =
    SM.add i (Type_check.lift (MemType (b, l, r)))
  in
  let add_lbl i m =
    match SM.find_opt m c.mems with
    | Some (_, _, r, _) -> SM.add i (Type_check.lift (LabelType r))
    | None -> failwith ("label "^i^" not bound to any memory region!")
  in
  tenv_empty
  |> SM.fold add_let c.lets
  |> SM.fold add_reg c.regs
  |> SM.fold add_mem c.mems
  |> SM.fold add_lbl c.lbls

let process_prog (c : casp_file) ((e, p) : extern list * casp_inst list) =
  (* construct environment for inst arg evaluation *)
  let tenv = tenv_of_casp c in
  (* evaluate extern labels *)
  let _ = List.iter
          (fun (pos, v) ->
            if (SM.mem v c.lbls) then ()
            else failat pos ("prog requires extern label "^v^" but not defined")) e
  in
  let type_check_arg op ((pos, a), t) =
    let t' = (pos, a)
      |> Type_check.type_check_atomic tenv
      |> Type_check.lower
    in
    (* strict type equality: labels aren't bits *)
    match (t', t) with
    | (_, AliasType i)
    | (_, AliasLocType i) ->
      failat pos ("BUG! preprocessing: alias type "^i^" "^
                  "should have been resolved by now")
    | (IntType, IntType) -> ()
    | (BitType l, BitType l') ->
      if l <> l' then
        failat pos ("bad type in argument to op "^op^": got "^
                    (string_of_int l)^" bit, expected "^
                    (string_of_int l')^" bit")
      else ()
    | (BoolType, BoolType) -> ()
    | (LocType l, LocType l') ->
      if l <> l' then
        failat pos ("bad type in argument to op "^op^": got "^
                    (string_of_int l)^" bit loc, expected "^
                    (string_of_int l')^" bit loc")
      else ()
    | (LabelType l, LabelType l') ->
      if l <> l' then
        failat pos ("bad type in argument to op "^op^": got "^
                    (string_of_int l)^" bit label, expected "^
                    (string_of_int l')^" bit label")
      else ()
    | _ ->
      failat pos ("bad type in argument to op "^op^": got "^
                  (PA.string_of_typ t')^", expected type "^
                  (PA.string_of_typ t))
  in
  (* check argument types in an instruction *)
  let type_check_inst (pos, (i, aa)) =
    match SM.find_opt i c.defops with
    | Some (aa', _s) ->
      (try
        (* cut out arg types for defop *)
        List.map snd aa'
        |> List.combine aa
        |> List.iter (type_check_arg i);
        (pos, (i, aa))
      with Invalid_argument _ ->
        (* List.combine throws, given differing list lengths *)
        failat pos ("wrong number of arguments to op "^i^": got "^
                    (string_of_int (List.length aa))^"args , expected "^
                    (string_of_int (List.length aa'))))
    | None ->
      failat pos ("unknown op "^i)
  in
  (* now checking each instruction *)
  List.map type_check_inst p

let process_sketch (c : casp_file) (s : sketch_inst list) =
  (* construct environment for inst arg evaluation *)
  let tenv = tenv_of_casp c in
  let type_check_arg op ((pos, a), t) =
    match a with
    | SketchArgPlaceHolder -> ()
    | SketchArg a ->
      let t' = (pos, a)
              |> Type_check.type_check_atomic tenv
              |> Type_check.lower
      in
      (* strict type equality: labels aren't bits *)
      match (t', t) with
      | (_, AliasType i)
      | (_, AliasLocType i) ->
        failat pos ("BUG! preprocessing: alias type "^i^" "^
                    "should have been resolved by now")
      | (IntType, IntType) -> ()
      | (BitType l, BitType l') ->
        if l <> l' then
          failat pos ("bad type in argument to op "^op^": got "^
                      (string_of_int l)^" bit, expected "^
                      (string_of_int l')^" bit")
        else ()
      | (BoolType, BoolType) -> ()
      | (LocType l, LocType l') ->
        if l <> l' then
          failat pos ("bad type in argument to op "^op^": got "^
                      (string_of_int l)^" bit loc, expected "^
                      (string_of_int l')^" bit loc")
        else ()
      | (LabelType l, LabelType l') ->
        if l <> l' then
          failat pos ("bad type in argument to op "^op^": got "^
                      (string_of_int l)^" bit label, expected "^
                      (string_of_int l')^" bit label")
        else ()
      | _ ->
        failat pos ("bad type in argument to op "^op^": got "^
                    (PA.string_of_typ t')^", expected type "^
                    (PA.string_of_typ t))
  in
  (* check argument types in an instruction *)
  let type_check_inst (pos, si) =
    match si with
    | SketchInst (i, aa) ->
      begin match SM.find_opt i c.defops with
      | Some (aa', _s) ->
        (try
          (* cut out arg types for defop *)
          List.map snd aa'
          |> List.combine aa
          |> List.iter (type_check_arg i);
          (pos, SketchInst (i, aa))
        with Invalid_argument _ ->
          (* List.combine throws, given differing list lengths *)
          failat pos ("wrong number of arguments to op "^i^": got "^
                      (string_of_int (List.length aa))^"args , expected "^
                      (string_of_int (List.length aa'))))
      | None ->
        failat pos ("unknown op "^i)
      end
    | SketchInstPlaceHolder -> (pos, SketchInstPlaceHolder)
  in
  (* now checking each instruction *)
  List.map type_check_inst s

let process_init (casp: casp_file) (sls : startstate list) =
  let type_check_value pos c l v =
    match v with
    | Vec b ->
      let w = Bits.width b in
      if w <> l then
        failat pos ("process_init: bad type in init: got "^(string_of_int w)^
                    " bit vec, expected "^(string_of_int l)^" bit vec/ptr")
      else v
    | Ptr (i, o) ->
      begin match SM.find_opt i c.mems with
      | Some (_, w, r, _) ->
        if r <> l then
          failat pos ("process_init: bad type in init: got "^(string_of_int r)^
                      " bit ptr, expected "^(string_of_int l)^" bit vec/ptr")
        else if BI.int_of_big_int o >= w then
          failat pos ("process_init: invalid mem offset, got offset "^
                      (BI.string_of_big_int o)^", but region "^i^
                      " has length "^(string_of_int w))
        else v
      | None -> failat pos ("process_init: unknown mem region "^i)
      end
    | _ -> failat pos ("process_init: bad type to init: "^(PA.string_of_atomic v))
  in
  (* check each atomic assignment *)
  let type_check_init (c, ls) (pos, s) =
    match s with
    | StartAssign (a, v) ->
      begin match a with
      | Id i ->
        begin match SM.find_opt i c.regs with
        | Some l -> (c, ls @ [(a, type_check_value pos c l v)])
        | None -> failat pos ("process_init: unknown reg "^i)
        end
      | Ptr (i, o) ->
        begin match SM.find_opt i c.mems with
        | Some (_, l, r, _) ->
          if BI.int_of_big_int o < l then
            (c, ls @ [(a, type_check_value pos c r v)])
          else
            failat pos ("process_init: invalid mem offset, got offset"^
                        (BI.string_of_big_int o)^
                        ", but region "^i^" has length "^(string_of_int l))
        | None ->
          failat pos ("process_init: unknown mem "^i)
        end
      | _ ->
        failat pos ("process_init: start state may only contain "^
                    "register or memory pointer; invalid "^
                    (PA.string_of_atomic a))
      end
    | StartMem (i1, b, l, r, i2) ->
      let c = { c with mems = SM.add i1 (b, l, r, i2) c.mems } in
      begin match i2 with
      | Some i2 -> ({ c with lbls = SM.add i2 i1 c.lbls }, ls)
      | None -> (c, ls)
      end
  in
  List.fold_left type_check_init (casp, []) sls

let process_speclet c tenv pos i t e =
  let _ = check_id c pos i in
  let t = alias_resolve c pos t in
  let e = alias_resolve_expr c e in
  let t' = Type_check.type_check_let tenv pos t e in
  (c, SM.add i t' tenv)

let process_specdecl ((c, tenv), lets) (pos, decl) =
  match decl with
  | DeclType (i, t) ->
    (process_type c tenv pos i t, lets)
  | DeclLet (i, t, e) ->
    (process_speclet c tenv pos i t e, lets @ [(i, t, e)])
  | DeclString (i, s) ->
    (process_string c tenv pos i s, lets)
  | DeclLetstate (i1, t, i2) ->
    (process_letstate c tenv pos i1 t i2, lets)
  | DeclInvariant e ->
    (process_invariant c tenv pos e, lets)
  | DeclDef (i, aa, t, e) ->
    (process_def c tenv pos i aa t e, lets)
  | DeclDefs (i, aa, s) ->
    (process_defs c tenv pos i aa s, lets)
  | DeclDefop (i, aa, se, ot, s) ->
    (process_defop c tenv pos i aa se ot s, lets)

let process_spec (c : casp_file) (s : spec) =
  let process_frame (modifyreg, modifymem) (_, frame) =
    match frame with
    | FrameModifyReg regs -> (SS.union modifyreg (SS.of_list regs), modifymem)
    | FrameModifyMem ptrs ->
      let updated_modifymem = List.fold_left
            (fun ls (i, o) -> ls @ [(i, o)] ) modifymem ptrs
      in
      (modifyreg, updated_modifymem)
  in
  let tenv = tenv_of_casp c in
  let (decls, frames, pre, post) = s in
  let ((c, _), lets) =
    List.fold_left process_specdecl ((c, tenv), []) decls
  in
  let (modifyreg, modifymem) =
    List.fold_left process_frame (SS.empty, []) frames
  in
  let spec =
    { modifyreg = modifyreg;
      modifymem = modifymem;
      lets = lets;
      precond = pre;
      postcond = post; }
  in
  (c, spec)
