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
open Pos
open Tsort
open Ale_ast
module C = Casp_ast
module PA = Prettyast

type absdecl = 
	| CaspType of pos * id * C.typ 
	| CaspLet of pos * id * C.typ * C.expr
	| CaspLetstate of pos * id * C.typ * id option
	| CaspDef of pos * id * C.arg list * C.typ * C.expr
	| AleRType of id
	| AleRVal of id * typ
	| AleRFunc of id * typ
	| AlePType of id * typ
	| AlePVal of id * typ * expr
	| AlePFunc of id * param list * typ * expr
	| AleRegion of id * width * width * width * id option
	| AleLet of id * typ * expr

let getwidth (c: casp_file) (w: width) =
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
      match SM.find_opt x c.lets with
      | None -> 99 (* placeholder *)
      | Some (Int k, _t) -> BI.int_of_big_int k
      | Some _ -> failwith ("Invalid type width " ^ x ^ " (preprocess)")

let convert_type (c: casp_file) (t: typ) : C.typ =
  match t with 
  | BoolType -> C.BoolType
  | IntType -> C.IntType
  | LblType w -> C.LabelType (getwidth c w)
  | BitType -> C.BitType 1
  | VecType w -> C.BitType (getwidth c w)
  | PtrType w -> C.BitType (getwidth c w)
  | RegType w -> C.LocType (getwidth c w)
  | AbsType i ->
    ( match SM.find_opt i c.types with
      | Some i -> i
      | None -> failwith ("undeclared abstract type "^i) )
  | _ -> failwith ("function type cannot be converted")

let convert_atomic a =
  match a with
  | Id i -> C.Id i
  | Int i -> C.Int i
  | Bool b -> C.Bool b
  | Vec v -> C.Vec v
  | Ptr (i, o) -> C.Ptr (i, o)

let convert_unop = function
  | Neg -> C.Neg
  | LogNot -> C.LogNot
  | BitNot -> C.BitNot

let convert_binop = function
  | Add -> C.BAdd
  | Sub -> C.BSub
  | Mul -> C.BMul
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

let rec convert_expr (c: casp_file) (ee: expr) : C.expr =
  match ee with 
  | Atomic a -> (Pos.none, C.Atomic (convert_atomic a))
  | Deref e -> (Pos.none, C.Deref (convert_expr c e))
  | Fetch e -> 
     (Pos.none, C.Fetch (convert_expr c e, (Pos.none, C.Atomic (C.Int (BI.of_int c.wordsize)))))
  | Index (e1, e2) -> 
    let i1 = convert_expr c e1 in 
    let i2 = convert_expr c e2 in 
    (Pos.none, C.Index (i1, i2))
  | Slice (e1, e2, e3) -> 
    let i1 = convert_expr c e1 in 
    let i2 = convert_expr c e2 in 
    let i3 = convert_expr c e3 in 
    (Pos.none, C.Slice (i1, i2, i3))
  | LetE (i, t, e1, e2) -> 
    let t = convert_type c t in
    let i1 = convert_expr c e1 in 
    let i2 = convert_expr c e2 in 
    (Pos.none, C.LetE (i, t, i1, i2))
  | IfE (e1, e2, e3) -> 
    let i1 = convert_expr c e1 in 
    let i2 = convert_expr c e2 in 
    let i3 = convert_expr c e3 in 
    (Pos.none, C.IfE (i1, i2, i3))
  | App (i, args) -> 
    let one_arg exprs a = exprs @ [convert_expr c a] in
    let argsls = List.fold_left one_arg [] args in
    (Pos.none, C.App (i, argsls))
  | Implies (e1, e2) -> 
    let i1 = convert_expr c e1 in 
    let i2 = convert_expr c e2 in 
    (Pos.none, C.Binop ((Pos.none, C.Unop (C.LogNot, i1)), C.LogOr, i2))
  | Unop (u, e) ->
    (Pos.none, C.Unop (convert_unop u, convert_expr c e))
  | Binop (e1, b, e2) ->
    let i1 = convert_expr c e1 in 
    let i2 = convert_expr c e2 in 
    (Pos.none, C.Binop (i1, convert_binop b, i2))

let process_casp casp = 
  List.fold_left Process.process_decl (casp_file_empty, Type_check.tenv_empty) casp

let process_ale ((requires: require list), (provides: provide list), ((frames: frame list), (blets: block_let list), (bpre: expr), (bpost: expr))) = 
	let one_require ls r = 
		match r with 
		| RequireType i -> ls @ [AleRType i]
		| RequireVal (i, t) -> ls @ [AleRVal (i, t)]
		| RequireFunc (i, t) -> ls @ [AleRFunc (i, t)]
	in
	let one_provide ls p = 
		match p with 
		| ProvideType (i, t) -> ls @ [AlePType (i, t)]
		| ProvideVal (i, t, e) -> ls @ [AlePVal (i, t, e)]
		| ProvideFunc (i, ps, t, e) -> ls @ [AlePFunc (i, ps, t, e)]
	in
	let one_frame (ls, vs, mrs, mms) f = 
		match f with
		| FrameLabel (i1, b, l, r, i2) -> (ls @ [AleRegion (i1, b, l, r, Some i2)], vs, mrs, mms)
		| FrameRegion (i1, b, l, r) -> (ls @ [AleRegion (i1, b, l, r, None)], vs, mrs, mms)
		| FrameModifyReg ids -> (ls, vs, mrs @ ids, mms)
		| FrameModifyMem ptrs -> (ls, vs, mrs, mms @ ptrs)
		| FrameInvariant e -> (ls, vs @ [e], mrs, mms)
	in 
	let one_blet ls (i, t, e) = ls @ [AleLet (i, t, e)] in
	let decls = List.fold_left one_require [] requires in
	let decls = List.fold_left one_provide decls provides in 
	let (decls, ivs, modregs, modmems) = List.fold_left one_frame (decls, [], [], []) frames in
	(List.fold_left one_blet decls blets, ivs, modregs, modmems, bpre, bpost)

let process_mapping (_pos, _modname, (decls: C.decl list), (modregs: id list), (modmems: (id * int) list)) = 
	let one_decl (ls, ivs) (pos, d) = 
		match d with 
	  | C.DeclType (i, t) -> (ls @ [CaspType (pos, i, t)], ivs)
	  | C.DeclLet (i, t, e) -> (ls @ [CaspLet (pos, i, t, e)], ivs)
	  | C.DeclString _ -> failat pos ("Map: not support DeclString (text)")
	  | C.DeclLetstate (i, t, io) -> (ls @ [CaspLetstate (pos, i, t, io)], ivs)
	  | C.DeclInvariant e -> (ls, ivs @ [e])
	  | C.DeclDef (i, args, t, e) -> (ls @ [CaspDef (pos, i, args, t, e)], ivs)
	  | C.DeclDefs _ -> failat pos ("Map: not support Defs (procedure)")
	  | C.DeclDefop _ -> failat pos ("Map: not support Defop (operation)")
	in
	(List.fold_left one_decl ([], []) decls, modregs, modmems)

let process_all ((requires: require list), (provides: provide list), (blk: block option)) (casp: C.decl list) (mappings: C.submodule list) = 
  (* step 0: process casp and get casp_file *)
  let (casp, tenv) = process_casp casp in

	(* step 1: get the corresponding map module for ale block *)
	let (bn, bspec) = match blk with 
		| None -> failwith "Ale: no block exist!"
		| Some (i, s) -> (i, s)
	in
  let get_block_module (_, mn, _, _, _) = ( mn = bn ) in
  let mappings = List.filter get_block_module mappings in
  let mappings = 
    ( if mappings == [] then failwith ("Map: block "^bn^" doesn't exist in mapping file") 
      else List.hd mappings ) 
  in

  (* step 2: process ale spec, get ale-absdecls*)
  let (aledecls, aleinvs, alemodreg, alemodmem, bpre, bpost) = process_ale (requires, provides, bspec) in
  (* step 3: process mapping, get casp-absdecls, *)
  let ((caspdecls, caspivs), caspmodreg, caspmodmem) = process_mapping mappings in

  (* step 4: merge them in order to tsort it *)
  let absdecls = caspdecls @ aledecls in

  (* step 5: get the defined/declared vars, including funcionid, variableid and memoryid *)
  let get_var (sdef, sdec) decl = 
  	match decl with 
		| CaspType (_, i, _) -> (SS.add i sdef, sdec)
		| CaspLet (_, i, _, _) -> (SS.add i sdef, sdec)
		| CaspLetstate (_, i, _, io) -> 
			begin match io with 
				| None -> (SS.add i sdef, sdec)
				| Some i2 -> (SS.add i2 (SS.add i sdef), sdec)
			end
		| CaspDef (_, i, _, _, _) -> (SS.add i sdef, sdec)
		| AlePType (i, _) -> (SS.add i sdef, sdec)
		| AlePVal (i, _, _) -> (SS.add i sdef, sdec)
		| AlePFunc (i, _, _, _) -> (SS.add i sdef, sdec)
		| AleRegion (i, _, _, _, io) -> 
			begin match io with 
				| None -> (SS.add i sdef, sdec)
				| Some i2 -> (SS.add i2 (SS.add i sdef), sdec)
			end
		| AleLet (i, _, _) -> (SS.add i sdef, sdec)

		| AleRType i -> (sdef, SS.add i sdec)
		| AleRVal (i, _) -> (sdef, SS.add i sdec)
		| AleRFunc (i, _) -> (sdef, SS.add i sdec)
  in   	
  let (defined_vars, declared_vars) = List.fold_left get_var (SS.empty, SS.empty) absdecls in

  (* step 6: diff two sets -> IDs defined in caspmach, will be ignored *)
  let existed = SS.union declared_vars defined_vars in
  let ignored = SS.diff declared_vars defined_vars in
  (* print_string (String.concat " " (SS.elements existed)); *)
  let existed_vars = ref [existed; existed] in 
  let ignored_vars = ref [ignored; ignored] in
  (* step 6.1: helper function for add/remove stacks *)
	let addone_new_stack i = 
		let existed_top = List.hd !existed_vars in
		let existed_top = SS.add i existed_top in 
		let ignored_top = List.hd !ignored_vars in
		let ignored_top = SS.add i ignored_top in 
		existed_vars := List.cons existed_top (!existed_vars);
		ignored_vars := List.cons ignored_top (!ignored_vars)
	in
	let addlist_new_stack ils = 
		let existed_top = List.hd !existed_vars in 
		let existed_top = 
			List.fold_left (fun s i -> SS.add i s) existed_top ils
		in
		let ignored_top = List.hd !ignored_vars in
		let ignored_top = 
			List.fold_left (fun s i -> SS.add i s) ignored_top ils
		in
		existed_vars := List.cons existed_top (!existed_vars);
		ignored_vars := List.cons ignored_top (!ignored_vars)
	in
	let remove_new_stack () = 
		existed_vars := List.tl !existed_vars;
		ignored_vars := List.tl !ignored_vars		
	in

  (* step 7: get memory-label pair *)
  let l2m_pair sm decl = 
  	match decl with 
		| CaspLetstate (_, i1, _, Some i2) -> SM.add i2 i1 sm
		| AleRegion (i1, _, _, _, Some i2) -> SM.add i2 i1 sm
		| _ -> sm
  in   	
  let l2m = List.fold_left l2m_pair SM.empty absdecls in 

  (* step 9: function to get key string for tsort *)
  let get_key decl = 
  	match decl with 
		| CaspType (_, i, _) -> i
		| CaspLet (_, i, _, _) -> i
		| CaspLetstate (_, i, _, _) -> i
		| CaspDef (_, i, _, _, _) -> i
		| AleRType i -> "r."^i
		| AleRVal (i, _) -> "r."^i
		| AleRFunc (i, _) -> "r."^i
		| AlePType (i, _) -> i
		| AlePVal (i, _, _) -> i
		| AlePFunc (i, _, _, _) -> i
		| AleRegion (i, _, _, _, _) -> i
		| AleLet (i, _, _) -> i
  in 

  (* step 10: function to get dependence string list for tsort *)
  let get_deps decl = 
  	let check_exist_ignore ls i = 
			match (SS.find_opt i (List.hd !existed_vars), SS.find_opt i (List.hd (List.tl !existed_vars))) with 
				| (Some _, Some _) -> (* defined in mapping file or ale spec *)
					begin match SS.find_opt i (List.hd !ignored_vars) with
					| Some _ -> ls (* defined in caspmach *)
					| None -> 
						begin match SM.find_opt i l2m with 
	  					| Some i2 -> ls @ [i2]
	  					| None -> ls @ [i]
	  				end
	  			end
				| (Some _, None) -> ls (* new stack variable *)
				| (None, _) -> ls (* not defined in map/ale, defined in caspmach, ignore it for now and check it later! *)
  	in
  	let check_awidth ls w = 
			match w with 
				| SymWidth i -> check_exist_ignore ls i
				| ConcWidth _ -> ls
		in
  	let get_deps_ctyp ls t = 
  		match t with 
  		| C.AliasType i -> check_exist_ignore ls i
  		| C.AliasLocType i -> check_exist_ignore ls i
  		| _ -> ls
  	in
  	let rec get_deps_atyp ls t = 
			match t with 
			| AbsType i -> check_exist_ignore ls i
			| LblType w | VecType w | PtrType w | RegType w -> check_awidth ls w
			| FunType (ts, t) -> get_deps_atyp (List.fold_left get_deps_atyp ls ts) t
			| _ -> ls
		in
  	let rec get_deps_cexpr ls (_pos, top_e) =
  		match top_e with 
  		| C.Atomic a -> 
  			begin match a with 
  				| C.Id i | C.Ptr (i, _) -> check_exist_ignore ls i
  				| _ -> ls
  			end
  		| C.Deref e -> get_deps_cexpr ls e
  		| C.Fetch (e1, e2) -> get_deps_cexpr (get_deps_cexpr ls e1) e2
  		| C.Index (e1, e2) -> get_deps_cexpr (get_deps_cexpr ls e1) e2
  		| C.Slice (e1, e2, e3) -> get_deps_cexpr (get_deps_cexpr (get_deps_cexpr ls e1) e2) e3
  		| C.Unop (_, e) ->  get_deps_cexpr ls e
  		| C.Binop (e1, _, e2) ->  get_deps_cexpr (get_deps_cexpr ls e1) e2
  		| C.App (i, es) -> List.fold_left get_deps_cexpr (check_exist_ignore ls i) es
  		| C.LetE (i, t, e1, e2) -> 
  				let ls1 = get_deps_cexpr (get_deps_ctyp ls t) e1 in 
  				(* update vars with new stack to ignore i for e2 *)
  				let _ = addone_new_stack i in 
  				let ls2 = get_deps_cexpr ls1 e2 in 
  				(* remove the new stack *)
  				let _ = remove_new_stack () in
  				ls2
  		| C.IfE (e1, e2, e3) -> get_deps_cexpr (get_deps_cexpr (get_deps_cexpr ls e1) e2) e3
  	in
  	let rec get_deps_aexpr ls top_e = 
  		match top_e with 
  		| Atomic a ->
  			begin match a with 
  				| Id i | Ptr (i, _) -> check_exist_ignore ls i
  				| _ -> ls
  			end
  		| Deref e -> get_deps_aexpr ls e
  		| Fetch e -> get_deps_aexpr ls e
  		| Index (e1, e2) -> get_deps_aexpr (get_deps_aexpr ls e1) e2
  		| Slice (e1, e2, e3) -> get_deps_aexpr (get_deps_aexpr (get_deps_aexpr ls e1) e2) e3
  		| Implies (e1, e2) -> get_deps_aexpr (get_deps_aexpr ls e1) e2
  		| Unop (_, e) -> get_deps_aexpr ls e
  		| Binop (e1, _, e2) -> get_deps_aexpr (get_deps_aexpr ls e1) e2
  		| App (i, es) -> List.fold_left get_deps_aexpr (check_exist_ignore ls i) es
  		| LetE (i, t, e1, e2) -> 
  				let ls1 = get_deps_aexpr (get_deps_atyp ls t) e1 in 
  				(* update vars with new stack to ignore i for e2 *)
  				let _ = addone_new_stack i in 
  				let ls2 = get_deps_aexpr ls1 e2 in 
  				(* remove the new stack *)
  				let _ = remove_new_stack () in
  				ls2
  		| IfE (e1, e2, e3) -> get_deps_aexpr (get_deps_aexpr (get_deps_aexpr ls e1) e2) e3
  	in
  	match decl with 
		| CaspType (_, _, t) -> get_deps_ctyp [] t
		| CaspLet (_, _, t, e) ->  get_deps_cexpr (get_deps_ctyp [] t) e
		| CaspLetstate (_, _, t, _) -> get_deps_ctyp [] t
		| CaspDef (_, _, args, t, e) -> 
			let argids = List.map (fun (i, _t) -> i) args in 
			let argtyps = List.map (fun (_i, t) -> t) args in 
			let ls1 = List.fold_left get_deps_ctyp [] argtyps in
			let ls2 = get_deps_ctyp ls1 t in 
			let _ = addlist_new_stack argids in
			let ls3 = get_deps_cexpr ls2 e in 
			let _ = remove_new_stack () in 
			ls3
		| AleRType i -> check_exist_ignore [] i
		| AleRVal (_, t) -> get_deps_atyp [] t
		| AleRFunc (_, t) -> get_deps_atyp [] t
		| AlePType (_, t) -> get_deps_atyp [] t
		| AlePVal (_, t, e) -> get_deps_aexpr (get_deps_atyp [] t) e
		| AlePFunc (_, params, t, e) -> 
			let argids = List.map (fun (i, _t) -> i) params in 
			let argtyps = List.map (fun (_i, t) -> t) params in 
			let ls1 = List.fold_left get_deps_atyp [] argtyps in
			let ls2 = get_deps_atyp ls1 t in 
			let _ = addlist_new_stack argids in
			let ls3 = get_deps_aexpr ls2 e in 
			let _ = remove_new_stack () in 
			ls3
		| AleRegion (_, wb, wl, wr, _) -> check_awidth (check_awidth (check_awidth [] wb) wl) wr
		| AleLet (_, t, e) -> get_deps_aexpr (get_deps_atyp [] t) e
	in 

	(* step 11: tsort!!! *)
	let sorted_decls = tsort get_key get_deps absdecls in

	(* step 13: output them as ordered spec *)
	let print_decls (casp, tenv, str) decl = 
		match decl with 
		| CaspType (pos, i, t) -> 
			let (casp, tenv) = Process.process_type casp tenv pos i t in
			(casp, tenv, str^"type "^i^" = "^(PA.string_of_typ t)^"\n")
		| CaspLet (pos, i, t, e) -> 
			let (casp, tenv) = Process.process_speclet casp tenv pos i t e in
			let casp = begin match e with 
					| (_, (C.Atomic (C.Int ai))) -> { casp with lets = SM.add i (C.Int ai, t) casp.lets }
					| _ -> casp
				end
			in
			(casp, tenv, str^"let "^i^" : "^(PA.string_of_typ t)^" = "^(PA.string_of_expr e)^"\n")
		| CaspLetstate (pos, i1, t, io) -> 
			let (casp, tenv) = Process.process_letstate casp tenv pos i1 t io in 
			begin match io with 
				| Some i2 -> 
					(casp, tenv, str^"letstate "^i1^" : "^(PA.string_of_typ t)^" memory with "^i2^"\n")
				| None -> 
					(casp, tenv, str^"letstate "^i1^" : "^(PA.string_of_typ t)^" memory\n")
			end
		| CaspDef (pos, i, xs, t, e) -> 
			let (casp, tenv) = Process.process_def casp tenv pos i xs t e in
			(casp, tenv, str^"def "^i^" "^(PA.string_of_typed_args xs)^" -> "^(PA.string_of_typ t)^" = \n"^(PA.string_of_expr e)^"\n")
		| AleRType _ | AleRVal (_, _) | AleRFunc (_, _) -> (casp, tenv, str) (* ignore requires *)
		| AlePType (i, t) -> 
			let t = convert_type casp t in
			let casp = { casp with types = SM.add i t casp.types } in
			(casp, tenv, str^"type "^i^" = "^(PA.string_of_typ t)^"\n")
		| AlePVal (i, t, e) -> 
			let t = convert_type casp t in 
			let e = convert_expr casp e in
			let tenv = SM.add i (Type_check.lift t) tenv in 
			(casp, tenv, str^"let "^i^" : "^(PA.string_of_typ t)^" = "^(PA.string_of_expr e)^"\n")
		| AlePFunc (i, ps, t, e) -> 
			let t = convert_type casp t in 
			let e = convert_expr casp e in 
      let one_param args (v, t) = args @ [(v, (convert_type casp t))] in
      let params = List.fold_left one_param [] ps in
		  (casp, tenv, str^"def "^i^" "^(PA.string_of_typed_args params)^" -> "^(PA.string_of_typ t)^" = \n"^(PA.string_of_expr e)^"\n")
		| AleRegion (i, b, l, r, io) ->
			let b = getwidth casp b in 
			let l = getwidth casp l in 
			let r = getwidth casp r in 
			begin match io with 
				| Some i2 -> 
					let casp = { casp with mems = SM.add i (b, l, r, Some i2) casp.mems; lbls = SM.add i2 i casp.lbls } in 
					(casp, tenv, str^"letstate "^i^" : "^(string_of_int b)^" bit "^(string_of_int l)^" len "^(string_of_int r)^" ref memory with "^i2^"\n")
				| None -> 
					let casp = { casp with mems = SM.add i (b, l, r, None) casp.mems} in 
					(casp, tenv, str^"letstate "^i^" : "^(string_of_int b)^" bit "^(string_of_int l)^" len "^(string_of_int r)^" ref memory\n")
			end
		| AleLet (i, t, e) ->
			let t = convert_type casp t in
			let e = convert_expr casp e in
			let tenv = SM.add i (Type_check.lift t) tenv in 
			(casp, tenv, str^"let "^i^" : "^(PA.string_of_typ t)^" = "^(PA.string_of_expr e)^"\n")
	in
	(* decls string *)
	let (casp, _tenv, decls_str) = List.fold_left print_decls (casp, tenv, "") sorted_decls in

	(* modify string *)
	let modifyreg_str = 
		if (alemodreg @ caspmodreg) == [] then "" 
		else List.fold_left (fun s i -> s^" "^i) "reg-modify : " (alemodreg @ caspmodreg)
	in
	let alemodmem = List.map (fun (i, o) -> (i, getwidth casp o)) alemodmem in
	let modifymem_str = 
		if (alemodmem @ caspmodmem) == [] then "" 
		else List.fold_left (fun s i -> s^" "^(string_of_consptr i)) "mem-modify : " (alemodmem @ caspmodmem)
	in

	(* pre/post string *)
	let ale_invariants_str = List.fold_left (fun s i -> s^" && "^(PA.string_of_expr (convert_expr casp i))) "" aleinvs in
  let casp_invariants_str = List.fold_left (fun s i -> s^" && "^(PA.string_of_expr i)) "" (caspivs @ casp.invs) in
	let pre_str = "( "^(PA.string_of_expr (convert_expr casp bpre))^" ) "^casp_invariants_str^ale_invariants_str in 
  let post_str = "( "^(PA.string_of_expr (convert_expr casp bpost))^" )"^casp_invariants_str^ale_invariants_str in

  decls_str^"\nframe:\n"^modifyreg_str^"\n"^modifymem_str^"\n\npre:\n"^pre_str^"\npost:\n"^post_str
