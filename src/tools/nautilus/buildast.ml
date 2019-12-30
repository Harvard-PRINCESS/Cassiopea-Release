(*
 * Copyright (c) 2018
 *	The President and Fellows of Harvard College.
 *
 * Written by David A. Holland.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE UNIVERSITY OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *)

open Ptree
module T = Ast

type ctx = {
   tagdecl_accum: (Pos.pos * T.typedecl) Types.StringMap.t ref;
   typedef_accum: (Pos.pos * T.typename) Types.StringMap.t ref;
   funcdecl_accum: (Pos.pos * T.typename) Types.StringMap.t ref;
   gencall_accum: (Pos.pos * string) list ref;
   nextid: int ref;
}

let newctx () = {
   tagdecl_accum = ref Types.StringMap.empty;
   typedef_accum = ref Types.StringMap.empty;
   funcdecl_accum = ref Types.StringMap.empty;
   gencall_accum = ref [];
   nextid = ref 0;
}

let ctx_addcall ctx pos name =
   ctx.gencall_accum := (pos, name) :: !(ctx.gencall_accum)

let ctx_addtag ctx pos name ty =
   ctx.tagdecl_accum :=
     Types.StringMap.add name (pos, ty) !(ctx.tagdecl_accum)

let ctx_addtype ctx pos name ty =
   ctx.typedef_accum :=
     Types.StringMap.add name (pos, ty) !(ctx.typedef_accum)

let ctx_addfunc ctx pos name ty =
   ctx.funcdecl_accum :=
     Types.StringMap.add name (pos, ty) !(ctx.funcdecl_accum)

let ctx_maketag ctx =
   let id = !(ctx.nextid) in
   ctx.nextid := id + 1;
   ".T" ^ string_of_int id


(**************************************************************)
(* parsetree tools *)

(*
 * storage classes
 *)

let string_of_sc sc =
   match sc with
        AUTO -> "auto"
      | EXTERN -> "extern"
      | REGISTER -> "register"
      | STATIC -> "static"
      | TYPEDEF -> "typedef"

let getstorageclass pos ds =
   let ret = ref [] in
   let examine d =
      match d with
           STORAGECLASS sc -> ret := sc :: !ret
         | _ -> ()
   in
   List.iter examine ds;
   match !ret with
        [] -> None
      | [sc] -> Some sc
      | sc :: _more ->
           Pos.failat pos "Multiple storage classes in declaration";
           Some sc

(*
 * type specifiers and qualifiers
 *)

let string_of_ts ts =
   let checkanon tag =
      if String.get tag 0 = '.' then "<anonymous>" else tag
   in
   match ts with
        VOID -> "void"
      | CHAR -> "char"
      | SHORT -> "short"
      | INT -> "int"
      | LONG -> "long"
      | FLOAT -> "float"
      | DOUBLE -> "double"
      | SIGNED -> "signed"
      | UNSIGNED -> "unsigned"
      | STRUCT (_pos, Some tag, _body) -> "struct " ^ checkanon tag
      | STRUCT (_pos, None, _body) -> "struct <anonymous>"
      | UNION (_pos, Some tag, _body) -> "union " ^ checkanon tag
      | UNION (_pos, None, _body) -> "union <anonymous>"
      | ENUM (_pos, Some tag, _body) -> "enum " ^ checkanon tag
      | ENUM (_pos, None, _body) -> "enum <anonymous>"
      | USETYPEDEF name -> name

let ts_sort tss =
   let cmp ts1 ts2 =
      if ts1 = ts2 then 0
      else match ts1, ts2 with
           SIGNED, _ -> -1
         | _, SIGNED -> 1
         | UNSIGNED, _ -> -1
         | _, UNSIGNED -> 1
         | SHORT, _ -> -1
         | _, SHORT -> 1
         | LONG, _ -> -1
         | _, LONG -> 1
         | _, _ -> 0
   in
   List.stable_sort cmp tss

let gettype pos ds =
   let tss = ref [] in
   let const = ref false in
   let volatile = ref false in
   let restrict = ref false in
   let examine d =
      match d with
           STORAGECLASS _ -> ()
         | TYPESPEC ts -> tss := ts :: !tss
         | TYPEQUAL tq -> begin
              match tq with
                   CONST -> const := true
                 | VOLATILE -> volatile := true
                 | RESTRICT -> restrict := true
           end
   in
   List.iter examine ds;
   tss := ts_sort !tss;
   let ty = match !tss with
        [] -> Pos.sayat pos "Warning: implicit int"; T.INT
      | [VOID] -> T.VOID
      | [CHAR] -> T.CHAR
      | [SIGNED; CHAR] -> T.SCHAR
      | [UNSIGNED; CHAR] -> T.UCHAR
      | [SHORT] -> T.SHORT
      | [SHORT; INT] -> T.SHORT
      | [SIGNED; SHORT] -> T.SHORT
      | [SIGNED; SHORT; INT] -> T.SHORT
      | [UNSIGNED; SHORT] -> T.USHORT
      | [UNSIGNED; SHORT; INT] -> T.USHORT
      | [INT] -> T.INT
      | [SIGNED; INT] -> T.INT
      | [UNSIGNED; INT] -> T.UINT
      | [SIGNED] -> T.INT
      | [UNSIGNED] -> T.UINT
      | [LONG] -> T.LONG
      | [LONG; INT] -> T.LONG
      | [SIGNED; LONG] -> T.LONG
      | [SIGNED; LONG; INT] -> T.LONG
      | [UNSIGNED; LONG] -> T.ULONG
      | [UNSIGNED; LONG; INT] -> T.ULONG
      | [LONG; LONG] -> T.LONG
      | [LONG; LONG; INT] -> T.LONG
      | [SIGNED; LONG; LONG] -> T.LONG
      | [SIGNED; LONG; LONG; INT] -> T.LONG
      | [UNSIGNED; LONG; LONG] -> T.ULONG
      | [UNSIGNED; LONG; LONG; INT] -> T.ULONG
      | [FLOAT] -> T.FLOAT
      | [DOUBLE] -> T.DOUBLE
      | [LONG; DOUBLE] -> T.LDOUBLE
      | [STRUCT (_pos, Some tag, _body)] -> T.STRUCT tag
      | [UNION (_pos, Some tag, _body)] -> T.UNION tag
      | [ENUM (_pos, Some tag, _body)] -> T.ENUM tag
      | [USETYPEDEF name] -> T.USETYPEDEF name
      | _ ->
           let s = String.concat " " (List.map string_of_ts !tss) in
           Pos.failat pos ("Illegal type: " ^ s);
           T.INT
   in
   let ty = if !restrict then T.RESTRICT ty else ty in
   let ty = if !const then T.CONST ty else ty in
   let ty = if !volatile then T.VOLATILE ty else ty in
   ty


(**************************************************************)
(* build pass *)

(*
 * common logic
 *)

let rec munge_pointer p ty =
   (*
    * The "pointer" construct in the syntax is a right-recursive sequence
    * of stars, which is made into a chain of POINTER values. The bottom
    * entry in the chain should have the declarator inside it, but the
    * grammar doesn't work that way for its own reasons.
    *
    * Since declarations are read inside-out though, the "ty" argument we
    * get (the type we've accumulated so far) is the type we're pointing
    * to. The qualifiers in the POINTER are on the right of the star and
    * apply to the pointer, so they should be applied second.
    *)
   let POINTER (_pos, tqs, optp') = p in
   let ty' = T.POINTER ty in
   let add t tq =
      match tq with
           CONST -> T.CONST t
         | RESTRICT -> T.RESTRICT t
         | VOLATILE -> T.VOLATILE t
   in
   let ty'' = List.fold_left add ty' tqs in
   match optp' with
        Some p' -> munge_pointer p' ty''
      | None -> ty''


let rec build'any'declarator declare'abs declare'name build'param ctx sc ty r =
   let recurse ty' r' =
      build'any'declarator declare'abs declare'name build'param ctx sc ty' r'
   in
   match r with
        DECLABS pos ->
           declare'abs ctx pos sc ty
      | DECLNAME (pos, name) ->
           declare'name ctx pos sc ty name
      | DECLARRAY (_pos, r', _optsz) ->
           let ty' = T.ARRAYTYPE (ty) in
           recurse ty' r'
      | DECLFUNC (_pos, r', params) ->
           let params' = List.map (build'param ctx) params in
           let ty' = T.FUNCTYPE (ty, params') in
           recurse ty' r'
      | KRDECLFUNC (_pos, r', params) ->
           let ty' = T.KRFUNCTYPE (ty, params) in
           recurse ty' r'
      | DECLPOINTER (_pos, p, r') ->
           let ty' = munge_pointer p ty in
           recurse ty' r'
      | DECLBITFIELD (_pos, Some r', _sz) ->
           let ty' = T.BITFIELD (ty) in
           recurse ty' r'
      | DECLBITFIELD (pos, None, _sz) ->
           let ty' = T.BITFIELD (ty) in
           declare'abs ctx pos sc ty'
      | DECLINIT (r', _i) ->
           recurse ty r'

let build'any'decl build'typespec build'declarator build'more ctx d =
   let buildit pos ds r =
      let ds' = List.map (build'typespec ctx) ds in
      let sc = getstorageclass pos ds' in
      let ty = gettype pos ds' in
      build'declarator ctx sc ty r
   in
   match d with
        DECL (pos, ds, r) -> [buildit pos ds r]
      | DECLS (pos, ds, rs) -> List.map (buildit pos ds) rs
      | MOREPARAMS -> [build'more ctx]


(*
 * structure members (which we don't actually need to care about)
 * also enum elements (ditto)
 *)

let build'structbody _ = ()
let build'enumbody _ = ()


(*
 * function parameters
 *)

let declare'param'abs _ctx pos sc ty =
   match sc with
        None -> T.PARAM (false, ty)
      | Some REGISTER -> T.PARAM (true, ty)
      | Some sc' ->
           Pos.failat pos ("Invalid storage class " ^ string_of_sc sc' ^
                           " in function parameter");
           T.PARAM (false, ty)

let declare'param'name ctx pos sc ty _name =
   declare'param'abs ctx pos sc ty

let build'param'typespec _ctx d =
   begin
   match d with
        TYPESPEC (STRUCT (pos, _, Some _body)) ->
             Pos.sayat pos "Warning: inaccessible struct declared in parameter"
      | TYPESPEC (UNION (pos, _, Some _body)) ->
             Pos.sayat pos "Warning: inaccessible union declared in parameter"
      | TYPESPEC (ENUM (pos, _, Some _body)) ->
             Pos.sayat pos "Warning: inaccessible enum declared in parameter"
      | _ -> ()
   end;
   d

let build'param'more _ctx =
   T.MOREPARAMS

let rec build'param'declarator ctx sc ty r =
   let f =
      build'any'declarator declare'param'abs declare'param'name build'param
   in
   f ctx sc ty r

and build'param ctx d =
   let f =
      build'any'decl build'param'typespec build'param'declarator
        build'param'more
   in
   match f ctx d with
        [d'] -> d'
      | _ -> assert false (* not syntactically possible *)


(*
 * top-level decls
 *)

let build'top'typespec ctx d =
   match d with
        TYPESPEC (STRUCT (pos, Some tag, Some body)) ->
           ctx_addtag ctx pos tag (T.STRUCTDECL (pos, build'structbody body));
           TYPESPEC (STRUCT (pos, Some tag, None))
      | TYPESPEC (STRUCT (pos, None, Some body)) ->
           let tag = ctx_maketag ctx in
           ctx_addtag ctx pos tag (T.STRUCTDECL (pos, build'structbody body));
           TYPESPEC (STRUCT (pos, Some tag, None))
      | TYPESPEC (UNION (pos, Some tag, Some body)) ->
           ctx_addtag ctx pos tag (T.UNIONDECL (pos, build'structbody body));
           TYPESPEC (UNION (pos, Some tag, None))
      | TYPESPEC (UNION (pos, None, Some body)) ->
           let tag = ctx_maketag ctx in
           ctx_addtag ctx pos tag (T.UNIONDECL (pos, build'structbody body));
           TYPESPEC (UNION (pos, Some tag, None))
      | TYPESPEC (ENUM (pos, Some tag, Some body)) ->
           ctx_addtag ctx pos tag (T.ENUMDECL (pos, build'enumbody body));
           TYPESPEC (ENUM (pos, Some tag, None))
      | TYPESPEC (ENUM (pos, None, Some body)) ->
           let tag = ctx_maketag ctx in
           ctx_addtag ctx pos tag (T.ENUMDECL (pos, build'enumbody body));
           TYPESPEC (ENUM (pos, Some tag, None))
      | _ -> d

let top'declare_abs _ctx _sc _ty =
   assert false (* not syntactically possible at top level *)

let top'declare_name ctx pos sc ty name =
   match sc with
        Some TYPEDEF -> ctx_addtype ctx pos name ty
      | _ -> match ty with
             T.FUNCTYPE _
           | T.KRFUNCTYPE _
           | T.POINTER (T.FUNCTYPE _)
           | T.POINTER (T.KRFUNCTYPE _) ->
                ctx_addfunc ctx pos name ty
           | _ -> ()

let build'top'declarator ctx sc ty r =
   let f =
      build'any'declarator top'declare_abs top'declare_name build'param
   in
   f ctx sc ty r

let build'top'more _ctx =
   assert false  (* not syntactically possible *)

let build'top'decl ctx d =
   let f =
      build'any'decl build'top'typespec build'top'declarator build'top'more
   in
   f ctx d

let build'decl ctx d =
   match d with
        GENCALL (pos, name) ->
           ctx_addcall ctx pos name
      | CDECL d' -> ignore (build'top'decl ctx d')

(**************************************************************)
(* external interface *)

let build ds =
   let ctx = newctx () in
   List.iter (build'decl ctx) ds;
   let tagdecls = !(ctx.tagdecl_accum) in
   let typedefs = !(ctx.typedef_accum) in
   let funcdecls = !(ctx.funcdecl_accum) in
   let gencalls = List.rev !(ctx.gencall_accum) in
   { T.tagdecls; T.typedefs; T.funcdecls; T.gencalls; }
