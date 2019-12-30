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


open Ast

let newctx () = ref Types.StringMap.empty

let ctx_getvar ctx name =
   try
      let (_pos, ty) = Types.StringMap.find name !ctx in
      Some ty
   with Not_found -> None

let ctx_addvar ctx name pos ty =
   try
      let (oldpos, _oldty) = Types.StringMap.find name !ctx in
      Pos.sayat pos ("Duplicate binding for variable " ^ name);
      Pos.crashat oldpos "Previous binding"
   with Not_found ->
      ctx := Types.StringMap.add name (pos, ty) !ctx

let string_of_boolop op =
   match op with
   | LOGNOT -> "logical not"
   | LOGAND -> "logical and"
   | LOGOR -> "logical or"
   | LOGEQ -> "boolean eq"

let string_of_intop op =
   match op with
   | INTEQ -> "integer eq"
   | INTLT -> "integer less-than"
   | INTADD -> "integer add"
   | INTSUB -> "integer subtract"

let string_of_bvop op =
   match op with
   | BVEQ -> "bitvector eq"
   | BVLT -> "bitvector less-than"
   | BVADD -> "bitvector add"
   | BVSUB -> "bitvector subtract"
   | BVBITAND -> "bitvector bitwise and"
   | BVBITOR -> "bitvector bitwise or"
   | BVUSHR -> "bitvector unsigned shift right"
   | BVSHL -> "bitvector shift left"

let string_of_ty ty =
   match ty with
   | BOOL -> "bool"
   | INT -> "int"
   | BV -> "bitvec"

let fail pos msg =
   Pos.crashat pos msg

let expect _ctx pos ty_expected ty what =
   if ty_expected <> ty then
      fail pos ("Type mismatch in " ^ what ^ ": Expected " ^
                string_of_ty ty_expected ^ ", found " ^ string_of_ty ty)
   else ()

let rec inf'binary ctx pos arg1 arg2 what =
   let (arg1', ty1) = inf'expr ctx arg1 in
   let (arg2', ty2) = inf'expr ctx arg2 in
   let args' = [arg1'; arg2'] in
   if ty1 <> ty2 then
      fail pos ("Mismatched operands for " ^ what ^ ": " ^
                string_of_ty ty1 ^ " and " ^ string_of_ty ty2)
   else
     (ty1, args')

and check'binary ctx _pos ty_expected arg1 arg2 =
   let arg1' = check'expr ctx ty_expected arg1 in
   let arg2' = check'expr ctx ty_expected arg2 in
   [arg1'; arg2']

and inf'eq ctx pos arg1 arg2 =
   let (ty, args') = inf'binary ctx pos arg1 arg2 "equal" in
   match ty with
   | BOOL -> BOOLOP (pos, LOGEQ, args')
   | INT -> INTOP (pos, INTEQ, args')
   | BV -> BVOP (pos, BVEQ, args')

and inf'lt ctx pos arg1 arg2 =
   let (ty, args') = inf'binary ctx pos arg1 arg2 "less-than" in
   match ty with
   | BOOL -> fail pos ("Less-than on booleans")
   | INT -> INTOP (pos, INTLT, args')
   | BV -> BVOP (pos, BVLT, args')

and inf'expr ctx e =
   match e with
   | CONST (pos, k, ty) ->
        (CONST (pos, k, ty), ty)
   | READVAR (pos, x, _ty) -> begin
        (* ty is not known, so we must fill it in *)
        match ctx_getvar ctx x with
        | Some ty ->
             (READVAR (pos, x, ty), ty)
        | None ->
             fail pos ("Unbound variable " ^ x)
     end
   | IF (pos, c, t, f) ->
        let c' = check'expr ctx BOOL c in
        let (t', ty't) = inf'expr ctx t in
        let (f', ty'f) = inf'expr ctx f in
        if ty't <> ty'f then
           fail pos ("Type mismatch in ite; got " ^ string_of_ty ty't ^
                     " and " ^ string_of_ty ty'f)
        else
           (IF (pos, c', t', f'), ty't)
   | SLICE (pos, e1, a, b) ->
        let e1' = check'expr ctx BV e1 in
        (SLICE (pos, e1', a, b), BV)
   | BV2INT (pos, e1) ->
        let e1' = check'expr ctx BV e1 in
        (BV2INT (pos, e1'), INT)
   | BOOLOP (pos, LOGNOT, [arg]) ->
        let arg' = check'expr ctx BOOL arg in
        (BOOLOP (pos, LOGNOT, [arg']), BOOL)
   | BOOLOP (pos, LOGAND, [arg1; arg2]) ->
        let arg1' = check'expr ctx BOOL arg1 in
        let arg2' = check'expr ctx BOOL arg2 in
        (BOOLOP (pos, LOGAND, [arg1'; arg2']), BOOL)
   | BOOLOP (pos, LOGOR, [arg1; arg2]) ->
        let arg1' = check'expr ctx BOOL arg1 in
        let arg2' = check'expr ctx BOOL arg2 in
        (BOOLOP (pos, LOGOR, [arg1'; arg2']), BOOL)
   | BOOLOP (pos, LOGEQ, [arg1; arg2]) ->
        (inf'eq ctx pos arg1 arg2, BOOL)
   | BOOLOP (pos, op, _) ->
        fail pos ("Wrong arguments for " ^ string_of_boolop op)
   | INTOP (pos, INTEQ, [arg1; arg2]) ->
        (inf'eq ctx pos arg1 arg2, BOOL)
   | INTOP (pos, INTLT, [arg1; arg2]) ->
        (inf'lt ctx pos arg1 arg2, BOOL)
   | INTOP (pos, INTADD, [arg1; arg2]) ->
        (* input distinguishes integer and bv add ops, so check it *)
        let args' = check'binary ctx pos INT arg1 arg2 in
        (INTOP (pos, INTADD, args'), INT)
   | INTOP (pos, INTSUB, [arg1; arg2]) ->
        (* input distinguishes integer and bv sub ops, so check it *)
        let args' = check'binary ctx pos INT arg1 arg2 in
        (INTOP (pos, INTSUB, args'), INT)
   | INTOP (pos, op, _) ->
        fail pos ("Wrong arguments for " ^ string_of_intop op)
   | BVOP (pos, BVEQ, [arg1; arg2]) ->
        (inf'eq ctx pos arg1 arg2, BOOL)
   | BVOP (pos, BVLT, [arg1; arg2]) ->
        (inf'lt ctx pos arg1 arg2, BOOL)
   | BVOP (pos, BVADD, [arg1; arg2]) ->
        (* input distinguishes integer and bv add ops, so check it *)
        let args' = check'binary ctx pos BV arg1 arg2 in
        (BVOP (pos, BVADD, args'), BV)
   | BVOP (pos, BVSUB, [arg1; arg2]) ->
        (* input distinguishes integer and bv sub ops, so check it *)
        let args' = check'binary ctx pos BV arg1 arg2 in
        (BVOP (pos, BVSUB, args'), BV)
   | BVOP (pos, BVBITAND, [arg1; arg2]) ->
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        (BVOP (pos, BVBITAND, [arg1'; arg2']), BV)
   | BVOP (pos, BVBITOR, [arg1; arg2]) ->
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        (BVOP (pos, BVBITOR, [arg1'; arg2']), BV)
   | BVOP (pos, BVUSHR, [arg1; arg2]) ->
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        (BVOP (pos, BVUSHR, [arg1'; arg2']), BV)
   | BVOP (pos, BVSHL, [arg1; arg2]) ->
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        (BVOP (pos, BVSHL, [arg1'; arg2']), BV)
   | BVOP (pos, op, _) ->
        fail pos ("Wrong arguments for " ^ string_of_bvop op)

and check'expr ctx ty_expected e =
   match e with
   | CONST (pos, k, ty) ->
        (* ty is already known and should be correct *)
        expect ctx pos ty_expected ty "constant";
        CONST (pos, k, ty)
   | READVAR (pos, x, _ty) -> begin
        (* ty is not known, so just fill it in *)
        match ctx_getvar ctx x with
        | Some ty ->
             expect ctx pos ty_expected ty "variable reference";
             READVAR (pos, x, ty)
        | None ->
             fail pos ("Unbound variable " ^ x)
     end
   | IF (pos, c, t, f) ->
        let c' = check'expr ctx BOOL c in
        let t' = check'expr ctx ty_expected t in
        let f' = check'expr ctx ty_expected f in
        IF (pos, c', t', f')
   | SLICE (pos, e1, a, b) ->
        expect ctx pos ty_expected BV "slice";
        let e1' = check'expr ctx BV e1 in
        SLICE (pos, e1', a, b)
   | BV2INT (pos, e1) ->
        expect ctx pos ty_expected INT "bv2int call";
        let e1' = check'expr ctx BV e1 in
        BV2INT (pos, e1')
   | BOOLOP (pos, LOGNOT, [arg]) ->
        expect ctx pos ty_expected BOOL "logical not";
        let arg' = check'expr ctx BOOL arg in
        BOOLOP (pos, LOGNOT, [arg'])
   | BOOLOP (pos, LOGAND, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "logical and";
        let arg1' = check'expr ctx BOOL arg1 in
        let arg2' = check'expr ctx BOOL arg2 in
        BOOLOP (pos, LOGAND, [arg1'; arg2'])
   | BOOLOP (pos, LOGOR, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "logical or";
        let arg1' = check'expr ctx BOOL arg1 in
        let arg2' = check'expr ctx BOOL arg2 in
        BOOLOP (pos, LOGOR, [arg1'; arg2'])
   | BOOLOP (pos, LOGEQ, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "eq";
        (* need to infer which kind of eq to use *)
        inf'eq ctx pos arg1 arg2
   | BOOLOP (pos, op, _) ->
        fail pos ("Wrong arguments for " ^ string_of_boolop op)
   | INTOP (pos, INTEQ, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "equal";
        (* need to infer which kind of eq to use *)
        inf'eq ctx pos arg1 arg2
   | INTOP (pos, INTLT, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "less-than";
        (* need to infer which kind of lt to use *)
        inf'lt ctx pos arg1 arg2
   | INTOP (pos, INTADD, [arg1; arg2]) ->
        (* input distinguishes integer and bv add ops, so check it *)
        expect ctx pos ty_expected INT "int-add";
        let args' = check'binary ctx pos INT arg1 arg2 in
        INTOP (pos, INTADD, args')
   | INTOP (pos, INTSUB, [arg1; arg2]) ->
        (* input distinguishes integer and bv add ops, so check it *)
        expect ctx pos ty_expected INT "int-sub";
        let args' = check'binary ctx pos INT arg1 arg2 in
        INTOP (pos, INTSUB, args')
   | INTOP (pos, op, _) ->
        fail pos ("Wrong arguments for " ^ string_of_intop op)
   | BVOP (pos, BVEQ, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "equal";
        (* need to infer which kind of eq to use *)
        inf'eq ctx pos arg1 arg2
   | BVOP (pos, BVLT, [arg1; arg2]) ->
        expect ctx pos ty_expected BOOL "less-than";
        (* need to infer which kind of lt to use *)
        inf'lt ctx pos arg1 arg2
   | BVOP (pos, BVADD, [arg1; arg2]) ->
        (* input distinguishes integer and bv add ops, so check it *)
        expect ctx pos ty_expected BV "bitvec-add";
        let args' = check'binary ctx pos BV arg1 arg2 in
        BVOP (pos, BVADD, args')
   | BVOP (pos, BVSUB, [arg1; arg2]) ->
        (* input distinguishes integer and bv sub ops, so check it *)
        expect ctx pos ty_expected BV "bitvec-sub";
        let args' = check'binary ctx pos BV arg1 arg2 in
        BVOP (pos, BVSUB, args')
   | BVOP (pos, BVBITAND, [arg1; arg2]) ->
        expect ctx pos ty_expected BV "bitwise and";
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        BVOP (pos, BVBITAND, [arg1'; arg2'])
   | BVOP (pos, BVBITOR, [arg1; arg2]) ->
        expect ctx pos ty_expected BV "bitwise or";
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        BVOP (pos, BVBITOR, [arg1'; arg2'])
   | BVOP (pos, BVUSHR, [arg1; arg2]) ->
        expect ctx pos ty_expected BV "bitwise unsigned shift right";
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        BVOP (pos, BVUSHR, [arg1'; arg2'])
   | BVOP (pos, BVSHL, [arg1; arg2]) ->
        expect ctx pos ty_expected BV "bitwise shift left";
        let arg1' = check'expr ctx BV arg1 in
        let arg2' = check'expr ctx BV arg2 in
        BVOP (pos, BVSHL, [arg1'; arg2'])
   | BVOP (pos, op, _) ->
        fail pos ("Wrong arguments for " ^ string_of_bvop op)

let inf'stmt ctx s =
   match s with
   | ASSERT (pos, e) ->
        ASSERT (pos, check'expr ctx BOOL e)
   | DECL (pos, x, ty) ->
        ctx_addvar ctx x pos ty;
        DECL (pos, x, ty)
   | LET (pos, x, ty, e) ->
        let e' = check'expr ctx ty e in
        ctx_addvar ctx x pos ty;
        LET (pos, x, ty, e')
   | MISC (pos, txt) ->
        MISC (pos, txt)

let loadpredefs ctx =
   ctx_addvar ctx "true" Pos.builtin BOOL;
   ctx_addvar ctx "false" Pos.builtin BOOL

let go stmts =
   let ctx = newctx () in
   loadpredefs ctx;
   List.map (inf'stmt ctx) stmts
