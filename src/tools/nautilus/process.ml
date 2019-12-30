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

open Ast

(**************************************************************)
(* eliminate typedefs *)

let rec untypedef'typename ctx ty =
   match ty with
        VOID | CHAR | SCHAR | UCHAR | SHORT | USHORT | INT | UINT
      | LONG | ULONG | LONGLONG | ULONGLONG | FLOAT | DOUBLE | LDOUBLE
      | STRUCT _ | UNION _ | ENUM _ -> ty
      | POINTER ty' -> POINTER (untypedef'typename ctx ty')
      | CONST ty' -> CONST (untypedef'typename ctx ty')
      | RESTRICT ty' -> RESTRICT (untypedef'typename ctx ty')
      | VOLATILE ty' -> VOLATILE (untypedef'typename ctx ty')
      | ARRAYTYPE ty' -> ARRAYTYPE (untypedef'typename ctx ty')
      | BITFIELD ty' -> BITFIELD (untypedef'typename ctx ty')
      | FUNCTYPE (ty', params) ->
          let ty'' = untypedef'typename ctx ty' in
          let params' = List.map (untypedef'param ctx) params in
          FUNCTYPE (ty'', params')
      | KRFUNCTYPE (ty', params) ->
          let ty'' = untypedef'typename ctx ty' in
          KRFUNCTYPE (ty'', params)
      | USETYPEDEF name ->
          let (_pos, ty') = Types.StringMap.find name ctx in
          untypedef'typename ctx ty'

and untypedef'param ctx p =
   match p with
        PARAM (isregister, ty) -> PARAM (isregister, untypedef'typename ctx ty)
      | MOREPARAMS -> MOREPARAMS

let untypedef'tagdecl _ctx d = d

let untypedef'funcdecl ctx (pos, ty) =
   let ty' = untypedef'typename ctx ty in
   (pos, ty')

let untypedef'spec { tagdecls; typedefs; funcdecls; gencalls; } =
   let tagdecls =
      Types.StringMap.map (untypedef'tagdecl typedefs) tagdecls
   in
   let funcdecls =
      Types.StringMap.map (untypedef'funcdecl typedefs) funcdecls
   in
   let typedefs = Types.StringMap.empty in
   { tagdecls; typedefs; funcdecls; gencalls; }

let untypedef spec = untypedef'spec spec


(**************************************************************)
(* change foo(void) to foo() *)

let devoid'funcdecl (pos, ty) =
   let ty' = match ty with
        FUNCTYPE (tyret, [PARAM (_, VOID)]) ->
           FUNCTYPE (tyret, [])
      | _ -> ty
   in
   (pos, ty')

let devoid'spec spec =
   let funcdecls = Types.StringMap.map devoid'funcdecl spec.funcdecls in
   { spec with funcdecls; }

let devoid spec = devoid'spec spec


(**************************************************************)
(* check the gencalls list *)

let floating ty =
   match ty with
        FLOAT | DOUBLE | LDOUBLE -> true
      | _ -> false

let rec unregisterizable ty isarg =
   match ty with
        VOID -> if isarg then true else false
      | STRUCT _ -> true
      | UNION _ -> true
      | CONST ty' -> unregisterizable ty' isarg
      | RESTRICT ty' -> unregisterizable ty' isarg
      | VOLATILE ty' -> unregisterizable ty' isarg
      | ARRAYTYPE _ -> true
      | BITFIELD _ -> true
      | FUNCTYPE _ -> true
      | KRFUNCTYPE _ -> true
      | _ -> false

let check_call_ok callpos funcpos name ty =
   let fail msg =
      Pos.failat callpos ("Cannot generate call for " ^ name ^ ": " ^ msg);
      Pos.failat funcpos ("Declaration of " ^ name ^ " is here")
   in
   let checktype t isarg what =
      if floating t then
         fail (what ^ " has floating point type")
      else if unregisterizable t isarg then
         fail ("the type of " ^ what ^ " cannot possibly be placed in a " ^
               "register.")
      else ()
   in
   let checkparam (n, p) =
      match p with
           PARAM (_isregister, t) ->
              checktype t true ("parameter " ^ string_of_int (n+1))
         | MOREPARAMS ->
              fail "it is variadic so I don't know what arguments to use."
   in
   match ty with
        FUNCTYPE (tyret, params) ->
           checktype tyret false "the return value";
           List.iter checkparam (Util.number params)
      | KRFUNCTYPE _ ->
           fail ("it is declared K&R-style so I don't know what arguments " ^
                 "to use.")
      | _ ->
           fail "it is not a function."

let checkcalls spec =
   let checkone (pos, name) =
      try
         let (fpos, ty) = Types.StringMap.find name spec.funcdecls in
         check_call_ok pos fpos name ty
      with Not_found ->
         Pos.failat pos ("No declaration for function " ^ name ^ " found")
   in
   List.iter checkone spec.gencalls


(**************************************************************)
(* external interface *)

let process spec =
   let spec' = devoid (untypedef spec) in
   checkcalls spec';
   spec'
