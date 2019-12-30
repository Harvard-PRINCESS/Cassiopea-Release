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
(* make an output C file *)

let uniq_types tys =
   List.sort_uniq compare tys

let rec emit_type spec ty sym =
   let sym' = if sym = "" then "" else " " ^ sym in
   match ty with
        VOID -> "void" ^ sym'
      | CHAR -> "char" ^ sym'
      | SCHAR -> "ssigned char" ^ sym'
      | UCHAR -> "unsigned char" ^ sym'
      | SHORT -> "short" ^ sym'
      | USHORT -> "unsigned short" ^ sym'
      | INT -> "int" ^ sym'
      | UINT -> "unsigned" ^ sym'
      | LONG -> "long" ^ sym'
      | ULONG -> "unsigned long" ^ sym'
      | LONGLONG -> "long long" ^ sym'
      | ULONGLONG -> "unsigned long long" ^ sym'
      | FLOAT -> "float" ^ sym'
      | DOUBLE -> "double" ^ sym'
      | LDOUBLE -> "long double" ^ sym'
      | STRUCT tag -> "struct " ^ tag ^ sym'
      | UNION tag -> "union " ^ tag ^ sym'
      | ENUM tag -> "enum " ^ tag ^ sym'
      | USETYPEDEF name -> name ^ sym'
      | POINTER ty' -> emit_type spec ty' (" *" ^ sym)
      | CONST ty' -> emit_type spec ty' (" const" ^ sym')
      | RESTRICT ty' -> emit_type spec ty' (" restrict" ^ sym')
      | VOLATILE ty' -> emit_type spec ty' (" volatile" ^ sym')
      | ARRAYTYPE ty' -> emit_type spec ty' (sym ^ "[]")
      | BITFIELD ty' -> emit_type spec ty' (sym ^ ": 123")
      | FUNCTYPE (tyret, []) ->
           emit_type spec tyret (sym ^ "(void)")
      | FUNCTYPE (tyret, params) ->
           let paramstr =
              let oneparam p =
                 match p with
                      PARAM (isregister, pty) ->
                         let isr = if isregister then "register " else "" in
                         isr ^ emit_type spec pty ""
                    | MOREPARAMS -> "..."
              in
              String.concat ", " (List.map oneparam params)
           in
           emit_type spec tyret (sym ^ "(" ^ paramstr ^ ")")
      | KRFUNCTYPE _ ->
           assert false (* disallowed upstream *)

let emit_funcheader spec tyret name params =
(*
   emit_type spec tyret ^
   " " ^
   name ^
   "(" ^
   begin
   match params with
        [] -> "void"
      | _ -> String.concat ", " (List.map (emit_type spec) params)
   end ^
   ")"
*)
   emit_type spec (FUNCTYPE (tyret, params)) name

let declare_type _spec ty =
   match ty with
        STRUCT name -> ["struct " ^ name ^ ";"]
      | UNION name -> ["union " ^ name ^ ";"]
      | ENUM name -> ["enum " ^ name ^ ";"] (* XXX: won't work *)
      | _ -> []

let declare_func spec tyret name params =
   emit_funcheader spec tyret name params ^ ";"

let generate_callfunc spec tyret name params =
   let params =
      let mk (n, p) =
         match p with
              PARAM (isregister, ty) -> (n, isregister, ty)
            | MOREPARAMS -> assert false (* prohibited upstream *)
      in
      List.map mk (Util.number params)
   in

   let hdr = emit_funcheader spec VOID "nautiluscall" [] in
   let locals =
      let mklocal (n, _isregister, ty) =
         "   " ^ emit_type spec ty ("arg" ^ string_of_int n) ^ ";\n"
      in
      String.concat "\n" (List.map mklocal params)
   in

   let firstasmargs =
      let mkarg (n, _, _) =
         "%" ^ string_of_int n
      in
      String.concat " " (List.map mkarg params)
   in
   let firstasmconstraints =
      let mkcons (n, _, _) =
         "\"+r\" (arg" ^ string_of_int n ^ ")"
      in
      String.concat ", " (List.map mkcons params)
   in
   let firstasm =
      "   __asm volatile(\"nautilusbegin " ^ firstasmargs ^ "\" :\n" ^
      "                  " ^ firstasmconstraints ^ ");\n"
   in

   let call =
      let ret = if tyret = VOID then "" else "ret = " in
      let mkarg (n, _, _) = "arg" ^ string_of_int n in
      let args = String.concat ", " (List.map mkarg params) in
      "   " ^ ret ^ name ^ "(" ^ args ^ ");\n"
   in

   let secondasmargs =
      if tyret = VOID then "" else "%0"
   in
   let secondasmconstraints =
      if tyret = VOID then "" else "\"r\" (ret)"
   in
   let secondasm =
      "   __asm volatile(\"nautilusend " ^ secondasmargs ^ "\" ::\n" ^
      "                  " ^ secondasmconstraints ^ ");\n"
   in

   hdr ^ "{\n" ^
   locals ^
   (if tyret = VOID then "" else
      "   " ^ emit_type spec tyret "ret" ^ ";\n\n"
   ) ^
   "   " ^ firstasm ^ "\n" ^
   "   " ^ call ^ "\n" ^
   "   " ^ secondasm ^ "\n" ^
   (if tyret = VOID then "" else "   return ret;\n") ^
   "}\n"

let ctext spec callname =
   let (_funcpos, ty) = Types.StringMap.find callname spec.funcdecls in
   let tyret, params =
      match ty with
           FUNCTYPE (tyret, params) -> tyret, params
         | _ -> assert false
   in
   let typarams =
      let once p =
         match p with
              PARAM (_, t) -> t
            | MOREPARAMS -> assert false
      in
      List.map once params
   in
   let alltypes = uniq_types (tyret :: typarams) in
   let typedecls = List.concat (List.map (declare_type spec) alltypes) in

   String.concat "\n" typedecls ^ "\n" ^
     declare_func spec tyret callname params ^ "\n" ^
     generate_callfunc spec tyret callname params ^ "\n"


(**************************************************************)
(* handle one input file *)

let readin name =
   let ptree = Lexer.read name in
   let ast = Buildast.build ptree in
   let ast = Process.process ast in
   ast

let writeout filename txt =
   let outfile = open_out filename in
   output_string outfile txt;
   close_out outfile

let run infile =
   let spec = readin infile in
   let one_call (_pos, callname) =
      let text = ctext spec callname in
      writeout ("nautasm_" ^ callname ^ ".c") text
   in
   List.iter one_call spec.gencalls
