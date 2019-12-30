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

let includepath = ref []

let curdir = ref "."
let includestack = ref []

(*
let string_of_lexpos pos =
   let line = string_of_int pos.Lexing.pos_lnum in
   let col = string_of_int (pos.Lexing.pos_cnum - pos.Lexing.pos_bol) in
   pos.Lexing.pos_fname ^ ":" ^ line ^ ":" ^ col
*)

let addincludepath path =
  includepath := !includepath @ [path]

let findinclude name =
  let tryopen pathname =
    try Some (pathname, open_in pathname)
    with Sys_error _ -> None
  in
  let once z dir =
    match z with
    | Some _ -> z
    | None -> tryopen (Filename.concat dir name)
  in
  match List.fold_left once None !includepath with
  | Some z -> z
  | None ->
      match tryopen (Filename.concat (!curdir) name) with
      | Some z -> z
      | None ->
          let msg = "Cannot find include file " ^ name in
          failwith ( (* getpostxt () ^ ": " ^ *) msg)

let setpathname lexbuf file =
  let pos = { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = file; } in
  { lexbuf with Lexing.lex_curr_p = pos; }

let includefile bypath name =
  let (pathname, channel) =
    if bypath then findinclude name
    else (name, open_in name)
 in
 let lexbuf = setpathname (Lexing.from_channel channel) pathname in
 includestack := (lexbuf, !curdir) :: !includestack;
 curdir := Filename.dirname pathname

let includewrap eof iseof lexer fakelexbuf =
   let lbupdate reallexbuf =
      fakelexbuf.Lexing.lex_eof_reached <- reallexbuf.Lexing.lex_eof_reached;
      fakelexbuf.Lexing.lex_start_p <- reallexbuf.Lexing.lex_start_p;
      fakelexbuf.Lexing.lex_curr_p <- reallexbuf.Lexing.lex_curr_p
   in
   let rec tryread () =
      match !includestack with
           [] -> eof
         | (reallexbuf, prevdir) :: more ->
              let tok = lexer reallexbuf in
              lbupdate reallexbuf;
              if iseof tok then begin
                 includestack := more;
                 curdir := prevdir;
                 tryread ()
              end
              else tok
   in
   tryread ()
