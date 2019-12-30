(*
 * Copyright (c) 2016
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

(* Source positions. *)

type pos = {
   file: string;
   startline: int;
   startcolumn: int;
   endline: int;
   endcolumn: int;
}

let fromparser () =
   let getlc lp =
      let line = lp.Lexing.pos_lnum in
      let column = lp.Lexing.pos_cnum - lp.Lexing.pos_bol + 1 in
      (line, column)
   in
      
   let lp0 = Parsing.symbol_start_pos () in
   let lp1 = Parsing.symbol_end_pos () in
   let file = lp0.Lexing.pos_fname in
   let (startline, startcolumn) = getlc lp0 in
   let (endline, endcolumn) = getlc lp1 in
   { file; startline; startcolumn; endline; endcolumn; }

let string_of_pos { file; startline; startcolumn; endline; endcolumn; } =
   let lcstr l c =
      string_of_int l ^ ":" ^ string_of_int c
   in
   let endstr =
      if startline <> endline then "-" ^ lcstr endline endcolumn 
      else if startcolumn <> endcolumn then "-" ^ string_of_int endcolumn
      else ""
   in
   file ^ ":" ^ lcstr startline startcolumn ^ endstr

let sayat pos msg = Util.say (string_of_pos pos ^ ": " ^ msg)
let crashat pos msg = Util.crash (string_of_pos pos ^ ": " ^ msg)

let builtin = {
   file = "<built-in>";
   startline = 0;
   startcolumn = 0;
   endline = 0;
   endcolumn = 0;
}

let nowhere = {
   file = "-";
   startline = 0;
   startcolumn = 0;
   endline = 0;
   endcolumn = 0;
}
