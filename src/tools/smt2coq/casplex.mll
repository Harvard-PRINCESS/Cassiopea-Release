(*
 * Copyright (c) 2016, 2017, 2018, 2019
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

{

open Pos
open Lextools
open Caspparse

let keywords = Types.stringmap_of_list [
   ("slice", SLICE);
   ("zero_extend", ZERO_EXTEND);
]
let doident = doident' keywords (fun x -> IDENT x)

let bitnumber_of_string s =
   let bitlen = (String.length s) - 2 in
   let k = int_of_string s in
   (k, bitlen)

let bitnumber'_of_string s =
   let bitlen = 4 * ((String.length s) - 2) in
   let k = int_of_string s in
   (k, bitlen)

}

let ws = [' ' '\t']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_' '-' '$']
let alnum = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '-' '$']
let bit = ['0' '1']
let hexdigit = ['a'-'f' 'A'-'F' '0'-'9']

rule base = parse
     ws+		{ advance lexbuf; base lexbuf }
   | '\n'		{ nl lexbuf; base lexbuf }
   | ';' ';' 		{ comment lexbuf; base lexbuf }
   | 'b' '+'		{ advance lexbuf; B_PLUS }
   | 'b' '-'		{ advance lexbuf; B_MINUS }
   | 'b' '<'		{ advance lexbuf; B_LT }
   | '0' 'b' bit+	{ BITNUMBER (tval' lexbuf bitnumber_of_string) }
   | '0' 'x' hexdigit+	{ BITNUMBER (tval' lexbuf bitnumber'_of_string) }
   | digit alnum*	{ NUMBER (tval' lexbuf int_of_string) }
   | letter alnum*	{ doident (tval lexbuf) }
   | '!'		{ advance lexbuf; BANG }
   | '&'		{ advance lexbuf; AMP }
   | '|'		{ advance lexbuf; BAR }
   | ':'		{ advance lexbuf; COLON }
   | '<'		{ advance lexbuf; LT }
   | '-'		{ advance lexbuf; MINUS }
   | '+'		{ advance lexbuf; PLUS }
   | '&' '&'		{ advance lexbuf; AMPAMP }
   | '|' '|'		{ advance lexbuf; BARBAR }
   | '=' '='		{ advance lexbuf; EQEQ }
   | '>' '>'		{ advance lexbuf; GTGT }
   | '<' '<'		{ advance lexbuf; LTLT }
   | '('		{ advance lexbuf; LPAREN }
   | ')'		{ advance lexbuf; RPAREN }
   | '['		{ advance lexbuf; LBRACK }
   | ']'		{ advance lexbuf; RBRACK }
   | _			{ badchar (posval lexbuf) (*; base lexbuf*) }
   | eof		{ EOF }

(* this needs to be its own state to defeat the longest-match rule *)
and comment = parse
     [ ^ '\n' ]* '\n'	{ nl lexbuf; }

{
let dumpone t =
   match t with
        EOF ->             "EOF"
      | NUMBER n ->        ("NUMBER " ^ string_of_int n)
      | BITNUMBER (n, w) ->  ("BITNUMBER " ^ string_of_int n ^ " " ^ string_of_int w)
      | IDENT x ->         ("IDENT " ^ x)
      | SLICE ->           "SLICE"
      | ZERO_EXTEND ->     "ZERO_EXTEND"
      | LPAREN ->          "LPAREN"
      | RPAREN ->          "RPAREN"
      | LBRACK ->          "LBRACK"
      | RBRACK ->          "RBRACK"
      | BANG ->            "BANG"
      | AMP ->             "AMP"
      | BAR ->             "BAR"
      | COLON ->           "COLON"
      | LT ->              "LT"
      | MINUS ->           "MINUS"
      | PLUS ->            "PLUS"
      | AMPAMP ->          "AMPAMP"
      | BARBAR ->          "BARBAR"
      | EQEQ ->            "EQEQ"
      | GTGT ->            "GTGT"
      | LTLT ->            "LTLT"
      | B_PLUS ->          "B_PLUS"
      | B_MINUS ->         "B_MINUS"
      | B_LT ->            "B_LT"


let iseof t =
   match t with
        EOF -> true
      | _ -> false

let read = read' base Caspparse.file EOF iseof dumpone (fun x -> x)
}
