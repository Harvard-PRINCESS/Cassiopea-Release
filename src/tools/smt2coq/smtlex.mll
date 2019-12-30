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
open Smtparse

let keywords = Types.stringmap_of_list [
   ("_", US);
   ("assert", ASSERT);
   ("BitVec", BITVEC);
   ("Bool", BOOL);
   ("check-sat", CHECK_SAT);
   ("declare-fun", DECLARE_FUN);
   ("define-fun", DEFINE_FUN);
   ("exit", EXIT);
   ("Int", INT);
   ("get-model", GET_MODEL);
   ("pop", POP);
   ("push", PUSH);
   ("set-option", SET_OPTION);
   ("zero_extend", ZERO_EXTEND);
]
let doident = doident' keywords (fun x -> IDENT x)

let bitnumber_of_string s =
   let bitlen = (String.length s) - 2 in
   let k = int_of_string ("0b" ^ (String.sub s 2 bitlen)) in
   (k, bitlen)

}

let ws = [' ' '\t']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_' '-' '$']
let alnum = ['0'-'9' 'a'-'z' 'A'-'Z' '_' '-' '$']
let bit = ['0' '1']

rule base = parse
     ws+		{ advance lexbuf; base lexbuf }
   | '\n'		{ nl lexbuf; base lexbuf }
   | ';' ';' 		{ comment lexbuf; base lexbuf }
   | digit alnum*	{ NUMBER (tval' lexbuf int_of_string) }
   | '#' 'b' bit+	{ BITNUMBER (tval' lexbuf bitnumber_of_string) }
   | letter alnum*	{ doident (tval lexbuf) }
   | ':'		{ advance lexbuf; COLON }
   | '.'		{ advance lexbuf; DOT }
   | '='		{ advance lexbuf; EQ }
   | '<'		{ advance lexbuf; LT }
   | '-'		{ advance lexbuf; MINUS }
   | '+'		{ advance lexbuf; PLUS }
   | '('		{ advance lexbuf; LPAREN }
   | ')'		{ advance lexbuf; RPAREN }
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
      | ASSERT ->          "ASSERT"
      | BITVEC ->          "BITVEC"
      | BOOL ->            "BOOL"
      | CHECK_SAT ->       "CHECK_SAT"
      | DECLARE_FUN ->     "DECLARE_FUN"
      | DEFINE_FUN ->      "DEFINE_FUN"
      | EXIT ->            "EXIT"
      | INT ->             "INT"
      | GET_MODEL ->       "GET_MODEL"
      | POP ->             "POP"
      | PUSH ->            "PUSH"
      | SET_OPTION ->      "SET_OPTION"
      | ZERO_EXTEND ->     "ZERO_EXTEND"
      | LPAREN ->          "LPAREN"
      | RPAREN ->          "RPAREN"
      | COLON ->           "COLON"
      | DOT ->             "DOT"
      | EQ ->              "EQ"
      | LT ->              "LT"
      | MINUS ->           "MINUS"
      | PLUS ->            "PLUS"
      | US ->              "US"

let iseof t =
   match t with
        EOF -> true
      | _ -> false

let read = read' base Smtparse.file EOF iseof dumpone (fun x -> x)
}
