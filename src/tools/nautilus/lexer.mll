(*
 * Copyright (c) 2016, 2017, 2018
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

(* prologue code *)
{
open Pos
open Lextools
open Parser

(* identifiers and keywords *)


let keywords = Types.stringmap_of_list [
   ("call", CALL);
   ("auto", AUTO);
   ("extern", EXTERN);
   ("register", REGISTER);
   ("static", STATIC);
   ("typedef", TYPEDEF);
   ("char", CHAR);
   ("double", DOUBLE);
   ("int", INT);
   ("float", FLOAT);
   ("long", LONG);
   ("short", SHORT);
   ("signed", SIGNED);
   ("unsigned", UNSIGNED);
   ("void", VOID);
   ("enum", ENUM);
   ("struct", STRUCT);
   ("union", UNION);
   ("const", CONST);
   ("restrict", RESTRICT);
   ("volatile", VOLATILE);
   ("sizeof", SIZEOF);
]
let doident =
   let mkident x =
      if Lexaux.is_typedef x then TYPEDEFNAME x else IDENT x
   in
   doident' keywords mkident

(* end of prologue code *)
}

(* common patterns *)

let ws = [' ' '\t']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z' '_']
let alnum = ['0'-'9' 'a'-'z' 'A'-'Z' '_']
let exp = ['e' 'E' 'a' 'A']
let sign = ['+' '-']

(* states *)
rule base = parse
     ws+		{ advance lexbuf; base lexbuf }
   | '\n'		{ nl lexbuf; base lexbuf }
   | '/' '*'		{ startcomment lexbuf; comment lexbuf; base lexbuf }
   | '"' 		{ startstring lexbuf; strconst lexbuf }
   | '\'' 		{ startstring lexbuf; charconst lexbuf }
   | '.' digit+				{ FNUMBER (tval lexbuf) }
   | '.' digit+ exp sign? digit+	{ FNUMBER (tval lexbuf) }
   | digit+ '.' digit*			{ FNUMBER (tval lexbuf) }
   | digit+ '.' digit* exp sign? digit+ { FNUMBER (tval lexbuf) }
   | digit alnum*	{ NUMBER (tval lexbuf) }
   | letter alnum*	{ doident (tval lexbuf) }
   | '&' '&'		{ advance lexbuf; AMPAMP }
   | '&' '='		{ advance lexbuf; AMPEQ }
   | '!' '='		{ advance lexbuf; BANGEQ }
   | '|' '|'		{ advance lexbuf; BARBAR }
   | '|' '='		{ advance lexbuf; BAREQ }
   | '^' '='		{ advance lexbuf; CARETEQ }
   | '.' '.' '.'	{ advance lexbuf; DOTDOTDOT }
   | '=' '='		{ advance lexbuf; EQEQ }
   | '>' '='		{ advance lexbuf; GTEQ }
   | '>' '>' '='	{ advance lexbuf; GTGTEQ }
   | '>' '>'		{ advance lexbuf; GTGT }
   | '<' '='		{ advance lexbuf; LTEQ }
   | '<' '<' '='	{ advance lexbuf; LTLTEQ }
   | '<' '<'		{ advance lexbuf; LTLT }
   | '-' '='		{ advance lexbuf; MINUSEQ }
   | '-' '>'		{ advance lexbuf; MINUSGT }
   | '-' '-'		{ advance lexbuf; MINUSMINUS }
   | '%' '='		{ advance lexbuf; PCTEQ }
   | '+' '='		{ advance lexbuf; PLUSEQ }
   | '+' '+'		{ advance lexbuf; PLUSPLUS }
   | '/' '='		{ advance lexbuf; SLASHEQ }
   | '*' '='		{ advance lexbuf; STAREQ }
   | '&'		{ advance lexbuf; AMP }
   | '!'		{ advance lexbuf; BANG }
   | '|'		{ advance lexbuf; BAR }
   | '^'		{ advance lexbuf; CARET }
   | ':'		{ advance lexbuf; COLON }
   | ','		{ advance lexbuf; COMMA }
   | '.'		{ advance lexbuf; DOT }
   | '='		{ advance lexbuf; EQ }
   | '>'		{ advance lexbuf; GT }
   | '<'		{ advance lexbuf; LT }
   | '-'		{ advance lexbuf; MINUS }
   | '%'		{ advance lexbuf; PCT }
   | '+'		{ advance lexbuf; PLUS }
   | '?'		{ advance lexbuf; QUES }
   | ';'		{ advance lexbuf; SEMIC }
   | '/'		{ advance lexbuf; SLASH }
   | '*'		{ advance lexbuf; STAR }
   | '~'		{ advance lexbuf; TILDE }
   | '('		{ advance lexbuf; LPAREN }
   | ')'		{ advance lexbuf; RPAREN }
   | '['		{ advance lexbuf; LBRACK }
   | ']'		{ advance lexbuf; RBRACK }
   | '{'		{ advance lexbuf; LBRACE }
   | '}'		{ advance lexbuf; RBRACE }
   | _			{ badchar (posval lexbuf); base lexbuf }
   | eof		{ EOF }

and strconst = parse
     [ ^ '\\' '"' '\n' ]+ { addstring (tval lexbuf); strconst lexbuf }
   | '\\' '"'		{ addchar '"'; advance lexbuf; strconst lexbuf }
   | '"'		{ advance lexbuf; QSTRING (getstring ()) }  (* done *)
   | '\n'		{ badstring (pos lexbuf); QSTRING (getstring ())}

and charconst = parse
     [ ^ '\'' '\n' ]+	{ addstring (tval lexbuf); charconst lexbuf }
   | '\\' '\''		{ addchar '\''; advance lexbuf; charconst lexbuf }
   | '\''		{ advance lexbuf; QCHAR (getstring ()) }  (* done *)
   | '\n'		{ badstring (pos lexbuf); QCHAR (getstring ())}

(* this needs to be its own state to defeat the longest-match rule *)
and comment = parse
     '*' '/'		{ advance lexbuf (* done *) }
   | '\n'		{ nl lexbuf; comment lexbuf }
   | eof		{ advance lexbuf; badcomment (pos lexbuf) }
   | _			{ advance lexbuf; comment lexbuf }

(* trailer code *)
{

let dumpone t =
   match t with
        EOF ->             "EOF"
      | QSTRING s ->       ("QSTRING " ^ s)
      | QCHAR s ->         ("QCHAR " ^ s)
      | NUMBER s ->        ("NUMBER " ^ s)
      | FNUMBER s ->       ("FNUMBER " ^ s)
      | IDENT x ->         ("IDENT " ^ x)
      | TYPEDEFNAME x ->   ("TYPEDEFNAME " ^ x)
      | CALL ->            ("CALL")
      | AUTO ->            ("AUTO")
      | EXTERN ->          ("EXTERN")
      | REGISTER ->        ("REGISTER")
      | STATIC ->          ("STATIC")
      | TYPEDEF ->         ("TYPEDEF")
      | CHAR ->            ("CHAR")
      | DOUBLE ->          ("DOUBLE")
      | INT ->             ("INT")
      | FLOAT ->           ("FLOAT")
      | LONG ->            ("LONG")
      | SHORT ->           ("SHORT")
      | SIGNED ->          ("SIGNED")
      | UNSIGNED ->        ("UNSIGNED")
      | VOID ->            ("VOID")
      | ENUM ->            ("ENUM")
      | STRUCT ->          ("STRUCT")
      | UNION ->           ("UNION")
      | CONST ->           ("CONST")
      | RESTRICT ->        ("RESTRICT")
      | VOLATILE ->        ("VOLATILE")
      | SIZEOF ->          ("SIZEOF")
      | AMPAMP ->          ("AMPAMP")
      | AMPEQ ->           ("AMPEQ")
      | BANGEQ ->          ("BANGEQ")
      | BARBAR ->          ("BARBAR")
      | BAREQ ->           ("BAREQ")
      | CARETEQ ->         ("CARETEQ")
      | DOTDOTDOT ->       ("DOTDOTDOT")
      | EQEQ ->            ("EQEQ")
      | GTEQ ->            ("GTEQ")
      | GTGTEQ ->          ("GTGTEQ")
      | GTGT ->            ("GTGT")
      | LTEQ ->            ("LTEQ")
      | LTLTEQ ->          ("LTLTEQ")
      | LTLT ->            ("LTLT")
      | MINUSEQ ->         ("MINUSEQ")
      | MINUSGT ->         ("MINUSGT")
      | MINUSMINUS ->      ("MINUSMINUS")
      | PCTEQ ->           ("PCTEQ")
      | PLUSEQ ->          ("PLUSEQ")
      | PLUSPLUS ->        ("PLUSPLUS")
      | SLASHEQ ->         ("SLASHEQ")
      | STAREQ ->          ("STAREQ")
      | AMP ->             ("AMP")
      | BANG ->            ("BANG")
      | BAR ->             ("BAR")
      | CARET ->           ("CARET")
      | COLON ->           ("COLON")
      | COMMA ->           ("COMMA")
      | DOT ->             ("DOT")
      | EQ ->              ("EQ")
      | GT ->              ("GT")
      | LT ->              ("LT")
      | MINUS ->           ("MINUS")
      | PCT ->             ("PCT")
      | PLUS ->            ("PLUS")
      | QUES ->            ("QUES")
      | SEMIC ->           ("SEMIC")
      | SLASH ->           ("SLASH")
      | STAR ->            ("STAR")
      | TILDE ->           ("TILDE")
      | LPAREN ->          ("LPAREN")
      | RPAREN ->          ("RPAREN")
      | LBRACK ->          ("LBRACK")
      | RBRACK ->          ("RBRACK")
      | LBRACE ->          ("LBRACE")
      | RBRACE ->          ("RBRACE")

let iseof t =
   match t with
        EOF -> true
      | _ -> false

let read = read' base Parser.file iseof dumpone (fun t -> t)
}
