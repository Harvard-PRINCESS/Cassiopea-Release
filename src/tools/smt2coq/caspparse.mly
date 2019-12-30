%{
(*
 * Copyright (c) 2017, 2019
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

(*
 * Cassiopeia's smt dump syntax.
 *)

module T = Casptree

let pos () = Pos.fromparser ()

let getop txt = match txt with
   | "or" -> T.LOGOR
   | "and" -> T.LOGAND
   | "not" -> T.LOGNOT
   | "bvor" -> T.BITOR
   | "bvlshr" -> T.BITUSHR
   | "bvshl" -> T.BITSHL
   | "bv2int" -> T.BV2INT
   | "ite" -> T.ITE
   | _ -> Pos.crashat (pos ()) ("Invalid operator " ^ txt)

let mkbitnumber (k, w) =
   T.BITCONST (pos (), k, w)

%}

%token EOF
%token <string> IDENT
%token <int> NUMBER
%token <int * int> BITNUMBER
%token SLICE ZERO_EXTEND
%token LPAREN RPAREN LBRACK RBRACK
%token AMP BANG BAR COLON LT MINUS PLUS
%token AMPAMP BARBAR EQEQ GTGT LTLT
%token B_PLUS B_MINUS B_LT

%type <Casptree.expr> file
%start file

%%

file:
   expr EOF				{ $1 }
;

expr:
     LPAREN IDENT exprs RPAREN		{ OP (pos (), getop $2, List.rev $3) }
   | LPAREN op exprs RPAREN		{ OP (pos (), $2, List.rev $3) }
   | IDENT				{ READVAR (pos (), $1) }
   | BITNUMBER				{ mkbitnumber $1 }
   | NUMBER				{ INTCONST (pos (), $1) }
   | LPAREN expr RPAREN			{ $2 }
;

exprs:
     expr				{ [$1] }
   | exprs expr				{ $2 :: $1 }
;

op:
     AMP				{ BITAND }
   | BANG				{ LOGNOT }
   | BAR				{ BITOR }
   | PLUS				{ ADD }
   | MINUS				{ SUB }
   | LT					{ INTLT }
   | AMPAMP				{ LOGAND }
   | BARBAR				{ LOGOR }
   | EQEQ				{ EQ }
   | GTGT				{ BITSHL }
   | LTLT				{ BITUSHR }
   | B_PLUS				{ T.BITADD }
   | B_MINUS				{ T.BITSUB }
   | B_LT				{ T.BITLT }
   | SLICE LBRACK NUMBER COLON NUMBER RBRACK { SLICE ($3, $5) }
   | ZERO_EXTEND NUMBER			{ T.ZEROEXTEND $2 }
;
