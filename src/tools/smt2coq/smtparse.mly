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
 * smtlib files.
 *)

module T = Smttree

let pos () = Pos.fromparser ()

let getop txt = match txt with
   | "or" -> T.LOGOR
   | "and" -> T.LOGAND
   | "not" -> T.LOGNOT
   | "bvadd" -> T.BITADD
   | "bvsub" -> T.BITSUB
   | "bvor" -> T.BITOR
   | "bvlshr" -> T.BITUSHR
   | "bvshl" -> T.BITSHL
   | "bv2int" -> T.BV2INT
   | "ite" -> T.ITE
   | _ -> Pos.crashat (pos ()) ("Invalid operator " ^ txt)

let getbool txt = match txt with
   | "true" -> true
   | "false" -> false
   | _ -> Pos.crashat (pos ()) ("Invalid boolean constant " ^ txt)

let mkbitnumber (k, w) =
   T.CONST (pos (), k, BV (pos (), w))

%}

%token EOF
%token <string> IDENT
%token <int> NUMBER
%token <int * int> BITNUMBER
%token ASSERT BITVEC BOOL CHECK_SAT DECLARE_FUN DEFINE_FUN EXIT INT GET_MODEL
%token POP PUSH SET_OPTION ZERO_EXTEND
%token LPAREN RPAREN
%token COLON DOT EQ LT MINUS PLUS US

%type <Smttree.stmt list> file
%start file

%%

file:
   statements EOF			{ List.rev $1 }
;

statements:
   /* nil */				{ [] }
   | statements pstatement		{ $2 :: $1 }
;

pstatement:
   LPAREN statement RPAREN		{ $2 }
;

statement:
     DECLARE_FUN IDENT unit typename	{ DECLARE_FUN (pos (), $2, $4) }
   | DEFINE_FUN IDENT unit typename expr { DEFINE_FUN (pos (), $2, $4, $5) }
   | ASSERT expr			{ ASSERT (pos (), $2) }
   | PUSH 				{ PUSH (pos ()) }
   | POP				{ POP (pos ()) }
   | CHECK_SAT				{ CHECK_SAT (pos ()) }
   | GET_MODEL				{ GET_MODEL (pos ()) }
   | SET_OPTION option_ boolconst	{ SET_OPTION (pos (), $2, $3) }
   | EXIT				{ T.EXIT (pos ()) }
;

unit:
   LPAREN RPAREN			{ () }
;

option_:
     COLON IDENT			{ ":" ^ $2 }
   | COLON IDENT DOT IDENT		{ ":" ^ $2 ^ "." ^ $4 }

expr:
     LPAREN IDENT exprs RPAREN		{ OP (pos (), getop $2, List.rev $3) }
   | LPAREN op exprs RPAREN		{ OP (pos (), $2, List.rev $3) }
   | IDENT				{ READVAR (pos (), $1) }
   | BITNUMBER				{ mkbitnumber $1 }
   | NUMBER				{ CONST (pos (), $1, INT (pos ())) }
;

exprs:
     /* nil */				{ [] }
   | exprs expr				{ $2 :: $1 }
;

op:
     PLUS				{ T.ADD }
   | MINUS				{ T.SUB }
   | LT					{ T.LT }
   | EQ					{ T.EQ }
   | LPAREN US ZERO_EXTEND NUMBER RPAREN { T.ZEROEXTEND $4 }
;

boolconst:
   IDENT				{ getbool $1 }
;
    
typename:
     BOOL				{ T.BOOL (pos ()) }
   | INT				{ T.INT (pos ()) }
   | LPAREN US BITVEC NUMBER RPAREN	{ T.BV (pos (), $4) }
;
