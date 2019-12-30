%{
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

(*
 * AnaGram, a System for Syntax Directed Programming
 * C Macro preprocessor
 * Sample C Grammar
 * Compatible with Kernighan and Ritchie, 2nd. Edition.
 *
 * Copyright 1993-2000 Parsifal Software. All Rights Reserved.
 *
 * This software is provided 'as-is', without any express or implied
 * warranty.  In no event will the authors be held liable for any damages
 * arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 *    claim that you wrote the original software. If you use this software
 *    in a product, an acknowledgment in the product documentation would be
 *    appreciated but is not required.
 * 2. Altered source versions must be plainly marked as such, and must not be
 *    misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 *)


open Pos
module T = Ptree
module A = Lexaux

let pos () = Pos.fromparser ()
let rev = List.rev

(*
 * logic for coping with typedefs
 *)

let hastypedef ds =
   let istypedef d =
      match d with
           T.STORAGECLASS T.TYPEDEF -> true
         | _ -> false
   in
   List.exists istypedef ds

let notypedefs ds =
   if hastypedef ds then
      Pos.failat (pos ()) "Typedefs within blocks are not supported"

let dotypedefs d =
   let rec process_declarator r =
      match r with
           T.DECLABS _pos -> ()
         | T.DECLNAME (pos, name) -> A.mark_typedef pos name
         | T.DECLARRAY (_pos, r', _sz) -> process_declarator r'
         | T.DECLFUNC (_pos, r', _params) -> process_declarator r'
         | T.KRDECLFUNC (_pos, r', _params) -> process_declarator r'
         | T.DECLPOINTER (_pos, _p, r') -> process_declarator r'
         | T.DECLBITFIELD (_pos, Some r', _w) -> process_declarator r'
         | T.DECLBITFIELD (_pos, None, _w) -> ()
         | T.DECLINIT (r', _i) -> process_declarator r'
   in
   begin
   match d with
        T.DECL (_pos, ds, r) ->
           if hastypedef ds then process_declarator r;
      | T.DECLS (_pos, ds, rs) ->
           if hastypedef ds then List.iter process_declarator rs
      | T.MOREPARAMS -> ()
   end;
   d

(*
 * shorthands for tree construction
 *)

(* expressions *)
let e_int s = T.INTCONSTANT (pos (), s)
let e_float s = T.FLOATCONSTANT (pos (), s)
let e_char s = T.CHARCONSTANT (pos (), s)
let e_str s = T.STRCONSTANT (pos (), s)
let e_var s = T.READVAR (pos (), s)
let e_field e s = T.READFIELD (pos (), e, s)
let e_pfield e s = T.READPTRFIELD (pos (), e, s)
let uop op e = T.UOP (pos (), op, e)
let bop e1 op e2 = T.BOP (pos (), e1, op, e2)
let e_call f args = T.CALL (pos (), f, rev args)
let e_esz e = T.ESIZEOF (pos (), e)
let e_sz t = T.SIZEOF (pos (), t)
let e_cast t e = T.CAST (pos (), t, e)
let e_if c t f = T.IFEXPR (pos (), c, t, f)

(* declarations *)
let d_d ds r = notypedefs ds; T.DECL (pos (), rev ds, r)
let d_ds ds rs = notypedefs ds; T.DECLS (pos (), rev ds, rev rs)
let d_gds ds rs = dotypedefs (T.DECLS (pos (), rev ds, rev rs))
let d_enum s = T.ENUMERATOR (pos (), s, None)
let d_enumv s e = T.ENUMERATOR (pos (), s, Some e)
let d_struct_tb t b = T.STRUCT (pos (), Some t, Some (rev b))
let d_struct_t t = T.STRUCT (pos (), Some t, None)
let d_struct_b b = T.STRUCT (pos (), None, Some (rev b))
let d_union_tb t b = T.UNION (pos (), Some t, Some b)
let d_union_t t = T.UNION (pos (), Some t, None)
let d_union_b b = T.UNION (pos (), None, Some b)
let d_enum_tb t b = T.ENUM (pos (), Some t, Some (rev b))
let d_enum_t t = T.ENUM (pos (), Some t, None)
let d_enum_b b = T.ENUM (pos (), None, Some (rev b))
let d_sc sc = T.STORAGECLASS sc
let d_ts ts = T.TYPESPEC ts
let d_tq tq = T.TYPEQUAL tq
let d_ptr0 tqs = T.POINTER (pos (), tqs, None)
let d_ptrN tqs p = T.POINTER (pos (), tqs, Some p)

(* initializers *)
let i_e e = T.INITEXPR (pos (), e)
let i_l is = T.INITLIST (pos (), is)

(* declarators *)
let abs = T.DECLABS (pos ())
let r_name s = T.DECLNAME (pos (), s)
let r_arrayi d = T.DECLARRAY (pos (), d, None)
let r_array d e = T.DECLARRAY (pos (), d, Some e)
let r_func d args = T.DECLFUNC (pos (), d, rev args)
let r_kr d args = T.KRDECLFUNC (pos (), d, rev args)
let r_ptr p d = T.DECLPOINTER (pos (), p, d)
let r_bf d e = T.DECLBITFIELD (pos (), Some d, e)
let r_anonbf e = T.DECLBITFIELD (pos (), None, e)
let r_i d i = T.DECLINIT (d, i)

%}

%token EOF
%token <string> NUMBER FNUMBER QCHAR QSTRING IDENT TYPEDEFNAME

/* reserved words */
%token CALL
%token AUTO EXTERN REGISTER STATIC TYPEDEF
%token CHAR DOUBLE INT FLOAT LONG SHORT SIGNED UNSIGNED VOID
%token ENUM STRUCT UNION
%token CONST RESTRICT VOLATILE
%token SIZEOF

/* grouping punctuation */
%token LBRACE RBRACE LBRACK RBRACK LPAREN RPAREN

/* ordinary punctuation */
%token AMP AMPAMP AMPEQ BANG BANGEQ BAR BARBAR BAREQ CARET CARETEQ COLON
%token COMMA DOT DOTDOTDOT EQ EQEQ GT GTEQ GTGTEQ GTGT
%token LT LTEQ LTLTEQ LTLT MINUS MINUSEQ MINUSGT MINUSMINUS PCT PCTEQ
%token PLUS PLUSEQ PLUSPLUS QUES SEMIC SLASH SLASHEQ STAR STAREQ TILDE

%type <Ptree.decl list> file

%start file

%%

file:
   decl_list EOF		{ rev $1 }
;

decl_list:
     /* nil */			{ [] }
   | decl_list decl		{ $2 :: $1 }
;

decl:
     CALL IDENT SEMIC		{ T.GENCALL (pos (), $2) }
   | c_decl			{ T.CDECL $1 }
;

/**************************************************************/
/* C */

c_decl:
     declaration_specifiers SEMIC			{ d_gds $1 [] }
   | declaration_specifiers init_declarator_list SEMIC	{ d_gds $1 $2 }
;

declaration_specifiers:
     declaration_specifier				{ [$1] }
   | declaration_specifiers declaration_specifier	{ $2 :: $1 }
;

declaration_specifier:
     storage_class_specifier				{ d_sc $1 }
   | type_specifier					{ d_ts $1 }
   | type_qualifier					{ d_tq $1 }
;

storage_class_specifier:
     AUTO						{ T.AUTO }
   | REGISTER						{ T.REGISTER }
   | STATIC						{ T.STATIC }
   | EXTERN						{ T.EXTERN }
   | TYPEDEF						{ T.TYPEDEF }
;

type_specifier:
     VOID						{ T.VOID }
   | CHAR						{ T.CHAR }
   | SHORT						{ T.SHORT }
   | INT						{ T.INT }
   | LONG						{ T.LONG }
   | FLOAT						{ T.FLOAT }
   | DOUBLE						{ T.DOUBLE }
   | SIGNED						{ T.SIGNED }
   | UNSIGNED						{ T.UNSIGNED }
   | struct_or_union_specifier				{ $1 }
   | enum_specifier					{ $1 }
   | TYPEDEFNAME					{ T.USETYPEDEF $1 }
;

type_qualifier:
     CONST						{ T.CONST }
   | VOLATILE						{ T.VOLATILE }
   | RESTRICT						{ T.RESTRICT }
;

struct_or_union_specifier:
     STRUCT IDENT LBRACE struct_declaration_list RBRACE	{ d_struct_tb $2 $4 }
   | STRUCT LBRACE struct_declaration_list RBRACE	{ d_struct_b $3 }
   | STRUCT IDENT					{ d_struct_t $2 }
   | UNION IDENT LBRACE struct_declaration_list RBRACE	{ d_union_tb $2 $4 }
   | UNION LBRACE struct_declaration_list RBRACE	{ d_union_b $3 }
   | UNION IDENT					{ d_union_t $2 }
;

struct_declaration_list:
     struct_declaration					{ [$1] }
   | struct_declaration_list struct_declaration		{ $2 :: $1 }
;

init_declarator:
     declarator						{ $1 }
   | declarator EQ initializer_				{ r_i $1 $3 }
;

init_declarator_list:
     init_declarator					{ [$1] }
   | init_declarator_list COMMA init_declarator		{ $3 :: $1 }
;

struct_declaration:
   specifier_qualifier_list struct_declarator_list SEMIC { d_ds $1 $2 }
;

specifier_qualifier_list:
     specifier_qualifier				{ [$1] }
   | specifier_qualifier_list specifier_qualifier	{ $2 :: $1 }
;

specifier_qualifier:
     type_specifier					{ d_ts $1 }
   | type_qualifier					{ d_tq $1 }
;

struct_declarator_list:
     struct_declarator					{ [$1] }
   | struct_declarator_list COMMA struct_declarator	{ $3 :: $1 }
;

struct_declarator:
     declarator						{ $1 }
   | declarator COLON constant_expression		{ r_bf $1 $3 }
   | COLON constant_expression				{ r_anonbf $2 }
;

enum_specifier:
     ENUM IDENT LBRACE enumerator_list RBRACE		{ d_enum_tb $2 $4 }
   | ENUM LBRACE enumerator_list RBRACE			{ d_enum_b $3 }
   | ENUM IDENT						{ d_enum_t $2 }
;

enumerator_list:
     enumerator						{ [$1] }
   | enumerator_list COMMA enumerator			{ $3 :: $1 }
;

enumerator:
     IDENT						{ d_enum $1 }
   | IDENT EQ constant_expression			{ d_enumv $1 $3 }
;

declarator:
     direct_declarator					{ $1 }
   | pointer direct_declarator				{ r_ptr $1 $2 }
;

direct_declarator:
   | IDENT						{ r_name $1 }
   | LPAREN declarator RPAREN				{ $2 }
   | direct_declarator LBRACK RBRACK			{ r_arrayi $1 }
   | direct_declarator LBRACK constant_expression RBRACK { r_array $1 $3 }
   | direct_declarator LPAREN parameter_type_list RPAREN { r_func $1 $3 }
   | direct_declarator LPAREN RPAREN			{ r_kr $1 [] }
   | direct_declarator LPAREN identifier_list RPAREN	{ r_kr $1 $3 }
;

pointer:
     STAR type_qualifier_list				{ d_ptr0 $2 }
   | STAR type_qualifier_list pointer			{ d_ptrN $2 $3 }
;

type_qualifier_list:
     /* nil */						{ [] }
   | type_qualifier_list type_qualifier			{ $2 :: $1 }
;

parameter_type_list:
     parameter_list					{ $1 }
   | parameter_list COMMA DOTDOTDOT			{ T.MOREPARAMS :: $1 }
;

parameter_list:
     parameter_declaration				{ [$1] }
   | parameter_list COMMA parameter_declaration		{ $3 :: $1 }
;

parameter_declaration:
     declaration_specifiers				{ d_d $1 abs }
   | declaration_specifiers abstract_declarator		{ d_d $1 $2 }
   | declaration_specifiers declarator			{ d_d $1 $2 }
;

identifier_list:
     IDENT						{ [$1] }
   | identifier_list COMMA IDENT			{ $3 :: $1 }
;

initializer_:
     assignment_expression				{ i_e $1 }
   | LBRACE initializer_list RBRACE			{ i_l $2 }
   | LBRACE initializer_list COMMA RBRACE		{ i_l $2 }
;

initializer_list:
     initializer_					{ [$1] }
   | initializer_list COMMA initializer_		{ $3 :: $1 }
;

type_name:
     specifier_qualifier_list				{ d_d $1 abs }
   | specifier_qualifier_list abstract_declarator	{ d_d $1 $2 }
;

abstract_declarator:
     pointer						{ r_ptr $1 abs }
   | direct_abstract_declarator				{ $1 }
   | pointer direct_abstract_declarator			{ r_ptr $1 $2 }
;

direct_abstract_declarator:
     LPAREN abstract_declarator RPAREN			{ $2 }
   | LBRACK RBRACK					{ r_arrayi abs }
   | LBRACK constant_expression RBRACK			{ r_array abs $2 }
   | direct_abstract_declarator LBRACK RBRACK		{ r_arrayi $1 }
   | direct_abstract_declarator LBRACK constant_expression RBRACK
	{ r_array $1 $3 }
   | LPAREN parameter_type_list RPAREN			{ r_func abs $2 }
   | LPAREN RPAREN					{ r_kr abs [] }
   | direct_abstract_declarator LPAREN parameter_type_list RPAREN
	{ r_func $1 $3 }
   | direct_abstract_declarator LPAREN RPAREN		{ r_kr $1 [] }
;

expression:
     assignment_expression				{ $1 }
   | expression COMMA assignment_expression		{ bop $1 T.SEQ $3 }
;

assignment_expression:
     conditional_expression				{ $1 }
   | unary_expression assignment_op assignment_expression { bop $1 $2 $3 }
;

assignment_op:
     EQ							{ T.ASSIGN }
   | STAREQ						{ T.MULASSIGN }
   | SLASHEQ						{ T.DIVASSIGN }
   | PCTEQ						{ T.MODASSIGN }
   | PLUSEQ						{ T.ADDASSIGN }
   | MINUSEQ						{ T.SUBASSIGN }
   | LTLTEQ						{ T.LSHIFTASSIGN }
   | GTGTEQ						{ T.RSHIFTASSIGN }
   | AMPEQ						{ T.BITANDASSIGN }
   | BAREQ						{ T.BITORASSIGN }
   | CARETEQ						{ T.BITXORASSIGN }
;

conditional_expression:
     logor_expression					{ $1 }
   | logor_expression QUES expression COLON conditional_expression
	{ e_if $1 $3 $5 }
;

constant_expression:
   conditional_expression				{ $1 }
;

logor_expression:
     logand_expression					{ $1 }
   | logor_expression BARBAR logand_expression		{ bop $1 T.LOGOR $3 }
;

logand_expression:
     bitor_expression					{ $1 }
   | logand_expression AMPAMP bitor_expression		{ bop $1 T.LOGAND $3 }
;

bitor_expression:
     bitxor_expression					{ $1 }
   | bitor_expression BAR bitxor_expression		{ bop $1 T.BITOR $3 }
;

bitxor_expression:
     bitand_expression					{ $1 }
   | bitxor_expression CARET bitand_expression		{ bop $1 T.BITXOR $3 }
;

bitand_expression:
     equality_expression				{ $1 }
   | bitand_expression AMP equality_expression		{ bop $1 T.BITAND $3 }
;

equality_expression:
     relational_expression				{ $1 }
   | equality_expression EQEQ relational_expression	{ bop $1 T.EQ $3 }
   | equality_expression BANGEQ relational_expression	{ bop $1 T.NEQ $3 }
;

relational_expression:
     shift_expression					{ $1 }
   | relational_expression LT shift_expression 		{ bop $1 T.LT $3 }
   | relational_expression GT shift_expression 		{ bop $1 T.GT $3 }
   | relational_expression LTEQ shift_expression 	{ bop $1 T.LTEQ $3 }
   | relational_expression GTEQ shift_expression 	{ bop $1 T.GTEQ $3 }
;

shift_expression:
     additive_expression				{ $1 }
   | shift_expression LTLT additive_expression 		{ bop $1 T.LSHIFT $3 }
   | shift_expression GTGT additive_expression 		{ bop $1 T.RSHIFT $3 }
;

additive_expression:
     multiplicative_expression				{ $1 }
   | additive_expression PLUS multiplicative_expression { bop $1 T.ADD $3 }
   | additive_expression MINUS multiplicative_expression { bop $1 T.SUB $3 }
;

multiplicative_expression:
     cast_expression					{ $1 }
   | multiplicative_expression STAR cast_expression 	{ bop $1 T.MUL $3 }
   | multiplicative_expression SLASH cast_expression	{ bop $1 T.DIV $3 }
   | multiplicative_expression PCT cast_expression 	{ bop $1 T.MOD $3 }
;

cast_expression:
     unary_expression					{ $1 }
   | LPAREN type_name RPAREN cast_expression		{ e_cast $2 $4 }
;

unary_expression:
     postfix_expression					{ $1 }
   | unary_operator cast_expression			{ uop $1 $2 }
   | PLUS cast_expression				{ $2 }
   | SIZEOF unary_expression				{ e_esz $2 }
   | SIZEOF LPAREN type_name RPAREN			{ e_sz $3 }
;

unary_operator:
     AMP						{ T.ADDROF }
   | STAR						{ T.INDIR }
   | MINUS						{ T.NEG }
   | TILDE						{ T.BITNOT }
   | BANG						{ T.LOGNOT }
   | PLUSPLUS						{ T.PREINC }
   | MINUSMINUS						{ T.PREDEC }
;

postfix_expression:
     primary_expression					{ $1 }
   | postfix_expression LBRACK expression RBRACK      { bop $1 T.READARRAY $3 }
   | postfix_expression LPAREN RPAREN			{ e_call $1 [] }
   | postfix_expression LPAREN argument_expression_list RPAREN { e_call $1 $3 }
   | postfix_expression DOT IDENT			{ e_field $1 $3 }
   | postfix_expression MINUSGT IDENT			{ e_pfield $1 $3 }
   | postfix_expression PLUSPLUS			{ uop T.POSTINC $1 }
   | postfix_expression MINUSMINUS			{ uop T.POSTDEC $1 }
;

primary_expression:
     IDENT						{ e_var $1 }
   | NUMBER						{ e_int $1 }
   | FNUMBER						{ e_float $1 }
   | QCHAR						{ e_char $1 }
   | QSTRING						{ e_str $1 }
   | LPAREN expression RPAREN				{ $2 }
;

argument_expression_list:
     assignment_expression				{ [$1] }
   | argument_expression_list COMMA assignment_expression { $3 :: $1 }
;
