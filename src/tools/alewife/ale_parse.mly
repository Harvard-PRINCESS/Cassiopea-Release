%{
open Util
open Lexing

module Bat = Batteries
module A   = Ale_ast

(*
 * c is an integer constant; w is the bitvector width it's supposed to
 * have. But it might be symbolic so we can't just make a bits; instead
 * emit a call to bv_to_len.
 *)
let widen w c =
   match w with
   | A.ConcWidth w' ->
        let w'' =
           if Big_int.is_int_big_int w' then Big_int.int_of_big_int w'
           else failwith ("Ridiculous constant width " ^ Big_int.string_of_big_int w')
        in
        A.Atomic (A.Vec (Bits.of_big_int w'' c))
   | A.SymWidth x ->
        (*
         * sleazy: generate a maximum-width bitvector regardless of the
         * actual value, and let bv_to_len truncate it. Assume that
         * maximum width is 64.
         *)
        let c' = A.Atomic (A.Vec (Bits.of_big_int 64 c)) in
        let w' = A.Atomic (A.Id x) in
        A.App ("bv_to_len", [w'; c'])

%}

%token <string> ID
/* %token <string> STRINGLIT */
%token <Util.bint> DECNUM
%token <Bits.t> HEXNUM
%token <Bits.t> BITNUM
/*%token <int> CONST*/
%token EOF LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET
%token COMMA COLON /* SEMIC */
%token PLUS MINUS STAR SLASH EQ LT GT AMPAMP PIPEPIPE CARETCARET AMP PIPE CARET BANG TILDE LTLT GTGT EQEQ BANGEQ IMPLY
%token BOOL TRUE FALSE INT BIT VEC PTR REG READ
%token REQUIRE PROVIDE TYPE VALUE FUNCTION
%token BLOCK LABEL REGION LEN REF WITH MODIFYREG MODIFYMEM INVARIANT LET IN IF THEN ELSE PRE POST

%type <Ale_ast.t> file
%start file

%%

file :
  rs=requires ps=provides bl=block EOF { (rs, ps, bl) }

type_args:
    /* nil */            	{ [] }
  | nonempty_type_args		{ $1 }
;

nonempty_type_args:
    t=typ	     	        { [t] }
  | ts=type_args COMMA t=typ    { ts @ [t] }
;

typ :
    i=ID  { A.AbsType (i) }
  | BOOL  { A.BoolType }
  | INT   { A.IntType }
  | bitsize LABEL { A.LblType $1 }
  | BIT   { A.BitType  }
  | bitsize VEC   { A.VecType $1 }
  | bitsize PTR   { A.PtrType $1 }
  | bitsize REG   { A.RegType $1 }
  | LPAREN args=type_args RPAREN t=typ {A.FunType (args, t)}
;

bitsize:
    /* nil */					{ A.SymWidth "wordsize" }
  | i=ID					{ A.SymWidth i }
  | c=DECNUM					{ A.ConcWidth c }
;

/**************************************************************/
/* expressions */
expr:
  if_expr   { $1 }

if_expr:
    imply_expr                                  { $1 }
  | imply_Lexpr                                 { $1 }
  | IF e1=expr THEN e2=expr ELSE e3=expr        { A.IfE (e1, e2, e3) }

imply_expr:
  | logor_expr                                  { $1 }
  | e1=imply_expr IMPLY e2=logor_expr           { A.Implies (e1, e2) }

imply_Lexpr:
  | logor_Lexpr                                 { $1 }
  | e1=imply_expr IMPLY e2=logor_Lexpr          { A.Implies (e1, e2) }

logor_expr:
  | logxor_expr                                 { $1 }
  | e1=logor_expr PIPEPIPE e2=logxor_expr       { A.Binop (e1, LogOr, e2) }

logor_Lexpr:
  | logxor_Lexpr                                { $1 }
  | e1=logor_expr PIPEPIPE e2=logxor_Lexpr      { A.Binop (e1, LogOr, e2) }

logxor_expr:
  | logand_expr                                 { $1 }
  | e1=logxor_expr CARETCARET e2=logand_expr    { A.Binop (e1, LogXor, e2) }

logxor_Lexpr:
  | logand_Lexpr                                { $1 }
  | e1=logxor_expr CARETCARET e2=logand_Lexpr   { A.Binop (e1, LogXor, e2) }

logand_expr:
  | bitor_expr                                  { $1 }
  | e1=logand_expr AMPAMP e2=bitor_expr         { A.Binop (e1, LogAnd, e2) }

logand_Lexpr:
  | bitor_Lexpr                                 { $1 }
  | e1=logand_expr AMPAMP e2=bitor_Lexpr        { A.Binop (e1, LogAnd, e2) }

bitor_expr:
  | bitxor_expr                                 { $1 }
  | e1=bitor_expr PIPE e2=bitxor_expr           { A.Binop (e1, BitOr, e2) }

bitor_Lexpr:
  | bitxor_Lexpr                                { $1 }
  | e1=bitor_expr PIPE e2=bitxor_Lexpr          { A.Binop (e1, BitOr, e2) }

bitxor_expr:
  | bitand_expr                                 { $1 }
  | e1=bitxor_expr CARET e2=bitand_expr         { A.Binop (e1, BitXor, e2) }

bitxor_Lexpr:
  | bitand_Lexpr                                { $1 }
  | e1=bitxor_expr CARET e2=bitand_Lexpr        { A.Binop (e1, BitXor, e2) }

bitand_expr:
  | eq_expr                                     { $1 }
  | e1=bitand_expr AMP e2=eq_expr               { A.Binop (e1, BitAnd, e2) }

bitand_Lexpr:
  | eq_Lexpr                                    { $1 }
  | e1=bitand_expr AMP e2=eq_Lexpr              { A.Binop (e1, BitAnd, e2) }

eq_expr:
  | compare_expr                                { $1 }
  | e1=eq_expr EQEQ e2=compare_expr             { A.Binop (e1, Eq, e2) }
  | e1=eq_expr BANGEQ e2=compare_expr           { A.Binop (e1, Neq, e2) }

eq_Lexpr:
  | compare_Lexpr                               { $1 }
  | e1=eq_expr EQEQ e2=compare_Lexpr            { A.Binop (e1, Eq, e2) }
  | e1=eq_expr BANGEQ e2=compare_Lexpr          { A.Binop (e1, Neq, e2) }

compare_expr:
  | shift_expr                                  { $1 }
  | e1=compare_expr LT e2=shift_expr            { A.Binop (e1, Lt, e2) }
  | e1=compare_expr GT e2=shift_expr            { A.Binop (e1, Gt, e2) }

compare_Lexpr:
  | shift_Lexpr                                 { $1 }
  | e1=compare_expr LT e2=shift_Lexpr           { A.Binop (e1, Lt, e2) }
  | e1=compare_expr GT e2=shift_Lexpr           { A.Binop (e1, Gt, e2) }

shift_expr:
  | add_expr                                    { $1 }
  | e1=shift_expr LTLT e2=add_expr              { A.Binop (e1, LShift, e2) }
  | e1=shift_expr GTGT e2=add_expr              { A.Binop (e1, RShift, e2) }

shift_Lexpr:
  | add_Lexpr                                   { $1 }
  | e1=shift_expr LTLT e2=add_Lexpr             { A.Binop (e1, LShift, e2) }
  | e1=shift_expr GTGT e2=add_Lexpr             { A.Binop (e1, RShift, e2) }

add_expr:
  | mul_expr                                    { $1 }
  | e1=add_expr PLUS e2=mul_expr                { A.Binop (e1, Add, e2) }
  | e1=add_expr MINUS e2=mul_expr               { A.Binop (e1, Sub, e2) }

add_Lexpr:
  | mul_Lexpr                                   { $1 }
  | e1=add_expr PLUS e2=mul_Lexpr               { A.Binop (e1, Add, e2) }
  | e1=add_expr MINUS e2=mul_Lexpr              { A.Binop (e1, Sub, e2) }

mul_expr:
  | prefix_expr                                 { $1 }
  | e1=mul_expr STAR e2=prefix_expr             { A.Binop (e1, Mul, e2) }
  | e1=mul_expr SLASH e2=prefix_expr            { A.Binop (e1, Div, e2) }

mul_Lexpr:
  | base_Lexpr                                  { $1 }
  | e1=mul_expr STAR e2=prefix_Lexpr            { A.Binop (e1, Mul, e2) }
  | e1=mul_expr SLASH e2=prefix_Lexpr           { A.Binop (e1, Div, e2) }

prefix_expr:
  | star_expr                                   { $1 }
  | MINUS e=prefix_expr                         { A.Unop (Neg, e)}
  | BANG  e=prefix_expr                         { A.Unop (LogNot, e) }
  | TILDE e=prefix_expr                         { A.Unop (BitNot, e) }

prefix_Lexpr:
  | base_Lexpr                                  { $1 }
  | MINUS e=prefix_Lexpr                        { A.Unop (Neg, e) }
  | BANG  e=prefix_Lexpr                        { A.Unop (LogNot, e) }
  | TILDE e=prefix_Lexpr                        { A.Unop (BitNot, e) }

star_expr:
  | bv_expr                                     { $1 }
  | STAR e=star_expr                            { A.Deref e }

bv_expr:
  | base_expr                                   { $1 }
  | e1=base_expr LBRACKET e2=base_expr RBRACKET { A.Index (e1, e2) }
  | e1=base_expr LBRACKET e2=base_expr COLON e3=base_expr RBRACKET { A.Slice (e1, e2, e3) }

base_expr:
  | a=semiatomic                                  { a }
  | READ LBRACKET e=expr RBRACKET                 { A.Fetch e }
  | i=ID LPAREN ee=expr_args RPAREN               { A.App (i, ee) }
/*  | LBRACE i=ID RBRACE                            { A.Label(i) } */
  | LPAREN e=expr RPAREN                          { e }

base_Lexpr:
  | LET i=ID COLON t=typ EQ e1=expr IN e2=expr  { A.LetE (i, t, e1, e2) }
;

semiatomic:
    a=atomic                                      { A.Atomic a }
  | LPAREN c=DECNUM COLON w=bitsize VEC RPAREN    { widen w c }
;

atomic :
    c=DECNUM { A.Int (c) }
  | h=HEXNUM { A.Vec (h) }
  | b=BITNUM { A.Vec (b) }
  | TRUE { A.Bool (true) }
  | FALSE { A.Bool (false) }
  | i=ID { A.Id (i) }
  | LBRACKET i=ID COMMA o=DECNUM RBRACKET { A.Ptr (i, o) } /* ptr: [id, offset] */

expr_args :
    /* nil */                     { [] }
  | nonempty_args                 { $1 }

nonempty_args:
  | a=expr                        { [a] }
  | aa=nonempty_args COMMA a=expr { aa @ [a] }

/**************************************************************/
/* requires */
requires : 
    /* nil */              { [] }
  | rs=requires r=require  { rs @ [r] }

require :
    REQUIRE TYPE i=ID                   { A.RequireType (i) }
  | REQUIRE VALUE i=ID COLON t=typ      { A.RequireVal (i, t) }
  | REQUIRE FUNCTION i=ID COLON t=typ   { A.RequireFunc (i, t) }

/**************************************************************/
/* provides */
provides : 
    /* nil */              { [] }
  | ps=provides p=provide  { ps @ [p] }

provide :
    PROVIDE TYPE i=ID EQ t=typ                               { A.ProvideType (i, t)}
  | PROVIDE VALUE i=ID COLON t=typ EQ e=expr                 { A.ProvideVal (i, t, e) }
  | PROVIDE FUNCTION i=ID LPAREN ps=params RPAREN COLON t=typ EQ e=expr   { A.ProvideFunc (i, ps, t, e)}

params :
    /* nil */             { [] }
  | ps=params p=param     { ps @ [p] }

param :
    LPAREN i=ID COLON t=typ RPAREN
  | i=ID COLON t=typ                { (i, t) }


/**************************************************************/
/* block */
block :
    /* nil */                             { None }
  | BLOCK i=ID LBRACE sp=block_spec RBRACE  { Some (i, sp) }

block_spec :
  f=frames l=block_lets PRE COLON pre=expr POST COLON post=expr
    { (f, l, pre, post) }

/**************************************************************/
/* frame */
frames : 
    /* nil */               { [] }
  | fs=frames f=frame       { fs @ [f] }

frame :
    REGION i1=ID COLON b=bitsize BIT l=bitsize LEN r=bitsize REF WITH i2=ID
      { A.FrameLabel (i1, b, l, r, i2) }
  | REGION i=ID COLON b=bitsize BIT l=bitsize LEN r=bitsize REF      
      { A.FrameRegion (i, b, l, r) }
  | MODIFYREG COLON m=idlist      { A.FrameModifyReg m }
  | MODIFYMEM COLON m=ptrlist     { A.FrameModifyMem m }
  | INVARIANT COLON e=expr        { A.FrameInvariant e }

idlist:
    ID                { [$1] }
  | ids=idlist i=ID   { ids @ [i] }

ptrone:
    LBRACKET i=ID COMMA o=bitsize RBRACKET { (i, o) }

ptrlist:
    ptrone                 { [$1] }
  | ps=ptrlist p=ptrone     { ps @ [p]}


/**************************************************************/
/* lets */
block_lets :
    /* nil */ { [] }
  | bls=block_lets bl=block_let   { bls @ [bl] }

block_let : 
    LET LPAREN i=ID COLON t=typ RPAREN EQ e=expr
  | LET i=ID COLON t=typ EQ e=expr { (i, t, e) }
