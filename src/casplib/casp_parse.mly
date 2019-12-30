%{
open Util
open Casp_ast

open Lexing

let pos_of startp endp =
  Pos.mk startp.pos_fname
    startp.pos_lnum endp.pos_lnum
    (startp.pos_cnum - startp.pos_bol)
    (endp.pos_cnum - endp.pos_bol)

let cnt  = ref 0
let next () = incr cnt; !cnt

let fresh_id () =
  "tmp" ^ (string_of_int (next ()))

let expand_match pos mkif mklet e t cc =
  let e_id = fresh_id () in
  let add_case (p, pp, pattern, pr, result) s =
    match s, pattern with
    | None, Id "_" -> Some result
    | None, _ -> failwith "Switch has no default case"
    | Some s', _ ->
      let cond = (p, Binop ((pp, Atomic (Id e_id)), Eq, (pr, Atomic pattern))) in
      Some (p, mkif cond result s')
  in
  match List.fold_right add_case cc None with
  | Some s -> (pos, mklet e_id t e s)
  | None -> failwith "Match is empty"

type proginst =
  | Inst of id * (Pos.t * atomic) list
  | Ext of id

let process_prog is =
  let separate_extern (l1, l2) (p, i) =
    match i with
    | Inst (x, y) -> (l1, l2 @ [p, (x, y)])
    | Ext x -> (l1 @ [p, x], l2)
  in
  List.fold_left separate_extern ([], []) is

%}

%token <Util.bint> DECNUM
%token <Bits.t> HEXNUM
%token <Bits.t> BITNUM
%token <string> ID
%token <string> STRINGLIT
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token AMPAMP PIPEPIPE CARETCARET LTMINUS MINUSGT LTLT GTGT EQEQ BANGEQ STARSTAR
%token DOTDOTDOT DOT CARET SEMIC QUES QUESQUES COLON COMMA PLUS MINUS STAR SLASH
%token EQ LT GT BPLUS BMINUS BSTAR BLT BGT BSLT BSGT AMP PIPE BANG TILDE
%token BIT LOC BOOL INT LABEL STRING
%token IF THEN ELSE FOR LET IN DO ASSERT ERR SKIP
%token TYPE LETSTATE INVARIANT DEF PROC DEFOP
%token TXT SEM DEC HEX BIN LBL
%token OPTYPE OPMEMORYHANDLE OPDATAHANDLE OPLOGIC OPARITHMETIC OPBRANCH OPCOPROCESSOR
%token SWITCH WITH CASE END INCLUDE
%token TRUE FALSE FETCH STORE LEN REF MEMORY
%token MODULE EXTERN
%token FRAME MODIFYREG MODIFYMEM PRE POST
%token EOF

%type <Casp_ast.decl list> casp_file
%type <Casp_ast.submodule list> map_file
%type <Casp_ast.extern list * Casp_ast.casp_inst list> prog_file
%type <Casp_ast.spec> spec_file
%type <Casp_ast.startstate list> init_file
%type <Casp_ast.sketch_inst list> sketch_file

%start casp_file prog_file spec_file map_file init_file sketch_file

%%

/*
 * The semicolon and the two layers here are apparently necessary to
 * persuade menhir to not read the first token of the next declaration
 * before executing the reduction action that does the inclusion.
 * (And then nothing works properly.) This is in spite of the fact
 * that there is no reason for it to be fetching a lookahead token in
 * this state - the reserved word INCLUDE uniquely identifies the
 * whole rule here and there should be no need to look at the token
 * after the STRINGLIT. There does not appear to be any way to tell
 * menhir that this rule must be reduced synchronously without
 * lookahead (ideally, there would be some declaration for this so
 * that the parser wouldn't build if that made it ambiguous)... there
 * is a discussion of a related problem in the menhir docs in
 * connection with interactive input and end-of-file, but the language
 * there claims menhir does the right thing, and it isn't.
 *
 * If updating menhir causes include files to stop working and
 * generate syntax errors on the semicolon or on the first thing in
 * the include file (because it was expecting to see a semicolon) that
 * means it's no longer prefetching the semicolon, and flattening
 * these two rules and that should make it work again.
 *
 * Grr.
 *
 * I am not having this problem with ocamlyacc.
 *
 * Separately, note that Include.includefile only manipulates the
 * input pipe for the parser and does not produce any values.
 */

inclusion:
  inclusion_ SEMIC { () }
;

inclusion_:
  INCLUDE f=STRINGLIT { Include.includefile true f }
;

/**************************************************************/
/* casp files */

casp_file :
  ds=decls EOF                    { ds }
;

/**************************************************************/
/* progs */

prog_file :
    is=insts EOF                  { process_prog is }
;

insts :
    /* nil */                     { [] }
  | is=insts LPAREN i=inst RPAREN { is @ [i] }
  | is=insts inclusion            { is }
;

inst :
  i=ID aa=inst_args {
    let p = pos_of $startpos $endpos in
    (p, Inst (i, aa))
  }
  | EXTERN i = ID {
    let p = pos_of $startpos $endpos in
    (p, Ext (i))
  }
;

inst_args :
    /* nil */             { [] }
  | aa=inst_args a=atomic {
      let p = pos_of $startpos(a) $endpos(a) in
      aa @ [(p, a)]
    }
;

/**************************************************************/
/* sketches */

sketch_file :
    is=sketch_insts EOF                  { is }
;

sketch_insts :
    /* nil */                     { [] }
  | is=sketch_insts LPAREN i=sketch_inst RPAREN { is @ [i] }
  | is=sketch_insts inclusion            { is }
;

sketch_inst :
    i=ID aa=sketch_inst_args {
      let p = pos_of $startpos $endpos in
      (p, SketchInst (i, aa))
    }
  | QUESQUES {
      let p = pos_of $startpos $endpos in
      (p, SketchInstPlaceHolder)
  }
;

sketch_inst_args :
    /* nil */             { [] }
  | aa=sketch_inst_args a=atomic {
      let p = pos_of $startpos(a) $endpos(a) in
      aa @ [ (p, SketchArg a) ]
    }
  | aa=sketch_inst_args QUESQUES {
      let p = pos_of $startpos $endpos in
      aa @ [ (p, SketchArgPlaceHolder) ]
    }
;

/**************************************************************/
/* start state for interpretation */

init_file :
    ss=starts EOF                  { ss }
;

starts :
    /* nil */                     { [] }
  | ss=starts LPAREN s=start RPAREN { ss @ [s] }
;

start :
  | a=atomic EQ i=atomic {
    let p = pos_of $startpos $endpos in
    (p, StartAssign (a, i))
  }
  | MEMORY i=ID COLON n1=DECNUM BIT n2=DECNUM LEN n3=DECNUM REF {
    let p = pos_of $startpos $endpos in
    (p, StartMem (i, BI.to_int n1, BI.to_int n2, BI.to_int n3, None))
  }
  | MEMORY i1=ID COLON n1=DECNUM BIT n2=DECNUM LEN n3=DECNUM REF WITH i2=ID {
    let p = pos_of $startpos $endpos in
    (p, StartMem (i1, BI.to_int n1, BI.to_int n2, BI.to_int n3, Some i2))
  }
;

/**************************************************************/
/* mapping files */

map_file :
  ms=mappings EOF                 { ms }
;

mappings :
    /* nil */                     { [] }
  | ms=mappings m=mapping         { ms @ [m] }
;

ptrone:
    LBRACKET i=ID COMMA o=DECNUM RBRACKET
    { (i, BI.to_int o) }
;

ptrlist:
    ptrone                 { [$1] }
  | ps=ptrlist p=ptrone     { ps @ [p]}
;

mapping :
  | MODULE i=ID LBRACE ds=decls MODIFYREG COLON mrs=idlist MODIFYMEM COLON mms=ptrlist RBRACE    {
      let p = pos_of $startpos $endpos in
      (p, i, ds, mrs, mms) }
  | MODULE i=ID LBRACE ds=decls MODIFYMEM COLON mms=ptrlist MODIFYREG COLON mrs=idlist RBRACE    {
      let p = pos_of $startpos $endpos in
      (p, i, ds, mrs, mms) }
  | MODULE i=ID LBRACE ds=decls MODIFYMEM COLON mms=ptrlist RBRACE    {
      let p = pos_of $startpos $endpos in
      (p, i, ds, [], mms) }
  | MODULE i=ID LBRACE ds=decls MODIFYREG COLON mrs=idlist RBRACE    {
      let p = pos_of $startpos $endpos in
      (p, i, ds, mrs, []) }
  | MODULE i=ID LBRACE ds=decls RBRACE    {
      let p = pos_of $startpos $endpos in
      (p, i, ds, [], []) }
;

/**************************************************************/
/* specs */

spec_file :
  ds=decls FRAME COLON fs=frames PRE COLON pre=expr POST COLON post=expr EOF
    { (ds, fs, pre, post) }
;

frames :
    /* nil */               { [] }
  | fs=frames f=frame       { fs @ [f] }
;

idlist:
    ID                { [$1] }
  | ids=idlist i=ID   { ids @ [i] }
;

frame :
  | MODIFYREG COLON m=idlist {
      let p = pos_of $startpos $endpos in
      (p, FrameModifyReg m) }
  | MODIFYMEM COLON m=ptrlist {
      let p = pos_of $startpos $endpos in
      (p, FrameModifyMem m) }
;

/**************************************************************/
/* declarations */

decls :
    /* nil */       { [] }
  | ds=decls d=decl { ds @ [d] }
  | ds=decls inclusion { ds }
;

decl :
  (* type declaration *)
    TYPE i=ID EQ t=typ {
      let p = pos_of $startpos $endpos in
      (p, DeclType (i, t))
    }
  (* top-level let binding *)
  | LET LPAREN i=ID COLON t=typ RPAREN EQ e=expr
  | LET i=ID COLON t=typ EQ e=expr {
      let p = pos_of $startpos $endpos in
      (p, DeclLet (i, t, e))
    }
  (* string let binding *)
  | LET LPAREN i=ID DOT TXT RPAREN EQ s=STRINGLIT
  | LET i=ID DOT TXT EQ s=STRINGLIT {
      let p = pos_of $startpos $endpos in
      (p, DeclString (i, s))
    }
  (* state declarations *)
  | LETSTATE LPAREN i=ID COLON t=typ RPAREN
  | LETSTATE i=ID COLON t=typ {
      let p = pos_of $startpos $endpos in
      (p, DeclLetstate (i, t, None))
    }
  | LETSTATE LPAREN i1=ID COLON t=typ RPAREN WITH i2=ID
  | LETSTATE i1=ID COLON t=typ WITH i2=ID {
      let p = pos_of $startpos $endpos in
      (p, DeclLetstate (i1, t, Some i2))
    }
  (* function definition *)
  | DEF i=ID ps=params MINUSGT t=typ EQ e=expr {
      let p = pos_of $startpos $endpos in
      (p, DeclDef (i, ps, t, e))
    }
  (* subroutine definition *)
  | PROC i=ID ps=params EQ s=stmt {
      let p = pos_of $startpos $endpos in
      (p, DeclDefs (i, ps, s))
    }
  (* instruction definition *)
  | DEFOP i=ID ps=params LBRACE b=body RBRACE {
      let p = pos_of $startpos $endpos in
      let (txt, optype, sem) = b in
      (p, DeclDefop (i, ps, txt, optype, sem))
    }
  (* invariant expression declarations *)
  | INVARIANT COLON e=expr
  | INVARIANT e=expr {
    let p = pos_of $startpos $endpos in
    (p, DeclInvariant e)
  }
;

params :
    /* nil */ { [] }
  | ps=params p=param { ps @ [p] }
;

param :
    LPAREN i=ID COLON t=typ RPAREN
  | i=ID COLON t=typ {
      (i, t)
    }
;

op_type :
    OPMEMORYHANDLE    { "memory_handle" }
  | OPDATAHANDLE      { "data_handle" }
  | OPLOGIC           { "logic" }
  | OPARITHMETIC      { "arithmetic" }
  | OPBRANCH          { "branch" }
  | OPCOPROCESSOR     { "coprocessor" }
  /* string, not pre-defined instruction type */
  | s=STRINGLIT              { s }
;

body :
    TXT EQ se=expr COMMA OPTYPE EQ ot=op_type COLON ost=STRINGLIT COMMA SEM EQ LBRACKET s=stmt RBRACKET
     { (se, Typed (ot, ost), s) }
  | OPTYPE EQ ot=op_type COLON ost=STRINGLIT COMMA SEM EQ LBRACKET s=stmt RBRACKET {
      let p = pos_of $startpos $endpos in
      ((p, Atomic (Str "")), Typed (ot, ost), s) }
  /* no operation type defined */
  | TXT EQ se=expr COMMA SEM EQ LBRACKET s=stmt RBRACKET
     { (se, NoTyped, s) }
  | SEM EQ LBRACKET s=stmt RBRACKET {
      let p = pos_of $startpos $endpos in
      ((p, Atomic (Str "")), NoTyped, s) }
  /* MK: what is this rule for? ghost ops? */
;

/**************************************************************/
/* statements */

stmt:
    continuing_stmt                             { $1 }
  | base_stmt                                   { $1 }
  | base_stmt SEMIC stmt                        {
      let p = pos_of $startpos $endpos in
      (p, Seq ($1, $3))
    }
;

complete_stmt:
    complete_continuing_stmt                    { $1 }
  | base_stmt                                   { $1 }
  | base_stmt SEMIC complete_stmt               {
      let p = pos_of $startpos $endpos in
      (p, Seq ($1, $3))
    }
;

base_stmt:
  | SKIP {
      let p = pos_of $startpos $endpos in
      (p, Skip)
    }
  | ERR {
      let p = pos_of $startpos $endpos in
      (p, Err)
    }
  | ASSERT e=expr {
      let p = pos_of $startpos $endpos in
      (p, Assert (e, "assertion failed"))
    }
  | ASSERT e=expr s=STRINGLIT {
      let p = pos_of $startpos $endpos in
      (p, Assert (e, s))
    }
  | STAR e1=expr LTMINUS e2=expr {
      let p = pos_of $startpos $endpos in
      (p, Assign (e1, e2))
    }
  | STORE LBRACKET e1=expr COMMA e2=expr RBRACKET LTMINUS e=expr {
      let p = pos_of $startpos $endpos in
      (p, Store (e1, e2, e))
    }
  | i=ID LPAREN ee=expr_args RPAREN {
      let p = pos_of $startpos $endpos in
      (p, Call (i, ee))
    }
  | SWITCH e=expr COLON typ=typ WITH ks=scases END {
      let p = pos_of $startpos $endpos in
      let mkif c t f = IfS (c, t, f) in
      let mklet i t e s = LetS (i, t, e, s) in
      expand_match p mkif mklet e typ ks
    }
  | LPAREN s=stmt RPAREN { s }
;

continuing_stmt:
  | FOR i=ID IN LBRACKET e1=expr DOTDOTDOT e2=expr RBRACKET DO s=stmt {
      let p = pos_of $startpos $endpos in
      (p, For (i, e1, e2, s))
    }
  | LET LPAREN i=ID COLON t=typ RPAREN EQ e=expr IN s=stmt
  | LET i=ID COLON t=typ EQ e=expr IN s=stmt {
      let p = pos_of $startpos $endpos in
      (p, LetS (i, t, e, s))
    }
  | IF e=expr THEN s=stmt {
      let p = pos_of $startpos $endpos in
      (p, IfS (e, s, (p, Skip)))
    }
  | IF e=expr THEN s1=complete_stmt ELSE s2=stmt {
      let p = pos_of $startpos $endpos in
      (p, IfS (e, s1, s2))
    }
;

complete_continuing_stmt:
  | FOR i=ID IN LBRACKET e1=expr DOTDOTDOT e2=expr RBRACKET DO s=complete_stmt {
      let p = pos_of $startpos $endpos in
      (p, For (i, e1, e2, s))
    }
  | LET LPAREN i=ID COLON t=typ RPAREN EQ e=expr IN s=complete_stmt
  | LET i=ID COLON t=typ EQ e=expr IN s=complete_stmt {
      let p = pos_of $startpos $endpos in
      (p, LetS (i, t, e, s))
    }
  | IF e=expr THEN s1=complete_stmt ELSE s2=complete_stmt {
      let p = pos_of $startpos $endpos in
      (p, IfS (e, s1, s2))
    }
;

/**************************************************************/
/* match cases */

scases:
    /* nil */     { [] }
  | scases scase  { $1 @ [$2] }
;

ecases:
    /* nil */     { [] }
  | ecases ecase  { $1 @ [$2] }
;

/* note: these should really have binders on the left */
scase:
  CASE atomic MINUSGT stmt  {
    let p = pos_of $startpos $endpos in
    let pp = pos_of $startpos($2) $endpos($2) in
    let pr = pos_of $startpos($4) $endpos($4) in
    (p, pp, $2, pr, $4)
  }
;

ecase:
  CASE atomic MINUSGT expr  {
    let p = pos_of $startpos $endpos in
    let pp = pos_of $startpos($2) $endpos($2) in
    let pr = pos_of $startpos($4) $endpos($4) in
    (p, pp, $2, pr, $4)
  }
;

/**************************************************************/
/* expressions */

expr:
  if_expr                                       { $1 }
;

if_expr:
    logor_expr                                  { $1 }
  | logor_Lexpr                                 { $1 }
  | i=ID QUES a1=atomic COLON a2=atomic {
      let p = pos_of $startpos $endpos in
      let pi = pos_of $startpos(i) $endpos(i) in
      let pa1 = pos_of $startpos(a1) $endpos(a1) in
      let pa2 = pos_of $startpos(a2) $endpos(a2) in
      (p, IfE ((pi, Atomic (Id i)), (pa1, Atomic a1), (pa2, Atomic a2)))
    }
  | IF e1=expr THEN e2=expr ELSE e3=expr {
      let p = pos_of $startpos $endpos in
      (p, IfE (e1, e2, e3))
    }
  | SWITCH e=expr COLON t=typ WITH cc=ecases END {
      let p = pos_of $startpos $endpos in
      let mkif e s1 s2 = IfE (e, s1, s2) in
      let mklet i t e1 e2 = LetE (i, t, e1, e2) in
      expand_match p mkif mklet e t cc
    }
;

logor_expr:
  | logxor_expr                                 { $1 }
  | e1=logor_expr PIPEPIPE e2=logxor_expr       {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LogOr, e2))
    }
;

logor_Lexpr:
  | logxor_Lexpr                                { $1 }
  | e1=logor_expr PIPEPIPE e2=logxor_Lexpr      {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LogOr, e2))
    }
;

logxor_expr:
  | logand_expr                                 { $1 }
  | e1=logxor_expr CARETCARET e2=logand_expr    {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LogXor, e2))
    }
;

logxor_Lexpr:
  | logand_Lexpr                                { $1 }
  | e1=logxor_expr CARETCARET e2=logand_Lexpr   {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LogXor, e2))
    }
;

logand_expr:
  | bitor_expr                                  { $1 }
  | e1=logand_expr AMPAMP e2=bitor_expr         {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LogAnd, e2))
    }
;

logand_Lexpr:
  | bitor_Lexpr                                 { $1 }
  | e1=logand_expr AMPAMP e2=bitor_Lexpr        {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LogAnd, e2))
    }
;

bitor_expr:
  | bitxor_expr                                 { $1 }
  | e1=bitor_expr PIPE e2=bitxor_expr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BitOr, e2))
    }
;

bitor_Lexpr:
  | bitxor_Lexpr                                { $1 }
  | e1=bitor_expr PIPE e2=bitxor_Lexpr          {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BitOr, e2))
    }
;

bitxor_expr:
  | bitand_expr                                 { $1 }
  | e1=bitxor_expr CARET e2=bitand_expr         {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BitXor, e2))
    }
;

bitxor_Lexpr:
  | bitand_Lexpr                                { $1 }
  | e1=bitxor_expr CARET e2=bitand_Lexpr        {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BitXor, e2))
    }
;

bitand_expr:
  | eq_expr                                     { $1 }
  | e1=bitand_expr AMP e2=eq_expr               {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BitAnd, e2))
    }
;

bitand_Lexpr:
  | eq_Lexpr                                    { $1 }
  | e1=bitand_expr AMP e2=eq_Lexpr              {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BitAnd, e2))
    }
;

eq_expr:
  | compare_expr                                { $1 }
  | e1=eq_expr EQEQ e2=compare_expr             {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Eq, e2))
    }
  | e1=eq_expr BANGEQ e2=compare_expr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Neq, e2))
    }
;

eq_Lexpr:
  | compare_Lexpr                               { $1 }
  | e1=eq_expr EQEQ e2=compare_Lexpr            {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Eq, e2))
    }
  | e1=eq_expr BANGEQ e2=compare_Lexpr          {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Neq, e2))
    }
;

compare_expr:
  | shift_expr                                  { $1 }
  | e1=compare_expr LT e2=shift_expr            {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Lt, e2))
    }
  | e1=compare_expr GT e2=shift_expr            {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Gt, e2))
    }
  | e1=compare_expr BLT e2=shift_expr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BLt, e2))
    }
  | e1=compare_expr BGT e2=shift_expr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BGt, e2))
    }
  | e1=compare_expr BSLT e2=shift_expr          {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BSLt, e2))
    }
  | e1=compare_expr BSGT e2=shift_expr          {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BSGt, e2))
    }
;

compare_Lexpr:
  | shift_Lexpr                                 { $1 }
  | e1=compare_expr LT e2=shift_Lexpr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Lt, e2))
    }
  | e1=compare_expr GT e2=shift_Lexpr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Gt, e2))
    }
  | e1=compare_expr BLT e2=shift_Lexpr          {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BLt, e2))
    }
  | e1=compare_expr BGT e2=shift_Lexpr          {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BGt, e2))
    }
  | e1=compare_expr BSLT e2=shift_Lexpr         {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BSLt, e2))
    }
  | e1=compare_expr BSGT e2=shift_Lexpr         {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BSGt, e2))
    }
;

shift_expr:
  | add_expr                                    { $1 }
  | e1=shift_expr LTLT e2=add_expr              {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LShift, e2))
    }
  | e1=shift_expr GTGT e2=add_expr              {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, RShift, e2))
    }
;

shift_Lexpr:
  | add_Lexpr                                   { $1 }
  | e1=shift_expr LTLT e2=add_Lexpr             {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, LShift, e2))
    }
  | e1=shift_expr GTGT e2=add_Lexpr             {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, RShift, e2))
    }
;

add_expr:
  | mul_expr                                    { $1 }
  | e1=add_expr PLUS e2=mul_expr                {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Add, e2))
    }
  | e1=add_expr MINUS e2=mul_expr               {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Sub, e2))
    }
  | e1=add_expr BPLUS e2=mul_expr               {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BAdd, e2))
    }
  | e1=add_expr BMINUS e2=mul_expr              {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BSub, e2))
    }
;

add_Lexpr:
  | mul_Lexpr                                   { $1 }
  | e1=add_expr PLUS e2=mul_Lexpr               {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Add, e2))
    }
  | e1=add_expr MINUS e2=mul_Lexpr              {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Sub, e2))
    }
  | e1=add_expr BPLUS e2=mul_Lexpr              {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BAdd, e2))
    }
  | e1=add_expr BMINUS e2=mul_Lexpr             {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BSub, e2))
    }
;

mul_expr:
  | pow_expr                                    { $1 }
  | e1=mul_expr STAR e2=prefix_expr             {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Mul, e2))
    }
  | e1=mul_expr SLASH e2=prefix_expr            {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Div, e2))
    }
  | e1=mul_expr BSTAR e2=prefix_expr            {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BMul, e2))
    }
;

mul_Lexpr:
  | pow_Lexpr                                   { $1 }
  | e1=mul_expr STAR e2=prefix_Lexpr            {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Mul, e2))
    }
  | e1=mul_expr SLASH e2=prefix_Lexpr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Div, e2))
    }
  | e1=mul_expr BSTAR e2=prefix_Lexpr           {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, BMul, e2))
    }
;

pow_expr:
  | prefix_expr                                   { $1 }
  | e1=base_expr STARSTAR e2=prefix_expr        {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Pow, e2))
    }
;

pow_Lexpr:
  | prefix_Lexpr                                  { $1 }
  | e1=base_expr STARSTAR e2=prefix_Lexpr       {
      let p = pos_of $startpos $endpos in
      (p, Binop (e1, Pow, e2))
    }
;

prefix_expr:
  | base_expr                                    { $1 }
  | MINUS e=prefix_expr                         {
      let p = pos_of $startpos $endpos in
      (p, Unop (Neg, e))
    }
  | BANG  e=prefix_expr                         {
      let p = pos_of $startpos $endpos in
      (p, Unop (LogNot, e))
    }
  | TILDE e=prefix_expr                         {
      let p = pos_of $startpos $endpos in
      (p, Unop (BitNot, e))
    }
  | STAR e=prefix_expr                          {
      let p = pos_of $startpos $endpos in
      (p, Deref (e))
    }
;

prefix_Lexpr:
  | base_Lexpr                                   { $1 }
  | MINUS e=prefix_Lexpr                        {
      let p = pos_of $startpos $endpos in
      (p, Unop (Neg, e))
    }
  | BANG  e=prefix_Lexpr                        {
      let p = pos_of $startpos $endpos in
      (p, Unop (LogNot, e))
    }
  | TILDE e=prefix_Lexpr                        {
      let p = pos_of $startpos $endpos in
      (p, Unop (BitNot, e))
    }
  | STAR e=prefix_Lexpr                         {
      let p = pos_of $startpos $endpos in
      (p, Deref (e))
    }
;

base_expr:
  | a=atomic {
      let p = pos_of $startpos $endpos in
      (p, Atomic (a))
    }
  | e1=base_expr LBRACKET e2=expr RBRACKET {
      let p = pos_of $startpos $endpos in
      (p, Index (e1, e2))
    }
  | e1=base_expr LBRACKET e2=expr COLON e3=expr RBRACKET {
      let p = pos_of $startpos $endpos in
      (p, Slice (e1, e2, e3))
    }
  | FETCH LBRACKET e1=expr COMMA e2=expr RBRACKET {
      let p = pos_of $startpos $endpos in
      (p, Fetch (e1, e2))
    }
  | i=ID LPAREN ee=expr_args RPAREN {
      let p = pos_of $startpos $endpos in
      (p, App (i, ee))
    }
  | i=ID DOT TXT                                {
      let p = pos_of $startpos $endpos in
      (p, App ("txt", [(p, Atomic (Id i))]))
    }
  | i=ID DOT LBL                                {
      let p = pos_of $startpos $endpos in
      (p, App ("lbl", [(p, Atomic (Id i))]))
    }
  | i=ID DOT DEC                                {
      let p = pos_of $startpos $endpos in
      (p, App ("dec", [(p, Atomic (Id i))]))
    }
  | i=ID DOT HEX                                {
      let p = pos_of $startpos $endpos in
      (p, App ("hex", [(p, Atomic (Id i))]))
    }
  | i=ID DOT BIN                                {
      let p = pos_of $startpos $endpos in
      (p, App ("bin", [(p, Atomic (Id i))]))
    }
  | LPAREN e=expr RPAREN { e }
;

base_Lexpr:
  | LET i=ID COLON t=typ EQ e1=expr IN e2=expr  {
      let p = pos_of $startpos $endpos in
      (p, LetE (i, t, e1, e2))
    }
;

atomic :
    c=DECNUM {
      Int (c)
    }
  | h=HEXNUM {
      Vec (h)
    }
  | b=BITNUM {
      Vec (b)
    }
  | TRUE {
      Bool (true)
    }
  | FALSE {
      Bool (false)
    }
  | i=ID {
      Id (i)
    }
  /* memory format: [id, offset] */
  | LBRACKET i=ID COMMA o=DECNUM RBRACKET {
      Ptr (i, o)
  }
  /* string */
  | s=STRINGLIT {
      Str (s)
  }
;

expr_args :
    /* nil */                     { [] }
  | nonempty_args                 { $1 }
;

nonempty_args:
  | a=expr                        { [a] }
  | aa=nonempty_args COMMA a=expr { aa @ [a] }
;

typ :
    n=DECNUM BIT { BitType (BI.to_int n) }
  | s=ID { AliasType (s) }
  | n=DECNUM BIT LOC { LocType (BI.to_int n) }
  | i=ID LOC { AliasLocType (i) }
  | BOOL { BoolType }
  | INT  { IntType }
  | STRING { StringType }
  | n1=DECNUM BIT n2=DECNUM LEN n3=DECNUM REF MEMORY {
      MemType (BI.to_int n1, BI.to_int n2, BI.to_int n3)
    }
  | n=DECNUM LABEL { LabelType (BI.to_int n) }
;
