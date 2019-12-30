%{
  open Util
  open Smtlib_ast
  open Lexing
%}

%token <Util.bint> DECNUM
%token <Bits.t> HEXNUM
%token <Bits.t> BITNUM
%token <string> ID
%token <string> STRINGLIT
%token LPAREN RPAREN EMPTY MINUS
%token INT BOOL BITVEC UNDER
%token TRUE FALSE LPARENEQUALS
%token DEFINE MODEL ERROR END_YICES

%type <Smtlib_ast.t> file
%type <Smtlib_ast.t> yices_file
%start file
%start yices_file

%%

file:
  /* format: (model XXX YYY) */
  | LPAREN MODEL d=defs RPAREN { List.rev d }
  /* we don't want this to happen */
  | LPAREN ERROR s=STRINGLIT RPAREN { failwith ("ERROR from solver: " ^ s) }
;

yices_file:
  /* format: (= NAME VALUE ...) */

  | d=equality_defs END_YICES { List.rev d }

  | LPAREN ERROR s=STRINGLIT RPAREN { failwith ("ERROR from solver: " ^ s) }
;

defs : /* format: (define-fun XXX) (define-fun YYY) */
  /* nil */       { [] }
  | ds=defs d=def { d :: ds }
;

equality_defs : /* format: (= NAME VALUE) ... */
  /* nil */                         { [] }
  | ds=equality_defs d=equality_def { d :: ds }
;

equality_def :
  /* format: (= NAME VALUE) */
  LPARENEQUALS i=ID b=BITNUM RPAREN
    { (i, Bit (bint_of_int (Bits.width b), b)) }
| LPARENEQUALS i=ID TRUE RPAREN
    { (i, Bool (true)) }
| LPARENEQUALS i=ID FALSE RPAREN
    { (i, Bool (false)) }
;

def :
  /* format: (define-fun NAME () Int VALUE) */
  | LPAREN DEFINE i=ID EMPTY INT v=DECNUM RPAREN
    { (i, Int (v)) }

  /* format: (define-fun NAME () Int (- VALUE)) */
  | LPAREN DEFINE i=ID EMPTY INT LPAREN MINUS v=DECNUM RPAREN RPAREN
    { (i, Int (BI.neg v)) }

  /* format: (define-fun NAME () Bool true) */
  | LPAREN DEFINE i=ID EMPTY BOOL TRUE RPAREN
    { (i, Bool (true)) }

  /* format: (define-fun NAME () Bool false) */
  | LPAREN DEFINE i=ID EMPTY BOOL FALSE RPAREN
    { (i, Bool (false)) }

  /* format: (define-fun NAME () (_ BitVec WIDTH) VALUE) */
  | LPAREN DEFINE i=ID EMPTY LPAREN UNDER BITVEC w=DECNUM RPAREN v=HEXNUM RPAREN
    { (i, Bit (w, v)) }

  /* format: (define-fun NAME () (_ BitVec WIDTH) VALUE) */
  | LPAREN DEFINE i=ID EMPTY LPAREN UNDER BITVEC w=DECNUM RPAREN v=BITNUM RPAREN
    { (i, Bit (w, v)) }
;
