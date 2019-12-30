{
open Util
open Lexing
open Ale_parse

module Bat = Batteries
module Inc = Include

let (++) = (^)

let get_pos lexbuf = Pos.mk
    lexbuf.lex_curr_p.pos_fname
    lexbuf.lex_start_p.pos_lnum
    lexbuf.lex_curr_p.pos_lnum
    (lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_p.pos_bol)
    (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)

let get_lex lb =
  Lexing.lexeme lb

let get_tok = get_lex

let bint_of_token lb =
  get_lex lb |>
  BI.of_string

}

let cr='\013'
let nl='\010'
let eol=(cr nl|nl|cr)
let ws=('\012'|'\t'|' ')*
let digit=['0'-'9']
let hex=['0'-'9''A'-'F''a'-'f']
let bit=['0'-'1']
let id = ['A'-'Z''a'-'z''_''.']['\'''a'-'z''A'-'Z''0'-'9''_']*


rule main = parse
  | eol       { new_line lexbuf; main lexbuf }
  | ws+       { main lexbuf }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '{'       { LBRACE }
  | '}'       { RBRACE }
  | '['       { LBRACKET }
  | ']'       { RBRACKET }
  | ':'       { COLON }
  (* | ';'       { SEMIC } *)
  | ','       { COMMA }
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '*'       { STAR }
  | '/'       { SLASH }
  | '='       { EQ }
  | '<'       { LT }
  | '>'       { GT }
  | "&&"      { AMPAMP }
  | "||"      { PIPEPIPE }
  | "^^"      { CARETCARET }
  | '&'       { AMP }
  | '|'       { PIPE }
  | "^"       { CARET }
  | '!'       { BANG }
  | '~'       { TILDE }
  | "<<"      { LTLT }
  | ">>"      { GTGT }
  | "=="      { EQEQ }
  | "!="      { BANGEQ }
  | "->"      { IMPLY }
  | "bool"    { BOOL } (* type *)
  | "boolean" { BOOL }
  | "true"    { TRUE }
  | "false"   { FALSE }
  | "int"     { INT }
  | "vec"     { VEC }
  | "ptr"     { PTR }
  | "reg"     { REG }
  | "read"    { READ }
  | "require"   { REQUIRE } (* alewife declaration *)
  | "provide"   { PROVIDE } (* alewife definition *)
  | "type"      { TYPE }
  | "value"     { VALUE }
  | "function"  { FUNCTION }
  | "block"     { BLOCK } (* alewife block *)
  | "label"     { LABEL } (* label in asm *)
  | "region"    { REGION } (* memory definition *)
  | "bit"       { BIT }
  | "len"       { LEN }
  | "ref"       { REF }
  | "with"      { WITH }
  | "reg-modify"    { MODIFYREG }
  | "mem-modify"    { MODIFYMEM }
  | "invariant" { INVARIANT }
  | "let"       { LET }
  | "in"        { IN }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "pre"       { PRE }
  | "post"      { POST }
  | digit+    {  DECNUM (bint_of_token lexbuf) }
  | "0x"hex+  { let tok = get_tok lexbuf in HEXNUM (Bits.of_string tok) }
  | "0b"bit+  { let tok = get_tok lexbuf in BITNUM (Bits.of_string tok) }
  | id        { ID (get_tok lexbuf) }
  | eof       { EOF }
  | "(*"      { comment 1 lexbuf }
  (* | '"'       {
    let fresh = Buffer.create 10 in
    lexbuf |>
    read_string fresh } *)
  | _         {
    let tok = get_tok lexbuf in
    let pos = get_pos lexbuf |> Pos.string_of in
    let msg = "invalid token: " ++ tok ++ "@" ++ pos in
    failwith msg
  }

and comment lvl = parse
| "(*"  { comment (lvl + 1) lexbuf }
| eol   { new_line lexbuf; comment lvl lexbuf }
| "*)"  { if lvl == 1 then main lexbuf else comment lvl lexbuf }
| _     { comment lvl lexbuf }

(* proudly copy and pasted from Real World OCaml 1st ed
 * THANKS YARON. *)
(* and read_string buf = parse
  | '"'       { STRINGLIT (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { failwith ("Illegal string character: " ^ Lexing.lexeme lexbuf) }
  | eof { failwith "String is not terminated" } *)

{

let read file =
  let ch = open_in file in
  let lexbuf = Lexing.from_channel ch in
  let pos = { lexbuf.lex_curr_p with pos_fname = file; } in
  let lexbuf = { lexbuf with lex_curr_p = pos; } in
  try
     Ale_parse.file main lexbuf
  with Ale_parse.Error ->
    let msg = get_pos lexbuf |> Pos.string_of in
     failwith (msg ++ ": Parse error");
}
