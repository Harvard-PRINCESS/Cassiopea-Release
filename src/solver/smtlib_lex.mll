{
open Util
open Lexing
open Smtlib_parse

module I = Smtlib_parse.MenhirInterpreter
module S = String

exception SyntaxError of string

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

let failwith msg = raise (SyntaxError (msg))

}

let cr='\013'
let nl='\010'
let eol=(cr nl|nl|cr)
let ws=('\012'|'\t'|' ')*
let digit=['0'-'9']
let hex=['0'-'9''A'-'F''a'-'f']
let bit=['0'-'1']
let id = ['A'-'Z''a'-'z''_''.']['\'''a'-'z''A'-'Z''0'-'9''_''@']*


rule main = parse
  | eol       { new_line lexbuf; main lexbuf }
  | ws+       { main lexbuf }
  | "()"      { EMPTY }
  | "("       { LPAREN }
  | ")"       { RPAREN }
  | "-"       { MINUS }
  | "(="      { LPARENEQUALS }
  | "Int"     { INT }
  | "Bool"    { BOOL }
  | "BitVec"  { BITVEC }
  | "_"       { UNDER }
  | "model"   { MODEL }
  | "define-fun" { DEFINE }
  | "true"    { TRUE }
  | "false"   { FALSE }
  | "error"   { ERROR } 
  | "end_yices_model" { END_YICES }
  | digit+    { DECNUM (bint_of_token lexbuf) }
  | "#x"hex+  {
    let tok = get_tok lexbuf in
    let tok = S.sub tok 1 ((S.length tok) - 1) in
    let tok = "0"^tok in
    HEXNUM (Bits.of_string tok) }
  | "#b"bit+  {
    let tok = get_tok lexbuf in
    let tok = S.sub tok 1 ((S.length tok) - 1) in
    let tok = "0"^tok in
    BITNUM (Bits.of_string tok) }
  | "(\"([^\"])*\")" {
    let tok = get_tok lexbuf in
    let tok = S.sub tok 1 ((S.length tok) - 1) in
    STRINGLIT (tok) }
  | id        { ID (get_lex lexbuf) }
  | _         {
    let tok = get_tok lexbuf in
    let pos = get_pos lexbuf |> Pos.string_of in
    let msg = "invalid token: " ++ tok ++ "@" ++ pos in
    failwith msg }

{

(**************************************************************)
(* toplevel *)

let read filestring =
  let lexbuf = Lexing.from_string filestring in
  try
    Smtlib_parse.file main lexbuf
  with Smtlib_parse.Error ->
    let msg = get_pos lexbuf |> Pos.string_of in
    failwith (msg ++ ": Parse error")

(* read the next parse out of the stream *)
let read_next ch =
  let lexbuf = Lexing.from_channel ch in
  try
    I.loop
      (I.lexer_lexbuf_to_supplier main lexbuf)
      (Smtlib_parse.Incremental.file lexbuf.lex_curr_p)
  with _ ->
    let msg = get_pos lexbuf |> Pos.string_of in
    let lxm = get_lex lexbuf in
    failwith ("ERROR: Lex error at position  " ++ msg ++ " with lexeme " ++ lxm)

(* read the next parse out of the stream and dump *)
let instrumented_read_next ch =
  let lexbuf = Lexing.from_channel ch in
  try
    I.loop
      (let _ = Printf.printf "%s " (get_lex lexbuf) in
       I.lexer_lexbuf_to_supplier main lexbuf)
      (Smtlib_parse.Incremental.file lexbuf.lex_curr_p)
  with _ ->
    let msg = get_pos lexbuf |> Pos.string_of in
    let lxm = get_lex lexbuf in
    failwith ("ERROR: Lex error at position  " ++ msg ++ " with lexeme " ++ lxm)

(* read the next parse out of the stream and dump *)
let instrumented_read_next_yices ch =
  let lexbuf = Lexing.from_channel ch in
  try
    I.loop
      (I.lexer_lexbuf_to_supplier main lexbuf)
      (Smtlib_parse.Incremental.yices_file lexbuf.lex_curr_p)
  with _ ->
    let msg = get_pos lexbuf |> Pos.string_of in
    let lxm = get_lex lexbuf in
    failwith ("ERROR: Lex error at position  " ++ msg ++ " with lexeme " ++ lxm)




}
