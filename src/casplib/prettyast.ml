(****************************************************************************************
BSD License

Copyright (c) 2016-2019, Harvard University
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

    Redistributions of source code must retain the above copyright
    notice, this list of conditions and the following disclaimer.

    Redistributions in binary form must reproduce the above copyright
    notice, this list of conditions and the following disclaimer in
    the documentation and/or other materials provided with the
    distribution.

    Neither the name of the copyright holder nor the names of its
    contributors may be used to endorse or promote products derived
    from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
****************************************************************************************)


open Util
open Casp_ast

let string_of_unop = function
  | Neg -> "(-)"
  | LogNot -> "!"
  | BitNot -> "~"

let string_of_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Pow -> "**"
  | Eq  -> "=="
  | Neq -> "!="
  | Lt  -> "<"
  | Gt  -> ">"
  | BAdd -> "b+"
  | BSub -> "b-"
  | BMul -> "b*"
  | BLt -> "b<"
  | BGt -> "b>"
  | BSLt -> "bs<"
  | BSGt -> "bs>"
  | LShift -> "<<"
  | RShift -> ">>"
  | LogAnd -> "&&"
  | LogOr  -> "||"
  | LogXor -> "^^"
  | BitAnd -> "&"
  | BitOr  -> "|"
  | BitXor -> "^"

let string_of_hex h =
  (string_of_bits h) ++
  " len:" ++ (string_of_int (Bits.width h))

let string_of_id i = i

let string_of_ids ii = ii
  |> List.map string_of_id
  |> String.concat "\n"

let pos_of_ty = function
  | None -> Pos.builtin
  | Some (pos, _) -> pos

let rec string_of_function_typ (arg_typs, return_typ) =
  let arg_typs = arg_typs |> (List.map string_of_typ) in
  let return_typ = string_of_typ return_typ in
  String.concat "->" (arg_typs @ [return_typ])

and string_of_typ = function
  | BitType i -> (string_of_int i)^" bit"
  | LocType i -> (string_of_int i)^" bit loc"
  | MemType (l, n, r) ->
    (string_of_int l)^" bit "^
    (string_of_int n)^" len "^
    (string_of_int r)^" ref "
  | LabelType i-> (string_of_int i)^" label"
  | StringType -> "string"
  | AliasType i -> i
  | AliasLocType i -> i^" loc"
  | BoolType -> "bool"
  | IntType -> "int"

let string_of_atomic = function
  | Id i -> string_of_id i
  | Int i -> string_of_bint i
  | Bool b -> if b then "true" else "false"
  | Vec v -> Bits.to_bitstring v
  | Ptr (i, o) -> "[" ^ (string_of_id i) ^ ", " ^ (string_of_bint o) ^ "]"
  | Str s -> "\""^s^"\""

let string_of_optype = function
  | Typed (s, ss) -> s^" : "^ss
  | NoTyped -> "not defined"

let rec string_of_expr (_, e) =
  match e with
  | Atomic a -> string_of_atomic a
  | Deref e -> "*" ^ string_of_expr e
  | Fetch (e1, e2) ->
      "fetch[" ^
      (string_of_expr e1) ^ "," ^
      (string_of_expr e2) ^ "]"
  | Index (e1, e2) ->
      (string_of_expr e1) ^ "[" ^ (string_of_expr e2) ^ "]"
  | Slice (e1, e2, e3) ->
      (string_of_expr e1) ^ "[" ^
      (string_of_expr e2) ^ ": " ^
      (string_of_expr e3) ^ "]"
  | Unop (op, e) ->
      (string_of_unop op) ^ " ( " ^ string_of_expr e ^ " )"
  | Binop (e1, op, e2) ->
      " ( " ^ string_of_expr e1 ^ " ) " ^
      string_of_binop op ^ " ( " ^
      string_of_expr e2 ^ " ) "
  | App (i, args) ->
      i ^ " ( " ^
      ((args |> List.map string_of_expr) |> String.concat ", ") ^
      " )"
  | LetE (i, ty, e1, e2) ->
      "let " ^ (string_of_id i) ^
      " : " ^ (string_of_typ ty) ^
      " = " ^ (string_of_expr e1) ^
      " in " ^ (string_of_expr e2)
  | IfE (e1, e2, e3) ->
      "if " ^ (string_of_expr e1) ^
      " then " ^ (string_of_expr e2) ^
      " else " ^ (string_of_expr e3)

let rec string_of_stmt (_, s) =
  match s with
  | Skip -> "skip"
  | Err -> "err"
  | Assert (e, s) ->
      let e = string_of_expr e in
      "assert " ^ e ^ " " ^ s
  | Seq (s1, s2) ->
      let s1 = string_of_stmt s1 in
      let s2 = string_of_stmt s2 in
      s1 ++ "; " ++ s2
  | Store (e1, e2, e) ->
      let e1 = string_of_expr e1 in
      let e2 = string_of_expr e2 in
      let e = string_of_expr e in
      "store[" ^ e1 ^ "," ^ e2 ^ "] <- "^ e
  | Assign (e1, e2) ->
      let e1 = string_of_expr e1 in
      let e2 = string_of_expr e2 in
      e1 ^ " := " ^ e2
  | For (i, e1, e2, s) ->
      "for " ++ i ++ " in " ++
      (string_of_expr e1) ++ ", ..., " ++
      (string_of_expr e2) ++ "\ndo\n\t" ++
      (string_of_stmt s) ++ "\ndone"
  | Call (i, args) ->
      i :: (args |> List.map string_of_expr) |>
      String.concat " "
  | LetS (i, t, e, s) ->
      "let " ++ i ++ ":" ++
      (string_of_typ t) ++ " = " ++
      (string_of_expr e) ++ " in\n" ++
      (string_of_stmt s)
  | IfS (e, s1, s2) ->
      "if " ++
      (string_of_expr e)  ++ " then " ++
      (string_of_stmt s1) ++ " else " ++
      (string_of_stmt s2)

let string_of_typed_id i t =
  string_of_id i ++ " : " ++ string_of_typ t

let string_of_typed_arg (i, t) =
  ch_wrap (string_of_typed_id i t) PAREN

let string_of_typed_args xs = xs
  |> (List.map string_of_typed_arg)
  |> String.concat " "

let string_of_decl = function
  | DeclType (i, t) ->
      let i, t = string_of_id i, string_of_typ t in
      "type " ++ i ++ " = " ++ t
  | DeclLet (i, t, e) ->
      let it = string_of_typed_id i t in
      let e  = string_of_expr e in
      "let " ++ it ++ " = " ++ e
  | DeclString (i, s) ->
      let i = string_of_id i in
      "let " ++ i ++ ".txt = " ++ s
  | DeclLetstate (i1, t, i2) ->
      let it = string_of_typed_id i1 t in
      begin match i2 with
      | None -> "letstate " ++ it
      | Some i2 -> "letstate " ++ it ++ "with " ++ i2
      end
  | DeclInvariant e ->
      let e = string_of_expr e in
      "invariant " ++ e
  | DeclDef (i, xs, t, e) ->
      let i   = string_of_id i in
      let xs  = string_of_typed_args xs in
      let t,e = string_of_typ t, string_of_expr e in
      "def " ++ i ++ " " ++ xs ++ " -> " ++ t ++ " " ++ e
  | DeclDefs (i, xs, s) ->
      let i   = string_of_id i in
      let xs  = string_of_typed_args xs in
      let s   = string_of_stmt s in
      "defs " ++ i ++ " " ++ xs ++ " -> () " ++ s
  | DeclDefop (i, xs, txt, optype, s) ->
      let i   = string_of_id i in
      let xs  = string_of_typed_args xs in
      let s   = string_of_stmt s in
      let txt = string_of_expr txt in
      let txt = "txt = " ++ txt in
      let optype = "op_type = " ++ string_of_optype optype in
      let sem = "sem = " ++ s in
      "defop " ++ i ++ " " ++ xs ++ " " ++
      (ch_wrap ("\n" ++ txt ++ "\n" ++ optype ++ "\n" ++ sem ++ "\n") BRACE)

let string_of_decl (pos, decl) =
  (Pos.string_of pos) ++ ": " ++
  (string_of_decl decl)

let string_of_casp m = m
  |> List.map string_of_decl
  |> String.concat "\n"

let string_of_inst (_, (i, args)) =
  let get_args a = string_of_atomic (snd a) in
  (string_of_id i) ++ " " ++
  String.concat " " (List.map get_args args)

let string_of_sketch_inst (_, (i, args)) =
  let get_args a =
    match snd a with
    | SketchArg a -> string_of_atomic a
    | SketchArgPlaceHolder -> "??"
  in
  (string_of_id i) ++ " " ++
  String.concat " " (List.map get_args args)

let string_of_inst inst =
  ch_wrap (string_of_inst inst) PAREN

let string_of_prog p = p
  |> List.map string_of_inst
  |> String.concat "\n"

let string_of_ptr (i, o) = "["^(string_of_id i)^", "^(string_of_int o)^"]"
let string_of_ptrs ii = ii
  |> List.map string_of_ptr
  |> String.concat "\n"

let string_of_frame (_, f) =
  match f with
  | FrameModifyReg ii ->
    "reg-modify : "^(string_of_ids ii)
  | FrameModifyMem pp ->
    "mem-modify : "^(string_of_ptrs pp)

let string_of_spec (ds, fs, pre, post) =
  let decl_str = ds |> List.map string_of_decl |> String.concat "\n" in
  let frame_str = fs |> List.map string_of_frame |> String.concat "\n" in
  let pre_str = string_of_expr pre in
  let post_str = string_of_expr post in
  "spec:\n" ^
  "decls:\n" ^ decl_str ^
  "frames:\n" ^ frame_str ^
  "pre:\n" ^ pre_str ^
  "post:\n" ^ post_str
