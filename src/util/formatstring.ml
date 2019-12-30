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

(* copy from grouper/support, 20190903 *)

(*
 * Support for format stirngs.
 *
 * As of 20190613 these are now $-substitutions like shell or make
 * rather than C-style printfs, because (a) we need to be able to
 * use the same argument more than once and (b) the printf-style
 * syntax for numbered arguments is vile. Also we don't need to
 * encode the types of the arguments in the format string.
 *
 * A format entry begins with a '$'.
 *
 * This may be followed by either a number or a number in braces or a
 * number in parentheses or another '$'. The delimited forms can be
 * extended later with modifiers for formatting if we end up wanting
 * that. The number selects the argument number to take, starting at
 * 1. (Why 1? Because ~everything else using this syntax does it
 * starting at 1 so starting from 0 would be very confusing.) $$
 * produces a single $.
 *)
open Util

type elt =
| LITERAL of Pos.pos * string
| USEARG of Pos.pos * int (* this int is 0-based *)

type t = int * elt list

(*
let dump tagword elts =
   prerr_string (tagword ^ "\n");
   let once elt =
      match elt with
      | LITERAL (_, s) -> prerr_string ("   --" ^ s ^ "--\n")
      | USEARG (_, k) -> prerr_string ("   [" ^ string_of_int k ^ "]\n")
   in
   List.iter once elts
*)

(*
 * is_format: check if there are $-escapes
 *)

let is_format s =
   match String.index_opt s '$' with
   | None -> false
   | Some _ -> true

let are_format strs =
   List.exists is_format strs

(*
 * parse
 *)

let doget s ix =
   if ix >= 0 && ix < String.length s then Some (String.get s ix)
   else None

let isdigit c =
   match c with
   | '0' | '1' | '2' | '3' | '4'
   | '5' | '6' | '7' | '8' | '9' -> true
   | _ -> false

let isnumber s =
   let rec test k =
      match doget s k with
      | None -> true
      | Some c -> if isdigit c then test (k+1) else false
   in
   String.length s > 0 && test 0

(* count how many characters of s satisfy p starting at offset skip *)
let rec count s skip p =
   match doget s skip with
   | None -> skip
   | Some c -> if p c then (count s (skip+1) p) else skip

(* find the offset of c in s; if missing pretend c was one past the end *)
let find pos s c =
   match String.index_opt s c with
   | None ->
        failat pos ("Unterminated variable substitution (expected '" ^
                        String.make 1 c ^ "')");
        (* String.length s + 1 *)
   | Some n -> n

(* extract argument number from s *)
(* (if we add modifiers, processing them goes in here) *)
let getarg s pos =
   if isnumber s then begin
      let k = int_of_string s in
      if k = 0 then
         failat pos ("Invalid variable " ^ s ^ " (may not be 0)")
      else ();
      USEARG (pos, k - 1)
   end else begin
      failat pos ("Invalid variable " ^ s ^ " (expected number)")(* ;
      LITERAL (pos, s) *)
   end

let rec doparse pos str =
   let len = String.length str in
   if len = 0 then []
   else
      match String.index_opt str '$' with
      | None ->
           (* no more formats; take the rest of the string *)
           [LITERAL (pos, str)]
      | Some 0 ->
           (* we're at a format *)
           let elt, n =
              match doget str 1 with
              | None ->
                   failat pos "Dangling $ in format string"(* ;
                   (fun pos1 -> LITERAL (pos1, "$")), 1 *)
              | Some '$' ->
                   (fun pos1 -> LITERAL (pos1, "$")), 2
              | Some '{' ->
                   let n = find pos str '}' in
                   let elt = getarg (String.sub str 2 (n-3)) in
                   (elt, n)
              | Some '(' ->
                   let n = find pos str ')' in
                   let elt = getarg (String.sub str 2 (n-3)) in
                   (elt, n)
              | Some _ ->
                   let n = count str 1 isdigit in
                   let elt = getarg (String.sub str 1 (n-1)) in
                   (elt, n)
           in
           let (pos1, pos2) = Pos.divide pos n in
           let str' = String.sub str n (len - n) in
           elt pos1 :: doparse pos2 str'
      | Some n ->
           (* not at a format *)
           let (pos1, pos2) = Pos.divide pos n in
           let elt = LITERAL (pos1, String.sub str 0 n) in
           elt :: doparse pos2 (String.sub str n (len - n))

let checkelt (highest, seen) elt =
   match elt with
   | LITERAL _ -> (highest, seen)
   | USEARG (_pos, k) ->
        let highest' = if k > highest then k else highest in
        let seen' = IntSet.add k seen in
        (highest', seen')

let parse pos str =
   let elts = doparse pos str in
   let (highest, seen) =
      List.fold_left checkelt (0, IntSet.empty) elts
   in
   let numparams = highest + 1 in
   if numparams = IntSet.cardinal seen then (numparams, elts)
   else failat pos "Not all arguments used in format"(* ;
   (numparams, elts) *)

let multiparse pos strs =
   let eltses = List.map (doparse pos) strs in
   let (highest, seen) =
      let checkfmt (highest, seen) elts =
         List.fold_left checkelt (highest, seen) elts
      in
      List.fold_left checkfmt (-1, IntSet.empty) eltses
   in
   let numparams = highest + 1 in
   if numparams = IntSet.cardinal seen then
      List.map (fun elts -> (numparams, elts)) eltses
   else failat pos "Not all arguments used in format"(* ;
   List.map (fun elts -> (numparams, elts)) eltses *)

(*
 * apply
 *)

let getnumargs (numparams, _elts) = numparams

let multigetnumargs fs =
   match fs with
   | [] -> 0
   | (numparams, _elts) :: _ -> numparams

let rec divide xs i =
   if i = 0 then ([], xs)
   else match xs with
      | [] -> ([], [])
      | x :: xs' -> let (a, b) = divide xs' (i-1) in (x :: a, b)

let pickargs (numparams, _elts) args =
   divide args numparams

let multipickargs fs args =
   match fs with
   | [] -> ([], args)
   | (numparams, _elts) :: _ -> divide args numparams

let apply' (numparams, elts) args =
   let numargs = List.length args in
   let insert elt =
      match elt with
      | LITERAL _ -> elt
      | USEARG (pos, k) ->
           if k < numargs then LITERAL (pos, List.nth args k)
           else USEARG (pos, k - numargs)
   in
   let elts' = List.map insert elts in
   (numparams - numargs, elts')

let apply pos f args =
   let (useargs, leftoverargs) = pickargs f args in
   if leftoverargs = [] then ()
   else failat pos "Too many arguments for format";
   apply' f useargs

let multiapply pos fs args =
   let (useargs, leftoverargs) = multipickargs fs args in
   if leftoverargs = [] then ()
   else failat pos "Too many arguments for format";
   List.map (fun f -> apply' f useargs) fs

let done_ (numparams, _elts) =
   numparams = 0

let multidone fs =
   List.for_all done_ fs

let finish pos (numparams, elts) =
   if numparams = 0 then ()
   else failat pos ("Not enough arguments for format");
   let once elt =
      match elt with
      | LITERAL (_pos, s) -> s
      | USEARG _ -> failat pos ("Leftover unapplied format entry??")
   in
   String.concat "" (List.map once elts)

let multifinish pos fs =
   List.map (finish pos) fs

(*
 * print
 * (this regurgitates the format string as a string)
 *)

let to_string (_numparams, elts) =
   let string_of_elt elt =
      match elt with
      | LITERAL (_, s) -> s
      | USEARG (_, k) -> "$" ^ string_of_int k
   in
   String.concat "" (List.map string_of_elt elts)

(*
 * compare
 * (ignores the recorded positions)
 * (is not equivalent to string compare of the original format strings)
 *)

let compare'elt elt1 elt2 =
   match elt1, elt2 with
   | LITERAL (_, s1), LITERAL (_, s2) -> compare s1 s2
   | LITERAL _, USEARG _ -> -1
   | USEARG _, LITERAL _ -> 1
   | USEARG (_, k1), USEARG (_, k2) -> compare k1 k2

(* sigh *)
let external_compare = compare

let rec compare (n1, elts1) (n2, elts2) =
   match elts1, elts2 with
   | [], [] -> external_compare n1 n2
   | [], _ :: _ -> -1
   | _ :: _, [] -> 1
   | elt1 :: elts1', elt2 :: elts2' ->
        let r = compare'elt elt1 elt2 in
        if r <> 0 then r else compare (n1, elts1') (n2,  elts2')
