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


module Bat = Batteries
module P   = Printf
module BI  = BatBig_int
module BInt = BatInt
module R   = BatText

open BatFormat

include Settings

module IntMap = Map.Make(struct type t=int let compare=compare end)
module StringMap  = Map.Make(String)
module Big_intMap = Map.Make(BI)
module BitsMap    = Map.Make(Bits)

module IM  = IntMap
module SM  = StringMap
module BIM = Big_intMap
module BM  = BitsMap

module IntSet = Set.Make(struct type t=int let compare=compare end)
module StringSet = Set.Make(String)
module BitsSet = Set.Make(Bits)

module SS = StringSet
module IS = IntSet
module BS = BitsSet

type rope = R.t
type bint = BI.t
type bits = Bits.t
type id = string

let ( ++ )  = (^)
let ( +++ ) = R.(^^^)

(* int2bv helper functions *)
let rec get_minwidth_rec n i = (* n: int *)
  if ((BInt.pow 2 i) <= n) && ((BInt.pow 2 (i + 1)) > n) then (i + 1)
  else get_minwidth_rec n (i + 1)
let get_min_width n = get_minwidth_rec (n * 4) 1

let get_maxbv_width width =
  BI.sub_big_int (BI.power_int_positive_int 2 width) BI.unit_big_int

let rla rl a = rl := a :: !rl
let arl rl a = rl := !rl @ [a]

let flap f l =
  l |> List.map f |> List.flatten

let string_of_list d f l =
  l |> List.map f |> String.concat d

let is_uniform_list = function
  | [] | [_] -> true
  | x :: t   -> List.for_all (fun y -> y = x) t

let maybe_filter = BatList.filter_map

let zip   = List.combine
let unzip = List.split

let string_of_bint = BI.to_string
let string_of_bits = Bits.to_string

let bitstring_of_bint b = "0b" ++ BI.to_string_in_binary b
let hexstring_of_bint b = "0x" ++ BI.to_string_in_hexa b
let bint_of_string = BI.of_string

let bint_of_int = BI.big_int_of_int
let int_of_bint = BI.int_of_big_int

let bint_clamp w n =
  BI.mod_big_int n (BI.power_int_positive_big_int 2 w)

type wrapper =
  | PAREN
  | BRACKET
  | BRACE
  | COLON

let ch_wrap s = function
  | PAREN   -> "(" ++ s ++ ")"
  | BRACKET -> "[" ++ s ++ "]"
  | BRACE   -> "{" ++ s ++ "}"
  | COLON   -> ":" ++ s ++ ":"

(* get list with numbers [a; a + 1; ...; b - 1] *)
let range a b =
  let rec range_ a b l =
    if a >= b then l
    else range_ (a + 1) b (a :: l)
  in
  List.rev (range_ a b [])

(* same but for big_int *)
let range_big a b =
  let rec range_ a b l =
    if BI.ge_big_int a b then l
    else range_ (BI.succ_big_int a) b (a :: l)
  in
  List.rev (range_ a b [])

(* split list into (first n-1 elements, nth element, rest of list) *)
let split_at l n =
  let rec split_inner n pre post =
    match post with
    | h :: t ->
      if n == 0 then
        (pre, h, t)
      else
        split_inner (n - 1) (pre @ [h]) t
    | [] -> failwith ("list too short by "^(string_of_int (n + 1)))
  in
  split_inner n [] l

let failat p msg =
  failwith ((Pos.string_of p)^": "^msg)

let shuffle ls =
  let ils = List.map (fun v -> (Random.bits (), v)) ls in
  List.map snd (List.sort (fun v1 v2 -> compare (fst v1) (fst v2)) ils)

let will_whiten src =
  !settings.seed <> 0 &&
  List.exists ((=) src) !settings.whiten

let print_log pattern =
  P.fprintf !settings.log_ch pattern

let print_out pattern =
  P.fprintf !settings.out_ch pattern

let flush_log () = flush !settings.log_ch

let flush_out () = flush !settings.out_ch
