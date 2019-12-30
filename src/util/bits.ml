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


open Batteries

module BI = BatBig_int

(* bit vector interface to Big_int *)

let big_pow = BI.power_int_positive_int

(* width, value *)
type t = Bits of int * BI.big_int

let zero w = Bits (w, BI.zero_big_int)

let width (Bits (w, _)) = w

(*
 * private operations
 *)

let clamp w n =
  BI.mod_big_int n (big_pow 2 w)

(*
 * comparison
 *)

let bits_compare (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then w1 - w2
  else BI.sign_big_int (BI.sub_big_int n1 n2)

let compare = bits_compare

(*
 * operations
 *)

let extend (Bits (w, n)) l =
  if w > l then
    (* XXX maybe should be assert *)
    failwith ("invalid extend: original "^(string_of_int w)^", got "^(string_of_int l))
  else Bits (l, n)

let get (Bits (_w, n)) d =
  (* assert (d < w); *)
  let mask = BI.power_int_positive_big_int 2 d in
  not (BI.eq_big_int (BI.and_big_int n mask) (BI.zero_big_int))

let getbit (Bits (_w1, n1)) (Bits (_w2, n2)) =
  (* assert (d < w); *)
  let mask = BI.power_int_positive_big_int 2 n2 in
  not (BI.eq_big_int (BI.and_big_int n1 mask) (BI.zero_big_int))

let getfield (Bits (_w, n)) l d1 d2 =
  assert (BI.eq_big_int l (BI.succ_big_int (BI.sub_big_int d2 d1)));
  let init = BI.zero_big_int in
  let len = BI.to_int l in
  let rec field x1 res =
    if BI.gt_big_int x1 d2 then res
    else
      let mask = BI.power_int_positive_big_int 2 x1 in
      let nbit = BI.eq_big_int (BI.and_big_int n mask) (BI.zero_big_int) in
      if nbit then
        let pos = BI.sub_big_int x1 d1 in
        let n' = BI.add_big_int res (BI.power_int_positive_big_int 2 pos) in
        field (BI.succ_big_int x1) n'
      else
        let n' = res in
        field (BI.succ_big_int x1) n'
  in
  Bits (len, (field d1 init))

let set (Bits (w, n)) d =
  let mask = BI.power_int_positive_big_int 2 d in
  let n' = BI.or_big_int n mask in
  Bits (w, n')

let unset (Bits (w, n)) d =
  let mask = BI.power_int_positive_big_int 2 d in
  let limit = big_pow 2 w in
  let one = BI.unit_big_int in
  let unmask = BI.sub_big_int (BI.sub_big_int limit mask) one in
  let n' = BI.and_big_int n unmask in
  Bits (w, n')

let add (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    (* XXX maybe should be assert *)
    failwith "bitvector add of different lengths"
  else
    let n' = BI.add_big_int n1 n2 in
    Bits (w1, clamp w1 n')

let sub (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    failwith "bitvector sub of different lengths"
  else
    let n' = BI.sub_big_int n1 n2 in
    Bits (w1, clamp w1 n')

let mul (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    failwith "bitvector mul of different lengths"
  else
    let n' = BI.mult_big_int n1 n2 in
    Bits (w1, clamp w1 n')

let ult (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    failwith "bitvector ult of different lengths"
  else
    BI.lt_big_int n1 n2

let ugt (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    failwith "bitvector ugt of different lengths"
  else
    BI.gt_big_int n1 n2

let to_signed w n =
  let sign_bit = BI.big_int_of_int (w - 1) in
  if get (Bits (w, n)) sign_bit then
    BI.sub_big_int n (BI.power_int_positive_big_int 2 (BI.succ_big_int sign_bit))
  else n

let slt (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    failwith "bitvector slt of different lengths"
  else
    BI.lt_big_int (to_signed w1 n1)
                  (to_signed w2 n2)

let sgt (Bits (w1, n1)) (Bits (w2, n2)) =
  if w1 <> w2 then
    failwith "bitvector sgt of different lengths"
  else
    BI.gt_big_int (to_signed w1 n1)
                  (to_signed w2 n2)

let not (Bits (w, n)) =
  let limit = big_pow 2 w in
  let one = BI.unit_big_int in
  let n' =
     BI.sub_big_int (BI.sub_big_int limit n) one
  in
  Bits (w, n')

let and_ (Bits (w1, n1)) (Bits (w2, n2)) =
  assert (w1 = w2);
  Bits (w1, BI.and_big_int n1 n2)

let or_ (Bits (w1, n1)) (Bits (w2, n2)) =
  assert (w1 = w2);
  Bits (w1, BI.or_big_int n1 n2)

let xor (Bits (w1, n1)) (Bits (w2, n2)) =
  assert (w1 = w2);
  Bits (w1, BI.xor_big_int n1 n2)

let lshift (Bits (w, n)) d =
  let n' = clamp w (BI.shift_left_big_int n (BI.int_of_big_int d)) in
  Bits (w, n')

let rshift (Bits (w, n)) d =
  let n' = clamp w (BI.shift_right_big_int n (BI.int_of_big_int d)) in
  Bits (w, n')

let rotl (Bits (w, n)) d =
  let n'l = clamp w (BI.shift_left_big_int n (BI.int_of_big_int d)) in
  let subd = w - (BI.to_int d) in
  let n'r = clamp w (BI.shift_right_big_int n subd) in
  let n' = BI.or_big_int n'l n'r in
  Bits (w, n')

let rotr (Bits (w, n)) d =
  let n'l = clamp w (BI.shift_right_big_int n (BI.int_of_big_int d)) in
  let subd = w - (BI.to_int d) in
  let n'r = clamp w (BI.shift_left_big_int n subd) in
  let n' = BI.or_big_int n'l n'r in
  Bits (w, n')

let concat (Bits (w1, n1)) (Bits (w2, n2)) =
  let rhs = lshift (Bits (w1 + w2, n1)) (BI.big_int_of_int w2) in
  or_ rhs (Bits (w1 + w2, n2))

let check_byte_align (Bits (_w, n)) times =
  let last_two = BI.and_big_int n (BI.big_int_of_int (times - 1)) in
  if BI.compare_big_int last_two (BI.zero_big_int) == 0 then true
  else false
  (* let mod_res = BI.mod_big_int n (BI.big_int_of_int 4) in
  if BI.compare_big_int mod_res (BI.zero_big_int) == 0 then true
  else false *)

let check_boundary (Bits (_w, n)) max =
  (BI.le_big_int (BI.zero_big_int) n) &&
  (BI.lt_big_int n (BI.big_int_of_int max))

let get_max w =
  let v = BI.sub_big_int (BI.power_int_positive_int 2 w) BI.unit_big_int in
  Bits (w, v)

(*
 * conversions
 *)

let of_big_int w n = Bits (w, clamp w n)
let of_int w n = of_big_int w (BI.big_int_of_int n)

let to_big_int (Bits (_, n)) = n
let to_big_int_signed (Bits (w, n)) = to_signed w n
let to_int (Bits (_, n)) = BI.int_of_big_int n

let of_string s =
  assert (String.get s 0 = '0');
  let bitsper =
    match (String.get s 1) with
      'x' | 'X' -> 4
    | 'b' -> 1
    | _ -> assert false
  in
  (* in the following, -2 because of 0x/0b prefix *)
  let width = (String.length s - 2) * bitsper in
  Bits (width, BI.big_int_of_string s)

let to_string (Bits (width, n)) =
  let (base, logbase, prefix) =
    if width mod 4 = 0 then (16, 4, "0x")
    else (2, 1, "0b")
  in
  let base = BI.big_int_of_int base in
  let todigit x =
    if x < 10 then string_of_int x
    else String.make 1 (String.get "abcdef" (x - 10))
  in
  let rec todigits x =
     if BI.eq_big_int x BI.zero_big_int then []
     else begin
        let (q, r) = BI.quomod_big_int x base in
        todigit (BI.int_of_big_int r) :: todigits q
     end
  in
  let digits = List.rev (todigits n) in
  let zeros = (width / logbase) - List.length digits in
  let zeros = if zeros >= 0 then zeros else 0 in
  prefix ^ String.make zeros '0' ^ String.concat "" digits

let to_bitstring (Bits (width, n)) =
  let s = BI.to_string_in_binary n in
  let z = BatString.repeat "0" (width - BatString.length s) in
  "0b" ^ z ^ s

let to_binarystring (Bits (width, n)) =
  let s = BI.to_string_in_binary n in
  let z = BatString.repeat "0" (width - BatString.length s) in
  z ^ s

let to_bstring (Bits (width, n)) =
  let s = BI.to_string_in_binary n in
  let z = BatString.repeat "0" (width - BatString.length s) in
  "#b" ^ z ^ s


let to_hexstring (Bits (width, n)) =
  let s = BI.to_string_in_hexa n in
  let z = BatString.repeat "0" ((width+3)/4 - BatString.length s) in
  "0x" ^ z ^ s

let to_hexdecimalstring (Bits (width, n)) =
  let s = BI.to_string_in_hexa n in
  let z = BatString.repeat "0" ((width+3)/4 - BatString.length s) in
  z ^ s

let to_xstring (Bits (width, n)) =
  let s = BI.to_string_in_hexa n in
  let z = BatString.repeat "0" ((width+3)/4 - BatString.length s) in
  "#x" ^ z ^ s


(* quick unit test for to_string *)

let _ =
  let test w n r =
     let s = to_string (Bits (w, BI.big_int_of_int n)) in
     if s <> r then failwith ("to_string test failed: " ^ r ^ " got " ^ s)
  in
  test 8 0 "0x00";
  test 7 0 "0b0000000";
  test 2 0 "0b00";
  test 1 0 "0b0";
  test 4 0 "0x0";
  test 1 1 "0b1";
  test 1 3 "0b11";
  test 8 257 "0x101";
  test 16 49152 "0xc000"
