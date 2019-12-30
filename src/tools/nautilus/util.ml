(*
 * Copyright (c) 2016
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

let die () =
   exit 1

let say msg =
   prerr_string msg;
   prerr_newline ()

let crash msg =
   say msg;
   die ()

let failed = ref 0
let fail () =
   failed := !failed + 1

let checkfail () =
   if !failed = 1 then begin
      say "Fatal error.";
      die ()
   end
   else if !failed > 1 then begin
      say (string_of_int !failed ^ " fatal errors.");
      die ()
   end
   else ()

(* XXX: check if there's a better way to do 2^n *)
(* XXX: also most users should probably be using Types.Wide.twoN *)
let rec power base n =
   if n = 0 then 1
   else if n = 1 then base
   else base * (power base (n - 1))

exception LogZero
let rec ilog2 x =
   if x >= 256 then 8 + (ilog2 (x/256))
   else if x >= 16 then 4 + (ilog2 (x/16))
   else if x >= 2 then 1 + (ilog2 (x/2))
   else if x > 0 then 0
   else raise LogZero

(* produces the value k bits wide with all 1-bits *)
let ones k =
   (power 2 k) - 1

let alleq xs = match xs with
     [] -> true
   | [_] -> true
   | x :: more -> List.for_all ((=) x) more

let rec intersperse a xs =
   match xs with
        [] -> []
      | [x] -> [x]
      | x :: more -> x :: a :: intersperse a more

let zip (xs : 'x list) (ys : 'y list) : ('x * 'y) list =
   List.map2 (fun x y -> (x, y)) xs ys
   (* or List.combine I guess *)

(* allows the lengths to not match, and truncates the longer list *)
let rec zip' (xs : 'x list) (ys : 'y list) : ('x * 'y) list =
   match xs, ys with
        x :: xmore, y :: ymore -> (x, y) :: zip' xmore ymore
      | [], _ -> []
      | _, [] -> []

let unzip xs = List.split xs

let rec unzip3 xs =
   match xs with
        [] -> ([], [], [])
      | (x, y, z) :: more ->
           let (xs, ys, zs) = unzip3 more in
           (x :: xs, y :: ys, z :: zs)

let number xs =
   let rec f n xs =
      match xs with
           [] -> []
         | x :: more -> (n, x) :: f (n + 1) more
   in
   f 0 xs

let rec take n xs =
   match (n, xs) with
        (0, _) -> []
      | (_, []) -> []
      | (n, x :: more) -> x :: take (n-1) more

let optmap f op = match op with
     None -> None
   | Some x -> Some (f x)

let autogenstr =
   "/* Automatically generated; do not edit */\n\n"

let writeout filename str =
   let outfile = open_out filename in
   output_string outfile str;
   close_out outfile

let test () =
   let xs = [0; 1; 2] in
   let ys = ["a"; "b"; "c"] in
   let ys2 = ["a"; "b"; "c"; "d"] in
   if (zip xs ys) <> (number ys) then
      crash ("util: zip or number failed to work properly");
   if (zip' xs ys2) <> (number ys) then
      crash ("util: zip' failed to work properly");
   if intersperse 3 xs <> [0; 3; 1; 3; 2] then
      crash ("util: intersperse failed to work properly");
   if ilog2 65535 <> 15 then
      crash ("util: ilog2 failed to work properly")
