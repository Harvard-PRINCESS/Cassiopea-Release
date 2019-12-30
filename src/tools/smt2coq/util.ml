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

let say msg =
   prerr_string msg;
   prerr_newline ()

let crash msg =
   prerr_string msg;
   prerr_newline ();
   exit 1

let ttysay msg =
   try
      let f = open_out "/dev/tty" in
      output_string f (msg ^ "\n");
      close_out f
   with _ -> ()

let number xs =
   let rec f n xs =
      match xs with
           [] -> []
         | x :: more -> (n, x) :: f (n + 1) more
   in
   f 0 xs

let repeat k x = List.init k (fun _ -> x)
let count k = List.init k (fun x -> x)

let rec take n xs =
   match n, xs with
   | 0, _ -> []
   | _, [] -> []
   | _, x :: xs' -> x :: take (n-1) xs'

let unzip xs = List.split xs
let zip xs ys = List.combine xs ys

let rec zip' xs ys =
   match xs, ys with
   | [], [] -> []
   | (x :: xs'), (y :: ys') -> (x, y) :: zip' xs' ys'
     (* like haskell's zip drop unmatched portions *)
   | [], _ :: _ -> []
   |  _ :: _, [] -> []

let rec untailcons xs =
   match xs with
   | [] -> raise (Failure "untailcons")
   | [x] -> ([], x)
   | x :: more -> let (more', last) = untailcons more in (x :: more', last)

let rec intersperse k xs =
   match xs with
   | [] -> []
   | [x] -> [x]
   | x :: y :: more -> x :: k :: intersperse k (y :: more)

let cartesian xs ys =
   let cart2 x =
      List.map (fun y -> (x, y)) ys
   in
   List.concat (List.map cart2 xs)
