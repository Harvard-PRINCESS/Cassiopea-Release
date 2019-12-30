(*
 * Copyright (c) 2017
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

(*
 * Topological sort of a list of objects. Requires that each object
 * have a unique key and that the dependencies can be expressed as
 * lists of keys.
 *
 * The key type is string. The code could be made polymorphic over the
 * key type by mucking with modules, but for now at least it doesn't
 * seem worthwhile.
 *
 * The tsort function takes three arguments:
 *    getkey, which maps from an object x to its key
 *    getdeps, which maps from an object x to the keys it depends on
 *    xs, the list of xs
 * and returns the list sorted topologically.
 *
 * getkey and getdeps are called only once per object so the information
 * they return does not need to be cached externally.
 *
 * Duplicate keys are not supported; if more than one object returns
 * the same key, only one will be returned in the output. In principle
 * a tsort that does support duplicate keys could be written as a
 * wrapper by grouping duplicates together into lists, but this code
 * is not provided.
 *)

module SM = Util.SM

exception Cyclic of string

let makemap getdeps kxs =
   let doadd map (key, x) =
      let deps = getdeps x in
      SM.add key (x, deps, ref false, ref false) map
   in
   List.fold_left doadd SM.empty kxs

let rec takeone output map key =
   let (x, deps, taken, seen) =
      try
         SM.find key map
      with Not_found ->
         raise (Failure ("tsort: Reference to nonexistent key " ^ key))
   in
   if !taken then ()
   else begin
      if !seen then begin
         raise (Cyclic key)
      end;
      seen := true;
      List.iter (takeone output map) deps;
      seen := false;
      taken := true;
      output := x :: !output;
   end

let tsort getkey getdeps xs =
   let kxs = List.map (fun x -> (getkey x, x)) xs in
   let keys = List.map (fun (k, _x) -> k) kxs in
   let map = makemap getdeps kxs in

   let output = ref [] in
   List.iter (takeone output map) keys;
   List.rev !output


(**************************************************************)
(* test *)

let test_getkey (k, _) = k
let test_getdeps (_, d) = d

let testdata1 = [
   ("alpha", []);
   ("beta", ["alpha"]);
   ("gamma", ["alpha"]);
   ("delta", ["beta"; "gamma"]);
   ("epsilon", ["gamma"; "delta"]);
]

let testdata2 = [
   ("alpha", ["epsilon"]);
   ("beta", ["alpha"]);
   ("gamma", ["alpha"]);
   ("delta", ["beta"; "gamma"]);
   ("epsilon", ["gamma"; "delta"]);
]

let dotest data =
   let data' = tsort test_getkey test_getdeps data in
   List.map test_getkey data'

let _ =
   assert(dotest testdata1 =
          ["alpha"; "beta"; "gamma"; "delta"; "epsilon"]);
   assert(dotest (List.rev testdata1) =
          ["alpha"; "gamma"; "beta"; "delta"; "epsilon"]);
   try
      let _ = dotest testdata2 in
      assert(false)
   with Cyclic x ->
      assert(x = "alpha")
