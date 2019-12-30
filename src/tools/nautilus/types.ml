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

(*
 * Does ocaml have something native of this form? I haven't been able to
 * find one.
 *)
type ('a, 'b) emulsion = OIL of 'a | WATER of 'b

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

(* Why doesn't this come with Map? *)
let stringmap_of_list kvs =
   let doadd z (k, v) = StringMap.add k v z in
   List.fold_left doadd StringMap.empty kvs

(* Especially since this *does* come with Set? *)
let stringset_of_list strs =
   StringSet.of_list strs
(*
   let doadd z str = StringSet.add str z in
   List.fold_left doadd StringSet.empty strs
*)

(* stringmap_of_list but with key extraction function instead of pairs *)
let stringmap_of_list_by_key getkey vs =
   let doadd z v = StringMap.add (getkey v) v z in
   List.fold_left doadd StringMap.empty vs

(* Why doesn't this come with Map either? *)
let stringmap_keys m =
   List.map (fun (k, _v) -> k) (StringMap.bindings m)

(* Map.union isn't in the ocaml on debian stale *)
let stringmap_union (f: string -> 'a -> 'a -> 'a option) m1 m2 =
   (* this equivalence is from the docs *)
   let f' k v1 v2 = match v1, v2 with
        None, None -> None
      | Some v, None -> Some v
      | None, Some v -> Some v
      | Some v1', Some v2' -> f k v1' v2'
   in
   StringMap.merge f' m1 m2

(* union over a list of sets *)
let stringset_unionall sets =
   List.fold_left StringSet.union StringSet.empty sets

(* StringMap.mapi in a specific external order *)
(* (caller is responsible for making sure keys has all keys exactly once) *)
let stringmap_mapi_inorder f map keys =
   let once newmap k =
      let v = StringMap.find k map in
      StringMap.add k (f k v) newmap
   in
   List.fold_left once StringMap.empty keys

(* Same, but iter *)
let stringmap_iter_inorder f map keys =
   let once k =
      let v = StringMap.find k map in
      f k v
   in
   List.iter once keys

(* Same, but bindings *)
let stringmap_bindings_inorder map keys =
   let once k bs =
      let v = StringMap.find k map in
      (k, v) :: bs
   in
   List.fold_right once keys []

(* Check that an order (for *_inorder) is well formed *)
let stringmap_assert_okorder map keys =
   let once_keys mseen k =
      try
         ignore (StringMap.find k map);
         StringSet.add k mseen
      with Not_found ->
         Util.crash ("stringmap_assert_inorder: key " ^ k ^ " not in map")
   in
   let mseen = List.fold_left once_keys StringSet.empty keys in
   let once_map k _ =
      if StringSet.mem k mseen then ()
      else Util.crash ("stringmap_assert_inorder: key " ^ k ^ " not in keys")
   in
   StringMap.iter once_map map

module IntMap = Map.Make(struct type t = int let compare = compare end)
module IntSet = Set.Make(struct type t = int let compare = compare end)

(* union over a list of sets *)
let intset_unionall sets =
   List.fold_left IntSet.union IntSet.empty sets

(*
 * Scope (nesting stringmap)
 *)

type 'a scope = {
   bindings: 'a StringMap.t;
   parent: 'a scope option;
}

let newscope parent = {
   bindings = StringMap.empty;
   parent = parent;
}

let emptyscope = newscope None

let scope_add k v s =
   let bindings = StringMap.add k v s.bindings in
   { s with bindings; }

let rec scope_find k s =
   try
      Some (StringMap.find k s.bindings)
   with Not_found ->
      match s.parent with
           None -> None
         | Some p -> scope_find k p

let scope_mem k s =
   scope_find k s <> None

let scope_mem_here k s =
   StringMap.mem k s.bindings

let scope_push s = newscope (Some s)
let scope_pop s =
   match s.parent with
        None -> Util.crash "scope_pop: unmatched"
      | Some p -> p
