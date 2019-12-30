(*
 * Support elements.
 *)

Require Import Arith ZArith Omega.
Require Import List.
Import ListNotations.
Require Import OrderedType OrderedTypeEx.
Require FMapAVL FMapFacts.

(*
 * Identifiers. Because Coq's string library is crap, use nats as
 * variable names.
 *
 * (Could wrap/newtype this for paranoia, but there doesn't seem to be
 * any immediate reason to bother, at least for now.)
 *)
Definition ident := nat.

(*
 * We'll also use nats for string literals.
 *)
Definition stringliteral := nat.

(*
 * We'll use Z for math integers, because we need to allow them to be
 * negative.
 *)
Definition integer := Z.

(*
 * For modeling purposes we'll use nats for bitvectors/machine
 * integers. This is good enough for now; we can substitute some
 * other machine integer or bitvector library later.
 *
 * Might need to not throw away the size though :-/
 *)
Definition bitvector (k: nat) := nat.

(*
 * Maps
 *)
Module NatMap := FMapAVL.Make Nat_as_OT.
Module NatMapFacts := FMapFacts.WFacts_fun Nat_as_OT NatMap.

Module IdentMap := NatMap.
Module IdentMapFacts := NatMapFacts.

Module BitvecMap := NatMap.
Module BitvecMapFacts := NatMapFacts.

Fixpoint identmap_add_many {T: Type}
                (kvs: list (ident * T)) (m: IdentMap.t T) : IdentMap.t T :=
   match kvs with
   | [] => m
   | (k, v) :: kvs' => identmap_add_many kvs' (IdentMap.add k v m)
   end.


