Require Import Arith Omega.
Require Import List. Import ListNotations.
Require Import OrderedType OrderedTypeEx.
Require FMapList FMapFacts.

(*************************************************************)
(*************************************************************)
(* problem elements *)

(*
 * A machine value
 *)
Inductive Value: Set :=
| MkValue (k: nat).

(*
 * identity of a state element: a register name
 *
 * XXX: this should probably be explicitly finite;
 * but so far it doesn't seem to matter.
 *)
Inductive Regname: Set :=
| MkRegname (elt: nat).

Definition Regname_lt a b :=
      match a, b with
      | MkRegname a', MkRegname b' => a' < b'
      end.

Module Regname_as_OT <: UsualOrderedType.
   Definition t := Regname.
   Definition eq (a b: t) := @eq t a b.
   Definition lt (a b: t) := Regname_lt a b.
   Definition eq_refl : (forall x : t, x = x) := @eq_refl t.
   Definition eq_sym := @eq_sym t.
   Definition eq_trans := @eq_trans t.
   Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
   Proof.
      unfold lt. unfold Regname_lt.
      intros.
      destruct x; destruct y; destruct z.
      apply Nat.lt_trans with (m := elt0); auto.
   Qed.
   Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
   Proof.
      unfold lt. unfold Regname_lt. unfold eq.
      intros. intro.
      destruct x; destruct y.
      injection H0; intros; subst; omega.
   Qed.
   Lemma compare : forall x y : t, Compare lt eq x y.
      unfold lt. unfold Regname_lt. unfold eq.
      intros.
      destruct x; destruct y.
      destruct (Nat.compare elt elt0) eqn:H.
      - apply EQ. rewrite Nat.compare_eq_iff in H. subst; auto.
      - apply LT. rewrite Nat.compare_lt_iff in H. auto.
      - apply GT. rewrite Nat.compare_gt_iff in H. auto.
   Qed.
   Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
   Proof.
      intros. destruct x; destruct y. unfold eq.
      destruct (Nat.eq_dec elt elt0).
      - subst. left. auto.
      - right. congruence.
   Qed.
End Regname_as_OT.

(*
 * state: a value for every register
 *)

Module RegnameMap := FMapList.Make Regname_as_OT.
Module RegnameMapFacts := FMapFacts.WFacts_fun Regname_as_OT RegnameMap.

Definition MachineState := RegnameMap.t Value.

(*
 * instruction
 *)
Inductive Insn: Set :=
| MkInsn (opcode: nat).

(*
 * instruction semantics
 *)
Axiom evalinsn: Insn -> MachineState -> MachineState.


(*************************************************************)
(*************************************************************)
(* program *)

Definition Program := list Insn.

Fixpoint eval (p: Program) (s: MachineState) : MachineState :=
   match p with
   | [] => s
   | insn :: more => eval more (evalinsn insn s)
   end.


(*************************************************************)
(*************************************************************)
(* specification *)

Inductive Spec :=
| MkSpec (pre post: MachineState -> Prop)
         (pre_dec: forall s, {pre s} + {~pre s})
         (post_dec: forall s, {post s} + {~post s}).

Definition satisfies (spec: Spec) (p: Program) (s: MachineState) :=
   match spec with
   | MkSpec precondition postcondition _ _ =>
        precondition s ->
        exists s', s' = eval p s /\ postcondition s'
   end.

Definition correct (spec: Spec) (p: Program) := forall s, satisfies spec p s.


(*************************************************************)
(*************************************************************)
(* solver *)

Axiom guess_solver: forall (P: Program -> Prop), option Program.
Axiom guess_solver_success: forall P p, guess_solver P = Some p -> P p.
Axiom guess_solver_failure: forall P, guess_solver P = None -> ~exists p, P p.

Lemma guess_solver_clarify: forall (P: Program -> Prop), {exists p, P p} + {~exists p, P p}.
Proof.
   intro.
   destruct (guess_solver P) eqn:H.
   - apply guess_solver_success in H. left. exists p. auto.
   - apply guess_solver_failure in H. right. auto.
Qed.

Fixpoint guess_prop (spec: Spec) (startstates: list MachineState) (p: Program) :=
   match startstates with
   | [] => True
   | startstate :: more => satisfies spec p startstate /\ guess_prop spec more p
   end.
Definition guess (spec: Spec) (startstates: list MachineState) :=
   guess_solver (guess_prop spec startstates).

Lemma guess_prop_in:
   forall startstate spec startstates p,
   guess_prop spec startstates p ->
   In startstate startstates ->
   satisfies spec p startstate.
Proof.
   intros.
   induction startstates; simpl in *; try contradiction.
   destruct H.
   destruct H0.
   - subst. auto.
   - auto.
Qed.
Lemma guess_success:
   forall spec startstates p, guess spec startstates = Some p ->
   (forall startstate,
    In startstate startstates ->
    satisfies spec p startstate).
Proof.
   intros.
   unfold guess in H.
   apply guess_solver_success in H.
   apply (guess_prop_in startstate) in H; auto.
Qed.
Lemma guess_failure:
   forall spec startstates, guess spec startstates = None ->
   (exists p,
    forall startstate,
    In startstate startstates ->
    satisfies spec p startstate) -> False.
Proof.
   intros.
   destruct H0 as [p H0].
   unfold guess in H.
   apply guess_solver_failure in H.
   contradict H.
   exists p.
   induction startstates; simpl; auto.
   simpl in H0.
   split.
   - apply (H0 a). left; auto.
   - apply IHstartstates. intros. apply (H0 startstate). right; auto.
Qed.

Axiom check_solver: forall (P: MachineState -> Prop), option MachineState.
Axiom check_solver_success: forall P, check_solver P = None -> ~exists s, P s.
Axiom check_solver_failure: forall P s, check_solver P = Some s -> P s.

(*
 * It is important that when checking you only allow the solver to return
 * counterexamples that satisfy the precondition. Otherwise the progress
 * lemma can't be proved: the next guess can be the same and therefore
 * the cegis loop can produce the same guess and useless counterexample
 * infinitely many times.
 *
 * Thus we assert pre startstate /\ ~ post endstate
 * and NOT pre startstate -> ~ post endstate.
 *)
Definition check_prop (spec: Spec) (p: Program) (startstate: MachineState) :=
   match spec with
   | MkSpec pre post _ _ => pre startstate /\ ~ post (eval p startstate)
   end.
Definition check (spec: Spec) (p: Program) :=
   check_solver (check_prop spec p).

Lemma check_success: forall spec p, check spec p = None -> correct spec p.
Proof.
   intros.
   apply check_solver_success in H.
   unfold check_prop in H.
   unfold correct.
   unfold satisfies.
   intros.
   destruct spec.
   intros.
   exists (eval p s). split; auto.
   destruct (post_dec (eval p s)); auto.
   contradict H.
   exists s.
   split; auto.
Qed.
Lemma check_failure:
   forall spec p counter, check spec p = Some counter ->
   match spec with
   | MkSpec pre post _ _ =>
        pre counter /\  (* likewise, here use /\ and not -> *)
        exists s', s' = eval p counter /\ ~post s'
   end.
Proof.
   intros.
   apply check_solver_failure in H.
   unfold check_prop in H.
   destruct spec.
   destruct H.
   split; auto.
   exists (eval p counter).
   split; auto.
Qed.


(*************************************************************)
(*************************************************************)
(* cegis *)

Inductive result: Type := FAILURE | SUCCESS (p: Program) | TRYAGAIN (ce: MachineState).

Definition once (spec: Spec) (startstates: list MachineState) :=
   match guess spec startstates with
   | None => FAILURE
   | Some p =>
        match check spec p with
        | None => SUCCESS p
        | Some ce => TRYAGAIN ce
        end
   end.

Theorem cegis_progress:
   forall spec startstates counter,
   once spec startstates = TRYAGAIN counter -> ~In counter startstates.
Proof.
   intros. intro.
   unfold once in H.
   destruct (guess spec startstates) eqn:Hguess; try discriminate.
   destruct (check spec p) eqn:Hcheck; try discriminate.
   injection H; intros; subst.
   apply check_failure in Hcheck.
   destruct spec.
   destruct Hcheck as [Hpre [s' [Hpost1 Hpost2]]].
   apply guess_success with (startstate := counter) in Hguess; auto.
   unfold satisfies in Hguess.
   specialize (Hguess Hpre).
   destruct Hguess as [s'' [Hguess1 Hguess2]].
   assert (s'' = s') by congruence; subst.
   contradiction.
Qed.

Theorem cegis_works:
   forall spec startstates p,
   once spec startstates = SUCCESS p -> correct spec p.
Proof.
   unfold once.
   intros.
   destruct (guess spec startstates); try discriminate.
   destruct (check spec p0) eqn:H0; try discriminate.
   injection H; intros; subst.
   apply check_success in H0.
   auto.
Qed.

