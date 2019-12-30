(*
 * x y z variables   (v i k j vars, id globals)
 * C integer literals
 * 0bC 0xC bitvector literals
 *)

Require Import Arith Omega.
Require Import List.
Import ListNotations.

Require Import support.

(**************************************************************)
(**************************************************************)
(*                           SYNTAX                           *)
(**************************************************************)
(**************************************************************)


(*
 * in the TR, this is N.
 *)
Inductive numbersym :=
| N_number (c: nat)
| N_symbol (x: ident)		(* originally this x was "id", aka global *)
.

(*
 * base types
 * in the TR, this is
 * \tau_{base}
 * \tau_{reg}
 * \tau_{label}
 *)
Inductive basetypename: Set :=
| UNITTYPE
| BOOLTYPE
| INTTYPE
| NAMEDTYPE (x: ident)
| BITTYPE (n: numbersym)	(* N bit *)
| REGTYPE (n: numbersym)	(* N reg *)
| LABELTYPE (n: numbersym)	(* N label *)
.

(*
 * types
 * in the TR, this is
 * \tau
 * \tau_{regs}
 * \tau_{mem}
 * \tau_{func}
 *)
Inductive typename: Type :=
| BASETYPE (ty: basetypename)
| REGSETTYPE (n: numbersym)	(* N reg set *)
| MEMTYPE (n1 n2 n3: numbersym)	(* N1 bit N2 len N3 ref *)
| FUNCTYPE (params: list basetypename) (ret: basetypename)  (* t1 t2 -> t3 *)
.

(*
 * unary operators
 * (unop in the TR)
 *)
Inductive uop: Set :=
| NEG
| LOGNOT
.

(*
 * binary operators
 * (binop in the TR)
 *)
Inductive bop: Set :=
| INTADD
| INTSUB
| INTMUL
| INTDIV
| EQ
| INTLT
| INTGT
| NEQ
| LOGOR
| LOGAND
| LOGXOR
| SHR
| SHL
| BITAND
| BITOR
| BITXOR
| BITADD
| BITSUB
| BITMUL
| BITULT
| BITUGT
| BITSLT
| BITSGT
.

(*
 * expressions
 * in the TR, this is e
 *)
Inductive expr: Type :=
| READVAR (x: ident)		(* originally this x was "id", aka global *)
| TRUE
| FALSE
| INTCONST (c: integer)
| BITCONST (k: nat) (c: bitvector k)
| FAIL
| CALL (func: ident) (args: exprs)	(* originally func was a global *)
| UOP (op: uop) (e1: expr)
| BOP (op: bop) (e1 e2: expr)
| GETBIT (e1 e2: expr)
| GETBITSLICE (e1 e2 e3: expr)
| LET_E (x: ident) (ty: typename) (e1 e2: expr)	(* x is not global *)
| IF_E (c t f: expr)
| POINTER (base: ident) (offset: expr)
| LABEL (label: ident)
| FETCH (e1: expr)
| ISPTR (e1: expr)
| BASE (e1: expr)
| OFFSET (e1: expr)
| READREG (e1: expr)
| SET (elements: exprs)
| LENGTH (e1: expr)
| IN (x: ident) (e1: expr)
| SUBSET (e1 e2: expr)
| UNION (e1 e2: expr)
| INTERSECT (e1 e2: expr)
with
exprs :=
| EXPRNIL
| EXPRCONS (e1: expr) (es: exprs)
.

(*
 * string expressions
 * in the TR, this is string
 *)
Inductive stringexpr :=
| STRINGLITERAL (text: stringliteral)
| VARTEXT (x: ident)			(* x can be either global or not *)
| APPEND (se1 se2: stringexpr)
.

(*
 * statements
 * in the TR, this is S
 *)
Inductive stmt: Type :=
| SEQ (s1 s2: stmt)
| LET_S (x: ident) (ty: typename) (e1: expr) (s2: stmt) (* x is not global *)
| FOR (x: ident) (upperbound: integer) (s1: stmt) (* x is not global *)
| IF_S (c: expr) (t f: stmt)
| WRITEREG (e1 e2: expr)
| STORE (e1 e2: expr)
| ASSERT (e1: expr)
| SKIP
| HALT
.

(*
 * declarations
 * in the TR, this is declaration
 *
 * x is global in all of these
 *)
Inductive decl: Type :=
| TYPEDECL (x: ident) (ty: basetypename)
| LET_D (x: ident) (ty: basetypename) (e1: expr)
| LETTEXT (x: ident) (text: stringliteral)
| DEF (x: ident) (params: list (ident * basetypename)) (ret: basetypename) (e1: expr)
| REGDECL (x: ident) (n: numbersym)	(* letstate for registers *)
| MEMDECL (x: ident) (cw len pw: numbersym) (* letstate for memory *)
| LABELDECL (x: ident) (cw len pw: numbersym) (label: ident) (* labels *)
.

(*
 * instructions
 * in the TR, this is def-inst, except that a def-inst is a list of them
 *)
Inductive insn: Type :=
| DEFINSN (x: ident) (params: list (ident * basetypename))
      (text: stringexpr) (s1: stmt)
.

(*
 * machines
 * in the TR, this is machine
 *)
Definition machine: Type := list decl * list insn.

(*
 * quantifier expressions
 * in the TR, thse are \phi_\forall, \phi_\exists
 * \phi is just e, so I haven't materialized it.
 *)
Inductive exists_expr: Type :=
| EXISTS (names: list (ident * basetypename)%type) (e1: expr).
Inductive forall_expr: Type :=
| FORALL (names: list (ident * basetypename)%type) (e1: exists_expr).

(*
 * frames
 * in the TR, this is frame
 *)
Definition frame: Type := list ident * list ident.

(*
 * specs
 * in the TR, this is define-spec
 *)
Inductive spec: Type :=
| SPEC (decls: list decl) (frame: frame) (pre post: forall_expr).

(*
 * invocation (call of an instruction)
 *)
Inductive invocation: Type :=
| INVOCATION (opcode: ident) (operands: exprs).

(*
 * programs
 * (list of instruction invocations)
 *)
Definition program : Type := list invocation.


(**************************************************************)
(**************************************************************)
(*                            TYPES                           *)
(**************************************************************)
(**************************************************************)

Definition tyenv := IdentMap.t typename.

Definition tyenv_empty := IdentMap.empty typename.

(* In for exprs *)
Inductive ExprsIn: expr -> exprs -> Prop :=
| ExprsHere: forall e es,
     ExprsIn e (EXPRCONS e es)
| ExprsThere: forall e e' es,
     ExprsIn e es ->
     ExprsIn e (EXPRCONS e' es)
.

(*
 * Type well-formedness rules
 *)

(* this is my factoring; it's not in the TR *)
(* this is for being suitable as a bit size, hence positivity *)
(* (though we don't try to restrict the symbol form to positive numbers) *)
Inductive Numbersym_wf (G: tyenv): numbersym -> Prop :=
| N_number_wf: forall k,
     k > 0 ->
     Numbersym_wf G (N_number k)
| N_symbol_wf: forall x,
     IdentMap.MapsTo x (BASETYPE INTTYPE) G ->
     Numbersym_wf G (N_symbol x)
.

Inductive Typename_wf (G: tyenv): typename -> Prop :=
| UNIT_wf:
     Typename_wf G (BASETYPE UNITTYPE)
| BOOL_wf:
     Typename_wf G (BASETYPE BOOLTYPE)
| INT_wf:
     Typename_wf G (BASETYPE INTTYPE)
| NAMED_wf: forall x ty,
     IdentMap.MapsTo x ty G ->
     Typename_wf G ty ->
     Typename_wf G (BASETYPE (NAMEDTYPE x))
| BIT_wf: forall n,
     Numbersym_wf G n ->
     Typename_wf G (BASETYPE (BITTYPE n))
| REG_wf: forall n,
     Numbersym_wf G n ->
     Typename_wf G (BASETYPE (REGTYPE n))
| LABEL_wf: forall n,
     Numbersym_wf G n ->
     Typename_wf G (BASETYPE (LABELTYPE n))
| REGSET_wf: forall n,
     Numbersym_wf G n ->
     Typename_wf G (REGSETTYPE n)
| MEM_wf: forall n1 n2 n3,
     Numbersym_wf G n1 ->
     Numbersym_wf G n2 ->
     Numbersym_wf G n3 ->
     Typename_wf G (MEMTYPE n1 n2 n3)
| FUNC_wf: forall params ret,
     (forall bty, List.In bty params -> Typename_wf G (BASETYPE bty)) ->
     Typename_wf G (BASETYPE ret) ->
     Typename_wf G (FUNCTYPE params ret)
.

(* this is also my factoring *)
Inductive Params_wf (G: tyenv): list (ident * basetypename) -> Prop :=
| Params_nil_wf:
     Params_wf G []
| Params_cons_wf: forall x ty more,
     Typename_wf G (BASETYPE ty) ->
     Params_wf G more ->
     Params_wf G ((x, ty) :: more)
.

Fixpoint identmap_add_params (xtys: list (ident * basetypename))
                                (m: IdentMap.t typename) :=
   match xtys with
   | [] => m
   | (x, ty) :: xtys' =>
        identmap_add_params xtys' (IdentMap.add x (BASETYPE ty) m)
   end.

Fixpoint params_to_types (xtys: list (ident * basetypename)) : list basetypename :=
   match xtys with
   | [] => []
   | (x, ty) :: more => ty :: params_to_types more
   end.

(*
 * Subtyping rules
 *)
Inductive Subtype: tyenv -> typename -> typename -> Prop :=
| MEM_subtype_len: forall G n1 n2a n2b n3,
     Numbersym_wf G n2b ->
     Typename_wf G (MEMTYPE n1 n2a n3) ->
     (* n2b < n2a -> *) (* XXX *)
     Subtype G (MEMTYPE n1 n2a n3) (MEMTYPE n1 n2b n3)
.

(*
 * Types for expressions
 * (from the "Pure Typing" judgments)
 * (and from the "Pure Pointer Typing" judgments)
 * (and from the "Pure Location Typing" judgments)
 * (and the second "Subtyping" judgment)
 *)
Inductive Exprtype: tyenv -> expr -> typename -> Prop :=
  (* "Pure Typing" *)
| TRUE_type: forall G,
     Exprtype G TRUE (BASETYPE BOOLTYPE)
| FALSE_type: forall G,
     Exprtype G FALSE (BASETYPE BOOLTYPE)
| INTCONST_type: forall G c,
     Exprtype G (INTCONST c) (BASETYPE INTTYPE)
| BITCONST_type: forall G k c,
     Exprtype G (BITCONST k c) (BASETYPE (BITTYPE (N_number k)))
| READVAR_type: forall G x ty,
     IdentMap.MapsTo x ty G ->
     Typename_wf G ty ->
     Exprtype G (READVAR x) ty
(* FAIL? *)
| CALL_type: forall G func params ret args,
     IdentMap.MapsTo func (FUNCTYPE params ret) G ->
     Exprtypes G args params ->
     Exprtype G (CALL func args) (BASETYPE ret)
(* UOP? *)
(* BOP? *)
| GETBIT_type: forall G e1 n e2,
     Exprtype G e1 (BASETYPE (BITTYPE n)) ->
     Exprtype G e2 (BASETYPE INTTYPE) ->
     Exprtype G (GETBIT e1 e2) (BASETYPE (BITTYPE (N_number 1)))
| GETBITSLICE_type: forall G e1 e2 e3 n m,
     Exprtype G e1 (BASETYPE (BITTYPE n)) ->
     Exprtype G e2 (BASETYPE INTTYPE) ->
     Exprtype G e3 (BASETYPE INTTYPE) ->
     (* XXX this is wrong: it allows checking with any m... *)
     Exprtype G (GETBIT e1 e2) (BASETYPE (BITTYPE (N_number m)))
| LET_E_type: forall G x e1 ty1 e2 ty2,
     Exprtype G e1 ty1 ->
     Exprtype (IdentMap.add x ty1 G) e2 ty2 ->
     Exprtype G (LET_E x ty1 e1 e2) ty2
| IF_E_type: forall G c t f ty,
     Exprtype G c (BASETYPE BOOLTYPE) ->
     Exprtype G t ty ->
     Exprtype G f ty ->
     Exprtype G (IF_E c t f) ty
  (* "Pure Pointer Typing" *)
| POINTER_type: forall G base offset cw len pw,
     (* XXX should pointer bases be in their own environment? *)
     Exprtype G (READVAR base) (MEMTYPE cw len pw) ->
     Exprtype G offset (BASETYPE INTTYPE) ->
     Exprtype G (POINTER base offset) (BASETYPE (BITTYPE pw))
| LABEL_type: forall G label pw,
     (* XXX should labels be in their own environment? *)
     Exprtype G (READVAR label) (BASETYPE (LABELTYPE pw)) ->
     Exprtype G (LABEL label) (BASETYPE (LABELTYPE pw))
| FETCH_type: forall G base offset cw len pw,
     Exprtype G offset (BASETYPE INTTYPE) ->
     Exprtype G (READVAR base) (MEMTYPE cw len pw) ->
     Exprtype G (FETCH (POINTER base offset)) (BASETYPE (BITTYPE cw))
| ISPTR_type: forall G e1 k,
     Exprtype G e1 (BASETYPE (BITTYPE k)) ->
     Exprtype G (ISPTR e1) (BASETYPE BOOLTYPE)
(* BASE? OFFSET? *)
  (* "Pure Location Typing" *)
| READREG_type: forall G e1 k,
     Exprtype G e1 (BASETYPE (REGTYPE k)) ->
     Exprtype G (READREG e1) (BASETYPE (BITTYPE k))
| SET_type: forall G elements k,
     (forall e1, ExprsIn e1 elements -> Exprtype G e1 (BASETYPE (REGTYPE k))) ->
     Exprtype G (SET elements) (REGSETTYPE k)
| LENGTH_type: forall G e1 k,
     Exprtype G e1 (REGSETTYPE k) ->
     Exprtype G (LENGTH e1) (BASETYPE INTTYPE)
| IN_type: forall G x e1 k,
     Exprtype G e1 (REGSETTYPE k) ->
     IdentMap.MapsTo x (BASETYPE (REGTYPE k)) G ->
     Exprtype G (IN x e1) (BASETYPE BOOLTYPE)
  (* SUBSET? *)
  (* UNION? INTERSECT? *)
| EXPR_SUBTYPE: forall G e1 ty1 ty2,
     Typename_wf G ty2 ->
     Subtype G ty1 ty2 ->
     Exprtype G e1 ty1 ->
     Exprtype G e1 ty2
with
Exprtypes: tyenv -> exprs -> list basetypename -> Prop :=
| Exprtypes_nil: forall G,
     Exprtypes G EXPRNIL []
| Exprtypes_cons: forall G e1 ty1 es tys,
     Exprtype G e1 (BASETYPE ty1) ->
     Exprtypes G es tys ->
     Exprtypes G (EXPRCONS e1 es) (ty1 :: tys)
.

(*
 * Typing for statements
 * (not in the TR currently)
 *
 * Statements don't produce types but they do have type correctness criteria.
 *)
Inductive Stmttyped: tyenv -> stmt -> Prop :=
| SEQ_typed: forall G s1 s2,
     Stmttyped G s1 ->
     Stmttyped G s2 ->
     Stmttyped G (SEQ s1 s2)
| LET_S_typed: forall G x ty e1 s2,
     Exprtype G e1 ty ->
     Stmttyped (IdentMap.add x ty G) s2 ->
     Stmttyped G (LET_S x ty e1 s2)
| FOR_typed: forall G x upperbound s1,
     Stmttyped G s1 ->
     Stmttyped G (FOR x upperbound s1)
| IF_S_typed: forall G c t f,
     Exprtype G c (BASETYPE BOOLTYPE) ->
     Stmttyped G t ->
     Stmttyped G f ->
     Stmttyped G (IF_S c t f)
| WRITEREG_typed: forall G e1 e2 k,
     Exprtype G e1 (BASETYPE (REGTYPE k)) ->
     Exprtype G e2 (BASETYPE (BITTYPE k)) ->
     Stmttyped G (WRITEREG e1 e2)
| STORE_typed: forall G base offset cw len pw e2,
     Exprtype G (READVAR base) (MEMTYPE cw len pw) ->
     Exprtype G offset (BASETYPE INTTYPE) ->
     Exprtype G e2 (BASETYPE (BITTYPE cw)) ->
     Stmttyped G (STORE (POINTER base offset) e2)
| ASSERT_typed: forall G e1,
     Exprtype G e1 (BASETYPE BOOLTYPE) ->
     Stmttyped G (ASSERT e1)
| SKIP_typed: forall G,
     Stmttyped G SKIP
| HALT_typed: forall G,
     Stmttyped G HALT
.

(*
 * Typing for decls
 * (from the "Program Typing" judgments)
 *
 * This takes two tyenvs: the first is the input, the second is the output.
 *)
Inductive Decltyped: tyenv -> decl -> tyenv -> Prop :=
  (* TYPEDECL? *)
| LET_D_typed: forall G x ty e1,
     Exprtype G e1 (BASETYPE ty) ->
     Decltyped G (LET_D x ty e1) (IdentMap.add x (BASETYPE ty) G)
  (* LETTEXT? *)
| DEF_typed: forall G x params ret e1,
     Params_wf G params ->
     Exprtype (identmap_add_params params G) e1 (BASETYPE ret) ->
     Decltyped G (DEF x params ret e1) (IdentMap.add x (FUNCTYPE (params_to_types params) ret) G)
| REGDECL_typed: forall G x n,
     Typename_wf G (BASETYPE (REGTYPE n)) ->
     Decltyped G (REGDECL x n) (IdentMap.add x (BASETYPE (REGTYPE n)) G)
| MEMDECL_typed: forall G x cw len pw,
     Typename_wf G (MEMTYPE cw len pw) ->
     Decltyped G (MEMDECL x cw len pw) (IdentMap.add x (MEMTYPE cw len pw) G)
| LABELDECL_typed: forall G x cw len pw label,
     Typename_wf G (MEMTYPE cw len pw) ->
     Typename_wf G (BASETYPE (LABELTYPE pw)) ->
     Decltyped G (LABELDECL x cw len pw label)
        (IdentMap.add x (MEMTYPE cw len pw)
            (IdentMap.add label (BASETYPE (LABELTYPE pw)) G))
.

(*
 * Typing for lists of decls
 *)
Inductive Declstyped: tyenv -> list decl -> tyenv -> Prop :=
| Declstyped_nil: forall G,
     Declstyped G [] G
| Declstyped_cons: forall G G' G'' d ds,
     Decltyped G d G' ->
     Declstyped G' ds G'' ->
     Declstyped G (d :: ds) G''
.

(*
 * Typing for the high-level constructs
 *)
Inductive Insntyped: tyenv -> insn -> tyenv -> Prop :=
| DEFINSN_typed: forall G x params text s1,
     Params_wf G params ->
     (* Stringexpr_typed G text -> *) (* XXX *)
     Stmttyped (identmap_add_params params G) s1 ->
     (* XXX is FUNCTYPE returning UNITTYPE what we want here? *)
     Insntyped G (DEFINSN x params text s1)
         (IdentMap.add x (FUNCTYPE (params_to_types params) UNITTYPE) G)
.

Inductive Insnstyped: tyenv -> list insn -> tyenv -> Prop :=
| Insnstyped_nil: forall G,
     Insnstyped G [] G
| Insnstyepd_cons: forall G G' G'' insn insns,
     Insntyped G insn G' ->
     Insnstyped G' insns G'' ->
     Insnstyped G (insn :: insns) G''
.

Inductive Machinetyped: tyenv -> machine -> tyenv -> Prop :=
| Machinetyped_really: forall G G' G'' decls insns,
     Declstyped G decls G' ->
     Insnstyped G' insns G'' ->
     Machinetyped G (decls, insns) G''
.

Inductive Existstyped: tyenv -> exists_expr -> Prop :=
| EXISTS_typed: forall G names e1,
     Params_wf G names ->
     Exprtype (identmap_add_params names G) e1 (BASETYPE BOOLTYPE) ->
     Existstyped G (EXISTS names e1)
.

Inductive Foralltyped: tyenv -> forall_expr -> Prop :=
| FORALL_typed: forall G names e1,
     Params_wf G names ->
     Existstyped (identmap_add_params names G) e1 ->
     Foralltyped G (FORALL names e1)
.

(* ugh *)
Inductive Frametyped: tyenv -> frame -> Prop :=
| Frametyped_really: forall G readset writeset,
     (forall x, In x readset -> exists k, IdentMap.MapsTo x (BASETYPE (REGTYPE k)) G) ->
     (forall x, In x writeset -> exists k, IdentMap.MapsTo x (BASETYPE (REGTYPE k)) G) ->
     Frametyped G (readset, writeset)
.

Inductive Spectyped: tyenv -> spec -> tyenv -> Prop :=
| SPEC_typed: forall G G' decls frame pre post,
     Declstyped G decls G' ->
     Frametyped G' frame ->
     Foralltyped G' pre ->
     Foralltyped G' post ->
     Spectyped G (SPEC decls frame pre post) G'
.

Inductive Invocationtyped: tyenv -> invocation -> Prop :=
| INVOCATION_typed: forall G opcode operands params,
     IdentMap.MapsTo opcode (FUNCTYPE params UNITTYPE) G ->
     Exprtypes G operands params ->
     Invocationtyped G (INVOCATION opcode operands)
.

Inductive Programtyped: tyenv -> program -> Prop :=
| Nil_typed: forall G,
     Programtyped G []
| Cons_typed: forall G inv invs,
     Invocationtyped G inv ->
     Programtyped G invs ->
     Programtyped G (inv :: invs)
.

(* validity: only well-formed types may appear in a typing environment *)
Definition Valid_tyenv (G: tyenv) :=
   forall x ty, IdentMap.MapsTo x ty G -> Typename_wf G ty.

(*
 * Proofs about valid type environments.
 *)

Lemma tyenv_empty_valid: Valid_tyenv tyenv_empty.
Proof.
   unfold Valid_tyenv.
   intros.
   rewrite IdentMapFacts.empty_mapsto_iff in H.
   contradiction.
Qed.

Lemma tyenv_add_valid:
   forall x ty G,
   Valid_tyenv G -> Typename_wf G ty -> Valid_tyenv (IdentMap.add x ty G).
Proof.
   unfold Valid_tyenv.
   intros.
   rewrite IdentMapFacts.add_mapsto_iff in H1.
   destruct H1.
   - destruct H1. subst.
     (* this should probably be a separate lemma *)
     clear H.
     (*
      * Actually...
          * This doesn't work because you can have x = x0.
          * Which is a problem partly because the type rules try to use
          * the same environment to hold type alias names and variable types.
          * There's no point trying to make this case go until that's sorted.
          * Furthermore, even then we can rebind type alias names and doing
          * so potentially invalidates the types of previously bound variables,
          * because those types might refer to the type alias name we change.
          * That needs to be sorted out as well.
          * And finally there's no point spending significant effort on this
          * until we set up the infrastructure to carry constants around for
          * binding bit widths.
          *)
         admit.
   - destruct H1.
     assert (Typename_wf G ty0) by (apply (H x0); auto).
     destruct ty0.
     * destruct ty0; try (constructor; fail).
       + inversion H3; subst. apply NAMED_wf with (ty := ty0). admit. admit.
       + admit.
       + admit.
       + admit.
     * admit.
     * admit.
     * inversion H3; subst. admit.
Admitted.

(* Exprtyped only assigns well-formed types *)
Lemma Exprtype_valid:
   forall G e ty,
   Valid_tyenv G ->
   Exprtype G e ty -> Typename_wf G ty.
Proof.
   intros.
   induction H0; auto; try (constructor; fail).
   - constructor. constructor. admit. (* XXX: can't show k > 0 *)
   - assert (Typename_wf G (FUNCTYPE params ret)) as H2 by (apply H in H0; auto).
     inversion H2; subst. auto.
   - constructor. constructor. omega.
   - constructor. constructor. admit. (* XXX can't show m > 0 *)
   - (* this breaks if you have type t = ...; let x: t = ...; then let t = 3 in x *)
     admit.
   - specialize (IHExprtype1 H). inversion IHExprtype1; subst.
     constructor. auto.
   - specialize (IHExprtype2 H). inversion IHExprtype2; subst.
     constructor. auto.
   - specialize (IHExprtype H). inversion IHExprtype; subst.
     constructor. auto.
   - induction elements.
     * admit. (* XXX: does not work, empty register set is polymorphic in k *)
     * specialize (H1 e1).
       assert (Typename_wf G (BASETYPE (REGTYPE k))).
       {
          apply H1; auto.
          constructor.
       }
       inversion H2; subst. constructor. auto.
Admitted.

Lemma Decltyped_valid:
   forall G d G', Valid_tyenv G -> Decltyped G d G' -> Valid_tyenv G'.
Proof.
   intros.
   induction H0.
   - apply tyenv_add_valid; auto. apply Exprtype_valid in H0; auto.
   - apply tyenv_add_valid; auto. apply Exprtype_valid in H1. admit. admit. (* XXX wrong *)
   - apply tyenv_add_valid; auto.
   - apply tyenv_add_valid; auto.
   - inversion H0; subst.
     apply tyenv_add_valid; auto.
     * apply tyenv_add_valid; auto.
     * constructor. admit. admit. admit. (* XXX *)
Admitted.

Lemma Declstyped_valid:
   forall G ds G', Valid_tyenv G -> Declstyped G ds G' -> Valid_tyenv G'.
Proof.
   intros.
   induction H0; auto.
   apply IHDeclstyped.
   apply Decltyped_valid in H0; auto.
Qed.

Lemma Insntyped_valid:
   forall G d G', Valid_tyenv G -> Insntyped G d G' -> Valid_tyenv G'.
Proof.
   intros.
   destruct H0.
   apply tyenv_add_valid; auto.
   constructor.
   - intros.
     clear H1.
     induction H0; simpl in H2; try contradiction.
     destruct H2; subst; auto.
   - constructor.
Qed.

Lemma Insnstyped_valid:
   forall G ds G', Valid_tyenv G -> Insnstyped G ds G' -> Valid_tyenv G'.
Proof.
   intros.
   induction H0; auto.
   apply IHInsnstyped.
   apply Insntyped_valid in H0; auto.
Qed.


(**************************************************************)
(**************************************************************)
(*                          SEMANTICS                         *)
(**************************************************************)
(**************************************************************)

(*
 * Because we don't distinguish values from expressions in the syntax,
 * the execution environments all hold expressions. We'll define some
 * predicates to limit what's allowed to be in them, though: the
 * variable environment can hold only primitive values, and registers
 * and memory can hold only bitvectors and pointer literals.
 *)

Definition varenv := IdentMap.t expr.
Definition regenv := IdentMap.t expr.
Definition region := BitvecMap.t expr.
Definition memenv := IdentMap.t region.

Definition varenv_empty := IdentMap.empty expr.
Definition regenv_empty := IdentMap.empty expr.
Definition memenv_empty := IdentMap.empty region.
Definition region_empty := BitvecMap.empty expr.

(*
 * Combined exec environment.
 *
 * (This is wrapped in a one-constructor inductive not for type safety
 * paranoia or because I like destructing things, but because tuples
 * larger than pairs are bad in Coq)
 *)
Inductive execenv: Type :=
| mkexecenv (L: varenv) (R: regenv) (M: memenv)
.

Definition execenv_empty :=
   mkexecenv varenv_empty regenv_empty memenv_empty.

(*
 * Primitive and machine values
 *)

Inductive Primitive: expr -> Prop :=
| TRUE_prim: Primitive TRUE
| FALSE_prim: Primitive FALSE
| INTCONST_prim: forall c, Primitive (INTCONST c)
| BITCONST_prim: forall k c, Primitive (BITCONST k c)
| POINTER_prim: forall base k c, Primitive (POINTER base (BITCONST k c))
| LABEL_prim: forall label, Primitive (LABEL label)
| SET_prim: forall elements,
     (forall e, ExprsIn e elements -> Primitive e) ->
     Primitive (SET elements)
.

Inductive Machine: expr -> Prop :=
| BITCONST_machine: forall k c, Machine (BITCONST k c)
| POINTER_machine: forall base k c, Machine (POINTER base (BITCONST k c))
.

Lemma Primitive_Machine: forall e, Machine e -> Primitive e.
Proof.
   intros.
   induction H; constructor.
Qed.

(*
 * Validity predicates
 *)

Definition Valid_varenv (L: varenv) :=
   forall x e, IdentMap.MapsTo x e L -> Primitive e.

Definition Valid_regenv (R: regenv) :=
   forall x e, IdentMap.MapsTo x e R -> Machine e.

Definition Valid_memenv (M: memenv) :=
   forall base region offset e,
      IdentMap.MapsTo base region M ->
      BitvecMap.MapsTo offset e region ->
      Machine e.

Definition Valid_execenv (S: execenv) :=
   match S with
   | mkexecenv L R M => Valid_varenv L /\ Valid_regenv R /\ Valid_memenv M
   end.

(*
 * Overall consistency and validity predicate.
 *
 * All the keys in the execution environments must exist in the typing
 * environment, and all the values in the execution environments must
 * be well typed.
 *)
Definition Consistent (G: tyenv) (S: execenv) : Prop :=
   (* validity *)
   Valid_tyenv G /\
   Valid_execenv S /\
   (* consistency *)
   match S with
   | mkexecenv L R M =>
        (forall x e,
            IdentMap.MapsTo x e L ->
            exists ty,
            IdentMap.MapsTo x ty G /\ Exprtype G e ty
        ) /\
        (forall x e,
            IdentMap.MapsTo x e R ->
            exists k,
            IdentMap.MapsTo x (BASETYPE (REGTYPE k)) G /\
            Exprtype G e (BASETYPE (BITTYPE k))
        ) /\
        (* also the type of the memory base must bound the region *)
        (forall base region,
            IdentMap.MapsTo base region M ->
            exists cw len pw,
            IdentMap.MapsTo base (MEMTYPE cw len pw) G /\
            (forall offset e,
                BitvecMap.MapsTo offset e region ->
                Exprtype G e (BASETYPE (BITTYPE cw)) /\
                (*offset < len*) (* XXX len is a numbersym *) True
            )
        )
   end.

Definition execenv_maps_var (x: ident) (e: expr) (S: execenv) :=
   match S with
   | mkexecenv L R M => IdentMap.MapsTo x e L
   end.

Definition execenv_bind_var (x: ident) (e: expr) (S: execenv) :=
   match S with
   | mkexecenv L R M => mkexecenv (IdentMap.add x e L) R M
   end.

Definition execenv_maps_register (r: ident) (e: expr) (S: execenv) :=
   match S with
   | mkexecenv L R M => IdentMap.MapsTo r e R
   end.

Definition execenv_maps_memory {k} (base: ident) (offset: bitvector k) (e: expr) (S: execenv) :=
   match S with
   | mkexecenv L R M =>
        exists region, IdentMap.MapsTo base region M /\ BitvecMap.MapsTo offset e region
   end.

Definition execenv_nonmaps_memory {k} (base: ident) (offset: bitvector k) (S: execenv) :=
   match S with
   | mkexecenv L R M =>
        ~IdentMap.In base M \/
        exists region, IdentMap.MapsTo base region M /\ ~BitvecMap.In offset region
   end.

(* XXX *)
Definition execenv_maps_func (f: ident) (params: list (ident * basetypename)) (ret: basetypename) (body: expr) (S: execenv) : Prop.
Admitted.

Definition bitvector_getbit {k: nat} (a: bitvector k) (b: integer) : bitvector 1.
Admitted.

Definition bitvector_getbits {k: nat} (a: bitvector k) (b: integer) (c: integer): bitvector 10.
Admitted.

Axiom ident_eq_dec: forall (x y: ident), {x = y} + {x <> y}.

Inductive BindParams: execenv -> list (ident * basetypename) -> exprs -> execenv -> Prop :=
| BindParams_nil: forall S,
     BindParams S [] EXPRNIL S
| BindParams_cons: forall S S' x ty xtys e es,
     Primitive e ->
     BindParams (execenv_bind_var x e S) xtys es S' ->
     BindParams S ((x, ty) :: xtys) (EXPRCONS e es) S'
.

Lemma Consistent_add:
   forall G S x e ty,
   Consistent G S ->
   Primitive e ->
   Exprtype G e ty ->
   Consistent (IdentMap.add x ty G) (execenv_bind_var x e S).
Proof.
   unfold Consistent.
   intros.
   destruct H as [HV1 [HV2 HV3]].
   destruct (execenv_bind_var x e S) eqn:Hbind. destruct S.
   destruct HV3 as [HV3 [HV4 HV5]].
   simpl in HV2. destruct HV2 as [HV2 [HV2a HV2b]].
   simpl in Hbind.
   injection Hbind; intros; subst.
   split; [ | (split; (split; [ | split])) ]; auto.
   - clear HV3 HV4 HV5. apply tyenv_add_valid; auto.
     apply Exprtype_valid in H1; auto.
   - clear HV3 HV4 HV5. unfold Valid_varenv in *. intros.
     rewrite IdentMapFacts.add_mapsto_iff in H.
     destruct H as [[H Ha] | [H Ha]].
     * subst. auto.
     * apply HV2 in Ha. auto.
   - clear HV4 HV5. intros.
     rewrite IdentMapFacts.add_mapsto_iff in H.
     destruct H as [[H Ha] | [H Ha]].
     * subst. exists ty.
       split.
       + rewrite IdentMapFacts.add_mapsto_iff. left. split; auto.
       + admit.
     * destruct (HV3 x0 e0 Ha) as [ty1 [Hm He]].
       exists ty1. split.
       + rewrite IdentMapFacts.add_neq_mapsto_iff; auto.
       + admit.
   - clear HV3 HV5. intros.
     destruct (HV4 x0 e0 H) as [k [Hm He]].
     exists k. split.
     * rewrite IdentMapFacts.add_mapsto_iff.
       destruct (ident_eq_dec x0 x).
       + subst. left. split; auto. admit. (* XXX wrong *)
       + right. split; auto.
     * admit.
   - clear HV3 HV4. intros.
     destruct (HV5 base region0 H) as [cw [len [pw [Hb Hx]]]].
     destruct (ident_eq_dec base x).
     * subst. admit.
     * exists cw, len, pw. split.
       + rewrite IdentMapFacts.add_neq_mapsto_iff; auto.
       + intros.
         destruct (Hx offset e0 H2).
         split.
         -- admit.
         -- auto. (* XXX *)
Admitted.

Lemma BindParams_consistent: forall G S params es S',
   Consistent G S ->
   BindParams S params es S' ->
   Consistent (identmap_add_params params G) S'.
Proof.
   intros.
   revert H. revert G.
   induction H0; intros.
   - simpl. auto.
   - apply IHBindParams.
     apply Consistent_add; auto.
     (* XXX: we need to know that params and es are type-consistent,
      * and there are various options for that but they all seem to suck. XXX
      *)
     admit.
Admitted.

Fixpoint exprs_num (es: exprs) : integer :=
   match es with
   | EXPRNIL => 0%Z
   | EXPRCONS _ es' => (1 + exprs_num es')%Z
   end.

(*
 * Expressions. Large-step semantics.
 *
 * Takes a type environment and an exec environment; both are invariant.
 * The output expr (the second one) is always either primitive or
 * FAIL; we'll prove that in a moment.
 *
 * These rules are from the Expression Semantics section of the TR.
 *
 * XXX: do we need a rule that says primitive values evaluate to themselves?
 *)
Inductive Evals_E: tyenv -> execenv -> expr -> expr -> Prop :=
| READVAR_eval: forall G S x e',
     execenv_maps_var x e' S ->
     Evals_E G S (READVAR x) e'
| CALL_eval: forall G S S' f params ret body args args' result,
     Evals_Es G S args args' ->
     execenv_maps_func f params ret body S ->
     (* XXX need to hide the local scope in S *)
     BindParams S params args' S' ->
     Evals_E G S' body result ->
     Evals_E G S (CALL f args) result
(* XXX
| UOP_eval
| BOP_eval
*)
| GETBIT_eval: forall G S e1 k c1 e2 c2,
     Evals_E G S e1 (BITCONST k c1) ->
     Evals_E G S e2 (INTCONST c2) ->
     (*c2 < k -> *) (* XXX wrong types *)
     Evals_E G S (GETBIT e1 e2) (BITCONST 1 (bitvector_getbit c1 c2))
| GETBITSLICE_eval: forall G S e1 k k' c1 e2 c2 e3 c3,
     Evals_E G S e1 (BITCONST k c1) ->
     Evals_E G S e2 (INTCONST c2) ->
     Evals_E G S e3 (INTCONST c3) ->
     (c2 < c3)%Z ->
     (*c3 < k -> *) (* XXX wrong types *)
     (*k' = c3 - c2 -> *) (* XXX wrong types *)
     Evals_E G S (GETBITSLICE e1 e2 e3) (BITCONST k' (bitvector_getbits c1 c2 c3))
| LET_E_eval: forall G S x ty e1 e1' e2 e2',
     Evals_E G S e1 e1' ->
     Evals_E G (execenv_bind_var x e1' S) e2 e2' ->
     Evals_E G S (LET_E x ty e1 e2) e2'
| IF_E_eval_true: forall G S c t t' f,
     Evals_E G S c TRUE ->
     Evals_E G S t t' ->
     Evals_E G S (IF_E c t f) t'
| IF_E_eval_false: forall G S c t f f',
     Evals_E G S c FALSE ->
     Evals_E G S f f' ->
     Evals_E G S (IF_E c t f) f'
| POINTER_eval: forall G S e1 e1' base,
     Evals_E G S e1 e1' ->
     Evals_E G S (POINTER base e1) (POINTER base e1')
| FETCH_eval: forall G S e1 base k offset result,
     Evals_E G S e1 (POINTER base (BITCONST k offset)) ->
     execenv_maps_memory base offset result S ->
     Evals_E G S (FETCH e1) result
| ISPTR_eval_true: forall G S e1 base e1',
     Evals_E G S e1 (POINTER base e1') ->
     Evals_E G S (ISPTR e1) TRUE
| ISPTR_eval_false: forall G S e1 k c,
     Evals_E G S e1 (BITCONST k c) ->
     Evals_E G S (ISPTR e1) FALSE
| BASE_eval: forall G S e1 base offset,
     Evals_E G S e1 (POINTER base offset) ->
     Evals_E G S (BASE e1) (READVAR base)
| OFFSET_eval: forall G S e1 base offset,
     Evals_E G S e1 (POINTER base offset) ->
     Evals_E G S (BASE e1) offset
| READREG_eval: forall G S e1 r result,
     Evals_E G S e1 (READVAR r) ->
     execenv_maps_register r result S ->
     Evals_E G S (READREG e1) result
| SET_eval: forall G S elements elements',
     Evals_Es G S elements elements' ->
     Evals_E G S (SET elements) (SET elements')
| LENGTH_eval: forall G S e1 elements,
     Evals_E G S e1 (SET elements) ->
     Evals_E G S (LENGTH e1) (INTCONST (exprs_num elements))
| IN_eval_true: forall G S x e1 elements,
     Evals_E G S e1 (SET elements) ->
     ExprsIn (READVAR x) elements ->
     Evals_E G S (IN x e1) TRUE
| IN_eval_false: forall G S x e1 elements,
     Evals_E G S e1 (SET elements) ->
     ~ ExprsIn (READVAR x) elements ->
     Evals_E G S (IN x e1) FALSE
(* XXX
| SUBSET_eval
| UNION_eval
| INTERSECT_eval
*)
  (* failures *)
| FETCH_eval_failure_notpointer: forall G S e1 c k,
     Evals_E G S e1 (BITCONST c k) ->
     Evals_E G S (FETCH e1) FAIL
| FETCH_eval_failure_badoffset: forall G S e1 base c offset,
     Evals_E G S e1 (POINTER base (BITCONST c offset)) ->
     execenv_nonmaps_memory base offset S ->
     Evals_E G S (FETCH e1) FAIL
with
Evals_Es: tyenv -> execenv -> exprs -> exprs -> Prop :=
| EXPRCONS_eval: forall G S e1 e1' es es',
     Evals_E G S e1 e1' ->
     Evals_Es G S es es' ->
     Evals_Es G S (EXPRCONS e1 es) (EXPRCONS e1' es')
.

Lemma Evals_E_primitive:
   forall G S e e',
   Consistent G S ->
   Evals_E G S e e' ->
   Primitive e' \/ e' = FAIL.
Proof.
   intros.
   induction H0; auto; try (right; auto; fail); try (left; constructor; fail).
   - unfold Consistent in H. destruct H. destruct H1.
     clear H2.
     unfold Valid_execenv in H1.
     destruct S.
     destruct H1. destruct H2.
     simpl in H0.
     unfold Valid_varenv in H1.
     left. apply (H1 x); auto.
   - (* XXX this won't work until we add to G, which... blah *) admit.
   - (* ditto *) admit.
   - (* XXX: POINTER_prim requires e1' to be explicitly a bitvector, not just Primitive,
        and we don't know that without type info *) admit.
   - unfold execenv_maps_memory in H1. destruct S.
     destruct H1 as [region [H1a H1b]].
     clear IHEvals_E. clear H0. clear e1.
     unfold Consistent in H.
     destruct H as [HV1 [HV2 HV3]].
     simpl in HV2.
     destruct HV2 as [HV2 [HV2a HV2b]].
     unfold Valid_memenv in HV2b.
     left.
     apply Primitive_Machine.
     apply (HV2b base region offset); auto.
   - (* XXX this is all wrong, shouldn't be allowed *) admit.
   - destruct (IHEvals_E H).
     * inversion H1; subst. left; constructor.
     * (* XXX missing failure propagation for this *) admit.
   - unfold execenv_maps_register in H1. destruct S.
     clear IHEvals_E. clear H0. clear e1.
     unfold Consistent in H.
     destruct H as [HV1 [HV2 HV3]].
     simpl in HV2.
     destruct HV2 as [HV2 [HV2a HV2b]].
     unfold Valid_regenv in HV2a.
     left.
     apply Primitive_Machine.
     apply (HV2a r result); auto.
   - (* XXX missing induction for elements' *) admit.
Admitted.

(*
 * Convert a for into a sequence of let-bindings of the iteration variable.
 *)
Fixpoint convert_for (x: ident) (i: integer) (n: nat) (s: stmt) : stmt :=
   match n with
   | 0 => SKIP
   | S n' =>
        let s1 := LET_S x (BASETYPE INTTYPE) (INTCONST i) s in
        let s2 := convert_for x (1 + i)%Z n' s in
        SEQ s1 s2
   end.

(* restore local variables, but retain machine state *)
Definition execenv_unscope (S S': execenv) :=
   match S, S' with
   | mkexecenv L _ _, mkexecenv _ R M => mkexecenv L R M
   end.

Definition execenv_has_register r S :=
   match S with
   | mkexecenv L R M => IdentMap.In r R
   end.

Definition execenv_setregister r e S :=
   match S with
   | mkexecenv L R M => mkexecenv L (IdentMap.add r e R) M
   end.

Definition execenv_has_memory base offset S :=
   match S with
   | mkexecenv L R M =>
        exists region,
        IdentMap.MapsTo base region M /\
        BitvecMap.In offset region
   end.

Definition execenv_setmem base offset e S :=
   match S with
   | mkexecenv L R M =>
        let region :=
           match IdentMap.find base M with
           | None => region_empty
           | Some region => region
           end
        in
        let region' := BitvecMap.add offset e region in
        mkexecenv L R (IdentMap.add base region' M)
   end.

(*
 * Statements. Large-step semantics.
 *
 * Takes a type environment and an execution environment; the execution
 * environment is updated.
 *)
Inductive Evals_S: tyenv -> execenv -> stmt -> execenv -> stmt -> Prop :=
| SEQ_evals: forall G S S' S'' s1 s2 s2',
     Evals_S G S s1  S' SKIP ->
     Evals_S G S' s2  S'' s2' ->
     Evals_S G S (SEQ s1 s2)  S'' s2'
| LET_S_evals: forall G S S' x ty e1 e1' s2 s2',
     Evals_E G S e1 e1' ->
     (* XXX if we keep G in here this needs to update G... *)
     Evals_S G (execenv_bind_var x e1' S) s2  S' s2' ->
     Evals_S G S (LET_S x ty e1 s2) (execenv_unscope S S') s2'
| FOR_evals: forall G S S' x upperbound s1 s1',
     Evals_S G S (convert_for x 1%Z (Z.to_nat upperbound) s1) S' s1' ->
     Evals_S G S (FOR x upperbound s1) S' s1'
| IF_S_evals_true: forall G S S' c t t' f,
     Evals_E G S c TRUE ->
     Evals_S G S t S' t' ->
     Evals_S G S (IF_S c t f) S' t'
| IF_S_evals_false: forall G S S' c t f f',
     Evals_E G S c FALSE ->
     Evals_S G S f S' f' ->
     Evals_S G S (IF_S c t f) S' f'
| WRITEREG_evals: forall G S e1 r e2 e2',
     Evals_E G S e1 (READVAR r) ->
     execenv_has_register r S ->
     Evals_E G S e2 e2' ->
     Evals_S G S (WRITEREG e1 e2) (execenv_setregister r e2' S) SKIP
| STORE_evals: forall G S e1 base k offset e2 e2',
     Evals_E G S e1 (POINTER base (BITCONST k offset)) ->
     execenv_has_memory base offset S ->
     Evals_E G S e2 e2' ->
     Evals_S G S (STORE e1 e2) (execenv_setmem base offset e2' S) SKIP
| ASSERT_evals_true: forall G S e1,
     Evals_E G S e1 TRUE ->
     Evals_S G S (ASSERT e1)   S SKIP
| ASSERT_evals_false: forall G S e1,
     Evals_E G S e1 FALSE ->
     Evals_S G S (ASSERT e1)   S HALT
| SKIP_evals: forall G S,
     Evals_S G S SKIP   S SKIP
.

(*
 * Evaluating statements preserves validity of the execution environment.
 *)
Lemma Evals_S_valid:
   forall G S s S' s',
   Consistent G S ->
   Valid_execenv S ->
   Evals_S G S s S' s' ->
   Valid_execenv S'.
Proof.
   intros.
   induction H1; auto.
   - apply IHEvals_S2.
     * admit. (* XXX *)
     * apply IHEvals_S1; auto.
   - (* this will be a huge pain *) admit.
   - unfold execenv_setregister.
     destruct S.
     simpl in H0.
     unfold Valid_execenv.
     destruct H0 as [H0 [H0a H0b]].
     split; auto.
     split; auto.
     unfold Valid_regenv in *.
     intros.
     rewrite IdentMapFacts.add_mapsto_iff in H4.
     destruct H4 as [[H4a H4b] | [H4a H4b]].
     * subst.
       apply Evals_E_primitive in H3; auto.
       destruct H3.
       + (* XXX wrong *) admit.
       + (* XXX don't have failure propagation for this *) admit.
     * apply H0a in H4b; auto.
   - unfold execenv_setmem.
     destruct S.
     simpl in H0.
     unfold Valid_execenv.
     destruct H0 as [H0 [H0a H0b]].
     split; auto.
     split; auto.
     unfold Valid_memenv in *.
     intros.
     rewrite IdentMapFacts.add_mapsto_iff in H4.
     destruct H4 as [[H4a H4b] | [H4a H4b]].
     * subst.
       rewrite BitvecMapFacts.add_mapsto_iff in H5.
       destruct H5 as [[H5a H5b] | [H5a H5b]].
       + subst.
         apply Evals_E_primitive in H3; auto.
         destruct H3.
         -- (* XXX wrong *) admit.
         -- (* XXX don't have failure propagation for this *) admit.
       + destruct (IdentMap.find base0 M) eqn:Hfind.
         -- apply H0b with (base := base0) in H5b; auto.
            rewrite IdentMapFacts.find_mapsto_iff; auto.
         -- rewrite BitvecMapFacts.empty_mapsto_iff in H5b. contradiction.
     * apply H0b with (base := base0) in H5; auto.
Admitted.

(*
 * Evaluating statements also preserves consistency.
 *)
Lemma Evals_S_consistent:
   forall G S s S' s',
   Consistent G S ->
   Evals_S G S s S' s' ->
   Consistent G S'.
Proof.
   intros.
   induction H0; auto.
   - admit.
   - unfold execenv_has_register in H1.
     unfold Consistent in *.
     destruct S.
     destruct H as [HC1 [HC2 [HC3 [HC4 HC5]]]].
     split; auto.
     split; [ | split]; auto; [ | split]; auto.
     * (* XXX this would duplicate previous lemma *) admit.
     * intros.
       rewrite IdentMapFacts.add_mapsto_iff in H.
       destruct H as [[Ha Hb] | [Ha Hb]].
       + subst.
         rewrite IdentMapFacts.in_find_iff in H1.
         destruct (NatMap.find x R) eqn:Hfind; try contradiction.
         rewrite <- IdentMapFacts.find_mapsto_iff in Hfind.
         destruct (HC4 x e0 Hfind) as [k [Hx1 Hx2]].
         exists k. split; auto.
         admit.
       + destruct (HC4 x e Hb) as [k [Hx1 Hx2]].
         exists k. split; auto.
   - unfold execenv_has_memory in H1.
     unfold Consistent in *.
     destruct S.
     destruct H as [HC1 [HC2 [HC3 [HC4 HC5]]]].
     split; auto.
     split; [ | split]; auto; [ | split]; auto.
     * (* XXX this would duplicate previous lemma *) admit.
     * intros.
       destruct H1 as [region [H1a H1b]].
       rewrite IdentMapFacts.add_mapsto_iff in H.
       destruct H as [[Ha Hb] | [Ha Hb]].
       + subst.
         destruct (HC5 base0 region H1a) as [cw [len [pw [Hx1 HX2]]]].
         exists cw, len, pw. split; auto.
         intros.
         apply HX2 with (offset := offset0).
         admit. (* blah *)
       + destruct (HC5 base region H1a) as [cw [len [pw [Hx1 Hx2]]]].
         exists cw, len, pw. split.
         -- admit.
         --  intros. apply Hx2 with (offset := offset0). admit. (* blah *)
Admitted.

(*
 * All statements evaluate either to SKIP or HALT.
 *)
Lemma Evals_S_terminates:
   forall G S s S' s',
   Consistent G S ->
   Evals_S G S s S' s' ->
   s' = SKIP \/ s' = HALT.
Proof.
   intros.
   induction H0; auto.
   - apply IHEvals_S2.
     apply Evals_S_consistent in H0_; auto.
   - apply IHEvals_S.
     (* XXX all wet... *)
     admit.
Admitted.

Axiom execenv_addfunc: ident -> list (ident * basetypename) -> basetypename -> expr -> execenv -> execenv.
Axiom execenv_addinsn: ident -> list (ident * basetypename) -> stmt -> execenv -> execenv.

Definition execenv_addreg (r: ident) (n: numbersym) (S: execenv) : execenv.
Admitted.

Definition execenv_addmem (base: ident) (len: numbersym) (S: execenv) : execenv.
Admitted.

Definition execenv_addlabel (base: ident) (len: numbersym) (label: ident) (S: execenv) : execenv.
Admitted.

(*
 * Declarations.
 *)
Inductive Evals_D: tyenv -> execenv -> decl -> execenv -> Prop :=
| TYPEDECL_evals: forall G S x ty,
     Evals_D G S (TYPEDECL x ty) S  (* no effect *)
| LET_D_evals: forall G S x ty e1 e1',
     Evals_E G S e1 e1' ->
     (* XXX: how do we know if it's a block-let? *)
     Evals_D G S (LET_D x ty e1) (execenv_bind_var x e1' S)
(* XXX
| LETTEXT_evals
*)
| DEF_evals: forall G S x params ret e1,
     Evals_D G S (DEF x params ret e1) (execenv_addfunc x params ret e1 S)
| DEF_regdecl: forall G S x n,
     Evals_D G S (REGDECL x n) (execenv_addreg x n S)
| DEF_memdecl: forall G S x cw len pw,
     Evals_D G S (MEMDECL x cw len pw) (execenv_addmem x len S)
| DEF_labeldecl: forall G S x cw len pw label,
     Evals_D G S (MEMDECL x cw len pw) (execenv_addlabel x len label S)
.

Inductive Evals_Ds: tyenv -> execenv -> list decl -> execenv -> Prop :=
| Evals_Ds_nil: forall G S,
     Evals_Ds G S [] S
| Evals_Ds_cons: forall G S S' S'' d ds,
     Evals_D G S d S' ->
     Evals_Ds G S' ds S'' ->
     Evals_Ds G S (d :: ds) S''
.

Inductive Evals_Insn: tyenv -> execenv -> insn -> execenv -> Prop :=
| DEFINSN_evals: forall G S x params text s1,
     Evals_Insn G S (DEFINSN x params text s1) (execenv_addinsn x params s1 S)
.

Inductive Evals_insns: tyenv -> execenv -> list insn -> execenv -> Prop :=
| Evals_insns_nil: forall G S,
     Evals_insns G S [] S
| Evals_insns_cons: forall G S S' S'' insn insns,
     Evals_Insn G S insn S' ->
     Evals_insns G S' insns S'' ->
     Evals_insns G S (insn :: insns) S''
.

Inductive Evals_Machine: tyenv -> execenv -> machine -> execenv -> Prop :=
| Machine_evals: forall G S S' S'' decls insns,
     Evals_Ds G S decls S' ->
     Evals_insns G S' insns S'' ->
     Evals_Machine G S (decls, insns) S''
.

Inductive Evals_exists: tyenv -> execenv -> exists_expr -> expr -> Prop :=
| EXISTS_evals_nil: forall G S e1 e1',
     Evals_E G S e1 e1' ->
     Evals_exists G S (EXISTS [] e1) e1'
(* XXX need the cons case *)
.

Inductive Evals_forall: tyenv -> execenv -> forall_expr -> expr -> Prop :=
| FORALL_evals_nil: forall G S e1 e1',
     Evals_exists G S e1 e1' ->
     Evals_forall G S (FORALL [] e1) e1'
(* XXX need the cons case *)
.

Axiom execenv_has_insn: ident -> list (ident * basetypename) -> stringexpr -> stmt -> Prop.

Inductive Evals_Inv: tyenv -> execenv -> invocation -> execenv -> Prop :=
| INVOCATION_evals: forall G S S' S'' opcode operands params text body,
     execenv_has_insn opcode params text body ->
     BindParams S params operands S' ->
     Evals_S G S' body S'' SKIP ->
     Evals_Inv G S (INVOCATION opcode operands) (execenv_unscope S S'')
.

Inductive Evals_Program: tyenv -> execenv -> program -> execenv -> Prop :=
| Program_evals_nil: forall G S,
     Evals_Program G S [] S
| Program_evals_cons: forall G S S' S'' inv invs,
     Evals_Inv G S inv S' ->
     Evals_Program G S' invs S'' ->
     Evals_Program G S (inv :: invs) S''
.

(* XXX this should take an input machine state and also eval pre/post and return the reuslts *)
Inductive Evals_Everything: tyenv -> machine -> spec -> program -> execenv -> Prop :=
| Everything_evals: forall G S S' S'' machine specdecls frame pre post program,
     Evals_Machine G execenv_empty machine S ->
     Evals_Ds G S specdecls S' ->
     Evals_Program G S' program S'' ->
     Evals_Everything G machine (SPEC specdecls frame pre post) program S''
.

Definition Program_Meets_Spec :=
    forall G S machine specdecls frame pre post program,
    Evals_Everything G machine (SPEC specdecls frame pre post) program S ->
    (*Evals_E G S0 pre TRUE ->*) (* XXX doesn't work, need to address initial machine state *)
    Evals_forall G S post TRUE.

(*
 * Loose end: programs are only supposed to have machine values in their operands
 *)
Definition Valid_program (p: program) :=
   forall inv, In inv p ->
      match inv with
      | INVOCATION opcode operands =>
           forall operand, ExprsIn operand operands -> Machine operand
      end.



(**************************************************************)
(**************************************************************)
(*                          SOUNDNESS                         *)
(**************************************************************)
(**************************************************************)

(*
 * preservation
 *)

Lemma preserves_expr:
   forall G S e e' ty,
   Consistent G S ->
   Exprtype G e ty ->
   Evals_E G S e e' ->
   Exprtype G e' ty.
Proof.
   intros.
   induction H0; inversion H1; subst.
   - unfold Consistent in H.
     unfold execenv_maps_var in H6.
     destruct H as [HC1 [HC2 HC3]].
     destruct S.
     destruct HC3 as [HC3 [HC4 HC5]].
     destruct (HC3 x e' H6) as [ty' [Hx Hy]].
     assert (ty' = ty) by admit.
     subst.
     auto.
   - admit.
Admitted.

Lemma progress_expr:
   forall G S e ty,
   Consistent G S ->
   Exprtype G e ty ->
   exists e',
   Evals_E G S e e'.
Proof.
Admitted.

Lemma preserves_stmt:
   forall G S S' s s',
   Consistent G S ->
   Stmttyped G s ->
   Evals_S G S s S' s' ->
   Consistent G S' /\ Stmttyped G s'.
Proof.
Admitted.

Lemma progress_stmt:
   forall G S s,
   Consistent G S ->
   Stmttyped G s ->
   exists S' s',
   Evals_S G S s S' s'.
Proof.
Admitted.

Lemma preserves_decl:
   forall G G' S S' d,
   Consistent G S ->
   Decltyped G d G' ->
   Evals_D G S d S' ->
   Consistent G' S'.
Proof.
Admitted.

Lemma progress_decl:
   forall G G' S d,
   Consistent G S ->
   Decltyped G d G' ->
   exists S',
   Evals_D G S d S'.
Proof.
Admitted.

Lemma preserves_decls:
   forall G G' S S' ds,
   Consistent G S ->
   Declstyped G ds G' ->
   Evals_Ds G S ds S' ->
   Consistent G' S'.
Proof.
Admitted.

Lemma progress_decls:
   forall G G' S ds,
   Consistent G S ->
   Declstyped G ds G'->
   exists S',
   Evals_Ds G S ds S'.
Proof.
Admitted.

Lemma preserves_insn:
   forall G G' S S' insn,
   Consistent G S ->
   Insntyped G insn G' ->  (* XXX this doesn't seem right *)
   Evals_Insn G S insn S' ->
   Consistent G' S'.
Proof.
Admitted.

Lemma progress_insn:
   forall G G' S insn,
   Consistent G S ->
   Insntyped G insn G' ->
   exists S',
   Evals_Insn G S insn S'.
Proof.
Admitted.

Lemma preserves_insns:
   forall G G' S S' insns,
   Consistent G S ->
   Insnstyped G insns G' ->
   Evals_insns G S insns S' ->
   Consistent G' S'.
Proof.
Admitted.

Lemma progress_insns:
   forall G G' S insns,
   Consistent G S ->
   Insnstyped G insns G' ->
   exists S',
   Evals_insns G S insns S'.
Proof.
Admitted.

Lemma preserves_machine:
   forall G G' S S' mach,
   Consistent G S ->
   Machinetyped G mach G' ->
   Evals_Machine G S mach S' ->
   Consistent G' S'.
Proof.
Admitted.

Lemma progress_machine:
   forall G G' S mach,
   Consistent G S ->
   Machinetyped G mach G' ->
   exists S',
   Evals_Machine G S mach S'.
Proof.
Admitted.

Lemma preserves_exists:
   forall G S e e',
   Consistent G S ->
   Existstyped G e ->
   Evals_exists G S e e' ->
   Exprtype G e' (BASETYPE BOOLTYPE).
Proof.
Admitted.

Lemma progress_exists:
   forall G S e,
   Consistent G S ->
   Existstyped G e ->
   exists e',
   Evals_exists G S e e'.
Proof.
Admitted.

Lemma preserves_forall:
   forall G S e e',
   Consistent G S ->
   Foralltyped G e ->
   Evals_forall G S e e' ->
   Exprtype G e' (BASETYPE BOOLTYPE).
Proof.
Admitted.

Lemma progress_forall:
   forall G S e,
   Consistent G S ->
   Foralltyped G e ->
   exists e',
   Evals_forall G S e e'.
Proof.
Admitted.

Lemma preserves_inv:
   forall G S S' inv,
   Consistent G S ->
   Invocationtyped G inv ->
   Evals_Inv G S inv S' ->
   Consistent G S'.
Proof.
Admitted.

Lemma progress_inv:
   forall G S inv,
   Consistent G S ->
   Invocationtyped G inv ->
   exists S',
   Evals_Inv G S inv S'.
Proof.
Admitted.

Lemma preserves_program:
   forall G S S' prog,
   Consistent G S ->
   Programtyped G prog ->
   Evals_Program G S prog S' ->
   Consistent G S'.
Proof.
Admitted.

Lemma progress_program:
   forall G S prog,
   Consistent G S ->
   Programtyped G prog ->
   exists S',
   Evals_Program G S prog S'.
Proof.
Admitted.

Lemma preserves_everything:
   forall G G' G'' S S' machine spec prog,
   Consistent G S ->
   Machinetyped G machine G' ->
   Spectyped G' spec G'' ->
   Programtyped G'' prog ->
   Evals_Everything G'' machine spec prog S' ->
   Consistent G'' S'.
Proof.
Admitted.

Lemma progress_everything:
   forall G G' G'' S machine spec prog,
   Consistent G S ->
   Machinetyped G machine G' ->
   Spectyped G' spec G'' ->
   Programtyped G'' prog ->
   exists S',
   Evals_Everything G'' machine spec prog S'.
Proof.
Admitted.

