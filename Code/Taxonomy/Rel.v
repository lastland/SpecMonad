(** * The heterogeneous relation arrow [Rel].

    [Rel A B := A -> B -> Prop] is a relation from [A] to [B], the
    category of relations interpreted as forward predicate transformers
    (strongest-postcondition arrows).  Using relations as the base
    ensures all arrow laws are provable without requiring monotonicity
    or additivity constraints.

    This file provides the arrow-view instances ([Arrow], [ArrowChoice],
    [ArrowApply], [ArrowLoop]) and the composed arrow-view specification
    types for the three computation monads ([prog], [ndprog],
    [nditprog]):

        [progRelArr S A = stateArrT S (optionArrT Rel) unit A]
        [nditRelArr S A = stateArrT S (optionArrT (optionArrT Rel)) unit A]

    The complementary fixed-input monad view lives in
    [Taxonomy/PredMonad.v].  Laws for this file are proved in
    [Taxonomy/RelFacts.v]. *)

From Coq Require Import
  Morphisms RelationClasses.
From Incorrectness.Classes Require Import
  Arrow OptionArrowT StateArrowT.

(* ================================================================= *)
(** ** [Rel]: definition and arrow instances                          *)
(* ================================================================= *)

Definition Rel (A B : Type) : Type := A -> B -> Prop.

(** Pointwise iff is the intrinsic equivalence on relations — no
    extensionality axioms required. *)
Definition Rel_eq {A B} (f g : Rel A B) : Prop :=
  forall a b, f a b <-> g a b.

#[global]
Instance Rel_eq_Equivalence {A B} : Equivalence (@Rel_eq A B).
Proof.
  constructor.
  - intros f a b. reflexivity.
  - intros f g H a b. symmetry. apply H.
  - intros f g h H1 H2 a b. etransitivity; [apply H1 | apply H2].
Qed.

#[global]
Instance ArrowEq_Rel : ArrowEq Rel := {
  arrow_eq := @Rel_eq
}.

(** Covariant inclusion: [R1 <= R2] iff [R1 ⊆ R2]. A larger relation
    is "above" a smaller one. This pairs with the partial-correctness
    Hoare order on [PrePost] in [Taxonomy/Galois.v]. *)
Definition Rel_le {A B} (R1 R2 : Rel A B) : Prop :=
  forall a b, R1 a b -> R2 a b.

#[global]
Instance Rel_le_PreOrder {A B} : PreOrder (@Rel_le A B).
Proof.
  constructor.
  - intros R a b H. exact H.
  - intros R1 R2 R3 H12 H23 a b H. apply H23, H12, H.
Qed.

#[global]
Instance Arrow_Rel : Arrow Rel := {
  arr_pure := fun A B f a b => f a = b ;
  arr_comp := fun A B C f g a c => exists b, f a b /\ g b c ;
  arr_first := fun A B C f p q =>
    let '(a, c) := p in let '(b, c') := q in f a b /\ c = c'
}.

#[global]
Instance ArrowChoice_Rel : ArrowChoice Rel := {
  arr_left := fun A B C f x y =>
    match x, y with
    | inl a, inl b => f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end
}.

#[global]
Instance ArrowApply_Rel : ArrowApply Rel := {
  arr_app := fun A B p b =>
    let '(f, a) := p in f a b
}.

#[global]
Instance ArrowLoop_Rel : ArrowLoop Rel := {
  arr_loop := fun A B C f a b => exists c, f (a, c) (b, c)
}.

(* ================================================================= *)
(** ** [optionRelArr] alias                                           *)
(* ================================================================= *)

(** The generic [optionArrT] transformer specializes cleanly to
    [Rel].  [ArrowChoice] and [ArrowApply] instances are
    inherited from the generic [ArrowChoice_optionArrT] etc. in
    [Classes/OptionArrowT]; their laws likewise come through the
    generic [ArrowChoiceLaws_optionArrT] etc. applied to [Rel]'s own
    arrow laws. *)

Definition optionRelArr := optionArrT Rel.

(* ================================================================= *)
(** ** Arrow-view specification types                                 *)
(* ================================================================= *)

Section ArrowSpec.

  Variable S : Type.

  (** For [prog] and [ndprog]: stateful computation with possible
      failure.  Unfolds to [(unit * S) -> option (A * S) -> Prop]. *)
  Definition progRelArr (A : Type) : Type :=
    stateArrT S (optionArrT Rel) unit A.

  (** For [nditprog]: stateful computation with failure and
      divergence.  Unfolds to [(unit * S) -> option (option (A * S)) -> Prop].
      The outer [option] represents exceptions; the inner [option]
      represents divergence. *)
  Definition nditRelArr (A : Type) : Type :=
    stateArrT S (optionArrT (optionArrT Rel)) unit A.

End ArrowSpec.
