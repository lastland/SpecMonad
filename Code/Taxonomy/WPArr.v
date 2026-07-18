(** * The Reader-WP Kleisli arrow [WPArr A B = A -> PureWP B].

    [WPArr A B := A -> PureWP B = A -> (B -> Prop) -> Prop] is the
    Kleisli category of the [PureWP] continuation monad (defined in
    [Taxonomy/WP.v]).  Equivalently it is [readerT A PureWP B], so it
    is automatically a monad in [B] (for fixed [A]) by composition of
    [Monad_PureWP] with the reader monad transformer — we leave that
    monad instance to ExtLib's reader machinery and only develop the
    Hughes-style [Arrow] interface here.

    This file defines the type, the Dijkstra refinement order
    [WPArr_le], and the [ArrowEq], [Arrow], [ArrowChoice],
    [ArrowApply] instances.  All their laws are proved in
    [Taxonomy/WPArrFacts.v], where they mostly hold definitionally
    up to Coq's eta conversion.

    Note: [arrow_eq] on [WPArr] is Leibniz equality.  A
    pointwise-iff equivalence is not usable here because the
    [comp_proper] arrow law would require every [WPArr] value to be
    monotone/Proper in its continuation, which is not enforced by
    the [WPArr] type. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness Require Import Taxonomy.WP Taxonomy.WPFacts.

(* ================================================================= *)
(** ** Type definition and refinement order                           *)
(* ================================================================= *)

Definition WPArr (A B : Type) : Type := A -> PureWP B.

(** DM4all refinement order (§3.1): reverse pointwise implication.
    [w1 ≤ w2] iff [w2 a Q → w1 a Q] for all [a], [Q].  A more specific
    (stronger) transformer is lower in this order. *)
Definition WPArr_le {A B} (w1 w2 : WPArr A B) : Prop :=
  forall a Q, w2 a Q -> w1 a Q.

#[global]
Instance WPArr_le_PreOrder {A B} : PreOrder (@WPArr_le A B).
Proof. constructor; cbv; auto. Qed.

#[global]
Instance ArrowEq_WPArr : ArrowEq WPArr := {
  arrow_eq := fun A B => @eq (WPArr A B)
}.

#[global]
Instance Arrow_WPArr : Arrow WPArr := {
  arr_pure := fun A B f => fun a Q => Q (f a) ;
  arr_comp := fun A B C f g => fun a Q => f a (fun b => g b Q) ;
  arr_first := fun A B C f =>
    fun p Q => let '(a, c) := p in f a (fun b => Q (b, c))
}.

#[global]
Instance ArrowChoice_WPArr : ArrowChoice WPArr := {
  arr_left := fun A B C f =>
    fun x Q =>
      match x with
      | inl a => f a (fun b => Q (inl b))
      | inr c => Q (inr c)
      end
}.

#[global]
Instance ArrowApply_WPArr : ArrowApply WPArr := {
  arr_app := fun A B =>
    fun p Q => let '(f, a) := p in f a Q
}.

(* ================================================================= *)
(** ** Well-formedness subtype and refinement orders                  *)
(* ================================================================= *)

(** [MonotoneWP] is the well-formedness subtype of [WPArr] used as the
    DM4All carrier for [W^Pure].  Monotonicity in the postcondition is
    required by the [PrePost]/WP Galois connections and for arrow/monad
    operations to preserve the carrier.

    These definitions are co-located with [WPArr] so the raw type and
    its well-formedness boundary live together; they were previously
    local to [Taxonomy/Galois.v]. *)
Definition wp_monotone {A B} (w : WPArr A B) : Prop :=
  forall a Q1 Q2, (forall b, Q1 b -> Q2 b) -> w a Q1 -> w a Q2.

Definition MonotoneWP (A B : Type) : Type :=
  { w : WPArr A B | wp_monotone w }.

(** DM4All refinement order (reverse pointwise implication):
    [w1 <= w2] iff [w2 a Q -> w1 a Q] for all [a], [Q].  A more
    specific (stronger) transformer is lower in this order. *)
Definition MonotoneWP_le {A B} (w1 w2 : MonotoneWP A B) : Prop :=
  WPArr_le (proj1_sig w1) (proj1_sig w2).

#[global]
Instance MonotoneWP_le_PreOrder {A B} : PreOrder (@MonotoneWP_le A B).
Proof.
  constructor; unfold MonotoneWP_le, WPArr_le; intros; auto.
Qed.

(** Forward pointwise implication: [w1 >= w2] iff [w1 a Q -> w2 a Q]
    for all [a], [Q].  Used by the angelic [PrePost]/WP Galois
    connections (AWP, AWLP). *)
Definition WPArr_ge {A B} (w1 w2 : WPArr A B) : Prop :=
  forall a Q, w1 a Q -> w2 a Q.

#[global]
Instance WPArr_ge_PreOrder {A B} : PreOrder (@WPArr_ge A B).
Proof. constructor; cbv; auto. Qed.

Definition MonotoneWP_ge {A B} (w1 w2 : MonotoneWP A B) : Prop :=
  WPArr_ge (proj1_sig w1) (proj1_sig w2).

#[global]
Instance MonotoneWP_ge_PreOrder {A B} : PreOrder (@MonotoneWP_ge A B).
Proof.
  constructor; unfold MonotoneWP_ge, WPArr_ge; intros; auto.
Qed.
