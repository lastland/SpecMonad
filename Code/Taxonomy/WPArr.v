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

(** Dijkstra refinement: pointwise implication.  Reads as "the
    refined [w2] accepts at least as many [(a, Q)] pairs as [w1]". *)
Definition WPArr_le {A B} (w1 w2 : WPArr A B) : Prop :=
  forall a Q, w1 a Q -> w2 a Q.

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
