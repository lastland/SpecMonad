(** * The Reader-WP Kleisli arrow [WPArr A B = A -> PureWP B].

    [WPArr A B := A -> PureWP B = A -> (B -> Prop) -> Prop] is the
    Kleisli category of the [PureWP] continuation monad (defined in
    [Taxonomy/WP.v]).  Equivalently it is [readerT A PureWP B], so it
    is automatically a monad in [B] (for fixed [A]) by composition of
    [Monad_PureWP] with the reader monad transformer — we leave that
    monad instance to ExtLib's reader machinery and only develop the
    Hughes-style [Arrow] interface here.

    This file defines the type and instances ([ArrowEq], [Arrow],
    [ArrowChoice], [ArrowApply]).  All their laws are proved in
    [Taxonomy/WPArrFacts.v], where they mostly hold definitionally
    up to Coq's eta conversion. *)

From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness Require Import Taxonomy.WP Taxonomy.WPFacts.

(* ================================================================= *)
(** ** Type definition and Arrow instances                            *)
(* ================================================================= *)

Definition WPArr (A B : Type) : Type := A -> PureWP B.

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
