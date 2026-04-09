(** * The Reader-WP Kleisli arrow [WPArr A B = A -> PureWP B].

    [WPArr A B := A -> PureWP B = A -> (B -> Prop) -> Prop] is the
    Kleisli category of the [PureWP] continuation monad (defined in
    [Taxonomy/WP.v]).  Equivalently it is [readerT A PureWP B], so it
    is automatically a monad in [B] (for fixed [A]) by composition of
    [Monad_PureWP] with the reader monad transformer — we leave that
    monad instance to ExtLib's reader machinery and only develop the
    Hughes-style [Arrow] interface here.

    All [Arrow] laws hold definitionally up to Coq's eta conversion;
    the proofs are [reflexivity] modulo product destructuring. *)

From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness Require Import Taxonomy.WP Taxonomy.WPFacts.

(* ================================================================= *)
(** ** Type definition and Arrow instance                             *)
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
Instance ArrowLaws_WPArr : ArrowLaws WPArr.
Proof.
  constructor; intros.
  - (* comp_id_l *) reflexivity.
  - (* comp_id_r *) reflexivity.
  - (* comp_assoc *) reflexivity.
  - (* pure_comp *) reflexivity.
  - (* first_pure *)
    apply functional_extensionality; intros [a c].
    apply functional_extensionality; intros Q. reflexivity.
  - (* first_comp *)
    apply functional_extensionality; intros [a c].
    apply functional_extensionality; intros Q. reflexivity.
  - (* first_fst *)
    apply functional_extensionality; intros [a c].
    apply functional_extensionality; intros Q. reflexivity.
  - (* first_assoc *)
    apply functional_extensionality; intros [[a c] d].
    apply functional_extensionality; intros Q. reflexivity.
  - (* comp_proper *)
    intros f1 f2 Hf g1 g2 Hg.
    cbv [arrow_eq ArrowEq_WPArr] in *. subst. reflexivity.
  - (* first_proper *)
    intros f1 f2 Hf.
    cbv [arrow_eq ArrowEq_WPArr] in *. subst. reflexivity.
Qed.
