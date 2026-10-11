(** * Triples at the base setting

    How each specification monad of the base setting is read
    ([SpecReading] for [WPure], [ASP], [DSLP], [DSP], [ASLP]), and the SP
    triples of the base morphisms as one judgement on the base arrow
    ([triple_aspPure] &c.). *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Incorrectness.Lib.Arrow Require Import
  Arrow OptionArrowT StateArrowT ArrowMonad ArrowMorphism RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Relational Require Import
  Rel RelSPostArr.
From Incorrectness.SP Require Import
  SPostArr DSPASLPArr SPostArrEquiv.
From Incorrectness.Relational Require PredMonad RelMonads.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.


(** A WP element is read backward, from a postcondition to the precondition
    it needs.  Preconditions are on [unit], or on the start state;
    postconditions on the result, on result and final state, or on the
    outcome of a computation that may raise. *)

#[global] Instance SpecReading_WPure (A : Type) :
  SpecReading WPure A unit A := {|
  spec_read := fun w : WPure A => Backward (fun Q (_ : unit) => getWPure w Q)
|}.

(** One base arrow, three pairs of indices. *)
Theorem triple_aspPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@aspPure) d k P Q
  <-> aspHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_dslpPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@dslpPure) d k P Q
  <-> dslpHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_dspPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@dspPure) d k P Q
  <-> dspHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_aslpPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@aslpPure) d k P Q
  <-> aslpHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.
