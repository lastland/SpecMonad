(** * Triples with state and exceptions, and how they lift from the base

    WP   the triple of a lifted morphism is the base triple, start state by
         start state, at the result type [option (A * S)]
         ([spec_holds_wpStExc]; [triple_dwpStExc] &c.).

    SP   the triple is the judgement on the base arrow at the indices
         [(unit * S, option (A * S))] ([triple_aspStExc] &c.).

    The last part reads each triple in terms of the outcomes of the program
    ([dwpStExc_read] &c.). *)

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
From Incorrectness.Verification.DivNonDet Require Import Triples.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.


#[global] Instance SpecReading_WStExc (S A : Type) :
  SpecReading (WStExc S) A S (option (A * S)) := {|
  spec_read := fun w : WStExc S A =>
    Backward (fun Q s => getWPure (unOptionT (runStateT w s)) Q)
|}.

#[global] Instance SpecReading_ASPStExc (S A : Type) :
  SpecReading (ASPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : ASPStExc S A => Forward (getASPStExc w)
|}.

#[global] Instance SpecReading_DSLPStExc (S A : Type) :
  SpecReading (DSLPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : DSLPStExc S A => Forward (getDSLPStExc w)
|}.

#[global] Instance SpecReading_DSPStExc (S A : Type) :
  SpecReading (DSPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : DSPStExc S A => Forward (getDSPStExc w)
|}.

#[global] Instance SpecReading_ASLPStExc (S A : Type) :
  SpecReading (ASLPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : ASLPStExc S A => Forward (getASLPStExc w)
|}.

(** A base morphism into [WPure], under [stateT], and under [stateT] over
    [optionT]. *)
Section LiftedWP.
  Variable σ : forall A, divndNE A -> WPure A.
  Hypothesis Hσ :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure σ.
  Variable S : Type.

  Lemma spec_holds_wpStExc {A} (m : stdivexcndNE S A) (k : approxKind)
    (P : S -> Prop) (Q : option (A * S) -> Prop) :
    spec_holds (stateT_map S (optionT_map σ) A m : WStExc S A) k P Q
    <-> forall s,
          spec_holds (σ _ (unOptionT (runStateT m s))) k (fun _ => P s) Q.
  Proof.
    exact (pt_holds_pointwise
             (fun Q' s => getWPure (σ _ (unOptionT (runStateT m s))) Q') k P Q).
  Qed.
End LiftedWP.

Theorem triple_dwpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dwpStExc S) m k P Q
  <-> forall s,
        triple (@dwpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@dwpPure) S m k P Q). Qed.

Theorem triple_dwlpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dwlpStExc S) m k P Q
  <-> forall s,
        triple (@dwlpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@dwlpPure) S m k P Q). Qed.

Theorem triple_awpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@awpStExc S) m k P Q
  <-> forall s,
        triple (@awpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@awpPure) S m k P Q). Qed.

Theorem triple_awlpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@awlpStExc S) m k P Q
  <-> forall s,
        triple (@awlpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@awlpPure) S m k P Q). Qed.

Theorem triple_aspStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@aspStExc S) m k P Q
  <-> aspHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dslpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dslpStExc S) m k P Q
  <-> dslpHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dspStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dspStExc S) m k P Q
  <-> dspHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aslpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@aslpStExc S) m k P Q
  <-> aslpHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(* ================================================================= *)
(** * The twenty-four readings, in terms of the outcomes              *)
(* ================================================================= *)

(** What each reading says of a precondition or a postcondition, at
    the two stacks.  The WP ones hold by computation. *)

Section Readings.
  Context {S A : Type}.

  Lemma dwpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (dwpStExc m) s)) Q
    <-> forall o, outStExc m s o -> match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma dwlpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (dwlpStExc m) s)) Q
    <-> forall o, outStExc m s o -> match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma awpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (awpStExc m) s)) Q
    <-> exists o, outStExc m s o /\ match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma awlpStExc_read (m : stdivexcndNE S A) (s : S) (Q : option (A * S) -> Prop) :
    getWPure (unOptionT (runStateT (awlpStExc m) s)) Q
    <-> exists o, outStExc m s o /\ match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma aspStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getASPArr (aspStExc m) (fun p => P (snd p)) r
    <-> exists s, P s /\ outStExc m s (Some r).
  Proof.
    split.
    - intros [[[] s] [Hp Hr]]. exists s. exact (conj Hp Hr).
    - intros [s [Hp Hr]]. exists (tt, s). exact (conj Hp Hr).
  Qed.

  Lemma dslpStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getDSLPArr (dslpStExc m) (fun p => P (snd p)) r
    <-> forall s, outStExc m s (Some r) -> P s.
  Proof.
    split.
    - intros H s Hr. exact (H (tt, s) Hr).
    - intros H [[] s] Hr. exact (H s Hr).
  Qed.

  Lemma dspStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getDSP (dspStExc m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outStExc m s (Some r))
        /\ (forall s, outStExc m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] H]. split.
      + exists s. exact (conj Hp Hr).
      + intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] H]. split.
      + exists (tt, s). exact (conj Hp Hr).
      + intros [[] s'] Hr'. exact (H s' Hr').
  Qed.

  Lemma aslpStExc_read (m : stdivexcndNE S A) (P : S -> Prop) (r : option (A * S)) :
    getASLP (aslpStExc m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outStExc m s (Some r))
        \/ (forall s, outStExc m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] | H].
      + left. exists s. exact (conj Hp Hr).
      + right. intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] | H].
      + left. exists (tt, s). exact (conj Hp Hr).
      + right. intros [[] s'] Hr'. exact (H s' Hr').
  Qed.
End Readings.
