(** * Triples with state, and how they lift from the base

    WP   the triple of a lifted morphism is the base triple, start state by
         start state ([spec_holds_wpSt] for any base morphism;
         [triple_dwpSt] &c.).

    SP   the triple is the judgement on the base arrow at the indices
         [(unit * S, A * S)] ([triple_aspSt] &c.).  An SP triple does not in
         general split start state by start state: an incorrectness triple
         at the state level asks for SOME start state per outcome.

    The last part reads each triple in terms of the outcomes of the program
    ([dwpSt_read] &c.). *)

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
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.

From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.

#[global] Instance SpecReading_WSt (S A : Type) :
  SpecReading (WSt S) A S (A * S)%type := {|
  spec_read := fun w : WSt S A =>
    Backward (fun Q s => getWPure (runStateT w s) Q)
|}.

#[global] Instance SpecReading_ASPSt (S A : Type) :
  SpecReading (ASPSt S) A S (A * S)%type := {|
  spec_read := fun w : ASPSt S A => Forward (getASPSt w)
|}.

#[global] Instance SpecReading_DSLPSt (S A : Type) :
  SpecReading (DSLPSt S) A S (A * S)%type := {|
  spec_read := fun w : DSLPSt S A => Forward (getDSLPSt w)
|}.

#[global] Instance SpecReading_DSPSt (S A : Type) :
  SpecReading (DSPSt S) A S (A * S)%type := {|
  spec_read := fun w : DSPSt S A => Forward (getDSPSt w)
|}.

#[global] Instance SpecReading_ASLPSt (S A : Type) :
  SpecReading (ASLPSt S) A S (A * S)%type := {|
  spec_read := fun w : ASLPSt S A => Forward (getASLPSt w)
|}.

(** A base morphism into [WPure], under [stateT], and under [stateT] over
    [optionT]. *)
Section LiftedWP.
  Variable σ : forall A, divndNE A -> WPure A.
  Hypothesis Hσ :
    @MonadMorphism divndNE WPure Monad__divndNE Monad_WPure
      Eq1__divndNE Eq1_WPure σ.
  Variable S : Type.

  (** The triple at a stack is the base triple, start state by start state.
      At state+exceptions the base triple is at the result type
      [option (A * S)]. *)
  Lemma spec_holds_wpSt {A} (m : stdivndNE S A) (k : approxKind)
    (P : S -> Prop) (Q : A * S -> Prop) :
    spec_holds (stateT_map S σ A m : WSt S A) k P Q
    <-> forall s, spec_holds (σ _ (runStateT m s)) k (fun _ => P s) Q.
  Proof.
    exact (pt_holds_pointwise
             (fun Q' s => getWPure (σ _ (runStateT m s)) Q') k P Q).
  Qed.
End LiftedWP.
Theorem triple_dwpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dwpSt S) m k P Q
  <-> forall s, triple (@dwpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@dwpPure) S m k P Q). Qed.

Theorem triple_dwlpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dwlpSt S) m k P Q
  <-> forall s, triple (@dwlpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@dwlpPure) S m k P Q). Qed.

Theorem triple_awpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@awpSt S) m k P Q
  <-> forall s, triple (@awpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@awpPure) S m k P Q). Qed.

Theorem triple_awlpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@awlpSt S) m k P Q
  <-> forall s, triple (@awlpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@awlpPure) S m k P Q). Qed.

Theorem triple_aspSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@aspSt S) m k P Q
  <-> aspHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dslpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dslpSt S) m k P Q
  <-> dslpHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dspSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dspSt S) m k P Q
  <-> dspHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aslpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@aslpSt S) m k P Q
  <-> aslpHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(* ================================================================= *)
(** * The twenty-four readings, in terms of the outcomes              *)
(* ================================================================= *)

(** What each reading says of a precondition or a postcondition, at
    the two stacks.  The WP ones hold by computation. *)

Section Readings.
  Context {S A : Type}.

  Lemma dwpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (dwpSt m) s) Q
    <-> forall o, outSt m s o -> match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma dwlpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (dwlpSt m) s) Q
    <-> forall o, outSt m s o -> match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma awpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (awpSt m) s) Q
    <-> exists o, outSt m s o /\ match o with Some r => Q r | None => False end.
  Proof. reflexivity. Qed.

  Lemma awlpSt_read (m : stdivndNE S A) (s : S) (Q : A * S -> Prop) :
    getWPure (runStateT (awlpSt m) s) Q
    <-> exists o, outSt m s o /\ match o with Some r => Q r | None => True end.
  Proof. reflexivity. Qed.

  Lemma aspSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getASPArr (aspSt m) (fun p => P (snd p)) r
    <-> exists s, P s /\ outSt m s (Some r).
  Proof.
    split.
    - intros [[[] s] [Hp Hr]]. exists s. exact (conj Hp Hr).
    - intros [s [Hp Hr]]. exists (tt, s). exact (conj Hp Hr).
  Qed.

  Lemma dslpSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getDSLPArr (dslpSt m) (fun p => P (snd p)) r
    <-> forall s, outSt m s (Some r) -> P s.
  Proof.
    split.
    - intros H s Hr. exact (H (tt, s) Hr).
    - intros H [[] s] Hr. exact (H s Hr).
  Qed.

  Lemma dspSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getDSP (dspSt m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outSt m s (Some r))
        /\ (forall s, outSt m s (Some r) -> P s).
  Proof.
    split.
    - intros [[[[] s] [Hp Hr]] H]. split.
      + exists s. exact (conj Hp Hr).
      + intros s' Hr'. exact (H (tt, s') Hr').
    - intros [[s [Hp Hr]] H]. split.
      + exists (tt, s). exact (conj Hp Hr).
      + intros [[] s'] Hr'. exact (H s' Hr').
  Qed.

  Lemma aslpSt_read (m : stdivndNE S A) (P : S -> Prop) (r : A * S) :
    getASLP (aslpSt m) (fun p => P (snd p)) r
    <-> (exists s, P s /\ outSt m s (Some r))
        \/ (forall s, outSt m s (Some r) -> P s).
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
