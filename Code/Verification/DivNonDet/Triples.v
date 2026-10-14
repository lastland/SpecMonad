(** * Triples at the base setting

    How each specification monad of the base setting is read
    ([SpecReading] for [WPure], [ASP], [DSLP], [DSP], [ASLP]), and the SP
    triples of the base morphisms as one judgement on the base arrow
    ([triple_aspPure] &c.), and each reading in terms of the outcomes
    ([dwpPure_read] &c.). *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.WP Require Import
  WPure.

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Incorrectness.SP Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
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

(** An SP element is read forward, from a precondition to the postcondition
    it establishes.  The monads fix the input [unit], so a precondition is
    on [unit], or on the start state. *)

#[global] Instance SpecReading_ASP (A : Type) :
  SpecReading ASP A unit A := {|
  spec_read := fun w : ASP A => Forward (getASPArr w)
|}.

#[global] Instance SpecReading_DSLP (A : Type) :
  SpecReading DSLP A unit A := {|
  spec_read := fun w : DSLP A => Forward (getDSLPArr w)
|}.

#[global] Instance SpecReading_DSP (A : Type) :
  SpecReading DSP A unit A := {|
  spec_read := fun w : DSP A => Forward (getDSP w)
|}.

#[global] Instance SpecReading_ASLP (A : Type) :
  SpecReading ASLP A unit A := {|
  spec_read := fun w : ASLP A => Forward (getASLP w)
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

(* ================================================================= *)
(** * The eight readings, in terms of the outcomes                    *)
(* ================================================================= *)

(** The only start point is [tt], so an SP precondition is the
    proposition [P tt]. *)

Section Readings.
  Context {A : Type}.

  Lemma dwpPure_read (d : divndNE A) (Q : A -> Prop) :
    getWPure (dwpPure d) Q
    <-> forall o, unOptionT (getNE d) o -> match o with Some a => Q a | None => False end.
  Proof. reflexivity. Qed.

  Lemma dwlpPure_read (d : divndNE A) (Q : A -> Prop) :
    getWPure (dwlpPure d) Q
    <-> forall o, unOptionT (getNE d) o -> match o with Some a => Q a | None => True end.
  Proof. reflexivity. Qed.

  Lemma awpPure_read (d : divndNE A) (Q : A -> Prop) :
    getWPure (awpPure d) Q
    <-> exists o, unOptionT (getNE d) o /\ match o with Some a => Q a | None => False end.
  Proof. reflexivity. Qed.

  Lemma awlpPure_read (d : divndNE A) (Q : A -> Prop) :
    getWPure (awlpPure d) Q
    <-> exists o, unOptionT (getNE d) o /\ match o with Some a => Q a | None => True end.
  Proof. reflexivity. Qed.

  Lemma aspPure_read (d : divndNE A) (P : unit -> Prop) (a : A) :
    getASPArr (aspPure d) P a <-> P tt /\ unOptionT (getNE d) (Some a).
  Proof.
    split; [ intros [[] H]; exact H | intro H; exists tt; exact H ].
  Qed.

  Lemma dslpPure_read (d : divndNE A) (P : unit -> Prop) (a : A) :
    getDSLPArr (dslpPure d) P a <-> (unOptionT (getNE d) (Some a) -> P tt).
  Proof.
    split; [ intros H Ho; exact (H tt Ho) | intros H [] Ho; exact (H Ho) ].
  Qed.

  Lemma dspPure_read (d : divndNE A) (P : unit -> Prop) (a : A) :
    getDSP (dspPure d) P a
    <-> (P tt /\ unOptionT (getNE d) (Some a)) /\ (unOptionT (getNE d) (Some a) -> P tt).
  Proof.
    split.
    - intros [[[] H] H']. exact (conj H (fun Ho => H' tt Ho)).
    - intros [H H']. split; [ exists tt; exact H | intros [] Ho; exact (H' Ho) ].
  Qed.

  Lemma aslpPure_read (d : divndNE A) (P : unit -> Prop) (a : A) :
    getASLP (aslpPure d) P a
    <-> (P tt /\ unOptionT (getNE d) (Some a)) \/ (unOptionT (getNE d) (Some a) -> P tt).
  Proof.
    split.
    - intros [[[] H] | H']; [ left; exact H | right; exact (fun Ho => H' tt Ho) ].
    - intros [H | H']; [ left; exists tt; exact H | right; intros [] Ho; exact (H' Ho) ].
  Qed.
End Readings.
