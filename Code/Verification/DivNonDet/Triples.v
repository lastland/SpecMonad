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

(* ================================================================= *)
(** * Same outcomes, same triples                                     *)
(* ================================================================= *)

(** Each reading depends only on the outcomes, so two computations with
    the same outcomes satisfy the same triples ([triple_dwpPure_same]
    &c.), by [pt_holds_same]. *)

Section SameOutcomes.
  Context {A : Type} (d1 d2 : divndNE A).
  Hypothesis Hout : forall o, unOptionT (getNE d1) o <-> unOptionT (getNE d2) o.

  Lemma triple_dwpPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@dwpPure) d1 k P Q <-> triple (@dwpPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros Q' _ H;
      apply dwpPure_read;
      intros o Ho;
      exact (proj1 (dwpPure_read _ _) H o (proj2 (Hout' o) Ho)).
  Qed.

  Lemma triple_dwlpPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@dwlpPure) d1 k P Q <-> triple (@dwlpPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros Q' _ H;
      apply dwlpPure_read;
      intros o Ho;
      exact (proj1 (dwlpPure_read _ _) H o (proj2 (Hout' o) Ho)).
  Qed.

  Lemma triple_awpPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@awpPure) d1 k P Q <-> triple (@awpPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros Q' _ H;
      apply awpPure_read;
      destruct (proj1 (awpPure_read _ _) H) as [o [Ho Hq]];
      exists o;
      exact (conj (proj1 (Hout' o) Ho) Hq).
  Qed.

  Lemma triple_awlpPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@awlpPure) d1 k P Q <-> triple (@awlpPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros Q' _ H;
      apply awlpPure_read;
      destruct (proj1 (awlpPure_read _ _) H) as [o [Ho Hq]];
      exists o;
      exact (conj (proj1 (Hout' o) Ho) Hq).
  Qed.

  Lemma triple_aspPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@aspPure) d1 k P Q <-> triple (@aspPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros P' a H;
      apply aspPure_read;
      destruct (proj1 (aspPure_read _ _ _) H) as [Hp Ho];
      exact (conj Hp (proj1 (Hout' _) Ho)).
  Qed.

  Lemma triple_dslpPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@dslpPure) d1 k P Q <-> triple (@dslpPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros P' a H;
      apply dslpPure_read;
      intro Ho;
      exact (proj1 (dslpPure_read _ _ _) H (proj2 (Hout' _) Ho)).
  Qed.

  Lemma triple_dspPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@dspPure) d1 k P Q <-> triple (@dspPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros P' a H;
      apply dspPure_read;
      destruct (proj1 (dspPure_read _ _ _) H) as [[Hp Ho] Hall];
      split;
      [ exact (conj Hp (proj1 (Hout' _) Ho)) | intro Ho'; exact (Hall (proj2 (Hout' _) Ho')) ].
  Qed.

  Lemma triple_aslpPure_same (k : approxKind) (P : unit -> Prop) (Q : A -> Prop) :
    triple (@aslpPure) d1 k P Q <-> triple (@aslpPure) d2 k P Q.
  Proof.
    apply pt_holds_same; cbn;
      [ pose proof Hout as Hout' | pose proof (fun o => iff_sym (Hout o)) as Hout' ].
    all: intros P' a H;
      apply aslpPure_read;
      destruct (proj1 (aslpPure_read _ _ _) H) as [[Hp Ho] | Hall];
      [ left; exact (conj Hp (proj1 (Hout' _) Ho))
      | right; intro Ho'; exact (Hall (proj2 (Hout' _) Ho')) ].
  Qed.
End SameOutcomes.

(* ================================================================= *)
(** * The named logics                                                *)
(* ================================================================= *)

(** The [Under] triple of each reading, by the name of its logic (see
    [Generic/Triple.v]). *)
Notation TotalCorr     P m Q := (triple (@dwpPure) m Under P Q).
Notation PartCorr      P m Q := (triple (@dwlpPure) m Under P Q).
Notation LisbonLogic   P m Q := (triple (@awpPure) m Under P Q).
Notation AngPartCorr   P m Q := (triple (@awlpPure) m Under P Q).
Notation IncorrLogic   P m Q := (triple (@aspPure) m Under P Q).
Notation PartIncorr    P m Q := (triple (@dslpPure) m Under P Q).
Notation DemIncorr     P m Q := (triple (@dspPure) m Under P Q).
Notation AngPartIncorr P m Q := (triple (@aslpPure) m Under P Q).
