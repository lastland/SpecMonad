(** * The triples of the monad morphisms, and how they lift

    Every morphism of [MonadMorphisms/MonadMorphisms.v] has its [triple]
    ([Triple.v]).  The triples lift with the morphisms:

      WP   the triple at a stack is the base triple, start state by start
           state ([triple_dwpSt] &c.);

      SP   the triples at the three levels are the judgement on one base
           arrow at three pairs of indices ([triple_aspPure],
           [triple_aspSt], [triple_aspStExc] &c.).  The arrow
           transformers change only the indices.

    An SP triple does not in general split start state by start state: an
    incorrectness triple at the state level asks for SOME start state per
    outcome.  The last part reads each of the twenty-four triples in terms
    of the outcomes of the program ([dwpSt_read] &c.). *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import
  Arrow OptionArrowT StateArrowT ArrowMonad ArrowMorphism RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Verification.Computation Require Import
  DivNonDetNE.
From Incorrectness.Relational Require Import
  Rel RelSPostArr.
From Incorrectness.SP Require Import
  SPostArr DSPASLPArr SPostArrEquiv.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Relational Require PredMonad RelMonads.
From Incorrectness.Verification.MonadMorphisms Require Import MonadMorphisms.
From Incorrectness.Verification.Triples Require Import Triple.

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
Theorem triple_dwpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dwpSt S) m k P Q
  <-> forall s, triple (@dwpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@dwpPure) S m k P Q). Qed.

Theorem triple_dwpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dwpStExc S) m k P Q
  <-> forall s,
        triple (@dwpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@dwpPure) S m k P Q). Qed.

Theorem triple_dwlpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dwlpSt S) m k P Q
  <-> forall s, triple (@dwlpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@dwlpPure) S m k P Q). Qed.

Theorem triple_dwlpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dwlpStExc S) m k P Q
  <-> forall s,
        triple (@dwlpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@dwlpPure) S m k P Q). Qed.

Theorem triple_awpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@awpSt S) m k P Q
  <-> forall s, triple (@awpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@awpPure) S m k P Q). Qed.

Theorem triple_awpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@awpStExc S) m k P Q
  <-> forall s,
        triple (@awpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@awpPure) S m k P Q). Qed.

Theorem triple_awlpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@awlpSt S) m k P Q
  <-> forall s, triple (@awlpPure) (runStateT m s) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpSt (@awlpPure) S m k P Q). Qed.

Theorem triple_awlpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@awlpStExc S) m k P Q
  <-> forall s,
        triple (@awlpPure) (unOptionT (runStateT m s)) k (fun _ => P s) Q.
Proof. exact (spec_holds_wpStExc (@awlpPure) S m k P Q). Qed.

(** The judgement on a base arrow, at arbitrary indices: [X] is what a
    precondition is a predicate on, [Y] what a postcondition is. *)

Definition aspHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getASPArr (@relASP X Y R))) k P Q.

Definition dslpHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getDSLPArr (@relDSLP X Y R))) k P Q.

Definition dspHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getDSP (@dspOfRelArr X Y R))) k P Q.

Definition aslpHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getASLP (@aslpOfRelArr X Y R))) k P Q.

(** Each reading of a relation, spelled out. *)
Lemma aspHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getASPArr (relASP R) P y <-> exists x, P x /\ R x y.
Proof. reflexivity. Qed.

Lemma dslpHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getDSLPArr (relDSLP R) P y <-> forall x, R x y -> P x.
Proof. reflexivity. Qed.

Lemma dspHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getDSP (dspOfRelArr R) P y
  <-> (exists x, P x /\ R x y) /\ (forall x, R x y -> P x).
Proof. reflexivity. Qed.

Lemma aslpHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getASLP (aslpOfRelArr R) P y
  <-> (exists x, P x /\ R x y) \/ (forall x, R x y -> P x).
Proof. reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_aspPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@aspPure) d k P Q
  <-> aspHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aspSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@aspSt S) m k P Q
  <-> aspHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aspStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@aspStExc S) m k P Q
  <-> aspHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_dslpPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@dslpPure) d k P Q
  <-> dslpHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dslpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dslpSt S) m k P Q
  <-> dslpHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dslpStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dslpStExc S) m k P Q
  <-> dslpHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_dspPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@dspPure) d k P Q
  <-> dspHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dspSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@dspSt S) m k P Q
  <-> dspHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_dspStExc {S A} (m : stdivexcndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : option (A * S) -> Prop) :
  triple (@dspStExc S) m k P Q
  <-> dspHolds (fun (us : unit * S) o => outStExc m (snd us) (Some o)) k
        (fun us => P (snd us)) Q.
Proof. destruct k; reflexivity. Qed.

(** One base arrow, three pairs of indices. *)
Theorem triple_aslpPure {A} (d : divndNE A) (k : approxKind)
  (P : unit -> Prop) (Q : A -> Prop) :
  triple (@aslpPure) d k P Q
  <-> aslpHolds (fun (_ : unit) a => unOptionT (getNE d) (Some a)) k P Q.
Proof. destruct k; reflexivity. Qed.

Theorem triple_aslpSt {S A} (m : stdivndNE S A) (k : approxKind)
  (P : S -> Prop) (Q : A * S -> Prop) :
  triple (@aslpSt S) m k P Q
  <-> aslpHolds (fun (us : unit * S) r => outSt m (snd us) (Some r)) k
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
