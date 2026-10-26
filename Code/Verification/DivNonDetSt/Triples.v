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

  (** *** Sequencing

      The morphism law at [bind], read at a start state: the specification
      of [bind m f] is that of [m] against the postcondition that the
      continuation's specification establishes.  This is the [Hbind]
      premise of [pt_holds_backward_seq]; the [Hmono] premise is free,
      since monotonicity is [WPure]'s carrier condition. *)
  Lemma wpSt_bind_read {A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
    (Q : B * S -> Prop) (s : S) :
    getWPure (σ _ (runStateT (bind m f) s)) Q
    <-> getWPure (σ _ (runStateT m s))
          (fun y => getWPure (σ _ (runStateT (f (fst y)) (snd y))) Q).
  Proof.
    etransitivity;
      [ exact (mm_bind Hσ (runStateT m s)
                 (fun vs => let (v, s') := vs in runStateT (f v) s') Q) |].
    cbn. split; apply getWPure_mono; intros [v s'] H; exact H.
  Qed.

  (** The composition rule, at both kinds: [Over] flips the three
      orderings and the side condition together. *)
  Lemma spec_holds_wpSt_seq {A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
    (k : approxKind) (p : S -> Prop) (q0 : A * S -> Prop)
    (pa : A -> S -> Prop) (q : B * S -> Prop) :
    spec_holds (stateT_map S σ A m : WSt S A) k p q0 ->
    (forall a, spec_holds (stateT_map S σ B (f a) : WSt S B) k (pa a) q) ->
    seq_side k q0 (fun y => pa (fst y) (snd y)) ->
    spec_holds (stateT_map S σ B (bind m f) : WSt S B) k p q.
  Proof.
    intros H1 H2 Hs.
    refine (pt_holds_backward_seq
              (fun Q s' => getWPure (σ _ (runStateT m s')) Q)
              (fun (y : A * S) Q => getWPure (σ _ (runStateT (f (fst y)) (snd y))) Q)
              (fun Q s' => getWPure (σ _ (runStateT (bind m f) s')) Q)
              (fun Q1 Q2 s' HQ => getWPure_mono _ Q1 Q2 HQ)
              (fun Q s' => wpSt_bind_read m f Q s')
              k p q0 (fun y => pa (fst y) (snd y)) q H1 _ Hs).
    intros [a s'].
    exact (proj1 (spec_holds_wpSt (f a) k (pa a) q) (H2 a) s').
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

(** *** Composition of wp triples

    [spec_holds_wpSt_seq] at each of the four wp morphisms.  Each is stated
    at the kind [k] it quantifies, so the four cover all eight wp
    triples. *)

Theorem triple_dwpSt_seq {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (k : approxKind) (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@dwpSt S) m k P Q0 ->
  (forall a, triple (@dwpSt S) (f a) k (Pa a) Q) ->
  seq_side k Q0 (fun y => Pa (fst y) (snd y)) ->
  triple (@dwpSt S) (bind m f) k P Q.
Proof. exact (spec_holds_wpSt_seq (@dwpPure) dwpPure_morphism S m f k P Q0 Pa Q). Qed.

Theorem triple_dwlpSt_seq {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (k : approxKind) (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@dwlpSt S) m k P Q0 ->
  (forall a, triple (@dwlpSt S) (f a) k (Pa a) Q) ->
  seq_side k Q0 (fun y => Pa (fst y) (snd y)) ->
  triple (@dwlpSt S) (bind m f) k P Q.
Proof. exact (spec_holds_wpSt_seq (@dwlpPure) dwlpPure_morphism S m f k P Q0 Pa Q). Qed.

Theorem triple_awpSt_seq {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (k : approxKind) (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@awpSt S) m k P Q0 ->
  (forall a, triple (@awpSt S) (f a) k (Pa a) Q) ->
  seq_side k Q0 (fun y => Pa (fst y) (snd y)) ->
  triple (@awpSt S) (bind m f) k P Q.
Proof. exact (spec_holds_wpSt_seq (@awpPure) awpPure_morphism S m f k P Q0 Pa Q). Qed.

Theorem triple_awlpSt_seq {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (k : approxKind) (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@awlpSt S) m k P Q0 ->
  (forall a, triple (@awlpSt S) (f a) k (Pa a) Q) ->
  seq_side k Q0 (fun y => Pa (fst y) (snd y)) ->
  triple (@awlpSt S) (bind m f) k P Q.
Proof. exact (spec_holds_wpSt_seq (@awlpPure) awlpPure_morphism S m f k P Q0 Pa Q). Qed.

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

(** *** Composition of ASP and DSLP triples

    The two sp monads whose [bind] is monotone also have a composition
    rule, in both directions.  Unlike the wp rules, the two kinds do not
    share a statement: the intermediate point carries a returned value that
    the continuation sees apart from the state, so [bind] must aggregate
    over the returned values -- by join for [ASPSt], by meet for [DSLPSt]
    -- and the kind that has to produce a returned value out of the
    premises needs the result type inhabited.  That is [Under] for [ASPSt]
    and [Over] for [DSLPSt]; Hoare logic (ASP [Over]) and partial
    incorrectness (DSLP [Under]) are free of it.

    The morphism law at [bind], read through the displayed formulas of
    Section 3.3. *)

Lemma aspSt_bind_read {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (r : B * S) :
  getASPSt (aspSt (bind m f)) P r
  <-> exists a, getASPSt (aspSt (f a)) (fun s' => getASPSt (aspSt m) P (a, s')) r.
Proof.
  etransitivity;
    [ exact (proj1 (eq1_ASPSt_get S _ _) (mm_bind (aspSt_morphism_rel S) m f) P r) |].
  exact (getASPSt_bind_formula S (aspSt m) (fun a => aspSt (f a)) P r).
Qed.

Lemma dslpSt_bind_read {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (r : B * S) :
  getDSLPSt (dslpSt (bind m f)) P r
  <-> forall a, getDSLPSt (dslpSt (f a)) (fun s' => getDSLPSt (dslpSt m) P (a, s')) r.
Proof.
  etransitivity;
    [ exact (proj1 (eq1_DSLPSt_get S _ _) (mm_bind (dslpSt_morphism_rel S) m f) P r) |].
  exact (getDSLPSt_bind_formula S (dslpSt m) (fun a => dslpSt (f a)) P r).
Qed.

Theorem triple_aspSt_seq_under {S A B} (Hinh : inhabited A)
  (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@aspSt S) m Under P Q0 ->
  (forall a, triple (@aspSt S) (f a) Under (Pa a) Q) ->
  seq_side_fwd (fun a s => (a, s)) Under Q0 Pa ->
  triple (@aspSt S) (bind m f) Under P Q.
Proof.
  exact (pt_holds_forward_join_under_seq
           (getASPSt (aspSt m)) (fun a s => (a, s))
           (fun a => getASPSt (aspSt (f a))) (getASPSt (aspSt (bind m f)))
           (fun a P1 P2 z HP => getASPSt_mono S _ P1 P2 z HP)
           (aspSt_bind_read m f) Hinh P Q0 Pa Q).
Qed.

Theorem triple_aspSt_seq_over {S A B}
  (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@aspSt S) m Over P Q0 ->
  (forall a, triple (@aspSt S) (f a) Over (Pa a) Q) ->
  seq_side_fwd (fun a s => (a, s)) Over Q0 Pa ->
  triple (@aspSt S) (bind m f) Over P Q.
Proof.
  exact (pt_holds_forward_join_over_seq
           (getASPSt (aspSt m)) (fun a s => (a, s))
           (fun a => getASPSt (aspSt (f a))) (getASPSt (aspSt (bind m f)))
           (fun a P1 P2 z HP => getASPSt_mono S _ P1 P2 z HP)
           (aspSt_bind_read m f) P Q0 Pa Q).
Qed.

Theorem triple_dslpSt_seq_under {S A B}
  (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@dslpSt S) m Under P Q0 ->
  (forall a, triple (@dslpSt S) (f a) Under (Pa a) Q) ->
  seq_side_fwd (fun a s => (a, s)) Under Q0 Pa ->
  triple (@dslpSt S) (bind m f) Under P Q.
Proof.
  exact (pt_holds_forward_meet_under_seq
           (getDSLPSt (dslpSt m)) (fun a s => (a, s))
           (fun a => getDSLPSt (dslpSt (f a))) (getDSLPSt (dslpSt (bind m f)))
           (fun a P1 P2 z HP => getDSLPSt_mono S _ P1 P2 z HP)
           (dslpSt_bind_read m f) P Q0 Pa Q).
Qed.

Theorem triple_dslpSt_seq_over {S A B} (Hinh : inhabited A)
  (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (Q0 : A * S -> Prop)
  (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  triple (@dslpSt S) m Over P Q0 ->
  (forall a, triple (@dslpSt S) (f a) Over (Pa a) Q) ->
  seq_side_fwd (fun a s => (a, s)) Over Q0 Pa ->
  triple (@dslpSt S) (bind m f) Over P Q.
Proof.
  exact (pt_holds_forward_meet_over_seq
           (getDSLPSt (dslpSt m)) (fun a s => (a, s))
           (fun a => getDSLPSt (dslpSt (f a))) (getDSLPSt (dslpSt (bind m f)))
           (fun a P1 P2 z HP => getDSLPSt_mono S _ P1 P2 z HP)
           (dslpSt_bind_read m f) Hinh P Q0 Pa Q).
Qed.

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

(* ================================================================= *)
(** * The named logics                                                *)
(* ================================================================= *)

(** The [Under] triple of each reading, by the name of its logic (see
    [Generic/Triple.v]). *)
Notation TotalCorr     P m Q := (triple (@dwpSt _) m Under P Q).
Notation PartCorr      P m Q := (triple (@dwlpSt _) m Under P Q).
Notation LisbonLogic   P m Q := (triple (@awpSt _) m Under P Q).
Notation AngPartCorr   P m Q := (triple (@awlpSt _) m Under P Q).
Notation IncorrLogic   P m Q := (triple (@aspSt _) m Under P Q).
Notation PartIncorr    P m Q := (triple (@dslpSt _) m Under P Q).
Notation DemIncorr     P m Q := (triple (@dspSt _) m Under P Q).
Notation AngPartIncorr P m Q := (triple (@aslpSt _) m Under P Q).
