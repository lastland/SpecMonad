(** * Relation-inclusion orders on stateful DSP and ASLP specifications

    This file orders the well-formed DSP and ASLP specification
    transformers by inclusion of their extracted binary relations.

    Representation map.  A well-formed transformer [w] denotes a binary
    relation [R] between initial states and outcomes, recovered by
    probing [w]:

    - DSP probes the top precondition [fun _ => True] and the
      co-singleton [fun t => t <> s]; see [DSPMonad.dsp_recov].
    - ASLP probes the bottom [fun _ => False] and the singleton
      [fun t => t = s]; see [ASLPMonad.aslp_recov].

    The order [m <= n] holds when every outcome reachable from a state
    under [m] is also reachable under [n].  The recoveries above make
    this a property of the underlying relations alone, independent of
    any precondition.

    For each carrier ([DSPStExc], [ASLPStExc], [StDSP.DSPSt],
    [StASLP.ASLPSt]) this file proves:

    - the inclusion order is a preorder, registered as a
      [RelationClasses.PreOrder] instance;
    - mutual inclusion coincides with the existing pointwise
      equivalence [eq1], taken with the [Eq1] instances of
      [DSPMonad.v] and [ASLPMonad.v].  The inclusion and pointwise
      orders thus induce the same equivalence, but they support
      different comparisons: relation inclusion does not imply the
      corresponding pointwise order (compiled counterexamples are in
      [Tests/SPRelationOrderTests.v]);
    - the actual bind ([bindDSPStExc], [bindASLPStExc],
      [StDSP.bindDSPSt], [StASLP.bindASLPSt]) is jointly monotone under
      relation inclusion, reusing the recovery lemmas
      [rec_bindDSPProg] / [rec_bindASLPProg] that identify those binds
      with relational composition.  Under the pointwise orders the same
      monotonicity fails; see [SPBindOrderCounterexample.v].

    Caveat.  Relation inclusion does not imply preservation of DSP/ASLP
    judgments at arbitrary preconditions: the DSP shape closes the
    relation universally and the ASLP shape disjoins an existential and
    a universal clause, so two specifications whose relations are
    included can still disagree on judgments. *)

From ITree Require Import Basics.Monad.
From Coq Require Import RelationClasses.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSPMonad ASLPMonad.

(* ===================================================================== *)
(** ** Relation inclusion for [DSPStExc] (option outcomes)               *)
(* ===================================================================== *)

Section DSPStExcRelOrder.
  Variable S : Type.

  (** The binary relation recovered from [w] by the DSP probe formulas:
      outcome [r] is reachable from [s] iff [w] accepts [r] at the top
      precondition while refusing it at the co-singleton of [s]. *)
  Definition dspStExcRel {A} (w : DSPStExc S A)
    : S -> option (A * S) -> Prop :=
    fun s r => getDSPStExc w (fun _ => True) r
               /\ ~ getDSPStExc w (fun t => t <> s) r.

  (** Relation inclusion: [m <= n] iff every outcome reachable from a
      state under [m] is reachable under [n]. *)
  Definition ordDSPStExcRel {A} (m n : DSPStExc S A) : Prop :=
    forall s r, dspStExcRel m s r -> dspStExcRel n s r.

  (** Mutual inclusion. *)
  Definition eqDSPStExcRel {A} (m n : DSPStExc S A) : Prop :=
    ordDSPStExcRel m n /\ ordDSPStExcRel n m.

  (** Well-formed DSP judgments are the DSP shape of the extracted
      relation ([getProgDSP_carrier]). *)
  Lemma dspStExcRel_carrier {A} (w : DSPStExc S A)
    (pre : S -> Prop) (r : option (A * S)) :
    getDSPStExc w pre r <->
      ((exists s, pre s /\ dspStExcRel w s r) /\
       (forall s, dspStExcRel w s r -> pre s)).
  Proof. exact (getProgDSP_carrier S w pre r). Qed.

  Lemma ordDSPStExcRel_refl {A} (m : DSPStExc S A) : ordDSPStExcRel m m.
  Proof. intros s r H. exact H. Qed.

  Lemma ordDSPStExcRel_trans {A} (m n p : DSPStExc S A) :
    ordDSPStExcRel m n -> ordDSPStExcRel n p -> ordDSPStExcRel m p.
  Proof. intros Hmn Hnp s r H. exact (Hnp s r (Hmn s r H)). Qed.

  #[global] Instance PreOrder_ordDSPStExcRel {A} :
    PreOrder (@ordDSPStExcRel A).
  Proof. split.
    - exact ordDSPStExcRel_refl.
    - intros m n p Hmn Hnp. exact (ordDSPStExcRel_trans m n p Hmn Hnp).
  Qed.

  (** Mutual inclusion is exactly judgment agreement, i.e. the existing
      pointwise equivalence [eq1].  Forward: both sides are the DSP
      shape of their extracted relation ([dspStExcRel_carrier]), and
      mutual inclusion makes the two relations extensionally equal, so
      the shapes agree by congruence ([dsp_cong]).  Backward: judgment
      agreement transfers the probes directly ([dsp_rec_ext]). *)
  Lemma eqDSPStExcRel_eq1 {A} (m n : DSPStExc S A) :
    eqDSPStExcRel m n <-> @eq1 (DSPStExc S) (Eq1__DSPStExc S) A m n.
  Proof.
    split.
    - intros [Hmn Hnm] pre r.
      pose proof (dsp_cong S (dspStExcRel m) (dspStExcRel n)
                    (fun s r => conj (Hmn s r) (fun Hr => Hnm s r Hr))
                    pre r) as Hcong.
      split.
      + intro Hw.
        exact (proj2 (dspStExcRel_carrier n pre r)
                 (proj1 Hcong (proj1 (dspStExcRel_carrier m pre r) Hw))).
      + intro Hw.
        exact (proj2 (dspStExcRel_carrier m pre r)
                 (proj2 Hcong (proj1 (dspStExcRel_carrier n pre r) Hw))).
    - intros H. split.
      + intros s r Hrel.
        exact (proj1 (dsp_rec_ext S (getDSPStExc m) (getDSPStExc n) H s r) Hrel).
      + intros s r Hrel.
        exact (proj2 (dsp_rec_ext S (getDSPStExc m) (getDSPStExc n) H s r) Hrel).
  Qed.

  (** Joint bind monotonicity on the actual operation, reusing the
      recovery lemma [rec_bindDSPProg] that identifies the bind with
      composition of the extracted relations. *)
  Lemma bindDSPStExcRel_mono {A B}
    (m n : DSPStExc S A) (k l : A -> DSPStExc S B) :
    ordDSPStExcRel m n ->
    (forall a, ordDSPStExcRel (k a) (l a)) ->
    ordDSPStExcRel (bindDSPStExc m k) (bindDSPStExc n l).
  Proof.
    intros Hm Hk s r Hprobe.
    apply (proj2 (rec_bindDSPProg S n l s r)).
    destruct (proj1 (rec_bindDSPProg S m k s r) Hprobe) as [o [Hrm Hcont]].
    exists o. split.
    - exact (Hm s o Hrm).
    - destruct o as [[a smid]|].
      + exact (Hk a smid r Hcont).
      + exact Hcont.
  Qed.

End DSPStExcRelOrder.

Arguments dspStExcRel {S} {A}.
Arguments ordDSPStExcRel {S} {A}.
Arguments eqDSPStExcRel {S} {A}.

(* ===================================================================== *)
(** ** Relation inclusion for [ASLPStExc] (option outcomes)              *)
(* ===================================================================== *)

Section ASLPStExcRelOrder.
  Variable S : Type.

  (** The binary relation recovered from [w] by the ASLP probe formulas:
      outcome [r] is reachable from [s] iff [w] refuses [r] at the
      bottom precondition while accepting it at the singleton of [s]. *)
  Definition aslpStExcRel {A} (w : ASLPStExc S A)
    : S -> option (A * S) -> Prop :=
    fun s r => ~ getASLPStExc w (fun _ => False) r
               /\ getASLPStExc w (fun t => t = s) r.

  (** Relation inclusion. *)
  Definition ordASLPStExcRel {A} (m n : ASLPStExc S A) : Prop :=
    forall s r, aslpStExcRel m s r -> aslpStExcRel n s r.

  (** Mutual inclusion. *)
  Definition eqASLPStExcRel {A} (m n : ASLPStExc S A) : Prop :=
    ordASLPStExcRel m n /\ ordASLPStExcRel n m.

  (** Well-formed ASLP judgments are the ASLP shape of the extracted
      relation ([getProgASLP_carrier]). *)
  Lemma aslpStExcRel_carrier {A} (w : ASLPStExc S A)
    (pre : S -> Prop) (r : option (A * S)) :
    getASLPStExc w pre r <->
      ((exists s, pre s /\ aslpStExcRel w s r) \/
       (forall s, aslpStExcRel w s r -> pre s)).
  Proof. exact (getProgASLP_carrier S w pre r). Qed.

  Lemma ordASLPStExcRel_refl {A} (m : ASLPStExc S A) : ordASLPStExcRel m m.
  Proof. intros s r H. exact H. Qed.

  Lemma ordASLPStExcRel_trans {A} (m n p : ASLPStExc S A) :
    ordASLPStExcRel m n -> ordASLPStExcRel n p -> ordASLPStExcRel m p.
  Proof. intros Hmn Hnp s r H. exact (Hnp s r (Hmn s r H)). Qed.

  #[global] Instance PreOrder_ordASLPStExcRel {A} :
    PreOrder (@ordASLPStExcRel A).
  Proof. split.
    - exact ordASLPStExcRel_refl.
    - intros m n p Hmn Hnp. exact (ordASLPStExcRel_trans m n p Hmn Hnp).
  Qed.

  (** Mutual inclusion is exactly judgment agreement, i.e. the existing
      pointwise equivalence [eq1].  Forward: both sides are the ASLP
      shape of their extracted relation ([aslpStExcRel_carrier]), and
      mutual inclusion makes the two relations extensionally equal, so
      the shapes agree by congruence ([aslp_cong]).  Backward: judgment
      agreement transfers the probes directly ([aslp_rec_ext]). *)
  Lemma eqASLPStExcRel_eq1 {A} (m n : ASLPStExc S A) :
    eqASLPStExcRel m n <-> @eq1 (ASLPStExc S) (Eq1__ASLPStExc S) A m n.
  Proof.
    split.
    - intros [Hmn Hnm] pre r.
      pose proof (aslp_cong S (aslpStExcRel m) (aslpStExcRel n)
                    (fun s r => conj (Hmn s r) (fun Hr => Hnm s r Hr))
                    pre r) as Hcong.
      split.
      + intro Hw.
        exact (proj2 (aslpStExcRel_carrier n pre r)
                 (proj1 Hcong (proj1 (aslpStExcRel_carrier m pre r) Hw))).
      + intro Hw.
        exact (proj2 (aslpStExcRel_carrier m pre r)
                 (proj2 Hcong (proj1 (aslpStExcRel_carrier n pre r) Hw))).
    - intros H. split.
      + intros s r Hrel.
        exact (proj1 (aslp_rec_ext S (getASLPStExc m) (getASLPStExc n) H s r) Hrel).
      + intros s r Hrel.
        exact (proj2 (aslp_rec_ext S (getASLPStExc m) (getASLPStExc n) H s r) Hrel).
  Qed.

  (** Joint bind monotonicity on the actual operation, reusing
      [rec_bindASLPProg]. *)
  Lemma bindASLPStExcRel_mono {A B}
    (m n : ASLPStExc S A) (k l : A -> ASLPStExc S B) :
    ordASLPStExcRel m n ->
    (forall a, ordASLPStExcRel (k a) (l a)) ->
    ordASLPStExcRel (bindASLPStExc m k) (bindASLPStExc n l).
  Proof.
    intros Hm Hk s r Hprobe.
    apply (proj2 (rec_bindASLPProg S n l s r)).
    destruct (proj1 (rec_bindASLPProg S m k s r) Hprobe) as [o [Hrm Hcont]].
    exists o. split.
    - exact (Hm s o Hrm).
    - destruct o as [[a smid]|].
      + exact (Hk a smid r Hcont).
      + exact Hcont.
  Qed.

End ASLPStExcRelOrder.

Arguments aslpStExcRel {S} {A}.
Arguments ordASLPStExcRel {S} {A}.
Arguments eqASLPStExcRel {S} {A}.

(* ===================================================================== *)
(** ** Relation inclusion for [StDSP.DSPSt] (pair outcomes)              *)
(* ===================================================================== *)

Section DSPStRelOrder.
  Variable S : Type.

  (** The binary relation recovered from [w] by the DSP probe formulas. *)
  Definition dspStRel {A} (w : StDSP.DSPSt S A) : S -> (A * S) -> Prop :=
    fun s r => StDSP.getDSPSt w (fun _ => True) r
               /\ ~ StDSP.getDSPSt w (fun t => t <> s) r.

  (** Relation inclusion. *)
  Definition ordDSPStRel {A} (m n : StDSP.DSPSt S A) : Prop :=
    forall s r, dspStRel m s r -> dspStRel n s r.

  (** Mutual inclusion. *)
  Definition eqDSPStRel {A} (m n : StDSP.DSPSt S A) : Prop :=
    ordDSPStRel m n /\ ordDSPStRel n m.

  (** Well-formed DSP judgments are the DSP shape of the extracted
      relation ([StDSP.getProgDSP_carrier]). *)
  Lemma dspStRel_carrier {A} (w : StDSP.DSPSt S A)
    (pre : S -> Prop) (r : (A * S)) :
    StDSP.getDSPSt w pre r <->
      ((exists s, pre s /\ dspStRel w s r) /\
       (forall s, dspStRel w s r -> pre s)).
  Proof. exact (StDSP.getProgDSP_carrier S w pre r). Qed.

  Lemma ordDSPStRel_refl {A} (m : StDSP.DSPSt S A) : ordDSPStRel m m.
  Proof. intros s r H. exact H. Qed.

  Lemma ordDSPStRel_trans {A} (m n p : StDSP.DSPSt S A) :
    ordDSPStRel m n -> ordDSPStRel n p -> ordDSPStRel m p.
  Proof. intros Hmn Hnp s r H. exact (Hnp s r (Hmn s r H)). Qed.

  #[global] Instance PreOrder_ordDSPStRel {A} :
    PreOrder (@ordDSPStRel A).
  Proof. split.
    - exact ordDSPStRel_refl.
    - intros m n p Hmn Hnp. exact (ordDSPStRel_trans m n p Hmn Hnp).
  Qed.

  (** Mutual inclusion is exactly judgment agreement, i.e. the existing
      pointwise equivalence [eq1].  Forward: both sides are the DSP
      shape of their extracted relation ([dspStRel_carrier]), and
      mutual inclusion makes the two relations extensionally equal, so
      the shapes agree by congruence ([StDSP.dsp_cong]).  Backward:
      judgment agreement transfers the probes directly
      ([StDSP.dsp_rec_ext]). *)
  Lemma eqDSPStRel_eq1 {A} (m n : StDSP.DSPSt S A) :
    eqDSPStRel m n <-> @eq1 (StDSP.DSPSt S) (StDSP.Eq1__DSPSt S) A m n.
  Proof.
    split.
    - intros [Hmn Hnm] pre r.
      pose proof (StDSP.dsp_cong S (dspStRel m) (dspStRel n)
                    (fun s r => conj (Hmn s r) (fun Hr => Hnm s r Hr))
                    pre r) as Hcong.
      split.
      + intro Hw.
        exact (proj2 (dspStRel_carrier n pre r)
                 (proj1 Hcong (proj1 (dspStRel_carrier m pre r) Hw))).
      + intro Hw.
        exact (proj2 (dspStRel_carrier m pre r)
                 (proj2 Hcong (proj1 (dspStRel_carrier n pre r) Hw))).
    - intros H. split.
      + intros s r Hrel.
        exact (proj1 (StDSP.dsp_rec_ext S (StDSP.getDSPSt m)
                        (StDSP.getDSPSt n) H s r) Hrel).
      + intros s r Hrel.
        exact (proj2 (StDSP.dsp_rec_ext S (StDSP.getDSPSt m)
                        (StDSP.getDSPSt n) H s r) Hrel).
  Qed.

  (** Joint bind monotonicity on the actual operation, reusing
      [StDSP.rec_bindDSPProg]. *)
  Lemma bindDSPStRel_mono {A B}
    (m n : StDSP.DSPSt S A) (k l : A -> StDSP.DSPSt S B) :
    ordDSPStRel m n ->
    (forall a, ordDSPStRel (k a) (l a)) ->
    ordDSPStRel (StDSP.bindDSPSt m k) (StDSP.bindDSPSt n l).
  Proof.
    intros Hm Hk s r Hprobe.
    apply (proj2 (StDSP.rec_bindDSPProg S n l s r)).
    destruct (proj1 (StDSP.rec_bindDSPProg S m k s r) Hprobe)
      as [a [smid [Hrm Hrk]]].
    exists a, smid. split.
    - exact (Hm s (a, smid) Hrm).
    - exact (Hk a smid r Hrk).
  Qed.

End DSPStRelOrder.

Arguments dspStRel {S} {A}.
Arguments ordDSPStRel {S} {A}.
Arguments eqDSPStRel {S} {A}.

(* ===================================================================== *)
(** ** Relation inclusion for [StASLP.ASLPSt] (pair outcomes)            *)
(* ===================================================================== *)

Section ASLPStRelOrder.
  Variable S : Type.

  (** The binary relation recovered from [w] by the ASLP probe formulas. *)
  Definition aslpStRel {A} (w : StASLP.ASLPSt S A) : S -> (A * S) -> Prop :=
    fun s r => ~ StASLP.getASLPSt w (fun _ => False) r
               /\ StASLP.getASLPSt w (fun t => t = s) r.

  (** Relation inclusion. *)
  Definition ordASLPStRel {A} (m n : StASLP.ASLPSt S A) : Prop :=
    forall s r, aslpStRel m s r -> aslpStRel n s r.

  (** Mutual inclusion. *)
  Definition eqASLPStRel {A} (m n : StASLP.ASLPSt S A) : Prop :=
    ordASLPStRel m n /\ ordASLPStRel n m.

  (** Well-formed ASLP judgments are the ASLP shape of the extracted
      relation ([StASLP.getProgASLP_carrier]). *)
  Lemma aslpStRel_carrier {A} (w : StASLP.ASLPSt S A)
    (pre : S -> Prop) (r : (A * S)) :
    StASLP.getASLPSt w pre r <->
      ((exists s, pre s /\ aslpStRel w s r) \/
       (forall s, aslpStRel w s r -> pre s)).
  Proof. exact (StASLP.getProgASLP_carrier S w pre r). Qed.

  Lemma ordASLPStRel_refl {A} (m : StASLP.ASLPSt S A) : ordASLPStRel m m.
  Proof. intros s r H. exact H. Qed.

  Lemma ordASLPStRel_trans {A} (m n p : StASLP.ASLPSt S A) :
    ordASLPStRel m n -> ordASLPStRel n p -> ordASLPStRel m p.
  Proof. intros Hmn Hnp s r H. exact (Hnp s r (Hmn s r H)). Qed.

  #[global] Instance PreOrder_ordASLPStRel {A} :
    PreOrder (@ordASLPStRel A).
  Proof. split.
    - exact ordASLPStRel_refl.
    - intros m n p Hmn Hnp. exact (ordASLPStRel_trans m n p Hmn Hnp).
  Qed.

  (** Mutual inclusion is exactly judgment agreement, i.e. the existing
      pointwise equivalence [eq1].  Forward: both sides are the ASLP
      shape of their extracted relation ([aslpStRel_carrier]), and
      mutual inclusion makes the two relations extensionally equal, so
      the shapes agree by congruence ([StASLP.aslp_cong]).  Backward:
      judgment agreement transfers the probes directly
      ([StASLP.aslp_rec_ext]). *)
  Lemma eqASLPStRel_eq1 {A} (m n : StASLP.ASLPSt S A) :
    eqASLPStRel m n <-> @eq1 (StASLP.ASLPSt S) (StASLP.Eq1__ASLPSt S) A m n.
  Proof.
    split.
    - intros [Hmn Hnm] pre r.
      pose proof (StASLP.aslp_cong S (aslpStRel m) (aslpStRel n)
                    (fun s r => conj (Hmn s r) (fun Hr => Hnm s r Hr))
                    pre r) as Hcong.
      split.
      + intro Hw.
        exact (proj2 (aslpStRel_carrier n pre r)
                 (proj1 Hcong (proj1 (aslpStRel_carrier m pre r) Hw))).
      + intro Hw.
        exact (proj2 (aslpStRel_carrier m pre r)
                 (proj2 Hcong (proj1 (aslpStRel_carrier n pre r) Hw))).
    - intros H. split.
      + intros s r Hrel.
        exact (proj1 (StASLP.aslp_rec_ext S (StASLP.getASLPSt m)
                        (StASLP.getASLPSt n) H s r) Hrel).
      + intros s r Hrel.
        exact (proj2 (StASLP.aslp_rec_ext S (StASLP.getASLPSt m)
                        (StASLP.getASLPSt n) H s r) Hrel).
  Qed.

  (** Joint bind monotonicity on the actual operation, reusing
      [StASLP.rec_bindASLPProg]. *)
  Lemma bindASLPStRel_mono {A B}
    (m n : StASLP.ASLPSt S A) (k l : A -> StASLP.ASLPSt S B) :
    ordASLPStRel m n ->
    (forall a, ordASLPStRel (k a) (l a)) ->
    ordASLPStRel (StASLP.bindASLPSt m k) (StASLP.bindASLPSt n l).
  Proof.
    intros Hm Hk s r Hprobe.
    apply (proj2 (StASLP.rec_bindASLPProg S n l s r)).
    destruct (proj1 (StASLP.rec_bindASLPProg S m k s r) Hprobe)
      as [a [smid [Hrm Hrk]]].
    exists a, smid. split.
    - exact (Hm s (a, smid) Hrm).
    - exact (Hk a smid r Hrk).
  Qed.

End ASLPStRelOrder.

Arguments aslpStRel {S} {A}.
Arguments ordASLPStRel {S} {A}.
Arguments eqASLPStRel {S} {A}.
