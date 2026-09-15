From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPRelationOrder SPBindOrderCounterexample.
Import SPBindOrderCounterexample.

(** * Relation inclusion does not imply the pointwise orders

    [SPRelationOrder.v] orders DSP and ASLP specifications by inclusion
    of their extracted relations, while [DSPMonad.v] and [ASLPMonad.v]
    carry the pointwise orders [StDSP.ordDSPSt] and [StASLP.ordASLPSt].
    The two lemmas below give compiled counterexamples showing that a
    one-sided relation inclusion does not transfer to the pointwise
    orders: each order compares a different aspect of the
    specifications.

    The witnesses reuse [R0], [R1], and [K] from
    [SPBindOrderCounterexample.v] over boolean state and unit results:
    [R0] reaches [(tt, false)] only from [false], [R1] reaches
    [(tt, s)] from [s], and [K] reaches [(tt, false)] from every
    state.  The connection between the packaged transformers and their
    relations is the probe recovery [StDSP.dsp_recov] /
    [StASLP.aslp_recov]. *)

Module SPRelationOrderTests.

  (** The relation recovered from [dspOf R] / [aslpOf R] is [R] itself. *)
  Lemma dspOf_rel {A} (R : bool -> A * bool -> Prop) (s : bool) (r : A * bool) :
    dspStRel (SPBindOrderCounterexample.dspOf R) s r <-> R s r.
  Proof. exact (StDSP.dsp_recov bool R s r). Qed.

  Lemma aslpOf_rel {A} (R : bool -> A * bool -> Prop) (s : bool) (r : A * bool) :
    aslpStRel (SPBindOrderCounterexample.aslpOf R) s r <-> R s r.
  Proof. exact (StASLP.aslp_recov bool R s r). Qed.

  (** [R0K] extends [R0] by the [K] outcomes, so it reaches [(tt, false)]
      from every state. *)
  Definition R0K (s : bool) (r : unit * bool) : Prop := R0 s r \/ K tt s r.

  (** [dspOf R0] is included in [dspOf R0K] under relation inclusion,
      but is not below it in the existing pointwise order: at
      precondition [fun s => s = false] and outcome [(tt, false)] the
      inclusion of relations enlarges the predecessor set, which breaks
      the universal clause of the DSP shape. *)
  Lemma dsp_rel_incl_not_pointwise :
    ordDSPStRel (SPBindOrderCounterexample.dspOf R0)
                (SPBindOrderCounterexample.dspOf R0K) /\
    ~ StDSP.ordDSPSt (SPBindOrderCounterexample.dspOf R0)
                     (SPBindOrderCounterexample.dspOf R0K).
  Proof.
    split.
    - intros s r Hrel.
      apply (proj2 (dspOf_rel R0K s r)). left.
      exact (proj1 (dspOf_rel R0 s r) Hrel).
    - intro Hle.
      assert (Hm : StDSP.getDSPSt
                     (SPBindOrderCounterexample.dspOf R0)
                     (fun s => s = false) (tt, false)).
      { split.
        - exists false. split; [ reflexivity | exact (conj eq_refl eq_refl) ].
        - intros s Hs. exact (proj1 Hs). }
      assert (Hn : ~ StDSP.getDSPSt
                     (SPBindOrderCounterexample.dspOf R0K)
                     (fun s => s = false) (tt, false)).
      { intros [_ C].
        assert (E : true = false).
        { apply (C true). right. reflexivity. }
        discriminate E. }
      exact (Hn (Hle (fun s => s = false) (tt, false) Hm)).
  Qed.

  (** [aslpOf R0] is included in [aslpOf R1] under relation inclusion,
      but is not below it in the existing pointwise order: at
      precondition [fun s => s = false] and outcome [(tt, true)] the
      vacuous universal clause of [R0] holds while [R1] reaches the
      outcome from [true], which satisfies neither ASLP clause. *)
  Lemma aslp_rel_incl_not_pointwise :
    ordASLPStRel (SPBindOrderCounterexample.aslpOf R0)
                 (SPBindOrderCounterexample.aslpOf R1) /\
    ~ StASLP.ordASLPSt (SPBindOrderCounterexample.aslpOf R0)
                       (SPBindOrderCounterexample.aslpOf R1).
  Proof.
    split.
    - intros s r Hrel.
      destruct (proj1 (aslpOf_rel R0 s r) Hrel) as [Hs Hr].
      apply (proj2 (aslpOf_rel R1 s r)). subst. reflexivity.
    - intro Hle.
      assert (Hm : StASLP.getASLPSt
                     (SPBindOrderCounterexample.aslpOf R0)
                     (fun s => s = false) (tt, true)).
      { right. intros s [Hs _]. exact Hs. }
      assert (Hn : ~ StASLP.getASLPSt
                     (SPBindOrderCounterexample.aslpOf R1)
                     (fun s => s = false) (tt, true)).
      { intros [D | C].
        - destruct D as [s [Hps Hr]]. destruct s.
          + discriminate Hps.
          + discriminate Hr.
        - assert (E : true = false) by (apply (C true); reflexivity).
          discriminate E. }
      exact (Hn (Hle (fun s => s = false) (tt, true) Hm)).
  Qed.

End SPRelationOrderTests.
