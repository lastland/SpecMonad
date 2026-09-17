From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSPMonad ASLPMonad.

(** * Ordered-bind counterexamples for stateful DSP and ASLP

    Three properties of these specification monads are distinct:

    - Monad laws state the unit and associativity equations up to extensional
      equivalence.
    - Precondition monotonicity fixes a well-formed transformer [w]: if
      [forall s, P s -> Q s], then [w P r -> w Q r].
    - Ordered bind must preserve the order between computations.  In
      particular, for a fixed continuation [k], [m0 <= m1] must imply
      [bind m0 k <= bind m1 k], where the order is pointwise implication
      over preconditions and outcomes.

    The existing monad laws and precondition-monotonicity results for
    [StDSP.DSPSt] and [StASLP.ASLPSt] coexist with the failures of ordered
    bind proved here.  Each counterexample varies only the first argument
    of bind and uses the same continuation on both sides.

    The witnesses use boolean state and unit return values.  Relations
    describe terminating outcomes [(tt, s)] of type [unit * bool]:

    - [R0] models [if state then diverge else skip].  It has no terminating
      outcome from [true], and from [false] it returns [tt] in state [false].
    - [R1] models [skip], returning [tt] without changing the state.
    - [K] models [state := false], returning [tt] in state [false].

    Thus divergence is represented by the absence of a terminating outcome.
    After composition, [K] sends both intermediate states to [(tt, false)].
    This makes the composed transformers fail the original pointwise order. *)

Module SPBindOrderCounterexample.

  Local Obligation Tactic := idtac.

  (** Package relations as well-formed transformers using the existing
      DSP and ASLP shape lemmas. *)
  #[program] Definition dspOf {A} (R : bool -> A * bool -> Prop)
    : StDSP.DSPSt bool A :=
    fun p r => (exists s, p s /\ R s r) /\ (forall s, R s r -> p s).
  Next Obligation.
    intros A R; exact (StDSP.dsp_shape_wf bool R).
  Qed.

  #[program] Definition aslpOf {A} (R : bool -> A * bool -> Prop)
    : StASLP.ASLPSt bool A :=
    fun p r => (exists s, p s /\ R s r) \/ (forall s, R s r -> p s).
  Next Obligation.
    intros A R; exact (StASLP.aslp_shape_wf bool R).
  Qed.

  Definition R0 (s : bool) (r : unit * bool) :=
    s = false /\ r = (tt, false).

  Definition R1 (s : bool) (r : unit * bool) :=
    r = (tt, s).

  Definition K (_ : unit) (_ : bool) (r : unit * bool) :=
    r = (tt, false).

  (** Before bind, DSP orders [R0] below [R1], while ASLP orders [R1]
      below [R0]. *)
  Lemma dsp_order : StDSP.ordDSPSt (dspOf R0) (dspOf R1).
  Proof.
    intros p r [[s [Hp [Hs Hr]]] Hall]; subst s r; split.
    - exists false; split; [exact Hp | reflexivity].
    - intros t H; inversion H; subst t; exact Hp.
  Qed.

  Lemma aslp_order : StASLP.ordASLPSt (aslpOf R1) (aslpOf R0).
  Proof.
    intros p r [[s [Hp Hr]] | Hall].
    - unfold R1 in Hr; subst r; destruct s.
      + right; intros t [Ht Hr]; discriminate Hr.
      + left; exists false; repeat split; assumption.
    - right; intros t [Ht Hr]; subst t r; apply (Hall false); reflexivity.
  Qed.

  (** The existing bind and relation-recovery lemmas reduce each bound
      transformer to the corresponding shape over relational composition. *)
  Lemma bind_dsp {A B} (R : bool -> A * bool -> Prop)
    (F : A -> bool -> B * bool -> Prop) p r :
    StDSP.getDSPSt
      (StDSP.bindDSPSt (dspOf R) (fun a => dspOf (F a))) p r <->
    ((exists s, p s /\ exists a t, R s (a, t) /\ F a t r) /\
     (forall s, (exists a t, R s (a, t) /\ F a t r) -> p s)).
  Proof.
    rewrite (StDSP.bindDSPProg_dsp bool);
      cbn [StDSP.getDSPSt dspOf];
      setoid_rewrite (StDSP.dsp_recov bool); reflexivity.
  Qed.

  Lemma bind_aslp {A B} (R : bool -> A * bool -> Prop)
    (F : A -> bool -> B * bool -> Prop) p r :
    StASLP.getASLPSt
      (StASLP.bindASLPSt (aslpOf R) (fun a => aslpOf (F a))) p r <->
    ((exists s, p s /\ exists a t, R s (a, t) /\ F a t r) \/
     (forall s, (exists a t, R s (a, t) /\ F a t r) -> p s)).
  Proof.
    rewrite (StASLP.bindASLPProg_aslp bool);
      cbn [StASLP.getASLPSt aslpOf];
      setoid_rewrite (StASLP.aslp_recov bool); reflexivity.
  Qed.

  (** At precondition [fun s => s = false], composition through [R0]
      accepts [(tt, false)].  Composition through [R1] also has predecessor
      [true], which violates the DSP universal condition. *)
  Theorem dsp_counterexample :
    exists (m0 m1 : StDSP.DSPSt bool unit)
      (k : unit -> StDSP.DSPSt bool unit),
      StDSP.ordDSPSt m0 m1 /\
      ~ StDSP.ordDSPSt (StDSP.bindDSPSt m0 k) (StDSP.bindDSPSt m1 k).
  Proof.
    exists (dspOf R0), (dspOf R1), (fun a => dspOf (K a)).
    split; [exact dsp_order |]; intro H.
    assert (HL : StDSP.getDSPSt
      (StDSP.bindDSPSt (dspOf R0) (fun a => dspOf (K a)))
      (fun s => s = false) (tt, false)).
    {
      apply bind_dsp; split.
      - exists false; split; [reflexivity |].
        exists tt, false; repeat split; reflexivity.
      - intros s [a [t [[Hs Hr] HK]]]; exact Hs.
    }
    specialize (H _ _ HL); apply bind_dsp in H; destruct H as [_ Hall].
    assert (E : true = false)
      by (apply Hall; exists tt, true; split; reflexivity).
    discriminate E.
  Qed.

  (** At precondition [fun s => s = true], composition through [R1]
      accepts [(tt, false)] via predecessor [true].  Composition through
      [R0] has only predecessor [false], so neither ASLP disjunct holds. *)
  Theorem aslp_counterexample :
    exists (m0 m1 : StASLP.ASLPSt bool unit)
      (k : unit -> StASLP.ASLPSt bool unit),
      StASLP.ordASLPSt m0 m1 /\
      ~ StASLP.ordASLPSt (StASLP.bindASLPSt m0 k) (StASLP.bindASLPSt m1 k).
  Proof.
    exists (aslpOf R1), (aslpOf R0), (fun a => aslpOf (K a)).
    split; [exact aslp_order |]; intro H.
    assert (HL : StASLP.getASLPSt
      (StASLP.bindASLPSt (aslpOf R1) (fun a => aslpOf (K a)))
      (fun s => s = true) (tt, false)).
    {
      apply bind_aslp; left; exists true; split; [reflexivity |].
      exists tt, true; split; reflexivity.
    }
    specialize (H _ _ HL); apply bind_aslp in H.
    destruct H as [[s [Hp [a [t [[Hs Hr] HK]]]]] | Hall]; [congruence |].
    assert (E : false = true)
      by (apply Hall; exists tt, false; repeat split; reflexivity).
    discriminate E.
  Qed.

  (** These witnesses refute bind monotonicity in its first argument,
      even with the continuation fixed. *)
  Corollary dsp_bind_not_monotone :
    ~ (forall (m0 m1 : StDSP.DSPSt bool unit)
         (k : unit -> StDSP.DSPSt bool unit),
      StDSP.ordDSPSt m0 m1 ->
      StDSP.ordDSPSt (StDSP.bindDSPSt m0 k) (StDSP.bindDSPSt m1 k)).
  Proof.
    intro H; destruct dsp_counterexample as [m0 [m1 [k [Hle Hbad]]]].
    exact (Hbad (H m0 m1 k Hle)).
  Qed.

  Corollary aslp_bind_not_monotone :
    ~ (forall (m0 m1 : StASLP.ASLPSt bool unit)
         (k : unit -> StASLP.ASLPSt bool unit),
      StASLP.ordASLPSt m0 m1 ->
      StASLP.ordASLPSt (StASLP.bindASLPSt m0 k) (StASLP.bindASLPSt m1 k)).
  Proof.
    intro H; destruct aslp_counterexample as [m0 [m1 [k [Hle Hbad]]]].
    exact (Hbad (H m0 m1 k Hle)).
  Qed.

End SPBindOrderCounterexample.

Check SPBindOrderCounterexample.dsp_counterexample.
Check SPBindOrderCounterexample.aslp_counterexample.
Check SPBindOrderCounterexample.dsp_bind_not_monotone.
Check SPBindOrderCounterexample.aslp_bind_not_monotone.

Print Assumptions SPBindOrderCounterexample.dsp_bind_not_monotone.
Print Assumptions SPBindOrderCounterexample.aslp_bind_not_monotone.
