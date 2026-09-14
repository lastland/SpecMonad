From ITree Require Import Extra.Dijkstra.DijkstraMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers DSPMonad ASLPMonad.

(** * Ordered-bind counterexamples for stateful DSP and ASLP

    Three properties of these specification monads are distinct:

    - Monad laws state the unit and associativity equations up to extensional
      equivalence.
    - Precondition monotonicity fixes a well-formed transformer [w]: if
      [forall s, P s -> Q s], then [w P r -> w Q r].
    - Ordered bind must preserve the order between computations.  In
      particular, for a fixed continuation [k], [m0 <= m1] must imply
      [bind m0 k <= bind m1 k].

    THE ORDER OF THIS FILE'S NEGATIVE THEOREMS IS THE OLD RAW
    TRANSFORMER ORDER [StTrans.ordSPSt] — pointwise implication
    [forall pre r, w1 pre r -> w2 pre r] over the projected
    transformers [StDSP.getDSPSt] / [StASLP.getASLPSt].  That order is
    NOT the canonical order on the monads: since the order
    redefinition, [StDSP.ordDSPSt] and [StASLP.ordASLPSt] compare
    computations by FORWARD INCLUSION of their RECOVERED RELATIONS
    ([StDSP.relDSPSt] / [StASLP.relASLPSt]), and under that order bind
    IS jointly monotone ([StDSP.bindDSPSt_mono],
    [StASLP.bindASLPSt_mono], and the concrete [OrderedMonad]
    dictionaries installed in [StDSP] / [StASLP]).  The positive
    section at the end of this file exhibits the comparison of [R0]
    and [R1] and its preservation under sequencing through the fixed
    continuation [K].

    The existing monad laws and precondition-monotonicity results for
    [StDSP.DSPSt] and [StASLP.ASLPSt] coexist with the failures of
    RAW-ORDERED bind proved here.  Each counterexample varies only the
    first argument of bind and uses the same continuation on both
    sides.

    The witnesses use boolean state and unit return values.  Relations
    describe terminating outcomes [(tt, s)] of type [unit * bool]:

    - [R0] models [if state then diverge else skip].  It has no terminating
      outcome from [true], and from [false] it returns [tt] in state [false].
    - [R1] models [skip], returning [tt] without changing the state.
    - [K] models [state := false], returning [tt] in state [false].

    Thus divergence is represented by the absence of a terminating outcome.
    After composition, [K] sends both intermediate states to [(tt, false)].
    This makes the composed transformers fail the raw transformer order.

    A second group of results strengthens the refutation from the
    current bind to every candidate bind.  On the boolean-state
    carriers, no function [beta] from boolean-result to unit-result
    computations whatsoever satisfies, together, the monad's
    left-identity law for the current return and monotonicity in the
    first argument FOR THE RAW ORDER.  Two direct evaluation probes
    drive the contradiction: [c] accepts an outcome when the
    precondition holds at the outcome's state component, and [k b]
    accepts an outcome when the precondition holds at the fixed
    boolean [b].  Every DSP return lies below [c], while [c] lies
    below every ASLP return; raw-order monotonicity thus forces
    [beta] applied to the probes to accept either every singleton
    precondition — contradicting the strictness of its output once
    conjunctivity meets them into the empty precondition — or some
    singleton precondition whose images under the two continuations
    force one boolean to equal both [false] and [true], once
    termination and disjunctivity extract it from the top
    precondition. *)

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

  (** Under the OLD RAW transformer order, DSP orders [R0] below
      [R1], while ASLP orders [R1] below [R0].  These are statements
      about [StTrans.ordSPSt] on the projected transformers; the
      canonical recovered-relation order on the monads compares both
      by forward inclusion and orders [R0] below [R1] in both — see
      [dsp_order_rel] and [aslp_order_rel] below. *)
  Lemma dsp_order_raw :
    StTrans.ordSPSt (StDSP.getDSPSt (dspOf R0)) (StDSP.getDSPSt (dspOf R1)).
  Proof.
    intros p r [[s [Hp [Hs Hr]]] Hall]; subst s r; split.
    - exists false; split; [exact Hp | reflexivity].
    - intros t H; inversion H; subst t; exact Hp.
  Qed.

  Lemma aslp_order_raw :
    StTrans.ordSPSt (StASLP.getASLPSt (aslpOf R1)) (StASLP.getASLPSt (aslpOf R0)).
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

  (** ** Obstruction theorems for the OLD RAW transformer order

      Every premise and conclusion in this section is a raw
      [StTrans.ordSPSt] statement on the [getDSPSt] / [getASLPSt]
      projections of the transformers; the witnesses and proofs are
      the historical ones. *)

  (** At precondition [fun s => s = false], composition through [R0]
      accepts [(tt, false)].  Composition through [R1] also has predecessor
      [true], which violates the DSP universal condition. *)
  Theorem dsp_counterexample :
    exists (m0 m1 : StDSP.DSPSt bool unit)
      (k : unit -> StDSP.DSPSt bool unit),
      StTrans.ordSPSt (StDSP.getDSPSt m0) (StDSP.getDSPSt m1) /\
      ~ StTrans.ordSPSt (StDSP.getDSPSt (StDSP.bindDSPSt m0 k))
          (StDSP.getDSPSt (StDSP.bindDSPSt m1 k)).
  Proof.
    exists (dspOf R0), (dspOf R1), (fun a => dspOf (K a)).
    split; [exact dsp_order_raw |]; intro H.
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
      StTrans.ordSPSt (StASLP.getASLPSt m0) (StASLP.getASLPSt m1) /\
      ~ StTrans.ordSPSt (StASLP.getASLPSt (StASLP.bindASLPSt m0 k))
          (StASLP.getASLPSt (StASLP.bindASLPSt m1 k)).
  Proof.
    exists (aslpOf R1), (aslpOf R0), (fun a => aslpOf (K a)).
    split; [exact aslp_order_raw |]; intro H.
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

  (** These witnesses refute RAW-ORDERED bind monotonicity in its
      first argument, even with the continuation fixed. *)
  Corollary dsp_bind_not_monotone :
    ~ (forall (m0 m1 : StDSP.DSPSt bool unit)
         (k : unit -> StDSP.DSPSt bool unit),
       StTrans.ordSPSt (StDSP.getDSPSt m0) (StDSP.getDSPSt m1) ->
       StTrans.ordSPSt (StDSP.getDSPSt (StDSP.bindDSPSt m0 k))
         (StDSP.getDSPSt (StDSP.bindDSPSt m1 k))).
  Proof.
    intro H; destruct dsp_counterexample as [m0 [m1 [k [Hle Hbad]]]].
    exact (Hbad (H m0 m1 k Hle)).
  Qed.

  Corollary aslp_bind_not_monotone :
    ~ (forall (m0 m1 : StASLP.ASLPSt bool unit)
         (k : unit -> StASLP.ASLPSt bool unit),
       StTrans.ordSPSt (StASLP.getASLPSt m0) (StASLP.getASLPSt m1) ->
       StTrans.ordSPSt (StASLP.getASLPSt (StASLP.bindASLPSt m0 k))
         (StASLP.getASLPSt (StASLP.bindASLPSt m1 k))).
  Proof.
    intro H; destruct aslp_counterexample as [m0 [m1 [k [Hle Hbad]]]].
    exact (Hbad (H m0 m1 k Hle)).
  Qed.

  (** ** No candidate bind is left-identity and raw-order monotone

      [dsp_bind_not_monotone] and [aslp_bind_not_monotone] above refute
      the CURRENT binds.  The two theorems below show that no
      replacement helps: quantifying over an ARBITRARY
      [beta : M bool -> (bool -> M unit) -> M unit], the monad's
      left-identity law for the current return and RAW-ORDER
      monotonicity in the first argument are jointly unsatisfiable.
      The essential ingredient is the well-formedness of [beta]'s
      OUTPUT, guaranteed by its carrier type: strictness and
      conjunctivity close the DSP case, termination and disjunctivity
      the ASLP case.  The two direct evaluation witnesses below
      merely need to inhabit the carrier.  Neither the concrete bind
      nor relation recovery is involved. *)

  (** The current returns read through their defining formulas: the DSP
      return conjoins and the ASLP return disjoins the existential (ASP)
      and universal (DSLP) returns. *)
  Lemma retDSPSt_iff (a : bool) (pre : bool -> Prop) (r : bool * bool) :
    StDSP.getDSPSt (StDSP.retDSPSt a) pre r <->
    ((exists s, pre s /\ r = (a, s)) /\ (forall s, r = (a, s) -> pre s)).
  Proof. reflexivity. Qed.

  Lemma retASLPSt_iff (a : bool) (pre : bool -> Prop) (r : bool * bool) :
    StASLP.getASLPSt (StASLP.retASLPSt a) pre r <->
    ((exists s, pre s /\ r = (a, s)) \/ (forall s, r = (a, s) -> pre s)).
  Proof. reflexivity. Qed.

  (** Direct evaluation witnesses.  [dsp_c] tests the precondition at
      [snd r], the state component of the outcome; [dsp_k b] tests it
      at the fixed boolean [b], independently of the outcome.  Neither
      enforces any relation between the result value and the state:
      both are pure precondition evaluations.  Each well-formedness
      obligation reduces to direct evaluation of the precondition. *)
  #[program] Definition dsp_c : StDSP.DSPSt bool bool :=
    fun p r => p (snd r).
  Next Obligation.
    split.
    - intros r H; exact H.
    - intros I [i0] p r; split; intro H; exact H.
  Qed.

  #[program] Definition dsp_k (b : bool) : StDSP.DSPSt bool unit :=
    fun p r => p b.
  Next Obligation.
    split.
    - intros r H; exact H.
    - intros I [i0] p r; split; intro H; exact H.
  Qed.

  #[program] Definition aslp_c : StASLP.ASLPSt bool bool :=
    fun p r => p (snd r).
  Next Obligation.
    split.
    - intros r; exact I.
    - intros I [i0] p r; split; intro H; exact H.
  Qed.

  #[program] Definition aslp_k (b : bool) : StASLP.ASLPSt bool unit :=
    fun p r => p b.
  Next Obligation.
    split.
    - intros r; exact I.
    - intros I [i0] p r; split; intro H; exact H.
  Qed.

  (** Left identity is stated as a pointwise iff over preconditions and
      outcomes, and monotonicity transports a raw-order comparison
      between computations through a fixed continuation. *)
  Theorem dsp_arbitrary_bind_impossible :
    forall (beta : StDSP.DSPSt bool bool
              -> (bool -> StDSP.DSPSt bool unit)
              -> StDSP.DSPSt bool unit),
       (forall (b : bool) (k : bool -> StDSP.DSPSt bool unit)
              (pre : bool -> Prop) (r : unit * bool),
          StDSP.getDSPSt (beta (StDSP.retDSPSt b) k) pre r
          <-> StDSP.getDSPSt (k b) pre r) ->
       (forall (m0 m1 : StDSP.DSPSt bool bool)
              (k : bool -> StDSP.DSPSt bool unit),
          StTrans.ordSPSt (StDSP.getDSPSt m0) (StDSP.getDSPSt m1) ->
          StTrans.ordSPSt (StDSP.getDSPSt (beta m0 k))
            (StDSP.getDSPSt (beta m1 k))) ->
       False.
  Proof.
    intros beta HLID HMONO.
    (* [ret b <= dsp_c]: the existential component of the return
       already hands over a predecessor satisfying the precondition. *)
    assert (Hret : forall b : bool,
             StTrans.ordSPSt (StDSP.getDSPSt (StDSP.retDSPSt b))
               (StDSP.getDSPSt dsp_c)).
    { intros b pre r H.
      destruct (proj1 (retDSPSt_iff b pre r) H) as [[s [Hps Hr]] _].
      subst r; exact Hps. }
    (* Left identity followed by monotonicity yields
       [dsp_k b <= beta dsp_c dsp_k]. *)
    assert (Hbound : forall (b : bool) (pre : bool -> Prop) (r : unit * bool),
             StDSP.getDSPSt (dsp_k b) pre r ->
             StDSP.getDSPSt (beta dsp_c dsp_k) pre r).
    { intros b pre r H.
      apply (HMONO (StDSP.retDSPSt b) dsp_c dsp_k (Hret b) pre r).
      exact (proj2 (HLID b dsp_k pre r) H). }
    (* At [(tt, false)] every singleton precondition is accepted. *)
    assert (Hsing : forall b : bool,
             StDSP.getDSPSt (beta dsp_c dsp_k) (fun s => s = b) (tt, false)).
    { intros b; exact (Hbound b (fun s => s = b) (tt, false) eq_refl). }
    (* Conjunctivity over the inhabited family of singletons accepts
       their meet, which is the empty precondition. *)
    pose proof (proj2 (proj2_sig (beta dsp_c dsp_k)) bool (inhabits true)
                   (fun b s => s = b) (tt, false)) as Hconj.
    assert (Hbot : StDSP.getDSPSt (beta dsp_c dsp_k)
                     (fun s => forall b, s = b) (tt, false))
      by exact (proj2 Hconj Hsing).
    assert (Heq : (fun s => forall b, s = b) = (fun _ : bool => False)).
    { apply (StTrans.predExt bool); intro s; split.
      - intro H.
        assert (E : true = false)
          by (rewrite <- (H true), (H false); reflexivity).
        discriminate E.
      - intros []. }
    rewrite Heq in Hbot.
    exact (proj1 (proj2_sig (beta dsp_c dsp_k)) (tt, false) Hbot).
  Qed.

  Theorem aslp_arbitrary_bind_impossible :
    forall (beta : StASLP.ASLPSt bool bool
              -> (bool -> StASLP.ASLPSt bool unit)
              -> StASLP.ASLPSt bool unit),
       (forall (b : bool) (k : bool -> StASLP.ASLPSt bool unit)
              (pre : bool -> Prop) (r : unit * bool),
          StASLP.getASLPSt (beta (StASLP.retASLPSt b) k) pre r
          <-> StASLP.getASLPSt (k b) pre r) ->
       (forall (m0 m1 : StASLP.ASLPSt bool bool)
              (k : bool -> StASLP.ASLPSt bool unit),
          StTrans.ordSPSt (StASLP.getASLPSt m0) (StASLP.getASLPSt m1) ->
          StTrans.ordSPSt (StASLP.getASLPSt (beta m0 k))
            (StASLP.getASLPSt (beta m1 k))) ->
       False.
  Proof.
    intros beta HLID HMONO.
    (* [aslp_c <= ret b]: the universal component of the return covers
       every directly evaluated precondition. *)
    assert (Hret : forall b : bool,
             StTrans.ordSPSt (StASLP.getASLPSt aslp_c)
               (StASLP.getASLPSt (StASLP.retASLPSt b))).
    { intros b pre r H.
      apply (proj2 (retASLPSt_iff b pre r)).
      right; intros s Hr; subst r; exact H. }
    (* Monotonicity followed by left identity yields
       [beta aslp_c aslp_k <= aslp_k b] for every [b]. *)
    assert (Hbound : forall (b : bool) (pre : bool -> Prop) (r : unit * bool),
             StASLP.getASLPSt (beta aslp_c aslp_k) pre r ->
             StASLP.getASLPSt (aslp_k b) pre r).
    { intros b pre r H.
      exact (proj1 (HLID b aslp_k pre r)
               (HMONO aslp_c (StASLP.retASLPSt b) aslp_k (Hret b) pre r H)). }
    (* Top preservation at [(tt, false)], read through the singleton
       cover of the state space, plus disjunctivity: some singleton is
       accepted. *)
    pose proof (proj1 (proj2_sig (beta aslp_c aslp_k)) (tt, false)) as Htop.
    assert (Heq : (fun _ : bool => True) = (fun s => exists b, s = b)).
    { apply (StTrans.predExt bool); intro s; split.
      - intros _; exists s; reflexivity.
      - intros _; exact I. }
    rewrite Heq in Htop.
    destruct (proj1 (proj2 (proj2_sig (beta aslp_c aslp_k)) bool
                      (inhabits true) (fun b s => s = b) (tt, false)) Htop)
      as [b0 Hb0].
    (* Projecting the accepted singleton through [aslp_k false] and
       [aslp_k true] forces [b0] to equal both booleans. *)
    assert (Hf : false = b0)
      by exact (Hbound false (fun s => s = b0) (tt, false) Hb0).
    assert (Ht : true = b0)
      by exact (Hbound true (fun s => s = b0) (tt, false) Hb0).
    congruence.
  Qed.

  (** ** Positive comparisons under the recovered-relation order

      The canonical orders [StDSP.ordDSPSt] and [StASLP.ordASLPSt]
      compare computations by FORWARD INCLUSION of their recovered
      relations.  Reading the packaged transformers back through the
      recovery probes, [R0] lies below [R1] for BOTH monads, and
      sequencing through the fixed continuation [K] preserves the
      comparison — derived here from the concrete ITree
      [OrderedMonad] dictionaries installed in [StDSP] and [StASLP]
      ([monot] applied to [dsp_order_rel] / [aslp_order_rel], with
      [reflex] for the continuation). *)

  Lemma rel_dspOf {A} (R : bool -> A * bool -> Prop) :
    forall s r, StDSP.relDSPSt (dspOf R) s r <-> R s r.
  Proof.
    intros s r.
    apply (StDSP.relDSPSt_of_shape bool R (dspOf R)).
    intros pre r'. reflexivity.
  Qed.

  Lemma rel_aslpOf {A} (R : bool -> A * bool -> Prop) :
    forall s r, StASLP.relASLPSt (aslpOf R) s r <-> R s r.
  Proof.
    intros s r.
    apply (StASLP.relASLPSt_of_shape bool R (aslpOf R)).
    intros pre r'. reflexivity.
  Qed.

  (** Forward inclusion of the relations: [R0] below [R1] under BOTH
      packaged monads' recovered-relation orders. *)
  Lemma dsp_order_rel : StDSP.ordDSPSt (dspOf R0) (dspOf R1).
  Proof.
    intros s r H.
    assert (HR0 : R0 s r) by exact (proj1 (rel_dspOf R0 s r) H).
    apply (proj2 (rel_dspOf R1 s r)).
    destruct HR0 as [Hs Hr]; subst s r; reflexivity.
  Qed.

  Lemma aslp_order_rel : StASLP.ordASLPSt (aslpOf R0) (aslpOf R1).
  Proof.
    intros s r H.
    assert (HR0 : R0 s r) by exact (proj1 (rel_aslpOf R0 s r) H).
    apply (proj2 (rel_aslpOf R1 s r)).
    destruct HR0 as [Hs Hr]; subst s r; reflexivity.
  Qed.

  (** Sequencing through the fixed continuation [K] via the concrete
      dictionaries: [monot] with [reflex] for the continuation. *)
  Theorem dsp_sequenced :
    StDSP.ordDSPSt
      (StDSP.bindDSPSt (dspOf R0) (fun a => dspOf (K a)))
      (StDSP.bindDSPSt (dspOf R1) (fun a => dspOf (K a))).
  Proof.
    exact (@monot (StDSP.DSPSt bool) (StDSP.Monad__DSPSt bool)
             (StDSP.OrderM__DSPSt bool) (StDSP.OrderedMonad__DSPSt bool)
             unit unit (dspOf R0) (dspOf R1)
             (fun a => dspOf (K a)) (fun a => dspOf (K a))
             dsp_order_rel
             (fun a => @reflex (StDSP.DSPSt bool) (StDSP.Monad__DSPSt bool)
                        (StDSP.OrderM__DSPSt bool) (StDSP.OrderedMonad__DSPSt bool)
                        unit (dspOf (K a)))).
  Qed.

  Theorem aslp_sequenced :
    StASLP.ordASLPSt
      (StASLP.bindASLPSt (aslpOf R0) (fun a => aslpOf (K a)))
      (StASLP.bindASLPSt (aslpOf R1) (fun a => aslpOf (K a))).
  Proof.
    exact (@monot (StASLP.ASLPSt bool) (StASLP.Monad__ASLPSt bool)
             (StASLP.OrderM__ASLPSt bool) (StASLP.OrderedMonad__ASLPSt bool)
             unit unit (aslpOf R0) (aslpOf R1)
             (fun a => aslpOf (K a)) (fun a => aslpOf (K a))
             aslp_order_rel
             (fun a => @reflex (StASLP.ASLPSt bool) (StASLP.Monad__ASLPSt bool)
                        (StASLP.OrderM__ASLPSt bool)
                        (StASLP.OrderedMonad__ASLPSt bool)
                        unit (aslpOf (K a)))).
  Qed.

End SPBindOrderCounterexample.

Check SPBindOrderCounterexample.dsp_counterexample.
Check SPBindOrderCounterexample.aslp_counterexample.
Check SPBindOrderCounterexample.dsp_bind_not_monotone.
Check SPBindOrderCounterexample.aslp_bind_not_monotone.
Check SPBindOrderCounterexample.dsp_arbitrary_bind_impossible.
Check SPBindOrderCounterexample.aslp_arbitrary_bind_impossible.
Check SPBindOrderCounterexample.dsp_order_rel.
Check SPBindOrderCounterexample.aslp_order_rel.
Check SPBindOrderCounterexample.dsp_sequenced.
Check SPBindOrderCounterexample.aslp_sequenced.

Print Assumptions SPBindOrderCounterexample.dsp_bind_not_monotone.
Print Assumptions SPBindOrderCounterexample.aslp_bind_not_monotone.
Print Assumptions SPBindOrderCounterexample.dsp_arbitrary_bind_impossible.
Print Assumptions SPBindOrderCounterexample.aslp_arbitrary_bind_impossible.
Print Assumptions SPBindOrderCounterexample.dsp_order_rel.
Print Assumptions SPBindOrderCounterexample.aslp_order_rel.
Print Assumptions SPBindOrderCounterexample.dsp_sequenced.
Print Assumptions SPBindOrderCounterexample.aslp_sequenced.
