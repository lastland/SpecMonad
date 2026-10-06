From ExtLib Require Import OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers DivExcSP.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  StExcNonDet TransformerLaws DivExcNonDet.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

(** * Full-outcome SP observations of [divexcnd] into [DSPDivExc] and [ASLPDivExc]

    [obsDSP] and [obsASLP] preserve return and bind while retaining all
    three raw outcome kinds:

    - [Some (Some a)] : successful return with value [a]
    - [Some None]     : exception
    - [None]          : divergence

    No terminating-slice projection occurs: exceptions and divergence
    remain distinct indices of the postcondition.  The readings differ,
    however: DSP requires [p /\ outcomes m o], whereas ASLP requires
    [p \/ ~ outcomes m o], not outcome membership.  This difference also
    explains why raw-union choice becomes disjunction for DSP but
    conjunction for ASLP. *)

Section Observations.

  (** ** Read an outcome predicate in the pure carriers

      With no state, [p] is one proposition, not a predicate that can hold
      at some predecessors and fail at others.  Pure DSP therefore
      collapses to ASP, and pure ASLP to DSLP; the carrier equivalences
      in [DSPMonad.v] and [ASLPMonad.v] justify these simpler readings. *)

  #[program] Definition readDSP {A} (r : A -> Prop) : DSPSP A :=
    fun p a => p /\ r a.
  Next Obligation.
    apply strict_conj_iff_singleton. intros p a. cbn. tauto.
  Qed.

  (** A reachable [a] requires [p]; an unreachable [a] satisfies this
      reading regardless of [p].  Classically, it is equivalent to
      [r a -> p], the pure DSLP reading. *)
  #[program] Definition readASLP {A} (r : A -> Prop) : ASLPSP A :=
    fun p a => p \/ ~ r a.
  Next Obligation.
    apply term_disj_iff_msingleton. intros p a. cbn. tauto.
  Qed.

  (** ** Retain the computation's full outcome indices

      Both wrappers preserve the option layers; neither selects a [Some]
      slice that would hide a failure outcome. *)

  Definition obsDSP {A} (m : divexcnd A) : DSPDivExc A :=
    mkOptionT (mkOptionT (readDSP (outcomes m))).

  Definition obsASLP {A} (m : divexcnd A) : ASLPDivExc A :=
    mkOptionT (mkOptionT (readASLP (outcomes m))).

  (** ** Run characterizations

      To inspect reachability, choose the precondition deliberately:
      - DSP at [True] is [outcomes m o]; at [False] it is always false.
      - ASLP at [False] is [~ outcomes m o]; at [True] it is always true.

      Thus an ASLP postcondition holding at an outcome does not say that
      the computation can produce it.  Read the examples below at [False]
      to distinguish reachable outcomes from unreachable ones. *)

  Lemma runDSPDivExc_obsDSP {A} (m : divexcnd A) (p : Prop)
      (o : option (option A)) :
    runDSPDivExc (obsDSP m) p o <-> p /\ outcomes m o.
  Proof. reflexivity. Qed.

  Lemma runASLPDivExc_obsASLP {A} (m : divexcnd A) (p : Prop)
      (o : option (option A)) :
    runASLPDivExc (obsASLP m) p o <-> p \/ ~ outcomes m o.
  Proof. reflexivity. Qed.

  (** ** Return morphism laws *)

  Theorem obsDSP_ret {A} (a : A) :
    eq1 (obsDSP (ret a : divexcnd A)) (ret a : DSPDivExc A).
  Proof.
    intros p ob.
    change (p /\ outcomes (ret a) ob <-> runDSPDivExc (ret a) p ob).
    rewrite outcomes_ret. cbn. tauto.
  Qed.

  Theorem obsASLP_ret {A} (a : A) :
    eq1 (obsASLP (ret a : divexcnd A)) (ret a : ASLPDivExc A).
  Proof.
    intros p ob.
    change (p \/ ~ outcomes (ret a) ob <-> runASLPDivExc (ret a) p ob).
    rewrite outcomes_ret. cbn. destruct (classic p); tauto.
  Qed.

  (** ** Bind morphism laws

      Both computation and specification bind call the user continuation
      only on [Some (Some a)].  On [Some None] or [None], each propagates
      the corresponding token instead.  These laws also cover empty
      outcome sets: no nonempty-outcome hypothesis is needed. *)

  Theorem obsDSP_bind {A B} (m : divexcnd A) (f : A -> divexcnd B) :
    eq1 (obsDSP (bind m f)) (bind (obsDSP m) (fun a => obsDSP (f a))).
  Proof.
    intros p ob.
    change (p /\ outcomes (bind m f) ob <->
      runDSPDivExc (bind (obsDSP m) (fun a => obsDSP (f a))) p ob).
    rewrite outcomes_bind. cbn. split.
    - intros [Hp [oa [Hm Hk]]]. exists oa.
      destruct oa as [[a|]|]; cbn in *; tauto.
    - intros [oa H]. destruct oa as [[a|]|]; cbn in *;
        destruct H as [[Hp Hm] Hk].
      all: split; [ exact Hp | eexists; split; eassumption ].
  Qed.

  (** At precondition [False], the ASLP law says that a final outcome is
      unreachable exactly when no intermediate outcome gives a path to it.
      This includes paths that simply propagate an exception or divergence,
      without calling [f]. *)
  Theorem obsASLP_bind {A B} (m : divexcnd A) (f : A -> divexcnd B) :
    eq1 (obsASLP (bind m f)) (bind (obsASLP m) (fun a => obsASLP (f a))).
  Proof.
    intros p ob.
    change (p \/ ~ outcomes (bind m f) ob <->
      runASLPDivExc (bind (obsASLP m) (fun a => obsASLP (f a))) p ob).
    rewrite outcomes_bind. cbn. split.
    - intros [Hp|Hn].
      + intros [[a|]|]; cbn; tauto.
      + intros [[a|]|]; cbn.
        * destruct (classic (outcomes m (Some (Some a)))) as [Hm|Hm]; [ right | tauto ].
          intro Hk. apply Hn. exists (Some (Some a)). auto.
        * intro Hk. right. intro Hm. apply Hn. exists (Some None). auto.
        * intro Hk. right. intro Hm. apply Hn. exists None. auto.
    - intro H. destruct (classic p) as [Hp|Hnp]; [ auto |]. right.
      intros [oa [Hm Hk]]. specialize (H oa).
      destruct oa as [[a|]|]; cbn in *; tauto.
  Qed.

  (** ** Nondeterministic choice characterizations

      [orP] is raw union, so DSP distributes [p /\ _] over the alternatives.
      ASLP negates that union: at [p = False], an outcome is unreachable
      from the choice exactly when both branches rule it out.
      Hence ASLP uses conjunction, not disjunction or left-biased fallback. *)

  Lemma obsDSP_orP {A} (m1 m2 : divexcnd A) (p : Prop)
      (o : option (option A)) :
    runDSPDivExc (obsDSP (orP m1 m2)) p o <->
    runDSPDivExc (obsDSP m1) p o \/ runDSPDivExc (obsDSP m2) p o.
  Proof.
    rewrite !runDSPDivExc_obsDSP, outcomes_orP. tauto.
  Qed.

  Lemma obsASLP_orP {A} (m1 m2 : divexcnd A) (p : Prop)
      (o : option (option A)) :
    runASLPDivExc (obsASLP (orP m1 m2)) p o <->
    runASLPDivExc (obsASLP m1) p o /\ runASLPDivExc (obsASLP m2) p o.
  Proof.
    rewrite !runASLPDivExc_obsASLP, outcomes_orP.
    destruct (classic p); tauto.
  Qed.

  (** ** Examples: reachability, failure propagation, and choice *)

  (** For [spinP], DSP at [True] singles out [None].  ASLP at [False]
      is false at [None] but true at [Some None]: divergence is reachable,
      whereas an exception is not. *)
  Example obsDSP_spin (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP (spinP : divexcnd nat)) p o <-> p /\ o = None.
  Proof.
    rewrite runDSPDivExc_obsDSP, outcomes_spin. reflexivity.
  Qed.

  Example obsASLP_spin (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP (spinP : divexcnd nat)) p o <-> p \/ o <> None.
  Proof.
    rewrite runASLPDivExc_obsASLP, outcomes_spin. reflexivity.
  Qed.

  (** The everywhere-blocking computation: its outcome set is empty.
      Defined locally only to state the failure-propagation examples below. *)
  Local Definition blockP {A} : divexcnd A :=
    @mkOptionT (optionT SetM) A
      (@mkOptionT SetM (option A) (fun _ => False)).

  (** A blocking continuation cannot erase divergence because [spinP]
      never calls it.  Both readings are therefore unchanged by this bind. *)
  Example spin_survives_empty_obsDSP (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP (bindP (spinP : divexcnd unit) (fun _ => blockP (A := nat)))) p o
    <-> p /\ o = None.
  Proof.
    rewrite runDSPDivExc_obsDSP, spin_survives_empty. reflexivity.
  Qed.

  Example spin_survives_empty_obsASLP (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP (bindP (spinP : divexcnd unit) (fun _ => blockP (A := nat)))) p o
    <-> p \/ o <> None.
  Proof.
    rewrite runASLPDivExc_obsASLP, spin_survives_empty. reflexivity.
  Qed.

  (** For [raiseP], ASLP at [False] is false at [Some None] but true at
      [None].  Compare [spinP] above: the readings distinguish an exception
      from divergence rather than treating both as one failure. *)
  Example obsDSP_raise (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP (raiseP : divexcnd nat)) p o <-> p /\ o = Some None.
  Proof.
    rewrite runDSPDivExc_obsDSP, outcomes_raise. reflexivity.
  Qed.

  Example obsASLP_raise (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP (raiseP : divexcnd nat)) p o <-> p \/ o <> Some None.
  Proof.
    rewrite runASLPDivExc_obsASLP, outcomes_raise. reflexivity.
  Qed.

  (** An exception bypasses the continuation just as divergence does. *)
  Example raise_survives_empty_obsDSP (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP (bindP (raiseP : divexcnd unit) (fun _ => blockP (A := nat)))) p o
    <-> p /\ o = Some None.
  Proof.
    rewrite runDSPDivExc_obsDSP, raise_survives_empty. reflexivity.
  Qed.

  Example raise_survives_empty_obsASLP (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP (bindP (raiseP : divexcnd unit) (fun _ => blockP (A := nat)))) p o
    <-> p \/ o <> Some None.
  Proof.
    rewrite runASLPDivExc_obsASLP, raise_survives_empty. reflexivity.
  Qed.

  (** Here the continuation is called: returning [0] then incrementing
      returns [1].  DSP at [True] holds only at [Some (Some 1)].  ASLP at
      [False] holds at [Some (Some 0)] but not [Some (Some 1)]: the old
      result is unreachable, not a second possible result. *)
  Example success_continuation_obsDSP (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP (bind (ret 0 : divexcnd nat) (fun n => ret (S n)))) p o
    <-> p /\ o = Some (Some 1).
  Proof.
    rewrite runDSPDivExc_obsDSP, success_continuation. reflexivity.
  Qed.

  Example success_continuation_obsASLP (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP (bind (ret 0 : divexcnd nat) (fun n => ret (S n)))) p o
    <-> p \/ o <> Some (Some 1).
  Proof.
    rewrite runASLPDivExc_obsASLP, success_continuation. reflexivity.
  Qed.

  (** [mixed] is the raw union of returning [0], raising, and diverging.
      DSP's disjunction lists alternatives; ASLP's conjunction requires
      each branch to rule out [o] whenever [p] is false. *)
  Example mixed_DSP_decomp (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP mixed) p o <->
    runDSPDivExc (obsDSP (ret 0)) p o \/
    runDSPDivExc (obsDSP raiseP) p o \/
    runDSPDivExc (obsDSP spinP) p o.
  Proof.
    unfold mixed.
    rewrite !obsDSP_orP. reflexivity.
  Qed.

  Example mixed_ASLP_decomp (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP mixed) p o <->
    runASLPDivExc (obsASLP (ret 0)) p o /\
    runASLPDivExc (obsASLP raiseP) p o /\
    runASLPDivExc (obsASLP spinP) p o.
  Proof.
    unfold mixed.
    rewrite !obsASLP_orP. reflexivity.
  Qed.

  Example mixed_DSP_outcomes (p : Prop) (o : option (option nat)) :
    runDSPDivExc (obsDSP mixed) p o <->
    p /\ (o = Some (Some 0) \/ o = Some None \/ o = None).
  Proof.
    rewrite runDSPDivExc_obsDSP, mixed_outcomes. reflexivity.
  Qed.

  (** At [p = False], this reading is false at all three reachable
      outcomes, but true at [Some (Some 1)].  At [p = True] it holds
      everywhere, so that precondition would hide the reachability
      distinction illustrated here. *)
  Example mixed_ASLP_outcomes (p : Prop) (o : option (option nat)) :
    runASLPDivExc (obsASLP mixed) p o <->
    p \/ ~ (o = Some (Some 0) \/ o = Some None \/ o = None).
  Proof.
    rewrite runASLPDivExc_obsASLP, mixed_outcomes. reflexivity.
  Qed.

End Observations.
