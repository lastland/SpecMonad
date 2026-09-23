(** * The four WP observations of [stdivexcnd], assembled from algebras.

    [stdivexcnd S A = stateT S (optionT divnd) A]
      -->  [WStExc S A = stateT S (optionT WPure) A]

    This is the stack where both kinds of layer occur at once, and the two
    [option]s get opposite treatments:

      - [divnd = optionT SetM] : COLLAPSED, by the four algebras of
        [DivNonDet_WPure_Algebra.v].  Its [None] is DIVERGENCE, and the
        total/liberal choice is what to assert for it;
      - the other [optionT]    : PRESERVED, by [MMor_optionT].  Its [None]
        is an EXCEPTION, which the specification must keep talking about,
        so it becomes the [optionT] of [WStExc];
      - [stateT]               : PRESERVED, by [MMor_stateT].

    So the four observations here are the SAME four as for [divnd] --
    the exception and state layers add no choices -- which is why this
    stack has four and not eight.

    [StDivExcNonDet_WStExc.v] writes all four out by hand with a
    [wpure_mono] lemma each. *)

From Coq Require Import Lia PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet StDivExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import
  DivNonDet_WPure_Algebra.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

Local Definition getNE_T {S A} (m : stdivexcndNE S A) : stateT S (optionT (optionT SetM)) A :=
  getNEx m.
#[local] Coercion getNE_T : stdivexcndNE >-> stateT.

Section Observations.
  Variable S : Type.

  (** Collapse the divergence layer, preserve the exception layer, preserve
      the state.  Four times. *)
  Definition MMorX_DWP : MMor (stdivexcnd S) (WStExc S) :=
    MMor_stateT S (MMor_optionT MMor_DWP).
  Definition MMorX_DWLP : MMor (stdivexcnd S) (WStExc S) :=
    MMor_stateT S (MMor_optionT MMor_DWLP).
  Definition MMorX_AWP : MMor (stdivexcnd S) (WStExc S) :=
    MMor_stateT S (MMor_optionT MMor_AWP).
  Definition MMorX_AWLP : MMor (stdivexcnd S) (WStExc S) :=
    MMor_stateT S (MMor_optionT MMor_AWLP).

  Definition obsDWP  {A} (m : stdivexcndNE S A) : WStExc S A := mmor MMorX_DWP (getNEx m).
  Definition obsDWLP {A} (m : stdivexcndNE S A) : WStExc S A := mmor MMorX_DWLP (getNEx m).
  Definition obsAWP  {A} (m : stdivexcndNE S A) : WStExc S A := mmor MMorX_AWP (getNEx m).
  Definition obsAWLP {A} (m : stdivexcndNE S A) : WStExc S A := mmor MMorX_AWLP (getNEx m).

  (** The outcome set of a [bind], for clients that reason about the
      computation directly.  Nothing about the observations depends on
      it; it is stated here because [StDivExcNonDet_WStExc.v] stated it. *)
  Lemma outcomes_bind {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) sigma ob :
    unOptionT (unOptionT (runStateT (x >>= f) sigma)) ob <->
    (exists oy, unOptionT (unOptionT (runStateT x sigma)) oy /\
      match oy with
      | Some (Some (a, s')) => unOptionT (unOptionT (runStateT (f a) s')) ob
      | Some None => ob = Some None
      | None => ob = None
      end).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. exists oy. split; [exact H1|].
      destruct oy as [[[a s']|]|]; cbn in *; exact H2.
    - intros [oy [H1 H2]]. exists oy. split; [exact H1|].
      destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  Qed.

  (** ** What each one says, in terms of the outcome set

      Strip the two preserved layers from both sides and what is left is
      the PURE observation, by [eq_refl]; composing that with the [divnd]
      characterisation gives the statements [StDivExcNonDet_WStExc.v]
      proves by unfolding.  Everything below -- triples and examples
      alike -- goes through these rather than through [cbn]. *)

  Lemma obsDWP_at {A} (m : stdivexcndNE S A) (s : S) :
    unOptionT (runStateT (obsDWP m) s) = obsDWPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsDWLP_at {A} (m : stdivexcndNE S A) (s : S) :
    unOptionT (runStateT (obsDWLP m) s) = obsDWLPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsAWP_at {A} (m : stdivexcndNE S A) (s : S) :
    unOptionT (runStateT (obsAWP m) s) = obsAWPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsAWLP_at {A} (m : stdivexcndNE S A) (s : S) :
    unOptionT (runStateT (obsAWLP m) s) = obsAWLPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsDWP_unfold {A} (m : stdivexcndNE S A) s post :
    unOptionT (runStateT (obsDWP m) s) post <->
    (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
                match oa with Some r => post r | None => False end).
  Proof. rewrite obsDWP_at. apply obsDWPp_get. Qed.

  Lemma obsDWLP_unfold {A} (m : stdivexcndNE S A) s post :
    unOptionT (runStateT (obsDWLP m) s) post <->
    (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
                match oa with Some r => post r | None => True end).
  Proof. rewrite obsDWLP_at. apply obsDWLPp_get. Qed.

  Lemma obsAWP_unfold {A} (m : stdivexcndNE S A) s post :
    unOptionT (runStateT (obsAWP m) s) post <->
    (exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r).
  Proof. rewrite obsAWP_at. apply obsAWPp_get. Qed.

  Lemma obsAWLP_unfold {A} (m : stdivexcndNE S A) s post :
    unOptionT (runStateT (obsAWLP m) s) post <->
    ((exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r)
     \/ unOptionT (unOptionT (runStateT m s)) None).
  Proof. rewrite obsAWLP_at. apply obsAWLPp_get. Qed.

  (** ** The morphism laws, for free *)

  Theorem obsDWP_ret {A} (a : A) :
    eq1 (obsDWP (ret a : stdivexcndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_DWP) A a). Qed.
  Theorem obsDWP_bind {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) :
    eq1 (obsDWP (x >>= f)) (obsDWP x >>= (fun a => obsDWP (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_DWP) A B x f). Qed.

  Theorem obsDWLP_ret {A} (a : A) :
    eq1 (obsDWLP (ret a : stdivexcndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_DWLP) A a). Qed.
  Theorem obsDWLP_bind {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) :
    eq1 (obsDWLP (x >>= f)) (obsDWLP x >>= (fun a => obsDWLP (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_DWLP) A B x f). Qed.

  Theorem obsAWP_ret {A} (a : A) :
    eq1 (obsAWP (ret a : stdivexcndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_AWP) A a). Qed.
  Theorem obsAWP_bind {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) :
    eq1 (obsAWP (x >>= f)) (obsAWP x >>= (fun a => obsAWP (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_AWP) A B x f). Qed.

  Theorem obsAWLP_ret {A} (a : A) :
    eq1 (obsAWLP (ret a : stdivexcndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_AWLP) A a). Qed.
  Theorem obsAWLP_bind {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) :
    eq1 (obsAWLP (x >>= f)) (obsAWLP x >>= (fun a => obsAWLP (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_AWLP) A B x f). Qed.

End Observations.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.
Arguments obsDWP_unfold {_} {_}.
Arguments obsDWLP_unfold {_} {_}.
Arguments obsAWP_unfold {_} {_}.
Arguments obsAWLP_unfold {_} {_}.

(* ================================================================= *)
(** ** WP triples                                                    *)
(* ================================================================= *)

Inductive approxKindWP := | SubsetOf | SupersetOf.

#[program] Definition pp2wp_subset {S A}
  (pre : S -> Prop) (post : option (A * S) -> Prop) : WStExc S A :=
  mkStateT (fun s0 => @mkOptionT WPure _
    (mkWPure (fun p => pre s0 /\ (forall r, post r -> p r)) _)).
Next Obligation.
  intros p q Hpq [Hpre Hsub]. split; [ exact Hpre |].
  intros r Hr. exact (Hpq r (Hsub r Hr)).
Qed.

#[program] Definition pp2wp_superset {S A}
  (pre : S -> Prop) (post : option (A * S) -> Prop) : WStExc S A :=
  mkStateT (fun s0 => @mkOptionT WPure _
    (mkWPure (fun p => (forall r, p r -> post r) -> pre s0) _)).
Next Obligation.
  intros p q Hpq H Hsub. apply H. intros r Hr. exact (Hsub r (Hpq r Hr)).
Qed.

Section WPTriples.

  Definition tripleWP {S A}
    (obs : stdivexcndNE S A -> WStExc S A)
    (prog : stdivexcndNE S A)
    (pre : S -> Prop)
    (kind : approxKindWP)
    (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | SubsetOf   => forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | SupersetOf => forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.

  Definition tripleWPspec {S A}
    (obs : stdivexcndNE S A -> WStExc S A)
    (prog : stdivexcndNE S A)
    (pre : S -> Prop)
    (kind : approxKindWP)
    (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | SubsetOf   => ordWStExc (obs prog) (pp2wp_subset pre post)
    | SupersetOf => ordWStExc (pp2wp_superset pre post) (obs prog)
    end.

  (** [StDivExcNonDet_WStExc.v] assumes the observation is monotone, and
      proves the four [obs*_monotonic] lemmas to supply it.  None of that
      is needed: [WStExc S A = stateT S (optionT WPure) A], so the
      transformer at each state is a [WPure] element and monotonicity is
      its carrier condition. *)
  Theorem tripleWPDefEq {S A}
    (obs : stdivexcndNE S A -> WStExc S A)
    (prog : stdivexcndNE S A)
    (kind : approxKindWP)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleWP obs prog pre kind post <-> tripleWPspec obs prog pre kind post.
  Proof.
    pose proof (fun s => getWPure_mono (unOptionT (runStateT (obs prog) s)))
      as Hmono.
    unfold tripleWP, tripleWPspec, ordWStExc, pp2wp_subset, pp2wp_superset.
    destruct kind; cbn [runStateT unOptionT]; split.
    - intros H s p [Hpre Hsub]. apply (Hmono s post p Hsub). exact (H s Hpre).
    - intros H s Hpre. apply (H s post). split; [ exact Hpre | intros r hr; exact hr ].
    - intros H s p Hwp Hsub. apply H. apply (Hmono s p post Hsub). exact Hwp.
    - intros H s Hwp. apply (H s post Hwp). intros r hr; exact hr.
  Qed.

End WPTriples.

(* ================================================================= *)
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)


(** The example programs of [ExampleProgramDefs.v], on the
    non-empty-outcomes carrier the observations above are defined on. *)
Example progA : stdivexcndNE nat unit :=
  put 42 ;;
  s <- get ;;
  orNEx (put s) (put (s + 1)).

Example progB : stdivexcndNE nat unit :=
  put 42 ;;
  s <- get ;;
  orNEx (put s) spinNEx.

Example progRet : stdivexcndNE nat unit := ret tt.

(** The examples of [StDivExcNonDet_WStExc.v], re-proved against the
    assembled observations.  Each proof begins by rewriting with the
    [_unfold] lemma above instead of [cbn]-ing through the definition, so
    what the example rests on is the [divnd] algebra, not the shape of a
    hand-written transformer. *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  tripleWP obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with Some (_, s) => s >= 42 | None => False end).
Proof.
  unfold tripleWP. intros s0 _. apply obsDWP_unfold.
  cbn. intros [[[]|]|] H; sauto.
Qed.

Theorem progA_DWP_all_spec :
  tripleWPspec obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with Some (_, s) => s >= 42 | None => False end).
Proof.
  unfold tripleWPspec, ordWStExc, pp2wp_subset.
  intros s p Hp. cbn [runStateT unOptionT] in Hp. destruct Hp as [_ Hsub].
  pose proof progA_DWP_all as Hall. unfold tripleWP in Hall. specialize (Hall s I).
  exact (getWPure_mono (unOptionT (runStateT (obsDWP progA) s)) _ p Hsub Hall).
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 :
  not (
    tripleWP obsDWP progA
      (fun _ => True)
      SubsetOf
      (fun r : option (unit * nat) =>
        match r with Some (_, s) => s = 42 | None => False end)).
Proof.
  intro contra. unfold tripleWP in contra. specialize (contra 0 I).
  rewrite obsDWP_unfold in contra. cbn in contra.
  specialize (contra (Some (Some (tt, 43)))). sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with Some (_, s) => s = 42 | None => False end).
Proof.
  intros s0 _. apply obsAWP_unfold. cbn.
  exists (Some (tt, 42)). split; sauto.
Qed.

Theorem progA_AWP_43 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with Some (_, s) => s = 43 | None => False end).
Proof.
  intros s0 _. apply obsAWP_unfold. cbn.
  exists (Some (tt, 43)). split; sauto.
Qed.

(** AWP, over-approximate reading: no run of [progA] reaches state [100],
    so [awp] of that outcome is empty and even [False] is a valid
    necessary precondition. *)
Theorem progA_AWP_100_over :
  tripleWP obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  unfold tripleWP. intros s H. rewrite obsAWP_unfold in H.
  destruct H as [r [Hr Heq]]. subst r. cbn in Hr. sauto.
Qed.

Theorem progA_AWP_100_over_spec :
  tripleWPspec obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  unfold tripleWPspec, ordWStExc, pp2wp_superset.
  intros s p Hp Hsub. rewrite obsAWP_unfold in Hp.
  destruct Hp as [r [Hr Hpr]]. specialize (Hsub r Hpr).
  subst r. cbn in Hr. sauto.
Qed.

(* ================================================================= *)
(** ** WP examples: nondeterminism + divergence                       *)
(* ================================================================= *)

Example progB_DWP := obsDWP progB.
Example progB_DWLP := obsDWLP progB.
Example progB_AWP := obsAWP progB.

(** DWP is unprovable: the divergent branch forces [False]. *)
Theorem progB_DWP_unprovable :
  not (
    tripleWP obsDWP progB
      (fun _ => True)
      SubsetOf
      (fun r : option (unit * nat) =>
        match r with Some (_, s) => s = 42 | None => False end)).
Proof.
  intro contra. unfold tripleWP in contra. specialize (contra 0 I).
  rewrite obsDWP_unfold in contra. cbn in contra.
  specialize (contra None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored.  This is exactly the
    [None => True] of [MAlg_DWLP] against the [None => False] of
    [MAlg_DWP] -- the two differ in nothing else. *)
Theorem progB_DWLP_42 :
  tripleWP obsDWLP progB
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with Some (_, s) => s = 42 | None => False end).
Proof.
  intros s0 _. apply obsDWLP_unfold. cbn. intros [[[]|]|] H; sauto.
Qed.

(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  tripleWP obsAWP progB
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with Some (_, s) => s = 42 | None => False end).
Proof.
  intros s0 _. apply obsAWP_unfold. cbn.
  exists (Some (tt, 42)). split; sauto.
Qed.

(** "There are divergent branches": with [post] empty the terminating
    disjunct of [obsAWLP] is empty, so the triple says exactly that some
    branch diverges. *)
Theorem progB_has_divergent_branch :
  tripleWP obsAWLP progB (fun _ => True) SubsetOf (fun _ => False).
Proof.
  intros s _. apply obsAWLP_unfold. right. cbn. sauto.
Qed.

(** The DWP-Inc triple: [dwp(postEq0)(s)] forces [s = 0]. *)
Theorem progRet_dwp_inc :
  tripleWP obsDWP progRet preEq0 SupersetOf postEq0.
Proof.
  intros s Hwp. rewrite obsDWP_unfold in Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(** Likewise DWLP-Inc, the divergence branch being vacuous. *)
Theorem progRet_dwlp_inc :
  tripleWP obsDWLP progRet preEq0 SupersetOf postEq0.
Proof.
  intros s Hwp. rewrite obsDWLP_unfold in Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(* ================================================================= *)
(** ** The law of the excluded miracle                               *)
(* ================================================================= *)
(** ** The law of the excluded miracle                               *)
(* ================================================================= *)

(** [stdivexcnd] used to be bigger than the language: the everywhere-
    BLOCKED element, with no outcomes at all, made [obsDWP] establish
    every postcondition -- a miracle.  It is no longer a program:
    nonemptiness is part of the carrier
    ([ComputationMonads/StDivExcNonDet.v]), so the miracle cannot be
    written down.

    What used to need [nonEmptyOutcomes m] as a hypothesis is therefore
    now a theorem about EVERY program -- Dijkstra's first healthiness
    condition, with nothing left to assume. *)

Theorem obsDWP_excluded_miracle {S A} (m : stdivexcndNE S A) (s : S) :
  ~ unOptionT (runStateT (obsDWP m) s) (fun _ => False).
Proof.
  intros H. destruct (proj2_sig m s) as [oa Hoa].
  pose proof (proj1 (obsDWP_unfold m s (fun _ => False)) H oa Hoa) as Hc.
  destruct oa as [r|]; exact Hc.
Qed.

(* ================================================================= *)
(** ** The WP-adequacy forms of [ret] and [bind]                     *)
(* ================================================================= *)

(** The pointwise laws the Dijkstra monads consume: [bind] here THREADS
    the continuation's weakest precondition through the postcondition,
    and the [None] branch carries the exception straight to [post None]
    -- the preserved [option] layer, visible in the law. *)

Section AdequacyWP.
  Variable S : Type.

  Lemma obsDWP_ret_wp {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsDWP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    rewrite obsDWP_unfold. cbn. split.
    - intro H. exact (H (Some (Some (a, s0))) eq_refl).
    - intros H oa Hoa. subst oa. exact H.
  Qed.

  Lemma obsDWP_bind_wp {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) s post :
    unOptionT (runStateT (obsDWP (x >>= f)) s) post <->
    unOptionT (runStateT (obsDWP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWP (f a)) s') post
               | None => post None
               end).
  Proof.
  rewrite (obsDWP_unfold (x >>= f) s post). rewrite (obsDWP_unfold x s _).
  setoid_rewrite outcomes_bind. split.
  - intros HL oy Hoy. destruct oy as [[[a s']|]|].
    + cbn beta iota. rewrite obsDWP_unfold. intros ob Hob.
      apply HL. exists (Some (Some (a, s'))). split; [exact Hoy | exact Hob].
    + apply (HL (Some None)). exists (Some None). split; [exact Hoy | reflexivity].
    + apply (HL None). exists None. split; [exact Hoy | reflexivity].
  - intros HR oa [oy [Hoy Hk]]. specialize (HR oy Hoy). destruct oy as [[[a s']|]|].
    + cbn beta iota in HR. rewrite obsDWP_unfold in HR. exact (HR oa Hk).
    + cbn in Hk. subst oa. exact HR.
    + cbn in Hk. subst oa. destruct HR.
  Qed.

  Lemma obsDWLP_ret_wp {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsDWLP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    rewrite obsDWLP_unfold. cbn. split.
    - intro H. exact (H (Some (Some (a, s0))) eq_refl).
    - intros H oa Hoa. subst oa. exact H.
  Qed.

  Lemma obsDWLP_bind_wp {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) s post :
  unOptionT (runStateT (obsDWLP (x >>= f)) s) post <->
  unOptionT (runStateT (obsDWLP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWLP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsDWLP_unfold (x >>= f) s post). rewrite (obsDWLP_unfold x s _).
  setoid_rewrite outcomes_bind. split.
  - intros HL oy Hoy. destruct oy as [[[a s']|]|].
    + cbn beta iota. rewrite obsDWLP_unfold. intros ob Hob.
      apply HL. exists (Some (Some (a, s'))). split; [exact Hoy | exact Hob].
    + apply (HL (Some None)). exists (Some None). split; [exact Hoy | reflexivity].
    + exact I.
  - intros HR oa [oy [Hoy Hk]]. specialize (HR oy Hoy). destruct oy as [[[a s']|]|].
    + cbn beta iota in HR. rewrite obsDWLP_unfold in HR. exact (HR oa Hk).
    + cbn in Hk. subst oa. exact HR.
    + cbn in Hk. subst oa. exact I.
  Qed.

  Lemma obsAWP_ret_wp {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsAWP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    rewrite obsAWP_unfold. cbn. split.
    - intros [r [Hr Hp]]. injection Hr as Hr. subst r. exact Hp.
    - intro H. exists (Some (a, s0)). split; [ reflexivity | exact H ].
  Qed.

  Lemma obsAWP_bind_wp {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) s post :
  unOptionT (runStateT (obsAWP (x >>= f)) s) post <->
  unOptionT (runStateT (obsAWP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsAWP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsAWP_unfold (x >>= f) s post). rewrite (obsAWP_unfold x s _). split.
  - intros [r [Hr Hpost]]. apply outcomes_bind in Hr. destruct Hr as [oy [Hoy Hk]].
    destruct oy as [[[a s']|]|].
    + exists (Some (a, s')). split; [exact Hoy|].
      cbn beta iota. rewrite obsAWP_unfold. exists r. split; [exact Hk | exact Hpost].
    + cbn in Hk. injection Hk as Hk. subst r. exists None. split; [exact Hoy|]. cbn beta iota. exact Hpost.
    + cbn in Hk. discriminate Hk.
  - intros [rx [Hrx HQ]]. destruct rx as [[a s']|].
    + cbn beta iota in HQ. rewrite obsAWP_unfold in HQ. destruct HQ as [r [Hr Hpost]].
      exists r. split; [|exact Hpost]. apply outcomes_bind.
      exists (Some (Some (a, s'))). split; [exact Hrx | exact Hr].
    + cbn beta iota in HQ. exists None. split; [|exact HQ]. apply outcomes_bind.
      exists (Some None). split; [exact Hrx | reflexivity].
  Qed.

  Lemma obsAWLP_ret_wp {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsAWLP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    rewrite obsAWLP_unfold. cbn. split.
    - intros [[r [Hr Hp]] | Hd];
        [ injection Hr as Hr; subst r; exact Hp | discriminate Hd ].
    - intro H. left. exists (Some (a, s0)). split; [ reflexivity | exact H ].
  Qed.

  Lemma obsAWLP_bind_wp {A B} (x : stdivexcndNE S A) (f : A -> stdivexcndNE S B) s post :
  unOptionT (runStateT (obsAWLP (x >>= f)) s) post <->
  unOptionT (runStateT (obsAWLP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsAWLP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsAWLP_unfold (x >>= f) s post). rewrite (obsAWLP_unfold x s _). split.
  - intros [[r [Hr Hpost]] | Hdiv].
    + apply outcomes_bind in Hr. destruct Hr as [oy [Hoy Hk]]. destruct oy as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoy|].
        cbn beta iota. rewrite obsAWLP_unfold. left. exists r. split; [exact Hk | exact Hpost].
      * cbn in Hk. injection Hk as Hk. subst r. left. exists None. split; [exact Hoy|]. cbn beta iota. exact Hpost.
      * cbn in Hk. discriminate Hk.
    + apply outcomes_bind in Hdiv. destruct Hdiv as [oy [Hoy Hk]]. destruct oy as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoy|].
        cbn beta iota. rewrite obsAWLP_unfold. right. exact Hk.
      * cbn in Hk. discriminate Hk.
      * right. exact Hoy.
  - intros [[rx [Hrx HQ]] | Hdivx].
    + destruct rx as [[a s']|].
      * cbn beta iota in HQ. rewrite obsAWLP_unfold in HQ. destruct HQ as [[r [Hr Hpost]] | Hdivf].
        -- left. exists r. split; [|exact Hpost]. apply outcomes_bind.
           exists (Some (Some (a, s'))). split; [exact Hrx | exact Hr].
        -- right. apply outcomes_bind. exists (Some (Some (a, s'))). split; [exact Hrx | exact Hdivf].
      * cbn beta iota in HQ. left. exists None. split; [|exact HQ]. apply outcomes_bind.
        exists (Some None). split; [exact Hrx | reflexivity].
    + right. apply outcomes_bind. exists None. split; [exact Hdivx | reflexivity].
  Qed.
End AdequacyWP.
