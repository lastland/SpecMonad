(** * State: the readings with start states

    The stateful counterpart of [PureReadings.v].  The relation monad is
    [RelSt S = stateT S Rel], so [RelSt S A = S -> A * S -> Prop]: from each
    start state, a set of outcomes.  ([SPSt S] is the same relations in
    arrow form.)  Its computation monad is [stateT S divnd], which is
    [stdivnd S], or [stateT S divndNE] where divergence must be kept.

      stateT S divndNE --obsDWPSt-->  stateT S DWP    strict, conjunctive WPs
                       --obsAWLPSt--> stateT S AWLP   terminating, disjunctive WPs
      stateT S divnd --sliceSt--> RelSt S --rhoAWPSt-->  stateT S AWP
                                          --rhoDWLPSt--> stateT S DWLP
                                          --rhoASPSt-->  ASPSt S
                                          --rhoDSLPSt--> DSLPSt S
                                          --rhoDSPSt-->  DSPSt S
                                          --rhoASLPSt--> ASLPSt S

    A WP reading asks where the program goes FROM one start state, so it is
    the pure reading applied at each start state.  The slice and the four WP
    arrows are all [liftSt], monad morphisms by the one theorem
    [MonadMorphism_stateT], and their targets are specification monads by
    [OrderedMonad_stateT].  The WP side is the pure picture, state by state.

    An SP reading asks where an outcome came FROM: it quantifies over the
    outcome's predecessors, the start states that reach it.  A predecessor
    set mixes start states, so SP readings are not lifts, and each is proved
    a morphism directly.  Without state a predecessor set is empty or
    [{tt}], so "some predecessor satisfies the precondition" and "every
    predecessor does" agree whenever there is one.  With two start states
    they separate:

    - ASP and DSLP still induce inclusion and its reverse
      ([rhoASPSt_order], [rhoDSLPSt_order]).

    - DSP no longer coincides with ASP ([dsp_differs_from_asp]; compare
      [rhoDSP_is_rhoASP]).  Its order asks that every outcome the smaller
      side reaches be reached by the larger side from NO MORE start states
      ([rhoDSPSt_order]); ASLP's order is the converse
      ([rhoASLPSt_rhoDSPSt]).  Without state "no more" is automatic and both
      are inclusions.  With state the order can run against inclusion
      ([dspSt_order_against_inclusion]) and relational [bind] does not
      preserve it: sequencing merges an outcome the order constrains with
      one it leaves free, and the free outcome's extra predecessors show up
      ([dspSt_order_not_bind_mono], [aslpSt_order_not_bind_mono]).

    - Hoare triples are still single inclusions, carved out by ASP and by
      DWLP ([hoareSt_carved_ASPSt], [hoareSt_carved_DWLPSt]).  An
      incorrectness triple is carved out when its precondition is one start
      state ([incorrectSt_carved_one]) and not when it has two
      ([incorrectSt_not_carved_two]): each outcome then needs SOME
      predecessor in the precondition, a union of inclusions that is not
      closed under intersection. *)

From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OrderedMonad MonadMorphism.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  PredMonad WPureMonad SPure ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.Readings Require Import PureReadings.

#[local] Existing Instance Monad_stateT.

(* ================================================================= *)
(** ** Monad morphisms lift through [stateT], state by state          *)
(* ================================================================= *)

Section StateLift.
  Variable S : Type.
  Context {M W : Type -> Type} {MonadM : Monad M} {MonadW : Monad W}
          {Eq1M : Eq1 M} {Eq1W : Eq1 W}
          {EqW : @Eq1Equivalence W MonadW Eq1W} {LawsW : @MonadLawsE W Eq1W MonadW}.

  Definition liftSt (σ : forall A, M A -> W A) {A} (m : stateT S M A) : stateT S W A :=
    mkStateT (fun s => σ _ (runStateT m s)).

  Theorem MonadMorphism_stateT (σ : forall A, M A -> W A) :
    MonadMorphism σ ->
    @MonadMorphism (stateT S M) (stateT S W) _ _ (Eq1_stateT S M) (Eq1_stateT S W)
      (fun A => @liftSt σ A).
  Proof.
    intro Hσ. constructor.
    - intros A x y Hxy s. exact (mm_proper Hσ _ _ (Hxy s)).
    - intros A a s. exact (mm_ret Hσ (a, s)).
    - intros A B x k s.
      etransitivity;
        [ exact (mm_bind Hσ (runStateT x s)
                   (fun vs => let (v, s') := vs in runStateT (k v) s')) |].
      apply Proper_bind; [ reflexivity | intros [v s']; reflexivity ].
  Qed.
End StateLift.

(* ================================================================= *)
(** ** The relation monad with state                                  *)
(* ================================================================= *)

Notation RelSt S := (stateT S PredM.Pred).
Notation mkRelSt R := (@mkStateT _ PredM.Pred _ R).

Definition Monad_RelSt (S : Type) : Monad (RelSt S) :=
  @Monad_stateT S PredM.Pred PredM.Monad_Pred.
Definition Eq1_RelSt (S : Type) : Eq1 (RelSt S) :=
  @Eq1_stateT S PredM.Pred PredM.Eq1_Pred.

#[local] Existing Instance Monad_RelSt | 0.
#[local] Existing Instance Eq1_RelSt | 0.

Lemma relSt_ret {S A} (a : A) (s : S) (r : A * S) :
  runStateT (ret a : RelSt S A) s r <-> r = (a, s).
Proof. reflexivity. Qed.

Lemma relSt_bind {S A B} (R : RelSt S A) (K : A -> RelSt S B) (s : S) (r : B * S) :
  runStateT (bind R K) s r <-> exists a s', runStateT R s (a, s') /\ runStateT (K a) s' r.
Proof.
  split.
  - intros [[a s'] [H1 H2]]. exists a, s'. split; assumption.
  - intros [a [s' [H1 H2]]]. exists (a, s'). split; assumption.
Qed.

Local Notation RelMMSt S W σ :=
  (@MonadMorphism (RelSt S) W (Monad_RelSt S) _ (Eq1_RelSt S) _ σ).

(* ================================================================= *)
(** ** The WP half: the pure readings at each start state              *)
(* ================================================================= *)

Section WPHalf.
  Variable S : Type.

  Definition sliceSt {A} : stateT S divnd A -> RelSt S A := liftSt S (@slice).
  Definition rhoAWPSt {A} : RelSt S A -> stateT S AWP A := liftSt S (@rhoAWP).
  Definition rhoDWLPSt {A} : RelSt S A -> stateT S DWLP A := liftSt S (@rhoDWLP).
  Definition obsDWPSt {A} : stateT S divndNE A -> stateT S DWP A := liftSt S (@obsDWP).
  Definition obsAWLPSt {A} : stateT S divndNE A -> stateT S AWLP A := liftSt S (@obsAWLP).

  Corollary sliceSt_morphism :
    @MonadMorphism (stateT S divnd) (RelSt S) _ (Monad_RelSt S)
      (@Eq1_stateT S divnd Eq1__divnd) (Eq1_RelSt S) (@sliceSt).
  Proof. exact (MonadMorphism_stateT S (@slice) slice_morphism). Qed.

  Corollary rhoAWPSt_morphism : RelMMSt S (stateT S AWP) (@rhoAWPSt).
  Proof. exact (MonadMorphism_stateT S (@rhoAWP) rhoAWP_morphism). Qed.

  Corollary rhoDWLPSt_morphism : RelMMSt S (stateT S DWLP) (@rhoDWLPSt).
  Proof. exact (MonadMorphism_stateT S (@rhoDWLP) rhoDWLP_morphism). Qed.

  Corollary obsDWPSt_morphism :
    @MonadMorphism (stateT S divndNE) (stateT S DWP) _ _ _ _ (@obsDWPSt).
  Proof. exact (MonadMorphism_stateT S (@obsDWP) obsDWP_morphism). Qed.

  Corollary obsAWLPSt_morphism :
    @MonadMorphism (stateT S divndNE) (stateT S AWLP) _ _ _ _ (@obsAWLPSt).
  Proof. exact (MonadMorphism_stateT S (@obsAWLP) obsAWLP_morphism). Qed.

  (** The targets are specification monads under the pointwise order. *)

  Corollary OrderedMonad_AWPSt : OrderedMonad (stateT S AWP) (le_stateT (@leWH AWPH)).
  Proof. exact (OrderedMonad_stateT _ OrderedMonad_AWP). Qed.

  Corollary OrderedMonad_DWLPSt : OrderedMonad (stateT S DWLP) (le_stateT (@leWH DWLPH)).
  Proof. exact (OrderedMonad_stateT _ OrderedMonad_DWLP). Qed.

  Corollary OrderedMonad_DWPSt : OrderedMonad (stateT S DWP) (le_stateT (@leWH DWPH)).
  Proof. exact (OrderedMonad_stateT _ OrderedMonad_DWP). Qed.

  Corollary OrderedMonad_AWLPSt : OrderedMonad (stateT S AWLP) (le_stateT (@leWH AWLPH)).
  Proof. exact (OrderedMonad_stateT _ OrderedMonad_AWLP). Qed.

  (** The induced orders are the pure ones at each start state. *)

  Theorem rhoAWPSt_order {A} (R R' : RelSt S A) :
    le_stateT (@leWH AWPH) A (rhoAWPSt R) (rhoAWPSt R')
    <-> (forall s r, runStateT R' s r -> runStateT R s r).
  Proof.
    split.
    - intros H s. exact (proj1 (rhoAWP_order (runStateT R s) (runStateT R' s)) (H s)).
    - intros H s. exact (proj2 (rhoAWP_order (runStateT R s) (runStateT R' s)) (H s)).
  Qed.

  Theorem rhoDWLPSt_order {A} (R R' : RelSt S A) :
    le_stateT (@leWH DWLPH) A (rhoDWLPSt R) (rhoDWLPSt R')
    <-> (forall s r, runStateT R s r -> runStateT R' s r).
  Proof.
    split.
    - intros H s. exact (proj1 (rhoDWLP_order (runStateT R s) (runStateT R' s)) (H s)).
    - intros H s. exact (proj2 (rhoDWLP_order (runStateT R s) (runStateT R' s)) (H s)).
  Qed.
End WPHalf.

(* ================================================================= *)
(** ** The SP half: readings over predecessors                         *)
(* ================================================================= *)

Section SPHalf.
  Variable S : Type.

  Definition rhoASPSt {A} (R : RelSt S A) : ASPSt S A := aspOfRelSt (runStateT R).
  Definition rhoDSLPSt {A} (R : RelSt S A) : DSLPSt S A := dslpOfRelSt (runStateT R).
  Definition rhoDSPSt {A} (R : RelSt S A) : DSPSt S A := dspOfRelSt (runStateT R).
  Definition rhoASLPSt {A} (R : RelSt S A) : ASLPSt S A := aslpOfRelSt (runStateT R).

  Theorem rhoASPSt_morphism : RelMMSt S (ASPSt S) (@rhoASPSt).
  Proof.
    constructor.
    - intros A R R' HR. apply eq1_ASPSt_get. intros pre r. unfold rhoASPSt.
      rewrite !getASPSt_of. split; intros [s [Hs Hr]]; exists s;
        (split; [ exact Hs | apply (HR s r); exact Hr ]).
    - intros A a. apply eq1_ASPSt_get. intros pre r. unfold rhoASPSt. cbn [ret Monad_ASPSt].
      rewrite getASPSt_of, getASPSt_ret. setoid_rewrite relSt_ret. reflexivity.
    - intros A B R K. apply eq1_ASPSt_get. intros pre r. unfold rhoASPSt. cbn [bind Monad_ASPSt].
      rewrite getASPSt_of, getASPSt_bind. setoid_rewrite getASPSt_of. setoid_rewrite relSt_bind.
      split.
      + intros [s [Hs [a [s' [H1 H2]]]]]. exists a, s'.
        split; [ exists s; split; assumption | exists s'; split; [ reflexivity | exact H2 ] ].
      + intros [a [s' [[s [Hs H1]] [t [Ht H2]]]]]. subst t.
        exists s. split; [ exact Hs | exists a, s'; split; assumption ].
  Qed.

  Theorem rhoDSLPSt_morphism : RelMMSt S (DSLPSt S) (@rhoDSLPSt).
  Proof.
    constructor.
    - intros A R R' HR. apply eq1_DSLPSt_get. intros pre r. unfold rhoDSLPSt.
      rewrite !getDSLPSt_of. split; intros H s Hr; apply H, (HR s r), Hr.
    - intros A a. apply eq1_DSLPSt_get. intros pre r. unfold rhoDSLPSt. cbn [ret Monad_DSLPSt].
      rewrite getDSLPSt_of, getDSLPSt_ret. setoid_rewrite relSt_ret. reflexivity.
    - intros A B R K. apply eq1_DSLPSt_get. intros pre r. unfold rhoDSLPSt. cbn [bind Monad_DSLPSt].
      rewrite getDSLPSt_of, getDSLPSt_bind. setoid_rewrite dslpRelSt_of.
      setoid_rewrite getDSLPSt_of. setoid_rewrite relSt_bind.
      split.
      + intros H a s' Hk s Hm. apply H. exists a, s'. split; assumption.
      + intros H s [a [s' [Hm Hk]]]. exact (H a s' Hk s Hm).
  Qed.

  (** DSP and ASLP are read through their recovered relations. *)

  Lemma eq1_DSPSt_rel {A} (w v : DSPSt S A) :
    (forall x y, dspRel w x y <-> dspRel v x y) -> eq1 w v.
  Proof.
    intros H P y. rewrite (dspRel_spec w P y), (dspRel_spec v P y).
    apply dspOf_cong. exact H.
  Qed.

  Lemma dspRel_retSt {A} (a : A) (s : S) (r : A * S) :
    dspRel (ret a : DSPSt S A) (tt, s) r <-> (a, s) = r.
  Proof.
    exact (@rd_pure DSPArr _ _ _ (@dspRel) RelDenote_DSP (unit * S) (A * S)
             (fun '(u, s0) => ((fun _ : unit => a) u, s0)) (tt, s) r).
  Qed.

  Theorem rhoDSPSt_morphism : RelMMSt S (DSPSt S) (@rhoDSPSt).
  Proof.
    constructor.
    - intros A R R' HR. apply eq1_DSPSt_rel. intros [[] s] r. unfold rhoDSPSt.
      rewrite !dspRelSt_of. exact (HR s r).
    - intros A a. apply eq1_DSPSt_rel. intros [[] s] r. unfold rhoDSPSt.
      rewrite dspRelSt_of, dspRel_retSt, relSt_ret.
      split; intro H; symmetry; exact H.
    - intros A B R K. apply eq1_DSPSt_rel. intros [[] s] r. unfold rhoDSPSt.
      rewrite dspRelSt_of, relSt_bind. symmetry.
      exact (dspRelSt_bind_of (runStateT R) (fun a => runStateT (K a)) s r).
  Qed.

  Lemma eq1_ASLPSt_rel {A} (w v : ASLPSt S A) :
    (forall x y, aslpRel w x y <-> aslpRel v x y) -> eq1 w v.
  Proof.
    intros H P y. rewrite (aslpRel_spec w P y), (aslpRel_spec v P y).
    apply aslpOf_cong. exact H.
  Qed.

  Lemma aslpRel_retSt {A} (a : A) (s : S) (r : A * S) :
    aslpRel (ret a : ASLPSt S A) (tt, s) r <-> (a, s) = r.
  Proof.
    exact (@rd_pure ASLPArr _ _ _ (@aslpRel) RelDenote_ASLP (unit * S) (A * S)
             (fun '(u, s0) => ((fun _ : unit => a) u, s0)) (tt, s) r).
  Qed.

  Theorem rhoASLPSt_morphism : RelMMSt S (ASLPSt S) (@rhoASLPSt).
  Proof.
    constructor.
    - intros A R R' HR. apply eq1_ASLPSt_rel. intros [[] s] r. unfold rhoASLPSt.
      rewrite !aslpRelSt_of. exact (HR s r).
    - intros A a. apply eq1_ASLPSt_rel. intros [[] s] r. unfold rhoASLPSt.
      rewrite aslpRelSt_of, aslpRel_retSt, relSt_ret.
      split; intro H; symmetry; exact H.
    - intros A B R K. apply eq1_ASLPSt_rel. intros [[] s] r. unfold rhoASLPSt.
      rewrite aslpRelSt_of, relSt_bind. symmetry.
      exact (aslpRelSt_bind_of (runStateT R) (fun a => runStateT (K a)) s r).
  Qed.

  (* ================================================================= *)
  (** *** The orders the SP readings induce on [RelSt S]               *)
  (* ================================================================= *)

  Theorem rhoASPSt_order {A} (R R' : RelSt S A) :
    ordASPSt (rhoASPSt R) (rhoASPSt R') <-> (forall s r, runStateT R s r -> runStateT R' s r).
  Proof.
    rewrite ordASPSt_get. unfold rhoASPSt. setoid_rewrite getASPSt_of. split.
    - intros H s r Hr.
      destruct (H (fun t => t = s) r (ex_intro _ s (conj eq_refl Hr))) as [t [Ht Ht']].
      subst t. exact Ht'.
    - intros H pre r [s [Hs Hr]]. exists s. split; [ exact Hs | exact (H s r Hr) ].
  Qed.

  Theorem rhoDSLPSt_order {A} (R R' : RelSt S A) :
    ordDSLPSt (rhoDSLPSt R) (rhoDSLPSt R') <-> (forall s r, runStateT R' s r -> runStateT R s r).
  Proof.
    rewrite ordDSLPSt_get. unfold rhoDSLPSt. setoid_rewrite getDSLPSt_of. split.
    - intros H s r Hr'. exact (H (fun t => runStateT R t r) r (fun t Ht => Ht) s Hr').
    - intros H pre r Hpre s Hr'. exact (Hpre s (H s r Hr')).
  Qed.

  (** At every outcome [R] reaches, [R'] reaches it too, and from no more
      start states. *)
  Theorem rhoDSPSt_order {A} (R R' : RelSt S A) :
    ordDSPSt (rhoDSPSt R) (rhoDSPSt R')
    <-> (forall r, (exists s, runStateT R s r) ->
           (exists s, runStateT R' s r) /\ (forall s, runStateT R' s r -> runStateT R s r)).
  Proof.
    rewrite ordDSPSt_get. unfold rhoDSPSt. setoid_rewrite getDSPSt_of. split.
    - intros H r [s0 H0].
      destruct (H (fun t => runStateT R t r) r
                  (conj (ex_intro _ s0 (conj H0 H0)) (fun t Ht => Ht)))
        as [[s [_ Hs]] Hall].
      split; [ exists s; exact Hs | exact Hall ].
    - intros H pre r [[s [Hs Hr]] Hall].
      destruct (H r (ex_intro _ s Hr)) as [[s' Hs'] Hback].
      split.
      + exists s'. split; [ exact (Hall s' (Hback s' Hs')) | exact Hs' ].
      + intros t Ht. exact (Hall t (Hback t Ht)).
  Qed.

  (** At every outcome [R'] reaches, [R] reaches it too, and from no more
      start states. *)
  Theorem rhoASLPSt_order {A} (R R' : RelSt S A) :
    ordASLPSt (rhoASLPSt R) (rhoASLPSt R')
    <-> (forall r, (exists s, runStateT R' s r) ->
           (exists s, runStateT R s r) /\ (forall s, runStateT R s r -> runStateT R' s r)).
  Proof.
    rewrite ordASLPSt_get. unfold rhoASLPSt. setoid_rewrite getASLPSt_of. split.
    - intros H r [s0 H0].
      assert (Hno : ~ ((exists t, ~ runStateT R' t r /\ runStateT R t r)
                       \/ (forall t, runStateT R t r -> ~ runStateT R' t r))).
      { intro Hl. destruct (H (fun t => ~ runStateT R' t r) r Hl) as [[t [Ht Ht']] | Hall].
        - exact (Ht Ht').
        - exact (Hall s0 H0 H0). }
      split.
      + apply NNPP. intro Hn. apply Hno. right. intros t Ht _. exact (Hn (ex_intro _ t Ht)).
      + intros t Ht. apply NNPP. intro Hn. apply Hno. left. exists t. split; assumption.
    - intros H pre r Hl. destruct (classic (exists s, runStateT R' s r)) as [Hr' | Hn].
      + destruct (H r Hr') as [[s1 Hs1] Hincl]. left.
        destruct Hl as [[s [Hs Hr]] | Hall].
        * exists s. split; [ exact Hs | exact (Hincl s Hr) ].
        * exists s1. split; [ exact (Hall s1 Hs1) | exact (Hincl s1 Hs1) ].
      + right. intros s Hs. exfalso. exact (Hn (ex_intro _ s Hs)).
  Qed.

  Corollary rhoASLPSt_rhoDSPSt {A} (R R' : RelSt S A) :
    ordASLPSt (rhoASLPSt R) (rhoASLPSt R') <-> ordDSPSt (rhoDSPSt R') (rhoDSPSt R).
  Proof. rewrite rhoASLPSt_order, rhoDSPSt_order. reflexivity. Qed.
End SPHalf.

(* ================================================================= *)
(** ** What two start states change                                    *)
(* ================================================================= *)

(** [bothReachTrue] reaches [(tt, true)] from both states, [fromTrue] from
    [true] alone. *)
Definition bothReachTrue : RelSt bool unit := mkRelSt (fun _ r => r = (tt, true)).
Definition fromTrue : RelSt bool unit := mkRelSt (fun s r => s = true /\ r = (tt, true)).

(** ASP accepts the precondition "the start state was [true]" at
    [(tt, true)], because one predecessor satisfies it; DSP rejects it,
    because the other does not. *)
Example dsp_differs_from_asp :
  getASPSt (rhoASPSt bool bothReachTrue) (fun s => s = true) (tt, true)
  /\ ~ getDSPSt (rhoDSPSt bool bothReachTrue) (fun s => s = true) (tt, true).
Proof.
  unfold rhoASPSt, rhoDSPSt. rewrite getASPSt_of, getDSPSt_of. cbn. split.
  - exists true. split; reflexivity.
  - intros [_ H]. discriminate (H false eq_refl).
Qed.

(** [fromTrue] is included in [bothReachTrue], yet the DSP order puts it
    above: the two reach the same outcome, [fromTrue] from fewer states. *)
Example dspSt_order_against_inclusion :
  (forall s r, runStateT fromTrue s r -> runStateT bothReachTrue s r)
  /\ ~ ordDSPSt (rhoDSPSt bool fromTrue) (rhoDSPSt bool bothReachTrue)
  /\ ordDSPSt (rhoDSPSt bool bothReachTrue) (rhoDSPSt bool fromTrue).
Proof.
  split; [| split ].
  - intros s r [_ Hr]. exact Hr.
  - rewrite rhoDSPSt_order. intro H.
    destruct (H (tt, true) (ex_intro _ true (conj eq_refl eq_refl))) as [_ Hback].
    destruct (Hback false eq_refl) as [E _]. discriminate E.
  - apply rhoDSPSt_order. intros r [s Hr]. split.
    + exists true. split; [ reflexivity | exact Hr ].
    + intros t [_ Ht]. exact Ht.
Qed.

(** [onlyFalse] returns only from [false]; [keepState] returns from every
    state, keeping it; [resetState] sets the state to [false].  The DSP order
    constrains [keepState] only at [(tt, false)], the one outcome
    [onlyFalse] reaches, where both have the predecessor [false] alone.
    [(tt, true)] is left free.  After [resetState] merges both outcomes onto
    [(tt, false)], [keepState]'s start state [true] becomes a predecessor
    there. *)
Definition onlyFalse : RelSt bool unit := mkRelSt (fun s r => s = false /\ r = (tt, false)).
Definition keepState : RelSt bool unit := mkRelSt (fun s r => r = (tt, s)).
Definition resetState (_ : unit) : RelSt bool unit := mkRelSt (fun _ r => r = (tt, false)).

Theorem dspSt_order_not_bind_mono :
  ordDSPSt (rhoDSPSt bool onlyFalse) (rhoDSPSt bool keepState)
  /\ ~ ordDSPSt (rhoDSPSt bool (bind onlyFalse resetState))
                (rhoDSPSt bool (bind keepState resetState)).
Proof.
  rewrite !rhoDSPSt_order. split.
  - intros r [s Hs]. destruct Hs as [-> ->]. split.
    + exists false. reflexivity.
    + intros t Ht. cbn in Ht. injection Ht as <-. split; reflexivity.
  - intro H.
    assert (Hin : exists s, runStateT (bind onlyFalse resetState) s (tt, false)).
    { exists false. apply relSt_bind. exists tt, false. cbn. split; [ split |]; reflexivity. }
    destruct (H (tt, false) Hin) as [_ Hback].
    assert (Htrue : runStateT (bind keepState resetState) true (tt, false)).
    { apply relSt_bind. exists tt, true. cbn. split; reflexivity. }
    destruct (proj1 (relSt_bind _ _ _ _) (Hback true Htrue)) as [a [s' [[E _] _]]].
    discriminate E.
Qed.

Theorem aslpSt_order_not_bind_mono :
  ordASLPSt (rhoASLPSt bool keepState) (rhoASLPSt bool onlyFalse)
  /\ ~ ordASLPSt (rhoASLPSt bool (bind keepState resetState))
                 (rhoASLPSt bool (bind onlyFalse resetState)).
Proof. rewrite !rhoASLPSt_rhoDSPSt. exact dspSt_order_not_bind_mono. Qed.

(* ================================================================= *)
(** ** Which triples an index carves out                               *)
(* ================================================================= *)

(** Hoare: every outcome from a [P]-state satisfies [Q]. *)
Definition hoareSt {S A} (P : S -> Prop) (Q : A * S -> Prop) (R : RelSt S A) : Prop :=
  forall s r, P s -> runStateT R s r -> Q r.

(** Incorrectness: every [Q]-outcome is reached from some [P]-state. *)
Definition incorrectSt {S A} (P : S -> Prop) (Q : A * S -> Prop) (R : RelSt S A) : Prop :=
  forall r, Q r -> exists s, P s /\ runStateT R s r.

Theorem hoareSt_carved_ASPSt {S A} (P : S -> Prop) (Q : A * S -> Prop) :
  carvedBy ordASPSt (rhoASPSt S) (hoareSt P Q).
Proof.
  exists (rhoASPSt S (mkRelSt (fun s r => P s -> Q r))). intro R.
  rewrite rhoASPSt_order. unfold hoareSt. cbn [runStateT].
  split; [ intros H s r Hr Hs; exact (H s r Hs Hr) | intros H s r Hs Hr; exact (H s r Hr Hs) ].
Qed.

Theorem hoareSt_carved_DWLPSt {S A} (P : S -> Prop) (Q : A * S -> Prop) :
  carvedBy (le_stateT (@leWH DWLPH) A) (rhoDWLPSt S) (hoareSt P Q).
Proof.
  exists (rhoDWLPSt S (mkRelSt (fun s r => P s -> Q r))). intro R.
  rewrite rhoDWLPSt_order. unfold hoareSt. cbn [runStateT].
  split; [ intros H s r Hr Hs; exact (H s r Hs Hr) | intros H s r Hs Hr; exact (H s r Hr Hs) ].
Qed.

Lemma rhoASPSt_onto {S A} (w : ASPSt S A) :
  ordASPSt (rhoASPSt S (mkRelSt (fun s r => getASPSt w (fun t => t = s) r))) w
  /\ ordASPSt w (rhoASPSt S (mkRelSt (fun s r => getASPSt w (fun t => t = s) r))).
Proof.
  unfold rhoASPSt. rewrite !ordASPSt_get. setoid_rewrite getASPSt_of. cbn [runStateT].
  split; intros pre r H; apply getASPSt_singleton; exact H.
Qed.

(** As without state, the classes an ASP index carves out from below are
    the principal up-sets of inclusion. *)
Corollary carved_ASPSt_op_iff {S A} (T : RelSt S A -> Prop) :
  carvedBy (fun x y => ordASPSt y x) (rhoASPSt S) T
  <-> exists W0 : RelSt S A, forall R, T R <-> (forall s r, runStateT W0 s r -> runStateT R s r).
Proof.
  apply (carved_iso (fun x y => ordASPSt y x) (rhoASPSt S)
           (fun R R' => forall s r, runStateT R' s r -> runStateT R s r)).
  - intros u v w H1 H2. exact (PreOrder_Transitive w v u H2 H1).
  - intro w. exists (mkRelSt (fun s r => getASPSt w (fun t => t = s) r)).
    destruct (rhoASPSt_onto w) as [H1 H2]. split; assumption.
  - intros R R'. apply rhoASPSt_order.
Qed.

Theorem incorrectSt_carved_one {S A} (p : S) (Q : A * S -> Prop) :
  carvedBy (fun x y => ordASPSt y x) (rhoASPSt S) (incorrectSt (fun s => s = p) Q).
Proof.
  apply carved_ASPSt_op_iff. exists (mkRelSt (fun s r => s = p /\ Q r)). intro R.
  unfold incorrectSt. cbn [runStateT]. split.
  - intros H s r [-> Hr]. destruct (H r Hr) as [s [-> HR]]. exact HR.
  - intros H r Hr. exists p. split; [ reflexivity | exact (H p r (conj eq_refl Hr)) ].
Qed.

(** With two start states, each one-witness relation satisfies the triple,
    so an up-set generator would lie inside both, hence be empty, and the
    empty relation would satisfy it too. *)
Theorem incorrectSt_not_carved_two {S A} (p1 p2 : S) (r0 : A * S) :
  p1 <> p2 ->
  ~ carvedBy (fun x y => ordASPSt y x) (rhoASPSt S)
      (incorrectSt (fun s => s = p1 \/ s = p2) (fun r => r = r0)).
Proof.
  intros Hne Hc. apply carved_ASPSt_op_iff in Hc. destruct Hc as [W0 HW].
  assert (Honly : forall p, p = p1 \/ p = p2 ->
             forall s r, runStateT W0 s r -> s = p /\ r = r0).
  { intros p Hp.
    exact (proj1 (HW (mkRelSt (fun s r => s = p /\ r = r0)))
             (fun r Hr => ex_intro _ p (conj Hp (conj eq_refl Hr)))). }
  assert (Hempty : incorrectSt (fun s => s = p1 \/ s = p2) (fun r => r = r0)
                     (mkRelSt (fun _ _ => False) : RelSt S A)).
  { apply (proj2 (HW _)). intros s r Hw. exfalso.
    destruct (Honly p1 (or_introl eq_refl) s r Hw) as [E1 _].
    destruct (Honly p2 (or_intror eq_refl) s r Hw) as [E2 _].
    apply Hne. congruence. }
  destruct (Hempty r0 eq_refl) as [s [_ []]].
Qed.
