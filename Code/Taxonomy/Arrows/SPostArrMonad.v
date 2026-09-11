(** * Effect-observation helpers for the ASP and DSLP specification monads.

    Minimal monad-facing layer for [Taxonomy/EffectObservations/SP]: the
    monad dictionaries of the arrow stacks, the relational readings of
    their [ret] and [bind] (instantiating the generic specs of
    [Classes.RelArrowCoherence]), the angelic-to-demonic conversion with
    its operation preservation, and the evaluators over an initial-state
    precondition. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad RelArrowCoherence.
From Incorrectness.Classes Require Import OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Export SPostArr.
Import MonadNotation.

(** ** Relation constructors *)

Local Obligation Tactic := idtac.

#[program] Definition relASP {A B} (R : A -> B -> Prop) : PureASPostArr A B :=
  fun P b => exists a, P a /\ R a b.
Next Obligation.
  intros A B R. split.
  - intros b [a [HF _]]. exact HF.
  - intros I HI p b. split.
    + intros [a [[i H] HR]]. exists i, a. auto.
    + intros [i [a [H HR]]]. exists a. split; [exists i; exact H | exact HR].
Qed.

#[program] Definition relDSLP {A B} (R : A -> B -> Prop) : PureDSLPostArr A B :=
  fun P b => forall a, R a b -> P a.
Next Obligation.
  intros A B R. split.
  - intros b a _. exact I.
  - intros I HI p b. split.
    + intros H i a Heq. exact (H a Heq i).
    + intros H a Heq i. exact (H i a Heq).
Qed.

Lemma getASP_relASP {A B} (R : A -> B -> Prop) P b :
  getASP (relASP R) P b <-> exists a, P a /\ R a b.
Proof. reflexivity. Qed.

Lemma getDSLP_relDSLP {A B} (R : A -> B -> Prop) P b :
  getDSLP (relDSLP R) P b <-> forall a, R a b -> P a.
Proof. reflexivity. Qed.

Lemma ASP_rel_relASP {A B} (R : A -> B -> Prop) a b :
  ASP_rel (relASP R) a b <-> R a b.
Proof.
  unfold ASP_rel. rewrite getASP_relASP. split.
  - intros [a' [Heq HR]]. subst a'. exact HR.
  - intro HR. exists a. split; [reflexivity | exact HR].
Qed.

Lemma DSLP_rel_relDSLP {A B} (R : A -> B -> Prop) a b :
  DSLP_rel (relDSLP R) a b <-> R a b.
Proof.
  unfold DSLP_rel. split.
  - intro H. apply H.
    apply (proj2 (getDSLP_relDSLP R (fun a0 => R a0 b) b)).
    intros a' HR'. exact HR'.
  - intros HR Q HQ. exact (proj1 (getDSLP_relDSLP R Q b) HQ a HR).
Qed.

(** ** Angelic-to-demonic conversion *)

Definition asp_to_dslp {A B} (w : PureASPostArr A B) : PureDSLPostArr A B :=
  relDSLP (ASP_rel w).

Lemma asp_to_dslp_spec {A B} (w : PureASPostArr A B) P b :
  getDSLP (asp_to_dslp w) P b <-> forall a, ASP_rel w a b -> P a.
Proof. exact (getDSLP_relDSLP (ASP_rel w) P b). Qed.

Lemma DSLP_rel_asp_to_dslp {A B} (w : PureASPostArr A B) a b :
  DSLP_rel (asp_to_dslp w) a b <-> ASP_rel w a b.
Proof. exact (DSLP_rel_relDSLP (ASP_rel w) a b). Qed.

(** ** Monad dictionaries

     These are plain definitions, not global instances, so that they do not
     compete with other monads' [Monad] instances.  The corresponding
     [Eq1]/[MonadLawsE] dictionaries are [Eq1_Arrow]/[MonadLawsE_Arrow]
     at these stacks; [Examples/ArrowMonadExamples.v] checks the selected
     monad dictionaries against those laws. *)

Definition Monad_ASPostArr (S : Type) : Monad (ASPostArr S) :=
  @Monad_Arrow (stateArrT S optionASPArr) (Arrow_stateOptASP S)
    (ArrowApply_stateOptASP S) unit.

Definition Monad_DSLPostArr (S : Type) : Monad (DSLPostArr S) :=
  @Monad_Arrow (stateArrT S optionDSLPArr) (Arrow_stateOptDSLP S)
    (ArrowApply_stateOptDSLP S) unit.

(** ** Relational [ret] and [bind] on the concrete stacks

     Each is the generic [RelArrowCoherence] spec instantiated with the
     stack's presentation; [apply] closes the goal by conversion. *)

Lemma ASP_rel_ret {S A} (a : A) (i : unit) (s : S) r :
  ASP_rel (@ret _ (Monad_ASPostArr S) A a) (i, s) r <-> Some (a, s) = r.
Proof.
  apply (@rel_state_option_pure PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr ASP_rel_presentation
    S unit A (fun _ => a) i s r).
Qed.

Lemma ASP_rel_bind {S A B} (m : ASPostArr S A) (k : A -> ASPostArr S B)
    (s : S) r :
  ASP_rel (@bind _ (Monad_ASPostArr S) A B m k) (tt, s) r <->
  exists om, ASP_rel m (tt, s) om /\
    match om with
    | Some (a, t) => ASP_rel (k a) (tt, t) r
    | None => r = None
    end.
Proof.
  apply (@rel_state_option_bind PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr ASP_rel_presentation
    S unit A B m k tt s r).
Qed.

Lemma DSLP_rel_bind {S A B} (m : DSLPostArr S A) (k : A -> DSLPostArr S B)
    (s : S) r :
  DSLP_rel (@bind _ (Monad_DSLPostArr S) A B m k) (tt, s) r <->
  exists om, DSLP_rel m (tt, s) om /\
    match om with
    | Some (a, t) => DSLP_rel (k a) (tt, t) r
    | None => r = None
    end.
Proof.
  apply (@rel_state_option_bind PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr DSLP_rel_presentation
    S unit A B m k tt s r).
Qed.

(** ** Evaluators *)

Definition runASP {S A} (w : ASPostArr S A) (pre : S -> Prop)
  (r : option (A * S)) : Prop := getASP w (fun us => pre (snd us)) r.

Definition runDSLP {S A} (w : DSLPostArr S A) (pre : S -> Prop)
  (r : option (A * S)) : Prop := getDSLP w (fun us => pre (snd us)) r.

Lemma runASP_rel {S A} (w : ASPostArr S A) (pre : S -> Prop) r :
  runASP w pre r <-> exists s, pre s /\ ASP_rel w (tt, s) r.
Proof.
  unfold runASP. rewrite (ASP_normal_form w (fun us => pre (snd us)) r).
  split.
  - intros [us [Hus Hw]]. destruct us as [[] s]. exists s.
    split; [exact Hus | exact Hw].
  - intros [s [Hs Hw]]. exists (tt, s). split; [exact Hs | exact Hw].
Qed.

Lemma runDSLP_rel {S A} (w : DSLPostArr S A) (pre : S -> Prop) r :
  runDSLP w pre r <-> forall s, DSLP_rel w (tt, s) r -> pre s.
Proof.
  unfold runDSLP. rewrite (DSLP_normal_form w (fun us => pre (snd us)) r).
  split.
  - intros H s Hr. apply (H (tt, s)). exact Hr.
  - intros H [[] s] Hr. exact (H s Hr).
Qed.

Lemma runASP_bind {S A B} (m : ASPostArr S A) (k : A -> ASPostArr S B)
    (pre : S -> Prop) r :
  runASP (@bind _ (Monad_ASPostArr S) A B m k) pre r <->
  exists s om, pre s /\ ASP_rel m (tt, s) om /\
    match om with
    | Some (a, t) => ASP_rel (k a) (tt, t) r
    | None => r = None
    end.
Proof.
  rewrite runASP_rel.
  split.
  - intros [s [Hpre Hb]]. apply (proj1 (ASP_rel_bind m k s r)) in Hb.
    destruct Hb as [om [Hm Hk]]. exists s, om.
    split; [exact Hpre | split; [exact Hm | exact Hk]].
  - intros [s [om [Hs [Hm Hk]]]]. exists s. split; [exact Hs |].
    apply (proj2 (ASP_rel_bind m k s r)).
    exists om. split; [exact Hm | exact Hk].
Qed.

(** ** The conversion preserves [ret] and [bind] *)

Lemma asp_to_dslp_ret {S A} (a : A) :
  asp_to_dslp (@ret _ (Monad_ASPostArr S) A a) =
  @ret _ (Monad_DSLPostArr S) A a.
Proof.
  apply PureDSLPostArr_eq. intros Q r.
  change (getDSLP (asp_to_dslp (@ret _ (Monad_ASPostArr S) A a)) Q r <->
    getDSLP (@arr_pure (stateArrT S optionDSLPArr) (Arrow_stateOptDSLP S)
      unit A (fun _ => a)) Q r).
  rewrite asp_to_dslp_spec, stateOptDSLP_pure_spec.
  split.
  - intros H [] s Hr. apply H. apply (proj2 (ASP_rel_ret a tt s r)). exact Hr.
  - intros H [[] s] Hr. apply H. apply (proj1 (ASP_rel_ret a tt s r)). exact Hr.
Qed.

Lemma asp_to_dslp_bind {S A B} (m : ASPostArr S A) (k : A -> ASPostArr S B) :
  asp_to_dslp (@bind _ (Monad_ASPostArr S) A B m k) =
  @bind _ (Monad_DSLPostArr S) A B (asp_to_dslp m)
    (fun a => asp_to_dslp (k a)).
Proof.
  apply PureDSLPostArr_eq. intros Q r.
  assert (Hiff : forall p,
    ASP_rel (@bind _ (Monad_ASPostArr S) A B m k) p r <->
    DSLP_rel (@bind _ (Monad_DSLPostArr S) A B (asp_to_dslp m)
      (fun a => asp_to_dslp (k a))) p r).
  { intros [[] s]. rewrite ASP_rel_bind, DSLP_rel_bind.
    split.
    - intros [om [Hm Hk]]. exists om. split.
      + apply (proj2 (DSLP_rel_asp_to_dslp m (tt, s) om)). exact Hm.
      + destruct om as [[a t]|].
        * apply (proj2 (DSLP_rel_asp_to_dslp (k a) (tt, t) r)). exact Hk.
        * exact Hk.
    - intros [om [Hm Hk]]. exists om. split.
      + apply (proj1 (DSLP_rel_asp_to_dslp m (tt, s) om)). exact Hm.
      + destruct om as [[a t]|].
        * apply (proj1 (DSLP_rel_asp_to_dslp (k a) (tt, t) r)). exact Hk.
        * exact Hk. }
  rewrite asp_to_dslp_spec, (DSLP_normal_form
    (@bind _ (Monad_DSLPostArr S) A B (asp_to_dslp m)
      (fun a => asp_to_dslp (k a))) Q r).
  split; intros H p Hrel.
  - apply H. apply (proj2 (Hiff p)). exact Hrel.
  - apply H. apply (proj1 (Hiff p)). exact Hrel.
Qed.
