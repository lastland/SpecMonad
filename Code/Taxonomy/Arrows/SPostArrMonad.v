(** * Effect-observation helpers for the ASP and DSLP specification monads.

    Minimal monad-facing layer for [Taxonomy/EffectObservations/SP]: the
    monad dictionaries of the arrow stacks, the relational readings of
    their [ret] and [bind] — [ret] read through the pure layers of the
    stack directly at the base pure law of [SPostArr], [bind] by
    instantiating [Classes.RelArrowCoherence.rel_state_option_bind_fields]
    with the five base relational operation laws — the angelic-to-demonic
    conversion with its operation preservation, and the evaluators over
    an initial-state precondition. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad RelArrowCoherence.
From Incorrectness.Classes Require Import OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Export SPostArr.
Import MonadNotation.

Local Obligation Tactic := idtac.

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
     at these stacks; [Tests/ArrowMonadInstances.v] checks the selected
     monad dictionaries against those laws. *)

Definition Monad_ASPostArr (S : Type) : Monad (ASPostArr S) :=
  @Monad_Arrow (stateArrT S optionASPArr) (Arrow_stateOptASP S)
    (ArrowApply_stateOptASP S) unit.

Definition Monad_DSLPostArr (S : Type) : Monad (DSLPostArr S) :=
  @Monad_Arrow (stateArrT S optionDSLPArr) (Arrow_stateOptDSLP S)
    (ArrowApply_stateOptDSLP S) unit.

(** ** Relational [ret] and [bind] on the concrete stacks

     [ret] reads only the base pure law [ASP_rel_pure] / [DSLP_rel_pure].
     Its function keeps [Some] outside the state-pair match, matching
     the option-over-base pure operation by conversion.  [bind]
     instantiates the generic [rel_state_option_bind_fields] with the
     stack's relation and the five base relational operation laws of
     [SPostArr]; [apply] closes the goal by conversion. *)

Lemma ASP_rel_ret {S A} (a : A) (i : unit) (s : S) r :
  ASP_rel (@ret _ (Monad_ASPostArr S) A a) (i, s) r <-> Some (a, s) = r.
Proof.
  exact (ASP_rel_pure (fun p => Some ((fun '(_, s) => (a, s)) p)) (i, s) r).
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
  apply (@rel_state_option_bind_fields PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr
    (@ASP_rel) (@ASP_rel_pure) (@ASP_rel_comp)
    (@ASP_rel_first) (@ASP_rel_left) (@ASP_rel_app)
    S unit A B m k tt s r).
Qed.

Lemma DSLP_rel_ret {S A} (a : A) (i : unit) (s : S) r :
  DSLP_rel (@ret _ (Monad_DSLPostArr S) A a) (i, s) r <-> Some (a, s) = r.
Proof.
  exact (DSLP_rel_pure (fun p => Some ((fun '(_, s) => (a, s)) p)) (i, s) r).
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
  apply (@rel_state_option_bind_fields PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr
    (@DSLP_rel) (@DSLP_rel_pure) (@DSLP_rel_comp)
    (@DSLP_rel_first) (@DSLP_rel_left) (@DSLP_rel_app)
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
  rewrite runASP_rel. split.
  - intros [s [Hs Hb]]. rewrite ASP_rel_bind in Hb.
    destruct Hb as [om [Hm Hk]]. exists s, om.
    split; [exact Hs | split; [exact Hm | exact Hk]].
  - intros [s [om [Hs [Hm Hk]]]]. exists s. split; [exact Hs |].
    apply (proj2 (ASP_rel_bind m k s r)).
    exists om. split; [exact Hm | exact Hk].
Qed.

(** ** The conversion preserves [ret] and [bind]

     Both proofs go through the relational extensionality of the DSLP
     carrier and the relational readings of the arrow-derived [ret] and
     [bind]; the angelic-to-demonic dictionary transports each side by
     [DSLP_rel_asp_to_dslp]. *)

Lemma asp_to_dslp_ret {S A} (a : A) :
  asp_to_dslp (@ret _ (Monad_ASPostArr S) A a) =
  @ret _ (Monad_DSLPostArr S) A a.
Proof.
  apply DSLP_rel_ext. intros [[] s] r.
  rewrite (DSLP_rel_asp_to_dslp (@ret _ (Monad_ASPostArr S) A a) (tt, s) r).
  rewrite ASP_rel_ret, DSLP_rel_ret. reflexivity.
Qed.

Lemma asp_to_dslp_bind {S A B} (m : ASPostArr S A) (k : A -> ASPostArr S B) :
  asp_to_dslp (@bind _ (Monad_ASPostArr S) A B m k) =
  @bind _ (Monad_DSLPostArr S) A B (asp_to_dslp m)
    (fun a => asp_to_dslp (k a)).
Proof.
  apply DSLP_rel_ext. intros [[] s] r.
  rewrite (DSLP_rel_asp_to_dslp (@bind _ (Monad_ASPostArr S) A B m k) (tt, s) r).
  rewrite ASP_rel_bind, DSLP_rel_bind.
  split.
  - intros [om [Hm Hk]]. exists om. split.
    + exact (proj2 (DSLP_rel_asp_to_dslp m (tt, s) om) Hm).
    + destruct om as [[a t]|].
      * exact (proj2 (DSLP_rel_asp_to_dslp (k a) (tt, t) r) Hk).
      * exact Hk.
  - intros [om [Hm Hk]]. exists om. split.
    + exact (proj1 (DSLP_rel_asp_to_dslp m (tt, s) om) Hm).
    + destruct om as [[a t]|].
      * exact (proj1 (DSLP_rel_asp_to_dslp (k a) (tt, t) r) Hk).
      * exact Hk.
Qed.
