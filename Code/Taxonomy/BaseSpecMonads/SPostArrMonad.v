(** * Effect-observation helpers for the ASP and DSLP specification monads.

    The bridge reuses the canonical unary monad dictionaries and runners.
    Its relational return/bind formulas and unit-input conversion results
    support observations. Binary carriers and conversion live in [SPostArr]. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad RelArrowCoherence.
From Incorrectness.Classes Require Import OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPMonad DSLPMonad.
From Incorrectness.Taxonomy.Arrows Require Export SPostArr.
Import MonadNotation.

(** ** Monad dictionaries

     These are plain definitions, not global instances, so that they do not
     compete with other monads' [Monad] instances.  The corresponding
     [Eq1]/[MonadLawsE] dictionaries are [Eq1_Arrow]/[MonadLawsE_Arrow]
     at these stacks; [Tests/ArrowMonadInstances.v] checks the selected
     monad dictionaries against those laws. *)

Definition Monad_ASPostArr (S : Type) : Monad (ASPostArr S) :=
  ASPMonad.Monad_ASPStExc S.

Definition Monad_DSLPostArr (S : Type) : Monad (DSLPostArr S) :=
  DSLPMonad.Monad_DSLPStExc S.

(** ** Relational [ret] and [bind] on the concrete stacks

     [ret] reads only the base pure law [ASP_rel_pure] / [DSLP_rel_pure].
     Its function keeps [Some] outside the state-pair match, matching
     the option-over-base pure operation by conversion.  [bind]
     instantiates the generic [relE_bind] with the existing compatibility
     semantic dictionaries; conversion identifies the canonical monad bind. *)

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
  exact (@relE_bind PureASPostArr Arrow_PureASPostArr ArrowApply_PureASPostArr
    RelArrow_PureASPostArr RelArrowApply_PureASPostArr
    ArrowChoice_PureASPostArr RelArrowChoice_PureASPostArr
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
  exact (@relE_bind PureDSLPostArr Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr
    RelArrow_PureDSLPostArr RelArrowApply_PureDSLPostArr
    ArrowChoice_PureDSLPostArr RelArrowChoice_PureDSLPostArr
    S unit A B m k tt s r).
Qed.

(** ** Evaluators *)

Definition runASP {S A} (w : ASPostArr S A) (pre : S -> Prop)
  (r : option (A * S)) : Prop := ASPMonad.getASPStExc w pre r.

Definition runDSLP {S A} (w : DSLPostArr S A) (pre : S -> Prop)
  (r : option (A * S)) : Prop := DSLPMonad.getDSLPStExc w pre r.

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
