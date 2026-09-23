(** * The four SP observations of [rddivnd], assembled from its denotation.

    [rddivnd R A = readerT R divnd A], and the environment is THREADED
    rather than absorbed: it stays a [readerT] on the specification side,
    exactly as on the WP side ([WP/RdDivNonDet_WRd_Algebra.v]).  So there
    is no new denotation to supply -- [PureRel_divnd] of
    [DivNonDet_SPure_Rel.v] is reused environment by environment, and each
    [_at] lemma below says so by [eq_refl].

    A threaded layer contributes no choices, so this stack has the same
    four observations as [divnd] itself and no more.

    The alternative reading, where the precondition ranges over SETS of
    environments, is a genuinely different observation -- it couples the
    environments the way a shared [S -> Prop] couples initial states --
    and nothing here covers it. *)

From ExtLib Require Import Monad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet RdDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad SPRelDenote.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  DivNonDet_SPure_Rel.

Import MonadNotation.
Open Scope monad_scope.

Section RdObservations.
  Variable R : Type.

  #[local] Existing Instance Monad_readerT.
  #[local] Existing Instance Eq1_readerT.

  (** The reader lift of each of the four: the specification keeps the
      environment the computation reads. *)

  Definition obsASPr {A} (m : rddivnd R A) : readerT R ASP A :=
    mkReaderT (fun r => obsASP (runReaderT m r)).
  Definition obsDSLPr {A} (m : rddivnd R A) : readerT R DSLP A :=
    mkReaderT (fun r => obsDSLP (runReaderT m r)).
  Definition obsDSPr {A} (m : rddivnd R A) : readerT R DSP A :=
    mkReaderT (fun r => obsDSP (runReaderT m r)).
  Definition obsASLPr {A} (m : rddivnd R A) : readerT R ASLP A :=
    mkReaderT (fun r => obsASLP (runReaderT m r)).

  (** ** The environment is threaded

      At each [r] the observation IS the pure one of the program run at
      [r], by [eq_refl]. *)

  Lemma obsASPr_at {A} (m : rddivnd R A) (r : R) :
    runReaderT (obsASPr m) r = obsASP (runReaderT m r).
  Proof. reflexivity. Qed.

  Lemma obsDSLPr_at {A} (m : rddivnd R A) (r : R) :
    runReaderT (obsDSLPr m) r = obsDSLP (runReaderT m r).
  Proof. reflexivity. Qed.

  Lemma obsDSPr_at {A} (m : rddivnd R A) (r : R) :
    runReaderT (obsDSPr m) r = obsDSP (runReaderT m r).
  Proof. reflexivity. Qed.

  Lemma obsASLPr_at {A} (m : rddivnd R A) (r : R) :
    runReaderT (obsASLPr m) r = obsASLP (runReaderT m r).
  Proof. reflexivity. Qed.

  (** ** The readings, environment by environment *)

  Lemma getASP_obsASPr {A} (m : rddivnd R A) (r : R) p a :
    getASP (runReaderT (obsASPr m) r) p a
    <-> (p /\ unOptionT (runReaderT m r) (Some a)).
  Proof. exact (getASP_obsASP (runReaderT m r) p a). Qed.

  Lemma getDSLP_obsDSLPr {A} (m : rddivnd R A) (r : R) p a :
    getDSLP (runReaderT (obsDSLPr m) r) p a
    <-> (unOptionT (runReaderT m r) (Some a) -> p).
  Proof. exact (getDSLP_obsDSLP (runReaderT m r) p a). Qed.

  Lemma getDSP_obsDSPr {A} (m : rddivnd R A) (r : R) p a :
    getDSPPure (runReaderT (obsDSPr m) r) p a
    <-> ((p /\ unOptionT (runReaderT m r) (Some a))
         /\ (unOptionT (runReaderT m r) (Some a) -> p)).
  Proof. exact (getDSP_obsDSP (runReaderT m r) p a). Qed.

  Lemma getASLP_obsASLPr {A} (m : rddivnd R A) (r : R) p a :
    getASLPPure (runReaderT (obsASLPr m) r) p a
    <-> ((p /\ unOptionT (runReaderT m r) (Some a))
         \/ (unOptionT (runReaderT m r) (Some a) -> p)).
  Proof. exact (getASLP_obsASLP (runReaderT m r) p a). Qed.

  (** ** The morphism laws, for free

      Each is the pure law at every environment: the [readerT] instances of
      [TransformerLaws.v] make [eq1] pointwise in [r]. *)

  Theorem obsASPr_ret {A} (a : A) : eq1 (obsASPr (ret a)) (ret a).
  Proof. intro r. exact (obsASP_ret a). Qed.
  Theorem obsASPr_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsASPr (x >>= f)) (obsASPr x >>= (fun a => obsASPr (f a))).
  Proof. intro r. exact (obsASP_bind (runReaderT x r) (fun a => runReaderT (f a) r)). Qed.

  Theorem obsDSLPr_ret {A} (a : A) : eq1 (obsDSLPr (ret a)) (ret a).
  Proof. intro r. exact (obsDSLP_ret a). Qed.
  Theorem obsDSLPr_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsDSLPr (x >>= f)) (obsDSLPr x >>= (fun a => obsDSLPr (f a))).
  Proof. intro r. exact (obsDSLP_bind (runReaderT x r) (fun a => runReaderT (f a) r)). Qed.

  Theorem obsDSPr_ret {A} (a : A) : eq1 (obsDSPr (ret a)) (ret a).
  Proof. intro r. exact (obsDSP_ret a). Qed.
  Theorem obsDSPr_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsDSPr (x >>= f)) (obsDSPr x >>= (fun a => obsDSPr (f a))).
  Proof. intro r. exact (obsDSP_bind (runReaderT x r) (fun a => runReaderT (f a) r)). Qed.

  Theorem obsASLPr_ret {A} (a : A) : eq1 (obsASLPr (ret a)) (ret a).
  Proof. intro r. exact (obsASLP_ret a). Qed.
  Theorem obsASLPr_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsASLPr (x >>= f)) (obsASLPr x >>= (fun a => obsASLPr (f a))).
  Proof. intro r. exact (obsASLP_bind (runReaderT x r) (fun a => runReaderT (f a) r)). Qed.

  (** ** [ask] observes as itself, and the slice is blind to divergence *)

  Lemma obsASP_askD (r : R) p (a : R) :
    getASP (runReaderT (obsASPr (askD R)) r) p a <-> (p /\ a = r).
  Proof.
    rewrite getASP_obsASPr. split.
    - intros [Hp Hr]. split; [ exact Hp |]. cbn in Hr. congruence.
    - intros [Hp ->]. split; [ exact Hp | reflexivity ].
  Qed.

  Lemma obsASPr_divergeD {A} (r : R) p (a : A) :
    ~ getASP (runReaderT (obsASPr (divergeD : rddivnd R A)) r) p a.
  Proof.
    rewrite getASP_obsASPr. intros [_ Hr]. cbn in Hr. congruence.
  Qed.

End RdObservations.

Arguments obsASPr  {R} {A}.
Arguments obsDSLPr {R} {A}.
Arguments obsDSPr  {R} {A}.
Arguments obsASLPr {R} {A}.
