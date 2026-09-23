(** * The four WP observations of [rddivnd], assembled from algebras.

    [rddivnd R A = readerT R divnd A]  -->  [WRd R A = readerT R WPure A]

      - [divnd]   : COLLAPSED, by the four algebras of
                    [DivNonDet_WPure_Algebra.v];
      - [readerT] : PRESERVED, by [MMor_readerT].

    A read-only environment is threaded, never collapsed, so it offers no
    choice and adds no observations: this stack has the same four as
    [divnd] itself.  [obsDWPr_at] says exactly that -- at each environment
    the reader observation IS the pure one.

    This is the WP counterpart of [SP/RdDivNonDet_RdSPPure.v], which
    threads the reader through the SP observations the same way. *)

From ExtLib Require Import Monad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet RdDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import
  DivNonDet_WPure_Algebra.

Import MonadNotation.
Open Scope monad_scope.

Local Definition getNE_T {R A} (m : rddivndNE R A) : readerT R (optionT SetM) A :=
  RdDivNonDet.getNE m.
#[local] Coercion getNE_T : rddivndNE >-> readerT.

Section Observations.
  Variable R : Type.

  (** One lift, four times. *)
  Definition MMorRd_DWP  : MMor (rddivnd R) (WRd R) := MMor_readerT R MMor_DWP.
  Definition MMorRd_DWLP : MMor (rddivnd R) (WRd R) := MMor_readerT R MMor_DWLP.
  Definition MMorRd_AWP  : MMor (rddivnd R) (WRd R) := MMor_readerT R MMor_AWP.
  Definition MMorRd_AWLP : MMor (rddivnd R) (WRd R) := MMor_readerT R MMor_AWLP.

  Definition obsDWPr  {A} (m : rddivndNE R A) : WRd R A := mmor MMorRd_DWP (getNE m).
  Definition obsDWLPr {A} (m : rddivndNE R A) : WRd R A := mmor MMorRd_DWLP (getNE m).
  Definition obsAWPr  {A} (m : rddivndNE R A) : WRd R A := mmor MMorRd_AWP (getNE m).
  Definition obsAWLPr {A} (m : rddivndNE R A) : WRd R A := mmor MMorRd_AWLP (getNE m).

  (** ** The environment is threaded

      At each [r] the observation is the pure one of the program run at
      [r], by [eq_refl] -- which is what "the reader layer is preserved"
      means concretely. *)

  Lemma obsDWPr_at {A} (m : rddivndNE R A) (r : R) :
    runReaderT (obsDWPr m) r = obsDWPp (runReaderT m r).
  Proof. reflexivity. Qed.

  Lemma obsDWLPr_at {A} (m : rddivndNE R A) (r : R) :
    runReaderT (obsDWLPr m) r = obsDWLPp (runReaderT m r).
  Proof. reflexivity. Qed.

  Lemma obsAWPr_at {A} (m : rddivndNE R A) (r : R) :
    runReaderT (obsAWPr m) r = obsAWPp (runReaderT m r).
  Proof. reflexivity. Qed.

  Lemma obsAWLPr_at {A} (m : rddivndNE R A) (r : R) :
    runReaderT (obsAWLPr m) r = obsAWLPp (runReaderT m r).
  Proof. reflexivity. Qed.

  (** ** The morphism laws, for free *)

  Theorem obsDWPr_ret {A} (a : A) : eq1 (obsDWPr (ret a)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorRd_DWP) A a). Qed.
  Theorem obsDWPr_bind {A B} (x : rddivndNE R A) (f : A -> rddivndNE R B) :
    eq1 (obsDWPr (x >>= f)) (obsDWPr x >>= (fun a => obsDWPr (f a))).
  Proof. exact (mmor_bind (MMor := MMorRd_DWP) A B x f). Qed.

  Theorem obsDWLPr_ret {A} (a : A) : eq1 (obsDWLPr (ret a)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorRd_DWLP) A a). Qed.
  Theorem obsDWLPr_bind {A B} (x : rddivndNE R A) (f : A -> rddivndNE R B) :
    eq1 (obsDWLPr (x >>= f)) (obsDWLPr x >>= (fun a => obsDWLPr (f a))).
  Proof. exact (mmor_bind (MMor := MMorRd_DWLP) A B x f). Qed.

  Theorem obsAWPr_ret {A} (a : A) : eq1 (obsAWPr (ret a)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorRd_AWP) A a). Qed.
  Theorem obsAWPr_bind {A B} (x : rddivndNE R A) (f : A -> rddivndNE R B) :
    eq1 (obsAWPr (x >>= f)) (obsAWPr x >>= (fun a => obsAWPr (f a))).
  Proof. exact (mmor_bind (MMor := MMorRd_AWP) A B x f). Qed.

  Theorem obsAWLPr_ret {A} (a : A) : eq1 (obsAWLPr (ret a)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorRd_AWLP) A a). Qed.
  Theorem obsAWLPr_bind {A B} (x : rddivndNE R A) (f : A -> rddivndNE R B) :
    eq1 (obsAWLPr (x >>= f)) (obsAWLPr x >>= (fun a => obsAWLPr (f a))).
  Proof. exact (mmor_bind (MMor := MMorRd_AWLP) A B x f). Qed.

  (** ** [ask] observes as itself

      Reading the environment is a total, deterministic step, so every one
      of the four sends it to the same specification. *)

  Theorem obsDWPr_ask (r : R) (post : R -> Prop) :
    getWPure (runReaderT (obsDWPr (askNE R)) r) post <-> post r.
  Proof.
    rewrite obsDWPr_at. rewrite obsDWPp_get. split.
    - intro H. exact (H (Some r) eq_refl).
    - intros Hp [a|] Ho; cbn in Ho; [| discriminate Ho ].
      injection Ho as ->. exact Hp.
  Qed.

End Observations.

Arguments obsDWPr {R} {A}.
Arguments obsDWLPr {R} {A}.
Arguments obsAWPr {R} {A}.
Arguments obsAWLPr {R} {A}.
