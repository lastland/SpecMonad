(** * The four WP observations of [stdivnd], assembled from algebras.

    [stdivnd S A = stateT S divnd A]  -->  [WSt S A = stateT S WPure A]

      - [divnd]  : COLLAPSED, by the four algebras of
                   [DivNonDet_WPure_Algebra.v];
      - [stateT] : PRESERVED, by [MMor_stateT].

    [StDivNonDet_WSt.v] defines the same four by writing each predicate
    transformer out, proving a [wpure_mono] lemma for each, and then
    proving [_ret] and [_bind] for each -- eight law proofs, all of the
    same shape.  Here the state layer is threaded ([obsDWPa_at]: at each
    initial state the observation IS the pure one) and the eight laws are
    citations.  The only proofs below are the four agreements with the
    hand-written definitions. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import
  StDivNonDet_WSt DivNonDet_WPure_Algebra.

Import TermSliceObsWP.
Import MonadNotation.
Open Scope monad_scope.

Section Observations.
  Variable S : Type.

  (** One lift, four times. *)
  Definition MMorSt_DWP  : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_DWP.
  Definition MMorSt_DWLP : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_DWLP.
  Definition MMorSt_AWP  : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_AWP.
  Definition MMorSt_AWLP : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_AWLP.

  Definition obsDWPa  {A} (m : stdivnd S A) : WSt S A := mmor MMorSt_DWP m.
  Definition obsDWLPa {A} (m : stdivnd S A) : WSt S A := mmor MMorSt_DWLP m.
  Definition obsAWPa  {A} (m : stdivnd S A) : WSt S A := mmor MMorSt_AWP m.
  Definition obsAWLPa {A} (m : stdivnd S A) : WSt S A := mmor MMorSt_AWLP m.

  (** ** The state is threaded

      At each initial state the observation is the PURE observation of the
      program run from that state, by [eq_refl].  That is what "the state
      layer is preserved" means concretely, and every fact below is this
      plus a fact about [divnd]. *)

  Lemma obsDWPa_at {A} (m : stdivnd S A) (s : S) :
    runStateT (obsDWPa m) s = obsDWPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsDWLPa_at {A} (m : stdivnd S A) (s : S) :
    runStateT (obsDWLPa m) s = obsDWLPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsAWPa_at {A} (m : stdivnd S A) (s : S) :
    runStateT (obsAWPa m) s = obsAWPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsAWLPa_at {A} (m : stdivnd S A) (s : S) :
    runStateT (obsAWLPa m) s = obsAWLPp (runStateT m s).
  Proof. reflexivity. Qed.

  (** ** The morphism laws, for free *)

  Theorem obsDWPa_ret {A} (a : A) : eq1 (obsDWPa (ret a : stdivnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_DWP) A a). Qed.
  Theorem obsDWPa_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDWPa (x >>= f)) (obsDWPa x >>= (fun a => obsDWPa (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_DWP) A B x f). Qed.

  Theorem obsDWLPa_ret {A} (a : A) : eq1 (obsDWLPa (ret a : stdivnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_DWLP) A a). Qed.
  Theorem obsDWLPa_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDWLPa (x >>= f)) (obsDWLPa x >>= (fun a => obsDWLPa (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_DWLP) A B x f). Qed.

  Theorem obsAWPa_ret {A} (a : A) : eq1 (obsAWPa (ret a : stdivnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_AWP) A a). Qed.
  Theorem obsAWPa_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsAWPa (x >>= f)) (obsAWPa x >>= (fun a => obsAWPa (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_AWP) A B x f). Qed.

  Theorem obsAWLPa_ret {A} (a : A) : eq1 (obsAWLPa (ret a : stdivnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_AWLP) A a). Qed.
  Theorem obsAWLPa_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsAWLPa (x >>= f)) (obsAWLPa x >>= (fun a => obsAWLPa (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_AWLP) A B x f). Qed.

  (** ** They are the hand-written observations

      All four, each one line after [_at] and the corresponding [divnd]
      characterisation: the same development, differently obtained. *)

  Theorem obsDWPa_is_obsDWP {A} (m : stdivndNE S A) (s : S) post :
    getWPure (runStateT (obsDWPa (getNE m)) s) post
    <-> getWPure (runStateT (obsDWP m) s) post.
  Proof. rewrite obsDWPa_at, obsDWPp_get. symmetry. apply obsDWP_unfold. Qed.

  Theorem obsDWLPa_is_obsDWLP {A} (m : stdivndNE S A) (s : S) post :
    getWPure (runStateT (obsDWLPa (getNE m)) s) post
    <-> getWPure (runStateT (obsDWLP m) s) post.
  Proof. rewrite obsDWLPa_at, obsDWLPp_get. symmetry. apply obsDWLP_unfold. Qed.

  Theorem obsAWPa_is_obsAWP {A} (m : stdivndNE S A) (s : S) post :
    getWPure (runStateT (obsAWPa (getNE m)) s) post
    <-> getWPure (runStateT (obsAWP m) s) post.
  Proof. rewrite obsAWPa_at, obsAWPp_get. symmetry. apply obsAWP_unfold. Qed.

  Theorem obsAWLPa_is_obsAWLP {A} (m : stdivndNE S A) (s : S) post :
    getWPure (runStateT (obsAWLPa (getNE m)) s) post
    <-> getWPure (runStateT (obsAWLP m) s) post.
  Proof. rewrite obsAWLPa_at, obsAWLPp_get. symmetry. apply obsAWLP_unfold. Qed.

End Observations.
