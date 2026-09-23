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

From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet StDivExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import
  StDivExcNonDet_WStExc DivNonDet_WPure_Algebra.

Import MonadNotation.
Open Scope monad_scope.

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

  Definition obsDWPx  {A} (m : stdivexcnd S A) : WStExc S A := mmor MMorX_DWP m.
  Definition obsDWLPx {A} (m : stdivexcnd S A) : WStExc S A := mmor MMorX_DWLP m.
  Definition obsAWPx  {A} (m : stdivexcnd S A) : WStExc S A := mmor MMorX_AWP m.
  Definition obsAWLPx {A} (m : stdivexcnd S A) : WStExc S A := mmor MMorX_AWLP m.

  (** ** Both preserved layers are threaded

      Strip the state and the exception layer from both sides and what is
      left is the PURE observation -- by [eq_refl], as for the reader and
      state stacks.  The postcondition type [option (A * S) -> Prop] is
      where the preserved exception layer shows up. *)

  Lemma obsDWPx_at {A} (m : stdivexcnd S A) (s : S) :
    unOptionT (runStateT (obsDWPx m) s) = obsDWPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsDWLPx_at {A} (m : stdivexcnd S A) (s : S) :
    unOptionT (runStateT (obsDWLPx m) s) = obsDWLPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsAWPx_at {A} (m : stdivexcnd S A) (s : S) :
    unOptionT (runStateT (obsAWPx m) s) = obsAWPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  Lemma obsAWLPx_at {A} (m : stdivexcnd S A) (s : S) :
    unOptionT (runStateT (obsAWLPx m) s) = obsAWLPp (unOptionT (runStateT m s)).
  Proof. reflexivity. Qed.

  (** ** The morphism laws, for free *)

  Theorem obsDWPx_ret {A} (a : A) :
    eq1 (obsDWPx (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_DWP) A a). Qed.
  Theorem obsDWPx_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsDWPx (x >>= f)) (obsDWPx x >>= (fun a => obsDWPx (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_DWP) A B x f). Qed.

  Theorem obsDWLPx_ret {A} (a : A) :
    eq1 (obsDWLPx (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_DWLP) A a). Qed.
  Theorem obsDWLPx_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsDWLPx (x >>= f)) (obsDWLPx x >>= (fun a => obsDWLPx (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_DWLP) A B x f). Qed.

  Theorem obsAWPx_ret {A} (a : A) :
    eq1 (obsAWPx (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_AWP) A a). Qed.
  Theorem obsAWPx_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsAWPx (x >>= f)) (obsAWPx x >>= (fun a => obsAWPx (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_AWP) A B x f). Qed.

  Theorem obsAWLPx_ret {A} (a : A) :
    eq1 (obsAWLPx (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorX_AWLP) A a). Qed.
  Theorem obsAWLPx_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsAWLPx (x >>= f)) (obsAWLPx x >>= (fun a => obsAWLPx (f a))).
  Proof. exact (mmor_bind (MMor := MMorX_AWLP) A B x f). Qed.

  (** ** They are the hand-written observations *)

  Theorem obsDWPx_is_obsDWP {A} (m : stdivexcnd S A) (s : S) post :
    getWPure (unOptionT (runStateT (obsDWPx m) s)) post
    <-> getWPure (unOptionT (runStateT (obsDWP m) s)) post.
  Proof. rewrite obsDWPx_at, obsDWPp_get. symmetry. apply obsDWP_unfold. Qed.

  Theorem obsDWLPx_is_obsDWLP {A} (m : stdivexcnd S A) (s : S) post :
    getWPure (unOptionT (runStateT (obsDWLPx m) s)) post
    <-> getWPure (unOptionT (runStateT (obsDWLP m) s)) post.
  Proof. rewrite obsDWLPx_at, obsDWLPp_get. symmetry. apply obsDWLP_unfold. Qed.

  Theorem obsAWPx_is_obsAWP {A} (m : stdivexcnd S A) (s : S) post :
    getWPure (unOptionT (runStateT (obsAWPx m) s)) post
    <-> getWPure (unOptionT (runStateT (obsAWP m) s)) post.
  Proof. rewrite obsAWPx_at, obsAWPp_get. symmetry. apply obsAWP_unfold. Qed.

  Theorem obsAWLPx_is_obsAWLP {A} (m : stdivexcnd S A) (s : S) post :
    getWPure (unOptionT (runStateT (obsAWLPx m) s)) post
    <-> getWPure (unOptionT (runStateT (obsAWLP m) s)) post.
  Proof. rewrite obsAWLPx_at, obsAWLPp_get. symmetry. apply obsAWLP_unfold. Qed.

End Observations.
