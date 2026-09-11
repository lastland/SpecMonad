(** * Generic [Eq1] and [MonadLawsE] for ExtLib's monad transformers

    [optionT], [stateT] and [readerT], each proved once, parametrically in the
    base monad: every section takes [Monad] / [Eq1] / [Eq1Equivalence] /
    [MonadLawsE] for [M] as a [Context] and produces the corresponding
    instances for the transformed monad.  Nothing here mentions a particular
    computation or specification monad.

    Every stack in the development chains through these — [stdivitree] and the
    other computation monads, [WPure]'s [WSt] / [WStExc], [PredMonad]'s
    [ProgWPred], and the [*Rd] specification monads. *)

From ITree Require Import Basics.Monad.
From ExtLib Require Import StateMonad OptionMonad.
From ExtLib Require Import ReaderMonad.

(* ================================================================= *)
(** ** Generic [Eq1] and [MonadLawsE] for ExtLib's [optionT]         *)
(* ================================================================= *)

Section OptionT.

  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {MLM : @MonadLawsE M Eq1M MonadM}.

  (** Two [optionT M A] values are equivalent when their
      underlying [M (option A)] values are [eq1]-equivalent.
      For [M = itree void1] this is [eutt eq] at type [option A]. *)
  #[global]
  Instance Eq1_optionT : Eq1 (optionT M) :=
    fun A x y => eq1 (unOptionT x) (unOptionT y).

  #[global]
  Instance Eq1Equivalence_optionT
    : @Eq1Equivalence (optionT M) _ Eq1_optionT.
  Proof.
    constructor;
      repeat intro; unfold eq1, Eq1_optionT in *.
    - reflexivity.
    - symmetry; auto.
    - etransitivity; eauto.
  Qed.

  #[global]
  Instance MonadLawsE_optionT
    : @MonadLawsE (optionT M) Eq1_optionT _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros T U f x. unfold eq1, Eq1_optionT. cbn.
      rewrite bind_ret_l.
      destruct (f x); reflexivity.
    - (* bind_ret_r *)
      intros T x. unfold eq1, Eq1_optionT. cbn.
      transitivity (bind (unOptionT x) (fun y => ret y)).
      + apply Proper_bind. reflexivity.
        repeat red; intros. destruct a; reflexivity.
      + apply bind_ret_r.
    - (* bind_bind *)
      intros T U V x f g. unfold eq1, Eq1_optionT. cbn.
      rewrite bind_bind.
      apply Proper_bind. reflexivity.
      intros. repeat red. destruct a.
      + reflexivity.
      + rewrite bind_ret_l. reflexivity.
    - (* Proper_bind *)
      repeat intro. unfold eq1, Eq1_optionT in *. cbn.
      apply Proper_bind.
      + exact H.
      + repeat red. intros. destruct a.
        * apply H0.
        * reflexivity.
  Qed.

End OptionT.

(* ================================================================= *)
(** ** Generic [Eq1] and [MonadLawsE] for ExtLib's [stateT]          *)
(* ================================================================= *)

Section StateT.

  Variable St : Type.
  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {MLM : @MonadLawsE M Eq1M MonadM}.

  #[local] Existing Instance Monad_stateT.

  (** Two [stateT St M A] values are equivalent when, for every
      initial state [s], their underlying [M (A * St)] values are
      [eq1]-equivalent.  For the full [stdivitree] stack this unfolds to
      [forall s, eutt eq (... s) (... s)]. *)
  #[global]
  Instance Eq1_stateT : Eq1 (stateT St M) :=
    fun T x y => forall s, eq1 (runStateT x s) (runStateT y s).

  #[global]
  Instance Eq1Equivalence_stateT
    : @Eq1Equivalence (stateT St M) _ Eq1_stateT.
  Proof.
    constructor.
    - repeat intro; unfold eq1, Eq1_stateT in *.
      reflexivity.
    - repeat intro; unfold eq1, Eq1_stateT in *.
      symmetry. apply H.
    - repeat intro; unfold eq1, Eq1_stateT in *.
      etransitivity.
      + apply H.
      + apply H0.
  Qed.

  #[global]
  Instance MonadLawsE_stateT
    : @MonadLawsE (stateT St M) Eq1_stateT _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros T U f x s. cbn.
      rewrite bind_ret_l. reflexivity.
    - (* bind_ret_r *)
      intros T x s. cbn.
      transitivity (bind (runStateT x s) (fun y => ret y)).
      + apply Proper_bind. reflexivity.
        repeat red; intros. destruct a; reflexivity.
      + apply bind_ret_r.
    - (* bind_bind *)
      intros T U V x f g s. cbn.
      rewrite bind_bind.
      apply Proper_bind. reflexivity.
      repeat red; intros. destruct a. reflexivity.
    - (* Proper_bind *)
      repeat intro. cbn.
      apply Proper_bind.
      + apply H.
      + repeat red. intros. destruct a.
        apply H0.
  Qed.

End StateT.

(* ================================================================= *)
(** ** Generic [Eq1] and [MonadLawsE] for ExtLib's [readerT]         *)
(* ================================================================= *)

Section ReaderT.

  Variable R : Type.
  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {MLM : @MonadLawsE M Eq1M MonadM}.

  #[local] Existing Instance Monad_readerT.

  (** Two [readerT R M A] values are equivalent when, for every environment
      [r], their underlying [M A] values are [eq1]-equivalent.  Simpler than
      [Eq1_stateT]: the environment is threaded but never returned, so no
      pairing has to be destructed in the law proofs. *)
  #[global]
  Instance Eq1_readerT : Eq1 (readerT R M) :=
    fun T x y => forall r, eq1 (runReaderT x r) (runReaderT y r).

  #[global]
  Instance Eq1Equivalence_readerT
    : @Eq1Equivalence (readerT R M) _ Eq1_readerT.
  Proof.
    constructor.
    - repeat intro; unfold eq1, Eq1_readerT in *. reflexivity.
    - repeat intro; unfold eq1, Eq1_readerT in *. symmetry. apply H.
    - repeat intro; unfold eq1, Eq1_readerT in *.
      etransitivity; [ apply H | apply H0 ].
  Qed.

  #[global]
  Instance MonadLawsE_readerT
    : @MonadLawsE (readerT R M) Eq1_readerT _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros T U f x r. cbn. rewrite bind_ret_l. reflexivity.
    - (* bind_ret_r *)
      intros T x r. cbn. apply bind_ret_r.
    - (* bind_bind *)
      intros T U V x f g r. cbn. rewrite bind_bind. reflexivity.
    - (* Proper_bind *)
      repeat intro. cbn.
      apply Proper_bind; [ apply H | repeat red; intros; apply H0 ].
  Qed.

End ReaderT.
