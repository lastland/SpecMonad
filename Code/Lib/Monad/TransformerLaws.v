(** * Generic [Eq1] and [MonadLawsE] for ExtLib's monad transformers

    [optionT] and [stateT], each proved once, parametrically in the
    base monad: every section takes [Monad] / [Eq1] / [Eq1Equivalence] /
    [MonadLawsE] for [M] as a [Context] and produces the corresponding
    instances for the transformed monad.  Nothing here mentions a particular
    computation or specification monad.

    Every stack in the development chains through these — the computation
    monads, [WPure]'s [WSt] / [WStExc], and [PredMonad]'s [ProgWPred]. *)

From ITree Require Import Basics.Monad.
From ExtLib Require Import StateMonad OptionMonad.

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
(** ** Generic order lifting for ExtLib's [optionT]                  *)
(* ================================================================= *)

(** The base order [leM] is an EXPLICIT parameter rather than a
    typeclass: stacking [optionT] layers can never trigger recursive
    instance search.  Reflexivity and simultaneous bind monotonicity lift
    once, parametrically in the base monad; a double-[optionT] stack
    instantiates the result at each layer. *)

Section OptionTOrder.

  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Variable leM : forall A, M A -> M A -> Prop.
  Hypothesis leM_refl : forall A (m : M A), leM A m m.
  Hypothesis bind_mono : forall A B (m n : M A) (f g : A -> M B),
    leM A m n -> (forall a, leM B (f a) (g a)) ->
    leM B (bind m f) (bind n g).

  Definition ord_optionT {A} (m n : optionT M A) : Prop :=
    leM (option A) (unOptionT m) (unOptionT n).

  Lemma ord_optionT_refl {A} (m : optionT M A) : ord_optionT m m.
  Proof. apply leM_refl. Qed.

  Lemma bind_optionT_mono {A B} (m n : optionT M A) (f g : A -> optionT M B) :
    ord_optionT m n -> (forall a, ord_optionT (f a) (g a)) ->
    ord_optionT (bind m f) (bind n g).
  Proof.
    intros Hmn Hfg. unfold ord_optionT in *.
    cbn. apply bind_mono.
    - exact Hmn.
    - intros [a|]; [ apply Hfg | apply leM_refl ].
  Qed.

End OptionTOrder.

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
      [eq1]-equivalent. *)
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
(** ** Ordered lifts, for [Lib/Monad/OrderedMonad.v]                   *)
(* ================================================================= *)

(** Each transformer lifts an ordered monad pointwise.  Theorems, not
    instances: they are recursive in the base monad. *)

From Coq Require Import Relation_Definitions.
From Incorrectness.Lib.Monad Require Import OrderedMonad.

Section OrderedOptionT.
  Context {M : Type -> Type} {MonadM : Monad M} {Eq1M : Eq1 M}.
  Context (le : forall A, relation (M A)).

  Definition le_optionT : forall A, relation (optionT M A) :=
    fun A x y => le (option A) (unOptionT x) (unOptionT y).

  Theorem OrderedMonad_optionT :
    OrderedMonad M le ->
    @OrderedMonad (optionT M) _ (@Eq1_optionT M Eq1M) le_optionT.
  Proof.
    intros [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre (option A)) as [Hr Ht]. constructor.
      + intro x. apply Hr.
      + intros x y z. apply Ht.
    - intros A x y H. exact (Heq _ _ _ H).
    - intros A B m1 m2 Hm k1 k2 Hk. unfold le_optionT. cbn.
      apply Hbind; [ exact Hm |].
      intros [a|]; [ exact (Hk a) | apply (Hpre (option B)) ].
  Qed.
End OrderedOptionT.

Section OrderedStateT.
  Context {St : Type} {M : Type -> Type} {MonadM : Monad M} {Eq1M : Eq1 M}.
  Context (le : forall A, relation (M A)).

  #[local] Existing Instance Monad_stateT.

  Definition le_stateT : forall A, relation (stateT St M A) :=
    fun A x y => forall s, le (A * St)%type (runStateT x s) (runStateT y s).

  Theorem OrderedMonad_stateT :
    OrderedMonad M le ->
    @OrderedMonad (stateT St M) _ (@Eq1_stateT St M Eq1M) le_stateT.
  Proof.
    intros [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre (A * St)%type) as [Hr Ht]. constructor.
      + intros x s. apply Hr.
      + intros x y z H1 H2 s. exact (Ht _ _ _ (H1 s) (H2 s)).
    - intros A x y H s. exact (Heq _ _ _ (H s)).
    - intros A B m1 m2 Hm k1 k2 Hk s. cbn.
      apply Hbind; [ exact (Hm s) |].
      intros [a s']. exact (Hk a s').
  Qed.
End OrderedStateT.


(* ================================================================= *)
(** ** Monad-morphism lifts, for [Lib/Monad/OrderedMonad.v]            *)
(* ================================================================= *)

(** Each transformer acts on monad morphisms: a morphism between two base
    monads, applied under the transformer, is a morphism between the
    transformed monads.  Theorems, not instances: they are recursive in the
    base monad. *)

Section MorphismLifts.
  Context {M W : Type -> Type} {MonadM : Monad M} {MonadW : Monad W}
          {Eq1M : Eq1 M} {Eq1W : Eq1 W}
          {EqW : @Eq1Equivalence W MonadW Eq1W}
          {LawsW : @MonadLawsE W Eq1W MonadW}.

  #[local] Existing Instance Monad_stateT.

  Definition optionT_map (σ : forall A, M A -> W A)
    : forall A, optionT M A -> optionT W A :=
    fun A m => mkOptionT (σ (option A) (unOptionT m)).

  Theorem MonadMorphism_optionT (σ : forall A, M A -> W A) :
    @MonadMorphism M W MonadM MonadW Eq1M Eq1W σ ->
    @MonadMorphism (optionT M) (optionT W)
      (@Monad_optionT M MonadM) (@Monad_optionT W MonadW)
      (@Eq1_optionT M Eq1M) (@Eq1_optionT W Eq1W) (optionT_map σ).
  Proof.
    intro Hσ. constructor.
    - intros A x y Hxy. exact (mm_proper Hσ _ _ Hxy).
    - intros A a. exact (mm_ret Hσ (Some a)).
    - intros A B x k.
      change (eq1
                (σ (option B)
                   (bind (unOptionT x)
                      (fun o => match o with
                                | None => ret None
                                | Some a => unOptionT (k a)
                                end)))
                (bind (σ (option A) (unOptionT x))
                   (fun o => match o with
                             | None => ret None
                             | Some a => σ (option B) (unOptionT (k a))
                             end))).
      etransitivity; [ apply (mm_bind Hσ) |].
      apply Proper_bind; [ reflexivity |].
      intros [a|]; [ reflexivity | exact (mm_ret Hσ None) ].
  Qed.

  Definition stateT_map (St : Type) (σ : forall A, M A -> W A)
    : forall A, stateT St M A -> stateT St W A :=
    fun A m => mkStateT (fun s => σ (A * St)%type (runStateT m s)).

  Theorem MonadMorphism_stateT (St : Type) (σ : forall A, M A -> W A) :
    @MonadMorphism M W MonadM MonadW Eq1M Eq1W σ ->
    @MonadMorphism (stateT St M) (stateT St W)
      (@Monad_stateT St M MonadM) (@Monad_stateT St W MonadW)
      (@Eq1_stateT St M Eq1M) (@Eq1_stateT St W Eq1W) (stateT_map St σ).
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
End MorphismLifts.
