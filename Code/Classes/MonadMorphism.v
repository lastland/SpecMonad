(** * Monad morphisms between monads with a chosen equivalence

    [σ : forall A, M A -> W A] is a monad morphism when it respects both
    monads' [eq1] and preserves [ret] and [bind] up to [W]'s [eq1].

    ITree's [Extra/Dijkstra/DijkstraMonad.MonadMorphism] is the special case
    of an effect observation into an ordered monad.  This record asks for no
    order on [W], so it also covers maps into monads that are not
    specification monads, and it asks the map to respect the source's [eq1],
    which composition needs. *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.

Record MonadMorphism {M W : Type -> Type} {MonadM : Monad M} {MonadW : Monad W}
  {Eq1M : Eq1 M} {Eq1W : Eq1 W} (σ : forall A, M A -> W A) : Prop := {
  mm_proper : forall A (x y : M A), eq1 x y -> eq1 (σ A x) (σ A y) ;
  mm_ret : forall A (a : A), eq1 (σ A (ret a)) (ret a) ;
  mm_bind : forall A B (x : M A) (k : A -> M B),
      eq1 (σ B (bind x k)) (bind (σ A x) (fun a => σ B (k a)))
}.

Arguments mm_proper {M W MonadM MonadW Eq1M Eq1W σ} _ {A} x y.
Arguments mm_ret {M W MonadM MonadW Eq1M Eq1W σ} _ {A} a.
Arguments mm_bind {M W MonadM MonadW Eq1M Eq1W σ} _ {A B} x k.

Theorem MonadMorphism_comp {M V W : Type -> Type}
  {MonadM : Monad M} {MonadV : Monad V} {MonadW : Monad W}
  {Eq1M : Eq1 M} {Eq1V : Eq1 V} {Eq1W : Eq1 W}
  {EqW : @Eq1Equivalence W MonadW Eq1W}
  (σ : forall A, M A -> V A) (τ : forall A, V A -> W A) :
  MonadMorphism σ -> MonadMorphism τ -> MonadMorphism (fun A x => τ A (σ A x)).
Proof.
  intros Hσ Hτ. constructor.
  - intros A x y Hxy. apply (mm_proper Hτ). exact (mm_proper Hσ x y Hxy).
  - intros A a. destruct (EqW A) as [_ _ Ht].
    exact (Ht _ _ _ (mm_proper Hτ _ _ (mm_ret Hσ a)) (mm_ret Hτ a)).
  - intros A B x k. destruct (EqW B) as [_ _ Ht].
    exact (Ht _ _ _ (mm_proper Hτ _ _ (mm_bind Hσ x k))
              (mm_bind Hτ (σ A x) (fun a => σ B (k a)))).
Qed.
