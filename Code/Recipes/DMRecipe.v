From ExtLib Require Import Monad MonadLaws.
From ITree Require Import Basics.Monad.
From ITree.Extra Require Export Dijkstra.DijkstraMonad.

Definition dualOrder {W : Type -> Type} (order : OrderM W) : OrderM W :=
  fun A x y => order A y x.

Inductive Direction :=
| Over
| Under.

Definition directedOrder {W : Type -> Type}
  (direction : Direction) (order : OrderM W) : OrderM W :=
  match direction with
  | Over => order
  | Under => dualOrder order
  end.

(** Forward transformers use implication order; backward transformers use
    reverse implication order.  Consequently their logical bounds swap. *)
Inductive Polarity :=
| Forward
| Backward.

Record TruthOrder (W : Type -> Type) (order : OrderM W) := {
  trueW : forall A, W A;
  falseW : forall A, W A;
  truthPolarity : Polarity;
  truthBounds :
    match truthPolarity with
    | Forward =>
        forall A (w : W A),
          order A (falseW A) w /\ order A w (trueW A)
    | Backward =>
        forall A (w : W A),
          order A (trueW A) w /\ order A w (falseW A)
    end
}.

Arguments trueW {W order} _ A.
Arguments falseW {W order} _ A.
Arguments truthPolarity {W order} _.
Arguments truthBounds {W order} _.

Record DMRecipe (M W : Type -> Type) := {
  monadM : Monad M;
  eqM : Eq1 M;
  eqEquivM : @Eq1Equivalence M monadM eqM;
  lawsM : @MonadLawsE M eqM monadM;

  monadW : Monad W;
  eqW : Eq1 W;
  eqEquivW : @Eq1Equivalence W monadW eqW;
  lawsW : @MonadLawsE W eqW monadW;

  orderW : OrderM W;
  orderedW : @OrderedMonad W monadW orderW;
  eqLeW :
    forall A (x y : W A),
      @eq1 W eqW A x y -> orderW A x y;
  truthOrder : TruthOrder W orderW;

  theta : EffectObs M W;
  thetaMorphism : @MonadMorphism M W monadM monadW eqW theta
}.

Arguments theta {M W} _ _ _.

Definition dmOrder {M W : Type -> Type}
  (direction : Direction) (recipe : DMRecipe M W)
  : OrderM W :=
  directedOrder direction (orderW M W recipe).
