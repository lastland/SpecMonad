From Incorrectness.Recipes Require Import DMRecipe.

Class Logic {M W : Type -> Type} (recipe : DMRecipe M W) := {
  meetW : forall A, W A -> W A -> W A;
  joinW : forall A, W A -> W A -> W A;
  meet_spec :
    forall A (x y z : W A),
      orderW M W recipe A x (meetW A y z) <->
      orderW M W recipe A x y /\ orderW M W recipe A x z;
  join_spec :
    forall A (x y z : W A),
      orderW M W recipe A (joinW A x y) z <->
      orderW M W recipe A x z /\ orderW M W recipe A y z
}.

Arguments meetW {M W recipe Logic} A _ _.
Arguments joinW {M W recipe Logic} A _ _.

Record LogicRecipe (M W : Type -> Type) := {
  recipeDM : DMRecipe M W;
  recipeLogic : Logic recipeDM
}.

Arguments recipeDM {M W} _.
Arguments recipeLogic {M W} _.

Definition opposite (direction : Direction) : Direction :=
  match direction with
  | Over => Under
  | Under => Over
  end.

Class ApproxOps {M W : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  (V : Type -> Type) := {
  approxRel : forall A, M A -> V A -> Prop
}.

Definition Approx {M W V : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  `{ops : @ApproxOps M W direction recipe V}
  {A : Type} (m : M A) (w : V A) : Prop :=
  approxRel A m w.

#[global] Instance nativeApprox {M W : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  : @ApproxOps M W direction recipe W | 10 := {
  approxRel :=
    fun A m w =>
      @DijkstraProp M W (dmOrder direction (recipeDM recipe))
        (theta (recipeDM recipe)) A w m
}.

Class SpecMap (W W' : Type -> Type) := {
  orderSpec : OrderM W';
  liftSpec : forall A, W A -> W' A;
  lowerSpec : forall A, W' A -> W A
}.

Arguments orderSpec {W W'} _ A _ _.
Arguments liftSpec {W W' SpecMap} A _.
Arguments lowerSpec {W W' SpecMap} A _.

Class ApproxGC {M W W' : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  (map : SpecMap W W') := {
  approx_gc :
    forall A (x : W A) (y : W' A),
      directedOrder direction (orderSpec map) A (liftSpec A x) y <->
      dmOrder direction (recipeDM recipe) A x (lowerSpec A y)
}.

#[global] Instance galoisApprox {M W W' : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  `{map : SpecMap W W'}
  `{gc : @ApproxGC M W W' direction recipe map}
  : @ApproxOps M W direction recipe W' | 20 := {
  approxRel :=
    fun A m w =>
      @DijkstraProp M W'
        (directedOrder direction (orderSpec map))
        (fun A m => liftSpec A (theta (recipeDM recipe) A m)) A w m
}.

Theorem approx_synonym {M W W' : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  `{map : SpecMap W W'}
  `{gc : @ApproxGC M W W' direction recipe map}
  {A : Type} (m : M A) (w : W' A) :
  @Approx M W W' direction recipe
    (galoisApprox direction recipe) A m w <->
  @Approx M W W direction recipe
    (nativeApprox direction recipe) A m (lowerSpec A w).
Proof.
  unfold Approx, DijkstraProp, dmOrder.
  exact (@approx_gc M W W' direction recipe map gc
    A (theta (recipeDM recipe) A m) w).
Qed.

Definition both {M W : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  {A : Type} (x y : W A) : W A :=
  match direction with
  | Over => @meetW M W (recipeDM recipe) (recipeLogic recipe) A x y
  | Under => @joinW M W (recipeDM recipe) (recipeLogic recipe) A x y
  end.

Definition Entails {M W : Type -> Type}
  (direction : Direction) (recipe : LogicRecipe M W)
  {A : Type} (x y : W A) : Prop :=
  match direction with
  | Over => orderW M W (recipeDM recipe) A x y
  | Under => orderW M W (recipeDM recipe) A y x
  end.

Section LogicLaws.

  Context {M W : Type -> Type}.
  Variable recipe : LogicRecipe M W.

  Theorem and_symmetry {A} (direction : Direction)
    (m : M A) (x y : W A) :
    Approx direction recipe m x /\ Approx direction recipe m y <->
    Approx direction recipe m (both direction recipe x y).
  Proof.
    destruct direction; cbn.
    - symmetry. apply (@meet_spec M W (recipeDM recipe) (recipeLogic recipe)).
    - symmetry. apply (@join_spec M W (recipeDM recipe) (recipeLogic recipe)).
  Qed.

  Theorem entails_symmetry {A} (direction : Direction) (x y : W A) :
    Entails direction recipe x y <->
    Entails (opposite direction) recipe y x.
  Proof. destruct direction; reflexivity. Qed.

  Theorem consequence {A} (direction : Direction)
    (m : M A) (x y : W A) :
    Entails direction recipe x y ->
    Approx direction recipe m x ->
    Approx direction recipe m y.
  Proof.
    destruct direction; cbn; intros Hxy Hx.
    - exact (@trans W
        (monadW M W (recipeDM recipe))
        (orderW M W (recipeDM recipe))
        (orderedW M W (recipeDM recipe)) A _ _ _ Hx Hxy).
    - exact (@trans W
        (monadW M W (recipeDM recipe))
        (orderW M W (recipeDM recipe))
        (orderedW M W (recipeDM recipe)) A _ _ _ Hxy Hx).
  Qed.

  Theorem agreement {A} (m : M A) (under over : W A) :
    Approx Under recipe m under ->
    Approx Over recipe m over ->
    orderW M W (recipeDM recipe) A under over.
  Proof.
    intros Hu Ho.
    exact (@trans W
      (monadW M W (recipeDM recipe))
      (orderW M W (recipeDM recipe))
      (orderedW M W (recipeDM recipe)) A _ _ _ Hu Ho).
  Qed.

End LogicLaws.

Arguments both {M W} direction recipe {A} x y.
Arguments Entails {M W} direction recipe {A} x y.
Arguments Approx {M W V} direction recipe {ops A} m w.
