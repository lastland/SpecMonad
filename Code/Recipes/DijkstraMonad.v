From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadLaws.
From ITree Require Import Basics.Monad.
From ITree.Extra Require Import Dijkstra.DijkstraMonad.
From Incorrectness.Recipes Require Export DMRecipe.

Definition flip (polarity : Polarity) : Polarity :=
  match polarity with
  | Forward => Backward
  | Backward => Forward
  end.

Definition dualTruth {W : Type -> Type} {order : OrderM W}
  (truth : TruthOrder W order) : TruthOrder W (dualOrder order).
Proof.
  destruct truth as [trueW falseW polarity bounds].
  refine {| trueW := trueW;
            falseW := falseW;
            truthPolarity := flip polarity |}.
  destruct polarity; cbn in *; intros A w;
    specialize (bounds A w); tauto.
Defined.

Definition dualOrdered (W : Type -> Type)
  (MonadW : Monad W) (OrderW : OrderM W)
  (OrderedW : @OrderedMonad W MonadW OrderW)
  : @OrderedMonad W MonadW (dualOrder OrderW).
Proof.
  constructor.
  - intros A w. exact (@reflex W MonadW OrderW OrderedW A w).
  - intros A w1 w2 w3 H12 H23.
    exact (@trans W MonadW OrderW OrderedW A w3 w2 w1 H23 H12).
  - intros A B w1 w2 f1 f2 Hw Hf.
    exact (@monot W MonadW OrderW OrderedW A B w2 w1 f2 f1 Hw Hf).
Defined.

Class DMOps {M W : Type -> Type}
  (direction : Direction) (recipe : DMRecipe M W) := {
  dmCarrier : forall A, W A -> Type;
  dmRun : forall {A w}, dmCarrier A w -> M A;
  dmRet : forall {A} (a : A),
      dmCarrier A (@ret W (monadW M W recipe) A a);
  dmBind : forall {A B w} (m : dmCarrier A w)
      {kW : A -> W B} (k : forall a, dmCarrier B (kW a)),
      dmCarrier B (@bind W (monadW M W recipe) A B w kW)
}.

Definition DM {M W : Type -> Type}
  (direction : Direction) (recipe : DMRecipe M W)
  `{ops : @DMOps M W direction recipe} (A : Type) (w : W A) : Type :=
  dmCarrier A w.

Section DijkstraMonads.

  Context {M W : Type -> Type}.
  Variable recipe : DMRecipe M W.

  Local Definition overCarrier (A : Type) (w : W A) : Type :=
    @DijkstraMonad M W
      (dmOrder Over recipe) (theta recipe) A w.

  Local Definition underCarrier (A : Type) (w : W A) : Type :=
    @DijkstraMonad M W
      (dmOrder Under recipe) (theta recipe) A w.

  Definition underOrdered :
    @OrderedMonad W (monadW M W recipe)
      (dualOrder (orderW M W recipe)) :=
    dualOrdered W
      (monadW M W recipe)
      (orderW M W recipe)
      (orderedW M W recipe).

  Definition underTruth :
    TruthOrder W (dualOrder (orderW M W recipe)) :=
    dualTruth (truthOrder M W recipe).

  Local Definition runOver {A w} (m : overCarrier A w) : M A :=
    proj1_sig m.

  Local Definition runUnder {A w} (m : underCarrier A w) : M A :=
    proj1_sig m.

  Lemma overCondition {A} (w : W A) (m : M A) :
    @DijkstraProp M W (orderW M W recipe) (theta recipe) A w m <->
    orderW M W recipe A (theta recipe A m) w.
  Proof. reflexivity. Qed.

  Lemma underCondition {A} (w : W A) (m : M A) :
    @DijkstraProp M W (dualOrder (orderW M W recipe))
      (theta recipe) A w m <->
    orderW M W recipe A w (theta recipe A m).
  Proof. reflexivity. Qed.

  #[program] Local Definition mkOverRet {A} (a : A)
    : overCarrier A (@ret W (monadW M W recipe) A a) :=
    @ret M (monadM M W recipe) A a.
  Next Obligation.
    apply (eqLeW M W recipe).
    exact (@ret_pres M W
      (monadM M W recipe)
      (monadW M W recipe)
      (eqW M W recipe)
      (theta recipe)
      (thetaMorphism M W recipe) A a).
  Qed.

  #[program] Local Definition mkUnderRet {A} (a : A)
    : underCarrier A (@ret W (monadW M W recipe) A a) :=
    @ret M (monadM M W recipe) A a.
  Next Obligation.
    apply (eqLeW M W recipe).
    pose proof (eqEquivW M W recipe A).
    symmetry.
    exact (@ret_pres M W
      (monadM M W recipe)
      (monadW M W recipe)
      (eqW M W recipe)
      (theta recipe)
      (thetaMorphism M W recipe) A a).
  Qed.

  #[program] Local Definition mkOverBind {A B}
    {w : W A} (m : overCarrier A w)
    {kW : A -> W B}
    (k : forall a, overCarrier B (kW a))
    : overCarrier B (@bind W (monadW M W recipe) A B w kW) :=
    @bind M (monadM M W recipe) A B
      (runOver m) (fun a => runOver (k a)).
  Next Obligation.
    eapply (@trans W
      (monadW M W recipe)
      (orderW M W recipe)
      (orderedW M W recipe) B).
    - apply (eqLeW M W recipe).
      exact (@bind_pres M W
        (monadM M W recipe)
        (monadW M W recipe)
        (eqW M W recipe)
        (theta recipe)
        (thetaMorphism M W recipe)
        A B (runOver m) (fun a => runOver (k a))).
    - apply (@monot W
        (monadW M W recipe)
        (orderW M W recipe)
        (orderedW M W recipe) A B).
      + exact (proj2_sig m).
      + intro a. exact (proj2_sig (k a)).
  Qed.

  #[program] Local Definition mkUnderBind {A B}
    {w : W A} (m : underCarrier A w)
    {kW : A -> W B}
    (k : forall a, underCarrier B (kW a))
    : underCarrier B (@bind W (monadW M W recipe) A B w kW) :=
    @bind M (monadM M W recipe) A B
      (runUnder m) (fun a => runUnder (k a)).
  Next Obligation.
    eapply (@trans W
      (monadW M W recipe)
      (orderW M W recipe)
      (orderedW M W recipe) B).
    - apply (@monot W
        (monadW M W recipe)
        (orderW M W recipe)
        (orderedW M W recipe) A B).
      + exact (proj2_sig m).
      + intro a. exact (proj2_sig (k a)).
    - apply (eqLeW M W recipe).
      pose proof (eqEquivW M W recipe B).
      symmetry.
      exact (@bind_pres M W
        (monadM M W recipe)
        (monadW M W recipe)
        (eqW M W recipe)
        (theta recipe)
        (thetaMorphism M W recipe)
        A B (runUnder m) (fun a => runUnder (k a))).
  Qed.

  #[global] Instance overDM : @DMOps M W Over recipe.
  Proof.
    refine {| dmCarrier := overCarrier;
              dmRun := @runOver;
              dmRet := @mkOverRet;
              dmBind := @mkOverBind |}.
  Defined.

  #[global] Instance underDM : @DMOps M W Under recipe.
  Proof.
    refine {| dmCarrier := underCarrier;
              dmRun := @runUnder;
              dmRet := @mkUnderRet;
              dmBind := @mkUnderBind |}.
  Defined.

End DijkstraMonads.

Arguments DM {M W} direction recipe {ops} A w.
