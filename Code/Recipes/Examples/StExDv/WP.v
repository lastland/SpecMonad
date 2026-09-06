From Coq Require Import
  FunctionalExtensionality
  PropExtensionality.
From ExtLib Require Import
  Monad MonadLaws
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import Program.

Import MonadNotation.
Open Scope monad_scope.

Definition PureWP (A : Type) : Type := (A -> Prop) -> Prop.

#[global] Instance Monad_PureWP : Monad PureWP := {
  ret := fun _ a p => p a;
  bind := fun _ _ m k p => m (fun a => k a p)
}.

#[global] Instance Eq1_PureWP : Eq1 PureWP :=
  fun A => eq.

#[global] Instance Eq1Equivalence_PureWP :
  @Eq1Equivalence PureWP Monad_PureWP Eq1_PureWP.
Proof. constructor; typeclasses eauto. Qed.

#[global] Instance MonadLawsE_PureWP :
  @MonadLawsE PureWP Eq1_PureWP Monad_PureWP.
Proof.
  constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A B x y Hxy f g Hfg.
    unfold eq1, Eq1_PureWP in *. subst.
    apply functional_extensionality; intro p. cbn. f_equal.
    apply functional_extensionality; intro a.
    rewrite (Hfg a). reflexivity.
Qed.

Section BaseProgWP.

  Variable S : Type.

  Definition BaseProgWP := stateT S (optionT PureWP).

  #[local] Existing Instance Monad_stateT.

  Definition baseWPRet {A} (a : A) : BaseProgWP A :=
    @ret (stateT _ _) _ _ a.

  Definition baseWPBind {A B}
    (m : BaseProgWP A) (k : A -> BaseProgWP B) : BaseProgWP B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global] Instance Monad__BaseProgWP : Monad BaseProgWP := {
    ret := fun _ => @baseWPRet _;
    bind := fun _ _ => @baseWPBind _ _
  }.

  Definition Eq1__BaseProgWP : Eq1 BaseProgWP :=
    Eq1_stateT S (optionT PureWP).

  Definition MonadLawsE__BaseProgWP :
    @MonadLawsE BaseProgWP Eq1__BaseProgWP Monad__BaseProgWP :=
    MonadLawsE_stateT S (optionT PureWP).

End BaseProgWP.

Record ProgWP (S A : Type) := {
  runProgWP : BaseProgWP S A;
  progWPMono :
    forall s (p q : option (A * S) -> Prop),
      (forall r, p r -> q r) ->
      unOptionT (runStateT runProgWP s) p ->
      unOptionT (runStateT runProgWP s) q
}.

Arguments runProgWP {S A} _.
Arguments progWPMono {S A} _ s p q _ _.

Section ProgWPMonad.

  Variable S : Type.

  #[program] Definition retProgWP {A} (a : A) : ProgWP S A := {|
    runProgWP :=
      mkStateT (fun s =>
        @mkOptionT PureWP _ (fun post => post (Some (a, s))))
  |}.

  Definition bindProgWP {A B}
    (m : ProgWP S A) (k : A -> ProgWP S B) : ProgWP S B.
  Proof.
    unshelve refine {|
      runProgWP :=
        mkStateT (fun s =>
          @mkOptionT PureWP _ (fun post =>
            unOptionT (runStateT (runProgWP m) s)
              (fun oa =>
                match oa with
                | Some (a, s') =>
                    unOptionT (runStateT (runProgWP (k a)) s') post
                | None => post None
                end)))
    |}.
    intros s p q H Hm.
    cbn in *.
    apply (progWPMono m s
      (fun oa =>
        match oa with
        | Some (a, s') => unOptionT (runStateT (runProgWP (k a)) s') p
        | None => p None
        end)
      (fun oa =>
        match oa with
        | Some (a, s') => unOptionT (runStateT (runProgWP (k a)) s') q
        | None => q None
        end)).
    - intros [[a s']|]; cbn.
      + apply (progWPMono (k a)); exact H.
      + apply H.
    - exact Hm.
  Defined.

  #[global] Instance Monad__ProgWP : Monad (ProgWP S) := {
    ret := fun _ => retProgWP;
    bind := fun _ _ => bindProgWP
  }.

  Definition Eq1__ProgWP : Eq1 (ProgWP S) :=
    fun A x y =>
      @eq1 (BaseProgWP S) (Eq1__BaseProgWP S) A (runProgWP x) (runProgWP y).

  #[global] Instance Eq1Equivalence_ProgWP :
    @Eq1Equivalence (ProgWP S) Monad__ProgWP Eq1__ProgWP.
  Proof.
    unfold Eq1Equivalence, Eq1__ProgWP, Eq1__BaseProgWP,
      Eq1_stateT, Eq1_optionT, Eq1_PureWP, eq1.
    intro A. constructor.
    - intros x s. reflexivity.
    - intros x y H s. symmetry. apply H.
    - intros x y z Hxy Hyz s. transitivity (unOptionT (runStateT (runProgWP y) s)).
      + apply Hxy.
      + apply Hyz.
  Qed.

  #[global] Instance MonadLawsE__ProgWP :
    @MonadLawsE (ProgWP S) Eq1__ProgWP Monad__ProgWP.
  Proof.
    constructor.
    - intros A B f x.
      unfold Eq1__ProgWP, Eq1__BaseProgWP, Eq1_stateT,
        Eq1_optionT, Eq1_PureWP, eq1.
      intro s. reflexivity.
    - intros A x.
      unfold Eq1__ProgWP, Eq1__BaseProgWP, Eq1_stateT,
        Eq1_optionT, Eq1_PureWP, eq1.
      intro s. apply functional_extensionality. intro post.
      apply propositional_extensionality. cbn.
      split; intro Hx.
      + apply (progWPMono x s
          (fun oa =>
            match oa with
            | Some (a, s') => post (Some (a, s'))
            | None => post None
            end) post).
        * intros [[a s']|]; cbn; intuition.
        * exact Hx.
      + apply (progWPMono x s post
          (fun oa =>
            match oa with
            | Some (a, s') => post (Some (a, s'))
            | None => post None
            end)).
        * intros [[a s']|]; cbn; intuition.
        * exact Hx.
    - intros A B C x f g.
      unfold Eq1__ProgWP, Eq1__BaseProgWP, Eq1_stateT,
        Eq1_optionT, Eq1_PureWP, eq1.
      intro s. reflexivity.
    - intros A B x y Hxy f g Hfg.
      unfold Eq1__ProgWP, Eq1__BaseProgWP, Eq1_stateT,
        Eq1_optionT, Eq1_PureWP, eq1 in *.
      intro s. apply functional_extensionality. intro post.
      apply propositional_extensionality. cbn in *.
      split; intro H.
      + apply (progWPMono y s
          (fun oa =>
            match oa with
            | Some (a, s') =>
                unOptionT (runStateT (runProgWP (f a)) s') post
            | None => post None
            end)
          (fun oa =>
            match oa with
            | Some (a, s') =>
                unOptionT (runStateT (runProgWP (g a)) s') post
            | None => post None
            end)).
        * intros [[a s']|]; cbn.
          -- rewrite (Hfg a s'). intuition.
          -- intuition.
        * rewrite <- (Hxy s). exact H.
      + apply (progWPMono x s
          (fun oa =>
            match oa with
            | Some (a, s') =>
                unOptionT (runStateT (runProgWP (g a)) s') post
            | None => post None
            end)
          (fun oa =>
            match oa with
            | Some (a, s') =>
                unOptionT (runStateT (runProgWP (f a)) s') post
            | None => post None
            end)).
        * intros [[a s']|]; cbn.
          -- rewrite <- (Hfg a s'). intuition.
          -- intuition.
        * rewrite (Hxy s). exact H.
  Qed.

  Definition wpLe : OrderM (ProgWP S) :=
    fun A x y =>
      forall s p,
        unOptionT (runStateT (runProgWP y) s) p ->
        unOptionT (runStateT (runProgWP x) s) p.

  #[global] Instance RefinementOrder_ProgWP :
    RefinementOrder (ProgWP S) := {
    refines := wpLe
  }.

  #[global] Instance OrderedMonad_ProgWP :
    @OrderedMonad (ProgWP S) Monad__ProgWP wpLe.
  Proof.
    constructor.
    - intros A w s p H. exact H.
    - intros A x y z Hxy Hyz s p Hx.
      exact (Hxy s p (Hyz s p Hx)).
    - intros A B x y f g Hxy Hfg s p Hx.
      cbn in Hx |- *.
      apply (progWPMono x s
        (fun oa =>
          match oa with
          | Some (a, s') => unOptionT (runStateT (runProgWP (g a)) s') p
          | None => p None
          end)
        (fun oa =>
          match oa with
          | Some (a, s') => unOptionT (runStateT (runProgWP (f a)) s') p
          | None => p None
          end)).
      + intros [[a s']|]; cbn.
        * apply (Hfg a s' p).
        * intros H. exact H.
      + apply (Hxy s _). exact Hx.
  Qed.

  Lemma eqLeWP {A} (x y : ProgWP S A) :
    @eq1 (ProgWP S) Eq1__ProgWP A x y -> wpLe A x y.
  Proof.
    unfold Eq1__ProgWP, Eq1__BaseProgWP, Eq1_stateT,
      Eq1_optionT, Eq1_PureWP, eq1, wpLe.
    intros H s p Hx. specialize (H s). cbn in H.
    rewrite H. exact Hx.
  Qed.

  #[program] Definition falseWP {A} : ProgWP S A := {|
    runProgWP := mkStateT (fun _ => @mkOptionT PureWP _ (fun _ => False))
  |}.

  #[program] Definition trueWP {A} : ProgWP S A := {|
    runProgWP := mkStateT (fun _ => @mkOptionT PureWP _ (fun _ => True))
  |}.

  Definition truthWP : TruthOrder (ProgWP S) wpLe.
  Proof.
    refine {| trueW := fun A => @trueWP A;
              falseW := fun A => @falseWP A;
              truthPolarity := Backward |}.
    split; intros s p H.
    - exact I.
    - contradiction.
  Defined.

End ProgWPMonad.

Section Recipe.

  Variable S : Type.
  Variable observation : EffectObs (prog S) (ProgWP S).
  Variable observationMorphism :
    @MonadMorphism (prog S) (ProgWP S)
      (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) observation.

  Local Definition makeWPDM : DMRecipe (prog S) (ProgWP S).
  Proof.
    refine {|
      monadM := Monad__nditprog S;
      eqM := Eq1__nditprog S;
      eqEquivM := Eq1Equivalence_nditprog S;
      lawsM := MonadLawsE__nditprog S;
      monadW := Monad__ProgWP S;
      eqW := Eq1__ProgWP S;
      eqEquivW := Eq1Equivalence_ProgWP S;
      lawsW := MonadLawsE__ProgWP S;
      orderW := wpLe S;
      orderedW := OrderedMonad_ProgWP S;
      eqLeW := @eqLeWP S;
      truthOrder := truthWP S;
      theta := observation;
      thetaMorphism := observationMorphism
    |}.
  Defined.

End Recipe.

Definition meetWP {S A} (x y : ProgWP S A) : ProgWP S A.
Proof.
  refine {|
    runProgWP :=
      mkStateT (fun s =>
        @mkOptionT PureWP _ (fun p =>
          unOptionT (runStateT (runProgWP x) s) p \/
          unOptionT (runStateT (runProgWP y) s) p))
  |}.
  intros s p q H [Hx | Hy].
  - left. eapply progWPMono; eauto.
  - right. eapply progWPMono; eauto.
Defined.

Definition joinWP {S A} (x y : ProgWP S A) : ProgWP S A.
Proof.
  refine {|
    runProgWP :=
      mkStateT (fun s =>
        @mkOptionT PureWP _ (fun p =>
          unOptionT (runStateT (runProgWP x) s) p /\
          unOptionT (runStateT (runProgWP y) s) p))
  |}.
  intros s p q H [Hx Hy]. split; eapply progWPMono; eauto.
Defined.

Definition logicWP (S : Type)
  (observation : EffectObs (prog S) (ProgWP S))
  (observationMorphism :
    @MonadMorphism (prog S) (ProgWP S)
      (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) observation)
  : Logic (makeWPDM S observation observationMorphism).
Proof.
  refine {| meetW := fun A => @meetWP S A;
            joinW := fun A => @joinWP S A |}.
  - intros A x y z.
    unfold makeWPDM, wpLe, meetWP; cbn. split.
    + intro H. split.
      * intros s p Hy. apply H. left. exact Hy.
      * intros s p Hz. apply H. right. exact Hz.
    + intros [Hy Hz] s p [H | H].
      * apply Hy. exact H.
      * apply Hz. exact H.
  - intros A x y z.
    unfold makeWPDM, wpLe, joinWP; cbn. split.
    + intro H. split.
      * intros s p Hz. exact (proj1 (H s p Hz)).
      * intros s p Hz. exact (proj2 (H s p Hz)).
    + intros [Hx Hy] s p Hz. split.
      * apply Hx. exact Hz.
      * apply Hy. exact Hz.
Defined.

Definition makeWPRecipe (S : Type)
  (observation : EffectObs (prog S) (ProgWP S))
  (observationMorphism :
    @MonadMorphism (prog S) (ProgWP S)
      (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) observation)
  : LogicRecipe (prog S) (ProgWP S) :=
  {| recipeDM := makeWPDM S observation observationMorphism;
     recipeLogic := logicWP S observation observationMorphism |}.

Lemma wpExt {S A} (x y : ProgWP S A) :
  (forall s p,
      unOptionT (runStateT (runProgWP x) s) p <->
      unOptionT (runStateT (runProgWP y) s) p) ->
  @eq1 (ProgWP S) (Eq1__ProgWP S) A x y.
Proof.
  unfold Eq1__ProgWP, Eq1__BaseProgWP, Eq1_stateT,
    Eq1_optionT, Eq1_PureWP, eq1.
  intros H s. apply functional_extensionality; intro p.
  apply propositional_extensionality. apply H.
Qed.
