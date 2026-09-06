From Coq Require Import
  FunctionalExtensionality
  PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import
  Monad MonadLaws MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.

Import MonadNotation.
Open Scope monad_scope.

Section TransformerLaws.

  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {LawsM : @MonadLawsE M Eq1M MonadM}.

  #[global] Instance Eq1_optionT : Eq1 (optionT M) :=
    fun A x y => eq1 (unOptionT x) (unOptionT y).

  #[global] Instance Eq1Equivalence_optionT :
    @Eq1Equivalence (optionT M) _ Eq1_optionT.
  Proof.
    constructor; repeat intro; unfold eq1, Eq1_optionT in *.
    - reflexivity.
    - symmetry; assumption.
    - etransitivity; eassumption.
  Qed.

  #[global] Instance MonadLawsE_optionT :
    @MonadLawsE (optionT M) Eq1_optionT _.
  Proof.
    constructor.
    - intros A B f x. unfold eq1, Eq1_optionT. cbn.
      rewrite bind_ret_l. destruct (f x); reflexivity.
    - intros A x. unfold eq1, Eq1_optionT. cbn.
      transitivity (bind (unOptionT x) (fun y => ret y)).
      + apply Proper_bind; [reflexivity |].
        repeat red; intros. destruct a; reflexivity.
      + apply bind_ret_r.
    - intros A B C x f g. unfold eq1, Eq1_optionT. cbn.
      rewrite bind_bind. apply Proper_bind; [reflexivity |].
      intros. repeat red. destruct a.
      + reflexivity.
      + rewrite bind_ret_l. reflexivity.
    - repeat intro. unfold eq1, Eq1_optionT in *. cbn.
      apply Proper_bind; [exact H |].
      repeat red; intros. destruct a.
      + apply H0.
      + reflexivity.
  Qed.

End TransformerLaws.

Section StateTransformerLaws.

  Variable S : Type.
  Variable M : Type -> Type.
  Context {MonadM : Monad M}.
  Context {Eq1M : Eq1 M}.
  Context {Eq1EquivM : @Eq1Equivalence M MonadM Eq1M}.
  Context {LawsM : @MonadLawsE M Eq1M MonadM}.

  #[local] Existing Instance Monad_stateT.

  #[global] Instance Eq1_stateT : Eq1 (stateT S M) :=
    fun A x y => forall s, eq1 (runStateT x s) (runStateT y s).

  #[global] Instance Eq1Equivalence_stateT :
    @Eq1Equivalence (stateT S M) _ Eq1_stateT.
  Proof.
    constructor.
    - repeat intro. unfold eq1, Eq1_stateT in *. reflexivity.
    - repeat intro. unfold eq1, Eq1_stateT in *.
      symmetry. apply H.
    - repeat intro. unfold eq1, Eq1_stateT in *.
      etransitivity; [apply H | apply H0].
  Qed.

  #[global] Instance MonadLawsE_stateT :
    @MonadLawsE (stateT S M) Eq1_stateT _.
  Proof.
    constructor.
    - intros A B f x s. cbn. rewrite bind_ret_l. reflexivity.
    - intros A x s. cbn.
      transitivity (bind (runStateT x s) (fun y => ret y)).
      + apply Proper_bind; [reflexivity |].
        repeat red; intros. destruct a; reflexivity.
      + apply bind_ret_r.
    - intros A B C x f g s. cbn.
      rewrite bind_bind. apply Proper_bind; [reflexivity |].
      repeat red; intros. destruct a. reflexivity.
    - repeat intro. cbn. apply Proper_bind.
      + apply H.
      + repeat red; intros. destruct a. apply H0.
  Qed.

End StateTransformerLaws.

Definition SetM (A : Type) : Type := A -> Prop.

#[global] Instance Monad_SetM : Monad SetM := {
  ret := fun _ a x => x = a;
  bind := fun _ _ m k b => exists a, m a /\ k a b
}.

#[global] Instance Eq1_SetM : Eq1 SetM :=
  fun A => eq.

#[global] Instance Eq1Equivalence_SetM :
  @Eq1Equivalence SetM Monad_SetM Eq1_SetM.
Proof. constructor; typeclasses eauto. Qed.

#[global] Instance MonadLawsE_SetM :
  @MonadLawsE SetM Eq1_SetM Monad_SetM.
Proof.
  constructor.
  - intros A B f x. unfold eq1, Eq1_SetM. cbn.
    apply functional_extensionality; intro b.
    apply propositional_extensionality. sauto limit: 200.
  - intros A x. unfold eq1, Eq1_SetM. cbn.
    apply functional_extensionality; intro b.
    apply propositional_extensionality. sauto limit: 200.
  - intros A B C x f g. unfold eq1, Eq1_SetM. cbn.
    apply functional_extensionality; intro c.
    apply propositional_extensionality. sauto limit: 200.
  - intros A B x y Hxy f g Hfg.
    unfold eq1, Eq1_SetM in *. subst.
    apply functional_extensionality; intro b.
    apply propositional_extensionality.
    split; intros [a [Ha Hk]]; exists a; split; try exact Ha;
      [rewrite <- (Hfg a) | rewrite (Hfg a)]; exact Hk.
Qed.

Section NonDetItProg.

  Variable S : Type.

  Definition prog A := stateT S (optionT (optionT SetM)) A.

  #[local] Existing Instance Monad_stateT.

  Definition nditRet {A} (a : A) : prog A :=
    @ret (stateT _ _) _ _ a.

  Definition nditBind {A B}
    (m : prog A) (k : A -> prog B) : prog B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global] Instance Monad__nditprog : Monad prog := {
    ret := fun _ => @nditRet _;
    bind := fun _ _ => @nditBind _ _
  }.

  Definition nditGet : prog S :=
    @get _ (stateT _ _) _.

  Definition nditPut (s : S) : prog unit :=
    @put _ (stateT _ _) _ s.

  #[global] Instance MonadState__nditprog : MonadState S prog := {
    get := nditGet;
    put := nditPut
  }.

  #[local] Existing Instance OptionTError.

  Definition nditRaise {A} (_ : unit) : prog A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition nditCatch {A}
    (m : prog A) (c : unit -> prog A) : prog A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global] Instance MonadExc__nditprog : MonadExc unit prog := {
    raise := fun _ => nditRaise;
    catch := fun _ => nditCatch
  }.

  Definition nditOr {A} (m1 m2 : prog A) : prog A :=
    mkStateT (fun s =>
      @mkOptionT (optionT SetM) _ (
        @mkOptionT SetM _ (fun oa =>
          unOptionT (unOptionT (runStateT m1 s)) oa \/
          unOptionT (unOptionT (runStateT m2 s)) oa))).

  Definition nditSpin {A} : prog A :=
    mkStateT (fun _ =>
      @mkOptionT (optionT SetM) _ (
        @mkOptionT SetM _ (fun oa => oa = None))).

  Definition Eq1__nditprog : Eq1 prog :=
    Eq1_stateT S (optionT (optionT SetM)).

  Definition MonadLawsE__nditprog :
    @MonadLawsE prog Eq1__nditprog Monad__nditprog :=
    MonadLawsE_stateT S (optionT (optionT SetM)).

  Definition Eq1Equivalence_nditprog :
    @Eq1Equivalence prog Monad__nditprog Eq1__nditprog :=
    Eq1Equivalence_stateT S (optionT (optionT SetM)).

End NonDetItProg.

(** Generic operational lemma describing the outcomes of a [prog]
    bind in terms of the outcomes of its two components. Shared by all
    observation functions defined over [prog]. *)
Lemma outcomes_bind {S A B}
  (m : prog S A) (k : A -> prog S B) s ob :
  unOptionT (unOptionT (runStateT (m >>= k) s)) ob <->
  exists oa,
    unOptionT (unOptionT (runStateT m s)) oa /\
    match oa with
    | Some (Some (a, s')) =>
        unOptionT (unOptionT (runStateT (k a) s')) ob
    | Some None => ob = Some None
    | None => ob = None
    end.
Proof.
  cbn. split.
  - intros [oa [Hm Hk]]. exists oa. split; [exact Hm |].
    destruct oa as [[[a s']|]|]; cbn in *; exact Hk.
  - intros [oa [Hm Hk]]. exists oa. split; [exact Hm |].
    destruct oa as [[[a s']|]|]; cbn in *; exact Hk.
Qed.
