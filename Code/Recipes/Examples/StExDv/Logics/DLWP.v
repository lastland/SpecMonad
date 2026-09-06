From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program WP PrePost Examples.

Import MonadNotation.
Open Scope monad_scope.
Open Scope refinement_scope.

Definition obsDLWP {S A} (m : prog S A) : BaseProgWP S A :=
  mkStateT (fun s =>
    @mkOptionT PureWP _ (fun post =>
      forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
        match oa with
        | Some r => post r
        | None => True
        end)).

Lemma obsDLWP_monotonic {S A} (m : prog S A) :
  forall s (p q : option (A * S) -> Prop),
    (forall r, p r -> q r) ->
    unOptionT (runStateT (obsDLWP m) s) p ->
    unOptionT (runStateT (obsDLWP m) s) q.
Proof.
  intros s p q H Hp oa Hoa. specialize (Hp oa Hoa).
  destruct oa as [r|]; [exact (H r Hp) | exact I].
Qed.

Lemma obsDLWP_unfold {S A} (m : prog S A) s post :
  unOptionT (runStateT (obsDLWP m) s) post <->
  forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
    match oa with Some r => post r | None => True end.
Proof. reflexivity. Qed.

Lemma obsDLWP_bind {S A B}
  (m : prog S A) (k : A -> prog S B) s post :
  unOptionT (runStateT (obsDLWP (m >>= k)) s) post <->
  unOptionT (runStateT (obsDLWP m) s)
    (fun r =>
      match r with
      | Some (a, s') => unOptionT (runStateT (obsDLWP (k a)) s') post
      | None => post None
      end).
Proof.
  rewrite (obsDLWP_unfold (m >>= k)), (obsDLWP_unfold m).
  setoid_rewrite outcomes_bind. split.
  - intros H oa Hoa. destruct oa as [[[a s']|]|].
    + cbn. intros ob Hob.
      apply H. exists (Some (Some (a, s'))). auto.
    + apply (H (Some None)). exists (Some None). auto.
    + exact I.
  - intros H ob [oa [Hoa Hk]]. specialize (H oa Hoa).
    destruct oa as [[[a s']|]|].
    + cbn in H. exact (H ob Hk).
    + subst ob. exact H.
    + subst ob. exact I.
Qed.

Definition dlwpObs {S A} (m : prog S A) : ProgWP S A :=
  {| runProgWP := obsDLWP m;
     progWPMono := @obsDLWP_monotonic S A m |}.

#[global] Instance dlwpMorphism (S : Type) :
  @MonadMorphism (prog S) (ProgWP S)
    (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) (@dlwpObs S).
Proof.
  constructor.
  - intros A a. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (obsDLWP (@nditRet S A a)) s) post <->
       unOptionT
         (runStateT (runProgWP (@retProgWP S A a)) s) post).
    cbv. split.
    + intro H. exact (H (Some (Some (a, s))) eq_refl).
    + intros H oa Hoa. subst oa. exact H.
  - intros A B m f. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (runProgWP (dlwpObs (bind m f))) s) post <->
       unOptionT
         (runStateT
           (runProgWP
             (@bindProgWP S A B (dlwpObs m)
               (fun a => dlwpObs (f a)))) s) post).
    unfold dlwpObs.
    cbn [runProgWP bindProgWP Monad__BaseProgWP baseWPBind].
    rewrite obsDLWP_bind.
    cbv [Monad__BaseProgWP baseWPBind Monad_stateT Monad_optionT
      Monad_PureWP].
    reflexivity.
Qed.

Definition dlwpRecipe (S : Type) : LogicRecipe (prog S) (ProgWP S) :=
  makeWPRecipe S (@dlwpObs S) (dlwpMorphism S).

Definition DLWPTriple {S A} (direction : Direction)
  (m : prog S A) (pre : S -> Prop)
  (post : option (A * S) -> Prop) : Prop :=
  Approx direction (dlwpRecipe S) m (unaryPP pre post).

Theorem dlwp_pp_galois {S A} (m : prog S A) (pq : PP S A) :
  pp2wp pq ⊑ dlwpObs m <->
  pq ⊑ wp2pp (dlwpObs m).
Proof. apply pp_wp_galois. Qed.

Definition dlwpAt42 : option (unit * nat) -> Prop :=
  fun r =>
    match r with
    | Some (_, s) => s = 42
    | None => False
    end.

Theorem progB_DLWP_42 :
  DLWPTriple Over progB (fun _ => True) dlwpAt42.
Proof.
  cbn [DLWPTriple Approx wpPPApproxOps dlwpRecipe
    makeWPRecipe dlwpObs].
  intros s0 _. intros [[[]|]|] H; sauto limit: 200.
Qed.

Theorem progRet_dlwp_inc :
  DLWPTriple Under progRet preEq0 postEq0.
Proof.
  cbn [DLWPTriple Approx wpPPApproxOps dlwpRecipe
    makeWPRecipe dlwpObs preEq0 postEq0].
  intros s Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  injection Hwp as Hs. exact Hs.
Qed.
