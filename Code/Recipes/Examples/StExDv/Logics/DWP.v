From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program WP PrePost Examples.

Import MonadNotation.
Open Scope monad_scope.
Open Scope refinement_scope.

Definition obsDWP {S A} (m : prog S A) : BaseProgWP S A :=
  mkStateT (fun s =>
    @mkOptionT PureWP _ (fun post =>
      forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
        match oa with
        | Some r => post r
        | None => False
        end)).

Lemma obsDWP_monotonic {S A} (m : prog S A) :
  forall s (p q : option (A * S) -> Prop),
    (forall r, p r -> q r) ->
    unOptionT (runStateT (obsDWP m) s) p ->
    unOptionT (runStateT (obsDWP m) s) q.
Proof.
  intros s p q H Hp oa Hoa. specialize (Hp oa Hoa).
  destruct oa as [r|]; [exact (H r Hp) | exact Hp].
Qed.

Lemma obsDWP_unfold {S A} (m : prog S A) s post :
  unOptionT (runStateT (obsDWP m) s) post <->
  forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
    match oa with Some r => post r | None => False end.
Proof. reflexivity. Qed.

Lemma obsDWP_bind {S A B}
  (m : prog S A) (k : A -> prog S B) s post :
  unOptionT (runStateT (obsDWP (m >>= k)) s) post <->
  unOptionT (runStateT (obsDWP m) s)
    (fun r =>
      match r with
      | Some (a, s') => unOptionT (runStateT (obsDWP (k a)) s') post
      | None => post None
      end).
Proof.
  rewrite (obsDWP_unfold (m >>= k)), (obsDWP_unfold m).
  setoid_rewrite outcomes_bind. split.
  - intros H oa Hoa. destruct oa as [[[a s']|]|].
    + cbn. intros ob Hob.
      apply H. exists (Some (Some (a, s'))). auto.
    + apply (H (Some None)). exists (Some None). auto.
    + apply (H None). exists None. auto.
  - intros H ob [oa [Hoa Hk]]. specialize (H oa Hoa).
    destruct oa as [[[a s']|]|].
    + cbn in H. exact (H ob Hk).
    + subst ob. exact H.
    + subst ob. contradiction.
Qed.

Definition dwpObs {S A} (m : prog S A) : ProgWP S A :=
  {| runProgWP := obsDWP m;
     progWPMono := @obsDWP_monotonic S A m |}.

#[global] Instance dwpMorphism (S : Type) :
  @MonadMorphism (prog S) (ProgWP S)
    (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) (@dwpObs S).
Proof.
  constructor.
  - intros A a. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (obsDWP (@nditRet S A a)) s) post <->
       unOptionT
         (runStateT (runProgWP (@retProgWP S A a)) s) post).
    cbv. split.
    + intro H. exact (H (Some (Some (a, s))) eq_refl).
    + intros H oa Hoa. subst oa. exact H.
  - intros A B m f. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (runProgWP (dwpObs (bind m f))) s) post <->
       unOptionT
         (runStateT
           (runProgWP
             (@bindProgWP S A B (dwpObs m)
               (fun a => dwpObs (f a)))) s) post).
    unfold dwpObs.
    cbn [runProgWP bindProgWP Monad__BaseProgWP baseWPBind].
    rewrite obsDWP_bind.
    cbv [Monad__BaseProgWP baseWPBind Monad_stateT Monad_optionT
      Monad_PureWP].
    reflexivity.
Qed.

Definition dwpRecipe (S : Type) : LogicRecipe (prog S) (ProgWP S) :=
  makeWPRecipe S (@dwpObs S) (dwpMorphism S).

Definition DWPTriple {S A} (direction : Direction)
  (m : prog S A) (pre : S -> Prop)
  (post : option (A * S) -> Prop) : Prop :=
  Approx direction (dwpRecipe S) m (unaryPP pre post).

Theorem dwp_pp_galois {S A} (m : prog S A) (pq : PP S A) :
  pp2wp pq ⊑ dwpObs m <->
  pq ⊑ wp2pp (dwpObs m).
Proof. apply pp_wp_galois. Qed.

Definition atLeast42 : option (unit * nat) -> Prop :=
  fun r =>
    match r with
    | Some (_, s) => s >= 42
    | None => False
    end.

Definition at42 : option (unit * nat) -> Prop :=
  fun r =>
    match r with
    | Some (_, s) => s = 42
    | None => False
    end.

Theorem progA_DWP_all :
  DWPTriple Over progA (fun _ => True) atLeast42.
Proof.
  cbn [DWPTriple Approx wpPPApproxOps dwpRecipe
    makeWPRecipe dwpObs].
  intros s0 _. intros [[[]|]|] H; sauto limit: 200.
Qed.

Theorem progA_DWP_not42 :
  ~ DWPTriple Over progA (fun _ => True) at42.
Proof.
  cbn [DWPTriple Approx wpPPApproxOps dwpRecipe
    makeWPRecipe dwpObs].
  intro H. specialize (H 0 I (Some (Some (tt, 43)))).
  sauto limit: 200.
Qed.

Theorem progB_DWP_unprovable :
  ~ DWPTriple Over progB (fun _ => True) at42.
Proof.
  cbn [DWPTriple Approx wpPPApproxOps dwpRecipe
    makeWPRecipe dwpObs].
  intro H. specialize (H 0 I None). sauto limit: 200.
Qed.

Theorem progRet_dwp_inc :
  DWPTriple Under progRet preEq0 postEq0.
Proof.
  cbn [DWPTriple Approx wpPPApproxOps dwpRecipe
    makeWPRecipe dwpObs preEq0 postEq0].
  intros s Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  injection Hwp as Hs. exact Hs.
Qed.
