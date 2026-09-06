From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Coq Require Import Lia PeanoNat.
From Hammer Require Import Tactics.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program WP PrePost Examples.

Import MonadNotation.
Open Scope monad_scope.
Open Scope refinement_scope.

Definition obsAWP {S A} (m : prog S A) : BaseProgWP S A :=
  mkStateT (fun s =>
    @mkOptionT PureWP _ (fun post =>
      exists r,
        unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r)).

Lemma obsAWP_monotonic {S A} (m : prog S A) :
  forall s (p q : option (A * S) -> Prop),
    (forall r, p r -> q r) ->
    unOptionT (runStateT (obsAWP m) s) p ->
    unOptionT (runStateT (obsAWP m) s) q.
Proof.
  intros s p q H [r [Hr Hp]].
  exists r. split; [exact Hr | exact (H r Hp)].
Qed.

Lemma obsAWP_unfold {S A} (m : prog S A) s post :
  unOptionT (runStateT (obsAWP m) s) post <->
  exists r,
    unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r.
Proof. reflexivity. Qed.

Lemma obsAWP_bind {S A B}
  (m : prog S A) (k : A -> prog S B) s post :
  unOptionT (runStateT (obsAWP (m >>= k)) s) post <->
  unOptionT (runStateT (obsAWP m) s)
    (fun r =>
      match r with
      | Some (a, s') => unOptionT (runStateT (obsAWP (k a)) s') post
      | None => post None
      end).
Proof.
  rewrite (obsAWP_unfold (m >>= k)), (obsAWP_unfold m). split.
  - intros [r [Hr Hp]]. apply outcomes_bind in Hr.
    destruct Hr as [oa [Hoa Hk]]. destruct oa as [[[a s']|]|].
    + exists (Some (a, s')). split; [exact Hoa |].
      cbn. exists r. auto.
    + injection Hk as Hk. subst r. exists None. auto.
    + discriminate.
  - intros [r [Hr Hpost]]. destruct r as [[a s']|].
    + cbn in Hpost.
      destruct Hpost as [r [Hk Hp]]. exists r. split; [|exact Hp].
      apply outcomes_bind. exists (Some (Some (a, s'))). auto.
    + exists None. split; [|exact Hpost].
      apply outcomes_bind. exists (Some None). auto.
Qed.

Definition awpObs {S A} (m : prog S A) : ProgWP S A :=
  {| runProgWP := obsAWP m;
     progWPMono := @obsAWP_monotonic S A m |}.

#[global] Instance awpMorphism (S : Type) :
  @MonadMorphism (prog S) (ProgWP S)
    (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) (@awpObs S).
Proof.
  constructor.
  - intros A a. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (obsAWP (@nditRet S A a)) s) post <->
       unOptionT
         (runStateT (runProgWP (@retProgWP S A a)) s) post).
    cbv.
    firstorder congruence.
  - intros A B m f. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (runProgWP (awpObs (bind m f))) s) post <->
       unOptionT
         (runStateT
           (runProgWP
             (@bindProgWP S A B (awpObs m)
               (fun a => awpObs (f a)))) s) post).
    unfold awpObs.
    cbn [runProgWP bindProgWP Monad__BaseProgWP baseWPBind].
    rewrite obsAWP_bind.
    cbv [Monad__BaseProgWP baseWPBind Monad_stateT Monad_optionT
      Monad_PureWP].
    reflexivity.
Qed.

Definition awpRecipe (S : Type) : LogicRecipe (prog S) (ProgWP S) :=
  makeWPRecipe S (@awpObs S) (awpMorphism S).

Definition AWPTriple {S A} (direction : Direction)
  (m : prog S A) (pre : S -> Prop)
  (post : option (A * S) -> Prop) : Prop :=
  Approx direction (awpRecipe S) m (unaryPP pre post).

Theorem awp_pp_galois {S A} (m : prog S A) (pq : PP S A) :
  pp2wp pq ⊑ awpObs m <->
  pq ⊑ wp2pp (awpObs m).
Proof. apply pp_wp_galois. Qed.

Definition reaches (n : nat) : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, n).

Theorem progA_AWP_42 :
  AWPTriple Over progA (fun _ => True) (reaches 42).
Proof.
  cbn [AWPTriple Approx wpPPApproxOps awpRecipe
    makeWPRecipe awpObs reaches].
  intros s0 _. exists (Some (tt, 42)). split; sauto limit: 200.
Qed.

Theorem progA_AWP_43 :
  AWPTriple Over progA (fun _ => True) (reaches 43).
Proof.
  cbn [AWPTriple Approx wpPPApproxOps awpRecipe
    makeWPRecipe awpObs reaches].
  intros s0 _. exists (Some (tt, 43)). split; sauto limit: 200.
Qed.

Theorem progA_AWP_100_over :
  AWPTriple Under progA (fun _ => False) (reaches 100).
Proof.
  cbn [AWPTriple Approx wpPPApproxOps awpRecipe
    makeWPRecipe awpObs reaches].
  intros s [r [Hr Hpost]].
  change (r = Some (tt, 100)) in Hpost.
  change False.
  subst r. cbn in Hr. sauto limit: 200.
Qed.

Theorem progB_AWP_42 :
  AWPTriple Over progB (fun _ => True) (reaches 42).
Proof.
  cbn [AWPTriple Approx wpPPApproxOps awpRecipe
    makeWPRecipe awpObs reaches].
  intros s0 _. exists (Some (tt, 42)). split; sauto limit: 200.
Qed.

Theorem progloom_triple :
  AWPTriple Over WithdrawExample.progloom
    (fun balance => balance > 0) WithdrawExample.exceptionPost.
Proof.
  cbn [AWPTriple Approx wpPPApproxOps awpRecipe
    makeWPRecipe awpObs WithdrawExample.progloom
    WithdrawExample.exceptionPost pickP].
  intros s Hpos.
  exists None. split; [|exact I].
  exists (Some (Some (S s, s))). split.
  - exists (S s). reflexivity.
  - cbn. exists (Some (Some (s, s))). split.
    + reflexivity.
    + rewrite Nat.leb_refl. cbn.
      exists (Some None). split; [reflexivity|]. cbn. reflexivity.
Qed.

Theorem progloom_triple_harder :
  ~ AWPTriple Over WithdrawExample.progloom_harder
      (fun balance => balance > 0) WithdrawExample.exceptionPost.
Proof.
  cbn [AWPTriple Approx wpPPApproxOps awpRecipe
    makeWPRecipe awpObs WithdrawExample.progloom_harder
    WithdrawExample.exceptionPost pickP].
  intro H. specialize (H 1 ltac:(cbn; lia)).
  destruct H as [r [Hreach Hpost]]. destruct r as [[[] n]|].
  - exact Hpost.
  - destruct Hreach as [a [[amt Ha] Hcont]]. subst a. cbn in Hcont.
    destruct Hcont as [a2 [Ha2 Hcont2]]. subst a2. cbn in Hcont2.
    discriminate Hcont2.
Qed.
