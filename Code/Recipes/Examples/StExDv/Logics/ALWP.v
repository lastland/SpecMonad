From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program WP PrePost Examples.

Import MonadNotation.
Open Scope monad_scope.
Open Scope refinement_scope.

Definition obsALWP {S A} (m : prog S A) : BaseProgWP S A :=
  mkStateT (fun s =>
    @mkOptionT PureWP _ (fun post =>
      (exists r,
        unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r) \/
      unOptionT (unOptionT (runStateT m s)) None)).

Lemma obsALWP_monotonic {S A} (m : prog S A) :
  forall s (p q : option (A * S) -> Prop),
    (forall r, p r -> q r) ->
    unOptionT (runStateT (obsALWP m) s) p ->
    unOptionT (runStateT (obsALWP m) s) q.
Proof.
  intros s p q H [[r [Hr Hp]] | Hdiv].
  - left. exists r. split; [exact Hr | exact (H r Hp)].
  - right. exact Hdiv.
Qed.

Lemma obsALWP_unfold {S A} (m : prog S A) s post :
  unOptionT (runStateT (obsALWP m) s) post <->
  (exists r,
    unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r) \/
  unOptionT (unOptionT (runStateT m s)) None.
Proof. reflexivity. Qed.

Lemma obsALWP_bind {S A B}
  (m : prog S A) (k : A -> prog S B) s post :
  unOptionT (runStateT (obsALWP (m >>= k)) s) post <->
  unOptionT (runStateT (obsALWP m) s)
    (fun r =>
      match r with
      | Some (a, s') => unOptionT (runStateT (obsALWP (k a)) s') post
      | None => post None
      end).
Proof.
  rewrite (obsALWP_unfold (m >>= k)), (obsALWP_unfold m). split.
  - intros [[r [Hr Hp]] | Hdiv].
    + apply outcomes_bind in Hr. destruct Hr as [oa [Hoa Hk]].
      destruct oa as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoa |].
        cbn. left. exists r. auto.
      * injection Hk as Hk. subst r. left. exists None. auto.
      * discriminate.
    + apply outcomes_bind in Hdiv. destruct Hdiv as [oa [Hoa Hk]].
      destruct oa as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoa |].
        cbn. right. exact Hk.
      * discriminate.
      * right. exact Hoa.
  - intros [[r [Hr Hpost]] | Hdiv].
    + destruct r as [[a s']|].
      * cbn in Hpost.
        destruct Hpost as [[r [Hk Hp]] | Hk].
        -- left. exists r. split; [|exact Hp].
           apply outcomes_bind. exists (Some (Some (a, s'))). auto.
        -- right. apply outcomes_bind.
           exists (Some (Some (a, s'))). auto.
      * left. exists None. split; [|exact Hpost].
        apply outcomes_bind. exists (Some None). auto.
    + right. apply outcomes_bind. exists None. auto.
Qed.

Definition alwpObs {S A} (m : prog S A) : ProgWP S A :=
  {| runProgWP := obsALWP m;
     progWPMono := @obsALWP_monotonic S A m |}.

#[global] Instance alwpMorphism (S : Type) :
  @MonadMorphism (prog S) (ProgWP S)
    (Monad__nditprog S) (Monad__ProgWP S) (Eq1__ProgWP S) (@alwpObs S).
Proof.
  constructor.
  - intros A a. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (obsALWP (@nditRet S A a)) s) post <->
       unOptionT
         (runStateT (runProgWP (@retProgWP S A a)) s) post).
    cbv. firstorder congruence.
  - intros A B m f. apply wpExt. intros s post.
    change
      (unOptionT
         (runStateT (runProgWP (alwpObs (bind m f))) s) post <->
       unOptionT
         (runStateT
           (runProgWP
             (@bindProgWP S A B (alwpObs m)
               (fun a => alwpObs (f a)))) s) post).
    unfold alwpObs.
    cbn [runProgWP bindProgWP Monad__BaseProgWP baseWPBind].
    rewrite obsALWP_bind.
    cbv [Monad__BaseProgWP baseWPBind Monad_stateT Monad_optionT
      Monad_PureWP].
    reflexivity.
Qed.

Definition alwpRecipe (S : Type) : LogicRecipe (prog S) (ProgWP S) :=
  makeWPRecipe S (@alwpObs S) (alwpMorphism S).

Definition ALWPTriple {S A} (direction : Direction)
  (m : prog S A) (pre : S -> Prop)
  (post : option (A * S) -> Prop) : Prop :=
  Approx direction (alwpRecipe S) m (unaryPP pre post).

Theorem alwp_pp_galois {S A} (m : prog S A) (pq : PP S A) :
  pp2wp pq ⊑ alwpObs m <->
  pq ⊑ wp2pp (alwpObs m).
Proof. apply pp_wp_galois. Qed.

Theorem progB_has_divergent_branch :
  ALWPTriple Over progB (fun _ => True) (fun _ => False).
Proof.
  cbn [ALWPTriple Approx wpPPApproxOps alwpRecipe
    makeWPRecipe alwpObs].
  intros s _. right.
  exists (Some (Some (tt, 42))). split; [reflexivity|].
  cbn. exists (Some (Some (42, 42))). split; [reflexivity|].
  cbn. right. reflexivity.
Qed.
