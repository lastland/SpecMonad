(** * O'Hearn-style rewriting rules for incorrectness triples

    Stated over the [tripleASP] triples of [SP/StDivExcNonDet_SPStExc]. *)

From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import BaseGaloisConnections NewGaloisConnections.
From Incorrectness.Taxonomy.Arrows Require Import PredArr RelSPPairArr.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivExcNonDet_SPStExc.

Import MonadNotation.
Open Scope monad_scope.

Section OHearnRewritingRules.
  Variable S : Type.

  Theorem first_symmetry_rule_1_asp :
    forall A (m : stdivexcnd S A) pre post1 post2,
      (tripleASP m Under pre post1 /\
       tripleASP m Under pre post2) ->
        tripleASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] r [Hr1 | Hr2].
    - exact (H1 r Hr1).
    - exact (H2 r Hr2).
  Qed.

  Theorem first_symmetry_rule_2_asp :
    forall A (m : stdivexcnd S A) pre post1 post2,
      tripleASP m Under pre (fun r => post1 r \/ post2 r) ->
      (tripleASP m Under pre post1 /\
       tripleASP m Under pre post2).
  Proof.
    intros A m pre post1 post2 H. split.
    - intros r Hr. exact (H r (or_introl Hr)).
    - intros r Hr. exact (H r (or_intror Hr)).
  Qed.

  Theorem first_symmetry_rule_asp :
    forall A (m : stdivexcnd S A) pre post1 post2,
      (tripleASP m Under pre post1 /\
       tripleASP m Under pre post2) <->
        tripleASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2. split.
    - apply first_symmetry_rule_1_asp.
    - apply first_symmetry_rule_2_asp.
  Qed.

  Theorem second_symmetry_rule_asp_1 :
    forall A (m : stdivexcnd S A) pre post1 post2,
      (tripleASP m Over pre post1 /\
         tripleASP m Over pre post2) ->
      tripleASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] r Hasp.
    split; [exact (H1 r Hasp) | exact (H2 r Hasp)].
  Qed.

  Theorem second_symmetry_rule_asp_2 :
    forall A (m : stdivexcnd S A) pre post1 post2,
      tripleASP m Over pre (fun r => post1 r /\ post2 r) ->
      (tripleASP m Over pre post1 /\
         tripleASP m Over pre post2).
  Proof.
    intros A m pre post1 post2 H. split; intros r Hasp;
      [exact (proj1 (H r Hasp)) | exact (proj2 (H r Hasp))].
  Qed.

  Theorem second_symmetry_rule_asp :
    forall A (m : stdivexcnd S A) pre post1 post2,
      (tripleASP m Over pre post1 /\
         tripleASP m Over pre post2) <->
        tripleASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2. split.
    - apply second_symmetry_rule_asp_1.
    - apply second_symmetry_rule_asp_2.
  Qed.

  (** Rule of consequence, [Under]: WEAKEN the precondition and SHRINK the
      postcondition — the opposite of the [Over] direction below, because
      [Under] has the observation in the conclusion. *)
  Theorem first_imp_symmetry_rule_asp :
      forall A (m : stdivexcnd S A) pre pre' post post',
        (tripleASP m Under pre post /\
           (forall r, pre r -> pre' r) /\ (forall r, post' r -> post r)) -> tripleASP m Under pre' post'.
  Proof.
    intros A m pre pre' post post' [Htriple [Hpre Hpost]] r Hpost'.
    destruct (Htriple r (Hpost r Hpost')) as [s [Hp Hr]].
    exists s. split; [exact (Hpre s Hp) | exact Hr].
  Qed.

  Theorem second_imp_symmetry_rule_asp :
      forall A (m : stdivexcnd S A) pre pre' post post',
        (tripleASP m Over pre post /\
           (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) -> tripleASP m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [Htriple [Hpre Hpost]] r [s [Hp' Hr]].
    apply Hpost. apply Htriple. exists s. split; [exact (Hpre s Hp') | exact Hr].
  Qed.

  (** A result witnessed by the under-approximation is reached from a [u]-state;
      if [u] entails [o], the over-approximation must accept it. *)
  Theorem principle_of_agreement_asp :
      forall A (m : stdivexcnd S A) u u' o o',
        (tripleASP m Under u u' /\ tripleASP m Over o o' /\
           (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hcor Himp]] r Hu'.
    destruct (Hinc r Hu') as [s [Hu Hr]].
    apply Hcor. exists s. split; [exact (Himp s Hu) | exact Hr].
  Qed.

  Theorem principle_of_denial_asp :
      forall A (m : stdivexcnd S A) u u' o o',
        (tripleASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleASP m Over o o').
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hcor.
    apply Hnot.
    apply (principle_of_agreement_asp A m u u' o o').
    exact (conj Hinc (conj Hcor Himp)).
  Qed.
End OHearnRewritingRules.
