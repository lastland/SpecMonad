(** * O'Hearn-style rewriting rules for incorrectness triples

    Extracted from the original [NonDetItObservation.v]; the triples and
    observations it reasons about live in [OldSPObservations.v]. *)

From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg ProgFacts WP Pred PredFacts SPost WPred WPNonDetItObservations.
From Incorrectness.Taxonomy.OldSP Require Import OldSPObservations.

Import MonadNotation.
Open Scope monad_scope.

Section OHearnRewritingRules.

  Variable S : Type.

  Theorem first_symmetry_rule_1_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Under pre post1 /\
       tripleSP obsASP m Under pre post2) ->
        tripleSP obsASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2.
    unfold tripleSP, obsASP, asp.
    intro H. inversion H as [H1 H2].
    intros r Hr. inversion Hr as [Hr1 | Hr2].
    - apply H1. exact Hr1.
    - apply H2. exact Hr2.
  Qed.

  Theorem first_symmetry_rule_2_asp :
    forall A (m : nditprog S A) pre post1 post2,
      tripleSP obsASP m Under pre (fun r => post1 r \/ post2 r) ->
      (tripleSP obsASP m Under pre post1 /\
       tripleSP obsASP m Under pre post2).
  Proof.
    intros A m pre post1 post2.
    unfold tripleSP, obsASP, asp.
    intro H. split.
    - intros r Hr. apply H. left. exact Hr.
    - intros r Hr. apply H. right. exact Hr.
  Qed.

  Theorem first_symmetry_rule_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Under pre post1 /\
       tripleSP obsASP m Under pre post2) <->
        tripleSP obsASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros. split.
    - apply first_symmetry_rule_1_asp.
    - apply first_symmetry_rule_2_asp.
  Qed.

  Theorem second_symmetry_rule_asp_1 :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Over pre post1 /\
         tripleSP obsASP m Over pre post2) ->
      tripleSP obsASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2.
    intro H. inversion H as [H1 H2].
    intros r Hr. split.
    - apply H1. exact Hr.
    - apply H2. exact Hr.
  Qed.

  Theorem second_symmetry_rule_asp_2 :
    forall A (m : nditprog S A) pre post1 post2,
      tripleSP obsASP m Over pre (fun r => post1 r /\ post2 r) ->
      (tripleSP obsASP m Over pre post1 /\
         tripleSP obsASP m Over pre post2).
  Proof.
    intros A m pre post1 post2.
    unfold tripleSP, obsASP, asp.
    intro H. split.
    - intros r Hr. apply H. exact Hr.
    - intros r Hr. apply H. exact Hr.
  Qed.

  Theorem second_symmetry_rule_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Over pre post1 /\
         tripleSP obsASP m Over pre post2) <->
        tripleSP obsASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros. split.
    - apply second_symmetry_rule_asp_1.
    - apply second_symmetry_rule_asp_2.
  Qed.

  Theorem second_symmetry_rule_dwp_1 :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleWP obsDWLP m pre SubsetOf post1 /\
         tripleWP obsDWLP m pre SubsetOf post2) ->
      tripleWP obsDWLP m pre SubsetOf (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] s Hpre.
    specialize (H1 s Hpre). specialize (H2 s Hpre).
    cbn in H1, H2 |- *.
    destruct (runStateT m s) as [[outcomes]].
    intros oa Hoa.
    specialize (H1 oa Hoa). specialize (H2 oa Hoa).
    destruct oa as [r|]; [|exact I].
    split; assumption.
  Qed.

  Theorem second_symmetry_rule_dwp_2 :
    forall A (m : nditprog S A) pre post1 post2,
      tripleWP obsDWLP m pre SubsetOf (fun r => post1 r /\ post2 r) ->
       (tripleWP obsDWLP m pre SubsetOf post1 /\
         tripleWP obsDWLP m pre SubsetOf post2).
  Proof.
    intros A m pre post1 post2 H.
    split.
    - intros s Hpre. specialize (H s Hpre). cbn in H |- *.
      destruct (runStateT m s) as [[outcomes]].
      intros oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [|exact I]. exact (proj1 H).
    - intros s Hpre. specialize (H s Hpre). cbn in H |- *.
      destruct (runStateT m s) as [[outcomes]].
      intros oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [|exact I]. exact (proj2 H).
  Qed.

  Theorem second_symmetry_rule_dwp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleWP obsDWLP m pre SubsetOf post1 /\
         tripleWP obsDWLP m pre SubsetOf post2) <->
        tripleWP obsDWLP m pre SubsetOf (fun r => post1 r /\ post2 r).
    Proof.
      intros. split.
      - apply second_symmetry_rule_dwp_1.
      - apply second_symmetry_rule_dwp_2.
    Qed.

    (** Rule of consequence for SP-Incorrect: weaken the precondition
        and shrink the postcondition. *)
    Theorem first_imp_symmetry_rule_asp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleSP obsASP m Under pre post /\
           (forall r, pre r -> pre' r) /\ (forall r, post' r -> post r)) -> tripleSP obsASP m Under pre' post'.
    Proof.
      intros A m pre pre' post post' [Htriple [Hpre Hpost]].
      unfold tripleSP, obsASP in *.
      unfold asp in *.
      intros r Hpost'.
      destruct (Htriple r (Hpost r Hpost')) as [s [Hp Hrel]].
      exists s. split; [apply Hpre; exact Hp | exact Hrel].
    Qed.

    (** Rule of consequence for SP-Correct: strengthen the precondition
        and weaken the postcondition. *)
    Theorem second_imp_symmetry_rule_asp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleSP obsASP m Over pre post /\
           (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) -> tripleSP obsASP m Over pre' post'.
    Proof.
      intros A m pre pre' post post' [Htriple [Hpre Hpost]].
      unfold tripleSP, obsASP in *.
      unfold asp in *.
      intros r [s [Hpre' Hrel]].
      apply Hpost. apply Htriple.
      exists s. split; [apply Hpre; exact Hpre' | exact Hrel].
    Qed.

    (** DWLP-Correct implies ASP-Correct (with consequence): a result
        reachable from a [pre']-state is a terminating outcome there, so
        the demonic partial transformer forces the postcondition. *)
    Theorem second_imp_symmetry_rule_dwp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleWP obsDWLP m pre SubsetOf post /\
           (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) -> tripleSP obsASP m Over pre' post'.
    Proof.
      intros A m pre pre' post post' [Hwp [Hpre Hpost]].
      unfold tripleWP, obsDWLP in Hwp.
      unfold tripleSP, obsASP.
      unfold asp, obsRel.
      intros r [s0 [Hpre' Hrel]].
      apply Hpost.
      specialize (Hwp s0 (Hpre s0 Hpre')). cbn in Hwp.
      destruct (runStateT m s0) as [[outcomes]] eqn:Hm. cbn in Hwp, Hrel.
      refine (Hwp (Some r) _).
      destruct r as [[a s']|]; exact Hrel.
    Qed.

    (** Principle of agreement (SP): if [u]-reachability witnesses the
        under-approximation [u'] and [u] entails the over-approximation
        precondition [o], then the over-approximation postcondition [o']
        holds of every [u']-result. *)
    Theorem principle_of_agreement_asp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ tripleSP obsASP m Over o o' /\
           (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
    Proof.
      intros A m u u' o o' [Hinc [Hcor Himp]].
      unfold tripleSP, obsASP in *.
      unfold asp in *.
      intros r Hu'.
      destruct (Hinc r Hu') as [s [Hu Hrel]].
      apply Hcor. exists s. split; [apply Himp; exact Hu | exact Hrel].
    Qed.

    (** Principle of agreement, demonic-partial-WP variant. *)
    Theorem principle_of_agreement_dwp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ tripleWP obsDWLP m o SubsetOf o' /\
           (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
    Proof.
      intros A m u u' o o' [Hinc [Hwp Himp]].
      unfold tripleSP, obsASP in Hinc.
      unfold asp, obsRel in Hinc.
      unfold tripleWP, obsDWLP in Hwp.
      intros r Hu'.
      destruct (Hinc r Hu') as [s [Hu Hrel]].
      specialize (Hwp s (Himp s Hu)). cbn in Hwp.
      destruct (runStateT m s) as [[outcomes]] eqn:Hm. cbn in Hwp, Hrel.
      refine (Hwp (Some r) _).
      destruct r as [[a s']|]; exact Hrel.
    Qed.

    (** Principle of denial (SP): contrapositive of agreement. *)
    Theorem principle_of_denial_asp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleSP obsASP m Over o o').
    Proof.
      intros A m u u' o o' [Hinc [Himp Hnot]] Hcor.
      apply Hnot.
      apply (principle_of_agreement_asp A m u u' o o').
      exact (conj Hinc (conj Hcor Himp)).
    Qed.

    (** Principle of denial, demonic-partial-WP variant. *)
    Theorem principle_of_denial_dwp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleWP obsDWLP m o SubsetOf o').
    Proof.
      intros A m u u' o o' [Hinc [Himp Hnot]] Hwp.
      apply Hnot.
      apply (principle_of_agreement_dwp A m u u' o o').
      exact (conj Hinc (conj Hwp Himp)).
    Qed.

End OHearnRewritingRules.


(* ================================================================= *)
(** ** Transported ([tripleSPm]) forms of the rules above              *)
(* ================================================================= *)

(** O'Hearn's rewriting rules and the agreement/denial principles. *)
Theorem m_first_symmetry_rule_asp : forall S A (m : nditprog S A) pre post1 post2,
    (tripleSPm spASP obsSP m Under pre post1 /\
     tripleSPm spASP obsSP m Under pre post2) <->
    tripleSPm spASP obsSP m Under pre (fun r => post1 r \/ post2 r).
Proof. intros S A m pre post1 post2. to_pointwise_sp. apply first_symmetry_rule_asp. Qed.

Theorem m_second_symmetry_rule_asp : forall S A (m : nditprog S A) pre post1 post2,
    (tripleSPm spASP obsSP m Over pre post1 /\
     tripleSPm spASP obsSP m Over pre post2) <->
    tripleSPm spASP obsSP m Over pre (fun r => post1 r /\ post2 r).
Proof. intros S A m pre post1 post2. to_pointwise_sp. apply second_symmetry_rule_asp. Qed.

Theorem m_first_imp_symmetry_rule_asp : forall S A (m : nditprog S A) pre pre' post post',
    (tripleSPm spASP obsSP m Under pre post /\
     (forall r, pre r -> pre' r) /\ (forall r, post' r -> post r)) ->
    tripleSPm spASP obsSP m Under pre' post'.
Proof. intros S A m pre pre' post post'. to_pointwise_sp. apply first_imp_symmetry_rule_asp. Qed.

Theorem m_second_imp_symmetry_rule_asp : forall S A (m : nditprog S A) pre pre' post post',
    (tripleSPm spASP obsSP m Over pre post /\
     (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) ->
    tripleSPm spASP obsSP m Over pre' post'.
Proof. intros S A m pre pre' post post'. to_pointwise_sp. apply second_imp_symmetry_rule_asp. Qed.

Theorem m_second_imp_symmetry_rule_dwp : forall S A (m : nditprog S A) pre pre' post post',
    (tripleWP obsDWLP m pre SubsetOf post /\
     (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) ->
    tripleSPm spASP obsSP m Over pre' post'.
Proof. intros S A m pre pre' post post'. to_pointwise_sp. apply second_imp_symmetry_rule_dwp. Qed.

Theorem m_principle_of_agreement_asp : forall S A (m : nditprog S A) u u' o o',
    (tripleSPm spASP obsSP m Under u u' /\ tripleSPm spASP obsSP m Over o o' /\
     (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
Proof. intros S A m u u' o o'. to_pointwise_sp. apply principle_of_agreement_asp. Qed.

Theorem m_principle_of_agreement_dwp : forall S A (m : nditprog S A) u u' o o',
    (tripleSPm spASP obsSP m Under u u' /\ tripleWP obsDWLP m o SubsetOf o' /\
     (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
Proof. intros S A m u u' o o'. to_pointwise_sp. apply principle_of_agreement_dwp. Qed.

Theorem m_principle_of_denial_asp : forall S A (m : nditprog S A) u u' o o',
    (tripleSPm spASP obsSP m Under u u' /\ (forall r, u r -> o r) /\
     ~ (forall r, u' r -> o' r)) -> ~ tripleSPm spASP obsSP m Over o o'.
Proof. intros S A m u u' o o'. to_pointwise_sp. apply principle_of_denial_asp. Qed.

Theorem m_principle_of_denial_dwp : forall S A (m : nditprog S A) u u' o o',
    (tripleSPm spASP obsSP m Under u u' /\ (forall r, u r -> o r) /\
     ~ (forall r, u' r -> o' r)) -> ~ tripleWP obsDWLP m o SubsetOf o'.
Proof. intros S A m u u' o o'. to_pointwise_sp. apply principle_of_denial_dwp. Qed.
