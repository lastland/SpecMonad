(** * O'Hearn-style rewriting rules for incorrectness triples

    The rewriting rules of O'Hearn's "Incorrectness Logic", for a
    computation with state.  They are stated over its ASP triples,
    [triple (@aspSt S)]: [Under] is the incorrectness triple and [Over] the
    correctness one.

    The correctness-side rules also have a variant for the demonic liberal
    WP triples, [triple (@dwlpSt S)].  A [dwlpSt] [Under] triple is the
    [aspSt] [Over] triple with the same pre- and postcondition
    ([dwlp_under_galois_asp_over]), so each variant follows from its ASP
    counterpart. *)

From ExtLib Require Import Monad StateMonad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.WP Require Import WPure.
From Incorrectness.SP Require Import ASPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Generic Require Import TripleTaxonomy.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.
From Incorrectness.Verification.DivNonDet Require Import TriplesTaxonomy.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Triples.
From Incorrectness.Verification.DivNonDetSt Require Import TriplesTaxonomy.


Section OHearnRewritingRules.
  Variable S : Type.

  Theorem first_symmetry_rule_1_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Under pre post1 /\
       triple (@aspSt S) m Under pre post2) ->
        triple (@aspSt S) m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] r [Hr1 | Hr2].
    - exact (H1 r Hr1).
    - exact (H2 r Hr2).
  Qed.

  Theorem first_symmetry_rule_2_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      triple (@aspSt S) m Under pre (fun r => post1 r \/ post2 r) ->
      (triple (@aspSt S) m Under pre post1 /\
       triple (@aspSt S) m Under pre post2).
  Proof.
    intros A m pre post1 post2 H. split.
    - intros r Hr. exact (H r (or_introl Hr)).
    - intros r Hr. exact (H r (or_intror Hr)).
  Qed.

  Theorem first_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Under pre post1 /\
       triple (@aspSt S) m Under pre post2) <->
        triple (@aspSt S) m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2. split.
    - apply first_symmetry_rule_1_asp.
    - apply first_symmetry_rule_2_asp.
  Qed.

  Theorem second_symmetry_rule_asp_1 :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Over pre post1 /\
         triple (@aspSt S) m Over pre post2) ->
      triple (@aspSt S) m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] r Hasp.
    split; [ exact (H1 r Hasp) | exact (H2 r Hasp) ].
  Qed.

  Theorem second_symmetry_rule_asp_2 :
    forall A (m : stdivndNE S A) pre post1 post2,
      triple (@aspSt S) m Over pre (fun r => post1 r /\ post2 r) ->
      (triple (@aspSt S) m Over pre post1 /\
         triple (@aspSt S) m Over pre post2).
  Proof.
    intros A m pre post1 post2 H. split; intros r Hasp;
      [ exact (proj1 (H r Hasp)) | exact (proj2 (H r Hasp)) ].
  Qed.

  Theorem second_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Over pre post1 /\
         triple (@aspSt S) m Over pre post2) <->
        triple (@aspSt S) m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2. split.
    - apply second_symmetry_rule_asp_1.
    - apply second_symmetry_rule_asp_2.
  Qed.

  (** Rule of consequence, [Under]: WEAKEN the precondition and SHRINK the
      postcondition — the opposite of the [Over] direction below, because
      [Under] has the transformer's value in the conclusion. *)
  Theorem first_imp_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre pre' post post',
      (triple (@aspSt S) m Under pre post /\
         (forall s, pre s -> pre' s) /\ (forall r, post' r -> post r)) ->
      triple (@aspSt S) m Under pre' post'.
  Proof.
    intros A m pre pre' post post' [Htriple [Hpre Hpost]] r Hpost'.
    destruct (Htriple r (Hpost r Hpost')) as [[[] s] [Hp Hr]].
    exists (tt, s). split; [ exact (Hpre s Hp) | exact Hr ].
  Qed.

  Theorem second_imp_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre pre' post post',
      (triple (@aspSt S) m Over pre post /\
         (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
      triple (@aspSt S) m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [Htriple [Hpre Hpost]] r [[[] s] [Hp' Hr]].
    apply Hpost. apply Htriple.
    exists (tt, s). split; [ exact (Hpre s Hp') | exact Hr ].
  Qed.

  (** A result witnessed by the under-approximation is reached from a
      [u]-state; if [u] entails [o], the over-approximation must accept it. *)
  Theorem principle_of_agreement_asp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ triple (@aspSt S) m Over o o' /\
         (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hcor Himp]] r Hu'.
    destruct (Hinc r Hu') as [[[] s] [Hu Hr]].
    apply Hcor. exists (tt, s). split; [ exact (Himp s Hu) | exact Hr ].
  Qed.

  Theorem principle_of_denial_asp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ (forall s, u s -> o s) /\
         ~ (forall r, u' r -> o' r)) -> ~ triple (@aspSt S) m Over o o'.
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hcor. apply Hnot.
    exact (principle_of_agreement_asp A m u u' o o'
             (conj Hinc (conj Hcor Himp))).
  Qed.

  (** *** The demonic liberal WP variants *)

  Theorem second_symmetry_rule_dwlp_1 :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@dwlpSt S) m Under pre post1 /\
         triple (@dwlpSt S) m Under pre post2) ->
      triple (@dwlpSt S) m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2].
    apply (proj2 (dwlp_under_galois_asp_over m pre _)).
    apply (second_symmetry_rule_asp_1 A m pre post1 post2).
    split; apply (proj1 (dwlp_under_galois_asp_over m pre _)); assumption.
  Qed.

  Theorem second_symmetry_rule_dwlp_2 :
    forall A (m : stdivndNE S A) pre post1 post2,
      triple (@dwlpSt S) m Under pre (fun r => post1 r /\ post2 r) ->
      (triple (@dwlpSt S) m Under pre post1 /\
         triple (@dwlpSt S) m Under pre post2).
  Proof.
    intros A m pre post1 post2 H.
    destruct (second_symmetry_rule_asp_2 A m pre post1 post2
                (proj1 (dwlp_under_galois_asp_over m pre _) H))
      as [H1 H2].
    split; apply (proj2 (dwlp_under_galois_asp_over m pre _)); assumption.
  Qed.

  Theorem second_symmetry_rule_dwlp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@dwlpSt S) m Under pre post1 /\
         triple (@dwlpSt S) m Under pre post2) <->
        triple (@dwlpSt S) m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros. split.
    - apply second_symmetry_rule_dwlp_1.
    - apply second_symmetry_rule_dwlp_2.
  Qed.

  (** A demonic liberal WP triple gives the ASP [Over] triple, with
      consequence. *)
  Theorem second_imp_symmetry_rule_dwlp :
    forall A (m : stdivndNE S A) pre pre' post post',
      (triple (@dwlpSt S) m Under pre post /\
         (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
      triple (@aspSt S) m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [Hwp Hcons].
    apply (second_imp_symmetry_rule_asp A m pre pre' post post').
    split; [| exact Hcons ].
    exact (proj1 (dwlp_under_galois_asp_over m pre post) Hwp).
  Qed.

  Theorem principle_of_agreement_dwlp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\
         triple (@dwlpSt S) m Under o o' /\
         (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hwp Himp]].
    apply (principle_of_agreement_asp A m u u' o o').
    exact (conj Hinc
             (conj (proj1 (dwlp_under_galois_asp_over m o o') Hwp) Himp)).
  Qed.

  Theorem principle_of_denial_dwlp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ (forall s, u s -> o s) /\
         ~ (forall r, u' r -> o' r)) -> ~ triple (@dwlpSt S) m Under o o'.
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hwp. apply Hnot.
    exact (principle_of_agreement_dwlp A m u u' o o'
             (conj Hinc (conj Hwp Himp))).
  Qed.
End OHearnRewritingRules.
