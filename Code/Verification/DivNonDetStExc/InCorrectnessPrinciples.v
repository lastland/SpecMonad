(** * O'Hearn-style rewriting rules, with state and exceptions

    The rules of [Generic/InCorrectnessPrinciples.v] for the ASP triples of
    computations with state and exceptions, [triple (@aspStExc S)]: [Under]
    is the incorrectness triple and [Over] the correctness one; a
    postcondition is on the outcome, an exception being [None].  The
    correctness-side rules also have a variant for the demonic liberal WP
    triples, [triple (@dwlpStExc S)], through the Galois edge
    [dwlp_under_galois_asp_over_exc]. *)

From ExtLib Require Import Monad StateMonad OptionMonad.
From Incorrectness.Verification.Generic Require Import Triple InCorrectnessPrinciples.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation Morphisms Triples TriplesTaxonomy.

Section OHearnRewritingRules.
  Variable S : Type.

  Theorem first_symmetry_rule_1_aspStExc :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      (triple (@aspStExc S) m Under pre post1 /\ triple (@aspStExc S) m Under pre post2) ->
      triple (@aspStExc S) m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2 H. exact (first_symmetry_rule_1 (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem first_symmetry_rule_2_aspStExc :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      triple (@aspStExc S) m Under pre (fun r => post1 r \/ post2 r) ->
      (triple (@aspStExc S) m Under pre post1 /\ triple (@aspStExc S) m Under pre post2).
  Proof.
    intros A m pre post1 post2 H. exact (first_symmetry_rule_2 (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem first_symmetry_rule_aspStExc :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      (triple (@aspStExc S) m Under pre post1 /\ triple (@aspStExc S) m Under pre post2) <->
      triple (@aspStExc S) m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2. split;
      [ apply first_symmetry_rule_1_aspStExc | apply first_symmetry_rule_2_aspStExc ].
  Qed.

  Theorem second_symmetry_rule_aspStExc_1 :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      (triple (@aspStExc S) m Over pre post1 /\ triple (@aspStExc S) m Over pre post2) ->
      triple (@aspStExc S) m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 H. exact (second_symmetry_rule_1 (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem second_symmetry_rule_aspStExc_2 :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      triple (@aspStExc S) m Over pre (fun r => post1 r /\ post2 r) ->
      (triple (@aspStExc S) m Over pre post1 /\ triple (@aspStExc S) m Over pre post2).
  Proof.
    intros A m pre post1 post2 H. exact (second_symmetry_rule_2 (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem second_symmetry_rule_aspStExc :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      (triple (@aspStExc S) m Over pre post1 /\ triple (@aspStExc S) m Over pre post2) <->
      triple (@aspStExc S) m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2. split;
      [ apply second_symmetry_rule_aspStExc_1 | apply second_symmetry_rule_aspStExc_2 ].
  Qed.

  Theorem first_imp_symmetry_rule_aspStExc :
    forall A (m : stdivexcndNE S A) pre pre' post post',
      (triple (@aspStExc S) m Under pre post /\
         (forall s, pre s -> pre' s) /\ (forall r, post' r -> post r)) ->
      triple (@aspStExc S) m Under pre' post'.
  Proof.
    intros A m pre pre' post post' [H [Hpre Hpost]].
    exact (first_imp_symmetry_rule (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => pre (snd us)) (fun us => pre' (snd us)) post post'
             (conj H (conj (fun us => Hpre (snd us)) Hpost))).
  Qed.

  Theorem second_imp_symmetry_rule_aspStExc :
    forall A (m : stdivexcndNE S A) pre pre' post post',
      (triple (@aspStExc S) m Over pre post /\
         (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
      triple (@aspStExc S) m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [H [Hpre Hpost]].
    exact (second_imp_symmetry_rule (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => pre (snd us)) (fun us => pre' (snd us)) post post'
             (conj H (conj (fun us => Hpre (snd us)) Hpost))).
  Qed.

  Theorem principle_of_agreement_aspStExc :
    forall A (m : stdivexcndNE S A) u u' o o',
      (triple (@aspStExc S) m Under u u' /\ triple (@aspStExc S) m Over o o' /\
         (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hcor Himp]].
    exact (principle_of_agreement (fun (us : unit * S) o => outStExc m (snd us) (Some o)) (fun us => u (snd us)) (fun us => o (snd us)) u' o'
             (conj Hinc (conj Hcor (fun us => Himp (snd us))))).
  Qed.

  Theorem principle_of_denial_aspStExc :
    forall A (m : stdivexcndNE S A) u u' o o',
      (triple (@aspStExc S) m Under u u' /\ (forall s, u s -> o s) /\
         ~ (forall r, u' r -> o' r)) -> ~ triple (@aspStExc S) m Over o o'.
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hcor. apply Hnot.
    exact (principle_of_agreement_aspStExc A m u u' o o' (conj Hinc (conj Hcor Himp))).
  Qed.

  (** *** The demonic liberal WP variants *)

  Theorem second_symmetry_rule_dwlpStExc_1 :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      (triple (@dwlpStExc S) m Under pre post1 /\ triple (@dwlpStExc S) m Under pre post2) ->
      triple (@dwlpStExc S) m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2].
    apply (proj2 (dwlp_under_galois_asp_over_exc m pre _)).
    apply (second_symmetry_rule_aspStExc_1 A m pre post1 post2).
    split; apply (proj1 (dwlp_under_galois_asp_over_exc m pre _)); assumption.
  Qed.

  Theorem second_symmetry_rule_dwlpStExc_2 :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      triple (@dwlpStExc S) m Under pre (fun r => post1 r /\ post2 r) ->
      (triple (@dwlpStExc S) m Under pre post1 /\ triple (@dwlpStExc S) m Under pre post2).
  Proof.
    intros A m pre post1 post2 H.
    destruct (second_symmetry_rule_aspStExc_2 A m pre post1 post2
                (proj1 (dwlp_under_galois_asp_over_exc m pre _) H)) as [H1 H2].
    split; apply (proj2 (dwlp_under_galois_asp_over_exc m pre _)); assumption.
  Qed.

  Theorem second_symmetry_rule_dwlpStExc :
    forall A (m : stdivexcndNE S A) pre post1 post2,
      (triple (@dwlpStExc S) m Under pre post1 /\ triple (@dwlpStExc S) m Under pre post2) <->
      triple (@dwlpStExc S) m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros. split; [ apply second_symmetry_rule_dwlpStExc_1 | apply second_symmetry_rule_dwlpStExc_2 ].
  Qed.

  Theorem second_imp_symmetry_rule_dwlpStExc :
    forall A (m : stdivexcndNE S A) pre pre' post post',
      (triple (@dwlpStExc S) m Under pre post /\
         (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
      triple (@aspStExc S) m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [Hwp Hcons].
    apply (second_imp_symmetry_rule_aspStExc A m pre pre' post post').
    split; [| exact Hcons ].
    exact (proj1 (dwlp_under_galois_asp_over_exc m pre post) Hwp).
  Qed.

  Theorem principle_of_agreement_dwlpStExc :
    forall A (m : stdivexcndNE S A) u u' o o',
      (triple (@aspStExc S) m Under u u' /\ triple (@dwlpStExc S) m Under o o' /\
         (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hwp Himp]].
    apply (principle_of_agreement_aspStExc A m u u' o o').
    exact (conj Hinc (conj (proj1 (dwlp_under_galois_asp_over_exc m o o') Hwp) Himp)).
  Qed.

  Theorem principle_of_denial_dwlpStExc :
    forall A (m : stdivexcndNE S A) u u' o o',
      (triple (@aspStExc S) m Under u u' /\ (forall s, u s -> o s) /\
         ~ (forall r, u' r -> o' r)) -> ~ triple (@dwlpStExc S) m Under o o'.
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hwp. apply Hnot.
    exact (principle_of_agreement_dwlpStExc A m u u' o o' (conj Hinc (conj Hwp Himp))).
  Qed.

End OHearnRewritingRules.
