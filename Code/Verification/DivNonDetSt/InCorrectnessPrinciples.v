(** * O'Hearn-style rewriting rules for incorrectness triples

    The rewriting rules of O'Hearn's "Incorrectness Logic", for a
    computation with state.  They are stated over its ASP triples,
    [triple (@aspSt S)]: [Under] is the incorrectness triple and [Over] the
    correctness one, and are the rules of [Generic/InCorrectnessPrinciples.v]
    at the relation between start states and outcomes.

    The correctness-side rules also have a variant for the demonic liberal
    WP triples, [triple (@dwlpSt S)].  A [dwlpSt] [Under] triple is the
    [aspSt] [Over] triple with the same pre- and postcondition
    ([PartCorr_galois_asp_over]), so each variant follows from its ASP
    counterpart. *)

From ExtLib Require Import Monad StateMonad.
From Incorrectness.Verification.Generic Require Import Triple InCorrectnessPrinciples.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import TriplesTaxonomy.

Section OHearnRewritingRules.
  Variable S : Type.

  Theorem first_symmetry_rule_1_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Under pre post1 /\ triple (@aspSt S) m Under pre post2) ->
      triple (@aspSt S) m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2 H. exact (first_symmetry_rule_1 (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem first_symmetry_rule_2_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      triple (@aspSt S) m Under pre (fun r => post1 r \/ post2 r) ->
      (triple (@aspSt S) m Under pre post1 /\ triple (@aspSt S) m Under pre post2).
  Proof.
    intros A m pre post1 post2 H. exact (first_symmetry_rule_2 (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem first_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Under pre post1 /\ triple (@aspSt S) m Under pre post2) <->
      triple (@aspSt S) m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2. split;
      [ apply first_symmetry_rule_1_asp | apply first_symmetry_rule_2_asp ].
  Qed.

  Theorem second_symmetry_rule_asp_1 :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Over pre post1 /\ triple (@aspSt S) m Over pre post2) ->
      triple (@aspSt S) m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 H. exact (second_symmetry_rule_1 (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem second_symmetry_rule_asp_2 :
    forall A (m : stdivndNE S A) pre post1 post2,
      triple (@aspSt S) m Over pre (fun r => post1 r /\ post2 r) ->
      (triple (@aspSt S) m Over pre post1 /\ triple (@aspSt S) m Over pre post2).
  Proof.
    intros A m pre post1 post2 H. exact (second_symmetry_rule_2 (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => pre (snd us)) post1 post2 H).
  Qed.

  Theorem second_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@aspSt S) m Over pre post1 /\ triple (@aspSt S) m Over pre post2) <->
      triple (@aspSt S) m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2. split;
      [ apply second_symmetry_rule_asp_1 | apply second_symmetry_rule_asp_2 ].
  Qed.

  Theorem first_imp_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre pre' post post',
      (triple (@aspSt S) m Under pre post /\
         (forall s, pre s -> pre' s) /\ (forall r, post' r -> post r)) ->
      triple (@aspSt S) m Under pre' post'.
  Proof.
    intros A m pre pre' post post' [H [Hpre Hpost]].
    exact (first_imp_symmetry_rule (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => pre (snd us)) (fun us => pre' (snd us)) post post'
             (conj H (conj (fun us => Hpre (snd us)) Hpost))).
  Qed.

  Theorem second_imp_symmetry_rule_asp :
    forall A (m : stdivndNE S A) pre pre' post post',
      (triple (@aspSt S) m Over pre post /\
         (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
      triple (@aspSt S) m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [H [Hpre Hpost]].
    exact (second_imp_symmetry_rule (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => pre (snd us)) (fun us => pre' (snd us)) post post'
             (conj H (conj (fun us => Hpre (snd us)) Hpost))).
  Qed.

  Theorem principle_of_agreement_asp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ triple (@aspSt S) m Over o o' /\
         (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hcor Himp]].
    exact (principle_of_agreement (fun (us : unit * S) r => outSt m (snd us) (Some r)) (fun us => u (snd us)) (fun us => o (snd us)) u' o'
             (conj Hinc (conj Hcor (fun us => Himp (snd us))))).
  Qed.

  Theorem principle_of_denial_asp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ (forall s, u s -> o s) /\
         ~ (forall r, u' r -> o' r)) -> ~ triple (@aspSt S) m Over o o'.
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hcor. apply Hnot.
    exact (principle_of_agreement_asp A m u u' o o' (conj Hinc (conj Hcor Himp))).
  Qed.

  (** *** The demonic liberal WP variants *)

  Theorem second_symmetry_rule_dwlp_1 :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@dwlpSt S) m Under pre post1 /\ triple (@dwlpSt S) m Under pre post2) ->
      triple (@dwlpSt S) m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2].
    apply (proj2 (PartCorr_galois_asp_over m pre _)).
    apply (second_symmetry_rule_asp_1 A m pre post1 post2).
    split; apply (proj1 (PartCorr_galois_asp_over m pre _)); assumption.
  Qed.

  Theorem second_symmetry_rule_dwlp_2 :
    forall A (m : stdivndNE S A) pre post1 post2,
      triple (@dwlpSt S) m Under pre (fun r => post1 r /\ post2 r) ->
      (triple (@dwlpSt S) m Under pre post1 /\ triple (@dwlpSt S) m Under pre post2).
  Proof.
    intros A m pre post1 post2 H.
    destruct (second_symmetry_rule_asp_2 A m pre post1 post2
                (proj1 (PartCorr_galois_asp_over m pre _) H)) as [H1 H2].
    split; apply (proj2 (PartCorr_galois_asp_over m pre _)); assumption.
  Qed.

  Theorem second_symmetry_rule_dwlp :
    forall A (m : stdivndNE S A) pre post1 post2,
      (triple (@dwlpSt S) m Under pre post1 /\ triple (@dwlpSt S) m Under pre post2) <->
      triple (@dwlpSt S) m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros. split; [ apply second_symmetry_rule_dwlp_1 | apply second_symmetry_rule_dwlp_2 ].
  Qed.

  Theorem second_imp_symmetry_rule_dwlp :
    forall A (m : stdivndNE S A) pre pre' post post',
      (triple (@dwlpSt S) m Under pre post /\
         (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
      triple (@aspSt S) m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [Hwp Hcons].
    apply (second_imp_symmetry_rule_asp A m pre pre' post post').
    split; [| exact Hcons ].
    exact (proj1 (PartCorr_galois_asp_over m pre post) Hwp).
  Qed.

  Theorem principle_of_agreement_dwlp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ triple (@dwlpSt S) m Under o o' /\
         (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hwp Himp]].
    apply (principle_of_agreement_asp A m u u' o o').
    exact (conj Hinc (conj (proj1 (PartCorr_galois_asp_over m o o') Hwp) Himp)).
  Qed.

  Theorem principle_of_denial_dwlp :
    forall A (m : stdivndNE S A) u u' o o',
      (triple (@aspSt S) m Under u u' /\ (forall s, u s -> o s) /\
         ~ (forall r, u' r -> o' r)) -> ~ triple (@dwlpSt S) m Under o o'.
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hwp. apply Hnot.
    exact (principle_of_agreement_dwlp A m u u' o o' (conj Hinc (conj Hwp Himp))).
  Qed.

End OHearnRewritingRules.
