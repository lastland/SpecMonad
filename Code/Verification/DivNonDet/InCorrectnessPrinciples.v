(** * O'Hearn-style rewriting rules, without state

    The rules of [Generic/InCorrectnessPrinciples.v] for the ASP triples of
    the base computations, [triple (@aspPure)]: [Under] is the incorrectness
    triple and [Over] the correctness one.  The correctness-side rules also
    have a variant for the demonic liberal WP triples, [triple (@dwlpPure)],
    through the Galois edge [PartCorr_galois_asp_over_pure]. *)

From ExtLib Require Import Monad OptionMonad.
From Incorrectness.Verification.Generic Require Import Triple InCorrectnessPrinciples.
From Incorrectness.Verification.DivNonDet Require Import Computation Morphisms Triples TriplesTaxonomy.

Theorem first_symmetry_rule_1_aspPure :
  forall A (d : divndNE A) pre post1 post2,
    (triple (@aspPure) d Under pre post1 /\ triple (@aspPure) d Under pre post2) ->
    triple (@aspPure) d Under pre (fun r => post1 r \/ post2 r).
Proof.
  intros A d pre post1 post2 H. exact (first_symmetry_rule_1 (fun (_ : unit) a => unOptionT (getNE d) (Some a)) pre post1 post2 H).
Qed.

Theorem first_symmetry_rule_2_aspPure :
  forall A (d : divndNE A) pre post1 post2,
    triple (@aspPure) d Under pre (fun r => post1 r \/ post2 r) ->
    (triple (@aspPure) d Under pre post1 /\ triple (@aspPure) d Under pre post2).
Proof.
  intros A d pre post1 post2 H. exact (first_symmetry_rule_2 (fun (_ : unit) a => unOptionT (getNE d) (Some a)) pre post1 post2 H).
Qed.

Theorem first_symmetry_rule_aspPure :
  forall A (d : divndNE A) pre post1 post2,
    (triple (@aspPure) d Under pre post1 /\ triple (@aspPure) d Under pre post2) <->
    triple (@aspPure) d Under pre (fun r => post1 r \/ post2 r).
Proof.
  intros A d pre post1 post2. split;
    [ apply first_symmetry_rule_1_aspPure | apply first_symmetry_rule_2_aspPure ].
Qed.

Theorem second_symmetry_rule_aspPure_1 :
  forall A (d : divndNE A) pre post1 post2,
    (triple (@aspPure) d Over pre post1 /\ triple (@aspPure) d Over pre post2) ->
    triple (@aspPure) d Over pre (fun r => post1 r /\ post2 r).
Proof.
  intros A d pre post1 post2 H. exact (second_symmetry_rule_1 (fun (_ : unit) a => unOptionT (getNE d) (Some a)) pre post1 post2 H).
Qed.

Theorem second_symmetry_rule_aspPure_2 :
  forall A (d : divndNE A) pre post1 post2,
    triple (@aspPure) d Over pre (fun r => post1 r /\ post2 r) ->
    (triple (@aspPure) d Over pre post1 /\ triple (@aspPure) d Over pre post2).
Proof.
  intros A d pre post1 post2 H. exact (second_symmetry_rule_2 (fun (_ : unit) a => unOptionT (getNE d) (Some a)) pre post1 post2 H).
Qed.

Theorem second_symmetry_rule_aspPure :
  forall A (d : divndNE A) pre post1 post2,
    (triple (@aspPure) d Over pre post1 /\ triple (@aspPure) d Over pre post2) <->
    triple (@aspPure) d Over pre (fun r => post1 r /\ post2 r).
Proof.
  intros A d pre post1 post2. split;
    [ apply second_symmetry_rule_aspPure_1 | apply second_symmetry_rule_aspPure_2 ].
Qed.

Theorem first_imp_symmetry_rule_aspPure :
  forall A (d : divndNE A) pre pre' post post',
    (triple (@aspPure) d Under pre post /\
       (forall s, pre s -> pre' s) /\ (forall r, post' r -> post r)) ->
    triple (@aspPure) d Under pre' post'.
Proof.
  intros A d pre pre' post post' [H [Hpre Hpost]].
  exact (first_imp_symmetry_rule (fun (_ : unit) a => unOptionT (getNE d) (Some a)) pre pre' post post'
           (conj H (conj Hpre Hpost))).
Qed.

Theorem second_imp_symmetry_rule_aspPure :
  forall A (d : divndNE A) pre pre' post post',
    (triple (@aspPure) d Over pre post /\
       (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
    triple (@aspPure) d Over pre' post'.
Proof.
  intros A d pre pre' post post' [H [Hpre Hpost]].
  exact (second_imp_symmetry_rule (fun (_ : unit) a => unOptionT (getNE d) (Some a)) pre pre' post post'
           (conj H (conj Hpre Hpost))).
Qed.

Theorem principle_of_agreement_aspPure :
  forall A (d : divndNE A) u u' o o',
    (triple (@aspPure) d Under u u' /\ triple (@aspPure) d Over o o' /\
       (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
Proof.
  intros A d u u' o o' [Hinc [Hcor Himp]].
  exact (principle_of_agreement (fun (_ : unit) a => unOptionT (getNE d) (Some a)) u o u' o'
           (conj Hinc (conj Hcor Himp))).
Qed.

Theorem principle_of_denial_aspPure :
  forall A (d : divndNE A) u u' o o',
    (triple (@aspPure) d Under u u' /\ (forall s, u s -> o s) /\
       ~ (forall r, u' r -> o' r)) -> ~ triple (@aspPure) d Over o o'.
Proof.
  intros A d u u' o o' [Hinc [Himp Hnot]] Hcor. apply Hnot.
  exact (principle_of_agreement_aspPure A d u u' o o' (conj Hinc (conj Hcor Himp))).
Qed.

(** *** The demonic liberal WP variants *)

Theorem second_symmetry_rule_dwlpPure_1 :
  forall A (d : divndNE A) pre post1 post2,
    (triple (@dwlpPure) d Under pre post1 /\ triple (@dwlpPure) d Under pre post2) ->
    triple (@dwlpPure) d Under pre (fun r => post1 r /\ post2 r).
Proof.
  intros A d pre post1 post2 [H1 H2].
  apply (proj2 (PartCorr_galois_asp_over_pure d pre _)).
  apply (second_symmetry_rule_aspPure_1 A d pre post1 post2).
  split; apply (proj1 (PartCorr_galois_asp_over_pure d pre _)); assumption.
Qed.

Theorem second_symmetry_rule_dwlpPure_2 :
  forall A (d : divndNE A) pre post1 post2,
    triple (@dwlpPure) d Under pre (fun r => post1 r /\ post2 r) ->
    (triple (@dwlpPure) d Under pre post1 /\ triple (@dwlpPure) d Under pre post2).
Proof.
  intros A d pre post1 post2 H.
  destruct (second_symmetry_rule_aspPure_2 A d pre post1 post2
              (proj1 (PartCorr_galois_asp_over_pure d pre _) H)) as [H1 H2].
  split; apply (proj2 (PartCorr_galois_asp_over_pure d pre _)); assumption.
Qed.

Theorem second_symmetry_rule_dwlpPure :
  forall A (d : divndNE A) pre post1 post2,
    (triple (@dwlpPure) d Under pre post1 /\ triple (@dwlpPure) d Under pre post2) <->
    triple (@dwlpPure) d Under pre (fun r => post1 r /\ post2 r).
Proof.
  intros. split; [ apply second_symmetry_rule_dwlpPure_1 | apply second_symmetry_rule_dwlpPure_2 ].
Qed.

Theorem second_imp_symmetry_rule_dwlpPure :
  forall A (d : divndNE A) pre pre' post post',
    (triple (@dwlpPure) d Under pre post /\
       (forall s, pre' s -> pre s) /\ (forall r, post r -> post' r)) ->
    triple (@aspPure) d Over pre' post'.
Proof.
  intros A d pre pre' post post' [Hwp Hcons].
  apply (second_imp_symmetry_rule_aspPure A d pre pre' post post').
  split; [| exact Hcons ].
  exact (proj1 (PartCorr_galois_asp_over_pure d pre post) Hwp).
Qed.

Theorem principle_of_agreement_dwlpPure :
  forall A (d : divndNE A) u u' o o',
    (triple (@aspPure) d Under u u' /\ triple (@dwlpPure) d Under o o' /\
       (forall s, u s -> o s)) -> (forall r, u' r -> o' r).
Proof.
  intros A d u u' o o' [Hinc [Hwp Himp]].
  apply (principle_of_agreement_aspPure A d u u' o o').
  exact (conj Hinc (conj (proj1 (PartCorr_galois_asp_over_pure d o o') Hwp) Himp)).
Qed.

Theorem principle_of_denial_dwlpPure :
  forall A (d : divndNE A) u u' o o',
    (triple (@aspPure) d Under u u' /\ (forall s, u s -> o s) /\
       ~ (forall r, u' r -> o' r)) -> ~ triple (@dwlpPure) d Under o o'.
Proof.
  intros A d u u' o o' [Hinc [Himp Hnot]] Hwp. apply Hnot.
  exact (principle_of_agreement_dwlpPure A d u u' o o' (conj Hinc (conj Hwp Himp))).
Qed.
