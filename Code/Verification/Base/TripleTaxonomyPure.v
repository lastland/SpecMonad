(** * The four WP readings of one base computation

    The WP edges of Verscht and Kaminski's diagram between the base readings
    of one element of [divndNE], and the Galois edges between a base WP
    reading and the terminating outcomes ([galois_slice_dwlpPure],
    [galois_awpPure_slice]).  Four of the WP implications go from a demonic
    to an angelic reading and need the computation to have an outcome;
    every element of [divndNE] has one.  The diagram is assembled with state
    in [State/TripleTaxonomySt.v]. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Import SPostArr DSPASLPArr.
From Incorrectness.PTMonadTaxonomy Require Import TransformerRelations.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.PTMonadTaxonomy Require Import
  Carriers MonadTaxonomy.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Generic Require Import TripleTaxonomy.
From Incorrectness.Verification.Base Require Import DivNonDetNE.
From Incorrectness.Verification.Base Require Import MorphismsPure.
From Incorrectness.Verification.Base Require Import TriplesPure.


(* ================================================================= *)
(** * The four WP readings of one base computation                   *)
(* ================================================================= *)

Section BaseWP.
  Context {X : Type} (d : divndNE X).

  Lemma dwpPure_incl_dwlpPure :
    pt_incl (spec_read (dwpPure d)) (spec_read (dwlpPure d)).
  Proof.
    intros Q u H oa Ho. specialize (H oa Ho).
    destruct oa; [ exact H | exact I ].
  Qed.

  Lemma awpPure_incl_awlpPure :
    pt_incl (spec_read (awpPure d)) (spec_read (awlpPure d)).
  Proof.
    intros Q u [oa [Ho H]]. exists oa. split; [ exact Ho |].
    destruct oa; [ exact H | exact I ].
  Qed.

  Lemma dwpPure_incl_awpPure :
    pt_incl (spec_read (dwpPure d)) (spec_read (awpPure d)).
  Proof.
    intros Q u H. destruct (getNE_nonEmpty d) as [oa Ho].
    exists oa. exact (conj Ho (H oa Ho)).
  Qed.

  Lemma dwlpPure_incl_awlpPure :
    pt_incl (spec_read (dwlpPure d)) (spec_read (awlpPure d)).
  Proof.
    intros Q u H. destruct (getNE_nonEmpty d) as [oa Ho].
    exists oa. exact (conj Ho (H oa Ho)).
  Qed.

  (** A demonic reading is the contrapositive of the angelic reading that
      counts divergence the other way.  Classical. *)
  Lemma demonic_contra (div div' : Prop) (Hd : div <-> ~ div') (Q : X -> Prop) :
    demonic div d Q <-> ~ angelic div' d (fun a => ~ Q a).
  Proof.
    split.
    - intros H [oa [Ho Hm]]. specialize (H oa Ho).
      destruct oa; [ exact (Hm H) | exact (proj1 Hd H Hm) ].
    - intros Hn oa Ho. destruct oa as [a|].
      + apply NNPP. intro HnQ. apply Hn. exists (Some a). exact (conj Ho HnQ).
      + apply (proj2 Hd). intro Hdiv. apply Hn. exists None. exact (conj Ho Hdiv).
  Qed.

  Lemma angelic_contra (div div' : Prop) (Hd : div <-> ~ div') (Q : X -> Prop) :
    angelic div d Q <-> ~ demonic div' d (fun a => ~ Q a).
  Proof.
    split.
    - intros [oa [Ho Hm]] Hdem. specialize (Hdem oa Ho).
      destruct oa; [ exact (Hdem Hm) | exact (proj1 Hd Hm Hdem) ].
    - intro Hn. apply NNPP. intro Hna. apply Hn. intros oa Ho.
      destruct oa as [a|].
      + intro Hq. apply Hna. exists (Some a). exact (conj Ho Hq).
      + apply NNPP. intro Hnd. apply Hna. exists None.
        exact (conj Ho (proj2 Hd Hnd)).
  Qed.

  Lemma awpPure_contra_dwlpPure :
    pt_contra (spec_read (awpPure d)) (spec_read (dwlpPure d)).
  Proof.
    intros Q u.
    exact (angelic_contra False True (conj (fun f _ => f) (fun n => n I)) Q).
  Qed.

  Lemma awlpPure_contra_dwpPure :
    pt_contra (spec_read (awlpPure d)) (spec_read (dwpPure d)).
  Proof.
    intros Q u.
    exact (angelic_contra True False (conj (fun _ f => f) (fun _ => I)) Q).
  Qed.

  Lemma dwpPure_contra_awlpPure :
    pt_contra (spec_read (dwpPure d)) (spec_read (awlpPure d)).
  Proof.
    intros Q u.
    exact (demonic_contra False True (conj (fun f _ => f) (fun n => n I)) Q).
  Qed.

  Lemma dwlpPure_contra_awpPure :
    pt_contra (spec_read (dwlpPure d)) (spec_read (awpPure d)).
  Proof.
    intros Q u.
    exact (demonic_contra True False (conj (fun _ f => f) (fun _ => I)) Q).
  Qed.

  (** The two Galois relations of [MonadTaxonomy.v], between the terminating
      outcomes and a WP reading. *)
  Lemma galois_slice_dwlpPure : GaloisPredWP (sliceNE d) (dwlpPure d).
  Proof.
    intro Q. split.
    - intros H a Ha. exact (H (Some a) Ha).
    - intros H [a|] Ho; [ exact (H a Ho) | exact I ].
  Qed.

  Lemma galois_awpPure_slice : GaloisWPPred (awpPure d) (sliceNE d).
  Proof.
    intro Q. split.
    - intros [[a|] [Ho H]]; [ exists a; exact (conj Ho H) | destruct H ].
    - intros [a [Ho H]]. exists (Some a). exact (conj Ho H).
  Qed.
End BaseWP.
