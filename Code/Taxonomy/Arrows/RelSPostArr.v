(** * Strongest-postcondition readings of the relational arrow.

    An arrow is a [Rel A B] relation. Its predicate transformer is derived
    from that relation using one of two readings:

    [asp R pre b = exists a, pre a /\ R a b]   (angelic / existential)
    [dslp R pre b = forall a, R a b -> pre a]  (demonic liberal / universal)

    The carrier, arrow operations, laws, and option/state stacks come from
    [Rel.v]. In particular, [optionRel] and [progRelArr] use the same
    relational operations for both readings. At an unreachable output,
    [asp] is false and [dslp] is vacuously true.

    [SPostArr.v] gives the property-only transformer presentation;
    [SPostArrEquiv.v] relates it to [Rel], preserving each reading and the
    arrow operations through the option and state transformers. *)

From Coq Require Import Classical_Prop.
From Incorrectness.Taxonomy.Arrows Require Export Rel.

(** ** Angelic strongest postcondition *)

Definition asp {A B} (R : Rel A B) (pre : A -> Prop) : B -> Prop :=
  fun b => exists a, pre a /\ R a b.

(** Evaluating singleton preconditions recovers the relation. The reverse
    round trip below applies to transformers in the image of [asp]. *)
Definition asp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : Rel A B :=
  fun a b => pt (fun a' => a = a') b.

Theorem asp_asp_inv : forall {A B} (R : Rel A B) a b,
    asp_inv (asp R) a b <-> R a b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? ?]]. subst. assumption.
  - intros. exists a. tauto.
Qed.

(** [asp] at the singleton precondition [eq a] recovers [R] at [a]. *)
Corollary asp_singleton : forall {A B} (R : Rel A B) (a : A) (b : B),
    asp R (eq a) b <-> R a b.
Proof.
  intros. unfold asp. split.
  - intros [a' [<- H]]. exact H.
  - intro H. exists a. auto.
Qed.

Theorem asp_inv_asp : forall {A B} (R : Rel A B) pre b,
    asp (asp_inv (asp R)) pre b <-> asp R pre b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? [? [? ?]]]]. subst.
    exists x0. tauto.
  - intros [? [? ?]].
    exists x. split; [assumption |].
    exists x. tauto.
Qed.

(** ** Demonic strongest liberal postcondition *)

Definition dslp {A B} (R : Rel A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

(** Intersecting all preconditions accepted at [b] recovers its
    predecessors. The reverse round trip applies to the image of [dslp]. *)
Definition dslp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : Rel A B :=
  fun a b => forall pre, pt pre b -> pre a.

Theorem dslp_dslp_inv : forall {A B} (R : Rel A B) a b,
    dslp_inv (dslp R) a b <-> R a b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros ?. apply H. auto.
  - intros. auto.
Qed.

Theorem dslp_inv_dslp : forall {A B} (R : Rel A B) pre b,
    dslp (dslp_inv (dslp R)) pre b <-> dslp R pre b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros. apply H; intros. auto.
  - intros. apply H0. apply H.
Qed.

(** ** Characterizations of DSP and ASLP

    Reference: Lena Verscht and Benjamin Lucien Kaminski,
    "A Taxonomy of Hoare-Like Logics: Towards a Holistic View using
    Predicate Transformers and Kleene Algebras with Top and Tests",
    POPL 2025, https://doi.org/10.1145/3704896.

    Their four SP readings use the same reachability relation:

    - [asp]: existential (angelic, total)
    - [dslp]: universal (demonic, liberal)
    - DSP: [asp /\ dslp] (demonic, total)
    - ASLP: [asp \/ dslp] (angelic, liberal)

    These characterizations match Verscht and Kaminski's Definitions 3.5
    and 3.6, which guard the quantifier by whether the inverse image is
    empty. Their §3.2.4 gives the conjunction/disjunction identities. *)

Section SPCharacterizations.

  Variables A B : Type.
  Variable R : Rel A B.

  Theorem dsp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, R a b) /\ forall a, R a b -> pre a) <->
    (asp R pre b /\ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [[a0 HRa0] Hall].
      split; [exists a0; auto | exact Hall].
    - intros [[a0 [Hpre HRa0]] Hall].
      split; [exists a0; exact HRa0 | exact Hall].
  Qed.

  Theorem aslp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, pre a /\ R a b) \/ ~ exists a, R a b) <->
    (asp R pre b \/ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [Hsp | Hunreach].
      + left. exact Hsp.
      + right. intros a HRab. exfalso. apply Hunreach. exists a. exact HRab.
    - intros [Hsp | Hdp].
      + left. exact Hsp.
      + destruct (classic (exists a, R a b)) as [[a0 HRa0] | Hunreach].
        * left. exists a0. split; [exact (Hdp a0 HRa0) | exact HRa0].
        * right. exact Hunreach.
  Qed.

End SPCharacterizations.
