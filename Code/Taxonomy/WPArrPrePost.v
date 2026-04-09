(** * Galois connection between [PrePost] and [WPArr].

    Concretization sends a Hoare-style pre/post pair [(P, R)] to the
    demonic weakest precondition transformer
    [fun a Q => P a /\ forall b, R a b -> Q b].

    Abstraction sends a WP transformer [w] to the pair
    [(fun a => exists Q, w a Q, fun a b => forall Q, w a Q -> Q b)]:
    pre is "[w] accepts something at [a]", relation is "[b] is in
    every [Q] that [w] accepts at [a]".

    The Galois adjunction holds **without any monotonicity or
    atomicity assumption on [w]** — it is an exact bi-implication.

    Note: the order on [PrePost] used here is *different* from the one
    used in [Pred ↔ PrePost] (defined in [Taxonomy/PrePost.v]).  Here
    the post-relation is **contravariant** (a stronger spec has a
    smaller relation), matching the demonic interpretation. *)

From Coq Require Import RelationClasses Morphisms.
From Incorrectness.Classes Require Import Arrow Galois.
From Incorrectness Require Import
  Taxonomy.WP Taxonomy.WPFacts Taxonomy.WPArr Taxonomy.PrePost.

(* ================================================================= *)
(** ** Orderings                                                      *)
(* ================================================================= *)

Definition PrePost_le_dem {A B} (pq1 pq2 : PrePost A B) : Prop :=
  (forall a,   fst pq1 a   -> fst pq2 a) /\
  (forall a b, snd pq2 a b -> snd pq1 a b).

#[global]
Instance PrePost_le_dem_PreOrder {A B}
  : PreOrder (@PrePost_le_dem A B).
Proof.
  constructor.
  - intros [P R]. split; intros; assumption.
  - intros [P1 R1] [P2 R2] [P3 R3] [HP12 HR12] [HP23 HR23].
    split; intros.
    + apply HP23, HP12. assumption.
    + apply HR12, HR23. assumption.
Qed.

Definition WPArr_le {A B} (w1 w2 : WPArr A B) : Prop :=
  forall a Q, w1 a Q -> w2 a Q.

#[global]
Instance WPArr_le_PreOrder {A B} : PreOrder (@WPArr_le A B).
Proof. constructor; cbv; auto. Qed.

(* ================================================================= *)
(** ** Concretization and abstraction                                 *)
(* ================================================================= *)

Definition gamma_PrePost_WPArr {A B} (pq : PrePost A B) : WPArr A B :=
  fun a Q => fst pq a /\ (forall b, snd pq a b -> Q b).

Definition alpha_WPArr_PrePost {A B} (w : WPArr A B) : PrePost A B :=
  ( fun a   => exists Q, w a Q
  , fun a b => forall Q, w a Q -> Q b ).

(* ================================================================= *)
(** ** Adjunction                                                     *)
(* ================================================================= *)

Lemma adjunction_PrePost_WPArr {A B} (w : WPArr A B) (pq : PrePost A B) :
  PrePost_le_dem (alpha_WPArr_PrePost w) pq <->
  WPArr_le w (gamma_PrePost_WPArr pq).
Proof.
  destruct pq as [P R].
  unfold PrePost_le_dem, WPArr_le, alpha_WPArr_PrePost, gamma_PrePost_WPArr.
  cbn.
  split.
  - intros [HP HR] a Q HwQ. split.
    + apply HP. exists Q. exact HwQ.
    + intros b HRb. exact (HR a b HRb Q HwQ).
  - intros H. split.
    + intros a [Q HwQ]. exact (proj1 (H a Q HwQ)).
    + intros a b HRb Q HwQ. exact (proj2 (H a Q HwQ) b HRb).
Qed.

(* ================================================================= *)
(** ** [Galois] instance                                              *)
(* ================================================================= *)

#[global]
Instance Galois_PrePost_WPArr
  : Galois PrePost WPArr (@PrePost_le_dem) (@WPArr_le) :=
{
  galois_alpha := @alpha_WPArr_PrePost ;
  galois_gamma := @gamma_PrePost_WPArr ;
  galois_adjunction := @adjunction_PrePost_WPArr
}.
