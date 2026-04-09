(** * Galois connections among the Taxonomy spec types.

    Three connections, expressed via the lightweight [Galois] class
    from [Classes/Galois.v]:

    1. [Galois_Pred_PrePost] — existential abstraction
       (α : Pred → PrePost) paired with Cartesian concretization
       (γ : PrePost → Pred).  Both orders covariant.  Registered as
       the canonical [Galois PrePost Pred] instance.

    2. [Galois_Pred_PrePost_proj] — a *second* adjunction in the same
       direction as (1) but with a different choice of maps:
       [α R := (False, R)] (empty precondition) and [γ := snd]
       (forget the precondition).  Mathematically distinct from (1)
       (different [(α, γ)] pair); shares the class signature, so it
       is exposed as a [Definition] rather than an [Instance] to keep
       (1) the canonical typeclass instance.

    3. [Galois_PrePost_WPArr] — "weakest spec" abstraction
       (α : WPArr → PrePost) paired with demonic concretization
       (γ : PrePost → WPArr).  Mixed order on PrePost: covariant in
       pre, contravariant in post.  Pointwise order on WPArr. *)

From Coq Require Import Relation_Definitions RelationClasses Morphisms.
From Incorrectness.Classes Require Import Arrow Galois.
From Incorrectness Require Import
  Taxonomy.WP Taxonomy.WPFacts
  Taxonomy.Pred Taxonomy.PrePost Taxonomy.WPArr.

(* ================================================================= *)
(** ** Component-wise inclusion orders                                *)
(* ================================================================= *)

Definition Pred_le {A B} (R1 R2 : Pred A B) : Prop :=
  forall a b, R1 a b -> R2 a b.

#[global]
Instance Pred_le_PreOrder {A B} : PreOrder (@Pred_le A B).
Proof.
  constructor.
  - intros R a b H. exact H.
  - intros R1 R2 R3 H12 H23 a b H. apply H23, H12, H.
Qed.

(** Covariant in both components. *)
Definition PrePost_le {A B} (pq1 pq2 : PrePost A B) : Prop :=
  (forall a,   fst pq1 a   -> fst pq2 a) /\
  (forall a b, snd pq1 a b -> snd pq2 a b).

#[global]
Instance PrePost_le_PreOrder {A B} : PreOrder (@PrePost_le A B).
Proof.
  constructor.
  - intros [P R]. split; intros; assumption.
  - intros [P1 R1] [P2 R2] [P3 R3] [HP12 HR12] [HP23 HR23].
    split; intros.
    + apply HP23, HP12, H.
    + apply HR23, HR12, H.
Qed.

(** Mixed: covariant in pre, contravariant in post — the demonic
    refinement order. *)
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
(** ** [Galois_Pred_PrePost]: existential abstraction                 *)
(* ================================================================= *)

(** [α] is the existential projection: pre is the domain of [R],
    relation is [R] itself.  [γ] is the Cartesian concretization. *)
Definition alpha_Pred_PrePost {A B} (R : Pred A B) : PrePost A B :=
  (fun a => exists b, R a b, R).

Definition gamma_PrePost_Pred {A B} (pq : PrePost A B) : Pred A B :=
  fun a b => fst pq a /\ snd pq a b.

Lemma adjunction_Pred_PrePost {A B}
  (R : Pred A B) (pq : PrePost A B) :
  PrePost_le (alpha_Pred_PrePost R) pq <->
  Pred_le R (gamma_PrePost_Pred pq).
Proof.
  unfold PrePost_le, Pred_le, alpha_Pred_PrePost, gamma_PrePost_Pred; simpl.
  split.
  - intros [HP HR] a b Hab. split.
    + apply HP. exists b. exact Hab.
    + apply HR. exact Hab.
  - intros H. split.
    + intros a [b Hab]. exact (proj1 (H a b Hab)).
    + intros a b Hab. exact (proj2 (H a b Hab)).
Qed.

#[global]
Instance Galois_Pred_PrePost
  : Galois PrePost Pred (@PrePost_le) (@Pred_le) :=
{
  galois_alpha := @alpha_Pred_PrePost ;
  galois_gamma := @gamma_PrePost_Pred ;
  galois_adjunction := @adjunction_Pred_PrePost
}.

(* ================================================================= *)
(** ** [Galois_Pred_PrePost_proj]: forget the precondition            *)
(* ================================================================= *)

(** A second Galois adjunction between [Pred] and [PrePost] in the
    *same* direction as [Galois_Pred_PrePost] above (α : Pred →
    PrePost), but capturing a different abstraction:

    - [α R := (False, R)] equips the relation with the empty
      precondition;
    - [γ pq := snd pq] forgets the precondition (projects out the
      post-relation).

    The adjunction holds because the [(False → fst pq)] conjunct in
    [PrePost_le (False, R) pq] is vacuously true, leaving exactly
    [R ⊆ snd pq] on both sides — symmetric to how the [(P → True)]
    conjunct of the dual ([forget_pre ⊣ trivial_pre]) collapses to
    the same shape. *)
Definition empty_pre {A B} (R : Pred A B) : PrePost A B :=
  (fun _ => False, R).

Definition forget_pre {A B} (pq : PrePost A B) : Pred A B := snd pq.

Lemma adjunction_Pred_PrePost_proj {A B}
  (R : Pred A B) (pq : PrePost A B) :
  PrePost_le (empty_pre R) pq <->
  Pred_le R (forget_pre pq).
Proof.
  destruct pq as [P R'].
  unfold PrePost_le, Pred_le, empty_pre, forget_pre; simpl.
  split.
  - intros [_ HR]. exact HR.
  - intros HR. split; [intros _ []| exact HR].
Qed.

(** Exposed as a [Definition] (not [Instance]) so that
    [Galois_Pred_PrePost] above remains the canonical typeclass
    instance for [Galois PrePost Pred].  Use this connection
    explicitly when you specifically want the projection
    abstraction. *)
Definition Galois_Pred_PrePost_proj
  : Galois PrePost Pred (@PrePost_le) (@Pred_le) :=
{|
  galois_alpha := @empty_pre ;
  galois_gamma := @forget_pre ;
  galois_adjunction := @adjunction_Pred_PrePost_proj
|}.

(* ================================================================= *)
(** ** [Galois_PrePost_WPArr]: demonic WP / weakest spec              *)
(* ================================================================= *)

(** Concretization sends a Hoare-style pair [(P, R)] to the demonic
    weakest precondition transformer
    [fun a Q => P a /\ forall b, R a b -> Q b].

    Abstraction sends a WP transformer [w] to the pair "[w] accepts
    something at [a]" / "[b] is in every [Q] that [w] accepts at [a]".

    The adjunction holds **without any monotonicity or atomicity
    assumption on [w]** — it is an exact bi-implication.  This uses
    [PrePost_le_dem] (mixed order) to make the [γ] map monotone. *)
Definition gamma_PrePost_WPArr {A B} (pq : PrePost A B) : WPArr A B :=
  fun a Q => fst pq a /\ (forall b, snd pq a b -> Q b).

Definition alpha_WPArr_PrePost {A B} (w : WPArr A B) : PrePost A B :=
  ( fun a   => exists Q, w a Q
  , fun a b => forall Q, w a Q -> Q b ).

Lemma adjunction_PrePost_WPArr {A B}
  (w : WPArr A B) (pq : PrePost A B) :
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

#[global]
Instance Galois_PrePost_WPArr
  : Galois PrePost WPArr (@PrePost_le_dem) (@WPArr_le) :=
{
  galois_alpha := @alpha_WPArr_PrePost ;
  galois_gamma := @gamma_PrePost_WPArr ;
  galois_adjunction := @adjunction_PrePost_WPArr
}.
