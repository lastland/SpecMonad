(** * Galois connections among the Taxonomy spec types.

    The canonical orders used here are:

    - [Pred_le R1 R2 := R1 ⊆ R2]: covariant inclusion on relations.

    - [PrePost_le]: partial-correctness Hoare order on pre/post pairs.
      [pq1 ≤ pq2] iff [fst pq2 ⊆ fst pq1] (strengthen the
      precondition) and [snd pq1 ⊆ snd pq2] (weaken the
      post-relation).

    - [WPArr_le w1 w2 := ∀ a Q, w1 a Q → w2 a Q]: pointwise
      implication on WP transformers.

    Three Galois connections are exposed:

    1. [Galois_Pred_PrePost] (primary) — [α R := (True, R)] paired
       with [γ pq := snd pq].  Under the Hoare order, the [True]
       precondition is the bottom of [fst]: [fst pq ⊆ True] holds
       trivially for every [pq], so the pre check dissolves and the
       adjunction reduces to [R ⊆ snd pq], matching [Pred_le R (snd pq)]
       under the covariant [Pred_le].

    2. [Galois_RelPrePost_WPArr]: Yoneda abstraction.  Pointwise
       orders on both sides; does not touch [PrePost_le] or [Pred_le].

    A False-pre alternative (for completeness — kept as a standalone
    lemma, not registered as a [Galois] instance because the order it
    requires conflicts with the global [PrePost_le] / [Pred_le]):

    - [adjunction_Pred_PrePost_False] uses the *Dijkstra refinement*
      duals [PrePost_le_dij] and [Pred_le_contra] (defined locally
      below) to recover the original empty-pre / forget-pre
      adjunction.  Under those duals, [False] is the bottom of [fst],
      and the pre check vacuously dissolves on the [α] side.

    The PrePost ↔ WPArr Galois ([Galois_PrePost_WPArr]) is also
    stated against the local Dijkstra-order alias [PrePost_le_dij]:
    its existential α / demonic γ pair is monotone under Dijkstra
    refinement but not under the Hoare order.  Re-deriving an
    angelic-style PrePost ↔ WPArr adjunction under the Hoare order
    is left as future work.

    **Variants that do not survive cleanly**:

    - The existential [α R := (fun a => ∃ b, R a b, R)] paired with
      Cartesian [γ (P, R) := λ a b. P a ∧ R a b].  The "domain of R
      ⊆ P" conjunct on the α side cannot be recovered from the γ side
      when [P] is empty outside the domain of [R]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Relation_Definitions RelationClasses Morphisms.
From Incorrectness.Classes Require Import Arrow Galois.
From Incorrectness Require Import
  Taxonomy.WP Taxonomy.WPFacts
  Taxonomy.Pred Taxonomy.PrePost Taxonomy.WPArr Taxonomy.RelPrePost.

(** The orders [Pred_le] (covariant), [PrePost_le] (Hoare),
    [WPArr_le], and [RelPrePost_le] live in the respective type
    files: [Taxonomy/Pred.v], [Taxonomy/PrePost.v], [Taxonomy/WPArr.v],
    and [Taxonomy/RelPrePost.v]. *)

(* ================================================================= *)
(** ** [Galois_Pred_PrePost]: full-pre / forget-pre (primary)         *)
(* ================================================================= *)

(** [α] equips a relation with the trivially-true (True) precondition;
    [γ] forgets the precondition and keeps only the post-relation.

    Under the Hoare order on [PrePost], [True] is the bottom of [fst]:
    [fst pq ⊆ True] holds for every [pq], so the pre check in
    [PrePost_le (True, R) pq] dissolves and the adjunction reduces to
    [R ⊆ snd pq], which is exactly [Pred_le R (snd pq)] under the
    covariant [Pred_le]. *)

Definition full_pre {A B} (R : Pred A B) : PrePost A B :=
  (fun _ => True, R).

Definition forget_pre {A B} (pq : PrePost A B) : Pred A B := snd pq.

Lemma adjunction_Pred_PrePost {A B}
  (R : Pred A B) (pq : PrePost A B) :
  PrePost_le (full_pre R) pq <-> Pred_le R (forget_pre pq).
Proof.
  destruct pq as [P R'].
  unfold PrePost_le, Pred_le, full_pre, forget_pre; cbn.
  split.
  - intros [_ HR]. exact HR.
  - intros HR. split; [intros _ _; exact I | exact HR].
Qed.

#[global]
Instance Galois_Pred_PrePost
  : Galois PrePost Pred (@PrePost_le) (@Pred_le) :=
{
  galois_alpha := @full_pre ;
  galois_gamma := @forget_pre ;
  galois_adjunction := @adjunction_Pred_PrePost
}.

(* ================================================================= *)
(** ** Alternative: False-pre under Dijkstra refinement               *)
(* ================================================================= *)

(** Local duals of the global orders, recovering the original
    Dijkstra-refinement view: [PrePost_le_dij] weakens the pre and
    strengthens the post, [Pred_le_contra] is contravariant inclusion
    on relations.  These exist here only to state the False-pre
    adjunction; they are intentionally *not* registered as
    [PreOrder] / [Galois] instances (that would conflict with the
    global [PrePost_le] / [Pred_le]). *)

Definition PrePost_le_dij {A B} (pq1 pq2 : PrePost A B) : Prop :=
  (forall a,   fst pq1 a   -> fst pq2 a) /\
  (forall a b, snd pq2 a b -> snd pq1 a b).

#[global]
Instance PrePost_le_dij_PreOrder {A B} : PreOrder (@PrePost_le_dij A B).
Proof.
  constructor.
  - intros [P R]. split; intros; assumption.
  - intros [P1 R1] [P2 R2] [P3 R3] [HP12 HR12] [HP23 HR23].
    split; intros.
    + apply HP23, HP12. assumption.
    + apply HR12, HR23. assumption.
Qed.

Definition Pred_le_contra {A B} (R1 R2 : Pred A B) : Prop :=
  forall a b, R2 a b -> R1 a b.

Definition empty_pre {A B} (R : Pred A B) : PrePost A B :=
  (fun _ => False, R).

(** Under the Dijkstra duals, [False] is the bottom of [fst]:
    [(False → fst pq)] holds trivially, so the pre check dissolves
    and the adjunction reduces to [snd pq ⊆ R]. *)
Lemma adjunction_Pred_PrePost_False {A B}
  (R : Pred A B) (pq : PrePost A B) :
  PrePost_le_dij (empty_pre R) pq <-> Pred_le_contra R (forget_pre pq).
Proof.
  destruct pq as [P R'].
  unfold PrePost_le_dij, Pred_le_contra, empty_pre, forget_pre; cbn.
  split.
  - intros [_ HR]. exact HR.
  - intros HR. split; [intros _ []| exact HR].
Qed.

(* ================================================================= *)
(** ** [Galois_PrePost_WPArr]: demonic WP / weakest spec              *)
(* ================================================================= *)

(** Concretization sends a Hoare-style pair [(P, R)] to the demonic
    weakest precondition transformer
    [fun a Q => P a /\ forall b, R a b -> Q b].

    Abstraction sends a WP transformer [w] to the pair "[w] accepts
    something at [a]" / "[b] is in every [Q] that [w] accepts at [a]".

    The existential α / demonic γ pair is monotone under *Dijkstra
    refinement* on [PrePost], not under the Hoare order used as the
    project-wide [PrePost_le].  We therefore state this Galois
    connection against the local [PrePost_le_dij] alias.  A
    Hoare-order-native version (likely angelic γ) is left as future
    work. *)

Definition gamma_PrePost_WPArr {A B} (pq : PrePost A B) : WPArr A B :=
  fun a Q => fst pq a /\ (forall b, snd pq a b -> Q b).

Definition alpha_WPArr_PrePost {A B} (w : WPArr A B) : PrePost A B :=
  ( fun a   => exists Q, w a Q
  , fun a b => forall Q, w a Q -> Q b ).

Lemma adjunction_PrePost_WPArr {A B}
  (w : WPArr A B) (pq : PrePost A B) :
  PrePost_le_dij (alpha_WPArr_PrePost w) pq <->
  WPArr_le w (gamma_PrePost_WPArr pq).
Proof.
  destruct pq as [P R].
  unfold PrePost_le_dij, WPArr_le, alpha_WPArr_PrePost, gamma_PrePost_WPArr.
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
  : Galois PrePost WPArr (@PrePost_le_dij) (@WPArr_le) :=
{
  galois_alpha := @alpha_WPArr_PrePost ;
  galois_gamma := @gamma_PrePost_WPArr ;
  galois_adjunction := @adjunction_PrePost_WPArr
}.

(* ================================================================= *)
(** ** [Galois_RelPrePost_WPArr]: Yoneda abstraction                  *)
(* ================================================================= *)

(** [γ] sends a WP transformer [w] to the [RelPrePost] that says
    "(P, R) is valid iff at every state in P, the post-relation [R]
    is accepted by [w]".  [α] is the [yoneda_at] from [RelPrePost.v]:
    it sends a [RelPrePost] to the WP that holds at [(a, Q)] iff [r]
    validates some pre/post pair whose pre contains [a] and whose
    post-row at [a] is pointwise iff [Q].

    The adjunction holds exactly (no monotonicity assumption needed),
    using [funext] + [propext] to convert pointwise iff to function
    equality.  This is in fact a Galois insertion: [α ∘ γ = id] on
    [WPArr], so [γ] embeds [WPArr] into [RelPrePost]. *)

Definition gamma_WPArr_RelPrePost {A B} (w : WPArr A B) : RelPrePost A B :=
  fun P R => forall a, P a -> w a (R a).

Definition alpha_RelPrePost_WPArr {A B} (r : RelPrePost A B) : WPArr A B :=
  fun a Q => yoneda_at r a Q.

Lemma adjunction_RelPrePost_WPArr {A B}
  (r : RelPrePost A B) (w : WPArr A B) :
  WPArr_le (alpha_RelPrePost_WPArr r) w
  <-> RelPrePost_le r (gamma_WPArr_RelPrePost w).
Proof.
  unfold WPArr_le, RelPrePost_le, alpha_RelPrePost_WPArr,
         gamma_WPArr_RelPrePost, yoneda_at.
  split.
  - intros H P R Hr a HPa.
    apply H. exists P, R. split; [exact Hr | split; [exact HPa | reflexivity]].
  - intros H a Q [P [R [Hr [HPa Hiff]]]].
    specialize (H P R Hr a HPa).
    replace Q with (R a); [exact H|].
    extensionality b. apply propositional_extensionality. apply Hiff.
Qed.

#[global]
Instance Galois_RelPrePost_WPArr
  : Galois WPArr RelPrePost (@WPArr_le) (@RelPrePost_le) :=
{
  galois_alpha := @alpha_RelPrePost_WPArr ;
  galois_gamma := @gamma_WPArr_RelPrePost ;
  galois_adjunction := @adjunction_RelPrePost_WPArr
}.
