(** * Galois connections among the Taxonomy spec types.

    **Dijkstra refinement** is used as the canonical order throughout:

    - [Pred_le R1 R2 := R2 ⊆ R1]: contravariant inclusion on
      relations.  [R1 ≤ R2] reads as "[R2] is more refined than [R1]"
      — the refined side has a smaller set of allowed outcomes.

    - [PrePost_le]: Dijkstra refinement on pre/post pairs — weaken
      the precondition, strengthen the post-relation.  [pq1 ≤ pq2]
      iff [fst pq1 ⊆ fst pq2] and [snd pq2 ⊆ snd pq1].

    - [WPArr_le w1 w2 := ∀ a Q, w1 a Q → w2 a Q]: pointwise
      implication on WP transformers.  This is already Dijkstra
      refinement in the wp form (a more-refined wp accepts more
      [(state, post)] pairs).

    Under these orders, three Galois connections survive:

    1. [Galois_Pred_PrePost] with [α R := (False, R)] and [γ pq := snd pq].
       The [False] precondition is vacuously minimal under [PrePost_le]
       because [(False → P)] is always true, so the pre check
       dissolves and the adjunction reduces to [snd pq ⊆ R], matching
       [Pred_le R (snd pq)].  This is the **only** [α, γ] pair for
       [Pred ↔ PrePost] that fits Dijkstra refinement cleanly.

    2. [Galois_PrePost_WPArr]: existential abstraction paired with
       demonic concretization.  [PrePost_le] here is the same
       Dijkstra refinement order (formerly [PrePost_le_dem]).

    3. [Galois_RelPrePost_WPArr]: Yoneda abstraction.  Pointwise
       orders on both sides; does not touch [PrePost_le].

    **Variants that do not survive Dijkstra refinement and were
    removed**:

    - The existential [α R := (fun a => ∃ b, R a b, R)] paired with
      Cartesian [γ (P, R) := λ a b. P a ∧ R a b].  The "domain of R
      ⊆ P" conjunct on the α side cannot be recovered from the γ
      side when [P] is empty outside the domain of [R].

    - The [True]-pre variants on both the [Pred ↔ PrePost] and
      [PrePost ↔ WPArr] sides.  The [α R := (True, R)] choice forces
      the [(True → P)] conjunct, which requires [P] to hold
      everywhere — incompatible with a clean adjunction. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Relation_Definitions RelationClasses Morphisms.
From Incorrectness.Classes Require Import Arrow Galois.
From Incorrectness Require Import
  Taxonomy.WP Taxonomy.WPFacts
  Taxonomy.Pred Taxonomy.PrePost Taxonomy.WPArr Taxonomy.RelPrePost.

(** The Dijkstra refinement orders [Pred_le], [PrePost_le],
    [WPArr_le], and [RelPrePost_le] live in the respective type
    files: [Taxonomy/Pred.v], [Taxonomy/PrePost.v], [Taxonomy/WPArr.v],
    and [Taxonomy/RelPrePost.v]. *)

(* ================================================================= *)
(** ** [Galois_Pred_PrePost]: empty-pre / forget-pre                  *)
(* ================================================================= *)

(** [α] equips a relation with the empty (False) precondition; [γ]
    forgets the precondition and keeps only the post-relation.

    Under Dijkstra refinement on [PrePost], the [False] precondition
    is vacuously minimal: [(False → fst pq)] is always true, so the
    pre check in [PrePost_le (False, R) pq] dissolves and the
    adjunction reduces to [snd pq ⊆ R], which is exactly
    [Pred_le R (snd pq)] under the contravariant [Pred_le]. *)

Definition empty_pre {A B} (R : Pred A B) : PrePost A B :=
  (fun _ => False, R).

Definition forget_pre {A B} (pq : PrePost A B) : Pred A B := snd pq.

Lemma adjunction_Pred_PrePost {A B}
  (R : Pred A B) (pq : PrePost A B) :
  PrePost_le (empty_pre R) pq <-> Pred_le R (forget_pre pq).
Proof.
  destruct pq as [P R'].
  unfold PrePost_le, Pred_le, empty_pre, forget_pre; cbn.
  split.
  - intros [_ HR]. exact HR.
  - intros HR. split; [intros _ []| exact HR].
Qed.

#[global]
Instance Galois_Pred_PrePost
  : Galois PrePost Pred (@PrePost_le) (@Pred_le) :=
{
  galois_alpha := @empty_pre ;
  galois_gamma := @forget_pre ;
  galois_adjunction := @adjunction_Pred_PrePost
}.

(* ================================================================= *)
(** ** [Galois_PrePost_WPArr]: demonic WP / weakest spec              *)
(* ================================================================= *)

(** Concretization sends a Hoare-style pair [(P, R)] to the demonic
    weakest precondition transformer
    [fun a Q => P a /\ forall b, R a b -> Q b].

    Abstraction sends a WP transformer [w] to the pair "[w] accepts
    something at [a]" / "[b] is in every [Q] that [w] accepts at [a]".

    The adjunction holds exactly without any monotonicity assumption
    on [w], using the Dijkstra refinement order [PrePost_le] (which
    is exactly what was previously called [PrePost_le_dem]). *)

Definition gamma_PrePost_WPArr {A B} (pq : PrePost A B) : WPArr A B :=
  fun a Q => fst pq a /\ (forall b, snd pq a b -> Q b).

Definition alpha_WPArr_PrePost {A B} (w : WPArr A B) : PrePost A B :=
  ( fun a   => exists Q, w a Q
  , fun a b => forall Q, w a Q -> Q b ).

Lemma adjunction_PrePost_WPArr {A B}
  (w : WPArr A B) (pq : PrePost A B) :
  PrePost_le (alpha_WPArr_PrePost w) pq <->
  WPArr_le w (gamma_PrePost_WPArr pq).
Proof.
  destruct pq as [P R].
  unfold PrePost_le, WPArr_le, alpha_WPArr_PrePost, gamma_PrePost_WPArr.
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
  : Galois PrePost WPArr (@PrePost_le) (@WPArr_le) :=
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
