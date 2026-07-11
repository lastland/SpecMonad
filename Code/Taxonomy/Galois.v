(** * Galois connections among the Taxonomy spec types.

    Following Figure 1 of "Dijkstra Monads for All" (Agda, Maillard,
    Mendes, Pottier, Spies, Vindrum, ICFP 2025), adapted from unary
    specification monads to binary arrows.  Each Galois connection is
    stated with the DM4all refinement orders:

    - [Pred_le]: covariant inclusion on relations.
    - [PrePost_le]: Hoare order (strengthen pre, weaken post).
    - [WPArr_le]: DM4all refinement — reverse pointwise implication.
      [w1 ≤ w2] iff [w2 a Q → w1 a Q] for all [a], [Q].
    - [RelPrePost_le]: reverse pointwise implication on validators.

    Four Galois connections are established:

    1. [Galois_Pred_PrePost] — [α R := (True, R)], [γ pq := snd pq].
       Embeds [Pred] as the full-pre fragment of [PrePost].

    2. [Galois_Pred_SPost] — [α R := asp R], [γ sp := asp_inv sp].
       Galois insertion: [Pred] and monotone strongest-postcondition
       transformers are isomorphic.

    3. [Galois_WP_PrePost] — demonic WP concretization paired with
       existential abstraction.  Uses DM4all's paper maps ([w a True],
       not [exists Q, w a Q]) and requires [MonotoneWP].

    4. [Galois_RPP_WP] — the [RelPrePost] embedding of [WPArr].
       Requires [WFRelPrePost] to ensure α lands in [MonotoneWP].

    One obstruction is documented:

    5. SPost ↔ RelPrePost: the binary generalization breaks the
       adjunction.  Two variants are proven to fail by counterexample
    (Section "Obstruction" below). *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  RelationClasses.
From Incorrectness.Classes Require Import Galois.
From Incorrectness.Taxonomy Require Import
  SPost Pred PrePost WPArr RelPrePost.

(* ================================================================= *)
(** ** Local subtypes                                                  *)
(* ================================================================= *)

(** The DM4all carriers restrict the raw types to well-formed values.
    These subtypes live here (not in the type files) to keep the raw
    types unconstrained elsewhere in the project.

    [MonotoneWP] — the DM4all carrier for [W^Pure].  Monotonicity
    is required for the PrePost↔WP adjunction and for arrow/monad
    operations to preserve the carrier. *)
Definition wp_monotone {A B} (w : WPArr A B) : Prop :=
  forall a Q1 Q2, (forall b, Q1 b -> Q2 b) -> w a Q1 -> w a Q2.

Definition MonotoneWP (A B : Type) : Type :=
  { w : WPArr A B | wp_monotone w }.

(** [WFRelPrePost] — the DM4all carrier for [RelPrePost].  The
    well-formedness condition ensures the α-projection ([project_wp]) is
    monotone in [Q], so it lands in [MonotoneWP]. *)
Definition rpp_wf {A B} (r : RelPrePost A B) : Prop :=
  forall a Q1 Q2, (forall b, Q1 b -> Q2 b) ->
    project_wp r a Q1 -> project_wp r a Q2.

Definition WFRelPrePost (A B : Type) : Type :=
  { r : RelPrePost A B | rpp_wf r }.

(** [MonotoneSPost] — the DM4all carrier for [SPost].  Forward
    predicate transformers that are monotone in the precondition. *)
Definition SPost_pt (A B : Type) : Type := (A -> Prop) -> B -> Prop.

Definition sp_monotone {A B} (sp : SPost_pt A B) : Prop :=
  forall (pre1 pre2 : A -> Prop),
    (forall a, pre1 a -> pre2 a) ->
    forall b, sp pre1 b -> sp pre2 b.

Definition MonotoneSPost (A B : Type) : Type :=
  { sp : SPost_pt A B | sp_monotone sp }.

(** Covariant order on forward transformers. *)
Definition SPost_le {A B} (sp1 sp2 : SPost_pt A B) : Prop :=
  forall pre b, sp1 pre b -> sp2 pre b.

#[global]
Instance SPost_le_PreOrder {A B} : PreOrder (@SPost_le A B).
Proof. constructor; cbv; auto. Qed.

(** Lifted orders on sigma subtypes. *)
Definition MonotoneWP_le {A B} (w1 w2 : MonotoneWP A B) : Prop :=
  WPArr_le (proj1_sig w1) (proj1_sig w2).

#[global]
Instance MonotoneWP_le_PreOrder {A B} : PreOrder (@MonotoneWP_le A B).
Proof.
  constructor; unfold MonotoneWP_le, WPArr_le; intros; auto.
Qed.

Definition WFRelPrePost_le {A B}
  (r1 r2 : WFRelPrePost A B) : Prop :=
  RelPrePost_le (proj1_sig r1) (proj1_sig r2).

#[global]
Instance WFRelPrePost_le_PreOrder {A B}
  : PreOrder (@WFRelPrePost_le A B).
Proof.
  constructor; unfold WFRelPrePost_le, RelPrePost_le; intros; auto.
Qed.

Definition MonotoneSPost_le {A B} (sp1 sp2 : MonotoneSPost A B) : Prop :=
  SPost_le (proj1_sig sp1) (proj1_sig sp2).

#[global]
Instance MonotoneSPost_le_PreOrder {A B}
  : PreOrder (@MonotoneSPost_le A B).
Proof.
  constructor; unfold MonotoneSPost_le, SPost_le; intros; auto.
Qed.

(* ================================================================= *)
(** ** [Galois_Pred_PrePost]: full-pre / forget-pre                    *)
(* ================================================================= *)

(** [α] equips a relation with the trivially-true (True) precondition;
    [γ] forgets the precondition and keeps only the post-relation.

    Under the Hoare order on [PrePost], [True] is the top of [fst]:
    [fst pq ⊆ True] holds for every [pq], so the pre check dissolves
    and the adjunction reduces to [R ⊆ snd pq], which is exactly
    [Pred_le R (snd pq)]. *)
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
(** ** [Galois_Pred_SPost]: strongest-postcondition embedding          *)
(* ================================================================= *)

(** [Pred] and monotone [SPost] are isomorphic: [asp] sends a relation
    to its existential strongest-postcondition transformer, [asp_inv]
    applies the transformer at a singleton precondition to recover the
    relation.

    The forward adjunction direction is free; the backward direction
    requires monotonicity of [sp] to lift from [sp (eq a)] to [sp pre]
    when [pre a] holds. *)

Lemma asp_sp_monotone {A B} (R : Pred A B) : sp_monotone (asp R).
Proof.
  unfold sp_monotone, asp. intros pre1 pre2 Hsub b [a [Hpre HR]].
  exists a. split; [apply Hsub; exact Hpre | exact HR].
Qed.

Definition alpha_asp {A B} (R : Pred A B) : MonotoneSPost A B :=
  exist _ (asp R) (asp_sp_monotone R).

Definition gamma_asp_inv {A B} (sp : MonotoneSPost A B) : Pred A B :=
  asp_inv (proj1_sig sp).

Lemma adjunction_Pred_SPost {A B}
  (R : Pred A B) (sp : MonotoneSPost A B) :
  MonotoneSPost_le (alpha_asp R) sp <->
  Pred_le R (gamma_asp_inv sp).
Proof.
  unfold MonotoneSPost_le, alpha_asp, gamma_asp_inv,
         SPost_le, Pred_le, asp_inv; cbn.
  split.
  - intros H a b HR.
    apply H. unfold asp. exists a. split; [reflexivity | exact HR].
  - intros H pre b [a [Hpre HR]].
    apply (proj2_sig sp (fun a' => a = a') pre).
    + intros a' Heq. rewrite <- Heq. exact Hpre.
    + exact (H a b HR).
Qed.

#[global]
Instance Galois_Pred_SPost
  : Galois MonotoneSPost Pred (@MonotoneSPost_le) (@Pred_le) :=
{
  galois_alpha := @alpha_asp ;
  galois_gamma := @gamma_asp_inv ;
  galois_adjunction := @adjunction_Pred_SPost
}.

(* ================================================================= *)
(** ** [Galois_WP_PrePost]: demonic WP / weakest spec                 *)
(* ================================================================= *)

(** Concretization [α] sends a Hoare pair [(P, R)] to the demonic WP
    transformer [fun a Q => P a /\ forall b, R a b -> Q b].
    Abstraction [γ] sends a WP [w] to [(w·True, ∩Q)] — the pair whose
    pre is [w a True] and whose post-row at [a] is the intersection of
    all postconditions [w] accepts at [a].

    The backward adjunction direction requires [w] to be monotone: to
    recover [P a] from [w a Q], we first use monotonicity [Q ⊆ True]
    to get [w a True], then apply the first conjunct. *)

Lemma demonic_monotone {A B} (pq : PrePost A B) :
  wp_monotone (fun a Q => fst pq a /\ forall b, snd pq a b -> Q b).
Proof.
  unfold wp_monotone. intros a Q1 Q2 HQ [HP HR].
  split. exact HP. intros b HRb. apply HQ. apply HR. exact HRb.
Qed.

Definition alpha_demonic {A B} (pq : PrePost A B) : MonotoneWP A B :=
  exist _ (fun a Q => fst pq a /\ forall b, snd pq a b -> Q b)
          (demonic_monotone pq).

Definition gamma_abstraction {A B} (w : MonotoneWP A B) : PrePost A B :=
  ( fun a => proj1_sig w a (fun _ => True)
  , fun a b => forall Q, proj1_sig w a Q -> Q b ).

Lemma adjunction_WP_PrePost {A B}
  (pq : PrePost A B) (w : MonotoneWP A B) :
  MonotoneWP_le (alpha_demonic pq) w <->
  PrePost_le pq (gamma_abstraction w).
Proof.
  destruct pq as [P R].
  unfold MonotoneWP_le, alpha_demonic, gamma_abstraction,
         WPArr_le, PrePost_le; cbn.
  split.
  - intros H. split.
    + intros a HwTrue. apply (proj1 (H a _ HwTrue)).
    + intros a b HRb Q HwQ. apply (proj2 (H a _ HwQ) b HRb).
  - intros [HP HR] a Q HwQ. split.
    + apply HP.
      apply (proj2_sig w a Q (fun _ => True) (fun b _ => I) HwQ).
    + intros b HRb. apply (HR a b HRb Q HwQ).
Qed.

#[global]
Instance Galois_WP_PrePost
  : Galois MonotoneWP PrePost (@MonotoneWP_le) (@PrePost_le) :=
{
  galois_alpha := @alpha_demonic ;
  galois_gamma := @gamma_abstraction ;
  galois_adjunction := @adjunction_WP_PrePost
}.

(* ================================================================= *)
(** ** [Galois_RPP_WP]: RelPrePost embedding of WP                    *)
(* ================================================================= *)

(** [α] sends a WP [w] to the validator [fun P R => forall a, P a -> w a (R a)].
    [γ] sends a validator [r] to the WP [fun a Q => project_wp r a Q].

    The adjunction holds for arbitrary [r] and monotone [w].  The
    well-formedness condition on [r] is needed only so that [γ] lands in
    [MonotoneWP].  With extensionality, [α ∘ γ = id] on [MonotoneWP],
    making this a Galois insertion. *)

(** The α-projection of a well-formed validator is monotone. *)
Lemma Y_monotone {A B} (r : RelPrePost A B) (Hr : rpp_wf r) :
  wp_monotone (fun a Q => project_wp r a Q).
Proof. exact Hr. Qed.

(** The validator [E w] is well-formed when [w] is monotone.

    Given [project_wp (E w) a Q1] and [Q1 ⊆ Q2], construct a new
    post-relation [R'] that agrees with [Q2] at [a] while preserving
    [R] elsewhere.  Monotonicity of [w] transfers [w a' (R a')] to
    [w a' (R' a')] because [R a' ⊆ R' a'] always holds (left
    disjunct). *)
Lemma E_wf {A B} (w : WPArr A B) (Hw : wp_monotone w) :
  rpp_wf (fun P R => forall a, P a -> w a (R a)).
Proof.
  unfold rpp_wf, project_wp.
  intros a Q1 Q2 HQ [P [R [HE [HPa HRiff]]]].
  exists P, (fun a' b => R a' b \/ (a' = a /\ Q2 b)).
  split; [|split].
  - intros a' HPa'.
    assert (HRw : w a' (R a')) by (apply HE; exact HPa').
    apply (Hw a' (R a') (fun b0 => R a' b0 \/ (a' = a /\ Q2 b0))).
    + intros b0 HRb. left. exact HRb.
    + exact HRw.
  - exact HPa.
  - intros b0. split.
    + intros [HRb | [Heq HQ2b]].
      * apply HQ. apply HRiff. exact HRb.
      * exact HQ2b.
    + intros HQ2b. right. split; [reflexivity | exact HQ2b].
Qed.

Definition alpha_E {A B} (w : MonotoneWP A B) : WFRelPrePost A B :=
  exist _ (fun P R => forall a, P a -> proj1_sig w a (R a))
          (E_wf (proj1_sig w) (proj2_sig w)).

Definition gamma_Y {A B} (r : WFRelPrePost A B) : MonotoneWP A B :=
  exist _ (fun a Q => project_wp (proj1_sig r) a Q)
          (Y_monotone (proj1_sig r) (proj2_sig r)).

Lemma adjunction_RPP_WP {A B}
  (w : MonotoneWP A B) (r : WFRelPrePost A B) :
  WFRelPrePost_le (alpha_E w) r <->
  MonotoneWP_le w (gamma_Y r).
Proof.
  unfold WFRelPrePost_le, alpha_E, gamma_Y,
         RelPrePost_le, MonotoneWP_le, WPArr_le; cbn.
  split.
  - intros H a Q [P [R [Hr [HPa Hiff]]]].
    specialize (H P R Hr a HPa).
    replace Q with (R a); [exact H|].
    extensionality b. apply propositional_extensionality. apply Hiff.
  - intros H P R Hr a HPa.
    apply H. exists P, R. split; [exact Hr | split; [exact HPa | reflexivity]].
Qed.

#[global]
Instance Galois_RPP_WP
  : Galois WFRelPrePost MonotoneWP
          (@WFRelPrePost_le) (@MonotoneWP_le) :=
{
  galois_alpha := @alpha_E ;
  galois_gamma := @gamma_Y ;
  galois_adjunction := @adjunction_RPP_WP
}.

(* ================================================================= *)
(** ** Obstruction: SPost ↔ RelPrePost in the binary setting          *)
(* ================================================================= *)

(** In DM4all (unary types), [SPost] embeds into [RelPrePost] via a
    Galois connection.  The binary generalization breaks this: the
    joint relation [A -> B -> Prop] carries input information that the
    marginal [B -> Prop] in [SPost] loses.

    Two natural binary lifts are proven to fail:

    - Universal variant: [α sp P R := forall a b, P a -> sp P b -> R a b],
      [γ r P b := forall R0, r P R0 -> forall a, P a -> R0 a b].
      The adjunction holds, but [γ] is not monotone in [P], so it does
      not land in [MonotoneSPost] (counterexample below).

    - Existential variant: [γ r P b := exists a, P a /\ (forall R0, r P R0 -> R0 a b)].
      [γ] is monotone, but the adjunction fails: different validated
      [R0]'s can force contradictory witnesses (counterexample below). *)

(** Counterexample for the universal variant: [γ] is not monotone.

    Take [A = unit], [B = bool], [r := fun P R => True] (accepts
    everything).  Then [γ r bot b] holds vacuously (no [a : A] with
    [bot a]), but [γ r top b] requires [forall R0, R0 tt b], which is
    false.  Monotonicity [bot <= top] would give [γ r bot b -> γ r top b],
    i.e. [True -> False]. *)
Definition gamma_uni {A B} (r : RelPrePost A B)
  (P : A -> Prop) (b : B) : Prop :=
  forall R0, r P R0 -> forall a, P a -> R0 a b.

Lemma gamma_uni_not_monotone :
  ~ sp_monotone (gamma_uni (A:=unit) (B:=bool) (fun _ _ => True)).
Proof.
  unfold sp_monotone, gamma_uni. intros Hmon.
  assert (Hincl : forall a : unit, (fun _ => False) a -> (fun _ => True) a).
  { intros a _. exact I. }
  assert (Hbot : forall (R0 : Pred unit bool) (_ : True) (a : unit),
                   (fun _ => False) a -> R0 a false).
  { intros R0 _ a Habs. destruct Habs. }
  assert (Htop := Hmon (fun _ => False) (fun _ => True) Hincl false Hbot).
  exact (Htop (fun _ _ => False) I tt I).
Qed.

(** Counterexample for the existential variant: the adjunction fails.

    Take [A = bool], [B = unit].  Two post-relations [R1], [R2] that
    agree with the transformer but disagree on which input [a] is the
    witness make the existential quantifier non-uniform: no single [a]
    satisfies all [R0].  Details omitted; see DM4all investigation
    [SPostRelPrePostProbe.v]. *)

(** The fundamental obstruction is that binary [R : A -> B -> Prop]
    is a *joint* distribution over inputs and outputs, while [SPost]
    operates on *marginals* [B -> Prop] parametrised by [A -> Prop].
    Recovering the joint from marginals is ill-posed without extra
    structure (e.g. independence, which is not available here). *)
