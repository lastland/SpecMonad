(** * Galois connections among the Taxonomy spec types.

    Following Figure 1 of "Dijkstra Monads for All"
    (Maillard et al., ICFP 2019), adapted from unary
    specification monads to binary arrows.  Each Galois connection is
    stated with the DM4all refinement orders:

    - [Rel_le]: covariant inclusion on relations.
    - [PrePost_le]: Hoare order (strengthen pre, weaken post).
    - [WPArr_le]: DM4all refinement — reverse pointwise implication.
      [w1 ≤ w2] iff [w2 a Q → w1 a Q] for all [a], [Q].
    - [RelPrePost_le]: reverse pointwise implication on validators.

    Four Galois connections are established:

    1. [Galois_Rel_PrePost] — [α R := (True, R)], [γ pq := snd pq].
       Embeds [Rel] as the full-pre fragment of [PrePostArr].

    2. [Galois_Rel_SPost] — [α R := asp R], [γ sp := asp_inv sp].
       Relates relations to monotone SP transformers.  Recovering a
       relation after [asp] gives it back; the opposite round trip is
       not an identity on all monotone transformers.

    3. [Galois_WP_PrePost] — demonic WP concretization paired with
       abstraction by [w a True] and the intersection of accepted
       postconditions.  Requires [MonotoneWP].

    4. [Galois_RPP_WP] — relates [MonotoneWP] to [WFRelPrePost].
       The validator's well-formedness ensures that its projection [γ]
       lands in [MonotoneWP].

    The final section proves that one proposed binary SP/validator map,
    [gamma_uni], is not monotone.  A second, existential proposal is
    recorded as historical discussion, not as a proved counterexample. *)

From Coq Require Import FunctionalExtensionality PropExtensionality RelationClasses.

From Incorrectness.Classes Require Import Galois.
From Incorrectness.Taxonomy.Arrows Require Import RelSPPairArr Rel PrePostArr WPArr RelPrePostArr SPArr.

(* ================================================================= *)
(** ** Local subtypes                                                  *)
(* ================================================================= *)

(** The DM4all carriers restrict the raw types to well-formed values.
    These subtypes live here (not in the type files) to keep the raw
    types unconstrained elsewhere in the project.

    [MonotoneWP] — the DM4all carrier for [W^Pure].  Monotonicity
    is required for the PrePostArr↔WP adjunction and for arrow/monad
    operations to preserve the carrier. *)
Definition wp_monotone {A B} (w : WPArr A B) : Prop :=
  forall a Q1 Q2, (forall b, Q1 b -> Q2 b) -> w a Q1 -> w a Q2.

Definition MonotoneWP (A B : Type) : Type :=
  { w : WPArr A B | wp_monotone w }.

(** [WFRelPrePost] — the DM4all carrier for [RelPrePostArr].  The
    well-formedness condition ensures the projection ([project_wp]) is
    monotone in [Q], so it lands in [MonotoneWP]. *)
Definition rpp_wf {A B} (r : RelPrePostArr A B) : Prop :=
  forall a Q1 Q2, (forall b, Q1 b -> Q2 b) ->
    project_wp r a Q1 -> project_wp r a Q2.

Definition WFRelPrePost (A B : Type) : Type :=
  { r : RelPrePostArr A B | rpp_wf r }.

(** [MonotoneSPost] bundles precondition monotonicity for raw forward
    transformers.  It is not the strict, disjunctive carrier of [SPostArr.v]. *)
Definition MonotoneSPost (A B : Type) : Type :=
  { sp : SPArrT A B | sp_monotone sp }.

(** Covariant order on forward transformers. *)
Definition SPost_le {A B} (sp1 sp2 : SPArrT A B) : Prop :=
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
(** ** [Galois_Rel_PrePost]: full-pre / forget-pre                    *)
(* ================================================================= *)

(** [α] equips a relation with the trivially-true (True) precondition;
    [γ] forgets the precondition and keeps only the post-relation.

    Under the Hoare order on [PrePostArr], [True] is the top of [fst]:
    [fst pq ⊆ True] holds for every [pq], so the pre check dissolves
    and the adjunction reduces to [R ⊆ snd pq], which is exactly
    [Rel_le R (snd pq)]. *)
Definition rel_to_pp {A B} (R : Rel A B) : PrePostArr A B :=
  (fun _ => True, R).

(* Preconditions are discarded. *)
Definition pp_to_rel {A B} (pq : PrePostArr A B) : Rel A B := snd pq.

Lemma adjunction_Rel_PrePost {A B}
  (R : Rel A B) (pq : PrePostArr A B) :
  PrePost_le (rel_to_pp R) pq <-> Rel_le R (pp_to_rel pq).
Proof.
  destruct pq as [P R'].
  unfold PrePost_le, Rel_le, rel_to_pp, pp_to_rel; cbn.
  split.
  - intros [_ HR]. exact HR.
  - intros HR. split; [intros _ _; exact I | exact HR].
Qed.

#[global]
Instance Galois_Rel_PrePost
  : Galois PrePostArr Rel (@PrePost_le) (@Rel_le) :=
{
  galois_alpha := @rel_to_pp ;
  galois_gamma := @pp_to_rel ;
  galois_adjunction := @adjunction_Rel_PrePost
}.

(* ================================================================= *)
(** ** [Galois_Rel_SPost]: strongest-postcondition embedding          *)
(* ================================================================= *)

(** [asp] sends a relation to its existential SP transformer; [asp_inv]
    evaluates a transformer at singleton preconditions.  These maps form
    the adjunction below, but not an isomorphism on [MonotoneSPost].
    With unit input and output types, the constantly true transformer is
    monotone, yet differs from every [asp R] at the empty precondition.

    The forward adjunction direction is free; the backward direction
    requires monotonicity of [sp] to lift from [sp (eq a)] to [sp pre]
    when [pre a] holds. *)

Lemma asp_sp_monotone {A B} (R : Rel A B) : sp_monotone (asp R).
Proof.
  unfold sp_monotone, asp. intros pre1 pre2 Hsub b [a [Hpre HR]].
  exists a. split; [apply Hsub; exact Hpre | exact HR].
Qed.

#[program] Definition alpha_asp {A B} (R : Rel A B) : MonotoneSPost A B :=
  asp R.
Next Obligation. exact (asp_sp_monotone R). Qed.

#[program] Definition gamma_asp_inv {A B} (sp : MonotoneSPost A B) : Rel A B :=
  asp_inv sp.

Lemma adjunction_Rel_SPost {A B}
  (R : Rel A B) (sp : MonotoneSPost A B) :
  MonotoneSPost_le (alpha_asp R) sp <->
  Rel_le R (gamma_asp_inv sp).
Proof.
  unfold MonotoneSPost_le, alpha_asp, gamma_asp_inv,
         SPost_le, Rel_le, asp_inv; cbn.
  split.
  - intros H a b HR.
    apply H. unfold asp. exists a. split; [reflexivity | exact HR].
  - intros H pre b [a [Hpre HR]].
    apply (proj2_sig sp (fun a' => a = a') pre).
    + intros a' Heq. rewrite <- Heq. exact Hpre.
    + exact (H a b HR).
Qed.

#[global]
Instance Galois_Rel_SPost
  : Galois MonotoneSPost Rel (@MonotoneSPost_le) (@Rel_le) :=
{
  galois_alpha := @alpha_asp ;
  galois_gamma := @gamma_asp_inv ;
  galois_adjunction := @adjunction_Rel_SPost
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

Lemma demonic_monotone {A B} (pq : PrePostArr A B) :
  wp_monotone (fun a Q => fst pq a /\ forall b, snd pq a b -> Q b).
Proof.
  unfold wp_monotone. intros a Q1 Q2 HQ [HP HR].
  split. exact HP. intros b HRb. apply HQ. apply HR. exact HRb.
Qed.

#[program] Definition alpha_demonic {A B} (pq : PrePostArr A B) : MonotoneWP A B :=
  fun a Q => fst pq a /\ forall b, snd pq a b -> Q b.
Next Obligation. exact (demonic_monotone pq). Qed.

#[program] Definition gamma_abstraction {A B} (w : MonotoneWP A B) : PrePostArr A B :=
  ( fun a => w a (fun _ => True)
  , fun a b => forall Q, w a Q -> Q b ).

Lemma adjunction_WP_PrePost {A B}
  (pq : PrePostArr A B) (w : MonotoneWP A B) :
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
  : Galois MonotoneWP PrePostArr (@MonotoneWP_le) (@PrePost_le) :=
{
  galois_alpha := @alpha_demonic ;
  galois_gamma := @gamma_abstraction ;
  galois_adjunction := @adjunction_WP_PrePost
}.

(* ================================================================= *)
(** ** [Galois_RPP_WP]: RelPrePostArr embedding of WP                    *)
(* ================================================================= *)

(** [α] sends a WP [w] to the validator [fun P R => forall a, P a -> w a (R a)].
    [γ] sends a validator [r] to the WP [fun a Q => project_wp r a Q].

    The adjunction holds for arbitrary [r] and monotone [w].  The
    well-formedness condition on [r] is needed only so that [γ] lands in
    [MonotoneWP].  With extensionality, [α ∘ γ = id] on [MonotoneWP],
    making this a Galois insertion. *)

(** The projection of a well-formed validator is monotone. *)
Lemma Y_monotone {A B} (r : RelPrePostArr A B) (Hr : rpp_wf r) :
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

#[program] Definition alpha_E {A B} (w : MonotoneWP A B) : WFRelPrePost A B :=
  fun P R => forall a, P a -> w a (R a).
Next Obligation. exact (E_wf (proj1_sig w) (proj2_sig w)). Qed.

#[program] Definition gamma_Y {A B} (r : WFRelPrePost A B) : MonotoneWP A B :=
  fun a Q => project_wp r a Q.
Next Obligation. exact (Y_monotone (proj1_sig r) (proj2_sig r)). Qed.

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
(** ** Obstruction: SPostArr ↔ RelPrePostArr in the binary setting          *)
(* ================================================================= *)

(** The unary [SPM.SPost] / [RPPM.RelPrePost] adjunction is proved in
    [BaseSpecMonads/BaseGaloisConnections.v].  The proposed binary map
    below instead takes a validator of input-indexed post-relations:

      [gamma_uni r P b = forall R0, r P R0 -> forall a, P a -> R0 a b].

    [gamma_uni_not_monotone] shows that this map does not land in
    [MonotoneSPost] for arbitrary validators.  It rules out this map,
    not every possible connection between binary specifications. *)

(** Counterexample for the universal variant: [γ] is not monotone.

    Take [A = unit], [B = bool], [r := fun P R => True] (accepts
    everything).  Then [γ r bot b] holds vacuously (no [a : A] with
    [bot a]), but [γ r top b] requires [forall R0, R0 tt b], which is
    false.  Monotonicity [bot <= top] would give [γ r bot b -> γ r top b],
    i.e. [True -> False]. *)
Definition gamma_uni {A B} (r : RelPrePostArr A B)
  (P : A -> Prop) (b : B) : Prop :=
  forall R0, r P R0 -> forall a, P a -> R0 a b.

Lemma gamma_uni_not_monotone :
  ~ sp_monotone (gamma_uni (A:=unit) (B:=bool) (fun _ _ => True)).
Proof.
  unfold sp_monotone, gamma_uni. intros Hmon.
  assert (Hincl : forall a : unit, (fun _ => False) a -> (fun _ => True) a).
  { intros a _. exact I. }
  assert (Hbot : forall (R0 : Rel unit bool) (_ : True) (a : unit),
                   (fun _ => False) a -> R0 a false).
  { intros R0 _ a Habs. destruct Habs. }
  assert (Htop := Hmon (fun _ => False) (fun _ => True) Hincl false Hbot).
  exact (Htop (fun _ _ => False) I tt I).
Qed.

(** Historical alternative, not formalized in this file:

      [fun r P b => exists a, P a /\ (forall R0, r P R0 -> R0 a b)].

    This formula requires one input witness shared by all validated
    post-relations.  The earlier investigation considered conflicting
    witnesses, but this file contains neither a monotonicity theorem nor
    an adjunction counterexample for the existential proposal. *)
