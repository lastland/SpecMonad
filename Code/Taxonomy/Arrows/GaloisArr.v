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

    A further section proves that one proposed binary SP/validator map,
    [gamma_uni], is not monotone.  A second, existential proposal is
    recorded as historical discussion, not as a proved counterexample.

    The last part reads the monotone carrier [MonotoneSPost] with either
    index fixed, as [MonoPT], and states on it the three relations of the
    taxonomy of Hoare-like logics: implication, contrapositive, and Galois
    connection. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions Classical_Prop.

From Incorrectness.Classes Require Import Galois.
From Incorrectness.Taxonomy.Arrows Require Import RelSPostArr Rel PrePostArr WPArr RelPrePostArr SPostArr.

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
    [MonotoneWP].  No extensionality is needed for the adjunction: the
    forward direction transfers [w a (R a)] to [w a Q] by monotonicity
    of [w] applied to the [R a ⊆ Q] half of the iff.  The theorem below
    states the adjunction under the two refinement orders, not an
    equality of bundled values. *)

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
    apply (proj2_sig w a (R a) Q).
    + intros b HRb. apply Hiff. exact HRb.
    + exact (H P R Hr a HPa).
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

(* ================================================================= *)
(** * [MonoPT]: the monotone carrier and the relations of the taxonomy *)
(* ================================================================= *)

(**   [PT A B]     = [(A -> Prop) -> B -> Prop]
      [MonoPT A B] = { t : PT A B | t monotone }

    [PT] is [SPostArr.SPArrT] under a neutral name, and [MonoPT] is
    [MonotoneSPost], because the carrier is read in two ways.  With the FIRST
    index fixed its elements are strongest-postcondition transformers: a
    precondition on the input goes to the outcomes it reaches.  With the
    SECOND index fixed they are weakest-precondition transformers: a
    postcondition on the outcomes goes to the inputs that guarantee it.

    Only the first reading comes with arrow operations.  An arrow yields a
    monad by fixing its input, never its output, so the WP monads are built
    separately ([BaseSpecMonads/WPureMonad.v]); [BaseSpecMonads/MonadTaxonomy.v]
    shows the carriers of both families isomorphic to this one.

    The carrier is used here for three relations only, the three kinds of
    edge in Verscht and Kaminski's "A Taxonomy of Hoare-Like Logics":

      [pt_le]            implication between transformers          (Thm. 3.7)
      [Contrapositive]   [t1 P] is the complement of [t2 (not P)]  (Thm. 3.8)
      [GaloisPT]         a left adjoint in [MonoPT A B] with its right
                         adjoint in [MonoPT B A]                   (Sec. 4.1)

    [pt_le] and [Contrapositive] relate two transformers with the same
    indices.  [GaloisPT] swaps them, so it relates an SP transformer to a WP
    one.  Everything about [Contrapositive] that turns a negated statement
    back into a positive one is classical; the lemmas that need
    [Classical_Prop] are marked.

    A transformer stands for two logics, [pt_under] and [pt_over]; the last
    section reads the three relations as implications and equivalences
    between those. *)

(* ================================================================= *)
(** ** The carrier                                                   *)
(* ================================================================= *)

Definition PT (A B : Type) : Type := SPArrT A B.

Definition MonoPT (A B : Type) : Type := MonotoneSPost A B.

Definition getPT {A B} (t : MonoPT A B) : (A -> Prop) -> B -> Prop := proj1_sig t.
Coercion getPT : MonoPT >-> Funclass.

Definition mkMonoPT {A B} (t : PT A B) (H : sp_monotone t) : MonoPT A B :=
  exist _ t H.

Lemma getPT_mono {A B} (t : MonoPT A B) (P Q : A -> Prop) b :
  (forall a, P a -> Q a) -> t P b -> t Q b.
Proof. intro H. exact (proj2_sig t P Q H b). Qed.

Lemma getPT_ext {A B} (t : MonoPT A B) (P Q : A -> Prop) b :
  (forall a, P a <-> Q a) -> (t P b <-> t Q b).
Proof. intro H. split; apply getPT_mono; intro a; apply H. Qed.

(* ================================================================= *)
(** ** The order, in both directions                                 *)
(* ================================================================= *)

(** [pt_le] is pointwise implication, [pt_ge] its converse, and [pt_eq]
    the equivalence they share. *)

Definition pt_le {A B} (t1 t2 : MonoPT A B) : Prop :=
  forall P b, t1 P b -> t2 P b.

Definition pt_ge {A B} (t1 t2 : MonoPT A B) : Prop := pt_le t2 t1.

Definition pt_eq {A B} (t1 t2 : MonoPT A B) : Prop :=
  forall P b, t1 P b <-> t2 P b.

#[global] Instance pt_le_PreOrder {A B} : PreOrder (@pt_le A B).
Proof.
  constructor.
  - intros t P b H. exact H.
  - intros t1 t2 t3 H1 H2 P b H. exact (H2 P b (H1 P b H)).
Qed.

#[global] Instance pt_ge_PreOrder {A B} : PreOrder (@pt_ge A B).
Proof.
  constructor.
  - intros t P b H. exact H.
  - intros t1 t2 t3 H1 H2 P b H. exact (H1 P b (H2 P b H)).
Qed.

#[global] Instance pt_eq_Equivalence {A B} : Equivalence (@pt_eq A B).
Proof.
  constructor.
  - intros t P b. reflexivity.
  - intros t1 t2 H P b. symmetry. exact (H P b).
  - intros t1 t2 t3 H1 H2 P b. etransitivity; [ exact (H1 P b) | exact (H2 P b) ].
Qed.

Lemma pt_le_antisym {A B} (t1 t2 : MonoPT A B) :
  pt_le t1 t2 -> pt_le t2 t1 -> pt_eq t1 t2.
Proof. intros H1 H2 P b. split; [ apply H1 | apply H2 ]. Qed.

Lemma pt_eq_le {A B} (t1 t2 : MonoPT A B) : pt_eq t1 t2 -> pt_le t1 t2.
Proof. intros H P b. apply H. Qed.

Lemma pt_eq_ge {A B} (t1 t2 : MonoPT A B) : pt_eq t1 t2 -> pt_ge t1 t2.
Proof. intros H P b. apply H. Qed.

Lemma pt_le_eq {A B} (t1 t1' t2 t2' : MonoPT A B) :
  pt_eq t1 t1' -> pt_eq t2 t2' -> pt_le t1 t2 -> pt_le t1' t2'.
Proof. intros E1 E2 H P b H1. apply (E2 P b), H, (E1 P b), H1. Qed.

(** Binary meets and joins, for the "in-between" transformers. *)

#[program] Definition pt_meet {A B} (t1 t2 : MonoPT A B) : MonoPT A B :=
  fun P b => t1 P b /\ t2 P b.
Next Obligation.
  intros P Q H b [H1 H2].
  split; [ exact (getPT_mono t1 P Q b H H1) | exact (getPT_mono t2 P Q b H H2) ].
Qed.

#[program] Definition pt_join {A B} (t1 t2 : MonoPT A B) : MonoPT A B :=
  fun P b => t1 P b \/ t2 P b.
Next Obligation.
  intros P Q H b [H1 | H2];
    [ left; exact (getPT_mono t1 P Q b H H1) | right; exact (getPT_mono t2 P Q b H H2) ].
Qed.

Section Lattice.
  Context {A B : Type} (t t1 t2 : MonoPT A B).

  Lemma pt_meet_get P b : pt_meet t1 t2 P b <-> t1 P b /\ t2 P b.
  Proof. reflexivity. Qed.

  Lemma pt_join_get P b : pt_join t1 t2 P b <-> t1 P b \/ t2 P b.
  Proof. reflexivity. Qed.

  Lemma pt_meet_le_l : pt_le (pt_meet t1 t2) t1.
  Proof. intros P b [H _]. exact H. Qed.

  Lemma pt_meet_le_r : pt_le (pt_meet t1 t2) t2.
  Proof. intros P b [_ H]. exact H. Qed.

  Lemma pt_meet_glb : pt_le t t1 -> pt_le t t2 -> pt_le t (pt_meet t1 t2).
  Proof. intros H1 H2 P b H. split; [ exact (H1 P b H) | exact (H2 P b H) ]. Qed.

  Lemma pt_le_join_l : pt_le t1 (pt_join t1 t2).
  Proof. intros P b H. left. exact H. Qed.

  Lemma pt_le_join_r : pt_le t2 (pt_join t1 t2).
  Proof. intros P b H. right. exact H. Qed.

  Lemma pt_join_lub : pt_le t1 t -> pt_le t2 t -> pt_le (pt_join t1 t2) t.
  Proof. intros H1 H2 P b [H | H]; [ exact (H1 P b H) | exact (H2 P b H) ]. Qed.
End Lattice.

(* ================================================================= *)
(** ** The contrapositive relation                                   *)
(* ================================================================= *)

(** [pt_dual t] accepts [P] exactly where [t] rejects its complement. *)

#[program] Definition pt_dual {A B} (t : MonoPT A B) : MonoPT A B :=
  fun P b => ~ t (fun a => ~ P a) b.
Next Obligation.
  intros P Q H b Hn Ht. apply Hn.
  refine (getPT_mono t _ _ b _ Ht). intros a Hq Hp. exact (Hq (H a Hp)).
Qed.

Lemma pt_dual_get {A B} (t : MonoPT A B) P b :
  pt_dual t P b <-> ~ t (fun a => ~ P a) b.
Proof. reflexivity. Qed.

Definition Contrapositive {A B} (t1 t2 : MonoPT A B) : Prop :=
  forall P b, t1 P b <-> ~ t2 (fun a => ~ P a) b.

Section Contrapositive.
  Context {A B : Type}.

  (** The relation is the graph of [pt_dual]. *)
  Lemma Contrapositive_dual (t1 t2 : MonoPT A B) :
    Contrapositive t1 t2 <-> pt_eq t1 (pt_dual t2).
  Proof. split; intro H; exact H. Qed.

  Lemma Contrapositive_pt_dual (t : MonoPT A B) : Contrapositive (pt_dual t) t.
  Proof. intros P b. reflexivity. Qed.

  Lemma Contrapositive_eq (t1 t1' t2 t2' : MonoPT A B) :
    pt_eq t1 t1' -> pt_eq t2 t2' -> Contrapositive t1 t2 -> Contrapositive t1' t2'.
  Proof. intros E1 E2 H P b. rewrite <- (E1 P b), <- (E2 _ b). exact (H P b). Qed.

  Lemma pt_dual_antitone (t1 t2 : MonoPT A B) :
    pt_le t1 t2 -> pt_le (pt_dual t2) (pt_dual t1).
  Proof. intros H P b H2 H1. exact (H2 (H _ b H1)). Qed.

  (** Classical. *)
  Lemma pt_dual_involutive (t : MonoPT A B) : pt_eq (pt_dual (pt_dual t)) t.
  Proof.
    intros P b. change (~ ~ t (fun a => ~ ~ P a) b <-> t P b). split.
    - intro H. apply NNPP. intro Hn. apply H. intro Ht. apply Hn.
      refine (getPT_mono t _ _ b _ Ht). intros a Ha. exact (NNPP _ Ha).
    - intros Ht Hn. apply Hn.
      refine (getPT_mono t _ _ b _ Ht). intros a Ha Hna. exact (Hna Ha).
  Qed.

  (** Classical. *)
  Lemma Contrapositive_sym (t1 t2 : MonoPT A B) :
    Contrapositive t1 t2 -> Contrapositive t2 t1.
  Proof.
    intros H P b. split.
    - intros H2 H1. apply (proj1 (H _ b) H1).
      refine (getPT_mono t2 _ _ b _ H2). intros a Ha Hna. exact (Hna Ha).
    - intro Hn. apply NNPP. intro H2. apply Hn. apply (proj2 (H _ b)).
      intro H2'. apply H2.
      refine (getPT_mono t2 _ _ b _ H2'). intros a Ha. exact (NNPP _ Ha).
  Qed.

  (** Each side determines the other. *)
  Lemma Contrapositive_functional (t1 t1' t2 : MonoPT A B) :
    Contrapositive t1 t2 -> Contrapositive t1' t2 -> pt_eq t1 t1'.
  Proof. intros H H' P b. rewrite (H P b). symmetry. exact (H' P b). Qed.

  (** Classical. *)
  Lemma Contrapositive_injective (t1 t2 t2' : MonoPT A B) :
    Contrapositive t1 t2 -> Contrapositive t1 t2' -> pt_eq t2 t2'.
  Proof.
    intros H H'.
    exact (Contrapositive_functional t2 t2' t1
             (Contrapositive_sym _ _ H) (Contrapositive_sym _ _ H')).
  Qed.

  (** It reverses the order. *)
  Lemma Contrapositive_antitone (t1 t2 t1' t2' : MonoPT A B) :
    Contrapositive t1 t2 -> Contrapositive t1' t2' -> pt_le t2 t2' -> pt_le t1' t1.
  Proof.
    intros H H' Hle P b H1'. apply (proj2 (H P b)). intro H2.
    exact (proj1 (H' P b) H1' (Hle _ b H2)).
  Qed.

  (** It exchanges meets and joins.  The second is classical. *)
  Lemma Contrapositive_meet_join (t1 t2 t1' t2' : MonoPT A B) :
    Contrapositive t1 t2 -> Contrapositive t1' t2' ->
    Contrapositive (pt_meet t1 t1') (pt_join t2 t2').
  Proof.
    intros H H' P b. change ((t1 P b /\ t1' P b) <->
      ~ (t2 (fun a => ~ P a) b \/ t2' (fun a => ~ P a) b)).
    rewrite (H P b), (H' P b). tauto.
  Qed.

  Lemma Contrapositive_join_meet (t1 t2 t1' t2' : MonoPT A B) :
    Contrapositive t1 t2 -> Contrapositive t1' t2' ->
    Contrapositive (pt_join t1 t1') (pt_meet t2 t2').
  Proof.
    intros H H' P b. change ((t1 P b \/ t1' P b) <->
      ~ (t2 (fun a => ~ P a) b /\ t2' (fun a => ~ P a) b)).
    rewrite (H P b), (H' P b). tauto.
  Qed.

  (** It exchanges the homomorphism properties: the contrapositive of a
      strict, disjunctive transformer is terminating and conjunctive, and
      conversely.  The two halves about families are classical. *)
  Lemma Contrapositive_strict (t1 t2 : MonoPT A B) :
    Contrapositive t1 t2 -> sp_terminating t2 -> sp_strict t1.
  Proof.
    intros H Ht b H1. apply (proj1 (H _ b) H1).
    refine (getPT_mono t2 _ _ b _ (Ht b)). intros a _ Hf. exact Hf.
  Qed.

  Lemma Contrapositive_terminating (t1 t2 : MonoPT A B) :
    Contrapositive t1 t2 -> sp_strict t2 -> sp_terminating t1.
  Proof.
    intros H Hs b. apply (proj2 (H _ b)). intro H2. apply (Hs b).
    refine (getPT_mono t2 _ _ b _ H2). intros a Hn. exact (Hn I).
  Qed.

  Lemma Contrapositive_conjunctive (t1 t2 : MonoPT A B) :
    Contrapositive t1 t2 -> sp_disjunctive t2 -> sp_conjunctive t1.
  Proof.
    intros H Hd I HI P b. rewrite (H _ b). split.
    - intros Hn i. apply (proj2 (H _ b)). intro H2. apply Hn.
      refine (getPT_mono t2 _ _ b _ H2). intros a Hna Hall. exact (Hna (Hall i)).
    - intros Hall H2.
      assert (H2' : t2 (fun a => exists i, ~ P i a) b).
      { refine (getPT_mono t2 _ _ b _ H2). intros a Hna.
        apply NNPP. intro Hne. apply Hna. intro i.
        apply NNPP. intro Hp. apply Hne. exists i. exact Hp. }
      apply (Hd I HI (fun i a => ~ P i a) b) in H2'. destruct H2' as [i Hi].
      exact (proj1 (H _ b) (Hall i) Hi).
  Qed.

  Lemma Contrapositive_disjunctive (t1 t2 : MonoPT A B) :
    Contrapositive t1 t2 -> sp_conjunctive t2 -> sp_disjunctive t1.
  Proof.
    intros H Hc I HI P b. rewrite (H _ b). split.
    - intro Hn. apply NNPP. intro Hne. apply Hn.
      refine (getPT_mono t2 (fun a => forall i, ~ P i a) _ b _ _).
      + intros a Hall [i Hi]. exact (Hall i Hi).
      + apply (Hc I HI (fun i a => ~ P i a) b). intro i.
        apply NNPP. intro H2. apply Hne. exists i. apply (proj2 (H _ b)). exact H2.
    - intros [i Hi] H2. apply (proj1 (H _ b) Hi).
      refine (getPT_mono t2 _ _ b _ H2). intros a Hna Hp. apply Hna. exists i. exact Hp.
  Qed.
  (** So [pt_dual] carries each refinement of the carrier onto its
      opposite. *)
  Lemma pt_dual_strict (t : MonoPT A B) : sp_terminating t -> sp_strict (pt_dual t).
  Proof. exact (Contrapositive_strict _ _ (Contrapositive_pt_dual t)). Qed.

  Lemma pt_dual_terminating (t : MonoPT A B) : sp_strict t -> sp_terminating (pt_dual t).
  Proof. exact (Contrapositive_terminating _ _ (Contrapositive_pt_dual t)). Qed.

  Lemma pt_dual_conjunctive (t : MonoPT A B) :
    sp_disjunctive t -> sp_conjunctive (pt_dual t).
  Proof. exact (Contrapositive_conjunctive _ _ (Contrapositive_pt_dual t)). Qed.

  Lemma pt_dual_disjunctive (t : MonoPT A B) :
    sp_conjunctive t -> sp_disjunctive (pt_dual t).
  Proof. exact (Contrapositive_disjunctive _ _ (Contrapositive_pt_dual t)). Qed.
End Contrapositive.

(* ================================================================= *)
(** ** The Galois relation                                           *)
(* ================================================================= *)

(** [s] in [MonoPT A B] is left adjoint to [w] in [MonoPT B A]: [s P] lies
    inside [Q] exactly when [P] lies inside [w Q]. *)

Definition GaloisPT {A B} (s : MonoPT A B) (w : MonoPT B A) : Prop :=
  forall P Q, (forall b, s P b -> Q b) <-> (forall a, P a -> w Q a).

Section Galois.
  Context {A B : Type}.

  Lemma GaloisPT_unit (s : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s w -> forall P a, P a -> w (s P) a.
  Proof. intros G P. apply (proj1 (G P (s P))). intros b H. exact H. Qed.

  Lemma GaloisPT_counit (s : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s w -> forall Q b, s (w Q) b -> Q b.
  Proof. intros G Q. apply (proj2 (G (w Q) Q)). intros a H. exact H. Qed.

  (** Adjoints are unique on each side. *)
  Lemma GaloisPT_right_unique (s : MonoPT A B) (w1 w2 : MonoPT B A) :
    GaloisPT s w1 -> GaloisPT s w2 -> pt_eq w1 w2.
  Proof.
    intros G1 G2 Q a. split.
    - apply (proj1 (G2 (w1 Q) Q)). exact (GaloisPT_counit s w1 G1 Q).
    - apply (proj1 (G1 (w2 Q) Q)). exact (GaloisPT_counit s w2 G2 Q).
  Qed.

  Lemma GaloisPT_left_unique (s1 s2 : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s1 w -> GaloisPT s2 w -> pt_eq s1 s2.
  Proof.
    intros G1 G2 P b. split.
    - apply (proj2 (G1 P (s2 P))). exact (GaloisPT_unit s2 w G2 P).
    - apply (proj2 (G2 P (s1 P))). exact (GaloisPT_unit s1 w G1 P).
  Qed.

  (** Passing to the adjoint reverses the order. *)
  Lemma GaloisPT_antitone (s1 s2 : MonoPT A B) (w1 w2 : MonoPT B A) :
    GaloisPT s1 w1 -> GaloisPT s2 w2 -> (pt_le s1 s2 <-> pt_le w2 w1).
  Proof.
    intros G1 G2. split.
    - intros H Q. apply (proj1 (G1 (w2 Q) Q)).
      intros b Hb. exact (GaloisPT_counit s2 w2 G2 Q b (H _ b Hb)).
    - intros H P. apply (proj2 (G1 P (s2 P))).
      intros a Ha. exact (H _ a (GaloisPT_unit s2 w2 G2 P a Ha)).
  Qed.

  (** A left adjoint preserves all joins, a right adjoint all meets. *)
  Lemma GaloisPT_left_strict (s : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s w -> sp_strict s.
  Proof.
    intros G b Hs.
    refine (proj2 (G (fun _ => False) (fun _ => False)) _ b Hs). intros a [].
  Qed.

  Lemma GaloisPT_left_disjunctive (s : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s w -> sp_disjunctive s.
  Proof.
    intros G I _ P b. split.
    - revert b. apply (proj2 (G _ (fun b => exists i, s (P i) b))).
      intros a [i Hi].
      refine (getPT_mono w _ _ a _ (GaloisPT_unit s w G (P i) a Hi)).
      intros b Hb. exists i. exact Hb.
    - intros [i Hi]. refine (getPT_mono s _ _ b _ Hi). intros a Ha. exists i. exact Ha.
  Qed.

  Lemma GaloisPT_right_terminating (s : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s w -> sp_terminating w.
  Proof.
    intros G a.
    apply (proj1 (G (fun _ => True) (fun _ => True))); [ intros; exact I | exact I ].
  Qed.

  Lemma GaloisPT_right_conjunctive (s : MonoPT A B) (w : MonoPT B A) :
    GaloisPT s w -> sp_conjunctive w.
  Proof.
    intros G I _ Q a. split.
    - intros H i. refine (getPT_mono w _ _ a _ H). intros b Hb. exact (Hb i).
    - revert a. apply (proj1 (G (fun a => forall i, w (Q i) a) _)).
      intros b Hb i. apply (GaloisPT_counit s w G (Q i) b).
      refine (getPT_mono s _ _ b _ Hb). intros a Ha. exact (Ha i).
  Qed.
End Galois.

Lemma GaloisPT_eq {A B} (s s' : MonoPT A B) (w w' : MonoPT B A) :
  pt_eq s s' -> pt_eq w w' -> GaloisPT s w -> GaloisPT s' w'.
Proof.
  intros Es Ew G P Q. split.
  - intros H a Ha. apply (Ew Q a). refine (proj1 (G P Q) _ a Ha).
    intros b Hb. apply H. apply (Es P b). exact Hb.
  - intros H b Hb. refine (proj2 (G P Q) _ b (proj2 (Es P b) Hb)).
    intros a Ha. apply (Ew Q a). exact (H a Ha).
Qed.

(** The contrapositives of an adjoint pair are adjoint the other way round.
    Classical. *)
Lemma GaloisPT_dual {A B} (s : MonoPT A B) (w : MonoPT B A) :
  GaloisPT s w -> GaloisPT (pt_dual w) (pt_dual s).
Proof.
  intros G Q P.
  change ((forall a, ~ w (fun b => ~ Q b) a -> P a) <->
          (forall b, Q b -> ~ s (fun a => ~ P a) b)).
  split.
  - intros H b Hq Hs.
    refine (proj2 (G (fun a => ~ P a) (fun b => ~ Q b)) _ b Hs Hq).
    intros a Hnp. apply NNPP. intro Hw. exact (Hnp (H a Hw)).
  - intros H a Hw. apply NNPP. intro Hnp. apply Hw.
    refine (proj1 (G (fun a => ~ P a) (fun b => ~ Q b)) _ a Hnp).
    intros b Hs Hq. exact (H b Hq Hs).
Qed.

(* ================================================================= *)
(** ** The two triples of a transformer                              *)
(* ================================================================= *)

(** A transformer [t] gives two judgements on a pair of predicates: [R]
    lies below [t P], or above it.  For a WP transformer these are
    "the precondition is included in [wp] of the postcondition" and its
    converse; for an SP transformer, "the postcondition is included in [sp]
    of the precondition" and its converse.  Each of the three relations is
    an implication or an equivalence between such judgements. *)

Definition pt_under {A B} (t : MonoPT A B) (P : A -> Prop) (R : B -> Prop) : Prop :=
  forall b, R b -> t P b.

Definition pt_over {A B} (t : MonoPT A B) (P : A -> Prop) (R : B -> Prop) : Prop :=
  forall b, t P b -> R b.

(** Each judgement is one of the two orders, against the least transformer
    with [R] below its value at [P] or the greatest with [R] above it. *)

#[program] Definition pt_least {A B} (P : A -> Prop) (R : B -> Prop) : MonoPT A B :=
  fun P' b => R b /\ forall a, P a -> P' a.
Next Obligation.
  intros P1 P2 H b [Hr Hp]. split; [ exact Hr | intros a Ha; exact (H a (Hp a Ha)) ].
Qed.

#[program] Definition pt_greatest {A B} (P : A -> Prop) (R : B -> Prop) : MonoPT A B :=
  fun P' b => (forall a, P' a -> P a) -> R b.
Next Obligation.
  intros P1 P2 H b H1 H2. apply H1. intros a Ha. exact (H2 a (H a Ha)).
Qed.

Section Triples.
  Context {A B : Type}.

  Lemma pt_under_least (t : MonoPT A B) P R :
    pt_under t P R <-> pt_le (pt_least P R) t.
  Proof.
    split.
    - intros H P' b [Hr Hp]. exact (getPT_mono t P P' b Hp (H b Hr)).
    - intros H b Hr. apply (H P b). split; [ exact Hr | intros a Ha; exact Ha ].
  Qed.

  Lemma pt_over_greatest (t : MonoPT A B) P R :
    pt_over t P R <-> pt_le t (pt_greatest P R).
  Proof.
    split.
    - intros H P' b Ht Hp. exact (H b (getPT_mono t P' P b Hp Ht)).
    - intros H b Ht. apply (H P b Ht). intros a Ha. exact Ha.
  Qed.

  (** The order is implication of [pt_under] triples, and of [pt_over]
      triples the other way round. *)
  Lemma pt_le_under (t1 t2 : MonoPT A B) :
    pt_le t1 t2 <-> (forall P R, pt_under t1 P R -> pt_under t2 P R).
  Proof.
    split.
    - intros H P R H1 b Hb. exact (H P b (H1 b Hb)).
    - intros H P b Hb. exact (H P (t1 P) (fun _ h => h) b Hb).
  Qed.

  Lemma pt_le_over (t1 t2 : MonoPT A B) :
    pt_le t1 t2 <-> (forall P R, pt_over t2 P R -> pt_over t1 P R).
  Proof.
    split.
    - intros H P R H2 b Hb. exact (H2 b (H P b Hb)).
    - intros H P b Hb. exact (H P (t2 P) (fun _ h => h) b Hb).
  Qed.

  (** A contrapositive pair exchanges the two triples at the negated
      predicates.  The second is classical. *)
  Lemma Contrapositive_under_over (t1 t2 : MonoPT A B) P R :
    Contrapositive t1 t2 ->
    (pt_under t1 P R <-> pt_over t2 (fun a => ~ P a) (fun b => ~ R b)).
  Proof.
    intro H. split.
    - intros H1 b H2 Hr. exact (proj1 (H P b) (H1 b Hr) H2).
    - intros H2 b Hr. apply (proj2 (H P b)). intro Ht. exact (H2 b Ht Hr).
  Qed.

  Lemma Contrapositive_over_under (t1 t2 : MonoPT A B) P R :
    Contrapositive t1 t2 ->
    (pt_over t1 P R <-> pt_under t2 (fun a => ~ P a) (fun b => ~ R b)).
  Proof.
    intro H. split.
    - intros H1 b Hnr. apply NNPP. intro H2. apply Hnr. apply H1.
      apply (proj2 (H P b)). exact H2.
    - intros H2 b H1. apply NNPP. intro Hnr. exact (proj1 (H P b) H1 (H2 b Hnr)).
  Qed.
End Triples.

(** An adjoint pair has the same triples, one read over and one under. *)
Lemma GaloisPT_over_under {A B} (s : MonoPT A B) (w : MonoPT B A) P Q :
  GaloisPT s w -> (pt_over s P Q <-> pt_under w Q P).
Proof. intro G. exact (G P Q). Qed.
