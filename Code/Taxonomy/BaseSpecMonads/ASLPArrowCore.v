(** * [ASLPArr]: the arrow of ASLP predicate transformers

    The dual of [DSPArrowCore.v]: the carrier refines [Arrows/SPArr.SPArrT]
    by monotonicity, termination and disjunctivity, which [aslp_hom_iff]
    shows are exactly the ASLPs of relations, and the arrow operations split
    an element into its ASP part and its DSLP part, run the operation on
    each separately, and DISJOIN.

    As in the DSP case the relational machinery cannot be deferred to
    [ASLPArrowRel.v] -- the operations are DEFINED through the split, so
    [aslpRel] and the two parts live here.

    The recovery probe is the dual one ([aslpOf_rel]): where DSP asks "some
    state reaches [y], and not one outside [pre]", ASLP asks "no state
    reaches [y] vacuously, and [x] does".

    See [DSPArrowCore.v] for the full discussion; everything here mirrors it.

    The operations are ASP's and DSLP's OWN, not re-derivations of them:
    [pure_ASLP] is [pureASP] or [pureDSLP], [comp_ASLP] is [compASP]
    or [compDSLP] on the two parts, and likewise for [first] and [left].
    That is what makes the recipe visible in the definitions -- an operation
    on a ASLP arrow IS the ASP operation and the DSLP operation, run
    separately and recombined.

    [arr_app] is the one exception: its type mentions the arrow itself, so
    [appASP] lives at domain [ASPArr A B * A] and cannot be used at
    [ASLPArr A B * A].  It is built directly from the recovered relation. *)


From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr SPArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure ASPArrowCore DSLPArrowCore.

(** Representability: [w] is the ASLP of some relation. *)
Definition ASLPhealthy {X Y} (w : SPArrT X Y) : Prop :=
  exists R : SPureArr X Y, forall P y, w P y <-> aslpOf R P y.

(** The ASLP of a relation is monotone, preserves top as a DSLP does, and is
    disjunctive over nonempty families as an ASP is. *)
Lemma aslp_healthy_hom {X Y} (w : SPArrT X Y) :
  ASLPhealthy w -> sp_monotone w /\ sp_terminating w /\ sp_disjunctive w.
Proof.
  intros [R HR]. split; [| split ].
  - intros P Q HPQ y Hw. apply HR in Hw. apply HR. destruct Hw as [[x [Hx HRx]] | Hd].
    + left. exists x. split; [ exact (HPQ x Hx) | exact HRx ].
    + right. intros x Hx. exact (HPQ x (Hd x Hx)).
  - intro y. apply (HR _ y). right. intros x _. exact I.
  - intros I [i0] P y. rewrite (HR _ y). split.
    + intros [[x [[i Hi] HRx]] | Hd].
      * exists i. apply (HR _ y). left. exists x. split; assumption.
      * destruct (classic (exists x, R x y)) as [[x HRx] | Hno].
        -- destruct (Hd x HRx) as [i Hi]. exists i. apply (HR _ y). left. exists x. split; assumption.
        -- exists i0. apply (HR _ y). right. intros x HRx. destruct (Hno (ex_intro _ x HRx)).
    + intros [i Hw]. apply (HR _ y) in Hw. destruct Hw as [[x [Hx HRx]] | Hd].
      * left. exists x. split; [ exists i; exact Hx | exact HRx ].
      * right. intros x HRx. exists i. exact (Hd x HRx).
Qed.

(** Conversely, a monotone, top-preserving and disjunctive transformer is
    the ASLP of the relation [aslpRel] probes: [x] reaches [y] when [w]
    rejects [y] at the empty precondition and accepts it at [{x}]. *)
Lemma aslp_hom_healthy {X Y} (w : SPArrT X Y) :
  sp_monotone w /\ sp_terminating w /\ sp_disjunctive w -> ASLPhealthy w.
Proof.
  intros [Hm [Ht Hd]].
  (* [P] lies below the union of [False] and the singletons of its elements *)
  assert (Hsplit : forall P y,
             w P y <-> w (fun _ => False) y \/ exists x, P x /\ w (fun z => z = x) y).
  { intros P y. split.
    - intro Hw.
      pose (F := fun (i : option { x : X | P x }) (z : X) =>
                   match i with Some x => z = proj1_sig x | None => False end).
      assert (HF : w (fun z => exists i, F i z) y).
      { apply (Hm P); [| exact Hw ]. intros z Hz. exists (Some (exist _ z Hz)). reflexivity. }
      apply (Hd _ (inhabits None) F y) in HF.
      destruct HF as [[[x Hx] |] Hw']; [ right; exists x; split; [ exact Hx | exact Hw' ] | left; exact Hw' ].
    - intros [Hw | [x [Hx Hw]]].
      + apply (Hm (fun _ => False)); [ intros z [] | exact Hw ].
      + apply (Hm (fun z => z = x)); [ intros z ->; exact Hx | exact Hw ]. }
  exists (fun x y => ~ w (fun _ => False) y /\ w (fun z => z = x) y).
  intros P y. unfold aslpOf, aspOf, dslpOf.
  destruct (classic (w (fun _ => False) y)) as [Hbot | Hnbot].
  - split.
    + intros _. right. intros x [Hn _]. destruct (Hn Hbot).
    + intros _. apply (Hm (fun _ => False)); [ intros x [] | exact Hbot ].
  - rewrite (Hsplit P y). split.
    + intros [Hw | [x [Hx Hw]]]; [ contradiction |].
      left. exists x. split; [ exact Hx | split; assumption ].
    + intros [[x [Hx [_ Hw]]] | Hall]; [ right; exists x; split; assumption |].
      destruct (proj1 (Hsplit (fun _ => True) y) (Ht y)) as [Hw | [x0 [_ Hw0]]];
        [ contradiction |].
      right. exists x0. split; [ exact (Hall x0 (conj Hnbot Hw0)) | exact Hw0 ].
Qed.

Theorem aslp_hom_iff {X Y} (w : SPArrT X Y) :
  ASLPhealthy w <-> sp_monotone w /\ sp_terminating w /\ sp_disjunctive w.
Proof. split; [ apply aslp_healthy_hom | apply aslp_hom_healthy ]. Qed.

Definition ASLPArr (X Y : Type) : Type :=
  { w : SPArrT X Y | sp_monotone w /\ sp_terminating w /\ sp_disjunctive w }.

Definition getASLP {X Y} (w : ASLPArr X Y) : (X -> Prop) -> Y -> Prop := proj1_sig w.

Definition ASLPArr_eq {X Y} (w v : ASLPArr X Y) : Prop :=
  forall P y, getASLP w P y <-> getASLP v P y.

Definition aslpRel {X Y} (w : ASLPArr X Y) : SPureArr X Y :=
  fun x y => ~ getASLP w (fun _ => False) y /\ getASLP w (fun z => z = x) y.

Lemma aslpRel_of {X Y} (R : SPureArr X Y) (w : ASLPArr X Y) :
  (forall P y, getASLP w P y <-> aslpOf R P y) -> Pred_eq (aslpRel w) R.
Proof.
  intros Hw x y. unfold aslpRel. rewrite !Hw. symmetry. apply aslpOf_rel.
Qed.

Lemma aslpOf_cong {X Y} (R R' : SPureArr X Y) :
  Pred_eq R R' -> forall P y, aslpOf R P y <-> aslpOf R' P y.
Proof.
  intros H P y. unfold aslpOf, aspOf, dslpOf.
  split; (intros [[x [HP Hx]] | Hd];
          [ left; exists x; split; [ exact HP | apply H; exact Hx ]
          | right; intros x Hx; apply Hd; apply H; exact Hx ]).
Qed.

Lemma aslpRel_spec {X Y} (w : ASLPArr X Y) P y :
  getASLP w P y <-> aslpOf (aslpRel w) P y.
Proof.
  destruct (aslp_hom_healthy _ (proj2_sig w)) as [R HR].
  assert (Hrel : Pred_eq (aslpRel w) R) by (apply aslpRel_of; exact HR).
  unfold getASLP. rewrite HR. exact (aslpOf_cong R (aslpRel w) (fun a b => iff_sym (Hrel a b)) P y).
Qed.

(** The two parts, as GENUINE [ASPArr] / [DSLPArr] elements rather than
    bare transformers -- see [DSPArrowCore.v].  [aspOf] preserves joins and
    [dslpOf] preserves meets, which is each carrier's healthiness condition,
    so the operations below can be ASP's and DSLP's own. *)

Definition aspPartAArr {X Y} (w : ASLPArr X Y) : ASPArr X Y :=
  mkASPArr (aspOf (aslpRel w)) (fun P b => aspOf_join (aslpRel w) P b).

Definition dslpPartAArr {X Y} (w : ASLPArr X Y) : DSLPArr X Y :=
  mkDSLPArr (dslpOf (aslpRel w)) (fun P b => dslpOf_meet (aslpRel w) P b).

Definition aspPartA  {X Y} (w : ASLPArr X Y) : (X -> Prop) -> Y -> Prop :=
  getASPArr (aspPartAArr w).
Definition dslpPartA {X Y} (w : ASLPArr X Y) : (X -> Prop) -> Y -> Prop :=
  getDSLPArr (dslpPartAArr w).

(** [ASLPMonad]'s split, at the arrow. *)
Theorem aslp_split {X Y} (w : ASLPArr X Y) P y :
  getASLP w P y <-> (aspPartA w P y \/ dslpPartA w P y).
Proof. exact (aslpRel_spec w P y). Qed.

Theorem aslpRel_faithful {X Y} (w v : ASLPArr X Y) :
  Pred_eq (aslpRel w) (aslpRel v) -> ASLPArr_eq w v.
Proof.
  intros H P y. rewrite (aslpRel_spec w P y), (aslpRel_spec v P y).
  exact (aslpOf_cong _ _ H P y).
Qed.

Theorem aslpRel_faithful_conv {X Y} (w v : ASLPArr X Y) :
  ASLPArr_eq w v -> Pred_eq (aslpRel w) (aslpRel v).
Proof.
  intros H x y. unfold aslpRel. split.
  - intros [Hn Hs]. split; [| apply H; exact Hs ].
    intro Hc. apply Hn. apply H. exact Hc.
  - intros [Hn Hs]. split; [| apply H; exact Hs ].
    intro Hc. apply Hn. apply H. exact Hc.
Qed.

#[local] Obligation Tactic := idtac.

(** *** The operations: split, operate on each part, DISJOIN *)

#[program] Definition pure_ASLP {X Y} (h : X -> Y) : ASLPArr X Y :=
  fun P y => pureASP h P y \/ pureDSLP h P y.
Next Obligation.
  intros X Y h. apply aslp_healthy_hom. exists (arr_pure h). intros P y. reflexivity.
Qed.

#[program] Definition comp_ASLP {X Y Z} (w : ASLPArr X Y) (v : ASLPArr Y Z)
  : ASLPArr X Z :=
  fun P z => compASP  (aspPartAArr  w) (aspPartAArr  v) P z
             \/ compDSLP (dslpPartAArr w) (dslpPartAArr v) P z.
Next Obligation.
  intros X Y Z w v. apply aslp_healthy_hom. exists (arr_comp (aslpRel w) (aslpRel v)). intros P z.
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_comp (aslpRel w) (aslpRel v)), (dslpOf_comp (aslpRel w) (aslpRel v)).
  reflexivity.
Qed.

#[program] Definition first_ASLP {X Y C} (w : ASLPArr X Y)
  : ASLPArr (X * C) (Y * C) :=
  fun P q => @firstASP  _ _ C (aspPartAArr  w) P q
             \/ @firstDSLP _ _ C (dslpPartAArr w) P q.
Next Obligation.
  intros X Y C w. apply aslp_healthy_hom. exists (arr_first (aslpRel w)). intros P q.
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_first (aslpRel w)), (dslpOf_first (aslpRel w)).
  reflexivity.
Qed.

#[global] Instance Arrow_ASLPArr : Arrow ASLPArr := {
  arr_pure  := @pure_ASLP ;
  arr_comp  := @comp_ASLP ;
  arr_first := @first_ASLP
}.

#[global] Instance ASLPArr_eq_Equivalence {X Y} : Equivalence (@ASLPArr_eq X Y).
Proof.
  constructor.
  - intros w P y. reflexivity.
  - intros w v H P y. symmetry. exact (H P y).
  - intros u w v H1 H2 P y. exact (iff_trans (H1 P y) (H2 P y)).
Qed.

#[global] Instance ArrowEq_ASLPArr : ArrowEq ASLPArr := {
  arrow_eq := @ASLPArr_eq ;
  arrow_eq_equiv := @ASLPArr_eq_Equivalence
}.
(* ----------------------------------------------------------------- *)
(** *** [ArrowApply] for ASLP, the same way                           *)
(* ----------------------------------------------------------------- *)

Definition appRelA {A B} : SPureArr (ASLPArr A B * A) B :=
  fun p b => aslpRel (fst p) (snd p) b.

#[program] Definition app_ASLP {A B} : ASLPArr (ASLPArr A B * A) B :=
  fun P b => aspOf appRelA P b \/ dslpOf appRelA P b.
Next Obligation.
  intros A B. apply aslp_healthy_hom. exists appRelA. intros P b. reflexivity.
Qed.

#[global] Instance ArrowApply_ASLPArr : ArrowApply ASLPArr := {
  arr_app := @app_ASLP
}.

(** [arr_left] for ASLP, so the two arrows offer the same operations. *)
#[program] Definition left_ASLP {X Y C} (w : ASLPArr X Y)
  : ASLPArr (X + C) (Y + C) :=
  fun P y => @leftASP  _ _ C (aspPartAArr  w) P y
             \/ @leftDSLP _ _ C (dslpPartAArr w) P y.
Next Obligation.
  intros X Y C w. apply aslp_healthy_hom. exists (arr_left (aslpRel w)). intros P [b|c]; unfold aslpOf.
  - unfold aspPartA, dslpPartA.
    rewrite (aspOf_left_inl (aslpRel w)), (dslpOf_left_inl (aslpRel w)). reflexivity.
  - rewrite (aspOf_left_inr (aslpRel w)), (dslpOf_left_inr (aslpRel w)). tauto.
Qed.

#[global] Instance ArrowChoice_ASLPArr : ArrowChoice ASLPArr := {
  arr_left := @left_ASLP
}.
