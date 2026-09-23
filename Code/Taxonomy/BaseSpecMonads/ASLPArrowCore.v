(** * [ASLPArr]: the arrow of ASLP predicate transformers

    The dual of [DSPArrowCore.v]: the carrier is a genuine ASLP transformer,
    and the arrow operations split an element into its ASP part and its DSLP
    part, run the operation on each separately, and DISJOIN.

    As in the DSP case the relational machinery cannot be deferred to
    [ASLPArrowRel.v] -- the operations are DEFINED through the split, so
    [aslpRel] and the two parts live here.

    The recovery probe is the dual one ([aslpOf_rel]): where DSP asks "some
    state reaches [y], and not one outside [pre]", ASLP asks "no state
    reaches [y] vacuously, and [x] does".

    See [DSPArrowCore.v] for the full discussion; everything here mirrors

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
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure ASPArrowCore DSLPArrowCore.

Definition ASLPhealthy {X Y} (w : (X -> Prop) -> Y -> Prop) : Prop :=
  exists R : SPureArr X Y, forall P y, w P y <-> aslpOf R P y.

Definition ASLPArr (X Y : Type) : Type := { w | @ASLPhealthy X Y w }.

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
  destruct (proj2_sig w) as [R HR].
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
  intros X Y h. exists (arr_pure h). intros P y. reflexivity.
Qed.

#[program] Definition comp_ASLP {X Y Z} (w : ASLPArr X Y) (v : ASLPArr Y Z)
  : ASLPArr X Z :=
  fun P z => compASP  (aspPartAArr  w) (aspPartAArr  v) P z
             \/ compDSLP (dslpPartAArr w) (dslpPartAArr v) P z.
Next Obligation.
  intros X Y Z w v. exists (arr_comp (aslpRel w) (aslpRel v)). intros P z.
  unfold aspPartA, dslpPartA, aslpOf.
  rewrite (aspOf_comp (aslpRel w) (aslpRel v)), (dslpOf_comp (aslpRel w) (aslpRel v)).
  reflexivity.
Qed.

#[program] Definition first_ASLP {X Y C} (w : ASLPArr X Y)
  : ASLPArr (X * C) (Y * C) :=
  fun P q => @firstASP  _ _ C (aspPartAArr  w) P q
             \/ @firstDSLP _ _ C (dslpPartAArr w) P q.
Next Obligation.
  intros X Y C w. exists (arr_first (aslpRel w)). intros P q.
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
  intros A B. exists appRelA. intros P b. reflexivity.
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
  intros X Y C w. exists (arr_left (aslpRel w)). intros P [b|c]; unfold aslpOf.
  - unfold aspPartA, dslpPartA.
    rewrite (aspOf_left_inl (aslpRel w)), (dslpOf_left_inl (aslpRel w)). reflexivity.
  - rewrite (aspOf_left_inr (aslpRel w)), (dslpOf_left_inr (aslpRel w)). tauto.
Qed.

#[global] Instance ArrowChoice_ASLPArr : ArrowChoice ASLPArr := {
  arr_left := @left_ASLP
}.
