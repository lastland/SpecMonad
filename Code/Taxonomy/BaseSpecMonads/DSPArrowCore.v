(** * [DSPArr]: the arrow of DSP predicate transformers

    The carrier is a genuine DSP transformer, and the arrow operations are
    built the way [OldMonads/DSPMonad.bindDSPStExc] builds [bind]: split an
    element into its ASP part and its DSLP part, run the operation on each
    separately, and CONJOIN.

    Unlike [ASPArrowCore.v], the relational machinery cannot be deferred to
    [DSPArrowRel.v]: the operations are DEFINED through the split, so
    [dspRel] and the two parts have to live here.  What [DSPArrowRel.v] adds
    is the reasoning -- [dspRel] as a faithful arrow morphism, and the three
    law bundles proved by transport along it.

    Why the split-then-conjoin recipe and not the naive one: the reading does
    NOT commute with composition.  Conjoining first gives
    [dspOf T (dspOf R P) z], which is STRICTLY STRONGER than
    [dspOf (arr_comp R T) P z] -- it forces the DSLP conjunct to quantify
    over intermediate points the composite never reaches.  Splitting first
    and conjoining last gives

      [aspOf T (aspOf R P) z /\ dslpOf T (dslpOf R P) z]

    which IS [dspOf (arr_comp R T) P z], by [aspOf_comp] and [dslpOf_comp].

    The price of making the carrier the transformer is that the relation has
    to be recovered by a classical probe ([dspRel], the arrow form of
    [OldMonads/DSPMonad.dsp_recov]).

    The operations are ASP's and DSLP's OWN, not re-derivations of them:
    [pure_DSP] is [pureASP] and [pureDSLP], [comp_DSP] is [compASP] and
    [compDSLP] on the two parts, and likewise for [first] and [left].  That
    is what makes the recipe visible in the definitions -- an operation on a
    DSP arrow IS the ASP operation and the DSLP operation, run separately and
    recombined.

    [arr_app] is the one exception: its type mentions the arrow itself, so
    [appASP] lives at domain [ASPArr A B * A] and cannot be used at
    [DSPArr A B * A].  It is built directly from the recovered relation. *)


From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure ASPArrowCore DSLPArrowCore.

(** Healthiness, as representability: [w] is a DSP transformer exactly when
    it is the DSP of some relation.  [DSPMonad.dsp_carrier] proves this
    equivalent to the intrinsic [Strict /\ Conjunctive]. *)
Definition DSPhealthy {X Y} (w : (X -> Prop) -> Y -> Prop) : Prop :=
  exists R : SPureArr X Y, forall P y, w P y <-> dspOf R P y.

Definition DSPArr (X Y : Type) : Type := { w | @DSPhealthy X Y w }.

Definition getDSP {X Y} (w : DSPArr X Y) : (X -> Prop) -> Y -> Prop := proj1_sig w.

Definition DSPArr_eq {X Y} (w v : DSPArr X Y) : Prop :=
  forall P y, getDSP w P y <-> getDSP v P y.

(** ** Recovery and the two parts *)

Definition dspRel {X Y} (w : DSPArr X Y) : SPureArr X Y :=
  fun x y => getDSP w (fun _ => True) y /\ ~ getDSP w (fun z => z <> x) y.

Lemma dspRel_of {X Y} (R : SPureArr X Y) (w : DSPArr X Y) :
  (forall P y, getDSP w P y <-> dspOf R P y) -> Pred_eq (dspRel w) R.
Proof.
  intros Hw x y. unfold dspRel. rewrite !Hw. symmetry. apply dspOf_rel.
Qed.

Lemma dspRel_spec {X Y} (w : DSPArr X Y) P y :
  getDSP w P y <-> dspOf (dspRel w) P y.
Proof.
  destruct (proj2_sig w) as [R HR].
  assert (Hrel : Pred_eq (dspRel w) R) by (apply dspRel_of; exact HR).
  unfold getDSP. rewrite HR. unfold dspOf, aspOf, dslpOf.
  split; intros [Ha Hd]; split.
  - destruct Ha as [x [HP Hx]]. exists x. split; [ exact HP | apply Hrel; exact Hx ].
  - intros x Hx. apply Hd. apply Hrel. exact Hx.
  - destruct Ha as [x [HP Hx]]. exists x. split; [ exact HP | apply Hrel; exact Hx ].
  - intros x Hx. apply Hd. apply Hrel. exact Hx.
Qed.

(** The two parts, as GENUINE [ASPArr] / [DSLPArr] elements rather than
    bare transformers.  [aspOf] preserves joins and [dslpOf] preserves meets
    ([SPure.aspOf_join], [SPure.dslpOf_meet]), which is exactly each
    carrier's healthiness condition -- so the parts really are an ASP arrow
    and a DSLP arrow, and the operations below can be ASP's and DSLP's own.

    [aspPart] / [dslpPart] are the same things read through the coercion,
    kept because the relational lemmas in [DSPArrowRel.v] are stated with
    them. *)

Definition aspPartArr {X Y} (w : DSPArr X Y) : ASPArr X Y :=
  mkASPArr (aspOf (dspRel w)) (fun P b => aspOf_join (dspRel w) P b).

Definition dslpPartArr {X Y} (w : DSPArr X Y) : DSLPArr X Y :=
  mkDSLPArr (dslpOf (dspRel w)) (fun P b => dslpOf_meet (dspRel w) P b).

Definition aspPart  {X Y} (w : DSPArr X Y) : (X -> Prop) -> Y -> Prop :=
  getASPArr (aspPartArr w).
Definition dslpPart {X Y} (w : DSPArr X Y) : (X -> Prop) -> Y -> Prop :=
  getDSLPArr (dslpPartArr w).

(** [DSPMonad.dsp_split], at the arrow. *)
Theorem dsp_split {X Y} (w : DSPArr X Y) P y :
  getDSP w P y <-> (aspPart w P y /\ dslpPart w P y).
Proof. exact (dspRel_spec w P y). Qed.

(** ** Faithfulness: an element is determined by its relation *)

Lemma dspOf_cong {X Y} (R R' : SPureArr X Y) :
  Pred_eq R R' -> forall P y, dspOf R P y <-> dspOf R' P y.
Proof.
  intros H P y. unfold dspOf, aspOf, dslpOf.
  split; intros [Ha Hd]; split.
  - destruct Ha as [x [HP Hx]]. exists x. split; [ exact HP | apply H; exact Hx ].
  - intros x Hx. apply Hd. apply H. exact Hx.
  - destruct Ha as [x [HP Hx]]. exists x. split; [ exact HP | apply H; exact Hx ].
  - intros x Hx. apply Hd. apply H. exact Hx.
Qed.

Theorem dspRel_faithful {X Y} (w v : DSPArr X Y) :
  Pred_eq (dspRel w) (dspRel v) -> DSPArr_eq w v.
Proof.
  intros H P y. rewrite (dspRel_spec w P y), (dspRel_spec v P y).
  exact (dspOf_cong _ _ H P y).
Qed.

Theorem dspRel_faithful_conv {X Y} (w v : DSPArr X Y) :
  DSPArr_eq w v -> Pred_eq (dspRel w) (dspRel v).
Proof.
  intros H x y. unfold dspRel. split.
  - intros [Ht Hn]. split; [ apply H; exact Ht |].
    intro Hc. apply Hn. apply H. exact Hc.
  - intros [Ht Hn]. split; [ apply H; exact Ht |].
    intro Hc. apply Hn. apply H. exact Hc.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The operations: split, operate on each part, conjoin          *)
(* ----------------------------------------------------------------- *)

#[local] Obligation Tactic := idtac.

(** [DSPMonad.retDSPStExc], at the arrow: the conjunction of ASP's and
    DSLP's [arr_pure].  Nothing to split -- the operation is atomic. *)
#[program] Definition pure_DSP {X Y} (h : X -> Y) : DSPArr X Y :=
  fun P y => pureASP h P y /\ pureDSLP h P y.
Next Obligation.
  intros X Y h. exists (arr_pure h). intros P y. reflexivity.
Qed.

(** [DSPMonad.bindDSPStExc], at the arrow.  On these carriers composition of
    the parts IS composition of predicate transformers ([aspOf_comp],
    [dslpOf_comp]), so there is no composite-relation machinery to build. *)
#[program] Definition comp_DSP {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z)
  : DSPArr X Z :=
  fun P z => compASP  (aspPartArr  w) (aspPartArr  v) P z
             /\ compDSLP (dslpPartArr w) (dslpPartArr v) P z.
Next Obligation.
  intros X Y Z w v. exists (arr_comp (dspRel w) (dspRel v)). intros P z.
  unfold aspPart, dslpPart, dspOf.
  rewrite (aspOf_comp (dspRel w) (dspRel v)), (dslpOf_comp (dspRel w) (dspRel v)).
  reflexivity.
Qed.

(** The same recipe for [arr_first]: both parts thread the [C] component the
    same way ([aspOf_first], [dslpOf_first]). *)
#[program] Definition first_DSP {X Y C} (w : DSPArr X Y)
  : DSPArr (X * C) (Y * C) :=
  fun P q => @firstASP  _ _ C (aspPartArr  w) P q
             /\ @firstDSLP _ _ C (dslpPartArr w) P q.
Next Obligation.
  intros X Y C w. exists (arr_first (dspRel w)). intros P q.
  unfold aspPart, dslpPart, dspOf.
  rewrite (aspOf_first (dspRel w)), (dslpOf_first (dspRel w)).
  reflexivity.
Qed.

#[global] Instance Arrow_DSPArr : Arrow DSPArr := {
  arr_pure  := @pure_DSP ;
  arr_comp  := @comp_DSP ;
  arr_first := @first_DSP
}.

#[global] Instance DSPArr_eq_Equivalence {X Y} : Equivalence (@DSPArr_eq X Y).
Proof.
  constructor.
  - intros w P y. reflexivity.
  - intros w v H P y. symmetry. exact (H P y).
  - intros u w v H1 H2 P y. exact (iff_trans (H1 P y) (H2 P y)).
Qed.

#[global] Instance ArrowEq_DSPArr : ArrowEq DSPArr := {
  arrow_eq := @DSPArr_eq ;
  arrow_eq_equiv := @DSPArr_eq_Equivalence
}.
(* ----------------------------------------------------------------- *)
(** *** [ArrowChoice]                                                 *)
(* ----------------------------------------------------------------- *)

(** At [inl] the two parts do what they do; at [inr] the value passes
    through and BOTH parts agree there ([aspOf_left_inr],
    [dslpOf_left_inr]), so the conjunction degenerates to the value itself. *)
#[program] Definition left_DSP {X Y C} (w : DSPArr X Y)
  : DSPArr (X + C) (Y + C) :=
  fun P y => @leftASP  _ _ C (aspPartArr  w) P y
             /\ @leftDSLP _ _ C (dslpPartArr w) P y.
Next Obligation.
  intros X Y C w. exists (arr_left (dspRel w)). intros P [b|c]; unfold dspOf.
  - unfold aspPart, dslpPart.
    rewrite (aspOf_left_inl (dspRel w)), (dslpOf_left_inl (dspRel w)). reflexivity.
  - rewrite (aspOf_left_inr (dspRel w)), (dslpOf_left_inr (dspRel w)). tauto.
Qed.

#[global] Instance ArrowChoice_DSPArr : ArrowChoice DSPArr := {
  arr_left := @left_DSP
}.
(* ----------------------------------------------------------------- *)
(** *** [ArrowApply]: the operation exists, the laws are a separate job *)
(* ----------------------------------------------------------------- *)

(** [arr_app] is ATOMIC -- there is no sub-arrow to split -- so, like
    [arr_pure], it is just the reading of the relation it should denote:
    "the arrow in the input, applied to the value in the input".

    Note what its TYPE does: [arr (arr A B * A) B] mentions the arrow
    itself, so unlike every operation above this one is NOT an instance of
    [PredArr]'s -- [PredArr]'s [arr_app] has domain [PredArr A B * A], a
    different type.  Its laws therefore do not transport, and are left open
    below. *)

Definition appRel {A B} : SPureArr (DSPArr A B * A) B :=
  fun p b => dspRel (fst p) (snd p) b.

#[program] Definition app_DSP {A B} : DSPArr (DSPArr A B * A) B :=
  fun P b => aspOf appRel P b /\ dslpOf appRel P b.
Next Obligation.
  intros A B. exists appRel. intros P b. reflexivity.
Qed.

#[global] Instance ArrowApply_DSPArr : ArrowApply DSPArr := {
  arr_app := @app_DSP
}.
