(** * The ASLP specification monads

    [ASLP], [ASLPSt S] and [ASLPStExc S], all at input [unit].  With
    [ArrowLaws] and [ArrowApplyLaws] in hand ([ASLPArrowRel.v]),
    [Arrows/SPostArr.v]'s generic construction gives the monad and ALL of
    [MonadLawsE] for free -- which is what [OldMonads/ASLPMonad.v] builds by
    hand.

    The arrow is in [ASLPArrowCore.v] and its relational reasoning in
    [ASLPArrowRel.v]; both are re-exported here, so a client still needs only
    [Require Import ASLPMonad]. *)

From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr.
From Incorrectness.Classes Require Import ArrowMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure.
From Incorrectness.Taxonomy.BaseSpecMonads Require Export ASLPArrowCore ASLPArrowRel.

(* ================================================================= *)
(** ** The monad view, at input [unit]                               *)
(* ================================================================= *)

Definition ASLP (A : Type) : Type := ASLPArr unit A.

#[global] Instance Monad_ASLP : Monad ASLP := Monad_Arrow ASLPArr unit.

#[global] Instance Eq1_ASLP : Eq1 ASLP := @Eq1_Arrow ASLPArr ArrowEq_ASLPArr.

Definition Eq1Equivalence_ASLP : @Eq1Equivalence ASLP _ Eq1_ASLP :=
  @Eq1Equivalence_Arrow ASLPArr _ _ ArrowEq_ASLPArr.

Definition MonadLawsE_ASLP : @MonadLawsE ASLP Eq1_ASLP Monad_ASLP :=
  @MonadLawsE_Arrow ASLPArr _ _ ArrowEq_ASLPArr _ _.

(* ================================================================= *)
(** ** The state and exception stacks                                *)
(* ================================================================= *)

(** As in [DSPMonad.v]: [stateArrT] and [optionArrT] lift everything above,
    with every instance pinned explicitly (leaving the stacked [ArrowEq] /
    [ArrowLaws] to resolution sends the search exponential). *)

Section Stacks.
  (** *** ASLP *)

  Definition ASLPStArr (S : Type) := stateArrT S ASLPArr.

  Definition ArrowEq_ASLPStArr (S : Type) : ArrowEq (ASLPStArr S) :=
    @ArrowEq_stateArrT S ASLPArr ArrowEq_ASLPArr.
  Definition ArrowLaws_ASLPStArr (S : Type) : ArrowLaws (ASLPStArr S) :=
    @ArrowLaws_stateArrT S ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr ArrowLaws_ASLPArr.
  Definition ArrowApply_ASLPStArr (S : Type) : ArrowApply (ASLPStArr S) :=
    @ArrowApply_stateArrT S ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr.
  Definition ArrowApplyLaws_ASLPStArr (S : Type) : ArrowApplyLaws (ASLPStArr S) :=
    @ArrowApplyLaws_stateArrT S ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      ArrowEq_ASLPArr ArrowLaws_ASLPArr ArrowApplyLaws_ASLPArr.

  Definition optASLP := optionArrT ASLPArr.

  Definition Arrow_optASLP : Arrow optASLP :=
    @Arrow_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr.
  Definition ArrowEq_optASLP : ArrowEq optASLP :=
    @ArrowEq_optionArrT ASLPArr ArrowEq_ASLPArr.
  Definition ArrowLaws_optASLP : ArrowLaws optASLP :=
    @ArrowLaws_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr
      ArrowEq_ASLPArr ArrowLaws_ASLPArr ArrowChoiceLaws_ASLPArr.
  Definition ArrowApply_optASLP : ArrowApply optASLP :=
    @ArrowApply_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr
      ArrowApply_ASLPArr.
  Definition ArrowApplyLaws_optASLP : ArrowApplyLaws optASLP :=
    @ArrowApplyLaws_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr
      ArrowApply_ASLPArr ArrowEq_ASLPArr ArrowLaws_ASLPArr
      ArrowChoiceLaws_ASLPArr ArrowApplyLaws_ASLPArr.

  Definition ASLPStExcArr (S : Type) := stateArrT S optASLP.

  Definition ArrowEq_ASLPStExcArr (S : Type) : ArrowEq (ASLPStExcArr S) :=
    @ArrowEq_stateArrT S optASLP ArrowEq_optASLP.
  Definition ArrowLaws_ASLPStExcArr (S : Type) : ArrowLaws (ASLPStExcArr S) :=
    @ArrowLaws_stateArrT S optASLP Arrow_optASLP ArrowEq_optASLP ArrowLaws_optASLP.
  Definition ArrowApply_ASLPStExcArr (S : Type) : ArrowApply (ASLPStExcArr S) :=
    @ArrowApply_stateArrT S optASLP Arrow_optASLP ArrowApply_optASLP.
  Definition ArrowApplyLaws_ASLPStExcArr (S : Type)
    : ArrowApplyLaws (ASLPStExcArr S) :=
    @ArrowApplyLaws_stateArrT S optASLP Arrow_optASLP ArrowApply_optASLP
      ArrowEq_optASLP ArrowLaws_optASLP ArrowApplyLaws_optASLP.

End Stacks.

(** *** The two stacked monads, with all their laws *)

Definition ASLPSt    (S A : Type) : Type := ASLPStArr    S unit A.
Definition ASLPStExc (S A : Type) : Type := ASLPStExcArr S unit A.

#[global] Instance Monad_ASLPSt    S : Monad (ASLPSt S)    := Monad_Arrow _ unit.
#[global] Instance Monad_ASLPStExc S : Monad (ASLPStExc S) := Monad_Arrow _ unit.

#[global] Instance Eq1_ASLPSt S : Eq1 (ASLPSt S) :=
  @Eq1_Arrow (ASLPStArr S) (ArrowEq_ASLPStArr S).
#[global] Instance Eq1_ASLPStExc S : Eq1 (ASLPStExc S) :=
  @Eq1_Arrow (ASLPStExcArr S) (ArrowEq_ASLPStExcArr S).

Definition MonadLawsE_ASLPSt S
  : @MonadLawsE (ASLPSt S) (Eq1_ASLPSt S) (Monad_ASLPSt S) :=
  @MonadLawsE_Arrow (ASLPStArr S) _ (ArrowApply_ASLPStArr S) (ArrowEq_ASLPStArr S)
    (ArrowLaws_ASLPStArr S) (ArrowApplyLaws_ASLPStArr S).
Definition MonadLawsE_ASLPStExc S
  : @MonadLawsE (ASLPStExc S) (Eq1_ASLPStExc S) (Monad_ASLPStExc S) :=
  @MonadLawsE_Arrow (ASLPStExcArr S) _ (ArrowApply_ASLPStExcArr S)
    (ArrowEq_ASLPStExcArr S) (ArrowLaws_ASLPStExcArr S)
    (ArrowApplyLaws_ASLPStExcArr S).

(* ================================================================= *)
(** ** [bind] is composition of the denoted relations                *)
(* ================================================================= *)

(** As in [DSPMonad.v]: [aslpRel] reads every arrow operation as the
    corresponding relational one ([ASLPArrowRel.v]). *)

#[global] Instance RelDenote_ASLP : @RelDenote ASLPArr _ _ _ (@aslpRel).
Proof.
  constructor.
  - intros X Y h x y. exact (aslpRel_pure h x y).
  - intros X Y Z f g x z. exact (aslpRel_comp f g x z).
  - intros X Y C f [x c] [y c']. exact (aslpRel_first f (x, c) (y, c')).
  - intros X Y C f x y. exact (aslpRel_left f x y).
  - intros X Y p y. exact (aslpRel_app p y).
Qed.

(* ================================================================= *)
(** ** Two orders                                                     *)
(* ================================================================= *)

(** The reading's own order is pointwise implication; the relational order
    is inclusion of the denoted relation.  Like DSP, ASLP is neither
    monotone nor antitone in the relation, so the two come apart, and only
    the relational one is a specification-monad order: [bind] is not
    monotone for the reading's ([not_OrderedMonad_ASLPSt]). *)

Definition ordASLP {A} (m n : ASLP A) : Prop :=
  forall P b, getASLP m P b -> getASLP n P b.
Definition ordASLPSt {S A} (m n : ASLPSt S A) : Prop :=
  forall P b, getASLP m P b -> getASLP n P b.
Definition ordASLPStExc {S A} (m n : ASLPStExc S A) : Prop :=
  forall P b, getASLP m P b -> getASLP n P b.

Definition ordASLPRel {A} (m n : ASLP A) : Prop :=
  forall a b, aslpRel m a b -> aslpRel n a b.
Definition ordASLPStRel {S A} (m n : ASLPSt S A) : Prop :=
  forall a b, aslpRel m a b -> aslpRel n a b.
Definition ordASLPStExcRel {S A} (m n : ASLPStExc S A) : Prop :=
  forall a b, aslpRel m a b -> aslpRel n a b.

#[global] Instance OrderedMonad_ASLP : OrderedMonad ASLP (@ordASLPRel).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (aslpRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk a b H.
    destruct (proj1 (rel_bind (arr := ASLPArr) (rel := @aslpRel) m1 k1 a b) H)
      as [x [H1 H2]].
    apply (proj2 (rel_bind (arr := ASLPArr) (rel := @aslpRel) m2 k2 a b)).
    exists x. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.

#[global] Instance OrderedMonad_ASLPSt S : OrderedMonad (ASLPSt S) (@ordASLPStRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (aslpRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (relS_bind (arr := ASLPArr) (rel := @aslpRel) S m1 k1 i s b) H)
      as [x [s' [H1 H2]]].
    apply (proj2 (relS_bind (arr := ASLPArr) (rel := @aslpRel) S m2 k2 i s b)).
    exists x, s'. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.

#[global] Instance OrderedMonad_ASLPStExc S
  : OrderedMonad (ASLPStExc S) (@ordASLPStExcRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (aslpRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (relE_bind (arr := ASLPArr) (rel := @aslpRel) S m1 k1 i s b) H)
      as [o1 [H1 H2]].
    apply (proj2 (relE_bind (arr := ASLPArr) (rel := @aslpRel) S m2 k2 i s b)).
    exists o1. split; [ exact (Hm _ _ H1) |].
    destruct o1 as [[x s']|]; [ exact (Hk x _ _ H2) | exact H2 ].
Qed.

(* ================================================================= *)
(** ** Readings at a shared precondition                             *)
(* ================================================================= *)

Definition aslpOfRelArr {X Y} (R : SPureArr X Y) : ASLPArr X Y :=
  exist _ (aslpOf R) (aslp_healthy_hom _ (ex_intro _ R (fun P y => iff_refl _))).

Lemma aslpRel_ofRelArr {X Y} (R : SPureArr X Y) x y :
  aslpRel (aslpOfRelArr R) x y <-> R x y.
Proof. exact (aslpRel_of R (aslpOfRelArr R) (fun P y => iff_refl _) x y). Qed.

Lemma getASLP_cong {X Y} (w : ASLPArr X Y) (P Q : X -> Prop) y :
  (forall x, P x <-> Q x) -> (getASLP w P y <-> getASLP w Q y).
Proof.
  intro H. rewrite (aslpRel_spec w P y), (aslpRel_spec w Q y).
  unfold aslpOf, aspOf, dslpOf. split; intros [[x [Hx Hr]] | Hall].
  - left. exists x. split; [ apply H; exact Hx | exact Hr ].
  - right. intros x' Hr'. apply H. exact (Hall x' Hr').
  - left. exists x. split; [ apply H; exact Hx | exact Hr ].
  - right. intros x' Hr'. apply H. exact (Hall x' Hr').
Qed.

Definition aslpOfPred {A} (Q : A -> Prop) : ASLP A := aslpOfRelArr (fun (_ : unit) a => Q a).
Definition getASLPPure {A} (w : ASLP A) (p : Prop) (a : A) : Prop := getASLP w (fun _ => p) a.

Lemma getASLPPure_of {A} (Q : A -> Prop) p a :
  getASLPPure (aslpOfPred Q) p a <-> ((p /\ Q a) \/ (Q a -> p)).
Proof.
  unfold getASLPPure, aslpOfPred, aslpOfRelArr, getASLP. cbn [proj1_sig].
  unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[] [Hp Hq]] | Hall]; [ left; split; assumption | right; intro Hq'; exact (Hall tt Hq') ].
  - intros [[Hp Hq] | Hall]; [ left; exists tt; split; assumption | right; intros [] Hq'; exact (Hall Hq') ].
Qed.

Definition aslpOfRelSt {S A} (R : S -> A * S -> Prop) : ASLPSt S A :=
  aslpOfRelArr (fun (p : unit * S) r => R (snd p) r).
Definition getASLPSt {S A} (w : ASLPSt S A) (pre : S -> Prop) (r : A * S) : Prop :=
  getASLP w (fun p => pre (snd p)) r.

Lemma getASLPSt_rel {S A} (w : ASLPSt S A) pre r :
  getASLPSt w pre r
  <-> (exists s, pre s /\ aslpRel w (tt, s) r) \/ (forall s, aslpRel w (tt, s) r -> pre s).
Proof.
  unfold getASLPSt. rewrite aslpRel_spec. unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] | Hall];
      [ left; exists s; split; assumption | right; intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] | Hall];
      [ left; exists (tt, s); split; assumption | right; intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.

Lemma aslpRelSt_of {S A} (R : S -> A * S -> Prop) s r :
  aslpRel (aslpOfRelSt R) (tt, s) r <-> R s r.
Proof. exact (aslpRel_ofRelArr (fun (p : unit * S) r => R (snd p) r) (tt, s) r). Qed.

Lemma getASLPSt_of {S A} (R : S -> A * S -> Prop) pre r :
  getASLPSt (aslpOfRelSt R) pre r <-> (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s).
Proof. rewrite getASLPSt_rel. setoid_rewrite aslpRelSt_of. reflexivity. Qed.

Lemma ordASLPSt_get {S A} (m n : ASLPSt S A) :
  ordASLPSt m n <-> (forall pre r, getASLPSt m pre r -> getASLPSt n pre r).
Proof.
  split.
  - intros H pre r. apply H.
  - intros H P r HP.
    refine (proj1 (getASLP_cong n (fun p => P (tt, snd p)) P r _) _);
      [ intros [[] s]; reflexivity |].
    apply (H (fun s => P (tt, s)) r).
    refine (proj1 (getASLP_cong m P (fun p => P (tt, snd p)) r _) HP).
    intros [[] s]; reflexivity.
Qed.

Lemma aslpRelSt_bind_of {S A B} (R : S -> A * S -> Prop) (K : A -> S -> B * S -> Prop) s r :
  aslpRel (bind (aslpOfRelSt R) (fun a => aslpOfRelSt (K a))) (tt, s) r
  <-> exists a s', R s (a, s') /\ K a s' r.
Proof.
  etransitivity;
    [ exact (relS_bind (arr := ASLPArr) (rel := @aslpRel) S
               (aslpOfRelSt R) (fun a => aslpOfRelSt (K a)) tt s r) |].
  setoid_rewrite aslpRelSt_of. reflexivity.
Qed.

Definition aslpOfRelStExc {S A} (R : S -> option (A * S) -> Prop) : ASLPStExc S A :=
  aslpOfRelArr (fun (p : unit * S) r => R (snd p) r).
Definition getASLPStExc {S A} (w : ASLPStExc S A) (pre : S -> Prop)
  (r : option (A * S)) : Prop :=
  getASLP w (fun p => pre (snd p)) r.

Lemma getASLPStExc_of {S A} (R : S -> option (A * S) -> Prop) pre r :
  getASLPStExc (aslpOfRelStExc R) pre r
  <-> (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s).
Proof.
  unfold getASLPStExc, aslpOfRelStExc, aslpOfRelArr, getASLP. cbn [proj1_sig].
  unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] | Hall];
      [ left; exists s; split; assumption | right; intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] | Hall];
      [ left; exists (tt, s); split; assumption | right; intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.

(* ================================================================= *)
(** ** The reading's order is not a specification-monad order         *)
(* ================================================================= *)

(** The dual of [DSPMonad.not_OrderedMonad_DSPSt], with the inclusion
    reversed: an unreachable outcome is TOP for ASLP, so [aslpR1 <= aslpR0]
    ([aslpR0] may drop what [aslpR1] reaches).  After [aslpK] merges both
    states onto [(tt, false)], [aslpR0]'s single start state [false] is not
    in [{true}], while [aslpR1] reached the outcome from [true]. *)
Definition aslpR0 (s : bool) (r : unit * bool) : Prop := s = false /\ r = (tt, false).
Definition aslpR1 (s : bool) (r : unit * bool) : Prop := r = (tt, s).
Definition aslpK (_ : unit) (_ : bool) (r : unit * bool) : Prop := r = (tt, false).

Lemma aslp_R1_le_R0 : ordASLPSt (aslpOfRelSt aslpR1) (aslpOfRelSt aslpR0).
Proof.
  apply (proj2 (ordASLPSt_get _ _)). intros pre r H0.
  pose proof (proj1 (getASLPSt_of _ _ _) H0) as H. clear H0.
  apply (proj2 (getASLPSt_of _ _ _)). unfold aslpR0, aslpR1 in *.
  destruct H as [[s [Hp Hr]] | Hall].
  - subst r. destruct s.
    + right. intros t [_ Ht]. discriminate Ht.
    + left. exists false. split; [ exact Hp | split; reflexivity ].
  - right. intros t [Ht Hr]. subst t r. exact (Hall false eq_refl).
Qed.

Lemma aslp_bind_R1_R0 :
  ~ ordASLPSt (bind (aslpOfRelSt aslpR1) (fun a => aslpOfRelSt (aslpK a)))
              (bind (aslpOfRelSt aslpR0) (fun a => aslpOfRelSt (aslpK a))).
Proof.
  intro H0.
  pose proof (proj1 (ordASLPSt_get _ _) H0 (fun s => s = true) (tt, false)) as H.
  clear H0. rewrite !getASLPSt_rel in H. setoid_rewrite aslpRelSt_bind_of in H.
  unfold aslpR0, aslpR1, aslpK in H.
  lapply H.
  - intros [[s [Hs [a [s' [[Hs0 _] _]]]]] | Hall].
    + congruence.
    + assert (E : false = true).
      { apply Hall. exists tt, false. split; [ split; reflexivity | reflexivity ]. }
      discriminate E.
  - left. exists true. split; [ reflexivity |].
    exists tt, true. split; reflexivity.
Qed.

Theorem not_OrderedMonad_ASLPSt :
  ~ @OrderedMonad (ASLPSt bool) (Monad_ASLPSt bool) (Eq1_ASLPSt bool) (@ordASLPSt bool).
Proof.
  intros [_ _ Hbind]. apply aslp_bind_R1_R0.
  apply (Hbind unit unit _ _ aslp_R1_le_R0). intros a P b Hb. exact Hb.
Qed.
