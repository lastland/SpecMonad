(** * The arrow-derived ASLP specification monads.
    Keep the recovered-relation order distinct from the pointwise reading
    order. The earlier implementation remains in OldMonads. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad ArrowMonad RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPostArr.
From Incorrectness.Taxonomy.Arrows Require Export SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSLPMonad.

Definition ASLP (A : Type) : Type := ASLPArr unit A.
#[global] Instance Monad_ASLP : Monad ASLP := Monad_Arrow ASLPArr unit.
#[global] Instance Eq1_ASLP : Eq1 ASLP := @Eq1_Arrow ASLPArr ArrowEq_ASLPArr unit.
Definition Eq1Equivalence_ASLP : @Eq1Equivalence ASLP _ Eq1_ASLP :=
  @Eq1Equivalence_Arrow ASLPArr _ _ ArrowEq_ASLPArr unit.
Definition MonadLawsE_ASLP : @MonadLawsE ASLP Eq1_ASLP Monad_ASLP :=
  @MonadLawsE_Arrow ASLPArr _ _ ArrowEq_ASLPArr _ _ unit.

Definition ASLPSt (S A : Type) : Type := ASLPStArr S unit A.
Definition ASLPStExc (S A : Type) : Type := ASLPStExcArr S unit A.
#[global] Instance Monad_ASLPSt S : Monad (ASLPSt S) := Monad_Arrow _ unit.
#[global] Instance Monad_ASLPStExc S : Monad (ASLPStExc S) := Monad_Arrow _ unit.
#[global] Instance Eq1_ASLPSt S : Eq1 (ASLPSt S) :=
  @Eq1_Arrow (ASLPStArr S) (ArrowEq_ASLPStArr S) unit.
#[global] Instance Eq1_ASLPStExc S : Eq1 (ASLPStExc S) :=
  @Eq1_Arrow (ASLPStExcArr S) (ArrowEq_ASLPStExcArr S) unit.
Definition MonadLawsE_ASLPSt S : @MonadLawsE (ASLPSt S) (Eq1_ASLPSt S) (Monad_ASLPSt S) :=
  @MonadLawsE_Arrow (ASLPStArr S) _ (ArrowApply_ASLPStArr S) (ArrowEq_ASLPStArr S)
    (ArrowLaws_ASLPStArr S) (ArrowApplyLaws_ASLPStArr S) unit.
Definition MonadLawsE_ASLPStExc S : @MonadLawsE (ASLPStExc S) (Eq1_ASLPStExc S) (Monad_ASLPStExc S) :=
  @MonadLawsE_Arrow (ASLPStExcArr S) _ (ArrowApply_ASLPStExcArr S)
    (ArrowEq_ASLPStExcArr S) (ArrowLaws_ASLPStExcArr S) (ArrowApplyLaws_ASLPStExcArr S) unit.

Definition ordASLP {A} (m n : ASLP A) : Prop := forall P b, getASLP m P b -> getASLP n P b.
Definition ordASLPSt {S A} (m n : ASLPSt S A) : Prop := forall P b, getASLP m P b -> getASLP n P b.
Definition ordASLPStExc {S A} (m n : ASLPStExc S A) : Prop := forall P b, getASLP m P b -> getASLP n P b.
Definition ordASLPRel {A} (m n : ASLP A) : Prop := forall a b, aslpRel m a b -> aslpRel n a b.
Definition ordASLPStRel {S A} (m n : ASLPSt S A) : Prop := forall a b, aslpRel m a b -> aslpRel n a b.
Definition ordASLPStExcRel {S A} (m n : ASLPStExc S A) : Prop := forall a b, aslpRel m a b -> aslpRel n a b.
#[global] Instance OrderedMonad_ASLP : OrderedMonad ASLP (@ordASLPRel).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (aslpRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk a b H.
    destruct (proj1 (@rel_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      RelArrow_ASLPArr RelArrowApply_ASLPArr unit A B m1 k1 a b) H) as [x [H1 H2]].
    apply (proj2 (@rel_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      RelArrow_ASLPArr RelArrowApply_ASLPArr unit A B m2 k2 a b)).
    exists x. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.
#[global] Instance OrderedMonad_ASLPSt S : OrderedMonad (ASLPSt S) (@ordASLPStRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (aslpRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (@relS_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      RelArrow_ASLPArr RelArrowApply_ASLPArr S unit A B m1 k1 i s b) H) as [x [s' [H1 H2]]].
    apply (proj2 (@relS_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      RelArrow_ASLPArr RelArrowApply_ASLPArr S unit A B m2 k2 i s b)).
    exists x, s'. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.
#[global] Instance OrderedMonad_ASLPStExc S : OrderedMonad (ASLPStExc S) (@ordASLPStExcRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (aslpRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (@relE_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      RelArrow_ASLPArr RelArrowApply_ASLPArr ArrowChoice_ASLPArr RelArrowChoice_ASLPArr
      S unit A B m1 k1 i s b) H) as [o1 [H1 H2]].
    apply (proj2 (@relE_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      RelArrow_ASLPArr RelArrowApply_ASLPArr ArrowChoice_ASLPArr RelArrowChoice_ASLPArr
      S unit A B m2 k2 i s b)).
    exists o1. split; [ exact (Hm _ _ H1) |].
    destruct o1 as [[x s']|]; [ exact (Hk x _ _ H2) | exact H2 ].
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
  getASLPSt w pre r <-> (exists s, pre s /\ aslpRel w (tt, s) r) \/ (forall s, aslpRel w (tt, s) r -> pre s).
Proof.
  unfold getASLPSt. rewrite aslpRel_spec. unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] | Hall];
      [ left; exists s; split; assumption | right; intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] | Hall];
      [ left; exists (tt, s); split; assumption | right; intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.
Lemma aslpRelSt_of {S A} (R : S -> A * S -> Prop) s r : aslpRel (aslpOfRelSt R) (tt, s) r <-> R s r.
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
  aslpRel (bind (aslpOfRelSt R) (fun a => aslpOfRelSt (K a))) (tt, s) r <-> exists a s', R s (a, s') /\ K a s' r.
Proof.
  etransitivity;
    [ exact (@relS_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
               RelArrow_ASLPArr RelArrowApply_ASLPArr S unit A B
               (aslpOfRelSt R) (fun a => aslpOfRelSt (K a)) tt s r) |].
  setoid_rewrite aslpRelSt_of. reflexivity.
Qed.
Definition aslpOfRelStExc {S A} (R : S -> option (A * S) -> Prop) : ASLPStExc S A :=
  aslpOfRelArr (fun (p : unit * S) r => R (snd p) r).
Definition getASLPStExc {S A} (w : ASLPStExc S A) (pre : S -> Prop) (r : option (A * S)) : Prop :=
  getASLP w (fun p => pre (snd p)) r.
Lemma getASLPStExc_of {S A} (R : S -> option (A * S) -> Prop) pre r :
  getASLPStExc (aslpOfRelStExc R) pre r <-> (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s).
Proof.
  unfold getASLPStExc, aslpOfRelStExc, aslpOfRelArr, getASLP. cbn [proj1_sig].
  unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] | Hall];
      [ left; exists s; split; assumption | right; intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] | Hall];
      [ left; exists (tt, s); split; assumption | right; intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.

(** Boolean-state counterexample for the pointwise reading order. *)
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
  unfold aslpR0, aslpR1, aslpK in H. lapply H.
  - intros [[s [Hs [a [s' [[Hs0 _] _]]]]] | Hall].
    + congruence.
    + assert (E : false = true).
      { apply Hall. exists tt, false. split; [ split; reflexivity | reflexivity ]. }
      discriminate E.
  - left. exists true. split; [ reflexivity |]. exists tt, true. split; reflexivity.
Qed.
Theorem not_OrderedMonad_ASLPSt :
  ~ @OrderedMonad (ASLPSt bool) (Monad_ASLPSt bool) (Eq1_ASLPSt bool) (@ordASLPSt bool).
Proof.
  intros [_ _ Hbind]. apply aslp_bind_R1_R0.
  apply (Hbind unit unit _ _ aslp_R1_le_R0). intros a P b Hb. exact Hb.
Qed.

(** ** Without state, ASLP is DSLP

    The dual of the collapse in [DSPMonad.v].  At input [unit] the ASP
    disjunct of an ASLP reading implies the DSLP one ([aslpOf_unit]), so the
    two healthiness conditions cut the same transformers out of
    [SPArrT unit A] ([dslp_aslp_unit_hom], [aslp_dslp_unit_hom]), and the
    identity on transformers is an isomorphism between the monads [ASLP] and
    [DSLP]: [aslp_to_dslp] and [dslp_to_aslp] are mutually inverse, preserve
    [ret] and [bind], and carry the pointwise orders to each other.

    [OldMonads/ASLPMonad.v] builds this collapse in by defining its pure
    ASLP monad through DSLP's.  Here the two monads are given independently,
    each by its own arrow.  Only [aslpOf_unit] is constructive: an ASLP
    element preserves joins, and is read through its relation, classically. *)

Lemma aslpOf_unit {A} (R : SPureArr unit A) (P : unit -> Prop) (a : A) :
  aslpOf R P a <-> dslpOf R P a.
Proof.
  unfold aslpOf, aspOf, dslpOf, asp, dslp. split.
  - intros [[[] [Hp _]] | H].
    + intros [] _. exact Hp.
    + exact H.
  - intro H. right. exact H.
Qed.

Lemma dslp_aslp_unit_hom {A} (w : SPArrT unit A) :
  sp_monotone w /\ sp_terminating w /\ sp_conjunctive w ->
  sp_monotone w /\ sp_terminating w /\ sp_disjunctive w.
Proof.
  intro H. apply aslp_healthy_hom.
  exists (dslpRelT w). intros P y.
  etransitivity; [ exact (dslp_hom_meet w H P y) |].
  symmetry. exact (aslpOf_unit (dslpRelT w) P y).
Qed.

Lemma aslp_dslp_unit_hom {A} (w : SPArrT unit A) :
  sp_monotone w /\ sp_terminating w /\ sp_disjunctive w ->
  sp_monotone w /\ sp_terminating w /\ sp_conjunctive w.
Proof.
  intro H. destruct (aslp_hom_healthy w H) as [R HR].
  apply dslp_meet_hom. intros P b.
  etransitivity; [ exact (HR P b) |].
  etransitivity; [ exact (aslpOf_unit R P b) |].
  split.
  - intros Hd a Ha. apply Ha.
    exact (proj2 (HR P b) (proj2 (aslpOf_unit R P b) Hd)).
  - intros Hall x Hx. apply Hall. intros Q HQ.
    exact (proj1 (aslpOf_unit R Q b) (proj1 (HR Q b) HQ) x Hx).
Qed.

Definition aslp_to_dslp {A} (l : ASLP A) : DSLP A :=
  exist _ (getASLP l) (aslp_dslp_unit_hom _ (proj2_sig l)).

Definition dslp_to_aslp {A} (n : DSLP A) : ASLP A :=
  exist _ (getDSLPArr n) (dslp_aslp_unit_hom _ (proj2_sig n)).

Lemma get_aslp_to_dslp {A} (l : ASLP A) P a :
  getDSLPArr (aslp_to_dslp l) P a <-> getASLP l P a.
Proof. reflexivity. Qed.

Lemma get_dslp_to_aslp {A} (n : DSLP A) P a :
  getASLP (dslp_to_aslp n) P a <-> getDSLPArr n P a.
Proof. reflexivity. Qed.

Lemma dslp_to_aslp_to_dslp {A} (n : DSLP A) :
  @eq1 DSLP Eq1_DSLP A (aslp_to_dslp (dslp_to_aslp n)) n.
Proof. intros P a. reflexivity. Qed.

Lemma aslp_to_dslp_to_aslp {A} (l : ASLP A) :
  @eq1 ASLP Eq1_ASLP A (dslp_to_aslp (aslp_to_dslp l)) l.
Proof. intros P a. reflexivity. Qed.

Lemma ordASLP_aslp_to_dslp {A} (l l' : ASLP A) :
  ordASLP l l' <-> ordDSLP (aslp_to_dslp l) (aslp_to_dslp l').
Proof. split; intro H; exact H. Qed.

Lemma ordDSLP_dslp_to_aslp {A} (n n' : DSLP A) :
  ordDSLP n n' <-> ordASLP (dslp_to_aslp n) (dslp_to_aslp n').
Proof. split; intro H; exact H. Qed.

(** The two elements denote one relation. *)
Lemma aslp_to_dslp_rel {A} (l : ASLP A) i a :
  dslpRel (aslp_to_dslp l) i a <-> aslpRel l i a.
Proof.
  destruct i. destruct (proj2_sig l) as [Hm [Ht _]].
  change ((forall P : unit -> Prop, getASLP l P a -> P tt)
          <-> ~ getASLP l (fun _ => False) a /\ getASLP l (fun z => z = tt) a).
  split.
  - intro H. split.
    + intro Hf. exact (H (fun _ => False) Hf).
    + refine (Hm _ _ _ a (Ht a)). intros [] _. reflexivity.
  - intros [Hn _] P HP. apply NNPP. intro Hp. apply Hn.
    refine (Hm _ _ _ a HP). intros [] Hx. exact (Hp Hx).
Qed.

Lemma dslp_to_aslp_rel {A} (n : DSLP A) i a :
  aslpRel (dslp_to_aslp n) i a <-> dslpRel n i a.
Proof. exact (iff_sym (aslp_to_dslp_rel (dslp_to_aslp n) i a)). Qed.

Lemma aslp_to_dslp_ret {A} (x : A) :
  @eq1 DSLP Eq1_DSLP A (aslp_to_dslp (@ret ASLP Monad_ASLP A x)) (@ret DSLP Monad_DSLP A x).
Proof.
  apply (proj2 (dslpRel_eq (aslp_to_dslp (@ret ASLP Monad_ASLP A x))
                  (@ret DSLP Monad_DSLP A x))).
  intros i a.
  etransitivity; [ exact (aslp_to_dslp_rel (@ret ASLP Monad_ASLP A x) i a) |].
  etransitivity;
    [ exact (@rel_pure ASLPArr Arrow_ASLPArr RelArrow_ASLPArr unit A (fun _ => x) i a) |].
  symmetry. exact (dslpRel_retDSLP x i a).
Qed.

Lemma aslp_to_dslp_bind {A B} (l : ASLP A) (k : A -> ASLP B) :
  @eq1 DSLP Eq1_DSLP B (aslp_to_dslp (@bind ASLP Monad_ASLP A B l k))
    (@bind DSLP Monad_DSLP A B (aslp_to_dslp l) (fun a => aslp_to_dslp (k a))).
Proof.
  apply (proj2 (dslpRel_eq (aslp_to_dslp (@bind ASLP Monad_ASLP A B l k))
                  (@bind DSLP Monad_DSLP A B (aslp_to_dslp l)
                     (fun a => aslp_to_dslp (k a))))).
  intros i b.
  etransitivity; [ exact (aslp_to_dslp_rel (@bind ASLP Monad_ASLP A B l k) i b) |].
  etransitivity;
    [ exact (@rel_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr RelArrow_ASLPArr
               RelArrowApply_ASLPArr unit A B l k i b) |].
  etransitivity;
    [| symmetry;
       exact (dslpRel_bindDSLP (aslp_to_dslp l) (fun a => aslp_to_dslp (k a)) i b) ].
  split; intros [a [H1 H2]]; exists a; split.
  - exact (proj2 (aslp_to_dslp_rel l i a) H1).
  - exact (proj2 (aslp_to_dslp_rel (k a) i b) H2).
  - exact (proj1 (aslp_to_dslp_rel l i a) H1).
  - exact (proj1 (aslp_to_dslp_rel (k a) i b) H2).
Qed.

Lemma dslp_to_aslp_ret {A} (x : A) :
  @eq1 ASLP Eq1_ASLP A (dslp_to_aslp (@ret DSLP Monad_DSLP A x)) (@ret ASLP Monad_ASLP A x).
Proof.
  apply (aslpRel_faithful (dslp_to_aslp (@ret DSLP Monad_DSLP A x))
           (@ret ASLP Monad_ASLP A x)).
  intros i a.
  etransitivity; [ exact (dslp_to_aslp_rel (@ret DSLP Monad_DSLP A x) i a) |].
  etransitivity; [ exact (dslpRel_retDSLP x i a) |].
  symmetry.
  exact (@rel_pure ASLPArr Arrow_ASLPArr RelArrow_ASLPArr unit A (fun _ => x) i a).
Qed.

Lemma dslp_to_aslp_bind {A B} (n : DSLP A) (k : A -> DSLP B) :
  @eq1 ASLP Eq1_ASLP B (dslp_to_aslp (@bind DSLP Monad_DSLP A B n k))
    (@bind ASLP Monad_ASLP A B (dslp_to_aslp n) (fun a => dslp_to_aslp (k a))).
Proof.
  apply (aslpRel_faithful (dslp_to_aslp (@bind DSLP Monad_DSLP A B n k))
           (@bind ASLP Monad_ASLP A B (dslp_to_aslp n) (fun a => dslp_to_aslp (k a)))).
  intros i b.
  etransitivity; [ exact (dslp_to_aslp_rel (@bind DSLP Monad_DSLP A B n k) i b) |].
  etransitivity; [ exact (dslpRel_bindDSLP n k i b) |].
  etransitivity;
    [| symmetry;
       exact (@rel_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr RelArrow_ASLPArr
                RelArrowApply_ASLPArr unit A B (dslp_to_aslp n)
                (fun a => dslp_to_aslp (k a)) i b) ].
  split; intros [a [H1 H2]]; exists a; split.
  - exact (proj2 (dslp_to_aslp_rel n i a) H1).
  - exact (proj2 (dslp_to_aslp_rel (k a) i b) H2).
  - exact (proj1 (dslp_to_aslp_rel n i a) H1).
  - exact (proj1 (dslp_to_aslp_rel (k a) i b) H2).
Qed.
