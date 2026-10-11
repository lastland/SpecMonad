(** * The arrow-derived ASLP monads

    [ASLP], [ASLPSt S] and [ASLPStExc S] are the monads of the arrows
    [ASLPArr], [ASLPStArr S] and [ASLPStExcArr S] at input [unit], ordered
    pointwise on their readings.  Without state [ASLP] is a specification
    monad, because it is [DSLP] ([OrderedMonad_ASLP]).  [ASLPSt S] and
    [ASLPStExc S] are not ([not_OrderedMonad_ASLPSt],
    [not_OrderedMonad_ASLPStExc]), and on [ASLPSt bool] no bind at all is
    left-unital and monotone ([aslp_arbitrary_bind_impossible]).

    The last part of the file defines the stateless monad directly, with no
    arrow, as [ASLPSP], and shows that it is [ASLP]. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Arrow Require Import ArrowMonad RelArrowCoherence.
From Incorrectness.Relational Require Import Rel RelSPostArr.
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

(** ** No bind on [ASLPSt bool] is left-unital and monotone

    The dual of [dsp_arbitrary_bind_impossible] in [DSPMonad.v]: for an
    ARBITRARY [beta], the left-identity law for the monad's return and
    monotonicity in the first argument are jointly unsatisfiable.  The proof
    uses only that the result of [beta] is in the carrier, so monotone,
    terminating and disjunctive.

    The probes are the same evaluations of the precondition.  Here
    [aslpAtFinal] is below every return, so [beta aslpAtFinal aslpAt] is
    below every [aslpAt b].  By termination it accepts the full
    precondition, which is the join of the singletons, hence by
    disjunctivity some singleton [{b0}]; being below [aslpAt false] and
    [aslpAt true], that forces [b0] to be both. *)

#[program] Definition aslpAtFinal : ASLPSt bool bool :=
  fun (P : unit * bool -> Prop) (r : bool * bool) => P (tt, snd r).
Next Obligation.
  split; [| split ].
  - intros P Q H r. apply H.
  - intros r. exact I.
  - intros I _ p r. reflexivity.
Qed.

#[program] Definition aslpAt (b : bool) : ASLPSt bool unit :=
  fun (P : unit * bool -> Prop) (_ : unit * bool) => P (tt, b).
Next Obligation.
  split; [| split ].
  - intros P Q H r. apply H.
  - intros r. exact I.
  - intros I _ p r. reflexivity.
Qed.

Theorem aslp_arbitrary_bind_impossible :
  forall beta : ASLPSt bool bool -> (bool -> ASLPSt bool unit) -> ASLPSt bool unit,
    (forall (b : bool) (k : bool -> ASLPSt bool unit),
       @eq1 (ASLPSt bool) (Eq1_ASLPSt bool) unit (beta (ret b) k) (k b)) ->
    (forall (m0 m1 : ASLPSt bool bool) (k : bool -> ASLPSt bool unit),
       ordASLPSt m0 m1 -> ordASLPSt (beta m0 k) (beta m1 k)) ->
    False.
Proof.
  intros beta Hlid Hmono.
  assert (Hret : forall b : bool, ordASLPSt aslpAtFinal (ret b)).
  { intros b P r H. cbn. right. intros [[] s] Hr. subst r. exact H. }
  assert (Hbound : forall b b0 : bool,
            getASLP (beta aslpAtFinal aslpAt) (fun p => snd p = b0) (tt, false) ->
            b = b0).
  { intros b b0 H.
    exact (proj1 (Hlid b aslpAt _ _)
             (Hmono aslpAtFinal (ret b) aslpAt (Hret b) _ _ H)). }
  destruct (proj2_sig (beta aslpAtFinal aslpAt)) as [Hm [Ht Hd]].
  assert (Hex : exists b0 : bool,
            getASLP (beta aslpAtFinal aslpAt) (fun p => snd p = b0) (tt, false)).
  { apply (proj1 (Hd bool (inhabits true) (fun b p => snd p = b) (tt, false))).
    refine (Hm (fun _ => True) _ _ (tt, false) (Ht (tt, false))).
    intros p _. exists (snd p). reflexivity. }
  destruct Hex as [b0 Hb0].
  pose proof (Hbound false b0 Hb0) as Hf. pose proof (Hbound true b0 Hb0) as Htr.
  rewrite <- Hf in Htr. discriminate Htr.
Qed.

(** ** With exceptions

    The witnesses of [not_OrderedMonad_ASLPSt], the terminating outcome
    [(tt, s)] read as [Some (tt, s)]. *)

Lemma getASLPStExc_rel {S A} (w : ASLPStExc S A) pre r :
  getASLPStExc w pre r <-> (exists s, pre s /\ aslpRel w (tt, s) r) \/ (forall s, aslpRel w (tt, s) r -> pre s).
Proof.
  unfold getASLPStExc. rewrite aslpRel_spec. unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] | Hall];
      [ left; exists s; split; assumption | right; intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] | Hall];
      [ left; exists (tt, s); split; assumption | right; intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.
Lemma aslpRelStExc_of {S A} (R : S -> option (A * S) -> Prop) s r :
  aslpRel (aslpOfRelStExc R) (tt, s) r <-> R s r.
Proof. exact (aslpRel_ofRelArr (fun (p : unit * S) r => R (snd p) r) (tt, s) r). Qed.
Lemma ordASLPStExc_get {S A} (m n : ASLPStExc S A) :
  ordASLPStExc m n <-> (forall pre r, getASLPStExc m pre r -> getASLPStExc n pre r).
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
Lemma aslpRelStExc_bind_of {S A B} (R : S -> option (A * S) -> Prop)
    (K : A -> S -> option (B * S) -> Prop) s o :
  aslpRel (bind (aslpOfRelStExc R) (fun a => aslpOfRelStExc (K a))) (tt, s) o
  <-> exists o1, R s o1 /\ match o1 with Some (a, s') => K a s' o | None => o = None end.
Proof.
  etransitivity;
    [ exact (@relE_bind ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr RelArrow_ASLPArr
               RelArrowApply_ASLPArr ArrowChoice_ASLPArr RelArrowChoice_ASLPArr
               S unit A B (aslpOfRelStExc R) (fun a => aslpOfRelStExc (K a)) tt s o) |].
  split; intros [o1 [H1 H2]]; exists o1.
  - split; [ exact (proj1 (aslpRelStExc_of R s o1) H1) |].
    destruct o1 as [[a s']|]; [ exact (proj1 (aslpRelStExc_of (K a) s' o) H2) | exact H2 ].
  - split; [ exact (proj2 (aslpRelStExc_of R s o1) H1) |].
    destruct o1 as [[a s']|]; [ exact (proj2 (aslpRelStExc_of (K a) s' o) H2) | exact H2 ].
Qed.

Definition aslpR0E (s : bool) (r : option (unit * bool)) : Prop := s = false /\ r = Some (tt, false).
Definition aslpR1E (s : bool) (r : option (unit * bool)) : Prop := r = Some (tt, s).
Definition aslpKE (_ : unit) (_ : bool) (r : option (unit * bool)) : Prop := r = Some (tt, false).
Lemma aslp_R1E_le_R0E : ordASLPStExc (aslpOfRelStExc aslpR1E) (aslpOfRelStExc aslpR0E).
Proof.
  apply (proj2 (ordASLPStExc_get _ _)). intros pre r H0.
  pose proof (proj1 (getASLPStExc_of _ _ _) H0) as H. clear H0.
  apply (proj2 (getASLPStExc_of _ _ _)). unfold aslpR0E, aslpR1E in *.
  destruct H as [[s [Hp Hr]] | Hall].
  - subst r. destruct s.
    + right. intros t [_ Ht]. discriminate Ht.
    + left. exists false. split; [ exact Hp | split; reflexivity ].
  - right. intros t [Ht Hr]. subst t r. exact (Hall false eq_refl).
Qed.
Lemma aslp_bind_R1E_R0E :
  ~ ordASLPStExc (bind (aslpOfRelStExc aslpR1E) (fun a => aslpOfRelStExc (aslpKE a)))
                 (bind (aslpOfRelStExc aslpR0E) (fun a => aslpOfRelStExc (aslpKE a))).
Proof.
  intro H0.
  pose proof (proj1 (ordASLPStExc_get _ _) H0 (fun s => s = true) (Some (tt, false))) as H.
  clear H0. rewrite !getASLPStExc_rel in H. setoid_rewrite aslpRelStExc_bind_of in H.
  unfold aslpR0E, aslpR1E, aslpKE in H. lapply H.
  - intros [[s [Hs [o1 [[Hs0 _] _]]]] | Hall].
    + congruence.
    + assert (E : false = true).
      { apply Hall. exists (Some (tt, false)). split; [ split; reflexivity | reflexivity ]. }
      discriminate E.
  - left. exists true. split; [ reflexivity |]. exists (Some (tt, true)). split; reflexivity.
Qed.
Theorem not_OrderedMonad_ASLPStExc :
  ~ @OrderedMonad (ASLPStExc bool) (Monad_ASLPStExc bool) (Eq1_ASLPStExc bool) (@ordASLPStExc bool).
Proof.
  intros [_ _ Hbind]. apply aslp_bind_R1E_R0E.
  apply (Hbind unit unit _ _ aslp_R1E_le_R0E). intros a P b Hb. exact Hb.
Qed.

(** ** Without state, ASLP is DSLP

    The dual of the collapse in [DSPMonad.v].  At input [unit] the ASP
    disjunct of an ASLP reading implies the DSLP one ([aslpOf_unit]), so the
    two healthiness conditions cut the same transformers out of
    [SPArrT unit A] ([dslp_aslp_unit_hom], [aslp_dslp_unit_hom]), and the
    identity on transformers is an isomorphism between the monads [ASLP] and
    [DSLP]: [aslp_to_dslp] and [dslp_to_aslp] are mutually inverse, preserve
    [ret] and [bind], and carry the pointwise orders to each other.

    The two monads are given independently, each by its own arrow, so
    preservation of [ret] and [bind] is a theorem, and with it the ordered
    monad structure of [ASLP] ([OrderedMonad_ASLP]).  Only [aslpOf_unit] is
    constructive: an ASLP element preserves joins, and is read through its
    relation, classically. *)

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

(** So without state ASLP is a specification monad under its own order: the
    order and its laws are DSLP's, pulled back along [aslp_to_dslp]. *)

Lemma aslp_to_dslp_morphism :
  @MonadMorphism ASLP DSLP Monad_ASLP Monad_DSLP Eq1_ASLP Eq1_DSLP
    (fun A => @aslp_to_dslp A).
Proof.
  constructor.
  - intros A x y H P a. exact (H P a).
  - intros A a. exact (aslp_to_dslp_ret a).
  - intros A B x k. exact (aslp_to_dslp_bind x k).
Qed.

Theorem OrderedMonad_ASLP : @OrderedMonad ASLP Monad_ASLP Eq1_ASLP (@ordASLP).
Proof.
  exact (OrderedMonad_pullback (fun A => @aslp_to_dslp A) (@ordDSLP)
           aslp_to_dslp_morphism OrderedMonad_DSLP).
Qed.

(* ================================================================= *)
(** * The directly defined monad [ASLPSP]                             *)
(* ================================================================= *)

(** The dual of [DSPSP] in [DSPMonad.v].  Written down directly on
    [SPPure A = Prop -> A -> Prop], the ASLP carrier condition is
    terminating and disjunctive, and at a [Prop] precondition that is
    EQUIVALENT to the DSLP one, [MSingleton] ([term_disj_iff_msingleton]):
    termination alone already forces [MSingleton]
    ([terminating_to_msingleton]), and [MSingleton] gives both connectives
    back ([msingleton_to_meet], [msingleton_to_disjunctive]).

    So [ASLPSP] is [DSLPSP] under a different presentation of the same
    subset of [SPPure], and its monad structure is transported rather than
    rebuilt.

    [ASLPSP] and [ASLP] are the same monad: [aslpsp_to_aslp] and
    [aslp_to_aslpsp] are mutually inverse, preserve [ret] and [bind], and
    carry the orders to each other. *)

From Coq Require Import PropExtensionality.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.

Section PureASLPMonad.

  Definition TerminatingDisjunctive {A} (w : SPPure A) : Prop :=
    Terminating w /\ Disjunctive w.

  Definition ASLPSP (A : Type) : Type := { w : SPPure A | TerminatingDisjunctive w }.

  Definition getASLPSP {A} (w : ASLPSP A) : SPPure A := proj1_sig w.

  Theorem term_disj_iff_msingleton {A} (w : SPPure A) :
    TerminatingDisjunctive w <-> MSingleton w.
  Proof.
    split.
    - intros [HT _]. exact (terminating_to_msingleton w HT).
    - intro H. split;
        [ exact (proj1 (msingleton_to_meet w H))
        | exact (msingleton_to_disjunctive w H) ].
  Qed.

  Definition dslpsp_to_aslpsp {A} (w : DSLPSP A) : ASLPSP A :=
    exist _ (getDSLPSP w) (proj2 (term_disj_iff_msingleton (getDSLPSP w)) (proj2_sig w)).

  Definition aslpsp_to_dslpsp {A} (w : ASLPSP A) : DSLPSP A :=
    exist _ (getASLPSP w) (proj1 (term_disj_iff_msingleton (getASLPSP w)) (proj2_sig w)).

  Lemma getASLPSP_dslpsp_to_aslpsp {A} (w : DSLPSP A) p a :
    getASLPSP (dslpsp_to_aslpsp w) p a <-> getDSLPSP w p a.
  Proof. split; intro H; exact H. Qed.

  Lemma getDSLPSP_aslpsp_to_dslpsp {A} (w : ASLPSP A) p a :
    getDSLPSP (aslpsp_to_dslpsp w) p a <-> getASLPSP w p a.
  Proof. split; intro H; exact H. Qed.

  Definition retASLPSP {A} (v : A) : ASLPSP A := dslpsp_to_aslpsp (retDSLPSP v).

  Definition bindASLPSP {A B} (m : ASLPSP A) (k : A -> ASLPSP B) : ASLPSP B :=
    dslpsp_to_aslpsp (bindDSLPSP (aslpsp_to_dslpsp m) (fun a => aslpsp_to_dslpsp (k a))).

  #[global] Instance Monad_ASLPSP : Monad ASLPSP :=
    {| ret := fun _ => retASLPSP ;
      bind := fun _ _ => bindASLPSP |}.

  #[global] Instance Eq1_ASLPSP : Eq1 ASLPSP :=
    fun A m n => forall p a, getASLPSP m p a <-> getASLPSP n p a.

  #[global] Instance Eq1Equivalence_ASLPSP
    : @Eq1Equivalence ASLPSP _ Eq1_ASLPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a); specialize (H2 p a). tauto.
  Qed.

  #[global] Instance MonadLawsE_ASLPSP : @MonadLawsE ASLPSP Eq1_ASLPSP _.
  Proof.
    destruct (@MonadLawsE_DSLPSP) as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => aslpsp_to_dslpsp (f a)) x).
    - intros A x. exact (Lbrr A (aslpsp_to_dslpsp x)).
    - intros A B C x f g.
      exact (Lbb A B C (aslpsp_to_dslpsp x) (fun a => aslpsp_to_dslpsp (f a))
               (fun b => aslpsp_to_dslpsp (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (aslpsp_to_dslpsp x) (aslpsp_to_dslpsp y) Hxy
               (fun a => aslpsp_to_dslpsp (f a)) (fun a => aslpsp_to_dslpsp (g a)) Hfg).
  Qed.

  Definition ordASLPSP {A} (m1 m2 : ASLPSP A) : Prop :=
    forall p a, getASLPSP m1 p a -> getASLPSP m2 p a.
  Definition ordASLPSPAt {A} (pre : Prop) (m1 m2 : ASLPSP A) : Prop :=
    forall a, getASLPSP m1 pre a -> getASLPSP m2 pre a.

  Lemma ordASLPSP_refl A (m : ASLPSP A) : ordASLPSP m m.
  Proof. intros p a H. exact H. Qed.
  Lemma bindASLPSP_mono A B (m n : ASLPSP A) (f g : A -> ASLPSP B) :
    ordASLPSP m n -> (forall a, ordASLPSP (f a) (g a)) ->
    ordASLPSP (bindASLPSP m f) (bindASLPSP n g).
  Proof.
    intros Hmn Hfg p b Hb a. apply Hfg.
    apply (getMSP_mono (aslpsp_to_dslpsp (f a)) (getASLPSP m p a) (getASLPSP n p a) b).
    - exact (Hmn p a).
    - exact (Hb a).
  Qed.
End PureASLPMonad.

(* ================================================================= *)
(** ** [ASLPSP] is [ASLP]                                             *)
(* ================================================================= *)

(** Three identifications compose: [ASLPSP] is [DSLPSP] by construction,
    [DSLPSP] is [DSLP] ([DSLPMonad.v]), and [DSLP] is [ASLP] (above). *)

Lemma dslp_to_aslp_morphism :
  @MonadMorphism DSLP ASLP Monad_DSLP Monad_ASLP Eq1_DSLP Eq1_ASLP
    (fun A => @dslp_to_aslp A).
Proof.
  constructor.
  - intros A x y H P a. exact (H P a).
  - intros A a. exact (dslp_to_aslp_ret a).
  - intros A B x k. exact (dslp_to_aslp_bind x k).
Qed.

Lemma aslpsp_to_dslpsp_morphism :
  @MonadMorphism ASLPSP DSLPSP Monad_ASLPSP Monad_DSLPSP Eq1_ASLPSP Eq1_DSLPSP
    (fun A => @aslpsp_to_dslpsp A).
Proof.
  constructor.
  - intros A x y H p a. exact (H p a).
  - intros A a p b. reflexivity.
  - intros A B x k p b. reflexivity.
Qed.

Lemma dslpsp_to_aslpsp_morphism :
  @MonadMorphism DSLPSP ASLPSP Monad_DSLPSP Monad_ASLPSP Eq1_DSLPSP Eq1_ASLPSP
    (fun A => @dslpsp_to_aslpsp A).
Proof.
  constructor.
  - intros A x y H p a. exact (H p a).
  - intros A a p b. reflexivity.
  - intros A B x k p b. reflexivity.
Qed.

Definition aslpsp_to_aslp {A} (w : ASLPSP A) : ASLP A :=
  dslp_to_aslp (dslpsp_to_dslp (aslpsp_to_dslpsp w)).

Definition aslp_to_aslpsp {A} (l : ASLP A) : ASLPSP A :=
  dslpsp_to_aslpsp (dslp_to_dslpsp (aslp_to_dslp l)).

Lemma get_aslpsp_to_aslp {A} (w : ASLPSP A) P a :
  getASLP (aslpsp_to_aslp w) P a <-> getASLPSP w (P tt) a.
Proof. reflexivity. Qed.

Lemma get_aslp_to_aslpsp {A} (l : ASLP A) p a :
  getASLPSP (aslp_to_aslpsp l) p a <-> getASLPPure l p a.
Proof. reflexivity. Qed.

(** The two maps are mutually inverse. *)

Lemma aslpsp_to_aslp_to_aslpsp {A} (w : ASLPSP A) :
  @eq1 ASLPSP Eq1_ASLPSP A (aslp_to_aslpsp (aslpsp_to_aslp w)) w.
Proof. intros p a. reflexivity. Qed.

Lemma aslp_to_aslpsp_to_aslp {A} (l : ASLP A) :
  @eq1 ASLP Eq1_ASLP A (aslpsp_to_aslp (aslp_to_aslpsp l)) l.
Proof.
  intros P a. apply (getASLP_cong l (fun _ => P tt) P a). intros []. reflexivity.
Qed.

(** Both preserve [ret] and [bind]. *)

Theorem aslpsp_to_aslp_morphism :
  @MonadMorphism ASLPSP ASLP Monad_ASLPSP Monad_ASLP Eq1_ASLPSP Eq1_ASLP
    (fun A => @aslpsp_to_aslp A).
Proof.
  exact (@MonadMorphism_comp ASLPSP DSLP ASLP Monad_ASLPSP Monad_DSLP Monad_ASLP
           Eq1_ASLPSP Eq1_DSLP Eq1_ASLP Eq1Equivalence_ASLP _ _
           (@MonadMorphism_comp ASLPSP DSLPSP DSLP Monad_ASLPSP Monad_DSLPSP Monad_DSLP
              Eq1_ASLPSP Eq1_DSLPSP Eq1_DSLP Eq1Equivalence_DSLP _ _
              aslpsp_to_dslpsp_morphism dslpsp_to_dslp_morphism)
           dslp_to_aslp_morphism).
Qed.

Theorem aslp_to_aslpsp_morphism :
  @MonadMorphism ASLP ASLPSP Monad_ASLP Monad_ASLPSP Eq1_ASLP Eq1_ASLPSP
    (fun A => @aslp_to_aslpsp A).
Proof.
  exact (@MonadMorphism_comp ASLP DSLPSP ASLPSP Monad_ASLP Monad_DSLPSP Monad_ASLPSP
           Eq1_ASLP Eq1_DSLPSP Eq1_ASLPSP Eq1Equivalence_ASLPSP _ _
           (@MonadMorphism_comp ASLP DSLP DSLPSP Monad_ASLP Monad_DSLP Monad_DSLPSP
              Eq1_ASLP Eq1_DSLP Eq1_DSLPSP Eq1Equivalence_DSLPSP _ _
              aslp_to_dslp_morphism dslp_to_dslpsp_morphism)
           dslpsp_to_aslpsp_morphism).
Qed.

(** Both preserve and reflect the order. *)

Lemma ordASLPSP_aslpsp_to_aslp {A} (w w' : ASLPSP A) :
  ordASLPSP w w' <-> ordASLP (aslpsp_to_aslp w) (aslpsp_to_aslp w').
Proof.
  split.
  - intros H P a. exact (H (P tt) a).
  - intros H p a. exact (H (fun _ => p) a).
Qed.

Lemma ordASLP_aslp_to_aslpsp {A} (l l' : ASLP A) :
  ordASLP l l' <-> ordASLPSP (aslp_to_aslpsp l) (aslp_to_aslpsp l').
Proof.
  split.
  - intros H p a. exact (H (fun _ => p) a).
  - intros H P a HP.
    refine (proj1 (getASLP_cong l' (fun _ => P tt) P a _) _);
      [ intros []; reflexivity |].
    apply (H (P tt) a).
    refine (proj2 (getASLP_cong l (fun _ => P tt) P a _) HP).
    intros []. reflexivity.
Qed.

(** So [ASLPSP] is a specification monad: its order is [DSLPSP]'s. *)

Theorem OrderedMonad_ASLPSP :
  @OrderedMonad ASLPSP Monad_ASLPSP Eq1_ASLPSP (@ordASLPSP).
Proof.
  exact (@OrderedMonad_pullback ASLPSP DSLPSP Monad_ASLPSP Monad_DSLPSP
           Eq1_ASLPSP Eq1_DSLPSP Eq1Equivalence_DSLPSP
           (fun A => @aslpsp_to_dslpsp A) (@ordDSLPSP)
           aslpsp_to_dslpsp_morphism OrderedMonad_DSLPSP).
Qed.
