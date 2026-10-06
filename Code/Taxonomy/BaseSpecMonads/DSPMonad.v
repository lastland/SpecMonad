(** * The arrow-derived DSP specification monads.
    The earlier well-formed-carrier implementation remains in OldMonads.
    The pointwise reading order and recovered-relation order differ; only
    the latter supplies the OrderedMonad instances below. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad ArrowMonad.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPure.
From Incorrectness.Taxonomy.BaseSpecMonads Require Export DSPArrowCore DSPArrowRel.

Definition DSP (A : Type) : Type := DSPArr unit A.
#[global] Instance Monad_DSP : Monad DSP := Monad_Arrow DSPArr unit.
#[global] Instance Eq1_DSP : Eq1 DSP := @Eq1_Arrow DSPArr ArrowEq_DSPArr unit.
Definition Eq1Equivalence_DSP : @Eq1Equivalence DSP _ Eq1_DSP :=
  @Eq1Equivalence_Arrow DSPArr _ _ ArrowEq_DSPArr unit.
Definition MonadLawsE_DSP : @MonadLawsE DSP Eq1_DSP Monad_DSP :=
  @MonadLawsE_Arrow DSPArr _ _ ArrowEq_DSPArr _ _ unit.

(** Explicit transformer dictionaries avoid recursive instance search. *)
Section Stacks.
  Definition DSPStArr (S : Type) := stateArrT S DSPArr.
  Definition ArrowEq_DSPStArr (S : Type) : ArrowEq (DSPStArr S) :=
    @ArrowEq_stateArrT S DSPArr ArrowEq_DSPArr.
  Definition ArrowLaws_DSPStArr (S : Type) : ArrowLaws (DSPStArr S) :=
    @ArrowLaws_stateArrT S DSPArr Arrow_DSPArr ArrowEq_DSPArr ArrowLaws_DSPArr.
  Definition ArrowApply_DSPStArr (S : Type) : ArrowApply (DSPStArr S) :=
    @ArrowApply_stateArrT S DSPArr Arrow_DSPArr ArrowApply_DSPArr.
  Definition ArrowApplyLaws_DSPStArr (S : Type) : ArrowApplyLaws (DSPStArr S) :=
    @ArrowApplyLaws_stateArrT S DSPArr Arrow_DSPArr ArrowApply_DSPArr
      ArrowEq_DSPArr ArrowLaws_DSPArr ArrowApplyLaws_DSPArr.
  Definition optDSP := optionArrT DSPArr.
  Definition Arrow_optDSP : Arrow optDSP :=
    @Arrow_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr.
  Definition ArrowEq_optDSP : ArrowEq optDSP :=
    @ArrowEq_optionArrT DSPArr ArrowEq_DSPArr.
  Definition ArrowLaws_optDSP : ArrowLaws optDSP :=
    @ArrowLaws_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr
      ArrowEq_DSPArr ArrowLaws_DSPArr ArrowChoiceLaws_DSPArr.
  Definition ArrowApply_optDSP : ArrowApply optDSP :=
    @ArrowApply_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr ArrowApply_DSPArr.
  Definition ArrowApplyLaws_optDSP : ArrowApplyLaws optDSP :=
    @ArrowApplyLaws_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr
      ArrowApply_DSPArr ArrowEq_DSPArr ArrowLaws_DSPArr ArrowChoiceLaws_DSPArr
      ArrowApplyLaws_DSPArr.
  Definition DSPStExcArr (S : Type) := stateArrT S optDSP.
  Definition ArrowEq_DSPStExcArr (S : Type) : ArrowEq (DSPStExcArr S) :=
    @ArrowEq_stateArrT S optDSP ArrowEq_optDSP.
  Definition ArrowLaws_DSPStExcArr (S : Type) : ArrowLaws (DSPStExcArr S) :=
    @ArrowLaws_stateArrT S optDSP Arrow_optDSP ArrowEq_optDSP ArrowLaws_optDSP.
  Definition ArrowApply_DSPStExcArr (S : Type) : ArrowApply (DSPStExcArr S) :=
    @ArrowApply_stateArrT S optDSP Arrow_optDSP ArrowApply_optDSP.
  Definition ArrowApplyLaws_DSPStExcArr (S : Type) : ArrowApplyLaws (DSPStExcArr S) :=
    @ArrowApplyLaws_stateArrT S optDSP Arrow_optDSP ArrowApply_optDSP
      ArrowEq_optDSP ArrowLaws_optDSP ArrowApplyLaws_optDSP.
End Stacks.

Definition DSPSt (S A : Type) : Type := DSPStArr S unit A.
Definition DSPStExc (S A : Type) : Type := DSPStExcArr S unit A.
#[global] Instance Monad_DSPSt S : Monad (DSPSt S) := Monad_Arrow _ unit.
#[global] Instance Monad_DSPStExc S : Monad (DSPStExc S) := Monad_Arrow _ unit.
#[global] Instance Eq1_DSPSt S : Eq1 (DSPSt S) :=
  @Eq1_Arrow (DSPStArr S) (ArrowEq_DSPStArr S) unit.
#[global] Instance Eq1_DSPStExc S : Eq1 (DSPStExc S) :=
  @Eq1_Arrow (DSPStExcArr S) (ArrowEq_DSPStExcArr S) unit.
Definition MonadLawsE_DSPSt S : @MonadLawsE (DSPSt S) (Eq1_DSPSt S) (Monad_DSPSt S) :=
  @MonadLawsE_Arrow (DSPStArr S) _ (ArrowApply_DSPStArr S) (ArrowEq_DSPStArr S)
    (ArrowLaws_DSPStArr S) (ArrowApplyLaws_DSPStArr S) unit.
Definition MonadLawsE_DSPStExc S : @MonadLawsE (DSPStExc S) (Eq1_DSPStExc S) (Monad_DSPStExc S) :=
  @MonadLawsE_Arrow (DSPStExcArr S) _ (ArrowApply_DSPStExcArr S)
    (ArrowEq_DSPStExcArr S) (ArrowLaws_DSPStExcArr S) (ArrowApplyLaws_DSPStExcArr S) unit.

#[global] Instance RelDenote_DSP : @RelDenote DSPArr _ _ _ (@dspRel).
Proof.
  constructor.
  - intros X Y h x y. exact (dspRel_pure h x y).
  - intros X Y Z f g x z. exact (dspRel_comp f g x z).
  - intros X Y C f [x c] [y c']. exact (dspRel_first f (x, c) (y, c')).
  - intros X Y C f x y. exact (dspRel_left f x y).
  - intros X Y p y. exact (dspRel_app p y).
Qed.

Definition ordDSP {A} (m n : DSP A) : Prop := forall P b, getDSP m P b -> getDSP n P b.
Definition ordDSPSt {S A} (m n : DSPSt S A) : Prop := forall P b, getDSP m P b -> getDSP n P b.
Definition ordDSPStExc {S A} (m n : DSPStExc S A) : Prop := forall P b, getDSP m P b -> getDSP n P b.
Definition ordDSPRel {A} (m n : DSP A) : Prop := forall a b, dspRel m a b -> dspRel n a b.
Definition ordDSPStRel {S A} (m n : DSPSt S A) : Prop := forall a b, dspRel m a b -> dspRel n a b.
Definition ordDSPStExcRel {S A} (m n : DSPStExc S A) : Prop := forall a b, dspRel m a b -> dspRel n a b.

#[global] Instance OrderedMonad_DSP : OrderedMonad DSP (@ordDSPRel).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (dspRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk a b H.
    destruct (proj1 (rel_bind (arr := DSPArr) (rel := @dspRel) m1 k1 a b) H) as [x [H1 H2]].
    apply (proj2 (rel_bind (arr := DSPArr) (rel := @dspRel) m2 k2 a b)).
    exists x. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.
#[global] Instance OrderedMonad_DSPSt S : OrderedMonad (DSPSt S) (@ordDSPStRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (dspRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (relS_bind (arr := DSPArr) (rel := @dspRel) S m1 k1 i s b) H) as [x [s' [H1 H2]]].
    apply (proj2 (relS_bind (arr := DSPArr) (rel := @dspRel) S m2 k2 i s b)).
    exists x, s'. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.
#[global] Instance OrderedMonad_DSPStExc S : OrderedMonad (DSPStExc S) (@ordDSPStExcRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (dspRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (relE_bind (arr := DSPArr) (rel := @dspRel) S m1 k1 i s b) H) as [o1 [H1 H2]].
    apply (proj2 (relE_bind (arr := DSPArr) (rel := @dspRel) S m2 k2 i s b)).
    exists o1. split; [ exact (Hm _ _ H1) |].
    destruct o1 as [[x s']|]; [ exact (Hk x _ _ H2) | exact H2 ].
Qed.

Definition dspOfRelArr {X Y} (R : SPureArr X Y) : DSPArr X Y :=
  exist _ (dspOf R) (dsp_healthy_hom _ (ex_intro _ R (fun P y => iff_refl _))).
Lemma dspRel_ofRelArr {X Y} (R : SPureArr X Y) x y : dspRel (dspOfRelArr R) x y <-> R x y.
Proof. exact (dspRel_of R (dspOfRelArr R) (fun P y => iff_refl _) x y). Qed.
Lemma getDSP_cong {X Y} (w : DSPArr X Y) (P Q : X -> Prop) y :
  (forall x, P x <-> Q x) -> (getDSP w P y <-> getDSP w Q y).
Proof.
  intro H. rewrite (dspRel_spec w P y), (dspRel_spec w Q y).
  unfold dspOf, aspOf, dslpOf. split; intros [[x [Hx Hr]] Hall]; split.
  - exists x. split; [ apply H; exact Hx | exact Hr ].
  - intros x' Hr'. apply H. exact (Hall x' Hr').
  - exists x. split; [ apply H; exact Hx | exact Hr ].
  - intros x' Hr'. apply H. exact (Hall x' Hr').
Qed.
Definition dspOfPred {A} (Q : A -> Prop) : DSP A := dspOfRelArr (fun (_ : unit) a => Q a).
Definition getDSPPure {A} (w : DSP A) (p : Prop) (a : A) : Prop := getDSP w (fun _ => p) a.
Lemma getDSPPure_of {A} (Q : A -> Prop) p a :
  getDSPPure (dspOfPred Q) p a <-> ((p /\ Q a) /\ (Q a -> p)).
Proof.
  unfold getDSPPure, dspOfPred, dspOfRelArr, getDSP. cbn [proj1_sig].
  unfold dspOf, aspOf, dslpOf. split.
  - intros [[[] [Hp Hq]] Hall]. split; [ split; assumption | intro Hq'; exact (Hall tt Hq') ].
  - intros [[Hp Hq] Hall]. split; [ exists tt; split; assumption | intros [] Hq'; exact (Hall Hq') ].
Qed.
Definition dspOfRelSt {S A} (R : S -> A * S -> Prop) : DSPSt S A :=
  dspOfRelArr (fun (p : unit * S) r => R (snd p) r).
Definition getDSPSt {S A} (w : DSPSt S A) (pre : S -> Prop) (r : A * S) : Prop :=
  getDSP w (fun p => pre (snd p)) r.
Lemma getDSPSt_rel {S A} (w : DSPSt S A) pre r :
  getDSPSt w pre r <-> (exists s, pre s /\ dspRel w (tt, s) r) /\ (forall s, dspRel w (tt, s) r -> pre s).
Proof.
  unfold getDSPSt. rewrite dspRel_spec. unfold dspOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] Hall].
    split; [ exists s; split; assumption | intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] Hall].
    split; [ exists (tt, s); split; assumption | intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.
Lemma dspRelSt_of {S A} (R : S -> A * S -> Prop) s r : dspRel (dspOfRelSt R) (tt, s) r <-> R s r.
Proof. exact (dspRel_ofRelArr (fun (p : unit * S) r => R (snd p) r) (tt, s) r). Qed.
Lemma getDSPSt_of {S A} (R : S -> A * S -> Prop) pre r :
  getDSPSt (dspOfRelSt R) pre r <-> (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s).
Proof. rewrite getDSPSt_rel. setoid_rewrite dspRelSt_of. reflexivity. Qed.
Lemma ordDSPSt_get {S A} (m n : DSPSt S A) :
  ordDSPSt m n <-> (forall pre r, getDSPSt m pre r -> getDSPSt n pre r).
Proof.
  split.
  - intros H pre r. apply H.
  - intros H P r HP.
    refine (proj1 (getDSP_cong n (fun p => P (tt, snd p)) P r _) _);
      [ intros [[] s]; reflexivity |].
    apply (H (fun s => P (tt, s)) r).
    refine (proj1 (getDSP_cong m P (fun p => P (tt, snd p)) r _) HP).
    intros [[] s]; reflexivity.
Qed.
Lemma dspRelSt_bind_of {S A B} (R : S -> A * S -> Prop) (K : A -> S -> B * S -> Prop) s r :
  dspRel (bind (dspOfRelSt R) (fun a => dspOfRelSt (K a))) (tt, s) r <-> exists a s', R s (a, s') /\ K a s' r.
Proof.
  etransitivity;
    [ exact (relS_bind (arr := DSPArr) (rel := @dspRel) S
               (dspOfRelSt R) (fun a => dspOfRelSt (K a)) tt s r) |].
  setoid_rewrite dspRelSt_of. reflexivity.
Qed.
Definition dspOfRelStExc {S A} (R : S -> option (A * S) -> Prop) : DSPStExc S A :=
  dspOfRelArr (fun (p : unit * S) r => R (snd p) r).
Definition getDSPStExc {S A} (w : DSPStExc S A) (pre : S -> Prop) (r : option (A * S)) : Prop :=
  getDSP w (fun p => pre (snd p)) r.
Lemma getDSPStExc_of {S A} (R : S -> option (A * S) -> Prop) pre r :
  getDSPStExc (dspOfRelStExc R) pre r <-> (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s).
Proof.
  unfold getDSPStExc, dspOfRelStExc, dspOfRelArr, getDSP. cbn [proj1_sig].
  unfold dspOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] Hall].
    split; [ exists s; split; assumption | intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] Hall].
    split; [ exists (tt, s); split; assumption | intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.

(** Relation inclusion and pointwise reading order are not interchangeable. *)
Example dsp_order_diverges : exists m n : DSPSt bool unit, ordDSPStRel m n /\ ~ ordDSPSt m n.
Proof.
  exists (dspOfRelSt (fun s r => r = (tt, s))),
         (dspOfRelSt (fun (_ : bool) (_ : unit * bool) => True)).
  split.
  - intros [[] s] r _. apply dspRelSt_of. exact I.
  - intro H0.
    pose proof (proj1 (ordDSPSt_get _ _) H0 (fun s => s = true) (tt, true)) as H.
    clear H0. rewrite !getDSPSt_of in H. destruct H as [_ Hall].
    + split; [ exists true; split; reflexivity |].
      intros s Hs. injection Hs as Hs'. symmetry. exact Hs'.
    + discriminate (Hall false I).
Qed.
Definition dspR0 (s : bool) (r : unit * bool) : Prop := s = false /\ r = (tt, false).
Definition dspR1 (s : bool) (r : unit * bool) : Prop := r = (tt, s).
Definition dspK (_ : unit) (_ : bool) (r : unit * bool) : Prop := r = (tt, false).
Lemma dsp_R0_le_R1 : ordDSPSt (dspOfRelSt dspR0) (dspOfRelSt dspR1).
Proof.
  apply (proj2 (ordDSPSt_get _ _)). intros pre r H0.
  pose proof (proj1 (getDSPSt_of _ _ _) H0) as H. clear H0.
  apply (proj2 (getDSPSt_of _ _ _)). unfold dspR0, dspR1 in *.
  destruct H as [[s [Hp [Hs Hr]]] _]. subst s r. split.
  - exists false. split; [ exact Hp | reflexivity ].
  - intros t Ht. injection Ht as <-. exact Hp.
Qed.
Lemma dsp_bind_R0_R1 :
  ~ ordDSPSt (bind (dspOfRelSt dspR0) (fun a => dspOfRelSt (dspK a)))
             (bind (dspOfRelSt dspR1) (fun a => dspOfRelSt (dspK a))).
Proof.
  intro H0.
  pose proof (proj1 (ordDSPSt_get _ _) H0 (fun s => s = false) (tt, false)) as H.
  clear H0. rewrite !getDSPSt_rel in H. setoid_rewrite dspRelSt_bind_of in H.
  unfold dspR0, dspR1, dspK in H. lapply H.
  - intros [_ Hall]. assert (E : true = false).
    { apply Hall. exists tt, true. split; reflexivity. }
    discriminate E.
  - split.
    + exists false. split; [ reflexivity |]. exists tt, false.
      split; [ split; reflexivity | reflexivity ].
    + intros s [a [s' [[Hs _] _]]]. exact Hs.
Qed.
Theorem not_OrderedMonad_DSPSt :
  ~ @OrderedMonad (DSPSt bool) (Monad_DSPSt bool) (Eq1_DSPSt bool) (@ordDSPSt bool).
Proof.
  intros [_ _ Hbind]. apply dsp_bind_R0_R1.
  apply (Hbind unit unit _ _ dsp_R0_le_R1). intros a P b Hb. exact Hb.
Qed.
