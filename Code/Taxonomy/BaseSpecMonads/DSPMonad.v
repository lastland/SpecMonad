(** * The arrow-derived DSP specification monads.
    The earlier well-formed-carrier implementation remains in OldMonads.
    The pointwise reading order and recovered-relation order differ; only
    the latter supplies the OrderedMonad instances below. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad ArrowMonad RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPostArr.
From Incorrectness.Taxonomy.Arrows Require Export SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPMonad.

Definition DSP (A : Type) : Type := DSPArr unit A.
#[global] Instance Monad_DSP : Monad DSP := Monad_Arrow DSPArr unit.
#[global] Instance Eq1_DSP : Eq1 DSP := @Eq1_Arrow DSPArr ArrowEq_DSPArr unit.
Definition Eq1Equivalence_DSP : @Eq1Equivalence DSP _ Eq1_DSP :=
  @Eq1Equivalence_Arrow DSPArr _ _ ArrowEq_DSPArr unit.
Definition MonadLawsE_DSP : @MonadLawsE DSP Eq1_DSP Monad_DSP :=
  @MonadLawsE_Arrow DSPArr _ _ ArrowEq_DSPArr _ _ unit.

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
    destruct (proj1 (@rel_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
      RelArrow_DSPArr RelArrowApply_DSPArr unit A B m1 k1 a b) H) as [x [H1 H2]].
    apply (proj2 (@rel_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
      RelArrow_DSPArr RelArrowApply_DSPArr unit A B m2 k2 a b)).
    exists x. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.
#[global] Instance OrderedMonad_DSPSt S : OrderedMonad (DSPSt S) (@ordDSPStRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (dspRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (@relS_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
      RelArrow_DSPArr RelArrowApply_DSPArr S unit A B m1 k1 i s b) H) as [x [s' [H1 H2]]].
    apply (proj2 (@relS_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
      RelArrow_DSPArr RelArrowApply_DSPArr S unit A B m2 k2 i s b)).
    exists x, s'. split; [ exact (Hm _ _ H1) | exact (Hk x _ _ H2) ].
Qed.
#[global] Instance OrderedMonad_DSPStExc S : OrderedMonad (DSPStExc S) (@ordDSPStExcRel S).
Proof.
  constructor.
  - intro A. constructor;
      [ intros m a b H; exact H | intros m n o H1 H2 a b H; exact (H2 a b (H1 a b H)) ].
  - intros A m n H a b. exact (proj1 (dspRel_faithful_conv m n H a b)).
  - intros A B m1 m2 Hm k1 k2 Hk [i s] b H.
    destruct (proj1 (@relE_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
      RelArrow_DSPArr RelArrowApply_DSPArr ArrowChoice_DSPArr RelArrowChoice_DSPArr
      S unit A B m1 k1 i s b) H) as [o1 [H1 H2]].
    apply (proj2 (@relE_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
      RelArrow_DSPArr RelArrowApply_DSPArr ArrowChoice_DSPArr RelArrowChoice_DSPArr
      S unit A B m2 k2 i s b)).
    exists o1. split; [ exact (Hm _ _ H1) |].
    destruct o1 as [[x s']|]; [ exact (Hk x _ _ H2) | exact H2 ].
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
    [ exact (@relS_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr
               RelArrow_DSPArr RelArrowApply_DSPArr S unit A B
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

(** ** Without state, DSP is ASP

    At input [unit] a precondition is a single proposition, and the DSLP
    conjunct of a DSP reading follows from the ASP one ([dspOf_unit]).  So
    the two healthiness conditions cut the same transformers out of
    [SPArrT unit A] ([asp_dsp_unit_hom], [dsp_asp_unit_hom]), and the
    identity on transformers is an isomorphism between the monads [DSP] and
    [ASP]: [dsp_to_asp] and [asp_to_dsp] are mutually inverse, preserve
    [ret] and [bind], and carry the pointwise orders to each other.

    This is the collapse that [OldMonads/DSPMonad.v] builds in by defining
    its pure DSP monad through ASP's.  Here the two monads are given
    independently, each by its own arrow, so preservation of [ret] and
    [bind] is a theorem.  [dspOf_unit], [asp_dsp_unit_hom] and [asp_to_dsp]
    are constructive; the converse inclusion of carriers, and so everything
    stated with [dsp_to_asp], is classical. *)

Lemma dspOf_unit {A} (R : SPureArr unit A) (P : unit -> Prop) (a : A) :
  dspOf R P a <-> aspOf R P a.
Proof.
  unfold dspOf, aspOf, dslpOf, asp, dslp. split.
  - intros [H _]. exact H.
  - intros [[] [Hp Hr]]. split.
    + exists tt. split; assumption.
    + intros [] _. exact Hp.
Qed.

Lemma asp_dsp_unit_hom {A} (w : SPArrT unit A) :
  sp_monotone w /\ sp_strict w /\ sp_disjunctive w ->
  sp_monotone w /\ sp_strict w /\ sp_conjunctive w.
Proof.
  intro H. apply dsp_healthy_hom.
  exists (fun x y => w (fun z => z = x) y). intros P y.
  etransitivity; [ exact (asp_hom_join w H P y) |].
  symmetry. exact (dspOf_unit (fun x y => w (fun z => z = x) y) P y).
Qed.

Lemma dsp_asp_unit_hom {A} (w : SPArrT unit A) :
  sp_monotone w /\ sp_strict w /\ sp_conjunctive w ->
  sp_monotone w /\ sp_strict w /\ sp_disjunctive w.
Proof.
  intro H. destruct (dsp_hom_healthy w H) as [R HR].
  apply asp_join_hom. intros P b.
  etransitivity; [ exact (HR P b) |].
  etransitivity; [ exact (dspOf_unit R P b) |].
  etransitivity; [ exact (aspOf_join R P b) |].
  split; intros [x [Hp Hx]]; exists x; (split; [ exact Hp |]).
  - exact (proj2 (HR _ b) (proj2 (dspOf_unit R _ b) Hx)).
  - exact (proj1 (dspOf_unit R _ b) (proj1 (HR _ b) Hx)).
Qed.

Definition dsp_to_asp {A} (d : DSP A) : ASP A :=
  exist _ (getDSP d) (dsp_asp_unit_hom _ (proj2_sig d)).

Definition asp_to_dsp {A} (m : ASP A) : DSP A :=
  exist _ (getASPArr m) (asp_dsp_unit_hom _ (proj2_sig m)).

Lemma get_dsp_to_asp {A} (d : DSP A) P a :
  getASPArr (dsp_to_asp d) P a <-> getDSP d P a.
Proof. reflexivity. Qed.

Lemma get_asp_to_dsp {A} (m : ASP A) P a :
  getDSP (asp_to_dsp m) P a <-> getASPArr m P a.
Proof. reflexivity. Qed.

Lemma asp_to_dsp_to_asp {A} (m : ASP A) :
  @eq1 ASP Eq1_ASP A (dsp_to_asp (asp_to_dsp m)) m.
Proof. intros P a. reflexivity. Qed.

Lemma dsp_to_asp_to_dsp {A} (d : DSP A) :
  @eq1 DSP Eq1_DSP A (asp_to_dsp (dsp_to_asp d)) d.
Proof. intros P a. reflexivity. Qed.

Lemma ordDSP_dsp_to_asp {A} (d d' : DSP A) :
  ordDSP d d' <-> ordASP (dsp_to_asp d) (dsp_to_asp d').
Proof. split; intro H; exact H. Qed.

Lemma ordASP_asp_to_dsp {A} (m m' : ASP A) :
  ordASP m m' <-> ordDSP (asp_to_dsp m) (asp_to_dsp m').
Proof. split; intro H; exact H. Qed.

(** The two elements denote one relation. *)
Lemma dsp_to_asp_rel {A} (d : DSP A) i a :
  aspRel (dsp_to_asp d) i a <-> dspRel d i a.
Proof.
  destruct i. destruct (proj2_sig d) as [Hm [Hs _]].
  change (getDSP d (fun x => x = tt) a
          <-> getDSP d (fun _ => True) a /\ ~ getDSP d (fun z => z <> tt) a).
  split.
  - intro H. split.
    + exact (Hm _ _ (fun _ _ => I) a H).
    + intro H2. apply (Hs a). refine (Hm _ _ _ a H2). intros [] Hn. exact (Hn eq_refl).
  - intros [H _]. refine (Hm _ _ _ a H). intros [] _. reflexivity.
Qed.

Lemma asp_to_dsp_rel {A} (m : ASP A) i a :
  dspRel (asp_to_dsp m) i a <-> aspRel m i a.
Proof. exact (iff_sym (dsp_to_asp_rel (asp_to_dsp m) i a)). Qed.

Lemma dsp_to_asp_ret {A} (x : A) :
  @eq1 ASP Eq1_ASP A (dsp_to_asp (@ret DSP Monad_DSP A x)) (@ret ASP Monad_ASP A x).
Proof.
  apply (proj2 (aspRel_eq (dsp_to_asp (@ret DSP Monad_DSP A x)) (@ret ASP Monad_ASP A x))).
  intros i a.
  etransitivity; [ exact (dsp_to_asp_rel (@ret DSP Monad_DSP A x) i a) |].
  etransitivity;
    [ exact (@rel_pure DSPArr Arrow_DSPArr RelArrow_DSPArr unit A (fun _ => x) i a) |].
  symmetry. exact (aspRel_retASP x i a).
Qed.

Lemma dsp_to_asp_bind {A B} (d : DSP A) (k : A -> DSP B) :
  @eq1 ASP Eq1_ASP B (dsp_to_asp (@bind DSP Monad_DSP A B d k))
    (@bind ASP Monad_ASP A B (dsp_to_asp d) (fun a => dsp_to_asp (k a))).
Proof.
  apply (proj2 (aspRel_eq (dsp_to_asp (@bind DSP Monad_DSP A B d k))
                  (@bind ASP Monad_ASP A B (dsp_to_asp d) (fun a => dsp_to_asp (k a))))).
  intros i b.
  etransitivity; [ exact (dsp_to_asp_rel (@bind DSP Monad_DSP A B d k) i b) |].
  etransitivity;
    [ exact (@rel_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr RelArrow_DSPArr
               RelArrowApply_DSPArr unit A B d k i b) |].
  etransitivity;
    [| symmetry;
       exact (aspRel_bindASP (dsp_to_asp d) (fun a => dsp_to_asp (k a)) i b) ].
  split; intros [a [H1 H2]]; exists a; split.
  - exact (proj2 (dsp_to_asp_rel d i a) H1).
  - exact (proj2 (dsp_to_asp_rel (k a) i b) H2).
  - exact (proj1 (dsp_to_asp_rel d i a) H1).
  - exact (proj1 (dsp_to_asp_rel (k a) i b) H2).
Qed.

Lemma asp_to_dsp_ret {A} (x : A) :
  @eq1 DSP Eq1_DSP A (asp_to_dsp (@ret ASP Monad_ASP A x)) (@ret DSP Monad_DSP A x).
Proof.
  apply (dspRel_faithful (asp_to_dsp (@ret ASP Monad_ASP A x)) (@ret DSP Monad_DSP A x)).
  intros i a.
  etransitivity; [ exact (asp_to_dsp_rel (@ret ASP Monad_ASP A x) i a) |].
  etransitivity; [ exact (aspRel_retASP x i a) |].
  symmetry. exact (@rel_pure DSPArr Arrow_DSPArr RelArrow_DSPArr unit A (fun _ => x) i a).
Qed.

Lemma asp_to_dsp_bind {A B} (m : ASP A) (k : A -> ASP B) :
  @eq1 DSP Eq1_DSP B (asp_to_dsp (@bind ASP Monad_ASP A B m k))
    (@bind DSP Monad_DSP A B (asp_to_dsp m) (fun a => asp_to_dsp (k a))).
Proof.
  apply (dspRel_faithful (asp_to_dsp (@bind ASP Monad_ASP A B m k))
           (@bind DSP Monad_DSP A B (asp_to_dsp m) (fun a => asp_to_dsp (k a)))).
  intros i b.
  etransitivity; [ exact (asp_to_dsp_rel (@bind ASP Monad_ASP A B m k) i b) |].
  etransitivity; [ exact (aspRel_bindASP m k i b) |].
  etransitivity;
    [| symmetry;
       exact (@rel_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr RelArrow_DSPArr
                RelArrowApply_DSPArr unit A B (asp_to_dsp m)
                (fun a => asp_to_dsp (k a)) i b) ].
  split; intros [a [H1 H2]]; exists a; split.
  - exact (proj2 (asp_to_dsp_rel m i a) H1).
  - exact (proj2 (asp_to_dsp_rel (k a) i b) H2).
  - exact (proj1 (asp_to_dsp_rel m i a) H1).
  - exact (proj1 (asp_to_dsp_rel (k a) i b) H2).
Qed.
