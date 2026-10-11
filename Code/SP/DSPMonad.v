(** * The arrow-derived DSP monads

    [DSP], [DSPSt S] and [DSPStExc S] are the monads of the arrows [DSPArr],
    [DSPStArr S] and [DSPStExcArr S] at input [unit], ordered pointwise on
    their readings.  Without state [DSP] is a specification monad, because
    it is [ASP] ([OrderedMonad_DSP]).  [DSPSt S] and [DSPStExc S] are not
    ([not_OrderedMonad_DSPSt], [not_OrderedMonad_DSPStExc]), and on
    [DSPSt bool] no bind at all is left-unital and monotone
    ([dsp_arbitrary_bind_impossible]).

    The last part of the file defines the stateless monad directly, with no
    arrow, as [DSPSP], and shows that it is [DSP]. *)
From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Arrow Require Import ArrowMonad RelArrowCoherence.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Export SPostArr DSPASLPArr.
From Incorrectness.SP Require Import ASPMonad.

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

(** ** No bind on [DSPSt bool] is left-unital and monotone

    [not_OrderedMonad_DSPSt] refutes the bind of the monad.  No replacement
    helps: for an ARBITRARY [beta], the left-identity law for the monad's
    return and monotonicity in the first argument are jointly
    unsatisfiable.  The proof uses only that the result of [beta] is in the
    carrier, so monotone, strict and conjunctive.

    Two probes, both plain evaluations of the precondition: [dspAtFinal]
    at the final state of the outcome, and [dspAt b] at the fixed state [b].  Every return is
    below [dspAtFinal], so by monotonicity and left identity every [dspAt b]
    is below [beta dspAtFinal dspAt].  That element therefore accepts each
    singleton precondition, hence by conjunctivity their meet, which is
    empty: this contradicts strictness. *)

#[program] Definition dspAtFinal : DSPSt bool bool :=
  fun (P : unit * bool -> Prop) (r : bool * bool) => P (tt, snd r).
Next Obligation.
  split; [| split ].
  - intros P Q H r. apply H.
  - intros r H. exact H.
  - intros I _ p r. reflexivity.
Qed.

#[program] Definition dspAt (b : bool) : DSPSt bool unit :=
  fun (P : unit * bool -> Prop) (_ : unit * bool) => P (tt, b).
Next Obligation.
  split; [| split ].
  - intros P Q H r. apply H.
  - intros r H. exact H.
  - intros I _ p r. reflexivity.
Qed.

Theorem dsp_arbitrary_bind_impossible :
  forall beta : DSPSt bool bool -> (bool -> DSPSt bool unit) -> DSPSt bool unit,
    (forall (b : bool) (k : bool -> DSPSt bool unit),
       @eq1 (DSPSt bool) (Eq1_DSPSt bool) unit (beta (ret b) k) (k b)) ->
    (forall (m0 m1 : DSPSt bool bool) (k : bool -> DSPSt bool unit),
       ordDSPSt m0 m1 -> ordDSPSt (beta m0 k) (beta m1 k)) ->
    False.
Proof.
  intros beta Hlid Hmono.
  assert (Hret : forall b : bool, ordDSPSt (ret b) dspAtFinal).
  { intros b P r H. cbn in H. destruct H as [[[[] s] [Hp Hr]] _].
    subst r. exact Hp. }
  assert (Hsing : forall b : bool,
            getDSP (beta dspAtFinal dspAt) (fun p => snd p = b) (tt, false)).
  { intro b. apply (Hmono (ret b) dspAtFinal dspAt (Hret b)).
    apply (proj2 (Hlid b dspAt _ _)). exact eq_refl. }
  destruct (proj2_sig (beta dspAtFinal dspAt)) as [Hm [Hs Hc]].
  apply (Hs (tt, false)).
  refine (Hm (fun p => forall b : bool, snd p = b) _ _ (tt, false) _).
  - intros p Hp. pose proof (Hp true) as Ht. rewrite (Hp false) in Ht. discriminate Ht.
  - exact (proj2 (Hc bool (inhabits true) (fun b p => snd p = b) (tt, false)) Hsing).
Qed.

(** ** With exceptions

    The witnesses of [not_OrderedMonad_DSPSt], the terminating outcome
    [(tt, s)] read as [Some (tt, s)]. *)

Lemma getDSPStExc_rel {S A} (w : DSPStExc S A) pre r :
  getDSPStExc w pre r <-> (exists s, pre s /\ dspRel w (tt, s) r) /\ (forall s, dspRel w (tt, s) r -> pre s).
Proof.
  unfold getDSPStExc. rewrite dspRel_spec. unfold dspOf, aspOf, dslpOf. split.
  - intros [[[[] s] [Hp Hr]] Hall].
    split; [ exists s; split; assumption | intros s' Hs'; exact (Hall (tt, s') Hs') ].
  - intros [[s [Hp Hr]] Hall].
    split; [ exists (tt, s); split; assumption | intros [[] s'] Hs'; exact (Hall s' Hs') ].
Qed.
Lemma dspRelStExc_of {S A} (R : S -> option (A * S) -> Prop) s r :
  dspRel (dspOfRelStExc R) (tt, s) r <-> R s r.
Proof. exact (dspRel_ofRelArr (fun (p : unit * S) r => R (snd p) r) (tt, s) r). Qed.
Lemma ordDSPStExc_get {S A} (m n : DSPStExc S A) :
  ordDSPStExc m n <-> (forall pre r, getDSPStExc m pre r -> getDSPStExc n pre r).
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
Lemma dspRelStExc_bind_of {S A B} (R : S -> option (A * S) -> Prop)
    (K : A -> S -> option (B * S) -> Prop) s o :
  dspRel (bind (dspOfRelStExc R) (fun a => dspOfRelStExc (K a))) (tt, s) o
  <-> exists o1, R s o1 /\ match o1 with Some (a, s') => K a s' o | None => o = None end.
Proof.
  etransitivity;
    [ exact (@relE_bind DSPArr Arrow_DSPArr ArrowApply_DSPArr RelArrow_DSPArr
               RelArrowApply_DSPArr ArrowChoice_DSPArr RelArrowChoice_DSPArr
               S unit A B (dspOfRelStExc R) (fun a => dspOfRelStExc (K a)) tt s o) |].
  split; intros [o1 [H1 H2]]; exists o1.
  - split; [ exact (proj1 (dspRelStExc_of R s o1) H1) |].
    destruct o1 as [[a s']|]; [ exact (proj1 (dspRelStExc_of (K a) s' o) H2) | exact H2 ].
  - split; [ exact (proj2 (dspRelStExc_of R s o1) H1) |].
    destruct o1 as [[a s']|]; [ exact (proj2 (dspRelStExc_of (K a) s' o) H2) | exact H2 ].
Qed.

Definition dspR0E (s : bool) (r : option (unit * bool)) : Prop := s = false /\ r = Some (tt, false).
Definition dspR1E (s : bool) (r : option (unit * bool)) : Prop := r = Some (tt, s).
Definition dspKE (_ : unit) (_ : bool) (r : option (unit * bool)) : Prop := r = Some (tt, false).
Lemma dsp_R0E_le_R1E : ordDSPStExc (dspOfRelStExc dspR0E) (dspOfRelStExc dspR1E).
Proof.
  apply (proj2 (ordDSPStExc_get _ _)). intros pre r H0.
  pose proof (proj1 (getDSPStExc_of _ _ _) H0) as H. clear H0.
  apply (proj2 (getDSPStExc_of _ _ _)). unfold dspR0E, dspR1E in *.
  destruct H as [[s [Hp [Hs Hr]]] _]. subst s r. split.
  - exists false. split; [ exact Hp | reflexivity ].
  - intros t Ht. injection Ht as <-. exact Hp.
Qed.
Lemma dsp_bind_R0E_R1E :
  ~ ordDSPStExc (bind (dspOfRelStExc dspR0E) (fun a => dspOfRelStExc (dspKE a)))
                (bind (dspOfRelStExc dspR1E) (fun a => dspOfRelStExc (dspKE a))).
Proof.
  intro H0.
  pose proof (proj1 (ordDSPStExc_get _ _) H0 (fun s => s = false) (Some (tt, false))) as H.
  clear H0. rewrite !getDSPStExc_rel in H. setoid_rewrite dspRelStExc_bind_of in H.
  unfold dspR0E, dspR1E, dspKE in H. lapply H.
  - intros [_ Hall]. assert (E : true = false).
    { apply Hall. exists (Some (tt, true)). split; reflexivity. }
    discriminate E.
  - split.
    + exists false. split; [ reflexivity |]. exists (Some (tt, false)).
      split; [ split; reflexivity | reflexivity ].
    + intros s [o1 [[Hs _] _]]. exact Hs.
Qed.
Theorem not_OrderedMonad_DSPStExc :
  ~ @OrderedMonad (DSPStExc bool) (Monad_DSPStExc bool) (Eq1_DSPStExc bool) (@ordDSPStExc bool).
Proof.
  intros [_ _ Hbind]. apply dsp_bind_R0E_R1E.
  apply (Hbind unit unit _ _ dsp_R0E_le_R1E). intros a P b Hb. exact Hb.
Qed.

(** ** Without state, DSP is ASP

    At input [unit] a precondition is a single proposition, and the DSLP
    conjunct of a DSP reading follows from the ASP one ([dspOf_unit]).  So
    the two healthiness conditions cut the same transformers out of
    [SPArrT unit A] ([asp_dsp_unit_hom], [dsp_asp_unit_hom]), and the
    identity on transformers is an isomorphism between the monads [DSP] and
    [ASP]: [dsp_to_asp] and [asp_to_dsp] are mutually inverse, preserve
    [ret] and [bind], and carry the pointwise orders to each other.

    The two monads are given independently, each by its own arrow, so
    preservation of [ret] and [bind] is a theorem, and with it the ordered
    monad structure of [DSP] ([OrderedMonad_DSP]).  [dspOf_unit], [asp_dsp_unit_hom] and [asp_to_dsp]
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

(** So without state DSP is a specification monad under its own order: the
    order and its laws are ASP's, pulled back along [dsp_to_asp]. *)

Lemma dsp_to_asp_morphism :
  @MonadMorphism DSP ASP Monad_DSP Monad_ASP Eq1_DSP Eq1_ASP (fun A => @dsp_to_asp A).
Proof.
  constructor.
  - intros A x y H P a. exact (H P a).
  - intros A a. exact (dsp_to_asp_ret a).
  - intros A B x k. exact (dsp_to_asp_bind x k).
Qed.

Theorem OrderedMonad_DSP : @OrderedMonad DSP Monad_DSP Eq1_DSP (@ordDSP).
Proof.
  exact (OrderedMonad_pullback (fun A => @dsp_to_asp A) (@ordASP)
           dsp_to_asp_morphism OrderedMonad_ASP).
Qed.

(* ================================================================= *)
(** * The directly defined monad [DSPSP]                              *)
(* ================================================================= *)

(** [DSP] above comes from the arrow [DSPArr] at input [unit].  Written
    down directly on [SPPure A = Prop -> A -> Prop], the DSP carrier
    condition is strict and conjunctive, and at a [Prop] precondition that
    is EQUIVALENT to the ASP one, [Singleton]
    ([strict_conj_iff_singleton]): strictness alone already forces
    [Singleton] ([strict_to_singleton]), and [Singleton] gives both
    connectives back ([singleton_to_join], [singleton_to_conjunctive]).

    So [DSPSP] is [ASPSP] under a different presentation of the same subset
    of [SPPure], and its monad structure is transported along that
    equivalence rather than rebuilt.  The reason DSP differs from ASP with
    state, a precondition that is a SET of states, is exactly what
    disappears when the state is dropped.

    [DSPSP] and [DSP] are the same monad: [dspsp_to_dsp] and [dsp_to_dspsp]
    are mutually inverse, preserve [ret] and [bind], and carry the orders to
    each other. *)

From Coq Require Import PropExtensionality.
From Incorrectness.SP Require Import RawSP.

Section PureDSPMonad.

  Definition StrictConjunctive {A} (w : SPPure A) : Prop :=
    Strict w /\ Conjunctive w.

  Definition DSPSP (A : Type) : Type := { w : SPPure A | StrictConjunctive w }.

  Definition getDSPSP {A} (w : DSPSP A) : SPPure A := proj1_sig w.

  Theorem strict_conj_iff_singleton {A} (w : SPPure A) :
    StrictConjunctive w <-> Singleton w.
  Proof.
    split.
    - intros [HS _]. exact (strict_to_singleton w HS).
    - intro H. split;
        [ exact (proj1 (singleton_to_join w H))
        | exact (singleton_to_conjunctive w H) ].
  Qed.

  (** The transports.  Both are the identity on the underlying transformer, so
      every law below is the corresponding [ASPSP] law read through them. *)

  Definition aspsp_to_dspsp {A} (w : ASPSP A) : DSPSP A :=
    exist _ (getASPSP w) (proj2 (strict_conj_iff_singleton (getASPSP w)) (proj2_sig w)).

  Definition dspsp_to_aspsp {A} (w : DSPSP A) : ASPSP A :=
    exist _ (getDSPSP w) (proj1 (strict_conj_iff_singleton (getDSPSP w)) (proj2_sig w)).

  Lemma getDSPSP_aspsp_to_dspsp {A} (w : ASPSP A) p a :
    getDSPSP (aspsp_to_dspsp w) p a <-> getASPSP w p a.
  Proof. split; intro H; exact H. Qed.

  Lemma getASPSP_dspsp_to_aspsp {A} (w : DSPSP A) p a :
    getASPSP (dspsp_to_aspsp w) p a <-> getDSPSP w p a.
  Proof. split; intro H; exact H. Qed.

  Definition retDSPSP {A} (v : A) : DSPSP A := aspsp_to_dspsp (retASPSP v).

  Definition bindDSPSP {A B} (m : DSPSP A) (k : A -> DSPSP B) : DSPSP B :=
    aspsp_to_dspsp (bindASPSP (dspsp_to_aspsp m) (fun a => dspsp_to_aspsp (k a))).

  #[global] Instance Monad_DSPSP : Monad DSPSP :=
    {| ret := fun _ => retDSPSP ;
      bind := fun _ _ => bindDSPSP |}.

  #[global] Instance Eq1_DSPSP : Eq1 DSPSP :=
    fun A m n => forall p a, getDSPSP m p a <-> getDSPSP n p a.

  #[global] Instance Eq1Equivalence_DSPSP
    : @Eq1Equivalence DSPSP _ Eq1_DSPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a); specialize (H2 p a). tauto.
  Qed.

  #[global] Instance MonadLawsE_DSPSP : @MonadLawsE DSPSP Eq1_DSPSP _.
  Proof.
    destruct (@MonadLawsE_ASPSP) as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => dspsp_to_aspsp (f a)) x).
    - intros A x. exact (Lbrr A (dspsp_to_aspsp x)).
    - intros A B C x f g.
      exact (Lbb A B C (dspsp_to_aspsp x) (fun a => dspsp_to_aspsp (f a))
               (fun b => dspsp_to_aspsp (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (dspsp_to_aspsp x) (dspsp_to_aspsp y) Hxy
               (fun a => dspsp_to_aspsp (f a)) (fun a => dspsp_to_aspsp (g a)) Hfg).
  Qed.

  Definition ordDSPSP {A} (m1 m2 : DSPSP A) : Prop :=
    forall p a, getDSPSP m1 p a -> getDSPSP m2 p a.
  Definition ordDSPSPAt {A} (pre : Prop) (m1 m2 : DSPSP A) : Prop :=
    forall a, getDSPSP m1 pre a -> getDSPSP m2 pre a.

  Lemma getDSPSP_mono {A} (w : DSPSP A) (p q : Prop) (a : A) :
    (p -> q) -> getDSPSP w p a -> getDSPSP w q a.
  Proof.
    intros Hpq Hw.
    pose proof (proj1 (strict_conj_iff_singleton (getDSPSP w)) (proj2_sig w) p a) as Hsp.
    pose proof (proj1 (strict_conj_iff_singleton (getDSPSP w)) (proj2_sig w) q a) as Hsq.
    apply (proj2 Hsq). split.
    - exact (Hpq (proj1 (proj1 Hsp Hw))).
    - exact (proj2 (proj1 Hsp Hw)).
  Qed.
  Lemma ordDSPSP_refl A (m : DSPSP A) : ordDSPSP m m.
  Proof. intros p a H. exact H. Qed.
  Lemma bindDSPSP_mono A B (m n : DSPSP A) (f g : A -> DSPSP B) :
    ordDSPSP m n -> (forall a, ordDSPSP (f a) (g a)) ->
    ordDSPSP (bindDSPSP m f) (bindDSPSP n g).
  Proof.
    intros Hmn Hfg p b [a H]. exists a. apply Hfg.
    apply (getDSPSP_mono (f a) (getDSPSP m p a) (getDSPSP n p a) b).
    - exact (Hmn p a).
    - exact H.
  Qed.
End PureDSPMonad.

(* ================================================================= *)
(** ** [DSPSP] is [DSP]                                               *)
(* ================================================================= *)

(** Three identifications compose: [DSPSP] is [ASPSP] by construction,
    [ASPSP] is [ASP] ([ASPMonad.v]), and [ASP] is [DSP] (above).  Each is
    the identity on transformers, up to reading a proposition as a predicate
    on [unit]. *)

Lemma asp_to_dsp_morphism :
  @MonadMorphism ASP DSP Monad_ASP Monad_DSP Eq1_ASP Eq1_DSP (fun A => @asp_to_dsp A).
Proof.
  constructor.
  - intros A x y H P a. exact (H P a).
  - intros A a. exact (asp_to_dsp_ret a).
  - intros A B x k. exact (asp_to_dsp_bind x k).
Qed.

Lemma dspsp_to_aspsp_morphism :
  @MonadMorphism DSPSP ASPSP Monad_DSPSP Monad_ASPSP Eq1_DSPSP Eq1_ASPSP
    (fun A => @dspsp_to_aspsp A).
Proof.
  constructor.
  - intros A x y H p a. exact (H p a).
  - intros A a p b. reflexivity.
  - intros A B x k p b. reflexivity.
Qed.

Lemma aspsp_to_dspsp_morphism :
  @MonadMorphism ASPSP DSPSP Monad_ASPSP Monad_DSPSP Eq1_ASPSP Eq1_DSPSP
    (fun A => @aspsp_to_dspsp A).
Proof.
  constructor.
  - intros A x y H p a. exact (H p a).
  - intros A a p b. reflexivity.
  - intros A B x k p b. reflexivity.
Qed.

Definition dspsp_to_dsp {A} (w : DSPSP A) : DSP A :=
  asp_to_dsp (aspsp_to_asp (dspsp_to_aspsp w)).

Definition dsp_to_dspsp {A} (d : DSP A) : DSPSP A :=
  aspsp_to_dspsp (asp_to_aspsp (dsp_to_asp d)).

Lemma get_dspsp_to_dsp {A} (w : DSPSP A) P a :
  getDSP (dspsp_to_dsp w) P a <-> getDSPSP w (P tt) a.
Proof. reflexivity. Qed.

Lemma get_dsp_to_dspsp {A} (d : DSP A) p a :
  getDSPSP (dsp_to_dspsp d) p a <-> getDSPPure d p a.
Proof. reflexivity. Qed.

(** The two maps are mutually inverse. *)

Lemma dspsp_to_dsp_to_dspsp {A} (w : DSPSP A) :
  @eq1 DSPSP Eq1_DSPSP A (dsp_to_dspsp (dspsp_to_dsp w)) w.
Proof. intros p a. reflexivity. Qed.

Lemma dsp_to_dspsp_to_dsp {A} (d : DSP A) :
  @eq1 DSP Eq1_DSP A (dspsp_to_dsp (dsp_to_dspsp d)) d.
Proof.
  intros P a. apply (getDSP_cong d (fun _ => P tt) P a). intros []. reflexivity.
Qed.

(** Both preserve [ret] and [bind]. *)

Theorem dspsp_to_dsp_morphism :
  @MonadMorphism DSPSP DSP Monad_DSPSP Monad_DSP Eq1_DSPSP Eq1_DSP
    (fun A => @dspsp_to_dsp A).
Proof.
  exact (@MonadMorphism_comp DSPSP ASP DSP Monad_DSPSP Monad_ASP Monad_DSP
           Eq1_DSPSP Eq1_ASP Eq1_DSP Eq1Equivalence_DSP _ _
           (@MonadMorphism_comp DSPSP ASPSP ASP Monad_DSPSP Monad_ASPSP Monad_ASP
              Eq1_DSPSP Eq1_ASPSP Eq1_ASP Eq1Equivalence_ASP _ _
              dspsp_to_aspsp_morphism aspsp_to_asp_morphism)
           asp_to_dsp_morphism).
Qed.

Theorem dsp_to_dspsp_morphism :
  @MonadMorphism DSP DSPSP Monad_DSP Monad_DSPSP Eq1_DSP Eq1_DSPSP
    (fun A => @dsp_to_dspsp A).
Proof.
  exact (@MonadMorphism_comp DSP ASPSP DSPSP Monad_DSP Monad_ASPSP Monad_DSPSP
           Eq1_DSP Eq1_ASPSP Eq1_DSPSP Eq1Equivalence_DSPSP _ _
           (@MonadMorphism_comp DSP ASP ASPSP Monad_DSP Monad_ASP Monad_ASPSP
              Eq1_DSP Eq1_ASP Eq1_ASPSP Eq1Equivalence_ASPSP _ _
              dsp_to_asp_morphism asp_to_aspsp_morphism)
           aspsp_to_dspsp_morphism).
Qed.

(** Both preserve and reflect the order. *)

Lemma ordDSPSP_dspsp_to_dsp {A} (w w' : DSPSP A) :
  ordDSPSP w w' <-> ordDSP (dspsp_to_dsp w) (dspsp_to_dsp w').
Proof.
  split.
  - intros H P a. exact (H (P tt) a).
  - intros H p a. exact (H (fun _ => p) a).
Qed.

Lemma ordDSP_dsp_to_dspsp {A} (d d' : DSP A) :
  ordDSP d d' <-> ordDSPSP (dsp_to_dspsp d) (dsp_to_dspsp d').
Proof.
  split.
  - intros H p a. exact (H (fun _ => p) a).
  - intros H P a HP.
    refine (proj1 (getDSP_cong d' (fun _ => P tt) P a _) _);
      [ intros []; reflexivity |].
    apply (H (P tt) a).
    refine (proj2 (getDSP_cong d (fun _ => P tt) P a _) HP).
    intros []. reflexivity.
Qed.

(** So [DSPSP] is a specification monad: its order is [ASPSP]'s. *)

Theorem OrderedMonad_DSPSP :
  @OrderedMonad DSPSP Monad_DSPSP Eq1_DSPSP (@ordDSPSP).
Proof.
  exact (@OrderedMonad_pullback DSPSP ASPSP Monad_DSPSP Monad_ASPSP
           Eq1_DSPSP Eq1_ASPSP Eq1Equivalence_ASPSP
           (fun A => @dspsp_to_aspsp A) (@ordASPSP)
           dspsp_to_aspsp_morphism OrderedMonad_ASPSP).
Qed.
