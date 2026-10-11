(** * The carriers of the SP and WP monads inside the monotone arrow carrier
      (paper, Section 4).

    The WP monads are read at the second index of [MonoPT] and the SP monads
    at the first; the four refinements of each family become subsets of
    that one carrier, where [TransformerTaxonomy.v] states implication,
    contrapositive and Galois connection once.  The broad monads [WSt S]
    and [SPStMon S], the variants inside them, the pure level, and the
    duals and adjoints of the healthiness classes.  [MonadTaxonomy.v]
    states the relations on the monads. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions Setoid Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import
  Arrow OptionArrowT StateArrowT.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.
From Incorrectness.Lib.Arrow Require Import
  ArrowMonad RelArrowCoherence.
From Incorrectness.Lib.Monad Require Import
  MonadRelation.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Import SPostArr DSPASLPArr.
From Incorrectness.Taxonomy Require Import TransformerTaxonomy.
From Incorrectness.WP Require Import
  WPure WPVariants.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy Require Import SPStBindComparisons.
From Incorrectness.Relational Require
  PredMonad.
From Incorrectness.SP Require
  RawSP.
From Incorrectness.Taxonomy Require
  MonotoneSPSt.

Import MonotoneSPSt.SPStMonotone.

Local Notation Monad_SPStMon_angelic := (@AngelicMonotone.Monad__AngelicSPStMon _).
Local Notation Monad_SPStMon_demonic := (@DemonicMonotone.Monad__DemonicSPStMon _).

Local Notation Pred := PredMonad.PredM.Pred.
Local Notation Monad_Pred := PredMonad.PredM.Monad_Pred.

(* ================================================================= *)
(** * The carriers of the SP and WP monads inside the monotone arrow carrier *)
(* ================================================================= *)

(** [TransformerTaxonomy.v] states the relations of the taxonomy on
    [MonoPT A B], monotone maps from predicates on [A] to predicates on
    [B].  This part shows that the carriers of the specification monads are
    that type with one index fixed, so that the relations apply to them:

      SP, first index fixed at the state [S]:    [MonoPT S (A * S)]
      WP, second index fixed at the state [S]:   [MonoPT (A * S) S]

    The isomorphisms are of CARRIERS.  The monad operations are not
    transported: the SP monads take theirs from an arrow at a fixed input,
    the WP monads from [WPure], and no arrow structure on [MonoPT] gives the
    latter.

    The broad monads:

      [WSt S A]                 ~  [MonoPT (A * S) S]     ([wstPT], [ptWSt])
      [SPStMonotone.SPStMon S A] ~  [MonoPT S (A * S)]     ([spstPT], [ptSPSt])

    The four flavours are the same four refinements of the arrow carrier on
    both sides, at swapped indices:

      [ASPSt S A]   ~  [ASPArr S (A * S)]      [AWPSt S A]   ~  [ASPArr (A * S) S]
      [DSLPSt S A]  ~  [DSLPArr S (A * S)]     [DWLPSt S A]  ~  [DSLPArr (A * S) S]
      [DSPSt S A]   ~  [DSPArr S (A * S)]      [DWPSt S A]   ~  [DSPArr (A * S) S]
      [ASLPSt S A]  ~  [ASLPArr S (A * S)]     [AWLPSt S A]  ~  [ASLPArr (A * S) S]

    and likewise without state, with [unit] as the fixed index
    ([Section PureCarriers]).

    [aspMono] &c. forget the extra homomorphism properties and land in
    [MonoPT]; [aspStPT], [awpStPT] &c. are the resulting images of the
    monads' elements, on which [pt_le], [Contrapositive] and [GaloisPT]
    are stated.  The orders agree: an SP monad's order is [pt_le] on the
    images, a WP monad's refinement is its converse [pt_ge].

    The last two sections show which refinements each of the other two
    relations pairs.  Every element of [ASPArr A B] has a contrapositive in
    [DSLPArr A B] and conversely, and likewise for [DSPArr A B] and
    [ASLPArr A B].  Every element of [ASPArr A B] has a right adjoint in
    [DSLPArr B A], and every element of [DSLPArr B A] a left adjoint in
    [ASPArr A B]. *)

(* ================================================================= *)
(** ** The second index, one state at a time                         *)
(* ================================================================= *)

(** A transformer in [PT B S] is a family of unary transformers indexed by
    [S], and each homomorphism property of [SP/SPostArr.v] is the corresponding
    property of [WPureMonad.v] at every state. *)

Section SecondIndex.
  Context {S B : Type} (t : PT B S).

  Lemma sp_monotone_at : sp_monotone t <-> forall s, wpure_mono (fun Q => t Q s).
  Proof.
    split.
    - intros H s p q Hpq. exact (H p q Hpq s).
    - intros H P Q HPQ s. exact (H s P Q HPQ).
  Qed.

  Lemma sp_strict_at : sp_strict t <-> forall s, wpure_strict (fun Q => t Q s).
  Proof. split; intros H s; exact (H s). Qed.

  Lemma sp_terminating_at :
    sp_terminating t <-> forall s, wpure_terminating (fun Q => t Q s).
  Proof. split; intros H s; exact (H s). Qed.

  Lemma sp_conjunctive_at :
    sp_conjunctive t <-> forall s, wpure_conjunctive (fun Q => t Q s).
  Proof.
    split.
    - intros H s I HI q. exact (H I HI q s).
    - intros H I HI P s. exact (H s I HI P).
  Qed.

  Lemma sp_disjunctive_at :
    sp_disjunctive t <-> forall s, wpure_disjunctive (fun Q => t Q s).
  Proof.
    split.
    - intros H s I HI q. exact (H I HI q s).
    - intros H I HI P s. exact (H s I HI P).
  Qed.

  Lemma awp_health_at :
    sp_monotone t /\ sp_strict t /\ sp_disjunctive t
    <-> forall s, awp_health B (fun Q => t Q s).
  Proof.
    split.
    - intros [H1 [H2 H3]] s.
      exact (conj (proj1 sp_monotone_at H1 s)
               (conj (proj1 sp_strict_at H2 s) (proj1 sp_disjunctive_at H3 s))).
    - intro H. split; [| split ].
      + apply sp_monotone_at. intro s. exact (proj1 (H s)).
      + apply sp_strict_at. intro s. exact (proj1 (proj2 (H s))).
      + apply sp_disjunctive_at. intro s. exact (proj2 (proj2 (H s))).
  Qed.

  Lemma dwlp_health_at :
    sp_monotone t /\ sp_terminating t /\ sp_conjunctive t
    <-> forall s, dwlp_health B (fun Q => t Q s).
  Proof.
    split.
    - intros [H1 [H2 H3]] s.
      exact (conj (proj1 sp_monotone_at H1 s)
               (conj (proj1 sp_terminating_at H2 s) (proj1 sp_conjunctive_at H3 s))).
    - intro H. split; [| split ].
      + apply sp_monotone_at. intro s. exact (proj1 (H s)).
      + apply sp_terminating_at. intro s. exact (proj1 (proj2 (H s))).
      + apply sp_conjunctive_at. intro s. exact (proj2 (proj2 (H s))).
  Qed.

  Lemma dwp_health_at :
    sp_monotone t /\ sp_strict t /\ sp_conjunctive t
    <-> forall s, dwp_health B (fun Q => t Q s).
  Proof.
    split.
    - intros [H1 [H2 H3]] s.
      exact (conj (proj1 sp_monotone_at H1 s)
               (conj (proj1 sp_strict_at H2 s) (proj1 sp_conjunctive_at H3 s))).
    - intro H. split; [| split ].
      + apply sp_monotone_at. intro s. exact (proj1 (H s)).
      + apply sp_strict_at. intro s. exact (proj1 (proj2 (H s))).
      + apply sp_conjunctive_at. intro s. exact (proj2 (proj2 (H s))).
  Qed.

  Lemma awlp_health_at :
    sp_monotone t /\ sp_terminating t /\ sp_disjunctive t
    <-> forall s, awlp_health B (fun Q => t Q s).
  Proof.
    split.
    - intros [H1 [H2 H3]] s.
      exact (conj (proj1 sp_monotone_at H1 s)
               (conj (proj1 sp_terminating_at H2 s) (proj1 sp_disjunctive_at H3 s))).
    - intro H. split; [| split ].
      + apply sp_monotone_at. intro s. exact (proj1 (H s)).
      + apply sp_terminating_at. intro s. exact (proj1 (proj2 (H s))).
      + apply sp_disjunctive_at. intro s. exact (proj2 (proj2 (H s))).
  Qed.
End SecondIndex.

(* ================================================================= *)
(** ** The first index, along [S ~ unit * S]                         *)
(* ================================================================= *)

(** The SP monads are arrows at input [unit] under [stateArrT S], so their
    first index is [unit * S].  [pullS] reads such a transformer at a
    precondition on [S] alone and [pushS] goes back; both preserve every
    homomorphism property. *)

Section FirstIndex.
  Context {S B : Type}.

  Definition pullS (f : PT (unit * S) B) : PT S B :=
    fun P b => f (fun p => P (snd p)) b.

  Definition pushS (g : PT S B) : PT (unit * S) B :=
    fun P b => g (fun s => P (tt, s)) b.

  Lemma pullS_monotone f : sp_monotone f -> sp_monotone (pullS f).
  Proof. intros H P Q HPQ b. apply H. intro p. apply HPQ. Qed.

  Lemma pullS_strict f : sp_strict f -> sp_strict (pullS f).
  Proof. intros H b. exact (H b). Qed.

  Lemma pullS_terminating f : sp_terminating f -> sp_terminating (pullS f).
  Proof. intros H b. exact (H b). Qed.

  Lemma pullS_conjunctive f : sp_conjunctive f -> sp_conjunctive (pullS f).
  Proof. intros H I HI P b. exact (H I HI (fun i p => P i (snd p)) b). Qed.

  Lemma pullS_disjunctive f : sp_disjunctive f -> sp_disjunctive (pullS f).
  Proof. intros H I HI P b. exact (H I HI (fun i p => P i (snd p)) b). Qed.

  Lemma pushS_monotone g : sp_monotone g -> sp_monotone (pushS g).
  Proof. intros H P Q HPQ b. apply H. intro s. apply HPQ. Qed.

  Lemma pushS_strict g : sp_strict g -> sp_strict (pushS g).
  Proof. intros H b. exact (H b). Qed.

  Lemma pushS_terminating g : sp_terminating g -> sp_terminating (pushS g).
  Proof. intros H b. exact (H b). Qed.

  Lemma pushS_conjunctive g : sp_conjunctive g -> sp_conjunctive (pushS g).
  Proof. intros H I HI P b. exact (H I HI (fun i s => P i (tt, s)) b). Qed.

  Lemma pushS_disjunctive g : sp_disjunctive g -> sp_disjunctive (pushS g).
  Proof. intros H I HI P b. exact (H I HI (fun i s => P i (tt, s)) b). Qed.

  Lemma pullS_pushS g P b : pullS (pushS g) P b <-> g P b.
  Proof. reflexivity. Qed.

  Lemma pushS_pullS f P b : sp_monotone f -> (pushS (pullS f) P b <-> f P b).
  Proof. intro H. split; apply H; intros [[] s] Hp; exact Hp. Qed.

  (** Implication and equivalence may be checked after [pullS]. *)
  Lemma pullS_le f g :
    sp_monotone f -> sp_monotone g ->
    (forall P b, f P b -> g P b) <-> (forall P b, pullS f P b -> pullS g P b).
  Proof.
    intros Hf Hg. split.
    - intros H P b. apply H.
    - intros H P b Hp. apply (pushS_pullS g P b Hg). apply H.
      apply (pushS_pullS f P b Hf). exact Hp.
  Qed.

  Lemma pullS_eq f g :
    sp_monotone f -> sp_monotone g ->
    (forall P b, f P b <-> g P b) <-> (forall P b, pullS f P b <-> pullS g P b).
  Proof.
    intros Hf Hg. split.
    - intros H P b. apply H.
    - intros H P b.
      rewrite <- (pushS_pullS f P b Hf), <- (pushS_pullS g P b Hg). apply H.
  Qed.
End FirstIndex.

(* ================================================================= *)
(** ** The four refinements inside the monotone carrier              *)
(* ================================================================= *)

Definition aspMono {A B} (f : ASPArr A B) : MonoPT A B :=
  mkMonoPT (getASPArr f) (proj1 (proj2_sig f)).

Definition dslpMono {A B} (f : DSLPArr A B) : MonoPT A B :=
  mkMonoPT (getDSLPArr f) (proj1 (proj2_sig f)).

Definition dspMono {A B} (f : DSPArr A B) : MonoPT A B :=
  mkMonoPT (getDSP f) (proj1 (proj2_sig f)).

Definition aslpMono {A B} (f : ASLPArr A B) : MonoPT A B :=
  mkMonoPT (getASLP f) (proj1 (proj2_sig f)).

(** [MonoPT] and its order are the monotone carrier of [TransformerTaxonomy.v] and
    its order, under the neutral names. *)

Lemma MonoPT_MonotoneSPost A B : MonoPT A B = TransformerTaxonomy.MonotoneSPost A B.
Proof. reflexivity. Qed.

Lemma pt_le_MonotoneSPost_le A B : @pt_le A B = @TransformerTaxonomy.MonotoneSPost_le A B.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** The broad monads                                              *)
(* ================================================================= *)

Section Broad.
  Context {S A : Type}.

  (** *** [WSt S A], at the second index *)

  #[program] Definition wstPT (w : WSt S A) : MonoPT (A * S) S :=
    fun Q s => getWPure (runStateT w s) Q.
  Next Obligation. intros P Q H s. exact (getWPure_mono (runStateT w s) P Q H). Qed.

  #[program] Definition ptWSt (t : MonoPT (A * S) S) : WSt S A :=
    mkStateT (fun s => mkWPure (fun Q => t Q s) _).
  Next Obligation. intros p q H. exact (getPT_mono t p q s H). Qed.

  Lemma ptWSt_wstPT (w : WSt S A) :
    @eq1 (WSt S) (Eq1__WSt S) A (ptWSt (wstPT w)) w.
  Proof. intros s Q. reflexivity. Qed.

  Lemma wstPT_ptWSt (t : MonoPT (A * S) S) : pt_eq (wstPT (ptWSt t)) t.
  Proof. intros Q s. reflexivity. Qed.

  (** [ordWSt] is refinement, the converse of implication. *)
  Lemma ordWSt_pt (w1 w2 : WSt S A) : ordWSt w1 w2 <-> pt_ge (wstPT w1) (wstPT w2).
  Proof. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ]. Qed.

  Lemma eq1_WSt_pt (w1 w2 : WSt S A) :
    @eq1 (WSt S) (Eq1__WSt S) A w1 w2 <-> pt_eq (wstPT w1) (wstPT w2).
  Proof. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ]. Qed.

  Lemma wstPT_ret (a : A) Q s : wstPT (ret a : WSt S A) Q s <-> Q (a, s).
  Proof. reflexivity. Qed.

  (** *** [SPStMon S A], at the first index *)

  Import MonotoneSPSt.SPStMonotone.

  #[program] Definition spstPT (m : SPStMon S A) : MonoPT S (A * S) :=
    fun P r => proj1_sig m P r.
  Next Obligation. intros P Q H r. exact (proj2_sig m P Q r H). Qed.

  Definition ptSPSt (t : MonoPT S (A * S)) : SPStMon S A :=
    exist (@SPStMonotone S A) (fun P r => t P r)
      (fun P Q r H => getPT_mono t P Q r H).

  Lemma ptSPSt_spstPT (m : SPStMon S A) P r :
    proj1_sig (ptSPSt (spstPT m)) P r <-> proj1_sig m P r.
  Proof. reflexivity. Qed.

  Lemma spstPT_ptSPSt (t : MonoPT S (A * S)) : pt_eq (spstPT (ptSPSt t)) t.
  Proof. intros P r. reflexivity. Qed.

  Lemma ordSPStMon_pt (m n : SPStMon S A) :
    ordSPStMon m n <-> pt_le (spstPT m) (spstPT n).
  Proof. split; intro H; exact H. Qed.

  Lemma pt_le_ptSPSt (t1 t2 : MonoPT S (A * S)) :
    pt_le t1 t2 <-> ordSPStMon (ptSPSt t1) (ptSPSt t2).
  Proof. split; intro H; exact H. Qed.
End Broad.

Lemma wstPT_bind {S A B} (w : WSt S A) (k : A -> WSt S B) Q s :
  wstPT (bind w k) Q s <-> wstPT w (fun r => wstPT (k (fst r)) Q (snd r)) s.
Proof. cbn. split; apply getWPure_mono; intros [a s'] H; exact H. Qed.

(** [WPure A], the same at a trivial state. *)

#[program] Definition wpurePT {A} (w : WPure A) : MonoPT A unit :=
  fun Q _ => getWPure w Q.
Next Obligation. intros P Q H _. exact (getWPure_mono w P Q H). Qed.

#[program] Definition ptWPure {A} (t : MonoPT A unit) : WPure A :=
  mkWPure (fun Q => t Q tt) _.
Next Obligation. intros p q H. exact (getPT_mono t p q tt H). Qed.

Lemma ptWPure_wpurePT {A} (w : WPure A) : eq1 (ptWPure (wpurePT w)) w.
Proof. intro Q. reflexivity. Qed.

Lemma wpurePT_ptWPure {A} (t : MonoPT A unit) : pt_eq (wpurePT (ptWPure t)) t.
Proof. intros Q []. reflexivity. Qed.

Lemma WP_le_pt {A} (w1 w2 : WPure A) : WP_le w1 w2 <-> pt_ge (wpurePT w1) (wpurePT w2).
Proof. split; [ intros H Q u; exact (H Q) | intros H Q; exact (H Q tt) ]. Qed.

(* ================================================================= *)
(** ** The WP flavours, at the second index                          *)
(* ================================================================= *)

(** For any healthiness condition: the image in the monotone carrier. *)

Section WPSubStPT.
  Context {h : WPHealth} {S A : Type}.

  #[program] Definition wpsubStPT (w : WPSubSt h S A) : MonoPT (A * S) S :=
    getWPSubSt w.
  Next Obligation. intros P Q H s. exact (getWPSubSt_mono h S w P Q s H). Qed.

  Lemma WPSubSt_le_pt (w1 w2 : WPSubSt h S A) :
    WPSubSt_le w1 w2 <-> pt_ge (wpsubStPT w1) (wpsubStPT w2).
  Proof. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ]. Qed.

  Lemma eq1_WPSubSt_pt (w1 w2 : WPSubSt h S A) :
    @eq1 (WPSubSt h S) (Eq1_WPSubSt h S) A w1 w2
    <-> pt_eq (wpsubStPT w1) (wpsubStPT w2).
  Proof. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ]. Qed.

  (** It is the broad monad's, after the inclusion into [WSt S]. *)
  Lemma wpsubStPT_toWSt (w : WPSubSt h S A) : pt_eq (wpsubStPT w) (wstPT (toWSt w)).
  Proof. intros Q s. reflexivity. Qed.
End WPSubStPT.

(** Elements of two different flavours are compared in [WSt S], where
    implication between their transformers is refinement the other way. *)
Lemma pt_le_toWSt {h1 h2 : WPHealth} {S A}
  (w1 : WPSubSt h1 S A) (w2 : WPSubSt h2 S A) :
  pt_le (wpsubStPT w1) (wpsubStPT w2) <-> ordWSt (toWSt w2) (toWSt w1).
Proof. split; [ intros H s Q; exact (H Q s) | intros H Q s; exact (H s Q) ]. Qed.

Section WPFlavourCarriers.
  Context {S A : Type}.

  (** *** [AWPSt S A ~ ASPArr (A * S) S] *)

  Definition awpStArr (w : AWPSt S A) : ASPArr (A * S) S :=
    exist _ (getAWPSt w)
      (proj2 (awp_health_at (getAWPSt w)) (fun s => proj2_sig (runStateT w s))).

  Definition arrAWPSt (t : ASPArr (A * S) S) : AWPSt S A :=
    mkStateT (fun s => exist _ (fun Q => getASPArr t Q s)
                         (proj1 (awp_health_at (getASPArr t)) (proj2_sig t) s)).

  Lemma arrAWPSt_awpStArr (w : AWPSt S A) : eq1 (arrAWPSt (awpStArr w)) w.
  Proof. intros s Q. reflexivity. Qed.

  Lemma awpStArr_arrAWPSt (t : ASPArr (A * S) S) : ASPArr_eq (awpStArr (arrAWPSt t)) t.
  Proof. intros Q s. reflexivity. Qed.

  Definition awpStPT (w : AWPSt S A) : MonoPT (A * S) S := wpsubStPT w.

  Lemma awpStPT_arr (w : AWPSt S A) : pt_eq (awpStPT w) (aspMono (awpStArr w)).
  Proof. intros Q s. reflexivity. Qed.

  (** *** [DWLPSt S A ~ DSLPArr (A * S) S] *)

  Definition dwlpStArr (w : DWLPSt S A) : DSLPArr (A * S) S :=
    exist _ (getDWLPSt w)
      (proj2 (dwlp_health_at (getDWLPSt w)) (fun s => proj2_sig (runStateT w s))).

  Definition arrDWLPSt (t : DSLPArr (A * S) S) : DWLPSt S A :=
    mkStateT (fun s => exist _ (fun Q => getDSLPArr t Q s)
                         (proj1 (dwlp_health_at (getDSLPArr t)) (proj2_sig t) s)).

  Lemma arrDWLPSt_dwlpStArr (w : DWLPSt S A) : eq1 (arrDWLPSt (dwlpStArr w)) w.
  Proof. intros s Q. reflexivity. Qed.

  Lemma dwlpStArr_arrDWLPSt (t : DSLPArr (A * S) S) :
    DSLPArr_eq (dwlpStArr (arrDWLPSt t)) t.
  Proof. intros Q s. reflexivity. Qed.

  Definition dwlpStPT (w : DWLPSt S A) : MonoPT (A * S) S := wpsubStPT w.

  Lemma dwlpStPT_arr (w : DWLPSt S A) : pt_eq (dwlpStPT w) (dslpMono (dwlpStArr w)).
  Proof. intros Q s. reflexivity. Qed.

  (** *** [DWPSt S A ~ DSPArr (A * S) S] *)

  Definition dwpStArr (w : DWPSt S A) : DSPArr (A * S) S :=
    exist _ (getDWPSt w)
      (proj2 (dwp_health_at (getDWPSt w)) (fun s => proj2_sig (runStateT w s))).

  Definition arrDWPSt (t : DSPArr (A * S) S) : DWPSt S A :=
    mkStateT (fun s => exist _ (fun Q => getDSP t Q s)
                         (proj1 (dwp_health_at (getDSP t)) (proj2_sig t) s)).

  Lemma arrDWPSt_dwpStArr (w : DWPSt S A) : eq1 (arrDWPSt (dwpStArr w)) w.
  Proof. intros s Q. reflexivity. Qed.

  Lemma dwpStArr_arrDWPSt (t : DSPArr (A * S) S) : DSPArr_eq (dwpStArr (arrDWPSt t)) t.
  Proof. intros Q s. reflexivity. Qed.

  Definition dwpStPT (w : DWPSt S A) : MonoPT (A * S) S := wpsubStPT w.

  Lemma dwpStPT_arr (w : DWPSt S A) : pt_eq (dwpStPT w) (dspMono (dwpStArr w)).
  Proof. intros Q s. reflexivity. Qed.

  (** *** [AWLPSt S A ~ ASLPArr (A * S) S] *)

  Definition awlpStArr (w : AWLPSt S A) : ASLPArr (A * S) S :=
    exist _ (getAWLPSt w)
      (proj2 (awlp_health_at (getAWLPSt w)) (fun s => proj2_sig (runStateT w s))).

  Definition arrAWLPSt (t : ASLPArr (A * S) S) : AWLPSt S A :=
    mkStateT (fun s => exist _ (fun Q => getASLP t Q s)
                         (proj1 (awlp_health_at (getASLP t)) (proj2_sig t) s)).

  Lemma arrAWLPSt_awlpStArr (w : AWLPSt S A) : eq1 (arrAWLPSt (awlpStArr w)) w.
  Proof. intros s Q. reflexivity. Qed.

  Lemma awlpStArr_arrAWLPSt (t : ASLPArr (A * S) S) :
    ASLPArr_eq (awlpStArr (arrAWLPSt t)) t.
  Proof. intros Q s. reflexivity. Qed.

  Definition awlpStPT (w : AWLPSt S A) : MonoPT (A * S) S := wpsubStPT w.

  Lemma awlpStPT_arr (w : AWLPSt S A) : pt_eq (awlpStPT w) (aslpMono (awlpStArr w)).
  Proof. intros Q s. reflexivity. Qed.

  (** *** The refinement orders are the converse of implication *)

  Lemma ordAWPSt_pt (w1 w2 : AWPSt S A) :
    ordAWPSt w1 w2 <-> pt_ge (awpStPT w1) (awpStPT w2).
  Proof. apply WPSubSt_le_pt. Qed.

  Lemma ordDWLPSt_pt (w1 w2 : DWLPSt S A) :
    ordDWLPSt w1 w2 <-> pt_ge (dwlpStPT w1) (dwlpStPT w2).
  Proof. apply WPSubSt_le_pt. Qed.

  Lemma ordDWPSt_pt (w1 w2 : DWPSt S A) :
    ordDWPSt w1 w2 <-> pt_ge (dwpStPT w1) (dwpStPT w2).
  Proof. apply WPSubSt_le_pt. Qed.

  Lemma ordAWLPSt_pt (w1 w2 : AWLPSt S A) :
    ordAWLPSt w1 w2 <-> pt_ge (awlpStPT w1) (awlpStPT w2).
  Proof. apply WPSubSt_le_pt. Qed.
End WPFlavourCarriers.

(* ================================================================= *)
(** ** The SP flavours, at the first index                           *)
(* ================================================================= *)

Section SPFlavourCarriers.
  Context {S A : Type}.

  (** *** [ASPSt S A ~ ASPArr S (A * S)] *)

  Definition aspStArr (m : ASPSt S A) : ASPArr S (A * S) :=
    exist _ (pullS (getASPArr m))
      (conj (pullS_monotone _ (proj1 (proj2_sig m)))
         (conj (pullS_strict _ (proj1 (proj2 (proj2_sig m))))
               (pullS_disjunctive _ (proj2 (proj2 (proj2_sig m)))))).

  Definition arrASPSt (g : ASPArr S (A * S)) : ASPSt S A :=
    exist _ (pushS (getASPArr g))
      (conj (pushS_monotone _ (proj1 (proj2_sig g)))
         (conj (pushS_strict _ (proj1 (proj2 (proj2_sig g))))
               (pushS_disjunctive _ (proj2 (proj2 (proj2_sig g)))))).

  Lemma arrASPSt_aspStArr (m : ASPSt S A) : eq1 (arrASPSt (aspStArr m)) m.
  Proof. intros P r. exact (pushS_pullS (getASPArr m) P r (proj1 (proj2_sig m))). Qed.

  Lemma aspStArr_arrASPSt (g : ASPArr S (A * S)) : ASPArr_eq (aspStArr (arrASPSt g)) g.
  Proof. intros P r. reflexivity. Qed.

  Definition aspStPT (m : ASPSt S A) : MonoPT S (A * S) := aspMono (aspStArr m).

  (** The isomorphism is the reading at a shared precondition. *)
  Lemma aspStPT_get (m : ASPSt S A) P r : aspStPT m P r <-> getASPSt m P r.
  Proof. reflexivity. Qed.

  Lemma ordASPSt_pt (m n : ASPSt S A) : ordASPSt m n <-> pt_le (aspStPT m) (aspStPT n).
  Proof. exact (pullS_le _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  Lemma eq1_ASPSt_pt (m n : ASPSt S A) : eq1 m n <-> pt_eq (aspStPT m) (aspStPT n).
  Proof. exact (pullS_eq _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  (** *** [DSLPSt S A ~ DSLPArr S (A * S)] *)

  Definition dslpStArr (m : DSLPSt S A) : DSLPArr S (A * S) :=
    exist _ (pullS (getDSLPArr m))
      (conj (pullS_monotone _ (proj1 (proj2_sig m)))
         (conj (pullS_terminating _ (proj1 (proj2 (proj2_sig m))))
               (pullS_conjunctive _ (proj2 (proj2 (proj2_sig m)))))).

  Definition arrDSLPSt (g : DSLPArr S (A * S)) : DSLPSt S A :=
    exist _ (pushS (getDSLPArr g))
      (conj (pushS_monotone _ (proj1 (proj2_sig g)))
         (conj (pushS_terminating _ (proj1 (proj2 (proj2_sig g))))
               (pushS_conjunctive _ (proj2 (proj2 (proj2_sig g)))))).

  Lemma arrDSLPSt_dslpStArr (m : DSLPSt S A) : eq1 (arrDSLPSt (dslpStArr m)) m.
  Proof. intros P r. exact (pushS_pullS (getDSLPArr m) P r (proj1 (proj2_sig m))). Qed.

  Lemma dslpStArr_arrDSLPSt (g : DSLPArr S (A * S)) :
    DSLPArr_eq (dslpStArr (arrDSLPSt g)) g.
  Proof. intros P r. reflexivity. Qed.

  Definition dslpStPT (m : DSLPSt S A) : MonoPT S (A * S) := dslpMono (dslpStArr m).

  Lemma dslpStPT_get (m : DSLPSt S A) P r : dslpStPT m P r <-> getDSLPSt m P r.
  Proof. reflexivity. Qed.

  Lemma ordDSLPSt_pt (m n : DSLPSt S A) :
    ordDSLPSt m n <-> pt_le (dslpStPT m) (dslpStPT n).
  Proof. exact (pullS_le _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  Lemma eq1_DSLPSt_pt (m n : DSLPSt S A) : eq1 m n <-> pt_eq (dslpStPT m) (dslpStPT n).
  Proof. exact (pullS_eq _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  (** *** [DSPSt S A ~ DSPArr S (A * S)] *)

  Definition dspStArr (m : DSPSt S A) : DSPArr S (A * S) :=
    exist _ (pullS (getDSP m))
      (conj (pullS_monotone _ (proj1 (proj2_sig m)))
         (conj (pullS_strict _ (proj1 (proj2 (proj2_sig m))))
               (pullS_conjunctive _ (proj2 (proj2 (proj2_sig m)))))).

  Definition arrDSPSt (g : DSPArr S (A * S)) : DSPSt S A :=
    exist _ (pushS (getDSP g))
      (conj (pushS_monotone _ (proj1 (proj2_sig g)))
         (conj (pushS_strict _ (proj1 (proj2 (proj2_sig g))))
               (pushS_conjunctive _ (proj2 (proj2 (proj2_sig g)))))).

  Lemma arrDSPSt_dspStArr (m : DSPSt S A) : eq1 (arrDSPSt (dspStArr m)) m.
  Proof. intros P r. exact (pushS_pullS (getDSP m) P r (proj1 (proj2_sig m))). Qed.

  Lemma dspStArr_arrDSPSt (g : DSPArr S (A * S)) : DSPArr_eq (dspStArr (arrDSPSt g)) g.
  Proof. intros P r. reflexivity. Qed.

  Definition dspStPT (m : DSPSt S A) : MonoPT S (A * S) := dspMono (dspStArr m).

  Lemma dspStPT_get (m : DSPSt S A) P r : dspStPT m P r <-> getDSPSt m P r.
  Proof. reflexivity. Qed.

  Lemma ordDSPSt_pt (m n : DSPSt S A) : ordDSPSt m n <-> pt_le (dspStPT m) (dspStPT n).
  Proof. exact (pullS_le _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  Lemma eq1_DSPSt_pt (m n : DSPSt S A) : eq1 m n <-> pt_eq (dspStPT m) (dspStPT n).
  Proof. exact (pullS_eq _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  (** *** [ASLPSt S A ~ ASLPArr S (A * S)] *)

  Definition aslpStArr (m : ASLPSt S A) : ASLPArr S (A * S) :=
    exist _ (pullS (getASLP m))
      (conj (pullS_monotone _ (proj1 (proj2_sig m)))
         (conj (pullS_terminating _ (proj1 (proj2 (proj2_sig m))))
               (pullS_disjunctive _ (proj2 (proj2 (proj2_sig m)))))).

  Definition arrASLPSt (g : ASLPArr S (A * S)) : ASLPSt S A :=
    exist _ (pushS (getASLP g))
      (conj (pushS_monotone _ (proj1 (proj2_sig g)))
         (conj (pushS_terminating _ (proj1 (proj2 (proj2_sig g))))
               (pushS_disjunctive _ (proj2 (proj2 (proj2_sig g)))))).

  Lemma arrASLPSt_aslpStArr (m : ASLPSt S A) : eq1 (arrASLPSt (aslpStArr m)) m.
  Proof. intros P r. exact (pushS_pullS (getASLP m) P r (proj1 (proj2_sig m))). Qed.

  Lemma aslpStArr_arrASLPSt (g : ASLPArr S (A * S)) :
    ASLPArr_eq (aslpStArr (arrASLPSt g)) g.
  Proof. intros P r. reflexivity. Qed.

  Definition aslpStPT (m : ASLPSt S A) : MonoPT S (A * S) := aslpMono (aslpStArr m).

  Lemma aslpStPT_get (m : ASLPSt S A) P r : aslpStPT m P r <-> getASLPSt m P r.
  Proof. reflexivity. Qed.

  Lemma ordASLPSt_pt (m n : ASLPSt S A) :
    ordASLPSt m n <-> pt_le (aslpStPT m) (aslpStPT n).
  Proof. exact (pullS_le _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.

  Lemma eq1_ASLPSt_pt (m n : ASLPSt S A) : eq1 m n <-> pt_eq (aslpStPT m) (aslpStPT n).
  Proof. exact (pullS_eq _ _ (proj1 (proj2_sig m)) (proj1 (proj2_sig n))). Qed.
End SPFlavourCarriers.

(* ================================================================= *)
(** ** The pure level                                                *)
(* ================================================================= *)

(** Without state the fixed index is [unit].  The SP monads are the arrow
    carriers at input [unit] by definition; the WP monads are isomorphic to
    the same carriers at output [unit]. *)

Section PureCarriers.
  Context {A : Type}.

  Lemma ASP_carrier : ASP A = ASPArr unit A.
  Proof. reflexivity. Qed.

  Lemma DSLP_carrier : DSLP A = DSLPArr unit A.
  Proof. reflexivity. Qed.

  Lemma DSP_carrier : DSP A = DSPArr unit A.
  Proof. reflexivity. Qed.

  Lemma ASLP_carrier : ASLP A = ASLPArr unit A.
  Proof. reflexivity. Qed.

  (** *** [AWP A ~ ASPArr A unit] *)

  Definition awpArr (w : AWP A) : ASPArr A unit :=
    exist _ (fun Q _ => getAWP w Q)
      (proj2 (awp_health_at (fun Q (_ : unit) => getAWP w Q)) (fun _ => proj2_sig w)).

  Definition arrAWP (t : ASPArr A unit) : AWP A :=
    exist _ (fun Q => getASPArr t Q tt)
      (proj1 (awp_health_at (getASPArr t)) (proj2_sig t) tt).

  Lemma arrAWP_awpArr (w : AWP A) : eq1 (arrAWP (awpArr w)) w.
  Proof. intro Q. reflexivity. Qed.

  Lemma awpArr_arrAWP (t : ASPArr A unit) : ASPArr_eq (awpArr (arrAWP t)) t.
  Proof. intros Q []. reflexivity. Qed.

  (** *** [DWLP A ~ DSLPArr A unit] *)

  Definition dwlpArr (w : DWLP A) : DSLPArr A unit :=
    exist _ (fun Q _ => getDWLP w Q)
      (proj2 (dwlp_health_at (fun Q (_ : unit) => getDWLP w Q)) (fun _ => proj2_sig w)).

  Definition arrDWLP (t : DSLPArr A unit) : DWLP A :=
    exist _ (fun Q => getDSLPArr t Q tt)
      (proj1 (dwlp_health_at (getDSLPArr t)) (proj2_sig t) tt).

  Lemma arrDWLP_dwlpArr (w : DWLP A) : eq1 (arrDWLP (dwlpArr w)) w.
  Proof. intro Q. reflexivity. Qed.

  Lemma dwlpArr_arrDWLP (t : DSLPArr A unit) : DSLPArr_eq (dwlpArr (arrDWLP t)) t.
  Proof. intros Q []. reflexivity. Qed.

  (** *** [DWP A ~ DSPArr A unit] *)

  Definition dwpArr (w : DWP A) : DSPArr A unit :=
    exist _ (fun Q _ => getDWP w Q)
      (proj2 (dwp_health_at (fun Q (_ : unit) => getDWP w Q)) (fun _ => proj2_sig w)).

  Definition arrDWP (t : DSPArr A unit) : DWP A :=
    exist _ (fun Q => getDSP t Q tt)
      (proj1 (dwp_health_at (getDSP t)) (proj2_sig t) tt).

  Lemma arrDWP_dwpArr (w : DWP A) : eq1 (arrDWP (dwpArr w)) w.
  Proof. intro Q. reflexivity. Qed.

  Lemma dwpArr_arrDWP (t : DSPArr A unit) : DSPArr_eq (dwpArr (arrDWP t)) t.
  Proof. intros Q []. reflexivity. Qed.

  (** *** [AWLP A ~ ASLPArr A unit] *)

  Definition awlpArr (w : AWLP A) : ASLPArr A unit :=
    exist _ (fun Q _ => getAWLP w Q)
      (proj2 (awlp_health_at (fun Q (_ : unit) => getAWLP w Q)) (fun _ => proj2_sig w)).

  Definition arrAWLP (t : ASLPArr A unit) : AWLP A :=
    exist _ (fun Q => getASLP t Q tt)
      (proj1 (awlp_health_at (getASLP t)) (proj2_sig t) tt).

  Lemma arrAWLP_awlpArr (w : AWLP A) : eq1 (arrAWLP (awlpArr w)) w.
  Proof. intro Q. reflexivity. Qed.

  Lemma awlpArr_arrAWLP (t : ASLPArr A unit) : ASLPArr_eq (awlpArr (arrAWLP t)) t.
  Proof. intros Q []. reflexivity. Qed.
End PureCarriers.

(* ================================================================= *)
(** ** [Contrapositive] pairs the refinements two by two             *)
(* ================================================================= *)

(** [pt_dual] exchanges strictness with termination and disjunctivity with
    conjunctivity ([TransformerTaxonomy.v]), so the contrapositive of an element of
    [ASPArr A B] is in [DSLPArr A B] and conversely, and likewise for
    [DSPArr A B] and [ASLPArr A B], at the same indices.  The halves about
    families are classical. *)

Section Duals.
  Context {A B : Type}.

  Definition dualASPArr (f : ASPArr A B) : DSLPArr A B :=
    exist _ (getPT (pt_dual (aspMono f)))
      (conj (proj2_sig (pt_dual (aspMono f)))
         (conj (pt_dual_terminating (aspMono f) (proj1 (proj2 (proj2_sig f))))
               (pt_dual_conjunctive (aspMono f) (proj2 (proj2 (proj2_sig f)))))).

  Definition dualDSLPArr (f : DSLPArr A B) : ASPArr A B :=
    exist _ (getPT (pt_dual (dslpMono f)))
      (conj (proj2_sig (pt_dual (dslpMono f)))
         (conj (pt_dual_strict (dslpMono f) (proj1 (proj2 (proj2_sig f))))
               (pt_dual_disjunctive (dslpMono f) (proj2 (proj2 (proj2_sig f)))))).

  Definition dualDSPArr (f : DSPArr A B) : ASLPArr A B :=
    exist _ (getPT (pt_dual (dspMono f)))
      (conj (proj2_sig (pt_dual (dspMono f)))
         (conj (pt_dual_terminating (dspMono f) (proj1 (proj2 (proj2_sig f))))
               (pt_dual_disjunctive (dspMono f) (proj2 (proj2 (proj2_sig f)))))).

  Definition dualASLPArr (f : ASLPArr A B) : DSPArr A B :=
    exist _ (getPT (pt_dual (aslpMono f)))
      (conj (proj2_sig (pt_dual (aslpMono f)))
         (conj (pt_dual_strict (aslpMono f) (proj1 (proj2 (proj2_sig f))))
               (pt_dual_conjunctive (aslpMono f) (proj2 (proj2 (proj2_sig f)))))).

  Lemma contra_dualASPArr (f : ASPArr A B) :
    Contrapositive (dslpMono (dualASPArr f)) (aspMono f).
  Proof. intros P b. reflexivity. Qed.

  Lemma contra_dualDSLPArr (f : DSLPArr A B) :
    Contrapositive (aspMono (dualDSLPArr f)) (dslpMono f).
  Proof. intros P b. reflexivity. Qed.

  Lemma contra_dualDSPArr (f : DSPArr A B) :
    Contrapositive (aslpMono (dualDSPArr f)) (dspMono f).
  Proof. intros P b. reflexivity. Qed.

  Lemma contra_dualASLPArr (f : ASLPArr A B) :
    Contrapositive (dspMono (dualASLPArr f)) (aslpMono f).
  Proof. intros P b. reflexivity. Qed.
End Duals.

(* ================================================================= *)
(** ** [GaloisPT] pairs [ASPArr A B] with [DSLPArr B A]              *)
(* ================================================================= *)

(** A left adjoint is strict and disjunctive and a right adjoint terminating
    and conjunctive ([TransformerTaxonomy.v]).  Conversely every element of [ASPArr A B]
    has a right adjoint and every element of [DSLPArr B A] a left one, both
    read off the relation the element denotes.  So [GaloisPT] relates the
    carrier of [ASPSt S] to that of [DWLPSt S], and the carrier of
    [AWPSt S] to that of [DSLPSt S], with a partner for every element on
    either side. *)

Section Adjoints.
  Context {A B : Type}.

  Definition radjASP (f : ASPArr A B) : DSLPArr B A :=
    ofRelDSLPArr (fun b a => aspRel f a b).

  Definition ladjDSLP (g : DSLPArr B A) : ASPArr A B :=
    ofRelASPArr (fun a b => dslpRel g b a).

  Lemma galois_radjASP (f : ASPArr A B) : GaloisPT (aspMono f) (dslpMono (radjASP f)).
  Proof.
    intros P Q. split.
    - intros H a Ha b Hr. apply H. apply get_aspRel. exists a. exact (conj Ha Hr).
    - intros H b Hf. apply get_aspRel in Hf. destruct Hf as [a [Ha Hr]].
      exact (H a Ha b Hr).
  Qed.

  Lemma galois_ladjDSLP (g : DSLPArr B A) : GaloisPT (aspMono (ladjDSLP g)) (dslpMono g).
  Proof.
    intros P Q. split.
    - intros H a Ha. apply get_dslpRel. intros b Hr. apply H. exists a. exact (conj Ha Hr).
    - intros H b [a [Ha Hr]]. exact (proj1 (get_dslpRel g Q a) (H a Ha) b Hr).
  Qed.
End Adjoints.

