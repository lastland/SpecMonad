(** * The taxonomy on the predicate-transformer monads

    The three relations of the taxonomy -- implication, contrapositive,
    Galois connection -- as relations between monads.  No computation and
    no observation appears: an element of a monad is a predicate
    transformer, and the relations are between elements.

    The first part of the file places the carriers of the monads inside the
    monotone arrow carrier, where the three relations are stated once
    ([Arrows/GaloisArr.v]).  The second part states them on the monads.

    They are defined on the two broad monads, in the monads' own terms:

      [WSt S]                      monotone WP transformers
      [SPStMonotone.SPStMon S]     monotone SP transformers

      implication      [impliesWSt] on [WSt S];  [impliesSPSt] on [SPStMon S]
      contrapositive   [contraWSt] on [WSt S];  [contraSPSt] on [SPStMon S]
      Galois           [GaloisSPWP m w]: the SP element is left adjoint to the WP one
                       [GaloisWPSP w m]: the WP element is left adjoint to the SP one

    Each is the corresponding relation of the arrow carrier
    ([Arrows/GaloisArr.v]), read through the carrier isomorphisms of
    the first part ([impliesWSt_pt], [contraWSt_pt], [GaloisSPWP_pt]
    &c.), and has that relation's laws.

    Each is a RELATION BETWEEN MONADS ([Classes/MonadRelation.v]): it holds
    at [ret] and is preserved by [bind].  [SPStMon S] has two structures,
    angelic and demonic, each a monad only up to an inequation
    ([SPPredicateTransformers.v]); the contrapositive exchanges them, and
    each Galois relation pairs one of them with [WSt S].

    Every flavour maps into its broad monad ([toWSt]; [asSPStMon] &c.), and
    [Section Flavours] has the instances between the flavours' own monads,
    one theorem each:

      implication, WP   [MonadRelation_dwp_implies_dwlp] and its converse
                        [MonadRelation_dwlp_implies_dwp]; likewise
                        DWP - AWP, AWP - AWLP, DWLP - AWLP
      implication, SP   [MonadRelation_dsp_implies_asp] and its converse
                        [MonadRelation_asp_implies_dsp]; likewise
                        DSP - DSLP, ASP - ASLP, DSLP - ASLP
      contrapositive    [MonadRelation_contra_awp_dwlp_one] and [_two];
                        likewise DWP - AWLP, ASP - DSLP, DSP - ASLP
      Galois            [MonadRelation_galois_asp_dwlp],
                        [MonadRelation_galois_awp_dslp]

    Between SP flavours, DSP and ASLP are compared through one of their two
    parts ([aspPartArr], [dslpPartArr]; [aspPartAArr], [dslpPartAArr]): the
    ASP part on an edge with ASP, the DSLP part on an edge with DSLP.  [bind]
    does not preserve the pointwise order of DSP or of ASLP
    ([not_OrderedMonad_DSPSt], [not_OrderedMonad_ASLPSt]); it preserves the
    order of a part, which is inclusion of the relations denoted
    ([MonadRelation_rel_incl_state]).  A DSP element is the meet of its parts and
    an ASLP element the join of its ([dsp_meet_parts], [aslp_join_parts]), so
    in the four directions of the taxonomy an instance entails the
    implication between the elements themselves ([dsp_implies_asp_part]
    &c.).  A converse instance relates an element to a part only:
    [MonadRelation_asp_implies_dsp] says that the ASP element implies the ASP
    part of the DSP element.

    In a contrapositive or Galois instance every element of either flavour
    has a partner in the other ([contra_awp_in_dwlp], [galois_asp_in_dwlp]
    &c.), unique by the laws of the relation.

    The relations do not depend on the transformers a monad is built with
    ([Classes/MonadRelation.v]).  On the WP side implication and the
    contrapositive are relations of the base monad [WPure] with itself
    ([MonadRelation_impliesWPure], [MonadRelation_contraWPure]); the ones on
    [WSt S] are their [stateT] lifts ([impliesWSt_lift], [contraWSt_lift]),
    and one more lift gives them on [WStExc S] and between any two flavours
    with state and exceptions ([MonadRelation_impliesWStExc],
    [MonadRelation_implies_WPSubStExc] &c.).  On the SP side an implication
    instance is an inclusion between the relations two arrows denote, stated
    at any indices ([Section PartInclusion]); the arrow transformers only
    change the indices, so the eight instances hold again between the
    state-and-exception monads ([MonadRelation_dsp_implies_asp_exc] &c.).

    Without any transformer the flavours collapse two by two
    ([DSPMonad.v], [ASLPMonad.v]): a DSP element and an ASP element that
    denote one relation are the same transformer, and likewise an ASLP and a
    DSLP element.  "The same transformer" is then a relation between the two
    monads ([MonadRelation_dsp_asp_pure], [MonadRelation_aslp_dslp_pure]).

    Statements marked classical use excluded middle; the others do not.
    Every statement about an ASLP element is classical, because the ASLP
    element of a relation preserves joins only classically; so is every
    statement about the relation or the [bind] of a DSP element, which
    recovers its relation by a classical probe. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions Setoid Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad
  ArrowMonad RelArrowCoherence MonadRelation.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPostArr SPostArr GaloisArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  WPureMonad ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPStBindComparisons.
From Incorrectness.Taxonomy.BaseSpecMonads Require
  SPPredicateTransformers SpecificationMonads.

Import SPPredicateTransformers.SPStMonotone.

Local Notation Monad_SPStMon_angelic := (@AngelicMonotone.Monad__AngelicSPStMon _).
Local Notation Monad_SPStMon_demonic := (@DemonicMonotone.Monad__DemonicSPStMon _).

(* ================================================================= *)
(** * The carriers of the SP and WP monads inside the monotone arrow carrier *)
(* ================================================================= *)

(** [Arrows/GaloisArr.v] states the relations of the taxonomy on
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
    [S], and each homomorphism property of [Arrows/SPostArr.v] is the corresponding
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

(** [MonoPT] and its order are the monotone carrier of [GaloisArr.v] and
    its order, under the neutral names. *)

Lemma MonoPT_MonotoneSPost A B : MonoPT A B = GaloisArr.MonotoneSPost A B.
Proof. reflexivity. Qed.

Lemma pt_le_MonotoneSPost_le A B : @pt_le A B = @GaloisArr.MonotoneSPost_le A B.
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

  Import SPPredicateTransformers.SPStMonotone.

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
    conjunctivity ([Arrows/GaloisArr.v]), so the contrapositive of an element of
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
    and conjunctive ([Arrows/GaloisArr.v]).  Conversely every element of [ASPArr A B]
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

(* ================================================================= *)
(** * The three relations, on the monads                             *)
(* ================================================================= *)

(* ================================================================= *)
(** ** The base WP monad [WPure]                                     *)
(* ================================================================= *)

(** Implication and the contrapositive are relations of [WPure] with itself,
    and every WP monad of the development is a stack of monad transformers
    over [WPure] or over one of its flavours.  A monad relation lifts through
    each transformer ([Classes/MonadRelation.v]), so the two relations are
    proved once, here, and every stack inherits them: pointwise in the start
    state under [stateT], at postconditions on [option A] under [optionT]. *)

Section WPureRelations.

  Definition impliesWPure {A} (w1 w2 : WPure A) : Prop :=
    forall Q : A -> Prop, w1 Q -> w2 Q.

  Definition contraWPure {A} (w1 w2 : WPure A) : Prop :=
    forall Q : A -> Prop, w1 Q <-> ~ w2 (fun a => ~ Q a).

  Theorem MonadRelation_impliesWPure :
    @MonadRelation WPure WPure Monad_WPure Monad_WPure (fun A => @impliesWPure A).
  Proof.
    constructor.
    - intros A a Q H. exact H.
    - intros A B m n k k' Hm Hk Q H.
      exact (Hm _ (getWPure_mono m _ _ (fun a Ha => Hk a Q Ha) H)).
  Qed.

  (** Classical. *)
  Theorem MonadRelation_contraWPure :
    @MonadRelation WPure WPure Monad_WPure Monad_WPure (fun A => @contraWPure A).
  Proof.
    constructor.
    - intros A a Q. change (Q a <-> ~ ~ Q a). split.
      + intros H Hn. exact (Hn H).
      + apply NNPP.
    - intros A B m n k k' Hm Hk Q.
      change (getWPure m (fun a => getWPure (k a) Q)
              <-> ~ getWPure n (fun a => getWPure (k' a) (fun b => ~ Q b))).
      split.
      + intros H Hn. apply (proj1 (Hm _) H).
        refine (getWPure_mono n _ _ _ Hn). intros a Ha Hka.
        exact (proj1 (Hk a Q) Hka Ha).
      + intro Hn. apply (proj2 (Hm _)). intro H. apply Hn.
        refine (getWPure_mono n _ _ _ H). intros a Ha.
        apply NNPP. intro Hk'. apply Ha. exact (proj2 (Hk a Q) Hk').
  Qed.

  (** Any two flavours, through their inclusions into [WPure]. *)
  Lemma MonadRelation_implies_toWPure (h1 h2 : WPHealth) :
    @MonadRelation (WPSub h1) (WPSub h2) (Monad_WPSub h1) (Monad_WPSub h2)
      (fun A w1 w2 => impliesWPure (toWPure w1) (toWPure w2)).
  Proof.
    refine (@MonadRelation_pullback (WPSub h1) (WPSub h2)
              (Monad_WPSub h1) (Monad_WPSub h2)
              WPure WPure Monad_WPure Monad_WPure
              (fun A => @impliesWPure A)
              (fun A => @eq1 WPure Eq1_WPure A) (fun A => @eq1 WPure Eq1_WPure A)
              (fun A => @toWPure h1 A) (fun A => @toWPure h2 A)
              _
              (fun A a => toWPure_ret h1 a) (fun A B m k => toWPure_bind h1 m k)
              (fun A a => toWPure_ret h2 a) (fun A B n k => toWPure_bind h2 n k)
              MonadRelation_impliesWPure).
    intros A x x' y y' Ex Ey H Q Hx.
    apply (proj2 (Ey Q)). apply (H Q). exact (proj1 (Ex Q) Hx).
  Qed.

  (** Classical. *)
  Lemma MonadRelation_contra_toWPure (h1 h2 : WPHealth) :
    @MonadRelation (WPSub h1) (WPSub h2) (Monad_WPSub h1) (Monad_WPSub h2)
      (fun A w1 w2 => contraWPure (toWPure w1) (toWPure w2)).
  Proof.
    refine (@MonadRelation_pullback (WPSub h1) (WPSub h2)
              (Monad_WPSub h1) (Monad_WPSub h2)
              WPure WPure Monad_WPure Monad_WPure
              (fun A => @contraWPure A)
              (fun A => @eq1 WPure Eq1_WPure A) (fun A => @eq1 WPure Eq1_WPure A)
              (fun A => @toWPure h1 A) (fun A => @toWPure h2 A)
              _
              (fun A a => toWPure_ret h1 a) (fun A B m k => toWPure_bind h1 m k)
              (fun A a => toWPure_ret h2 a) (fun A B n k => toWPure_bind h2 n k)
              MonadRelation_contraWPure).
    intros A x x' y y' Ex Ey H Q.
    etransitivity; [ exact (Ex Q) |]. etransitivity; [ exact (H Q) |].
    split; intros Hn Hy; apply Hn; apply (Ey (fun a => ~ Q a)); exact Hy.
  Qed.
End WPureRelations.

(* ================================================================= *)
(** ** The WP monad [WSt S]                                          *)
(* ================================================================= *)

Section WPMonad.
  Context {S : Type}.

  (** *** Implication *)

  Definition impliesWSt {A} (w1 w2 : WSt S A) : Prop :=
    forall (Q : A * S -> Prop) s, runStateT w1 s Q -> runStateT w2 s Q.

  Lemma impliesWSt_pt {A} (w1 w2 : WSt S A) :
    impliesWSt w1 w2 <-> pt_le (wstPT w1) (wstPT w2).
  Proof. split; intro H; exact H. Qed.

  (** It is the converse of the refinement [ordWSt]. *)
  Lemma impliesWSt_ordWSt {A} (w1 w2 : WSt S A) : impliesWSt w1 w2 <-> ordWSt w2 w1.
  Proof. split; [ intros H s Q; exact (H Q s) | intros H Q s; exact (H s Q) ]. Qed.

  Theorem OrderedMonad_impliesWSt :
    @OrderedMonad (WSt S) (Monad__WSt S) (Eq1__WSt S) (fun A => @impliesWSt A).
  Proof.
    refine (OrderedMonad_iff (fun A (x y : WSt S A) => ordWSt y x) _
              (fun A x y => iff_sym (impliesWSt_ordWSt x y)) _).
    exact (@OrderedMonad_flip (WSt S) _ _ (Eq1Equivalence__WSt S) _
             (SpecificationMonads.OrderedMonad_WSt S)).
  Qed.

  (** It is the [stateT] lift of implication in [WPure]. *)
  Lemma impliesWSt_lift {A} (w1 w2 : WSt S A) :
    impliesWSt w1 w2 <-> forall s, impliesWPure (runStateT w1 s) (runStateT w2 s).
  Proof. split; [ intros H s Q; exact (H Q s) | intros H Q s; exact (H s Q) ]. Qed.

  Theorem MonadRelation_impliesWSt :
    @MonadRelation (WSt S) (WSt S) (Monad__WSt S) (Monad__WSt S) (fun A => @impliesWSt A).
  Proof.
    exact (MonadRelation_iff _ _ (fun A w1 w2 => iff_sym (impliesWSt_lift w1 w2))
             (MonadRelation_stateT _ S MonadRelation_impliesWPure)).
  Qed.

  (** *** The contrapositive relation *)

  Definition contraWSt {A} (w1 w2 : WSt S A) : Prop :=
    forall (Q : A * S -> Prop) s,
      runStateT w1 s Q <-> ~ runStateT w2 s (fun r => ~ Q r).

  Lemma contraWSt_pt {A} (w1 w2 : WSt S A) :
    contraWSt w1 w2 <-> Contrapositive (wstPT w1) (wstPT w2).
  Proof. split; intro H; exact H. Qed.

  (** Every element has a contrapositive. *)
  Lemma contraWSt_exists {A} (w : WSt S A) : exists w', contraWSt w' w.
  Proof. exists (ptWSt (pt_dual (wstPT w))). intros Q s. reflexivity. Qed.

  Lemma contraWSt_eq1 {A} (w1 w1' w2 w2' : WSt S A) :
    @eq1 (WSt S) (Eq1__WSt S) A w1 w1' -> @eq1 (WSt S) (Eq1__WSt S) A w2 w2' ->
    (contraWSt w1 w2 <-> contraWSt w1' w2').
  Proof.
    intros E1 E2.
    pose proof (proj1 (eq1_WSt_pt w1 w1') E1) as F1.
    pose proof (proj1 (eq1_WSt_pt w2 w2') E2) as F2.
    split.
    - exact (Contrapositive_eq (wstPT w1) (wstPT w1') (wstPT w2) (wstPT w2') F1 F2).
    - exact (Contrapositive_eq (wstPT w1') (wstPT w1) (wstPT w2') (wstPT w2)
               (fun Q s => iff_sym (F1 Q s)) (fun Q s => iff_sym (F2 Q s))).
  Qed.

  (** Classical. *)
  Lemma contraWSt_sym {A} (w1 w2 : WSt S A) : contraWSt w1 w2 -> contraWSt w2 w1.
  Proof. exact (Contrapositive_sym (wstPT w1) (wstPT w2)). Qed.

  (** Each side determines the other. *)
  Lemma contraWSt_functional {A} (w1 w1' w2 : WSt S A) :
    contraWSt w1 w2 -> contraWSt w1' w2 -> @eq1 (WSt S) (Eq1__WSt S) A w1 w1'.
  Proof.
    intros H H'. apply eq1_WSt_pt.
    exact (Contrapositive_functional (wstPT w1) (wstPT w1') (wstPT w2) H H').
  Qed.

  (** Classical. *)
  Lemma contraWSt_injective {A} (w1 w2 w2' : WSt S A) :
    contraWSt w1 w2 -> contraWSt w1 w2' -> @eq1 (WSt S) (Eq1__WSt S) A w2 w2'.
  Proof.
    intros H H'. apply eq1_WSt_pt.
    exact (Contrapositive_injective (wstPT w1) (wstPT w2) (wstPT w2') H H').
  Qed.

  (** It reverses implication. *)
  Lemma contraWSt_antitone {A} (w1 w2 w1' w2' : WSt S A) :
    contraWSt w1 w2 -> contraWSt w1' w2' -> impliesWSt w2 w2' -> impliesWSt w1' w1.
  Proof.
    exact (Contrapositive_antitone (wstPT w1) (wstPT w2) (wstPT w1') (wstPT w2')).
  Qed.

  (** Classical. *)
  Lemma contraWSt_order {A} (w1 w2 w1' w2' : WSt S A) :
    contraWSt w1 w2 -> contraWSt w1' w2' -> (impliesWSt w1 w1' <-> impliesWSt w2' w2).
  Proof.
    intros H H'. split.
    - exact (contraWSt_antitone w2 w1 w2' w1' (contraWSt_sym _ _ H) (contraWSt_sym _ _ H')).
    - exact (contraWSt_antitone w1' w2' w1 w2 H' H).
  Qed.

  (** It exchanges meets and joins. *)
  Definition meetWSt {A} (w1 w2 : WSt S A) : WSt S A :=
    ptWSt (pt_meet (wstPT w1) (wstPT w2)).

  Definition joinWSt {A} (w1 w2 : WSt S A) : WSt S A :=
    ptWSt (pt_join (wstPT w1) (wstPT w2)).

  Lemma meetWSt_get {A} (w1 w2 : WSt S A) Q s :
    runStateT (meetWSt w1 w2) s Q <-> runStateT w1 s Q /\ runStateT w2 s Q.
  Proof. reflexivity. Qed.

  Lemma joinWSt_get {A} (w1 w2 : WSt S A) Q s :
    runStateT (joinWSt w1 w2) s Q <-> runStateT w1 s Q \/ runStateT w2 s Q.
  Proof. reflexivity. Qed.

  Lemma contraWSt_meet_join {A} (w1 w2 w1' w2' : WSt S A) :
    contraWSt w1 w2 -> contraWSt w1' w2' ->
    contraWSt (meetWSt w1 w1') (joinWSt w2 w2').
  Proof.
    exact (Contrapositive_meet_join (wstPT w1) (wstPT w2) (wstPT w1') (wstPT w2')).
  Qed.

  (** Classical. *)
  Lemma contraWSt_join_meet {A} (w1 w2 w1' w2' : WSt S A) :
    contraWSt w1 w2 -> contraWSt w1' w2' ->
    contraWSt (joinWSt w1 w1') (meetWSt w2 w2').
  Proof.
    exact (Contrapositive_join_meet (wstPT w1) (wstPT w2) (wstPT w1') (wstPT w2')).
  Qed.

  (** It is the [stateT] lift of the contrapositive in [WPure], so it holds at
      [ret] and is preserved by [bind].  Classical. *)
  Lemma contraWSt_lift {A} (w1 w2 : WSt S A) :
    contraWSt w1 w2 <-> forall s, contraWPure (runStateT w1 s) (runStateT w2 s).
  Proof. split; [ intros H s Q; exact (H Q s) | intros H Q s; exact (H s Q) ]. Qed.

  Theorem MonadRelation_contraWSt :
    @MonadRelation (WSt S) (WSt S) (Monad__WSt S) (Monad__WSt S) (fun A => @contraWSt A).
  Proof.
    exact (MonadRelation_iff _ _ (fun A w1 w2 => iff_sym (contraWSt_lift w1 w2))
             (MonadRelation_stateT _ S MonadRelation_contraWPure)).
  Qed.
End WPMonad.

(* ================================================================= *)
(** ** The WP monad [WStExc S]                                       *)
(* ================================================================= *)

(** One transformer further: [WStExc S] is [stateT S (optionT WPure)], and
    the two relations are the lifts of the base ones through both
    transformers.  Postconditions are on [option (A * S)].  The same holds
    for any pair of flavours, whose state-and-exception monads are
    [stateT S (optionT (WPSub h))]. *)

Section WPExcMonad.
  Context {S : Type}.

  Definition impliesWStExc {A} (w1 w2 : WStExc S A) : Prop :=
    forall (Q : option (A * S) -> Prop) s,
      unOptionT (runStateT w1 s) Q -> unOptionT (runStateT w2 s) Q.

  Definition contraWStExc {A} (w1 w2 : WStExc S A) : Prop :=
    forall (Q : option (A * S) -> Prop) s,
      unOptionT (runStateT w1 s) Q <-> ~ unOptionT (runStateT w2 s) (fun r => ~ Q r).

  Theorem MonadRelation_impliesWStExc :
    @MonadRelation (WStExc S) (WStExc S) (Monad__WStExc S) (Monad__WStExc S)
      (fun A => @impliesWStExc A).
  Proof.
    refine (MonadRelation_iff _ _ _
              (MonadRelation_stateT _ S (MonadRelation_optionT _ MonadRelation_impliesWPure))).
    intros A w1 w2. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ].
  Qed.

  (** Classical. *)
  Theorem MonadRelation_contraWStExc :
    @MonadRelation (WStExc S) (WStExc S) (Monad__WStExc S) (Monad__WStExc S)
      (fun A => @contraWStExc A).
  Proof.
    refine (MonadRelation_iff _ _ _
              (MonadRelation_stateT _ S (MonadRelation_optionT _ MonadRelation_contraWPure))).
    intros A w1 w2. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ].
  Qed.

  Theorem MonadRelation_implies_WPSubStExc (h1 h2 : WPHealth) :
    @MonadRelation (stateT S (optionT (WPSub h1))) (stateT S (optionT (WPSub h2)))
      (@Monad_stateT S _ (@Monad_optionT _ (Monad_WPSub h1)))
      (@Monad_stateT S _ (@Monad_optionT _ (Monad_WPSub h2)))
      (fun A m n => forall s,
         impliesWPure (toWPure (unOptionT (runStateT m s)))
                      (toWPure (unOptionT (runStateT n s)))).
  Proof.
    exact (MonadRelation_stateT _ S
             (MonadRelation_optionT _ (MonadRelation_implies_toWPure h1 h2))).
  Qed.

  (** Classical. *)
  Theorem MonadRelation_contra_WPSubStExc (h1 h2 : WPHealth) :
    @MonadRelation (stateT S (optionT (WPSub h1))) (stateT S (optionT (WPSub h2)))
      (@Monad_stateT S _ (@Monad_optionT _ (Monad_WPSub h1)))
      (@Monad_stateT S _ (@Monad_optionT _ (Monad_WPSub h2)))
      (fun A m n => forall s,
         contraWPure (toWPure (unOptionT (runStateT m s)))
                     (toWPure (unOptionT (runStateT n s)))).
  Proof.
    exact (MonadRelation_stateT _ S
             (MonadRelation_optionT _ (MonadRelation_contra_toWPure h1 h2))).
  Qed.
End WPExcMonad.

(* ================================================================= *)
(** ** The SP monad [SPStMon S]                                      *)
(* ================================================================= *)

Section SPMonad.
  Context {S : Type}.

  (** *** The two structures *)

  (** *** Implication *)

  (** The pointwise order [ordSPStMon] of [SPPredicateTransformers.v]. *)
  Definition impliesSPSt {A} (m n : SPStMon S A) : Prop :=
    forall (P : S -> Prop) r, proj1_sig m P r -> proj1_sig n P r.

  Lemma impliesSPSt_pt {A} (m n : SPStMon S A) :
    impliesSPSt m n <-> pt_le (spstPT m) (spstPT n).
  Proof. split; intro H; exact H. Qed.

  Lemma impliesSPSt_ord {A} (m n : SPStMon S A) : impliesSPSt m n <-> m ≦ n.
  Proof. split; intro H; exact H. Qed.

  (** It is compatible with each structure. *)
  Theorem MonadRelation_impliesSPSt_angelic :
    @MonadRelation (SPStMon S) (SPStMon S) Monad_SPStMon_angelic Monad_SPStMon_angelic
      (fun A => @impliesSPSt A).
  Proof.
    constructor.
    - intros A a P r H. exact H.
    - intros A B m n k k'. exact (AngelicMonotone.bind_monotone m n k k').
  Qed.

  Theorem MonadRelation_impliesSPSt_demonic :
    @MonadRelation (SPStMon S) (SPStMon S) Monad_SPStMon_demonic Monad_SPStMon_demonic
      (fun A => @impliesSPSt A).
  Proof.
    constructor.
    - intros A a P r H. exact H.
    - intros A B m n k k'. exact (DemonicMonotone.bind_monotone m n k k').
  Qed.

  (** *** The contrapositive relation *)

  Definition contraSPSt {A} (m1 m2 : SPStMon S A) : Prop :=
    forall (P : S -> Prop) r,
      proj1_sig m1 P r <-> ~ proj1_sig m2 (fun s => ~ P s) r.

  Lemma contraSPSt_pt {A} (m1 m2 : SPStMon S A) :
    contraSPSt m1 m2 <-> Contrapositive (spstPT m1) (spstPT m2).
  Proof. split; intro H; exact H. Qed.

  (** Every element has a contrapositive. *)
  Lemma contraSPSt_exists {A} (m : SPStMon S A) : exists m', contraSPSt m' m.
  Proof. exists (ptSPSt (pt_dual (spstPT m))). intros P r. reflexivity. Qed.

  Lemma contraSPSt_equiv {A} (m1 m1' m2 m2' : SPStMon S A) :
    m1 ≈ m1' -> m2 ≈ m2' -> (contraSPSt m1 m2 <-> contraSPSt m1' m2').
  Proof.
    intros [E1 E1'] [E2 E2']. split.
    - exact (Contrapositive_eq (spstPT m1) (spstPT m1') (spstPT m2) (spstPT m2')
               (fun P r => conj (E1 P r) (E1' P r)) (fun P r => conj (E2 P r) (E2' P r))).
    - exact (Contrapositive_eq (spstPT m1') (spstPT m1) (spstPT m2') (spstPT m2)
               (fun P r => conj (E1' P r) (E1 P r)) (fun P r => conj (E2' P r) (E2 P r))).
  Qed.

  (** Classical. *)
  Lemma contraSPSt_sym {A} (m1 m2 : SPStMon S A) : contraSPSt m1 m2 -> contraSPSt m2 m1.
  Proof. exact (Contrapositive_sym (spstPT m1) (spstPT m2)). Qed.

  (** Each side determines the other. *)
  Lemma contraSPSt_functional {A} (m1 m1' m2 : SPStMon S A) :
    contraSPSt m1 m2 -> contraSPSt m1' m2 -> m1 ≈ m1'.
  Proof.
    intros H H'.
    pose proof (Contrapositive_functional (spstPT m1) (spstPT m1') (spstPT m2) H H') as E.
    split; intros P r; apply E.
  Qed.

  (** Classical. *)
  Lemma contraSPSt_injective {A} (m1 m2 m2' : SPStMon S A) :
    contraSPSt m1 m2 -> contraSPSt m1 m2' -> m2 ≈ m2'.
  Proof.
    intros H H'.
    pose proof (Contrapositive_injective (spstPT m1) (spstPT m2) (spstPT m2') H H') as E.
    split; intros P r; apply E.
  Qed.

  (** It reverses implication. *)
  Lemma contraSPSt_antitone {A} (m1 m2 m1' m2' : SPStMon S A) :
    contraSPSt m1 m2 -> contraSPSt m1' m2' -> impliesSPSt m2 m2' -> impliesSPSt m1' m1.
  Proof.
    exact (Contrapositive_antitone (spstPT m1) (spstPT m2) (spstPT m1') (spstPT m2')).
  Qed.

  (** Classical. *)
  Lemma contraSPSt_order {A} (m1 m2 m1' m2' : SPStMon S A) :
    contraSPSt m1 m2 -> contraSPSt m1' m2' -> (impliesSPSt m1 m1' <-> impliesSPSt m2' m2).
  Proof.
    intros H H'. split.
    - exact (contraSPSt_antitone m2 m1 m2' m1' (contraSPSt_sym _ _ H) (contraSPSt_sym _ _ H')).
    - exact (contraSPSt_antitone m1' m2' m1 m2 H' H).
  Qed.

  (** It exchanges meets and joins. *)
  Definition meetSPSt {A} (m1 m2 : SPStMon S A) : SPStMon S A :=
    ptSPSt (pt_meet (spstPT m1) (spstPT m2)).

  Definition joinSPSt {A} (m1 m2 : SPStMon S A) : SPStMon S A :=
    ptSPSt (pt_join (spstPT m1) (spstPT m2)).

  Lemma meetSPSt_get {A} (m1 m2 : SPStMon S A) P r :
    proj1_sig (meetSPSt m1 m2) P r <-> proj1_sig m1 P r /\ proj1_sig m2 P r.
  Proof. reflexivity. Qed.

  Lemma joinSPSt_get {A} (m1 m2 : SPStMon S A) P r :
    proj1_sig (joinSPSt m1 m2) P r <-> proj1_sig m1 P r \/ proj1_sig m2 P r.
  Proof. reflexivity. Qed.

  Lemma contraSPSt_meet_join {A} (m1 m2 m1' m2' : SPStMon S A) :
    contraSPSt m1 m2 -> contraSPSt m1' m2' ->
    contraSPSt (meetSPSt m1 m1') (joinSPSt m2 m2').
  Proof.
    exact (Contrapositive_meet_join (spstPT m1) (spstPT m2) (spstPT m1') (spstPT m2')).
  Qed.

  (** Classical. *)
  Lemma contraSPSt_join_meet {A} (m1 m2 m1' m2' : SPStMon S A) :
    contraSPSt m1 m2 -> contraSPSt m1' m2' ->
    contraSPSt (joinSPSt m1 m1') (meetSPSt m2 m2').
  Proof.
    exact (Contrapositive_join_meet (spstPT m1) (spstPT m2) (spstPT m1') (spstPT m2')).
  Qed.

  (** A contrapositive pair denotes one relation: the left element at a
      singleton is the right element's test at that state.  Classical. *)
  Lemma contraSPSt_singleton {A} (m1 m2 : SPStMon S A) si r :
    contraSPSt m1 m2 ->
    (proj1_sig m1 (fun s => s = si) r <-> forall P, proj1_sig m2 P r -> P si).
  Proof.
    intro H. split.
    - intros H1 P H2. apply NNPP. intro Hn. apply (proj1 (H _ r) H1).
      refine (proj2_sig m2 _ _ r _ H2). intros s Hs Heq. subst s. exact (Hn Hs).
    - intro Hall. apply (proj2 (H _ r)). intro H2. exact (Hall _ H2 eq_refl).
  Qed.

  (** It exchanges the angelic and the demonic structure: classical. *)
  Lemma contraSPSt_ret {A} (a : A) :
    contraSPSt (AngelicMonotone.retP a) (DemonicMonotone.retP (S := S) a).
  Proof.
    intros P r. cbn. split.
    - intros [Hp Ha] H. exact (H Ha Hp).
    - intro H. apply NNPP. intro Hn. apply H. intros Ha Hp. apply Hn. exact (conj Hp Ha).
  Qed.

  Lemma contraSPSt_bind {A B} (m1 m2 : SPStMon S A) (k1 k2 : A -> SPStMon S B) :
    contraSPSt m1 m2 -> (forall a, contraSPSt (k1 a) (k2 a)) ->
    contraSPSt (AngelicMonotone.bindP m1 k1) (DemonicMonotone.bindP m2 k2).
  Proof.
    intros Hm Hk P r. cbn. split.
    - intros [a [si [H1 Hk1]]] Hall.
      apply (proj1 (Hm P (a, si)) H1). apply Hall.
      exact (proj1 (contraSPSt_singleton (k1 a) (k2 a) si r (Hk a)) Hk1).
    - intro Hn. apply NNPP. intro Hne. apply Hn. intros a si Htest.
      apply NNPP. intro H2. apply Hne. exists a, si. split.
      + apply (proj2 (Hm P (a, si))). exact H2.
      + exact (proj2 (contraSPSt_singleton (k1 a) (k2 a) si r (Hk a)) Htest).
  Qed.

  Theorem MonadRelation_contraSPSt :
    @MonadRelation (SPStMon S) (SPStMon S) Monad_SPStMon_angelic Monad_SPStMon_demonic
      (fun A => @contraSPSt A).
  Proof. constructor; [ exact (@contraSPSt_ret) | exact (@contraSPSt_bind) ]. Qed.
End SPMonad.

(* ================================================================= *)
(** ** Galois relations between the two monads                       *)
(* ================================================================= *)

Section GaloisMonads.
  Context {S : Type}.

  Definition GaloisSPWP {A} (m : SPStMon S A) (w : WSt S A) : Prop :=
    forall (P : S -> Prop) (Q : A * S -> Prop),
      (forall r, proj1_sig m P r -> Q r) <-> (forall s, P s -> runStateT w s Q).

  Definition GaloisWPSP {A} (w : WSt S A) (m : SPStMon S A) : Prop :=
    forall (Q : A * S -> Prop) (P : S -> Prop),
      (forall s, runStateT w s Q -> P s) <-> (forall r, Q r -> proj1_sig m P r).

  Lemma GaloisSPWP_pt {A} (m : SPStMon S A) (w : WSt S A) :
    GaloisSPWP m w <-> GaloisPT (spstPT m) (wstPT w).
  Proof. split; intro H; exact H. Qed.

  Lemma GaloisWPSP_pt {A} (w : WSt S A) (m : SPStMon S A) :
    GaloisWPSP w m <-> GaloisPT (wstPT w) (spstPT m).
  Proof. split; intro H; exact H. Qed.

  Lemma GaloisSPWP_equiv {A} (m m' : SPStMon S A) (w w' : WSt S A) :
    m ≈ m' -> @eq1 (WSt S) (Eq1__WSt S) A w w' -> (GaloisSPWP m w <-> GaloisSPWP m' w').
  Proof.
    intros [E E'] Ew. pose proof (proj1 (eq1_WSt_pt w w') Ew) as F. split.
    - exact (GaloisPT_eq (spstPT m) (spstPT m') (wstPT w) (wstPT w')
               (fun P r => conj (E P r) (E' P r)) F).
    - exact (GaloisPT_eq (spstPT m') (spstPT m) (wstPT w') (wstPT w)
               (fun P r => conj (E' P r) (E P r)) (fun Q s => iff_sym (F Q s))).
  Qed.

  Lemma GaloisWPSP_equiv {A} (w w' : WSt S A) (m m' : SPStMon S A) :
    @eq1 (WSt S) (Eq1__WSt S) A w w' -> m ≈ m' -> (GaloisWPSP w m <-> GaloisWPSP w' m').
  Proof.
    intros Ew [E E']. pose proof (proj1 (eq1_WSt_pt w w') Ew) as F. split.
    - exact (GaloisPT_eq (wstPT w) (wstPT w') (spstPT m) (spstPT m')
               F (fun P r => conj (E P r) (E' P r))).
    - exact (GaloisPT_eq (wstPT w') (wstPT w) (spstPT m') (spstPT m)
               (fun Q s => iff_sym (F Q s)) (fun P r => conj (E' P r) (E P r))).
  Qed.

  (** Each side determines the other. *)
  Lemma GaloisSPWP_right_unique {A} (m : SPStMon S A) (w1 w2 : WSt S A) :
    GaloisSPWP m w1 -> GaloisSPWP m w2 -> @eq1 (WSt S) (Eq1__WSt S) A w1 w2.
  Proof.
    intros G1 G2. apply eq1_WSt_pt.
    exact (GaloisPT_right_unique (spstPT m) (wstPT w1) (wstPT w2) G1 G2).
  Qed.

  Lemma GaloisSPWP_left_unique {A} (m1 m2 : SPStMon S A) (w : WSt S A) :
    GaloisSPWP m1 w -> GaloisSPWP m2 w -> m1 ≈ m2.
  Proof.
    intros G1 G2.
    pose proof (GaloisPT_left_unique (spstPT m1) (spstPT m2) (wstPT w) G1 G2) as E.
    split; intros P r; apply E.
  Qed.

  Lemma GaloisWPSP_right_unique {A} (w : WSt S A) (m1 m2 : SPStMon S A) :
    GaloisWPSP w m1 -> GaloisWPSP w m2 -> m1 ≈ m2.
  Proof.
    intros G1 G2.
    pose proof (GaloisPT_right_unique (wstPT w) (spstPT m1) (spstPT m2) G1 G2) as E.
    split; intros P r; apply E.
  Qed.

  Lemma GaloisWPSP_left_unique {A} (w1 w2 : WSt S A) (m : SPStMon S A) :
    GaloisWPSP w1 m -> GaloisWPSP w2 m -> @eq1 (WSt S) (Eq1__WSt S) A w1 w2.
  Proof.
    intros G1 G2. apply eq1_WSt_pt.
    exact (GaloisPT_left_unique (wstPT w1) (wstPT w2) (spstPT m) G1 G2).
  Qed.

  (** Passing to the adjoint reverses implication. *)
  Lemma GaloisSPWP_order {A} (m1 m2 : SPStMon S A) (w1 w2 : WSt S A) :
    GaloisSPWP m1 w1 -> GaloisSPWP m2 w2 -> (impliesSPSt m1 m2 <-> impliesWSt w2 w1).
  Proof.
    exact (GaloisPT_antitone (spstPT m1) (spstPT m2) (wstPT w1) (wstPT w2)).
  Qed.

  Lemma GaloisWPSP_order {A} (w1 w2 : WSt S A) (m1 m2 : SPStMon S A) :
    GaloisWPSP w1 m1 -> GaloisWPSP w2 m2 -> (impliesWSt w1 w2 <-> impliesSPSt m2 m1).
  Proof.
    exact (GaloisPT_antitone (wstPT w1) (wstPT w2) (spstPT m1) (spstPT m2)).
  Qed.

  (** [GaloisSPWP] pairs the angelic structure with [WSt S]. *)
  Lemma GaloisSPWP_ret {A} (a : A) : GaloisSPWP (AngelicMonotone.retP a) (ret a : WSt S A).
  Proof.
    intros P Q. cbn. split.
    - intros H s Hp. exact (H (a, s) (conj Hp eq_refl)).
    - intros H [a' s] [Hp Ha]. cbn in Hp, Ha. subst a'. exact (H s Hp).
  Qed.

  Lemma GaloisSPWP_bind {A B} (m : SPStMon S A) (w : WSt S A)
    (k : A -> SPStMon S B) (k' : A -> WSt S B) :
    GaloisSPWP m w -> (forall a, GaloisSPWP (k a) (k' a)) ->
    GaloisSPWP (AngelicMonotone.bindP m k) (bind w k').
  Proof.
    intros Gm Gk.
    change (GaloisPT (spstPT m) (wstPT w)) in Gm.
    change (forall a, GaloisPT (spstPT (k a)) (wstPT (k' a))) in Gk.
    change (GaloisPT (spstPT (AngelicMonotone.bindP m k)) (wstPT (bind w k'))).
    intros P Q. split.
    - intros H s Hp. apply wstPT_bind. revert s Hp. apply (proj1 (Gm P _)).
      intros [a si] Hm. cbn [fst snd]. refine (proj1 (Gk a (fun s => s = si) Q) _ si eq_refl).
      intros r Hr. apply H. exists a, si. exact (conj Hm Hr).
    - intros H r [a [si [Hm Hr]]].
      refine (proj2 (Gk a (fun s => s = si) Q) _ r Hr). intros s ->.
      refine (proj2 (Gm P (fun x => wstPT (k' (fst x)) Q (snd x))) _ (a, si) Hm).
      intros s Hp. apply wstPT_bind. exact (H s Hp).
  Qed.

  Theorem MonadRelation_GaloisSPWP :
    @MonadRelation (SPStMon S) (WSt S) Monad_SPStMon_angelic (Monad__WSt S)
      (fun A => @GaloisSPWP A).
  Proof. constructor; [ exact (@GaloisSPWP_ret) | exact (@GaloisSPWP_bind) ]. Qed.

  (** [GaloisWPSP] pairs [WSt S] with the demonic structure. *)
  Lemma GaloisWPSP_ret {A} (a : A) :
    GaloisWPSP (ret a : WSt S A) (DemonicMonotone.retP a).
  Proof.
    intros Q P. cbn. split.
    - intros H [a' s] Hq Ha. cbn in Ha. subst a'. exact (H s Hq).
    - intros H s Hq. exact (H (a, s) Hq eq_refl).
  Qed.

  (** A left adjoint in [WSt S] is determined at singletons, where it is the
      test of its right adjoint. *)
  Lemma GaloisWPSP_singleton {A} (w : WSt S A) (m : SPStMon S A) r si :
    GaloisWPSP w m ->
    (runStateT w si (fun x => x = r) <-> forall P, proj1_sig m P r -> P si).
  Proof.
    intro G. change (GaloisPT (wstPT w) (spstPT m)) in G. split.
    - intros Hw P Hm. refine (proj2 (G (fun x => x = r) P) _ si Hw). intros x ->. exact Hm.
    - intro Hall. apply (Hall (fun s => wstPT w (fun x => x = r) s)).
      refine (proj1 (G (fun x => x = r) _) _ r eq_refl). intros s Hs. exact Hs.
  Qed.

  Lemma GaloisWPSP_join {A} (w : WSt S A) (m : SPStMon S A) Q si :
    GaloisWPSP w m ->
    (runStateT w si Q <-> exists r, Q r /\ runStateT w si (fun x => x = r)).
  Proof.
    intro G. change (GaloisPT (wstPT w) (spstPT m)) in G. split.
    - revert si. apply (proj2 (G Q (fun s => exists r, Q r /\ wstPT w (fun x => x = r) s))).
      intros r Hq. refine (proj1 (G (fun x => x = r) _) _ r eq_refl).
      intros s Hs. exists r. exact (conj Hq Hs).
    - intros [r [Hq Hw]]. refine (getPT_mono (wstPT w) _ _ si _ Hw). intros x ->. exact Hq.
  Qed.

  Lemma GaloisWPSP_bind {A B} (w : WSt S A) (m : SPStMon S A)
    (k' : A -> WSt S B) (k : A -> SPStMon S B) :
    GaloisWPSP w m -> (forall a, GaloisWPSP (k' a) (k a)) ->
    GaloisWPSP (bind w k') (DemonicMonotone.bindP m k).
  Proof.
    intros Gw Gk.
    pose proof (fun a => GaloisWPSP_join (k' a) (k a)) as Hjoin.
    pose proof (fun a => GaloisWPSP_singleton (k' a) (k a)) as Hsing.
    change (GaloisPT (wstPT w) (spstPT m)) in Gw.
    change (GaloisPT (wstPT (bind w k')) (spstPT (DemonicMonotone.bindP m k))).
    intros Q P. split.
    - intros H r Hq a si Htest.
      refine (proj1 (Gw (fun x => wstPT (k' (fst x)) Q (snd x)) P) _ (a, si) _).
      + intros s Hs. apply H. apply wstPT_bind. exact Hs.
      + cbn [fst snd]. apply (proj2 (Hjoin a Q si (Gk a))).
        exists r. split; [ exact Hq |].
        exact (proj2 (Hsing a r si (Gk a)) Htest).
    - intros H s Hw. apply wstPT_bind in Hw. revert s Hw.
      apply (proj2 (Gw (fun x => wstPT (k' (fst x)) Q (snd x)) P)).
      intros [a si] Hk. cbn [fst snd] in Hk.
      destruct (proj1 (Hjoin a Q si (Gk a)) Hk) as [r [Hq Hr]].
      refine (H r Hq a si _).
      exact (proj1 (Hsing a r si (Gk a)) Hr).
  Qed.

  Theorem MonadRelation_GaloisWPSP :
    @MonadRelation (WSt S) (SPStMon S) (Monad__WSt S) Monad_SPStMon_demonic
      (fun A => @GaloisWPSP A).
  Proof. constructor; [ exact (@GaloisWPSP_ret) | exact (@GaloisWPSP_bind) ]. Qed.

  (** The contrapositives of a pair of one kind form a pair of the other.
      Classical. *)
  Lemma GaloisSPWP_contra {A} (m m' : SPStMon S A) (w w' : WSt S A) :
    GaloisSPWP m w -> contraSPSt m' m -> contraWSt w' w -> GaloisWPSP w' m'.
  Proof.
    intros G Hm Hw.
    exact (GaloisPT_eq (pt_dual (wstPT w)) (wstPT w') (pt_dual (spstPT m)) (spstPT m')
             (fun Q s => iff_sym (Hw Q s)) (fun P r => iff_sym (Hm P r))
             (GaloisPT_dual (spstPT m) (wstPT w) G)).
  Qed.

  Lemma GaloisWPSP_contra {A} (w w' : WSt S A) (m m' : SPStMon S A) :
    GaloisWPSP w m -> contraWSt w' w -> contraSPSt m' m -> GaloisSPWP m' w'.
  Proof.
    intros G Hw Hm.
    exact (GaloisPT_eq (pt_dual (spstPT m)) (spstPT m') (pt_dual (wstPT w)) (wstPT w')
             (fun P r => iff_sym (Hm P r)) (fun Q s => iff_sym (Hw Q s))
             (GaloisPT_dual (wstPT w) (spstPT m) G)).
  Qed.

  (** [GaloisSPWP] and [GaloisWPSP] are the adjointness relations [Ladj] and
      [Radj] of [SPPredicateTransformers.v]. *)
  Lemma Ladj_GaloisSPWP {A} (m : SPStMon S A) (w : WSt S A) :
    AngelicMonotone.Ladj m w <-> GaloisSPWP m w.
  Proof. split; intro H; exact H. Qed.

  Lemma Radj_GaloisWPSP {A} (m : SPStMon S A) (w : WSt S A) :
    DemonicMonotone.Radj m w <-> GaloisWPSP w m.
  Proof. split; [ intros H Q P; exact (H P Q) | intros H P Q; exact (H Q P) ]. Qed.

End GaloisMonads.

(* ================================================================= *)
(** ** The flavours inside the broad monads                          *)
(* ================================================================= *)

(** The WP flavours map into [WSt S] by [toWSt], a monad morphism
    ([WPureMonad.v]).  The SP flavours map into [SPStMon S] by their
    readings at a shared precondition: [asSPStMon] and [asDSLPStMon] of
    [SPStBindComparisons.v], and [asDSPStMon] and [asASLPStMon] here.  ASP's
    monad structure is the angelic one and DSLP's the demonic one.  DSP's
    [bind] is the meet of an angelic and a demonic [bind], and ASLP's their
    join ([bindDSPSt_SPStMonotone], [bindASLPSt_SPStMonotone]). *)

Section SPInclusions.
  Context {S : Type}.

  Definition asDSPStMon {A} (m : DSPSt S A) : SPStMon S A := ptSPSt (dspStPT m).
  Definition asASLPStMon {A} (m : ASLPSt S A) : SPStMon S A := ptSPSt (aslpStPT m).

  Lemma asSPStMon_ret {A} (a : A) : asSPStMon (ret a : ASPSt S A) ≈ AngelicMonotone.retP a.
  Proof.
    split; intros P r H.
    - destruct (proj1 (getASPSt_ret S a P r) H) as [s [Hp ->]]. exact (conj Hp eq_refl).
    - destruct r as [a' s]. destruct H as [Hp Ha]. cbn in Hp, Ha. subst a'.
      apply (getASPSt_ret S a P (a, s)). exists s. exact (conj Hp eq_refl).
  Qed.

  Lemma asSPStMon_bind {A B} (m : ASPSt S A) (k : A -> ASPSt S B) :
    asSPStMon (bind m k) ≈ AngelicMonotone.bindP (asSPStMon m) (fun a => asSPStMon (k a)).
  Proof.
    split; intros P r H.
    - exact (proj1 (getASPSt_bind S m k P r) H).
    - exact (proj2 (getASPSt_bind S m k P r) H).
  Qed.

  Lemma asDSLPStMon_ret {A} (a : A) :
    asDSLPStMon (ret a : DSLPSt S A) ≈ DemonicMonotone.retP a.
  Proof.
    split; intros P r H.
    - destruct r as [a' s]. intro Ha. cbn in Ha. subst a'.
      exact (proj1 (getDSLPSt_ret S a P (a, s)) H s eq_refl).
    - apply (getDSLPSt_ret S a P r). intros s ->. exact (H eq_refl).
  Qed.

  Lemma asDSLPStMon_bind {A B} (m : DSLPSt S A) (k : A -> DSLPSt S B) :
    asDSLPStMon (bind m k) ≈ DemonicMonotone.bindP (asDSLPStMon m) (fun a => asDSLPStMon (k a)).
  Proof.
    split; intros P r H.
    - exact (proj1 (bindDSLPSt_demonic_formula_spec m k P r) H).
    - exact (proj2 (bindDSLPSt_demonic_formula_spec m k P r) H).
  Qed.

  (** The inclusions reflect the orders and the equivalences. *)
  Lemma ordASPSt_SPSt {A} (m n : ASPSt S A) :
    ordASPSt m n <-> impliesSPSt (asSPStMon m) (asSPStMon n).
  Proof. apply ordASPSt_pt. Qed.

  Lemma ordDSLPSt_SPSt {A} (m n : DSLPSt S A) :
    ordDSLPSt m n <-> impliesSPSt (asDSLPStMon m) (asDSLPStMon n).
  Proof. apply ordDSLPSt_pt. Qed.

  Lemma ordDSPSt_SPSt {A} (m n : DSPSt S A) :
    ordDSPSt m n <-> impliesSPSt (asDSPStMon m) (asDSPStMon n).
  Proof. apply ordDSPSt_pt. Qed.

  Lemma ordASLPSt_SPSt {A} (m n : ASLPSt S A) :
    ordASLPSt m n <-> impliesSPSt (asASLPStMon m) (asASLPStMon n).
  Proof. apply ordASLPSt_pt. Qed.

  Lemma eq1_ASPSt_SPSt {A} (m n : ASPSt S A) : eq1 m n <-> asSPStMon m ≈ asSPStMon n.
  Proof.
    split.
    - intro H. pose proof (proj1 (eq1_ASPSt_pt m n) H) as E. split; intros P r; apply E.
    - intros [E E']. apply eq1_ASPSt_pt. intros P r. exact (conj (E P r) (E' P r)).
  Qed.

  Lemma eq1_DSLPSt_SPSt {A} (m n : DSLPSt S A) : eq1 m n <-> asDSLPStMon m ≈ asDSLPStMon n.
  Proof.
    split.
    - intro H. pose proof (proj1 (eq1_DSLPSt_pt m n) H) as E. split; intros P r; apply E.
    - intros [E E']. apply eq1_DSLPSt_pt. intros P r. exact (conj (E P r) (E' P r)).
  Qed.

  Lemma eq1_DSPSt_SPSt {A} (m n : DSPSt S A) : eq1 m n <-> asDSPStMon m ≈ asDSPStMon n.
  Proof.
    split.
    - intro H. pose proof (proj1 (eq1_DSPSt_pt m n) H) as E. split; intros P r; apply E.
    - intros [E E']. apply eq1_DSPSt_pt. intros P r. exact (conj (E P r) (E' P r)).
  Qed.

  Lemma eq1_ASLPSt_SPSt {A} (m n : ASLPSt S A) : eq1 m n <-> asASLPStMon m ≈ asASLPStMon n.
  Proof.
    split.
    - intro H. pose proof (proj1 (eq1_ASLPSt_pt m n) H) as E. split; intros P r; apply E.
    - intros [E E']. apply eq1_ASLPSt_pt. intros P r. exact (conj (E P r) (E' P r)).
  Qed.
End SPInclusions.

(* ================================================================= *)
(** ** The parts of DSP and ASLP, at any indices                     *)
(* ================================================================= *)

(** A DSP element has an ASP part and a DSLP part, and so has an ASLP
    element ([Arrows/SPostArr.v]).  Each part denotes the relation of its
    element.  Between ASP elements implication is inclusion of the relations
    denoted, and between DSLP elements the converse inclusion ([aspRel_incl],
    [dslpRel_incl]).  So implication between a part and an element of the
    part's flavour is an inclusion between the relations of the two
    elements.  The indices are arbitrary, so one statement serves every
    stack of arrow transformers. *)

Section PartInclusion.
  Context {X Y : Type}.

  Lemma aspRel_aspPartArr (d : DSPArr X Y) x y :
    aspRel (aspPartArr d) x y <-> dspRel d x y.
  Proof. exact (aspRel_ofRel (dspRel d) x y). Qed.

  Lemma dslpRel_dslpPartArr (d : DSPArr X Y) x y :
    dslpRel (dslpPartArr d) x y <-> dspRel d x y.
  Proof. exact (dslpRel_ofRel (dspRel d) x y). Qed.

  Lemma aspRel_aspPartAArr (l : ASLPArr X Y) x y :
    aspRel (aspPartAArr l) x y <-> aslpRel l x y.
  Proof. exact (aspRel_ofRel (aslpRel l) x y). Qed.

  Lemma dslpRel_dslpPartAArr (l : ASLPArr X Y) x y :
    dslpRel (dslpPartAArr l) x y <-> aslpRel l x y.
  Proof. exact (dslpRel_ofRel (aslpRel l) x y). Qed.

  Lemma dsp_implies_asp_rel (d : DSPArr X Y) (a : ASPArr X Y) :
    (forall P y, getASPArr (aspPartArr d) P y -> getASPArr a P y)
    <-> (forall x y, dspRel d x y -> aspRel a x y).
  Proof.
    etransitivity; [ exact (aspRel_incl (aspPartArr d) a) |].
    split; intros H x y Hr.
    - exact (H x y (proj2 (aspRel_aspPartArr d x y) Hr)).
    - exact (H x y (proj1 (aspRel_aspPartArr d x y) Hr)).
  Qed.

  Lemma asp_implies_dsp_rel (a : ASPArr X Y) (d : DSPArr X Y) :
    (forall P y, getASPArr a P y -> getASPArr (aspPartArr d) P y)
    <-> (forall x y, aspRel a x y -> dspRel d x y).
  Proof.
    etransitivity; [ exact (aspRel_incl a (aspPartArr d)) |].
    split; intros H x y Hr.
    - exact (proj1 (aspRel_aspPartArr d x y) (H x y Hr)).
    - exact (proj2 (aspRel_aspPartArr d x y) (H x y Hr)).
  Qed.

  Lemma dsp_implies_dslp_rel (d : DSPArr X Y) (n : DSLPArr X Y) :
    (forall P y, getDSLPArr (dslpPartArr d) P y -> getDSLPArr n P y)
    <-> (forall x y, dslpRel n x y -> dspRel d x y).
  Proof.
    etransitivity; [ exact (dslpRel_incl (dslpPartArr d) n) |].
    split; intros H x y Hr.
    - exact (proj1 (dslpRel_dslpPartArr d x y) (H x y Hr)).
    - exact (proj2 (dslpRel_dslpPartArr d x y) (H x y Hr)).
  Qed.

  Lemma dslp_implies_dsp_rel (n : DSLPArr X Y) (d : DSPArr X Y) :
    (forall P y, getDSLPArr n P y -> getDSLPArr (dslpPartArr d) P y)
    <-> (forall x y, dspRel d x y -> dslpRel n x y).
  Proof.
    etransitivity; [ exact (dslpRel_incl n (dslpPartArr d)) |].
    split; intros H x y Hr.
    - exact (H x y (proj2 (dslpRel_dslpPartArr d x y) Hr)).
    - exact (H x y (proj1 (dslpRel_dslpPartArr d x y) Hr)).
  Qed.

  Lemma asp_implies_aslp_rel (a : ASPArr X Y) (l : ASLPArr X Y) :
    (forall P y, getASPArr a P y -> getASPArr (aspPartAArr l) P y)
    <-> (forall x y, aspRel a x y -> aslpRel l x y).
  Proof.
    etransitivity; [ exact (aspRel_incl a (aspPartAArr l)) |].
    split; intros H x y Hr.
    - exact (proj1 (aspRel_aspPartAArr l x y) (H x y Hr)).
    - exact (proj2 (aspRel_aspPartAArr l x y) (H x y Hr)).
  Qed.

  Lemma aslp_implies_asp_rel (l : ASLPArr X Y) (a : ASPArr X Y) :
    (forall P y, getASPArr (aspPartAArr l) P y -> getASPArr a P y)
    <-> (forall x y, aslpRel l x y -> aspRel a x y).
  Proof.
    etransitivity; [ exact (aspRel_incl (aspPartAArr l) a) |].
    split; intros H x y Hr.
    - exact (H x y (proj2 (aspRel_aspPartAArr l x y) Hr)).
    - exact (H x y (proj1 (aspRel_aspPartAArr l x y) Hr)).
  Qed.

  Lemma dslp_implies_aslp_rel (n : DSLPArr X Y) (l : ASLPArr X Y) :
    (forall P y, getDSLPArr n P y -> getDSLPArr (dslpPartAArr l) P y)
    <-> (forall x y, aslpRel l x y -> dslpRel n x y).
  Proof.
    etransitivity; [ exact (dslpRel_incl n (dslpPartAArr l)) |].
    split; intros H x y Hr.
    - exact (H x y (proj2 (dslpRel_dslpPartAArr l x y) Hr)).
    - exact (H x y (proj1 (dslpRel_dslpPartAArr l x y) Hr)).
  Qed.

  Lemma aslp_implies_dslp_rel (l : ASLPArr X Y) (n : DSLPArr X Y) :
    (forall P y, getDSLPArr (dslpPartAArr l) P y -> getDSLPArr n P y)
    <-> (forall x y, dslpRel n x y -> aslpRel l x y).
  Proof.
    etransitivity; [ exact (dslpRel_incl (dslpPartAArr l) n) |].
    split; intros H x y Hr.
    - exact (proj1 (dslpRel_dslpPartAArr l x y) (H x y Hr)).
    - exact (proj2 (dslpRel_dslpPartAArr l x y) (H x y Hr)).
  Qed.
End PartInclusion.


(* ================================================================= *)
(** ** The edges between the flavours                                *)
(* ================================================================= *)

(** The instances between the flavours' own monads.  Each is written out
    for its pair of flavours, with the relation of the broad monads applied
    to the two inclusions. *)

Section Flavours.
  Context {S : Type}.

  (* --------------------------------------------------------------- *)
  (** *** Implication between the WP flavours                         *)
  (* --------------------------------------------------------------- *)

  (** Every flavour's [ret] and [bind] are [WSt S]'s, so implication in
      [WSt S] relates any two flavours as monads. *)
  Lemma MonadRelation_implies_toWSt (h1 h2 : WPHealth) :
    @MonadRelation (WPSubSt h1 S) (WPSubSt h2 S) (Monad_WPSubSt h1 S) (Monad_WPSubSt h2 S)
      (fun A w1 w2 => impliesWSt (toWSt w1) (toWSt w2)).
  Proof.
    refine (@MonadRelation_pullback (WPSubSt h1 S) (WPSubSt h2 S)
              (Monad_WPSubSt h1 S) (Monad_WPSubSt h2 S)
              (WSt S) (WSt S) (Monad__WSt S) (Monad__WSt S)
              (fun A => @impliesWSt S A)
              (fun A => @eq1 (WSt S) (Eq1__WSt S) A) (fun A => @eq1 (WSt S) (Eq1__WSt S) A)
              (fun A => @toWSt h1 S A) (fun A => @toWSt h2 S A)
              _
              (fun A a => toWSt_ret h1 S a) (fun A B m k => toWSt_bind h1 S m k)
              (fun A a => toWSt_ret h2 S a) (fun A B n k => toWSt_bind h2 S n k)
              MonadRelation_impliesWSt).
    intros A x x' y y' Ex Ey H Q s Hx.
    apply (proj2 (Ey s Q)). apply (H Q s). exact (proj1 (Ex s Q) Hx).
  Qed.

  (** The four implications of the taxonomy between WP flavours, each with
      its converse. *)
  Theorem MonadRelation_dwp_implies_dwlp :
    @MonadRelation (DWPSt S) (DWLPSt S) (Monad_DWPSt S) (Monad_DWLPSt S)
      (fun A d l => impliesWSt (toWSt d) (toWSt l)).
  Proof. exact (MonadRelation_implies_toWSt dwp_health dwlp_health). Qed.

  Theorem MonadRelation_dwlp_implies_dwp :
    @MonadRelation (DWLPSt S) (DWPSt S) (Monad_DWLPSt S) (Monad_DWPSt S)
      (fun A l d => impliesWSt (toWSt l) (toWSt d)).
  Proof. exact (MonadRelation_implies_toWSt dwlp_health dwp_health). Qed.

  Theorem MonadRelation_dwp_implies_awp :
    @MonadRelation (DWPSt S) (AWPSt S) (Monad_DWPSt S) (Monad_AWPSt S)
      (fun A d a => impliesWSt (toWSt d) (toWSt a)).
  Proof. exact (MonadRelation_implies_toWSt dwp_health awp_health). Qed.

  Theorem MonadRelation_awp_implies_dwp :
    @MonadRelation (AWPSt S) (DWPSt S) (Monad_AWPSt S) (Monad_DWPSt S)
      (fun A a d => impliesWSt (toWSt a) (toWSt d)).
  Proof. exact (MonadRelation_implies_toWSt awp_health dwp_health). Qed.

  Theorem MonadRelation_awp_implies_awlp :
    @MonadRelation (AWPSt S) (AWLPSt S) (Monad_AWPSt S) (Monad_AWLPSt S)
      (fun A a l => impliesWSt (toWSt a) (toWSt l)).
  Proof. exact (MonadRelation_implies_toWSt awp_health awlp_health). Qed.

  Theorem MonadRelation_awlp_implies_awp :
    @MonadRelation (AWLPSt S) (AWPSt S) (Monad_AWLPSt S) (Monad_AWPSt S)
      (fun A l a => impliesWSt (toWSt l) (toWSt a)).
  Proof. exact (MonadRelation_implies_toWSt awlp_health awp_health). Qed.

  Theorem MonadRelation_dwlp_implies_awlp :
    @MonadRelation (DWLPSt S) (AWLPSt S) (Monad_DWLPSt S) (Monad_AWLPSt S)
      (fun A l l' => impliesWSt (toWSt l) (toWSt l')).
  Proof. exact (MonadRelation_implies_toWSt dwlp_health awlp_health). Qed.

  Theorem MonadRelation_awlp_implies_dwlp :
    @MonadRelation (AWLPSt S) (DWLPSt S) (Monad_AWLPSt S) (Monad_DWLPSt S)
      (fun A l l' => impliesWSt (toWSt l) (toWSt l')).
  Proof. exact (MonadRelation_implies_toWSt awlp_health dwlp_health). Qed.

  (* --------------------------------------------------------------- *)
  (** *** Implication between the SP flavours                         *)
  (* --------------------------------------------------------------- *)

  (** The four SP elements of one relation.  The DSP element is the meet of
      the ASP and the DSLP element, and the ASLP element their join. *)
  Lemma dsp_meet_of {A} (R : S -> A * S -> Prop) :
    asDSPStMon (dspOfRelSt R)
    ≈ meetSPSt (asSPStMon (aspOfRelSt R)) (asDSLPStMon (dslpOfRelSt R)).
  Proof.
    split; intros P r H.
    - destruct (proj1 (getDSPSt_of R P r) H) as [Ha Hd].
      exact (conj (proj2 (getASPSt_of S R P r) Ha) (proj2 (getDSLPSt_of S R P r) Hd)).
    - destruct H as [Ha Hd]. apply (proj2 (getDSPSt_of R P r)).
      exact (conj (proj1 (getASPSt_of S R P r) Ha) (proj1 (getDSLPSt_of S R P r) Hd)).
  Qed.

  Lemma aslp_join_of {A} (R : S -> A * S -> Prop) :
    asASLPStMon (aslpOfRelSt R)
    ≈ joinSPSt (asSPStMon (aspOfRelSt R)) (asDSLPStMon (dslpOfRelSt R)).
  Proof.
    split; intros P r H.
    - destruct (proj1 (getASLPSt_of R P r) H) as [Ha | Hd].
      + left. exact (proj2 (getASPSt_of S R P r) Ha).
      + right. exact (proj2 (getDSLPSt_of S R P r) Hd).
    - apply (proj2 (getASLPSt_of R P r)). destruct H as [Ha | Hd].
      + left. exact (proj1 (getASPSt_of S R P r) Ha).
      + right. exact (proj1 (getDSLPSt_of S R P r) Hd).
  Qed.

  Lemma dsp_implies_asp_of {A} (R : S -> A * S -> Prop) :
    impliesSPSt (asDSPStMon (dspOfRelSt R)) (asSPStMon (aspOfRelSt R)).
  Proof. intros P r H. exact (proj1 (proj1 (dsp_meet_of R) P r H)). Qed.

  Lemma dsp_implies_dslp_of {A} (R : S -> A * S -> Prop) :
    impliesSPSt (asDSPStMon (dspOfRelSt R)) (asDSLPStMon (dslpOfRelSt R)).
  Proof. intros P r H. exact (proj2 (proj1 (dsp_meet_of R) P r H)). Qed.

  Lemma asp_implies_aslp_of {A} (R : S -> A * S -> Prop) :
    impliesSPSt (asSPStMon (aspOfRelSt R)) (asASLPStMon (aslpOfRelSt R)).
  Proof. intros P r H. exact (proj2 (aslp_join_of R) P r (or_introl H)). Qed.

  Lemma dslp_implies_aslp_of {A} (R : S -> A * S -> Prop) :
    impliesSPSt (asDSLPStMon (dslpOfRelSt R)) (asASLPStMon (aslpOfRelSt R)).
  Proof. intros P r H. exact (proj2 (aslp_join_of R) P r (or_intror H)). Qed.

  (** DSP and ASLP are compared with the other flavours through their parts
      ([Arrows/SPostArr.v]).  A DSP element is the meet of
      its two parts, and an ASLP element the join of its two.  Classical. *)
  Lemma dsp_meet_parts {A} (d : DSPSt S A) :
    asDSPStMon d ≈ meetSPSt (asSPStMon (aspPartArr d)) (asDSLPStMon (dslpPartArr d)).
  Proof.
    split; intros P r H.
    - exact (proj1 (dsp_split d (fun p => P (snd p)) r) H).
    - exact (proj2 (dsp_split d (fun p => P (snd p)) r) H).
  Qed.

  Lemma aslp_join_parts {A} (l : ASLPSt S A) :
    asASLPStMon l ≈ joinSPSt (asSPStMon (aspPartAArr l)) (asDSLPStMon (dslpPartAArr l)).
  Proof.
    split; intros P r H.
    - exact (proj1 (aslp_split l (fun p => P (snd p)) r) H).
    - exact (proj2 (aslp_split l (fun p => P (snd p)) r) H).
  Qed.

  (** Between two elements of one flavour, implication in [SPStMon S] is the
      pointwise order of the flavour's own carrier. *)
  Lemma impliesSPSt_asp {A} (m m' : ASPSt S A) :
    impliesSPSt (asSPStMon m) (asSPStMon m')
    <-> (forall P r, getASPArr m P r -> getASPArr m' P r).
  Proof. exact (iff_sym (ordASPSt_get S m m')). Qed.

  Lemma impliesSPSt_dslp {A} (n n' : DSLPSt S A) :
    impliesSPSt (asDSLPStMon n) (asDSLPStMon n')
    <-> (forall P r, getDSLPArr n P r -> getDSLPArr n' P r).
  Proof. exact (iff_sym (ordDSLPSt_get S n n')). Qed.

  (** The four implications of the taxonomy between SP flavours, each with
      its converse.  An ASP-kind edge compares ASP parts and a DSLP-kind edge
      DSLP parts.  Each is an inclusion between the relations the two
      elements denote ([PartInclusion]), and [stateArrT] preserves such an
      inclusion ([MonadRelation_rel_incl_state]).  Classical. *)

  Theorem MonadRelation_dsp_implies_asp :
    @MonadRelation (DSPSt S) (ASPSt S) (Monad_DSPSt S) (Monad_ASPSt S)
      (fun A d a => impliesSPSt (asSPStMon (aspPartArr d)) (asSPStMon a)).
  Proof.
    refine (MonadRelation_iff
              (fun A (d : DSPSt S A) (a : ASPSt S A) => forall p r, dspRel d p r -> aspRel a p r) _
              (fun A d a => iff_sym (iff_trans (impliesSPSt_asp (aspPartArr d) a) (dsp_implies_asp_rel d a))) _).
    exact (MonadRelation_rel_incl_state (arr1 := DSPArr) (arr2 := ASPArr) S unit).
  Qed.

  Theorem MonadRelation_asp_implies_dsp :
    @MonadRelation (ASPSt S) (DSPSt S) (Monad_ASPSt S) (Monad_DSPSt S)
      (fun A a d => impliesSPSt (asSPStMon a) (asSPStMon (aspPartArr d))).
  Proof.
    refine (MonadRelation_iff
              (fun A (a : ASPSt S A) (d : DSPSt S A) => forall p r, aspRel a p r -> dspRel d p r) _
              (fun A a d => iff_sym (iff_trans (impliesSPSt_asp a (aspPartArr d)) (asp_implies_dsp_rel a d))) _).
    exact (MonadRelation_rel_incl_state (arr1 := ASPArr) (arr2 := DSPArr) S unit).
  Qed.

  Theorem MonadRelation_dsp_implies_dslp :
    @MonadRelation (DSPSt S) (DSLPSt S) (Monad_DSPSt S) (Monad_DSLPSt S)
      (fun A d n => impliesSPSt (asDSLPStMon (dslpPartArr d)) (asDSLPStMon n)).
  Proof.
    refine (MonadRelation_iff
              (fun A (d : DSPSt S A) (n : DSLPSt S A) => forall p r, dslpRel n p r -> dspRel d p r) _
              (fun A d n => iff_sym (iff_trans (impliesSPSt_dslp (dslpPartArr d) n) (dsp_implies_dslp_rel d n))) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state (arr1 := DSLPArr) (arr2 := DSPArr) S unit)).
  Qed.

  Theorem MonadRelation_dslp_implies_dsp :
    @MonadRelation (DSLPSt S) (DSPSt S) (Monad_DSLPSt S) (Monad_DSPSt S)
      (fun A n d => impliesSPSt (asDSLPStMon n) (asDSLPStMon (dslpPartArr d))).
  Proof.
    refine (MonadRelation_iff
              (fun A (n : DSLPSt S A) (d : DSPSt S A) => forall p r, dspRel d p r -> dslpRel n p r) _
              (fun A n d => iff_sym (iff_trans (impliesSPSt_dslp n (dslpPartArr d)) (dslp_implies_dsp_rel n d))) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state (arr1 := DSPArr) (arr2 := DSLPArr) S unit)).
  Qed.

  Theorem MonadRelation_asp_implies_aslp :
    @MonadRelation (ASPSt S) (ASLPSt S) (Monad_ASPSt S) (Monad_ASLPSt S)
      (fun A a l => impliesSPSt (asSPStMon a) (asSPStMon (aspPartAArr l))).
  Proof.
    refine (MonadRelation_iff
              (fun A (a : ASPSt S A) (l : ASLPSt S A) => forall p r, aspRel a p r -> aslpRel l p r) _
              (fun A a l => iff_sym (iff_trans (impliesSPSt_asp a (aspPartAArr l)) (asp_implies_aslp_rel a l))) _).
    exact (MonadRelation_rel_incl_state (arr1 := ASPArr) (arr2 := ASLPArr) S unit).
  Qed.

  Theorem MonadRelation_aslp_implies_asp :
    @MonadRelation (ASLPSt S) (ASPSt S) (Monad_ASLPSt S) (Monad_ASPSt S)
      (fun A l a => impliesSPSt (asSPStMon (aspPartAArr l)) (asSPStMon a)).
  Proof.
    refine (MonadRelation_iff
              (fun A (l : ASLPSt S A) (a : ASPSt S A) => forall p r, aslpRel l p r -> aspRel a p r) _
              (fun A l a => iff_sym (iff_trans (impliesSPSt_asp (aspPartAArr l) a) (aslp_implies_asp_rel l a))) _).
    exact (MonadRelation_rel_incl_state (arr1 := ASLPArr) (arr2 := ASPArr) S unit).
  Qed.

  Theorem MonadRelation_dslp_implies_aslp :
    @MonadRelation (DSLPSt S) (ASLPSt S) (Monad_DSLPSt S) (Monad_ASLPSt S)
      (fun A n l => impliesSPSt (asDSLPStMon n) (asDSLPStMon (dslpPartAArr l))).
  Proof.
    refine (MonadRelation_iff
              (fun A (n : DSLPSt S A) (l : ASLPSt S A) => forall p r, aslpRel l p r -> dslpRel n p r) _
              (fun A n l => iff_sym (iff_trans (impliesSPSt_dslp n (dslpPartAArr l)) (dslp_implies_aslp_rel n l))) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state (arr1 := ASLPArr) (arr2 := DSLPArr) S unit)).
  Qed.

  Theorem MonadRelation_aslp_implies_dslp :
    @MonadRelation (ASLPSt S) (DSLPSt S) (Monad_ASLPSt S) (Monad_DSLPSt S)
      (fun A l n => impliesSPSt (asDSLPStMon (dslpPartAArr l)) (asDSLPStMon n)).
  Proof.
    refine (MonadRelation_iff
              (fun A (l : ASLPSt S A) (n : DSLPSt S A) => forall p r, dslpRel n p r -> aslpRel l p r) _
              (fun A l n => iff_sym (iff_trans (impliesSPSt_dslp (dslpPartAArr l) n) (aslp_implies_dslp_rel l n))) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state (arr1 := DSLPArr) (arr2 := ASLPArr) S unit)).
  Qed.

  (** The same eight instances one transformer further, between the
      flavours' state-and-exception monads.  The parts and the lemmas of
      [PartInclusion] are those of the base arrows at other indices, and
      [stateArrT] over [optionArrT] preserves inclusion of the relations
      denoted ([MonadRelation_rel_incl_state_option]).  Each relation is the
      pointwise order of an ASP or a DSLP carrier, which [ordASPStExc_get]
      and [ordDSLPStExc_get] read at a shared precondition on the start
      state.  Classical. *)
  Theorem MonadRelation_dsp_implies_asp_exc :
    @MonadRelation (DSPStExc S) (ASPStExc S) (Monad_DSPStExc S) (Monad_ASPStExc S)
      (fun A d a => ordASPStExc (aspPartArr d) a).
  Proof.
    refine (MonadRelation_iff
              (fun A (d : DSPStExc S A) (a : ASPStExc S A) => forall p o, dspRel d p o -> aspRel a p o) _
              (fun A d a => iff_sym (dsp_implies_asp_rel d a)) _).
    exact (MonadRelation_rel_incl_state_option (arr1 := DSPArr) (arr2 := ASPArr) S unit).
  Qed.

  Theorem MonadRelation_asp_implies_dsp_exc :
    @MonadRelation (ASPStExc S) (DSPStExc S) (Monad_ASPStExc S) (Monad_DSPStExc S)
      (fun A a d => ordASPStExc a (aspPartArr d)).
  Proof.
    refine (MonadRelation_iff
              (fun A (a : ASPStExc S A) (d : DSPStExc S A) => forall p o, aspRel a p o -> dspRel d p o) _
              (fun A a d => iff_sym (asp_implies_dsp_rel a d)) _).
    exact (MonadRelation_rel_incl_state_option (arr1 := ASPArr) (arr2 := DSPArr) S unit).
  Qed.

  Theorem MonadRelation_dsp_implies_dslp_exc :
    @MonadRelation (DSPStExc S) (DSLPStExc S) (Monad_DSPStExc S) (Monad_DSLPStExc S)
      (fun A d n => ordDSLPStExc (dslpPartArr d) n).
  Proof.
    refine (MonadRelation_iff
              (fun A (d : DSPStExc S A) (n : DSLPStExc S A) => forall p o, dslpRel n p o -> dspRel d p o) _
              (fun A d n => iff_sym (dsp_implies_dslp_rel d n)) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state_option (arr1 := DSLPArr) (arr2 := DSPArr) S unit)).
  Qed.

  Theorem MonadRelation_dslp_implies_dsp_exc :
    @MonadRelation (DSLPStExc S) (DSPStExc S) (Monad_DSLPStExc S) (Monad_DSPStExc S)
      (fun A n d => ordDSLPStExc n (dslpPartArr d)).
  Proof.
    refine (MonadRelation_iff
              (fun A (n : DSLPStExc S A) (d : DSPStExc S A) => forall p o, dspRel d p o -> dslpRel n p o) _
              (fun A n d => iff_sym (dslp_implies_dsp_rel n d)) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state_option (arr1 := DSPArr) (arr2 := DSLPArr) S unit)).
  Qed.

  Theorem MonadRelation_asp_implies_aslp_exc :
    @MonadRelation (ASPStExc S) (ASLPStExc S) (Monad_ASPStExc S) (Monad_ASLPStExc S)
      (fun A a l => ordASPStExc a (aspPartAArr l)).
  Proof.
    refine (MonadRelation_iff
              (fun A (a : ASPStExc S A) (l : ASLPStExc S A) => forall p o, aspRel a p o -> aslpRel l p o) _
              (fun A a l => iff_sym (asp_implies_aslp_rel a l)) _).
    exact (MonadRelation_rel_incl_state_option (arr1 := ASPArr) (arr2 := ASLPArr) S unit).
  Qed.

  Theorem MonadRelation_aslp_implies_asp_exc :
    @MonadRelation (ASLPStExc S) (ASPStExc S) (Monad_ASLPStExc S) (Monad_ASPStExc S)
      (fun A l a => ordASPStExc (aspPartAArr l) a).
  Proof.
    refine (MonadRelation_iff
              (fun A (l : ASLPStExc S A) (a : ASPStExc S A) => forall p o, aslpRel l p o -> aspRel a p o) _
              (fun A l a => iff_sym (aslp_implies_asp_rel l a)) _).
    exact (MonadRelation_rel_incl_state_option (arr1 := ASLPArr) (arr2 := ASPArr) S unit).
  Qed.

  Theorem MonadRelation_dslp_implies_aslp_exc :
    @MonadRelation (DSLPStExc S) (ASLPStExc S) (Monad_DSLPStExc S) (Monad_ASLPStExc S)
      (fun A n l => ordDSLPStExc n (dslpPartAArr l)).
  Proof.
    refine (MonadRelation_iff
              (fun A (n : DSLPStExc S A) (l : ASLPStExc S A) => forall p o, aslpRel l p o -> dslpRel n p o) _
              (fun A n l => iff_sym (dslp_implies_aslp_rel n l)) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state_option (arr1 := ASLPArr) (arr2 := DSLPArr) S unit)).
  Qed.

  Theorem MonadRelation_aslp_implies_dslp_exc :
    @MonadRelation (ASLPStExc S) (DSLPStExc S) (Monad_ASLPStExc S) (Monad_DSLPStExc S)
      (fun A l n => ordDSLPStExc (dslpPartAArr l) n).
  Proof.
    refine (MonadRelation_iff
              (fun A (l : ASLPStExc S A) (n : DSLPStExc S A) => forall p o, dslpRel n p o -> aslpRel l p o) _
              (fun A l n => iff_sym (aslp_implies_dslp_rel l n)) _).
    exact (MonadRelation_flip _ (MonadRelation_rel_incl_state_option (arr1 := DSLPArr) (arr2 := ASLPArr) S unit)).
  Qed.

  (** In the four directions of the taxonomy an instance entails the
      implication between the elements themselves.  Classical. *)
  Lemma dsp_implies_asp_part {A} (d : DSPSt S A) (a : ASPSt S A) :
    impliesSPSt (asSPStMon (aspPartArr d)) (asSPStMon a) ->
    impliesSPSt (asDSPStMon d) (asSPStMon a).
  Proof. intros H P r Hd. exact (H P r (proj1 (proj1 (dsp_meet_parts d) P r Hd))). Qed.

  Lemma dsp_implies_dslp_part {A} (d : DSPSt S A) (n : DSLPSt S A) :
    impliesSPSt (asDSLPStMon (dslpPartArr d)) (asDSLPStMon n) ->
    impliesSPSt (asDSPStMon d) (asDSLPStMon n).
  Proof. intros H P r Hd. exact (H P r (proj2 (proj1 (dsp_meet_parts d) P r Hd))). Qed.

  Lemma asp_implies_aslp_part {A} (a : ASPSt S A) (l : ASLPSt S A) :
    impliesSPSt (asSPStMon a) (asSPStMon (aspPartAArr l)) ->
    impliesSPSt (asSPStMon a) (asASLPStMon l).
  Proof.
    intros H P r Ha. exact (proj2 (aslp_join_parts l) P r (or_introl (H P r Ha))).
  Qed.

  Lemma dslp_implies_aslp_part {A} (n : DSLPSt S A) (l : ASLPSt S A) :
    impliesSPSt (asDSLPStMon n) (asDSLPStMon (dslpPartAArr l)) ->
    impliesSPSt (asDSLPStMon n) (asASLPStMon l).
  Proof.
    intros H P r Hn. exact (proj2 (aslp_join_parts l) P r (or_intror (H P r Hn))).
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Contrapositive                                              *)
  (* --------------------------------------------------------------- *)

  (** For a pair of flavours X - Y, with elements [x] and [y]:

        [_one]   [x Q] exactly when not [y (not Q)]
        [_two]   [y Q] exactly when not [x (not Q)]

      Classical throughout. *)

  (** Between any two WP flavours the contrapositive is a relation of
      monads. *)
  Lemma MonadRelation_contra_toWSt (h1 h2 : WPHealth) :
    @MonadRelation (WPSubSt h1 S) (WPSubSt h2 S) (Monad_WPSubSt h1 S) (Monad_WPSubSt h2 S)
      (fun A w1 w2 => contraWSt (toWSt w1) (toWSt w2)).
  Proof.
    refine (@MonadRelation_pullback (WPSubSt h1 S) (WPSubSt h2 S)
              (Monad_WPSubSt h1 S) (Monad_WPSubSt h2 S)
              (WSt S) (WSt S) (Monad__WSt S) (Monad__WSt S)
              (fun A => @contraWSt S A)
              (fun A => @eq1 (WSt S) (Eq1__WSt S) A) (fun A => @eq1 (WSt S) (Eq1__WSt S) A)
              (fun A => @toWSt h1 S A) (fun A => @toWSt h2 S A)
              (fun A x x' y y' Ex Ey => proj2 (contraWSt_eq1 x x' y y' Ex Ey))
              (fun A a => toWSt_ret h1 S a) (fun A B m k => toWSt_bind h1 S m k)
              (fun A a => toWSt_ret h2 S a) (fun A B n k => toWSt_bind h2 S n k)
              MonadRelation_contraWSt).
  Qed.

  Theorem MonadRelation_contra_awp_dwlp_one :
    @MonadRelation (AWPSt S) (DWLPSt S) (Monad_AWPSt S) (Monad_DWLPSt S)
      (fun A a l => contraWSt (toWSt a) (toWSt l)).
  Proof. exact (MonadRelation_contra_toWSt awp_health dwlp_health). Qed.

  Theorem MonadRelation_contra_awp_dwlp_two :
    @MonadRelation (AWPSt S) (DWLPSt S) (Monad_AWPSt S) (Monad_DWLPSt S)
      (fun A a l => contraWSt (toWSt l) (toWSt a)).
  Proof. exact (MonadRelation_flip _ (MonadRelation_contra_toWSt dwlp_health awp_health)). Qed.

  Theorem MonadRelation_contra_dwp_awlp_one :
    @MonadRelation (DWPSt S) (AWLPSt S) (Monad_DWPSt S) (Monad_AWLPSt S)
      (fun A d l => contraWSt (toWSt d) (toWSt l)).
  Proof. exact (MonadRelation_contra_toWSt dwp_health awlp_health). Qed.

  Theorem MonadRelation_contra_dwp_awlp_two :
    @MonadRelation (DWPSt S) (AWLPSt S) (Monad_DWPSt S) (Monad_AWLPSt S)
      (fun A d l => contraWSt (toWSt l) (toWSt d)).
  Proof. exact (MonadRelation_flip _ (MonadRelation_contra_toWSt awlp_health dwp_health)). Qed.

  Theorem MonadRelation_contra_asp_dslp_one :
    @MonadRelation (ASPSt S) (DSLPSt S) (Monad_ASPSt S) (Monad_DSLPSt S)
      (fun A m n => contraSPSt (asSPStMon m) (asDSLPStMon n)).
  Proof.
    exact (@MonadRelation_pullback (ASPSt S) (DSLPSt S) (Monad_ASPSt S) (Monad_DSLPSt S)
             (SPStMon S) (SPStMon S) Monad_SPStMon_angelic Monad_SPStMon_demonic
             (fun A => @contraSPSt S A)
             (fun A m m' => m ≈ m') (fun A m m' => m ≈ m')
             (fun A => @asSPStMon S A) (fun A => @asDSLPStMon S A)
             (fun A x x' y y' Ex Ey => proj2 (contraSPSt_equiv x x' y y' Ex Ey))
             (fun A a => asSPStMon_ret a) (fun A B m k => asSPStMon_bind m k)
             (fun A a => asDSLPStMon_ret a) (fun A B n k => asDSLPStMon_bind n k)
             MonadRelation_contraSPSt).
  Qed.

  Theorem MonadRelation_contra_asp_dslp_two :
    @MonadRelation (ASPSt S) (DSLPSt S) (Monad_ASPSt S) (Monad_DSLPSt S)
      (fun A m n => contraSPSt (asDSLPStMon n) (asSPStMon m)).
  Proof.
    exact (MonadRelation_iff _ _
             (fun A m n => conj (contraSPSt_sym (asSPStMon m) (asDSLPStMon n))
                                (contraSPSt_sym (asDSLPStMon n) (asSPStMon m)))
             MonadRelation_contra_asp_dslp_one).
  Qed.

  (** The fixed input [unit] of a flavour's monad carries no information. *)
  Lemma forall_unit_input {T : Type} (Q : unit * S -> T -> Prop) :
    (forall s r, Q (tt, s) r) <-> (forall p r, Q p r).
  Proof.
    split; [ intros H [[] s] r; exact (H s r) | intros H s r; exact (H (tt, s) r) ].
  Qed.


  (** A DSP element and an ASLP element are contrapositive exactly when they
      denote one relation. *)
  Lemma contra_dsp_aslp_rel {A} (m : DSPSt S A) (n : ASLPSt S A) :
    contraSPSt (asDSPStMon m) (asASLPStMon n)
    <-> (forall s r, dspRel m (tt, s) r <-> aslpRel n (tt, s) r).
  Proof.
    split.
    - intros H s r.
      assert (HR : forall P : S -> Prop,
                 ((exists s', P s' /\ dspRel m (tt, s') r)
                  /\ (forall s', dspRel m (tt, s') r -> P s'))
                 <-> ~ ((exists s', ~ P s' /\ aslpRel n (tt, s') r)
                        \/ (forall s', aslpRel n (tt, s') r -> ~ P s'))).
      { intro P. etransitivity; [ symmetry; exact (getDSPSt_rel m P r) |].
        etransitivity; [ exact (H P r) |].
        split; intros Hn Hx.
        - exact (Hn (proj2 (getASLPSt_rel n (fun s' => ~ P s') r) Hx)).
        - exact (Hn (proj1 (getASLPSt_rel n (fun s' => ~ P s') r) Hx)). }
      split.
      + intro Hd.
        assert (Hne : exists s0, aslpRel n (tt, s0) r).
        { apply NNPP. intro Hno.
          refine (proj1 (HR (fun _ => True)) _ _).
          - split; [ exists s; exact (conj I Hd) | intros; exact I ].
          - right. intros s' Hs' _. exact (Hno (ex_intro _ s' Hs')). }
        destruct Hne as [s0 Hs0].
        apply NNPP. intro Hna.
        destruct (proj2 (HR (fun s' => s' <> s))) as [_ Hall].
        * intros [[s' [Hs' Hr']] | Hall'].
          -- apply Hna. assert (Heq : s' = s) by (apply NNPP; exact Hs').
             subst s'. exact Hr'.
          -- apply Hna. assert (Heq : s0 = s) by (apply NNPP; exact (Hall' s0 Hs0)).
             subst s0. exact Hs0.
        * exact (Hall s Hd eq_refl).
      + intro Ha.
        assert (Hne : exists s0, dspRel m (tt, s0) r).
        { destruct (proj2 (HR (fun _ => True))) as [[s0 [_ Hs0]] _].
          - intros [[s' [Hf _]] | Hall]; [ exact (Hf I) | exact (Hall s Ha I) ].
          - exists s0. exact Hs0. }
        destruct Hne as [s0 Hs0].
        apply NNPP. intro Hnd.
        refine (proj1 (HR (fun s' => s' <> s)) _ _).
        * split.
          -- exists s0. split; [ intro Heq; subst s0; exact (Hnd Hs0) | exact Hs0 ].
          -- intros s' Hr' Heq. subst s'. exact (Hnd Hr').
        * left. exists s. split; [ intro Hx; exact (Hx eq_refl) | exact Ha ].
    - intros H P r.
      change (getDSPSt m P r <-> ~ getASLPSt n (fun s => ~ P s) r).
      rewrite (getDSPSt_rel m P r), (getASLPSt_rel n (fun s => ~ P s) r). split.
      + intros [[s [Hp Hr]] Hall] [[s' [Hn Hr']] | Hall'].
        * exact (Hn (Hall s' (proj2 (H s' r) Hr'))).
        * exact (Hall' s (proj1 (H s r) Hr) Hp).
      + intro Hn. split.
        * apply NNPP. intro Hex. apply Hn. right. intros s Hr Hp.
          apply Hex. exists s. exact (conj Hp (proj2 (H s r) Hr)).
        * intros s Hr. apply NNPP. intro Hp. apply Hn. left.
          exists s. exact (conj Hp (proj1 (H s r) Hr)).
  Qed.

  Theorem MonadRelation_contra_dsp_aslp_one :
    @MonadRelation (DSPSt S) (ASLPSt S) (Monad_DSPSt S) (Monad_ASLPSt S)
      (fun A m n => contraSPSt (asDSPStMon m) (asASLPStMon n)).
  Proof.
    refine (MonadRelation_iff
              (fun A (m : DSPSt S A) (n : ASLPSt S A) =>
                 forall p r, dspRel m p r <-> aslpRel n p r) _
              (fun A m n => iff_sym (iff_trans (contra_dsp_aslp_rel m n)
                 (forall_unit_input (fun p r => dspRel m p r <-> aslpRel n p r)))) _).
    exact (MonadRelation_rel_eq_state (arr1 := DSPArr) (arr2 := ASLPArr) S unit).
  Qed.

  Theorem MonadRelation_contra_dsp_aslp_two :
    @MonadRelation (DSPSt S) (ASLPSt S) (Monad_DSPSt S) (Monad_ASLPSt S)
      (fun A m n => contraSPSt (asASLPStMon n) (asDSPStMon m)).
  Proof.
    exact (MonadRelation_iff _ _
             (fun A m n => conj (contraSPSt_sym (asDSPStMon m) (asASLPStMon n))
                                (contraSPSt_sym (asASLPStMon n) (asDSPStMon m)))
             MonadRelation_contra_dsp_aslp_one).
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Galois                                                      *)
  (* --------------------------------------------------------------- *)

  Theorem MonadRelation_galois_asp_dwlp :
    @MonadRelation (ASPSt S) (DWLPSt S) (Monad_ASPSt S) (Monad_DWLPSt S)
      (fun A m w => GaloisSPWP (asSPStMon m) (toWSt w)).
  Proof.
    exact (@MonadRelation_pullback (ASPSt S) (DWLPSt S) (Monad_ASPSt S) (Monad_DWLPSt S)
             (SPStMon S) (WSt S) Monad_SPStMon_angelic (Monad__WSt S)
             (fun A => @GaloisSPWP S A)
             (fun A m m' => m ≈ m') (fun A => @eq1 (WSt S) (Eq1__WSt S) A)
             (fun A => @asSPStMon S A) (fun A => @toWSt dwlp_health S A)
             (fun A x x' y y' Ex Ey => proj2 (GaloisSPWP_equiv x x' y y' Ex Ey))
             (fun A a => asSPStMon_ret a) (fun A B m k => asSPStMon_bind m k)
             (fun A a => toWSt_ret dwlp_health S a)
             (fun A B n k => toWSt_bind dwlp_health S n k)
             MonadRelation_GaloisSPWP).
  Qed.

  Theorem MonadRelation_galois_awp_dslp :
    @MonadRelation (AWPSt S) (DSLPSt S) (Monad_AWPSt S) (Monad_DSLPSt S)
      (fun A a n => GaloisWPSP (toWSt a) (asDSLPStMon n)).
  Proof.
    exact (@MonadRelation_pullback (AWPSt S) (DSLPSt S) (Monad_AWPSt S) (Monad_DSLPSt S)
             (WSt S) (SPStMon S) (Monad__WSt S) Monad_SPStMon_demonic
             (fun A => @GaloisWPSP S A)
             (fun A => @eq1 (WSt S) (Eq1__WSt S) A) (fun A m m' => m ≈ m')
             (fun A => @toWSt awp_health S A) (fun A => @asDSLPStMon S A)
             (fun A x x' y y' Ex Ey => proj2 (GaloisWPSP_equiv x x' y y' Ex Ey))
             (fun A a => toWSt_ret awp_health S a)
             (fun A B m k => toWSt_bind awp_health S m k)
             (fun A a => asDSLPStMon_ret a) (fun A B n k => asDSLPStMon_bind n k)
             MonadRelation_GaloisWPSP).
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Partners                                                    *)
  (* --------------------------------------------------------------- *)

  (** In a contrapositive or Galois instance every element of either flavour
      has a partner in the other.  Partners are unique: that is
      [contraWSt_functional], [GaloisSPWP_right_unique] &c., and the
      inclusions reflect [eq1] ([eq1_toWSt], [eq1_ASPSt_SPSt] &c.). *)

  (** Classical: the contrapositive exchanges conjunctive and disjunctive
      only classically. *)
  Lemma contra_awp_in_dwlp {A} (a : AWPSt S A) :
    exists l : DWLPSt S A, contraWSt (toWSt a) (toWSt l).
  Proof.
    exists (arrDWLPSt (dualASPArr (awpStArr a))).
    apply contraWSt_sym. intros Q s. reflexivity.
  Qed.

  Lemma contra_dwlp_in_awp {A} (l : DWLPSt S A) :
    exists a : AWPSt S A, contraWSt (toWSt a) (toWSt l).
  Proof. exists (arrAWPSt (dualDSLPArr (dwlpStArr l))). intros Q s. reflexivity. Qed.

  Lemma contra_dwp_in_awlp {A} (d : DWPSt S A) :
    exists l : AWLPSt S A, contraWSt (toWSt d) (toWSt l).
  Proof.
    exists (arrAWLPSt (dualDSPArr (dwpStArr d))).
    apply contraWSt_sym. intros Q s. reflexivity.
  Qed.

  Lemma contra_awlp_in_dwp {A} (l : AWLPSt S A) :
    exists d : DWPSt S A, contraWSt (toWSt d) (toWSt l).
  Proof. exists (arrDWPSt (dualASLPArr (awlpStArr l))). intros Q s. reflexivity. Qed.

  Lemma contra_asp_in_dslp {A} (m : ASPSt S A) :
    exists n : DSLPSt S A, contraSPSt (asSPStMon m) (asDSLPStMon n).
  Proof.
    exists (arrDSLPSt (dualASPArr (aspStArr m))).
    apply contraSPSt_sym. intros P r. reflexivity.
  Qed.

  Lemma contra_dslp_in_asp {A} (n : DSLPSt S A) :
    exists m : ASPSt S A, contraSPSt (asSPStMon m) (asDSLPStMon n).
  Proof. exists (arrASPSt (dualDSLPArr (dslpStArr n))). intros P r. reflexivity. Qed.

  Lemma contra_dsp_in_aslp {A} (m : DSPSt S A) :
    exists n : ASLPSt S A, contraSPSt (asDSPStMon m) (asASLPStMon n).
  Proof.
    exists (arrASLPSt (dualDSPArr (dspStArr m))).
    apply contraSPSt_sym. intros P r. reflexivity.
  Qed.

  Lemma contra_aslp_in_dsp {A} (n : ASLPSt S A) :
    exists m : DSPSt S A, contraSPSt (asDSPStMon m) (asASLPStMon n).
  Proof. exists (arrDSPSt (dualASLPArr (aslpStArr n))). intros P r. reflexivity. Qed.

  (** Every ASP element has a right adjoint in DWLP, and every DWLP element a
      left adjoint in ASP; likewise AWP and DSLP. *)
  Lemma galois_asp_in_dwlp {A} (m : ASPSt S A) :
    exists w : DWLPSt S A, GaloisSPWP (asSPStMon m) (toWSt w).
  Proof.
    exists (arrDWLPSt (radjASP (aspStArr m))). exact (galois_radjASP (aspStArr m)).
  Qed.

  Lemma galois_dwlp_in_asp {A} (w : DWLPSt S A) :
    exists m : ASPSt S A, GaloisSPWP (asSPStMon m) (toWSt w).
  Proof.
    exists (arrASPSt (ladjDSLP (dwlpStArr w))). exact (galois_ladjDSLP (dwlpStArr w)).
  Qed.

  Lemma galois_awp_in_dslp {A} (a : AWPSt S A) :
    exists n : DSLPSt S A, GaloisWPSP (toWSt a) (asDSLPStMon n).
  Proof.
    exists (arrDSLPSt (radjASP (awpStArr a))). exact (galois_radjASP (awpStArr a)).
  Qed.

  Lemma galois_dslp_in_awp {A} (n : DSLPSt S A) :
    exists a : AWPSt S A, GaloisWPSP (toWSt a) (asDSLPStMon n).
  Proof.
    exists (arrAWPSt (ladjDSLP (dslpStArr n))). exact (galois_ladjDSLP (dslpStArr n)).
  Qed.

  (** A Galois relation carries the order of one flavour to that of the
      other. *)
  Lemma galois_asp_dwlp_order {A} (m m' : ASPSt S A) (w w' : DWLPSt S A) :
    GaloisSPWP (asSPStMon m) (toWSt w) -> GaloisSPWP (asSPStMon m') (toWSt w') ->
    (ordASPSt m m' <-> ordDWLPSt w w').
  Proof.
    intros G G'. rewrite ordASPSt_SPSt.
    etransitivity; [ exact (GaloisSPWP_order _ _ _ _ G G') |].
    exact (impliesWSt_ordWSt (toWSt w') (toWSt w)).
  Qed.

  Lemma galois_awp_dslp_order {A} (a a' : AWPSt S A) (n n' : DSLPSt S A) :
    GaloisWPSP (toWSt a) (asDSLPStMon n) -> GaloisWPSP (toWSt a') (asDSLPStMon n') ->
    (ordAWPSt a a' <-> ordDSLPSt n n').
  Proof.
    intros G G'. rewrite ordDSLPSt_SPSt.
    etransitivity; [ symmetry; exact (impliesWSt_ordWSt (toWSt a') (toWSt a)) |].
    exact (GaloisWPSP_order _ _ _ _ G' G).
  Qed.
End Flavours.

(* ================================================================= *)
(** ** Without state: the collapse, between the monads               *)
(* ================================================================= *)

(** At a fixed input [unit] and with no transformer, [DSP] and [ASP] are
    isomorphic by the identity on transformers, and so are [ASLP] and [DSLP]
    ([DSPMonad.v], [ASLPMonad.v]).  As relations between the monads: two
    elements are the same transformer exactly when they denote one relation,
    and denoting one relation holds at [ret] and is preserved by [bind]
    ([MonadRelation_rel_eq]).  Classical. *)

Section PureCollapse.

  Theorem MonadRelation_dsp_asp_pure :
    @MonadRelation DSP ASP Monad_DSP Monad_ASP
      (fun A d a => forall P b, getDSP d P b <-> getASPArr a P b).
  Proof.
    refine (MonadRelation_iff
              (fun A (d : DSP A) (a : ASP A) => forall x y, dspRel d x y <-> aspRel a x y)
              _ _ (MonadRelation_rel_eq (arr1 := DSPArr) (arr2 := ASPArr) unit)).
    intros A d a. split.
    - intros H P b.
      exact (proj2 (aspRel_eq (dsp_to_asp d) a)
               (fun x y => iff_trans (dsp_to_asp_rel d x y) (H x y)) P b).
    - intros H x y.
      etransitivity; [ symmetry; exact (dsp_to_asp_rel d x y) |].
      exact (proj1 (aspRel_eq (dsp_to_asp d) a) H x y).
  Qed.

  Theorem MonadRelation_aslp_dslp_pure :
    @MonadRelation ASLP DSLP Monad_ASLP Monad_DSLP
      (fun A l n => forall P b, getASLP l P b <-> getDSLPArr n P b).
  Proof.
    refine (MonadRelation_iff
              (fun A (l : ASLP A) (n : DSLP A) => forall x y, aslpRel l x y <-> dslpRel n x y)
              _ _ (MonadRelation_rel_eq (arr1 := ASLPArr) (arr2 := DSLPArr) unit)).
    intros A l n. split.
    - intros H P b.
      exact (proj2 (dslpRel_eq (aslp_to_dslp l) n)
               (fun x y => iff_trans (aslp_to_dslp_rel l x y) (H x y)) P b).
    - intros H x y.
      etransitivity; [ symmetry; exact (aslp_to_dslp_rel l x y) |].
      exact (proj1 (dslpRel_eq (aslp_to_dslp l) n) H x y).
  Qed.
End PureCollapse.
