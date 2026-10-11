(** * The taxonomy diagram, with state and with state and exceptions

    For one computation [m : stdivndNE S A], read in the eight ways of
    [MonadMorphisms.v], the sixteen triples

      WP   [b] included in [wp(c)]   ([Under])     [wp(c)] included in [b]   ([Over])
      SP   [sp(b)] included in [c]   ([Over])      [c] included in [sp(b)]   ([Under])

    with [b] a predicate on start states and [c] one on results with their
    final states, stand in the relations of Verscht and Kaminski's diagram
    (POPL 2025, Figure 10).  Row by row:

      b ⊆ awp(c)   ==>  b ⊆ awlp(c)        dwp(c) ⊆ b   <==  dwlp(c) ⊆ b
          /\                /\                 /\                /\
      b ⊆ dwp(c)   ==>  b ⊆ dwlp(c)        awp(c) ⊆ b   <==  awlp(c) ⊆ b

      aslp(b) ⊆ c  ==>  asp(b) ⊆ c         c ⊆ dslp(b)  <==  c ⊆ dsp(b)
          \/                \/                 \/                \/
      dslp(b) ⊆ c  ==>  dsp(b) ⊆ c         c ⊆ aslp(b)  <==  c ⊆ asp(b)

    Sixteen implications:

      [dwp_under_dwlp_under]   [awp_under_awlp_under]
      [dwp_under_awp_under]    [dwlp_under_awlp_under]
      [dwlp_over_dwp_over]     [awlp_over_awp_over]
      [awp_over_dwp_over]      [awlp_over_dwlp_over]
      [aslp_over_asp_over]     [aslp_over_dslp_over]
      [asp_over_dsp_over]      [dslp_over_dsp_over]
      [dsp_under_dslp_under]   [dsp_under_asp_under]
      [dslp_under_aslp_under]  [asp_under_aslp_under]

    Eight contrapositives, each an equivalence between an [Under] triple and
    an [Over] triple at the complemented predicates (classical):

      [awp_under_contra_dwlp_over]   [awlp_under_contra_dwp_over]
      [dwp_under_contra_awlp_over]   [dwlp_under_contra_awp_over]
      [dsp_under_contra_aslp_over]   [dslp_under_contra_asp_over]
      [asp_under_contra_dslp_over]   [aslp_under_contra_dsp_over]

    Two Galois connections, each an equivalence between a WP triple and an SP
    triple at the same predicates:

      [dwlp_under_galois_asp_over]   b ⊆ dwlp(c)  iff  asp(b) ⊆ c
      [awp_over_galois_dslp_under]   awp(c) ⊆ b   iff  c ⊆ dslp(b)

    The WP edges are edges between the base readings of one element of
    [divndNE], carried to the state level start state by start state
    ([spec_holds_wpSt]).  The SP edges are edges between the four readings
    of one relation, at arbitrary indices.  The Galois edges pair a base WP
    reading with the terminating outcomes ([galois_slice_dwlpPure],
    [galois_awpPure_slice]).

    Four of the WP implications go from a demonic to an angelic reading and
    need the computation to have an outcome.  Every element of [divndNE]
    has one.

    The second half of the file proves the same edges for
    [m : stdivexcndNE S A], under the same names with [_exc]. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.Computation Require Import DivNonDetNE.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.Taxonomy.Arrows Require Import GaloisArr.
From Incorrectness.WP Require Import
  WPureMonad.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy Require Import
  MonadTaxonomy.
From Incorrectness.Triples Require Import Triple MonadMorphisms.

(* ================================================================= *)
(** * The four WP readings of one base computation                   *)
(* ================================================================= *)

Section BaseWP.
  Context {X : Type} (d : divndNE X).

  Lemma dwpPure_incl_dwlpPure :
    pt_incl (spec_read (dwpPure d)) (spec_read (dwlpPure d)).
  Proof.
    intros Q u H oa Ho. specialize (H oa Ho).
    destruct oa; [ exact H | exact I ].
  Qed.

  Lemma awpPure_incl_awlpPure :
    pt_incl (spec_read (awpPure d)) (spec_read (awlpPure d)).
  Proof.
    intros Q u [oa [Ho H]]. exists oa. split; [ exact Ho |].
    destruct oa; [ exact H | exact I ].
  Qed.

  Lemma dwpPure_incl_awpPure :
    pt_incl (spec_read (dwpPure d)) (spec_read (awpPure d)).
  Proof.
    intros Q u H. destruct (getNE_nonEmpty d) as [oa Ho].
    exists oa. exact (conj Ho (H oa Ho)).
  Qed.

  Lemma dwlpPure_incl_awlpPure :
    pt_incl (spec_read (dwlpPure d)) (spec_read (awlpPure d)).
  Proof.
    intros Q u H. destruct (getNE_nonEmpty d) as [oa Ho].
    exists oa. exact (conj Ho (H oa Ho)).
  Qed.

  (** A demonic reading is the contrapositive of the angelic reading that
      counts divergence the other way.  Classical. *)
  Lemma demonic_contra (div div' : Prop) (Hd : div <-> ~ div') (Q : X -> Prop) :
    demonic div d Q <-> ~ angelic div' d (fun a => ~ Q a).
  Proof.
    split.
    - intros H [oa [Ho Hm]]. specialize (H oa Ho).
      destruct oa; [ exact (Hm H) | exact (proj1 Hd H Hm) ].
    - intros Hn oa Ho. destruct oa as [a|].
      + apply NNPP. intro HnQ. apply Hn. exists (Some a). exact (conj Ho HnQ).
      + apply (proj2 Hd). intro Hdiv. apply Hn. exists None. exact (conj Ho Hdiv).
  Qed.

  Lemma angelic_contra (div div' : Prop) (Hd : div <-> ~ div') (Q : X -> Prop) :
    angelic div d Q <-> ~ demonic div' d (fun a => ~ Q a).
  Proof.
    split.
    - intros [oa [Ho Hm]] Hdem. specialize (Hdem oa Ho).
      destruct oa; [ exact (Hdem Hm) | exact (proj1 Hd Hm Hdem) ].
    - intro Hn. apply NNPP. intro Hna. apply Hn. intros oa Ho.
      destruct oa as [a|].
      + intro Hq. apply Hna. exists (Some a). exact (conj Ho Hq).
      + apply NNPP. intro Hnd. apply Hna. exists None.
        exact (conj Ho (proj2 Hd Hnd)).
  Qed.

  Lemma awpPure_contra_dwlpPure :
    pt_contra (spec_read (awpPure d)) (spec_read (dwlpPure d)).
  Proof.
    intros Q u.
    exact (angelic_contra False True (conj (fun f _ => f) (fun n => n I)) Q).
  Qed.

  Lemma awlpPure_contra_dwpPure :
    pt_contra (spec_read (awlpPure d)) (spec_read (dwpPure d)).
  Proof.
    intros Q u.
    exact (angelic_contra True False (conj (fun _ f => f) (fun _ => I)) Q).
  Qed.

  Lemma dwpPure_contra_awlpPure :
    pt_contra (spec_read (dwpPure d)) (spec_read (awlpPure d)).
  Proof.
    intros Q u.
    exact (demonic_contra False True (conj (fun f _ => f) (fun n => n I)) Q).
  Qed.

  Lemma dwlpPure_contra_awpPure :
    pt_contra (spec_read (dwlpPure d)) (spec_read (awpPure d)).
  Proof.
    intros Q u.
    exact (demonic_contra True False (conj (fun _ f => f) (fun _ => I)) Q).
  Qed.

  (** The two Galois relations of [MonadTaxonomy.v], between the terminating
      outcomes and a WP reading. *)
  Lemma galois_slice_dwlpPure : GaloisPredWP (sliceNE d) (dwlpPure d).
  Proof.
    intro Q. split.
    - intros H a Ha. exact (H (Some a) Ha).
    - intros H [a|] Ho; [ exact (H a Ho) | exact I ].
  Qed.

  Lemma galois_awpPure_slice : GaloisWPPred (awpPure d) (sliceNE d).
  Proof.
    intro Q. split.
    - intros [[a|] [Ho H]]; [ exists a; exact (conj Ho H) | destruct H ].
    - intros [a [Ho H]]. exists (Some a). exact (conj Ho H).
  Qed.
End BaseWP.

(** A relation between the base morphisms is one between their lifts,
    start state by start state. *)
Section LiftedEdges.
  Context {S : Type} (σ1 σ2 : forall A, divndNE A -> WPure A).

  Lemma wpSt_under_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop),
      spec_holds (stateT_map S σ1 A m : WSt S A) Under b c ->
      spec_holds (stateT_map S σ2 A m : WSt S A) Under b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpSt σ2 S m Under b c)). intro s.
    exact (pt_holds_incl_under _ _ _ _ (Hi _ (runStateT m s))
             (proj1 (spec_holds_wpSt σ1 S m Under b c) H s)).
  Qed.

  Lemma wpSt_over_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop),
      spec_holds (stateT_map S σ2 A m : WSt S A) Over b c ->
      spec_holds (stateT_map S σ1 A m : WSt S A) Over b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpSt σ1 S m Over b c)). intro s.
    exact (pt_holds_incl_over _ _ _ _ (Hi _ (runStateT m s))
             (proj1 (spec_holds_wpSt σ2 S m Over b c) H s)).
  Qed.

  Lemma wpSt_contra :
    (forall X (d : divndNE X),
        pt_contra (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop),
      spec_holds (stateT_map S σ1 A m : WSt S A) Under b c
      <-> spec_holds (stateT_map S σ2 A m : WSt S A) Over
            (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    intros Hc A m b c.
    etransitivity; [ exact (spec_holds_wpSt σ1 S m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (spec_holds_wpSt σ2 S m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    split; intros H s.
    - exact (proj1 (pt_holds_contra _ _ _ _ (Hc _ (runStateT m s))) (H s)).
    - exact (proj2 (pt_holds_contra _ _ _ _ (Hc _ (runStateT m s))) (H s)).
  Qed.
End LiftedEdges.

(** The same under [stateT] over [optionT]. *)
Section LiftedEdgesExc.
  Context {S : Type} (σ1 σ2 : forall A, divndNE A -> WPure A).

  Lemma wpStExc_under_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivexcndNE S A) (b : S -> Prop) (c : option (A * S) -> Prop),
      spec_holds (stateT_map S (optionT_map σ1) A m : WStExc S A) Under b c ->
      spec_holds (stateT_map S (optionT_map σ2) A m : WStExc S A) Under b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpStExc σ2 S m Under b c)). intro s.
    exact (pt_holds_incl_under _ _ _ _ (Hi _ (unOptionT (runStateT m s)))
             (proj1 (spec_holds_wpStExc σ1 S m Under b c) H s)).
  Qed.

  Lemma wpStExc_over_incl :
    (forall X (d : divndNE X),
        pt_incl (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivexcndNE S A) (b : S -> Prop) (c : option (A * S) -> Prop),
      spec_holds (stateT_map S (optionT_map σ2) A m : WStExc S A) Over b c ->
      spec_holds (stateT_map S (optionT_map σ1) A m : WStExc S A) Over b c.
  Proof.
    intros Hi A m b c H.
    apply (proj2 (spec_holds_wpStExc σ1 S m Over b c)). intro s.
    exact (pt_holds_incl_over _ _ _ _ (Hi _ (unOptionT (runStateT m s)))
             (proj1 (spec_holds_wpStExc σ2 S m Over b c) H s)).
  Qed.

  Lemma wpStExc_contra :
    (forall X (d : divndNE X),
        pt_contra (spec_read (σ1 X d)) (spec_read (σ2 X d))) ->
    forall A (m : stdivexcndNE S A) (b : S -> Prop) (c : option (A * S) -> Prop),
      spec_holds (stateT_map S (optionT_map σ1) A m : WStExc S A) Under b c
      <-> spec_holds (stateT_map S (optionT_map σ2) A m : WStExc S A) Over
            (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    intros Hc A m b c.
    etransitivity; [ exact (spec_holds_wpStExc σ1 S m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (spec_holds_wpStExc σ2 S m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    split; intros H s.
    - exact (proj1 (pt_holds_contra _ _ _ _ (Hc _ (unOptionT (runStateT m s)))) (H s)).
    - exact (proj2 (pt_holds_contra _ _ _ _ (Hc _ (unOptionT (runStateT m s)))) (H s)).
  Qed.
End LiftedEdgesExc.

(* ================================================================= *)
(** * The four SP readings of one relation                           *)
(* ================================================================= *)

Section OneRelation.
  Context {X Y : Type} (R : Rel X Y).

  Lemma dsp_incl_asp :
    pt_incl (Forward (getDSP (dspOfRelArr R))) (Forward (getASPArr (relASP R))).
  Proof. intros P y H. exact (proj1 H). Qed.

  Lemma dsp_incl_dslp :
    pt_incl (Forward (getDSP (dspOfRelArr R))) (Forward (getDSLPArr (relDSLP R))).
  Proof. intros P y H. exact (proj2 H). Qed.

  Lemma asp_incl_aslp :
    pt_incl (Forward (getASPArr (relASP R))) (Forward (getASLP (aslpOfRelArr R))).
  Proof. intros P y H. exact (or_introl H). Qed.

  Lemma dslp_incl_aslp :
    pt_incl (Forward (getDSLPArr (relDSLP R))) (Forward (getASLP (aslpOfRelArr R))).
  Proof. intros P y H. exact (or_intror H). Qed.

  (** Classical: [contra_asp_dslp_rel] and [contra_dsp_aslp_rel], at two
      elements that denote [R]. *)
  Lemma asp_contra_dslp :
    pt_contra (Forward (getASPArr (relASP R))) (Forward (getDSLPArr (relDSLP R))).
  Proof.
    exact (proj2 (contra_asp_dslp_rel (relASP R) (relDSLP R))
             (fun x y => iff_trans (aspRel_ofRel R x y)
                           (iff_sym (dslpRel_ofRel R x y)))).
  Qed.

  Lemma dslp_contra_asp :
    pt_contra (Forward (getDSLPArr (relDSLP R))) (Forward (getASPArr (relASP R))).
  Proof.
    exact (Contrapositive_sym (aspMono (relASP R)) (dslpMono (relDSLP R))
             asp_contra_dslp).
  Qed.

  Lemma dsp_contra_aslp :
    pt_contra (Forward (getDSP (dspOfRelArr R))) (Forward (getASLP (aslpOfRelArr R))).
  Proof.
    exact (proj2 (contra_dsp_aslp_rel (dspOfRelArr R) (aslpOfRelArr R))
             (fun x y => iff_trans (dspRel_ofRelArr R x y)
                           (iff_sym (aslpRel_ofRelArr R x y)))).
  Qed.

  Lemma aslp_contra_dsp :
    pt_contra (Forward (getASLP (aslpOfRelArr R))) (Forward (getDSP (dspOfRelArr R))).
  Proof.
    exact (Contrapositive_sym (dspMono (dspOfRelArr R)) (aslpMono (aslpOfRelArr R))
             dsp_contra_aslp).
  Qed.
End OneRelation.

(* ================================================================= *)
(** * The diagram                                                     *)
(* ================================================================= *)

Section Diagram.
  Context {S A : Type} (m : stdivndNE S A) (b : S -> Prop) (c : A * S -> Prop).

  Local Notation R := (fun (us : unit * S) (r : A * S) => outSt m (snd us) (Some r)).

  (** ** WP implications *)

  Theorem dwp_under_dwlp_under :
    triple (@dwpSt S) m Under b c -> triple (@dwlpSt S) m Under b c.
  Proof.
    exact (wpSt_under_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awp_under_awlp_under :
    triple (@awpSt S) m Under b c -> triple (@awlpSt S) m Under b c.
  Proof.
    exact (wpSt_under_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwp_under_awp_under :
    triple (@dwpSt S) m Under b c -> triple (@awpSt S) m Under b c.
  Proof.
    exact (wpSt_under_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem dwlp_under_awlp_under :
    triple (@dwlpSt S) m Under b c -> triple (@awlpSt S) m Under b c.
  Proof.
    exact (wpSt_under_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_over_dwp_over :
    triple (@dwlpSt S) m Over b c -> triple (@dwpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_over_awp_over :
    triple (@awlpSt S) m Over b c -> triple (@awpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem awp_over_dwp_over :
    triple (@awpSt S) m Over b c -> triple (@dwpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem awlp_over_dwlp_over :
    triple (@awlpSt S) m Over b c -> triple (@dwlpSt S) m Over b c.
  Proof.
    exact (wpSt_over_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  (** ** WP contrapositives *)

  Theorem awp_under_contra_dwlp_over :
    triple (@awpSt S) m Under b c
    <-> triple (@dwlpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@awpPure) (@dwlpPure)
             (fun X d => awpPure_contra_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_under_contra_dwp_over :
    triple (@awlpSt S) m Under b c
    <-> triple (@dwpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@awlpPure) (@dwpPure)
             (fun X d => awlpPure_contra_dwpPure d) A m b c).
  Qed.

  Theorem dwp_under_contra_awlp_over :
    triple (@dwpSt S) m Under b c
    <-> triple (@awlpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@dwpPure) (@awlpPure)
             (fun X d => dwpPure_contra_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_under_contra_awp_over :
    triple (@dwlpSt S) m Under b c
    <-> triple (@awpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpSt_contra (@dwlpPure) (@awpPure)
             (fun X d => dwlpPure_contra_awpPure d) A m b c).
  Qed.

  (** ** SP implications *)

  Theorem aslp_over_asp_over :
    triple (@aslpSt S) m Over b c -> triple (@aspSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_aspSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aslpSt m Over b c) H)).
  Qed.

  Theorem aslp_over_dslp_over :
    triple (@aslpSt S) m Over b c -> triple (@dslpSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dslpSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_aslpSt m Over b c) H)).
  Qed.

  Theorem asp_over_dsp_over :
    triple (@aspSt S) m Over b c -> triple (@dspSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_aspSt m Over b c) H)).
  Qed.

  Theorem dslp_over_dsp_over :
    triple (@dslpSt S) m Over b c -> triple (@dspSt S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspSt m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dslpSt m Over b c) H)).
  Qed.

  Theorem dsp_under_dslp_under :
    triple (@dspSt S) m Under b c -> triple (@dslpSt S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_dslpSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dspSt m Under b c) H)).
  Qed.

  Theorem dsp_under_asp_under :
    triple (@dspSt S) m Under b c -> triple (@aspSt S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aspSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_dspSt m Under b c) H)).
  Qed.

  Theorem dslp_under_aslp_under :
    triple (@dslpSt S) m Under b c -> triple (@aslpSt S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aslpSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_dslpSt m Under b c) H)).
  Qed.

  Theorem asp_under_aslp_under :
    triple (@aspSt S) m Under b c -> triple (@aslpSt S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aslpSt m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aspSt m Under b c) H)).
  Qed.

  (** ** SP contrapositives *)

  Theorem dsp_under_contra_aslp_over :
    triple (@dspSt S) m Under b c
    <-> triple (@aslpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dspSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aslpSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dsp_contra_aslp R)).
  Qed.

  Theorem dslp_under_contra_asp_over :
    triple (@dslpSt S) m Under b c
    <-> triple (@aspSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dslpSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aspSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dslp_contra_asp R)).
  Qed.

  Theorem asp_under_contra_dslp_over :
    triple (@aspSt S) m Under b c
    <-> triple (@dslpSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aspSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dslpSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (asp_contra_dslp R)).
  Qed.

  Theorem aslp_under_contra_dsp_over :
    triple (@aslpSt S) m Under b c
    <-> triple (@dspSt S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aslpSt m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dspSt m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (aslp_contra_dsp R)).
  Qed.

  (** ** Galois connections *)

  Theorem dwlp_under_galois_asp_over :
    triple (@dwlpSt S) m Under b c <-> triple (@aspSt S) m Over b c.
  Proof.
    symmetry.
    refine (proj2 (galois_asp_rel (aspSt m)
                     (fun s Q => getWPure (runStateT (dwlpSt m) s) Q)) _ b c).
    intros s Q.
    etransitivity; [ exact (galois_slice_dwlpPure (runStateT m s) Q) |].
    split.
    - intros H y Hy. exact (H y (proj1 (aspRel_ofRel _ (tt, s) y) Hy)).
    - intros H a Ha. exact (H a (proj2 (aspRel_ofRel _ (tt, s) a) Ha)).
  Qed.

  Theorem awp_over_galois_dslp_under :
    triple (@awpSt S) m Over b c <-> triple (@dslpSt S) m Under b c.
  Proof.
    refine (proj2 (galois_dslp_rel
                     (fun s Q => getWPure (runStateT (awpSt m) s) Q)
                     (dslpSt m)) _ c b).
    intros s Q.
    etransitivity; [ exact (galois_awpPure_slice (runStateT m s) Q) |].
    split.
    - intros [a [Ha Hq]]. exists a.
      exact (conj (proj2 (dslpRel_ofRel _ (tt, s) a) Ha) Hq).
    - intros [y [Hy Hq]]. exists y.
      exact (conj (proj1 (dslpRel_ofRel _ (tt, s) y) Hy) Hq).
  Qed.
End Diagram.

(* ================================================================= *)
(** * The diagram, with exceptions                                    *)
(* ================================================================= *)

(** The same twenty-six edges for one [m : stdivexcndNE S A], with a
    postcondition on [option (A * S)]: [None] is the exception.  The base
    lemmas are used at the result type [option (A * S)], and the SP edges
    at the output index [option (A * S)]; nothing else changes. *)

Section DiagramExc.
  Context {S A : Type} (m : stdivexcndNE S A)
    (b : S -> Prop) (c : option (A * S) -> Prop).

  Local Notation R :=
    (fun (us : unit * S) (o : option (A * S)) => outStExc m (snd us) (Some o)).

  (** ** WP implications *)

  Theorem dwp_under_dwlp_under_exc :
    triple (@dwpStExc S) m Under b c -> triple (@dwlpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awp_under_awlp_under_exc :
    triple (@awpStExc S) m Under b c -> triple (@awlpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwp_under_awp_under_exc :
    triple (@dwpStExc S) m Under b c -> triple (@awpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem dwlp_under_awlp_under_exc :
    triple (@dwlpStExc S) m Under b c -> triple (@awlpStExc S) m Under b c.
  Proof.
    exact (wpStExc_under_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_over_dwp_over_exc :
    triple (@dwlpStExc S) m Over b c -> triple (@dwpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwpPure) (@dwlpPure)
             (fun X d => dwpPure_incl_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_over_awp_over_exc :
    triple (@awlpStExc S) m Over b c -> triple (@awpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@awpPure) (@awlpPure)
             (fun X d => awpPure_incl_awlpPure d) A m b c).
  Qed.

  Theorem awp_over_dwp_over_exc :
    triple (@awpStExc S) m Over b c -> triple (@dwpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwpPure) (@awpPure)
             (fun X d => dwpPure_incl_awpPure d) A m b c).
  Qed.

  Theorem awlp_over_dwlp_over_exc :
    triple (@awlpStExc S) m Over b c -> triple (@dwlpStExc S) m Over b c.
  Proof.
    exact (wpStExc_over_incl (@dwlpPure) (@awlpPure)
             (fun X d => dwlpPure_incl_awlpPure d) A m b c).
  Qed.

  (** ** WP contrapositives *)

  Theorem awp_under_contra_dwlp_over_exc :
    triple (@awpStExc S) m Under b c
    <-> triple (@dwlpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@awpPure) (@dwlpPure)
             (fun X d => awpPure_contra_dwlpPure d) A m b c).
  Qed.

  Theorem awlp_under_contra_dwp_over_exc :
    triple (@awlpStExc S) m Under b c
    <-> triple (@dwpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@awlpPure) (@dwpPure)
             (fun X d => awlpPure_contra_dwpPure d) A m b c).
  Qed.

  Theorem dwp_under_contra_awlp_over_exc :
    triple (@dwpStExc S) m Under b c
    <-> triple (@awlpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@dwpPure) (@awlpPure)
             (fun X d => dwpPure_contra_awlpPure d) A m b c).
  Qed.

  Theorem dwlp_under_contra_awp_over_exc :
    triple (@dwlpStExc S) m Under b c
    <-> triple (@awpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    exact (wpStExc_contra (@dwlpPure) (@awpPure)
             (fun X d => dwlpPure_contra_awpPure d) A m b c).
  Qed.

  (** ** SP implications *)

  Theorem aslp_over_asp_over_exc :
    triple (@aslpStExc S) m Over b c -> triple (@aspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_aspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aslpStExc m Over b c) H)).
  Qed.

  Theorem aslp_over_dslp_over_exc :
    triple (@aslpStExc S) m Over b c -> triple (@dslpStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dslpStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_aslpStExc m Over b c) H)).
  Qed.

  Theorem asp_over_dsp_over_exc :
    triple (@aspStExc S) m Over b c -> triple (@dspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_aspStExc m Over b c) H)).
  Qed.

  Theorem dslp_over_dsp_over_exc :
    triple (@dslpStExc S) m Over b c -> triple (@dspStExc S) m Over b c.
  Proof.
    intro H. apply (proj2 (triple_dspStExc m Over b c)).
    exact (pt_holds_incl_over _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dslpStExc m Over b c) H)).
  Qed.

  Theorem dsp_under_dslp_under_exc :
    triple (@dspStExc S) m Under b c -> triple (@dslpStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_dslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_dslp R)
             (proj1 (triple_dspStExc m Under b c) H)).
  Qed.

  Theorem dsp_under_asp_under_exc :
    triple (@dspStExc S) m Under b c -> triple (@aspStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aspStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dsp_incl_asp R)
             (proj1 (triple_dspStExc m Under b c) H)).
  Qed.

  Theorem dslp_under_aslp_under_exc :
    triple (@dslpStExc S) m Under b c -> triple (@aslpStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (dslp_incl_aslp R)
             (proj1 (triple_dslpStExc m Under b c) H)).
  Qed.

  Theorem asp_under_aslp_under_exc :
    triple (@aspStExc S) m Under b c -> triple (@aslpStExc S) m Under b c.
  Proof.
    intro H. apply (proj2 (triple_aslpStExc m Under b c)).
    exact (pt_holds_incl_under _ _ _ _ (asp_incl_aslp R)
             (proj1 (triple_aspStExc m Under b c) H)).
  Qed.

  (** ** SP contrapositives *)

  Theorem dsp_under_contra_aslp_over_exc :
    triple (@dspStExc S) m Under b c
    <-> triple (@aslpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dspStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aslpStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dsp_contra_aslp R)).
  Qed.

  Theorem dslp_under_contra_asp_over_exc :
    triple (@dslpStExc S) m Under b c
    <-> triple (@aspStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_dslpStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_aspStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (dslp_contra_asp R)).
  Qed.

  Theorem asp_under_contra_dslp_over_exc :
    triple (@aspStExc S) m Under b c
    <-> triple (@dslpStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aspStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dslpStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (asp_contra_dslp R)).
  Qed.

  Theorem aslp_under_contra_dsp_over_exc :
    triple (@aslpStExc S) m Under b c
    <-> triple (@dspStExc S) m Over (fun s => ~ b s) (fun r => ~ c r).
  Proof.
    etransitivity; [ exact (triple_aslpStExc m Under b c) |].
    etransitivity;
      [| symmetry;
         exact (triple_dspStExc m Over (fun s => ~ b s) (fun r => ~ c r)) ].
    exact (pt_holds_contra _ _ _ _ (aslp_contra_dsp R)).
  Qed.

  (** ** Galois connections *)

  Theorem dwlp_under_galois_asp_over_exc :
    triple (@dwlpStExc S) m Under b c <-> triple (@aspStExc S) m Over b c.
  Proof.
    symmetry.
    refine (proj2 (galois_asp_rel (aspStExc m)
                     (fun s Q => getWPure (unOptionT (runStateT (dwlpStExc m) s)) Q)) _ b c).
    intros s Q.
    etransitivity; [ exact (galois_slice_dwlpPure (unOptionT (runStateT m s)) Q) |].
    split.
    - intros H y Hy. exact (H y (proj1 (aspRel_ofRel _ (tt, s) y) Hy)).
    - intros H a Ha. exact (H a (proj2 (aspRel_ofRel _ (tt, s) a) Ha)).
  Qed.

  Theorem awp_over_galois_dslp_under_exc :
    triple (@awpStExc S) m Over b c <-> triple (@dslpStExc S) m Under b c.
  Proof.
    refine (proj2 (galois_dslp_rel
                     (fun s Q => getWPure (unOptionT (runStateT (awpStExc m) s)) Q)
                     (dslpStExc m)) _ c b).
    intros s Q.
    etransitivity; [ exact (galois_awpPure_slice (unOptionT (runStateT m s)) Q) |].
    split.
    - intros [a [Ha Hq]]. exists a.
      exact (conj (proj2 (dslpRel_ofRel _ (tt, s) a) Ha) Hq).
    - intros [y [Hy Hq]]. exists y.
      exact (conj (proj1 (dslpRel_ofRel _ (tt, s) y) Hy) Hq).
  Qed.
End DiagramExc.
