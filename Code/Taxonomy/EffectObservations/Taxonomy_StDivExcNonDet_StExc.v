(** * Taxonomy of the observations of [stdivexcnd]

    Everything here COMPARES observations rather than defining them.

    The WP half relates the four observations of
    [WP/StDivExcNonDet_WStExc.v]: the inclusions of Theorem 3.7, the
    contrapositive transformers of Theorem 3.8, and the resulting taxonomy of
    triples (upper half of Figure 5).

    The SP half does the same for [SP/StDivExcNonDet_SPStExc.v]: the
    contrapositive pairs and the taxonomy of the [ASP] / [DSLP] / [DSP] /
    [ASLP] triples.

    [Section GaloisConnection] then joins the two, identifying the [obsDWLP]
    and [obsAWP] triples with the [obsASP] and [obsDSLP] ones. *)

From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observation inclusions (Theorem 3.7)                        *)
(* ================================================================= *)

Section NDItWPInclusions.

  Variable S : Type.

  (** Total demonic <= partial demonic: replace [False] with [True]
      in the divergence branch. *)
  Theorem obsDWP_incl_obsDWLP :
    forall A (m : stdivexcnd S A) s post,
      unOptionT (runStateT (obsDWP m) s) post ->
      unOptionT (runStateT (obsDWLP m) s) post.
  Proof.
    intros A m s post. cbn.
    destruct (runStateT m s) as [[outcomes]].
    intros H oa Hoa. specialize (H oa Hoa).
    destruct oa; [exact H | exact I].
  Qed.

  (** Total angelic <= partial angelic: left-inject the existential
      witness into the disjunction. *)
  Theorem obsAWP_incl_obsAWLP :
    forall A (m : stdivexcnd S A) s post,
      unOptionT (runStateT (obsAWP m) s) post ->
      unOptionT (runStateT (obsAWLP m) s) post.
  Proof.
    intros A m s post. cbn.
    destruct (runStateT m s) as [[outcomes]].
    intros [r [Hr Hp]]. left. exists r. exact (conj Hr Hp).
  Qed.

  (** Demonic <= angelic (total): needs at least one outcome.
      DWP excludes [None], so the witness must be [Some r]. *)
  Theorem obsDWP_incl_obsAWP :
    forall A (m : stdivexcnd S A) s post,
      (exists oa, unOptionT (unOptionT (runStateT m s)) oa) ->
      unOptionT (runStateT (obsDWP m) s) post ->
      unOptionT (runStateT (obsAWP m) s) post.
  Proof.
    intros A m s post. cbn.
    destruct (runStateT m s) as [[outcomes]].
    intros [oa Hoa] H.
    destruct oa as [r|].
    - exists r. exact (conj Hoa (H (Some r) Hoa)).
    - exfalso. exact (H None Hoa).
  Qed.

  (** Demonic <= angelic (partial): needs at least one outcome.
      If [Some r], left with witness; if [None], right with divergence. *)
  Theorem obsDWLP_incl_obsAWLP :
    forall A (m : stdivexcnd S A) s post,
      (exists oa, unOptionT (unOptionT (runStateT m s)) oa) ->
      unOptionT (runStateT (obsDWLP m) s) post ->
      unOptionT (runStateT (obsAWLP m) s) post.
  Proof.
    intros A m s post. cbn.
    destruct (runStateT m s) as [[outcomes]].
    intros [oa Hoa] H.
    destruct oa as [r|].
    - left. exists r. exact (conj Hoa (H (Some r) Hoa)).
    - right. exact Hoa.
  Qed.

End NDItWPInclusions.

Section NDItWPContrapositives.

  Variable S : Type.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.8: Contrapositive transformers WP               *)
  (* -------------------------------------------------------------- *)

  Theorem obsAWP_contrapositive_obsDWLP :
    forall A (m : stdivexcnd S A) s post,
      unOptionT (runStateT (obsAWP m) s) post <->
      ~ unOptionT (runStateT (obsDWLP m) s) (fun r => ~ post r).
  Proof.
    intros A m s post. cbn.
    destruct (runStateT m s) as [[outcomes]].
    split.
    - intros [r [Hr Hp]] Hdwlp.
      exact (Hdwlp (Some r) Hr Hp).
    - intro Hnn.
      apply NNPP. intro Habs.
      apply Hnn.
      intros oa Hoa. destruct oa as [r|].
      + intro Hp. apply Habs. exists r. exact (conj Hoa Hp).
      + exact I.
  Qed.

  Theorem obsDWP_contrapositive_obsAWLP :
    forall A (m : stdivexcnd S A) s post,
      unOptionT (runStateT (obsDWP m) s) post <->
      ~ unOptionT (runStateT (obsAWLP m) s) (fun r => ~ post r).
  Proof.
    intros A m s post. cbn.
    destruct (runStateT m s) as [[outcomes]].
    split.
    - intros Hdwp [Hawlp | Hdiv].
      + destruct Hawlp as [r [Hr Hnp]].
        exact (Hnp (Hdwp (Some r) Hr)).
      + exact (Hdwp None Hdiv).
    - intros Hnawlp oa Hoa.
      destruct oa as [r|].
      + apply NNPP. intro Hnp.
        apply Hnawlp. left. exists r. exact (conj Hoa Hnp).
      + exfalso. apply Hnawlp. right. exact Hoa.
  Qed.

End NDItWPContrapositives.

(* ================================================================= *)
(** ** Taxonomy of WP transformers (Upper half of Figure 5)                        *)
(* ================================================================= *)

Section TaxonomyWPTransformers.
  Variable S : Type.

  Theorem cc_dwp_implies_dwlp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWP m pre SubsetOf post ->
      tripleWP obsDWLP m pre SubsetOf post.
  Proof.
    intros A m pre post H s Hpre.
    apply obsDWP_incl_obsDWLP. exact (H s Hpre).
  Qed.

  Theorem cc_dwp_implies_dwlp_spec :
    forall A (m: stdivexcnd S A) pre post,
      tripleWPspec obsDWP m pre SubsetOf post ->
      tripleWPspec obsDWLP m pre SubsetOf post.
  Proof.
    (* Both [Under] specs share the same source [pp2wp_under pre post];
       the implication is the [obsDWP <= obsDWLP] inclusion, pointwise. *)
    intros A m pre post H s p Hp.
    apply obsDWP_incl_obsDWLP. apply H. exact Hp.
  Qed.

  Theorem cc_dwp_implies_awp :
    forall A (m: stdivexcnd S A) pre post,
      (forall s0, pre s0 -> exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsDWP m pre SubsetOf post ->
      tripleWP obsAWP m pre SubsetOf post.
  Proof.
    intros A m pre post Hne H s Hpre.
    apply obsDWP_incl_obsAWP.
    - exact (Hne s Hpre).
    - exact (H s Hpre).
  Qed.

  Theorem cc_awp_implies_awlp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWP m pre SubsetOf post ->
      tripleWP obsAWLP m pre SubsetOf post.
  Proof.
    intros A m pre post H s Hpre.
    apply obsAWP_incl_obsAWLP. exact (H s Hpre).
  Qed.

  Theorem cc_dwlp_implies_awlp :
    forall A (m: stdivexcnd S A) pre post,
      (forall s0, pre s0 -> exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsDWLP m pre SubsetOf post ->
      tripleWP obsAWLP m pre SubsetOf post.
  Proof.
    intros A m pre post Hne H s Hpre.
    apply obsDWLP_incl_obsAWLP.
    - exact (Hne s Hpre).
    - exact (H s Hpre).
  Qed.

  Theorem ii_awlp_implies_dwlp :
    forall A (m: stdivexcnd S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsAWLP m pre SupersetOf post ->
      tripleWP obsDWLP m pre SupersetOf post.
  Proof.
    intros A m pre post Hne H s Hdwlp.
    apply H. apply obsDWLP_incl_obsAWLP.
    - exact (Hne s).
    - exact Hdwlp.
  Qed.

  Theorem ii_awlp_implies_dwlp_spec :
    forall A (m: stdivexcnd S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWPspec obsAWLP m pre SupersetOf post ->
      tripleWPspec obsDWLP m pre SupersetOf post.
  Proof.
    (* Both [Over] specs share the same target [pp2wp_over pre post];
       the implication is the [obsDWLP <= obsAWLP] inclusion (needs a
       reachable outcome), pointwise. *)
    intros A m pre post Hne H s p Hdwlp.
    apply H. apply obsDWLP_incl_obsAWLP.
    - exact (Hne s).
    - exact Hdwlp.
  Qed.

  Theorem ii_dwlp_implies_dwp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWLP m pre SupersetOf post ->
      tripleWP obsDWP m pre SupersetOf post.
  Proof.
    intros A m pre post H s Hdwp.
    apply H. apply obsDWP_incl_obsDWLP. exact Hdwp.
  Qed.

  Theorem ii_awlp_implies_awp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWLP m pre SupersetOf post ->
      tripleWP obsAWP m pre SupersetOf post.
  Proof.
    intros A m pre post H s Hawp.
    apply H. apply obsAWP_incl_obsAWLP. exact Hawp.
  Qed.

  Theorem ii_awp_implies_dwp :
    forall A (m: stdivexcnd S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsAWP m pre SupersetOf post ->
      tripleWP obsDWP m pre SupersetOf post.
  Proof.
    intros A m pre post Hne H s Hdwp.
    apply H. apply obsDWP_incl_obsAWP.
    - exact (Hne s).
    - exact Hdwp.
  Qed.

  Theorem ci_awp_dwlp_contrapositive :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWLP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWP obsAWP m pre SubsetOf post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply (proj2 (obsAWP_contrapositive_obsDWLP _ _ m s post)).
    intro Hdwlp. exact (Hii s Hdwlp Hpre).
  Qed.

  Theorem ci_awp_dwlp_contrapositive_spec :
    forall A (m: stdivexcnd S A) pre post,
      tripleWPspec obsDWLP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWPspec obsAWP m pre SubsetOf post.
  Proof.
    (* Spec-level mirror of [ci_awp_dwlp_contrapositive]: the [obsAWP]/[obsDWLP]
       contrapositive at predicate [p], with [post <= p] supplying the needed
       [~ p <= ~ post] by contraposition. *)
    intros A m pre post Hii s p Hp.
    destruct Hp as [Hpre Hsub].
    apply (proj2 (obsAWP_contrapositive_obsDWLP _ _ m s p)).
    intro Hdwlp.
    apply (Hii s (fun r => ~ p r) Hdwlp).
    - intros r Hnp Hpost. exact (Hnp (Hsub r Hpost)).
    - exact Hpre.
  Qed.

  Theorem ci_awp_dwlp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleWP obsAWP m (fun s => ~ (pre s)) SubsetOf (fun r => ~ (post r)) ->
      tripleWP obsDWLP m pre SupersetOf post.
  Proof.
    intros A m pre post Hii s Hdwlp.
    apply NNPP. intro Hnpre.
    specialize (Hii s Hnpre).
    unfold obsAWP in Hii. unfold obsDWLP in Hdwlp. cbn in Hii, Hdwlp.
    destruct (runStateT m s) as [[outcomes]]. cbn in Hii, Hdwlp.
    destruct Hii as [r [Hr Hnpost]].
    exact (Hnpost (Hdwlp (Some r) Hr)).
  Qed.

  Theorem ci_dwp_awlp_contrapositive :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWLP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWP obsDWP m pre SubsetOf post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply (proj2 (obsDWP_contrapositive_obsAWLP _ _ m s post)).
    intro Hawlp. exact (Hii s Hawlp Hpre).
  Qed.

  Theorem ci_dwp_awlp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleWP obsDWP m (fun s => ~ (pre s)) SubsetOf (fun r => ~ (post r)) ->
      tripleWP obsAWLP m pre SupersetOf post.
  Proof.
    intros A m pre post Hii s Hawlp. apply NNPP. intro Hnpre.
    specialize (Hii s Hnpre).
    unfold obsDWP, obsAWLP in *. cbn in Hii, Hawlp.
    destruct (runStateT m s) as [[outcomes]]. cbn in Hii, Hawlp.
    destruct Hawlp as [[r [Hr Hpost]] | Hnone].
    - exact (Hii (Some r) Hr Hpost).
    - exact (Hii None Hnone).
  Qed.

  Theorem ci_awlp_dwp_contrapositive :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWP obsAWLP m pre SubsetOf post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply NNPP. intro Hnawlp.
    assert (Hdwp : unOptionT (runStateT (obsDWP m) s) (fun r => ~ post r)).
    { unfold obsDWP, obsAWLP in *.
      cbn in Hnawlp |- *.
      destruct (runStateT m s) as [[outcomes]].
      intros oa Hoa. destruct oa as [r|].
      - intro Hr. apply Hnawlp. left. exists r. exact (conj Hoa Hr).
      - exfalso. apply Hnawlp. right. exact Hoa. }
    exact (Hii s Hdwp Hpre).
  Qed.

  Theorem ci_awlp_dwp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleWP obsAWLP m (fun s => ~ (pre s)) SubsetOf (fun r => ~ (post r)) ->
      tripleWP obsDWP m pre SupersetOf post.
  Proof.
    intros A m pre post Hii s Hdwp. apply NNPP. intro Hnpre.
    specialize (Hii s Hnpre).
    unfold obsAWLP, obsDWP in *. cbn in Hii, Hdwp.
    destruct (runStateT m s) as [[outcomes]]. cbn in Hii, Hdwp.
    destruct Hii as [[r [Hr Hnpost]] | Hnone].
    - exact (Hnpost (Hdwp (Some r) Hr)).
    - exact (Hdwp None Hnone).
  Qed.
  
  Theorem ci_dwlp_awp_contrapositive :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWP obsDWLP m pre SubsetOf post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply NNPP. intro Hndwlp.
    assert (Hawp : unOptionT (runStateT (obsAWP m) s) (fun r => ~ post r)).
    { unfold obsAWP, obsDWLP in *.
      cbn in Hndwlp |- *.
      destruct (runStateT m s) as [[outcomes]].
      apply NNPP. intro Hnawp.
      apply Hndwlp.
      intros oa Hoa. destruct oa as [r|].
      - apply NNPP. intro Hr. apply Hnawp. exists r. exact (conj Hoa Hr).
      - exact I. }
    exact (Hii s Hawp Hpre).
  Qed.

   Theorem ci_dwlp_awp_contrapositive' :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWLP m (fun s => ~ (pre s)) SubsetOf (fun r => ~ (post r)) ->
      tripleWP obsAWP m pre SupersetOf post.
  Proof.
    intros A m pre post Hii s Hawp. apply NNPP. intro Hnpre.
    specialize (Hii s Hnpre).
    unfold obsDWLP, obsAWP in *. cbn in Hii, Hawp.
    destruct (runStateT m s) as [[outcomes]]. cbn in Hii, Hawp.
    destruct Hawp as [r [Hr Hpost]].
    exact (Hii (Some r) Hr Hpost).
  Qed.
End TaxonomyWPTransformers.

(* ==================================================================== *)
(** * SP side: the observations of [stdivexcnd] into [SPStExc]          *)
(* ==================================================================== *)

From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import BaseGaloisConnections NewGaloisConnections.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivExcNonDet_SPStExc.

Section ContrapositiveTransformers.
  Variable S : Type.
  
  Theorem obsASP_contrapositive {A} (m : stdivexcnd S A) pre r :
  getASPStExc (obsASP m) pre r <->
    ~ getDSLPStExc (obsDSLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [s [Hp Hr]] Hall. exact (Hall s Hr Hp).
    - intro Hnn. apply NNPP. intro Habs. apply Hnn.
      intros s Hr Hp. apply Habs. exists s. split; [exact Hp | exact Hr].
  Qed.

  Theorem obsDSP_contrapositive {A} (m : stdivexcnd S A) pre r :
    getDSPStExc (obsDSP m) pre r <->
      ~ getASLPStExc (obsASLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] Hall] [[s' [Hnp Hr']] | Hall'].
      + exact (Hnp (Hall s' Hr')).
      + exact (Hall' s Hr Hp).
    - intro Hnn. split.
      + apply NNPP. intro Hnex. apply Hnn. right.
        intros s Hr Hp. apply Hnex. exists s. split; [exact Hp | exact Hr].
      + intros s Hr. apply NNPP. intro Hnp. apply Hnn. left.
        exists s. split; [exact Hnp | exact Hr].
  Qed.

End ContrapositiveTransformers.

Section TaxonomySPTransformers.
  Variable S : Type.

   Theorem cc_aslp_implies_asp :
    forall A (m: stdivexcnd S A) pre post,
      tripleASLP m Over pre post ->
      tripleASP m Over pre post.
   Proof. intros A m pre post H r Hasp. apply (H r). left. exact Hasp. Qed.

   Theorem cc_aslp_implies_dslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleASLP m Over pre post ->
      tripleDSLP m Over pre post.
   Proof. intros A m pre post H r Hdslp. apply (H r). right. exact Hdslp. Qed.

   Theorem cc_dslp_implies_dsp :
    forall A (m: stdivexcnd S A) pre post,
      tripleDSLP m Over pre post ->
      tripleDSP m Over pre post.
   Proof. intros A m pre post H r [_ Hdslp]. exact (H r Hdslp). Qed.

   Theorem cc_asp_implies_dsp :
    forall A (m: stdivexcnd S A) pre post,
      tripleASP m Over pre post ->
      tripleDSP m Over pre post.
   Proof. intros A m pre post H r [Hasp _]. exact (H r Hasp). Qed.

   Theorem ii_dsp_implies_dslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleDSP m Under pre post ->
      tripleDSLP m Under pre post.
   Proof. intros A m pre post H r Hpost. exact (proj2 (H r Hpost)). Qed.

   Theorem ii_dslp_implies_aslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleDSLP m Under pre post ->
      tripleASLP m Under pre post.
   Proof. intros A m pre post H r Hpost. right. exact (H r Hpost). Qed.

   Theorem ii_asp_implies_aslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleASP m Under pre post ->
      tripleASLP m Under pre post.
   Proof. intros A m pre post H r Hpost. left. exact (H r Hpost). Qed.

   Theorem ii_dsp_implies_asp :
    forall A (m: stdivexcnd S A) pre post,
      tripleDSP m Under pre post ->
      tripleASP m Under pre post.
   Proof. intros A m pre post H r Hpost. exact (proj1 (H r Hpost)). Qed.

   Theorem ci_aslp_dsp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleASLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleDSP m Under pre post.
   Proof.
     intros A m pre post H r Hpost. split.
     - apply NNPP. intro Hnex. apply (H r); [| exact Hpost]. right.
       intros s Hr Hp. apply Hnex. exists s. split; [exact Hp | exact Hr].
     - intros s Hr. apply NNPP. intro Hnp. apply (H r); [| exact Hpost]. left.
       exists s. split; [exact Hnp | exact Hr].
   Qed.

   Theorem ci_aslp_dsp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleDSP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleASLP m Over pre post.
   Proof.
     intros A m pre post H r Haslp. apply NNPP. intro Hnpost.
     destruct (H r Hnpost) as [[s0 [Hnp Hr0]] Hall].
     destruct Haslp as [[s [Hp Hr]] | Hall2].
     - exact (Hall s Hr Hp).
     - exact (Hnp (Hall2 s0 Hr0)).
   Qed.

     Theorem ci_asp_dslp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleASP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleDSLP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost s Hr.
    apply NNPP. intro Hnpre.
    apply (Hii r); [| exact Hpost].
    exists s. split; [exact Hnpre | exact Hr].
  Qed.

  Theorem ci_asp_dslp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleDSLP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleASP m Over pre post.
  Proof.
    intros A m pre post Hii r [s [Hpre Hr]].
    apply NNPP. intro Hnpost.
    exact (Hii r Hnpost s Hr Hpre).
  Qed.

  (** The other diagonal of the square: a DSLP over-approximation of the
      negated pair is an ASP under-approximation of the original, and back.
      Both readings are the single relational statement
      [forall r, post r -> exists s, pre s /\ reach m s r], reached in each
      direction by [NNPP]. *)
  Theorem ci_dslp_asp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleDSLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleASP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost.
    apply NNPP. intro Hnex.
    apply (Hii r); [| exact Hpost].
    intros s Hr Hpre. apply Hnex. exists s. split; [exact Hpre | exact Hr].
  Qed.

  Theorem ci_dslp_asp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleASP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleDSLP m Over pre post.
  Proof.
    intros A m pre post Hii r Hdslp.
    apply NNPP. intro Hnpost.
    destruct (Hii r Hnpost) as [s [Hnpre Hr]].
    exact (Hnpre (Hdslp s Hr)).
  Qed.
End TaxonomySPTransformers.

(* ==================================================================== *)
(** * Where the WP and SP triples meet                                  *)
(* ==================================================================== *)

Section GaloisConnection.
  Variable S : Type.
  
  (** [obsDWLP] and [obsAWP] applied to a postcondition are the two readings of
      the same terminating slice that [obsASP] / [obsDSLP] use, so the triples
      differ only in the order of the [s] and [r] quantifiers. *)
  Lemma dwlp_slice {A} (m : stdivexcnd S A) (s : S) (p : option (A * S) -> Prop) :
    unOptionT (runStateT (obsDWLP m) s) p
    <-> (forall r, unOptionT (unOptionT (runStateT m s)) (Some r) -> p r).
  Proof.
    cbn. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    cbn. split.
    - intros H r Hr. exact (H (Some r) Hr).
    - intros H oa Hoa. destruct oa as [r|]; [ exact (H r Hoa) | exact I ].
  Qed.

  Lemma awp_slice {A} (m : stdivexcnd S A) (s : S) (p : option (A * S) -> Prop) :
    unOptionT (runStateT (obsAWP m) s) p
    <-> (exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ p r).
  Proof.
    cbn. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    cbn. split; intros [r [Hr Hp]]; exists r; split; assumption.
  Qed.

  Theorem dwlp_asp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWLP m pre SubsetOf post <->
        tripleASP m Over pre post.
  Proof.
    intros A m pre post. split.
    - intros H r [s [Hpre Hr]].
      exact (proj1 (dwlp_slice m s post) (H s Hpre) r Hr).
    - intros H s Hpre. apply dwlp_slice.
      intros r Hr. exact (H r (ex_intro _ s (conj Hpre Hr))).
    Qed.

  Theorem awp_dslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWP m pre SupersetOf post <->
        tripleDSLP m Under pre post.
  Proof.
    intros A m pre post. split.
    - intros H r Hpost s Hr.
      exact (H s (proj2 (awp_slice m s post) (ex_intro _ r (conj Hr Hpost)))).
    - intros H s Hawp.
      destruct (proj1 (awp_slice m s post) Hawp) as [r [Hr Hpost]].
      exact (H r Hpost s Hr).
  Qed.
End GaloisConnection.

(* ==================================================================== *)
(** * A worked example spanning both readings                           *)
(* ==================================================================== *)

From Incorrectness.Taxonomy Require Import ExampleProgramDefs.


(* ================================================================= *)
(** ** Angelic vs. demonic nondeterminism under exceptions            *)
(* ================================================================= *)

(** A withdrawal session that nondeterministically [pick]s an [amount]
    and either throws (when the amount exceeds the balance) or debits the
    balance.  [balance] is the state.

      def withdrawSessionAngelic' returns (u : Unit)
        require balance > 0
        ensures False do
        let mut amount <- pick Nat
        if amount > balance then throw "Insufficient funds"
        else balance := balance - amount
        return

    The exception payload is [unit] (the message is dropped), and [pick
    Nat] is the unbounded-choice combinator [pickP] from [StDivExcNonDet.v].

    "Angelic, [ensures False]": from any positive balance *some* execution
    reaches an acceptable outcome.  A normal return is forbidden
    ([ensures False]); the only acceptable outcome is the exceptional one
    ([None]), so the triple states that the angelic scheduler can always
    drive the session to the [throw].  This is [tripleWP obsAWP _ Under]
    with a postcondition that is [True] on the exception and [False] on
    every normal return.  The [obsDWP] (demonic) reading of the same spec
    is invalid: the demon may pick a small amount and return normally. *)

Module WithdrawExample.

  (** Angelic spec: pick [amount = S balance > balance] to force the
      [raise], so the exceptional outcome [Some None] is reachable. *)
  Theorem progloom_triple :
    tripleWP obsAWP progloom
      (fun balance => balance > 0)
      SubsetOf
      (fun r => match r with Some (tt, _) => False | None => True end).
    Proof.
      intros s Hpos. cbn.
      exists None. split; [| exact I].
      exists (Some (Some (S s, s))). split.
      - exists (S s). reflexivity.
      - cbn. exists (Some (Some (s, s))). split.
        + reflexivity.
        + rewrite Nat.leb_refl. cbn.
      exists (Some None). split; [reflexivity|]. cbn. reflexivity.
    Qed.

  (** Traditional incorrectness reading: under-approximation of [asp],
      with the *same* postcondition as [progloom_triple] (on [option
      (unit * nat)], [match … Some (tt,_) => False | None => True] is
      exactly [r = None]).

      [tripleASP _ Under] is [post ⊆ obsASP(pre)] (∀ asserted output,
      ∃ input): "the throw is reachable from *some* [balance > 0]" —
      O'Hearn-style bug *presence*.  [progloom_triple] is the angelic-total
      WP reading [pre ⊆ awp(post)] (∀ input, ∃ output): "the throw is
      reachable from *every* [balance > 0]" — angelic *coverage*.  Same
      program, same postcondition; only the triple and the quantifier
      order over inputs/outputs differ. *)
  Theorem progloom_triple_asp :
    tripleASP progloom Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
  Proof.
    intros r Hr. destruct r as [[[] n]|]; [ exfalso; exact Hr | ].
    apply getProg_obsASP.
    exists 1. split.
    - exact (ltac:(lia) : 1 > 0).
    - cbn.
      exists (Some (Some (2, 1))). split.
      + exists 2. reflexivity.
      + cbn. exists (Some (Some (1, 1))). split.
        * reflexivity.
        * cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
  Qed.

  (** WP coverage FAILS: the throw is reached iff [balance] is even (the
      picked [amount] is irrelevant), so from an odd [balance] (e.g. [1])
      every branch returns normally and the exception is unreachable —
      [awp(post)] is empty there, breaking [pre ⊆ awp(post)]. *)
  Theorem progloom_triple_harder :
    ~ (tripleWP obsAWP progloom_harder
      (fun balance => balance > 0)
      SubsetOf
      (fun r => match r with Some (tt, _) => False | None => True end)).
  Proof.
    intro H. specialize (H 1 (ltac:(lia) : 1 > 0)). cbn in H.
    destruct H as [r [Hreach Hpost]]. destruct r as [[[] n]|].
    - exact Hpost.
    - destruct Hreach as [a [[amt Ha] Hcont]]. subst a. cbn in Hcont.
      destruct Hcont as [a2 [Ha2 Hcont2]]. subst a2. cbn in Hcont2.
      discriminate Hcont2.
  Qed.

  (** SP incorrectness HOLDS: the throw is still reachable from *some*
      [balance > 0] — pick an even one (e.g. [2]).  Same program and
      postcondition as [progloom_triple_harder]; only the quantifier
      order over inputs differs (∃ input here vs ∀ input there). *)
  Theorem progloom_triple_asp_harder :
    tripleASP progloom_harder Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
  Proof.
    intros r Hr. destruct r as [[[] n]|]; [ exfalso; exact Hr | ].
    apply getProg_obsASP.
    exists 2. split.
    - exact (ltac:(lia) : 2 > 0).
    - cbn.
      exists (Some (Some (0, 2))). split.
      + exists 0. reflexivity.
      + cbn. exists (Some (Some (2, 2))). split.
        * reflexivity.
        * cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
  Qed.
End WithdrawExample.

