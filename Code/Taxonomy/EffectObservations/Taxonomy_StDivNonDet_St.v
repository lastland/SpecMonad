(** * Taxonomy of the state-only observations of [stdivnd]

    Both halves compare observations rather than defining them.

    [TaxonomyStDivNonDetWSt] covers the WP side: the four observations
    ([obsDWP], [obsDWLP], [obsAWP], [obsAWLP]) defined and proved monad
    morphisms in [WP/StDivNonDet_WSt.v], the inclusions of Theorem 3.7, the
    contrapositive transformers of Theorem 3.8, and the implications between
    the triples they support.

    [TaxonomyStDivNonDetSPSt] covers the SP side: the contrapositive pairs
    among the terminating-slice observations of [SP/StDivNonDet_SPSt.v], and
    the two contrapositive diagonals between the [ASP] and [DSLP] triples. *)

From ExtLib Require Import StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivNonDet_WSt.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.
Import TermSliceObsWP.

Module TaxonomyStDivNonDetWSt.


Section NDObservationComparisons.

  Variable S : Type.

  (* --------------------------------------------------------------- *)
  (** *** Observation inclusions (Theorem 3.7)                         *)
  (* --------------------------------------------------------------- *)

  Theorem obsDWP_incl_obsDWLP {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWP m) s post -> runStateT (obsDWLP m) s post.
  Proof.
    intro H0. apply obsDWLP_unfold.
    pose proof (proj1 (obsDWP_unfold m s post) H0) as H.
    intros oa Hoa. specialize (H oa Hoa). destruct oa; [ exact H | exact I ].
  Qed.

  Theorem obsAWP_incl_obsAWLP {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsAWP m) s post -> runStateT (obsAWLP m) s post.
  Proof.
    intro H. apply obsAWLP_unfold. left. exact (proj1 (obsAWP_unfold m s post) H).
  Qed.

  Theorem obsDWP_incl_obsAWP {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWP m) s post -> runStateT (obsAWP m) s post.
  Proof.
    intro H0. destruct (getNE_nonEmpty S m s) as [oa Hoa]. pose proof (proj1 (obsDWP_unfold m s post) H0) as H.
    apply obsAWP_unfold. destruct oa as [r|].
    - exists r. exact (conj Hoa (H (Some r) Hoa)).
    - exfalso. exact (H None Hoa).
  Qed.

  Theorem obsDWLP_incl_obsAWLP {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWLP m) s post -> runStateT (obsAWLP m) s post.
  Proof.
    intro H0. destruct (getNE_nonEmpty S m s) as [oa Hoa]. pose proof (proj1 (obsDWLP_unfold m s post) H0) as H.
    apply obsAWLP_unfold. destruct oa as [r|].
    - left. exists r. exact (conj Hoa (H (Some r) Hoa)).
    - right. exact Hoa.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Contrapositive transformers (Theorem 3.8)                    *)
  (* --------------------------------------------------------------- *)

  Theorem obsAWP_contrapositive_obsDWLP {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsAWP m) s post <-> ~ runStateT (obsDWLP m) s (fun r => ~ post r).
  Proof.
    cbn. destruct (runStateT (getNE m) s) as [outcomes]. split.
    - intros [r [Hr Hp]] Hdwlp. exact (Hdwlp (Some r) Hr Hp).
    - intro Hnn. apply NNPP. intro Habs. apply Hnn.
      intros oa Hoa. destruct oa as [r|].
      + intro Hp. apply Habs. exists r. exact (conj Hoa Hp).
      + exact I.
  Qed.

  Theorem obsDWP_contrapositive_obsAWLP {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWP m) s post <-> ~ runStateT (obsAWLP m) s (fun r => ~ post r).
  Proof.
    cbn. destruct (runStateT (getNE m) s) as [outcomes]. split.
    - intros Hdwp [[r [Hr Hnp]] | Hdiv].
      + exact (Hnp (Hdwp (Some r) Hr)).
      + exact (Hdwp None Hdiv).
    - intros Hnawlp oa Hoa. destruct oa as [r|].
      + apply NNPP. intro Hnp. apply Hnawlp. left. exists r. exact (conj Hoa Hnp).
      + exfalso. apply Hnawlp. right. exact Hoa.
  Qed.


End NDObservationComparisons.

(* ================================================================= *)
(** ** Taxonomy of WP transformers                                   *)
(* ================================================================= *)

Section NDTaxonomyWP.

  Variable S : Type.

  (** [SubsetOf]: the observation is the conclusion, so the strongest
      transformer gives the strongest triple. *)

  Theorem cc_dwp_implies_dwlp A (m : stdivndNE S A) pre post :
    tripleWP obsDWP m pre SubsetOf post -> tripleWP obsDWLP m pre SubsetOf post.
  Proof. intros H s Hpre. exact (obsDWP_incl_obsDWLP S m s post (H s Hpre)). Qed.

  Theorem cc_awp_implies_awlp A (m : stdivndNE S A) pre post :
    tripleWP obsAWP m pre SubsetOf post -> tripleWP obsAWLP m pre SubsetOf post.
  Proof. intros H s Hpre. exact (obsAWP_incl_obsAWLP S m s post (H s Hpre)). Qed.

  Theorem cc_dwp_implies_awp A (m : stdivndNE S A) pre post :
    tripleWP obsDWP m pre SubsetOf post -> tripleWP obsAWP m pre SubsetOf post.
  Proof.
    intros H s Hpre. exact (obsDWP_incl_obsAWP S m s post (H s Hpre)).
  Qed.

  Theorem cc_dwlp_implies_awlp A (m : stdivndNE S A) pre post :
    tripleWP obsDWLP m pre SubsetOf post -> tripleWP obsAWLP m pre SubsetOf post.
  Proof.
    intros H s Hpre. exact (obsDWLP_incl_obsAWLP S m s post (H s Hpre)).
  Qed.

  (** [SupersetOf]: the observation is a premise, so everything flips. *)

  Theorem ii_dwlp_implies_dwp A (m : stdivndNE S A) pre post :
    tripleWP obsDWLP m pre SupersetOf post -> tripleWP obsDWP m pre SupersetOf post.
  Proof. intros H s Hwp. exact (H s (obsDWP_incl_obsDWLP S m s post Hwp)). Qed.

  Theorem ii_awlp_implies_awp A (m : stdivndNE S A) pre post :
    tripleWP obsAWLP m pre SupersetOf post -> tripleWP obsAWP m pre SupersetOf post.
  Proof. intros H s Hwp. exact (H s (obsAWP_incl_obsAWLP S m s post Hwp)). Qed.

  Theorem ii_awp_implies_dwp A (m : stdivndNE S A) pre post :
    tripleWP obsAWP m pre SupersetOf post -> tripleWP obsDWP m pre SupersetOf post.
  Proof.
    intros H s Hwp. exact (H s (obsDWP_incl_obsAWP S m s post Hwp)).
  Qed.

  Theorem ii_awlp_implies_dwlp A (m : stdivndNE S A) pre post :
    tripleWP obsAWLP m pre SupersetOf post -> tripleWP obsDWLP m pre SupersetOf post.
  Proof.
    intros H s Hwp. exact (H s (obsDWLP_incl_obsAWLP S m s post Hwp)).
  Qed.

  (** Contrapositive diagonals, from Theorem 3.8. *)

  Theorem ci_awp_dwlp_contrapositive A (m : stdivndNE S A) pre post :
    tripleWP obsDWLP m (fun s => ~ pre s) SubsetOf (fun r => ~ post r) ->
    tripleWP obsAWP m pre SupersetOf post.
  Proof.
    intros H s Hawp. apply NNPP. intro Hnpre.
    exact (proj1 (obsAWP_contrapositive_obsDWLP S m s post) Hawp (H s Hnpre)).
  Qed.

  Theorem ci_dwp_awlp_contrapositive A (m : stdivndNE S A) pre post :
    tripleWP obsAWLP m (fun s => ~ pre s) SubsetOf (fun r => ~ post r) ->
    tripleWP obsDWP m pre SupersetOf post.
  Proof.
    intros H s Hdwp. apply NNPP. intro Hnpre.
    exact (proj1 (obsDWP_contrapositive_obsAWLP S m s post) Hdwp (H s Hnpre)).
  Qed.

End NDTaxonomyWP.


End TaxonomyStDivNonDetWSt.

(* ==================================================================== *)
(** * SP side: the terminating-slice observations of [stdivnd]          *)
(* ==================================================================== *)

From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivNonDet_SPSt.

Module TaxonomyStDivNonDetSPSt.
Import StASP StDSLP StDSP StASLP.
Import TermSliceObs.

Section StObservationComparisons.
  Variable S : Type.

  (** The angelic/demonic-liberal contrapositive pair. *)
  Theorem obsASP_contrapositive {A} (m : stdivnd S A) pre r :
    getASPSt (obsASP m) pre r <-> ~ getDSLPSt (obsDSLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [s [Hp Hr]] Hall. exact (Hall s Hr Hp).
    - intro Hnn. apply NNPP. intro Habs. apply Hnn.
      intros s Hr Hp. apply Habs. exists s. split; [ exact Hp | exact Hr ].
  Qed.

  (** Its demonic/angelic-liberal counterpart. *)
  Theorem obsDSP_contrapositive {A} (m : stdivnd S A) pre r :
    getDSPSt (obsDSP m) pre r <-> ~ getASLPSt (obsASLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] Hall] [[s' [Hnp Hr']] | Hall'].
      + exact (Hnp (Hall s' Hr')).
      + exact (Hall' s Hr Hp).
    - intro Hnn. split.
      + apply NNPP. intro Hnex. apply Hnn. right.
        intros s Hr Hp. apply Hnex. exists s. split; [ exact Hp | exact Hr ].
      + intros s Hr. apply NNPP. intro Hnp. apply Hnn. left.
        exists s. split; [ exact Hnp | exact Hr ].
  Qed.

End StObservationComparisons.

Section StTripleTaxonomy.

  (** The two contrapositive diagonals. *)

  Theorem ci_asp_dslp_contrapositive {S A} (m : stdivnd S A) pre post :
    tripleASP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSLP m Under pre post.
  Proof.
    intros Hii r Hpost s Hr. apply NNPP. intro Hnpre.
    apply (Hii r); [| exact Hpost ].
    exists s. split; [ exact Hnpre | exact Hr ].
  Qed.

  Theorem ci_dslp_asp_contrapositive {S A} (m : stdivnd S A) pre post :
    tripleDSLP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASP m Under pre post.
  Proof.
    intros Hii r Hpost. apply NNPP. intro Hnex.
    apply (Hii r); [| exact Hpost ].
    intros s Hr Hpre. apply Hnex. exists s. split; [ exact Hpre | exact Hr ].
  Qed.

End StTripleTaxonomy.

End TaxonomyStDivNonDetSPSt.
