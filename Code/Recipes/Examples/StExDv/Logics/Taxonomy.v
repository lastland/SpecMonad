(** * Taxonomy of the sixteen predicate-transformer logics

    This file formalises the black implication arrows, green
    contrapositive equivalences, and orange Galois connections in the
    taxonomy figure.

    The four black WP arrows from a universal transformer to an existential
    one need the standard feasibility assumption: every initial state has at
    least one outcome.  The relational program carrier also admits the empty
    outcome set, so those arrows would be false without this assumption. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.Recipes Require Import DMRecipe.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program PrePost
  Logics.AWP Logics.DWP Logics.DLWP Logics.ALWP
  Logics.ASP Logics.DLSP Logics.DSP Logics.ALSP.

Definition negPred {A} (p : A -> Prop) : A -> Prop :=
  fun x => ~ p x.

Definition Feasible {S A} (m : prog S A) : Prop :=
  forall s, exists oa, unOptionT (unOptionT (runStateT m s)) oa.

(* ==================================================================== *)
(** * Unfolded WP triples                                                *)
(* ==================================================================== *)

Lemma awp_over_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  AWPTriple Over m pre post <->
  forall s, pre s ->
    exists r,
      unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r.
Proof. reflexivity. Qed.

Lemma awp_under_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  AWPTriple Under m pre post <->
  forall s,
    (exists r,
      unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r) ->
    pre s.
Proof. reflexivity. Qed.

Lemma dwp_over_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DWPTriple Over m pre post <->
  forall s, pre s ->
    forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
      match oa with
      | Some r => post r
      | None => False
      end.
Proof. reflexivity. Qed.

Lemma dwp_under_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DWPTriple Under m pre post <->
  forall s,
    (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
      match oa with
      | Some r => post r
      | None => False
      end) ->
    pre s.
Proof. reflexivity. Qed.

Lemma dlwp_over_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DLWPTriple Over m pre post <->
  forall s, pre s ->
    forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
      match oa with
      | Some r => post r
      | None => True
      end.
Proof. reflexivity. Qed.

Lemma dlwp_under_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DLWPTriple Under m pre post <->
  forall s,
    (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
      match oa with
      | Some r => post r
      | None => True
      end) ->
    pre s.
Proof. reflexivity. Qed.

Lemma alwp_over_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ALWPTriple Over m pre post <->
  forall s, pre s ->
    (exists r,
      unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r) \/
    unOptionT (unOptionT (runStateT m s)) None.
Proof. reflexivity. Qed.

Lemma alwp_under_spec {S A} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ALWPTriple Under m pre post <->
  forall s,
    ((exists r,
      unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r) \/
     unOptionT (unOptionT (runStateT m s)) None) ->
    pre s.
Proof. reflexivity. Qed.

(* ==================================================================== *)
(** * Black arrows: simple implications                                  *)
(* ==================================================================== *)

Theorem awp_over_implies_alwp_over {S A} (m : prog S A) pre post :
  AWPTriple Over m pre post -> ALWPTriple Over m pre post.
Proof.
  rewrite awp_over_spec, alwp_over_spec.
  intros H s Hpre. left. exact (H s Hpre).
Qed.

Theorem dwp_over_implies_dlwp_over {S A} (m : prog S A) pre post :
  DWPTriple Over m pre post -> DLWPTriple Over m pre post.
Proof.
  rewrite dwp_over_spec, dlwp_over_spec.
  intros H s Hpre oa Hoa. specialize (H s Hpre oa Hoa).
  destruct oa; [exact H | exact I].
Qed.

Theorem dwp_over_implies_awp_over {S A} (m : prog S A) pre post :
  Feasible m ->
  DWPTriple Over m pre post -> AWPTriple Over m pre post.
Proof.
  rewrite dwp_over_spec, awp_over_spec.
  intros Hfeas H s Hpre. destruct (Hfeas s) as [oa Hoa].
  specialize (H s Hpre oa Hoa). destruct oa as [r|].
  - exists r. split; assumption.
  - contradiction.
Qed.

Theorem dlwp_over_implies_alwp_over {S A} (m : prog S A) pre post :
  Feasible m ->
  DLWPTriple Over m pre post -> ALWPTriple Over m pre post.
Proof.
  rewrite dlwp_over_spec, alwp_over_spec.
  intros Hfeas H s Hpre. destruct (Hfeas s) as [oa Hoa].
  specialize (H s Hpre oa Hoa). destruct oa as [r|].
  - left. exists r. split; assumption.
  - right. exact Hoa.
Qed.

Theorem dlwp_under_implies_dwp_under {S A} (m : prog S A) pre post :
  DLWPTriple Under m pre post -> DWPTriple Under m pre post.
Proof.
  rewrite dlwp_under_spec, dwp_under_spec.
  intros H s Hdwp. apply H. intros oa Hoa.
  specialize (Hdwp oa Hoa). destruct oa; [exact Hdwp | exact I].
Qed.

Theorem alwp_under_implies_awp_under {S A} (m : prog S A) pre post :
  ALWPTriple Under m pre post -> AWPTriple Under m pre post.
Proof.
  rewrite alwp_under_spec, awp_under_spec.
  intros H s Hawp. apply H. left. exact Hawp.
Qed.

Theorem awp_under_implies_dwp_under {S A} (m : prog S A) pre post :
  Feasible m ->
  AWPTriple Under m pre post -> DWPTriple Under m pre post.
Proof.
  rewrite awp_under_spec, dwp_under_spec.
  intros Hfeas H s Hdwp. apply H.
  destruct (Hfeas s) as [oa Hoa].
  specialize (Hdwp oa Hoa). destruct oa as [r|].
  - exists r. split; assumption.
  - contradiction.
Qed.

Theorem alwp_under_implies_dlwp_under {S A} (m : prog S A) pre post :
  Feasible m ->
  ALWPTriple Under m pre post -> DLWPTriple Under m pre post.
Proof.
  rewrite alwp_under_spec, dlwp_under_spec.
  intros Hfeas H s Hdlwp. apply H.
  destruct (Hfeas s) as [oa Hoa].
  specialize (Hdlwp oa Hoa). destruct oa as [r|].
  - left. exists r. split; assumption.
  - right. exact Hoa.
Qed.

Theorem alsp_over_implies_asp_over {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  ALSPTriple Over m pre post -> ASPTriple Over m pre post.
Proof.
  rewrite alsp_over_spec, asp_over_spec.
  intros H r Hasp. apply H. left. exact Hasp.
Qed.

Theorem asp_over_implies_dsp_over {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  ASPTriple Over m pre post -> DSPTriple Over m pre post.
Proof.
  rewrite asp_over_spec, dsp_over_spec.
  intros H r [Hasp _]. exact (H r Hasp).
Qed.

Theorem alsp_over_implies_dlsp_over {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  ALSPTriple Over m pre post -> DLSPTriple Over m pre post.
Proof.
  rewrite alsp_over_spec, dlsp_over_spec.
  intros H r Hdslp. apply H. right. exact Hdslp.
Qed.

Theorem dlsp_over_implies_dsp_over {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DLSPTriple Over m pre post -> DSPTriple Over m pre post.
Proof.
  rewrite dlsp_over_spec, dsp_over_spec.
  intros H r [_ Hdslp]. exact (H r Hdslp).
Qed.

Theorem dsp_under_implies_dlsp_under {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DSPTriple Under m pre post -> DLSPTriple Under m pre post.
Proof.
  rewrite dsp_under_spec, dlsp_under_spec.
  intros H r Hpost. exact (proj2 (H r Hpost)).
Qed.

Theorem dsp_under_implies_asp_under {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DSPTriple Under m pre post -> ASPTriple Under m pre post.
Proof.
  rewrite dsp_under_spec, asp_under_spec.
  intros H r Hpost. exact (proj1 (H r Hpost)).
Qed.

Theorem dlsp_under_implies_alsp_under {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DLSPTriple Under m pre post -> ALSPTriple Under m pre post.
Proof.
  rewrite dlsp_under_spec, alsp_under_spec.
  intros H r Hpost. right. exact (H r Hpost).
Qed.

Theorem asp_under_implies_alsp_under {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  ASPTriple Under m pre post -> ALSPTriple Under m pre post.
Proof.
  rewrite asp_under_spec, alsp_under_spec.
  intros H r Hpost. left. exact (H r Hpost).
Qed.

(* ==================================================================== *)
(** * Green dotted arrows: contrapositive equivalences                   *)
(* ==================================================================== *)

Theorem awp_dlwp_contrapositive {S A} (m : prog S A) pre post :
  AWPTriple Over m pre post <->
  DLWPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite awp_over_spec, dlwp_under_spec.
  unfold negPred. split.
  - intros H s Hdlwp Hpre.
    destruct (H s Hpre) as [r [Hr Hpost]].
    exact (Hdlwp (Some r) Hr Hpost).
  - intros H s Hpre. apply NNPP. intro Hnone.
    apply (H s).
    + intros oa Hoa. destruct oa as [r|]; [|exact I].
      intro Hpost. apply Hnone. exists r. split; assumption.
    + exact Hpre.
Qed.

Theorem alwp_dwp_contrapositive {S A} (m : prog S A) pre post :
  ALWPTriple Over m pre post <->
  DWPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite alwp_over_spec, dwp_under_spec.
  unfold negPred. split.
  - intros H s Hdwp Hpre.
    destruct (H s Hpre) as [[r [Hr Hpost]] | Hdiv].
    + exact (Hdwp (Some r) Hr Hpost).
    + exact (Hdwp None Hdiv).
  - intros H s Hpre. apply NNPP. intro Hnone.
    apply (H s).
    + intros oa Hoa. destruct oa as [r|].
      * intro Hpost. apply Hnone. left. exists r. split; assumption.
      * apply Hnone. right. exact Hoa.
    + exact Hpre.
Qed.

Theorem dwp_alwp_contrapositive {S A} (m : prog S A) pre post :
  DWPTriple Over m pre post <->
  ALWPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite dwp_over_spec, alwp_under_spec.
  unfold negPred. split.
  - intros H s Halwp Hpre.
    destruct Halwp as [[r [Hr Hpost]] | Hdiv].
    + exact (Hpost (H s Hpre (Some r) Hr)).
    + exact (H s Hpre None Hdiv).
  - intros H s Hpre oa Hoa. destruct oa as [r|].
    + apply NNPP. intro Hpost. apply (H s).
      * left. exists r. split; assumption.
      * exact Hpre.
    + apply (H s).
      * right. exact Hoa.
      * exact Hpre.
Qed.

Theorem dlwp_awp_contrapositive {S A} (m : prog S A) pre post :
  DLWPTriple Over m pre post <->
  AWPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite dlwp_over_spec, awp_under_spec.
  unfold negPred. split.
  - intros H s [r [Hr Hpost]] Hpre.
    exact (Hpost (H s Hpre (Some r) Hr)).
  - intros H s Hpre oa Hoa. destruct oa as [r|]; [|exact I].
    apply NNPP. intro Hpost. apply (H s).
    + exists r. split; assumption.
    + exact Hpre.
Qed.

Theorem alsp_dsp_triple_contrapositive {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  ALSPTriple Over m pre post <->
  DSPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite alsp_over_spec, dsp_under_spec.
  unfold negPred. split.
  - intros H r Hpost.
    split.
    + apply NNPP. intro Hnone. apply Hpost, H. right.
      intros s Hr. apply NNPP. intro Hnpre.
      apply Hnone. exists s. split; assumption.
    + intros s Hr Hpre. apply Hpost, H. left.
      exists s. split; assumption.
  - intros H r Halsp. apply NNPP. intro Hpost.
    destruct (H r Hpost) as [Hex Hall].
    destruct Halsp as [[s [Hpre Hr]] | Hpre].
    + exact (Hall s Hr Hpre).
    + destruct Hex as [s [Hnpre Hr]]. exact (Hnpre (Hpre s Hr)).
Qed.

Theorem asp_dlsp_triple_contrapositive {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  ASPTriple Over m pre post <->
  DLSPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite asp_over_spec, dlsp_under_spec.
  unfold negPred. split.
  - intros H r Hpost s Hr Hpre. apply Hpost, H.
    exists s. split; assumption.
  - intros H r Hasp. apply NNPP. intro Hpost.
    destruct Hasp as [s [Hpre Hr]].
    exact (H r Hpost s Hr Hpre).
Qed.

Theorem dlsp_asp_triple_contrapositive {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DLSPTriple Over m pre post <->
  ASPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite dlsp_over_spec, asp_under_spec.
  unfold negPred. split.
  - intros H r Hpost.
    apply NNPP. intro Hnone. apply Hpost, H.
    intros s Hr. apply NNPP. intro Hnpre.
    apply Hnone. exists s. split; assumption.
  - intros H r Hdslp. apply NNPP. intro Hpost.
    destruct (H r Hpost) as [s [Hnpre Hr]].
    exact (Hnpre (Hdslp s Hr)).
Qed.

Theorem dsp_alsp_triple_contrapositive {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DSPTriple Over m pre post <->
  ALSPTriple Under m (negPred pre) (negPred post).
Proof.
  rewrite dsp_over_spec, alsp_under_spec.
  unfold negPred. split.
  - intros H r Hpost.
    destruct (classic (exists s, ~ pre s /\ SP.obsRel m s r)) as [Hex | Hnone].
    + left. exact Hex.
    + right. intros s Hr Hpre. apply Hpost, H. split.
      * exists s. split; assumption.
      * intros t Ht. apply NNPP. intro Hnpre.
        apply Hnone. exists t. split; assumption.
  - intros H r Hdsp. apply NNPP. intro Hpost.
    destruct Hdsp as [Hex Hall].
    destruct (H r Hpost) as [[s [Hnpre Hr]] | Hnpre].
    + exact (Hnpre (Hall s Hr)).
    + destruct Hex as [s [Hpre Hr]]. exact (Hnpre s Hr Hpre).
Qed.

(* ==================================================================== *)
(** * Orange arrows: Galois connections                                  *)
(* ==================================================================== *)

Theorem dlwp_asp_galois {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  DLWPTriple Over m pre post <-> ASPTriple Over m pre post.
Proof.
  rewrite dlwp_over_spec, asp_over_spec.
  split.
  - intros H r [s [Hpre Hr]]. exact (H s Hpre (Some r) Hr).
  - intros H s Hpre oa Hoa. destruct oa as [r|].
    + apply H. exists s. split; assumption.
    + exact I.
Qed.

Theorem awp_dlsp_galois {S A}
  `{defaultStateS : DefaultState S}
  (m : prog S A) pre post :
  AWPTriple Under m pre post <-> DLSPTriple Under m pre post.
Proof.
  rewrite awp_under_spec, dlsp_under_spec.
  split.
  - intros H r Hpost s Hr. apply H. exists r. split; assumption.
  - intros H s [r [Hr Hpost]]. exact (H r Hpost s Hr).
Qed.
