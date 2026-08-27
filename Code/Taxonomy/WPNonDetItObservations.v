(** * WP observations for [nditprog]

    Extracted from the original [NonDetItObservation.v]. *)

From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg ProgFacts WP Pred PredFacts SPost WPred.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

Section NDItObservationWP.

  Variable S : Type.

  (** Demonic WP (total): ALL outcomes must terminate and satisfy
      the postcondition.  Divergence is not acceptable. *)
  Definition obsDWP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            forall oa, outcomes oa ->
                              match oa with
                              | Some r => post r
                              | None => False
                              end
                        end
                    end)).

  (** Demonic WLP (partial): ALL terminating outcomes satisfy the
      postcondition.  Divergence is acceptable. *)
  Definition obsDWLP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            forall oa, outcomes oa ->
                              match oa with
                              | Some r => post r
                              | None => True
                              end
                        end
                    end)).

  (** Angelic WP (total): SOME terminating outcome satisfies the
      postcondition. *)
  Definition obsAWP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            exists r, outcomes (Some r) /\ post r
                        end
                    end)).

  (** Angelic WLP (partial): SOME terminating outcome satisfies the
      postcondition, OR divergence is possible. *)
  Definition obsAWLP {A} (m : nditprog S A) : ProgWP S A :=
    mkStateT
      (fun s => @mkOptionT PureWP _
                 (fun post =>
                    match runStateT m s with
                    | mkOptionT inner =>
                        match inner with
                        | mkOptionT outcomes =>
                            (exists r, outcomes (Some r) /\ post r) \/
                            outcomes None
                        end
                    end)).

  Theorem obsDPCollapse :
    forall {A} (m : nditprog S A) post s0,
      (~ unOptionT (unOptionT (runStateT m s0)) None) ->
      (unOptionT (runStateT (obsDWP m) s0) post <-> unOptionT (runStateT (obsDWLP m) s0) post).
  Proof.
    intros A m post s0 Hnd. cbn.
    destruct (runStateT m s0) as [[outcomes]]. cbn in Hnd.
    split.
    - (* DWP -> DWLP: weaken [False] to [True] in the divergence branch. *)
      intros H oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [exact H | exact I].
    - (* DWLP -> DWP: divergence is unreachable, so its branch is vacuous. *)
      intros H oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [exact H | exfalso; exact (Hnd Hoa)].
  Qed.

  Theorem obsAPCollapse :
    forall {A} (m : nditprog S A) post s0,
      (~ unOptionT (unOptionT (runStateT m s0)) None) ->
      (unOptionT (runStateT (obsAWP m) s0) post <-> unOptionT (runStateT (obsAWLP m) s0) post).
  Proof.
    intros A m post s0 Hnd. cbn.
    destruct (runStateT m s0) as [[outcomes]]. cbn in Hnd.
    split.
    - (* AWP -> AWLP: left-inject the terminating witness. *)
      intro H. left. exact H.
    - (* AWLP -> AWP: the divergence disjunct is ruled out. *)
      intros [H | Hdiv]; [exact H | exfalso; exact (Hnd Hdiv)].
  Qed.

End NDItObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.

(* ================================================================= *)
(** ** WP triples                                                    *)
(* ================================================================= *)

Section WPTriples.

  Inductive approxKindWP := | SubsetOf | SupersetOf.

  Definition tripleWP {S A}
    (obs : nditprog S A -> ProgWP S A)
    (prog : nditprog S A)
    (pre : S -> Prop)
    (kind:approxKindWP)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match kind with
    | SubsetOf =>
        forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | SupersetOf =>
        forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.

  Definition pp2wp_subset {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : ProgWP S A :=
    mkStateT (fun s0 => @mkOptionT PureWP _ (fun p => pre s0 /\ (forall r, post r -> p r))).

  Definition pp2wp_superset {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : ProgWP S A :=
    mkStateT (fun s0 => @mkOptionT PureWP _ (fun p => (forall r, p r -> post r) -> pre s0)). 

  Definition ordProgWP {S A} (m1 m2 : ProgWP S A) : Prop :=
    forall s p, unOptionT (runStateT m1 s) p -> unOptionT (runStateT m2 s) p.

  Definition tripleWPspec {S A}
    (obs : nditprog S A -> ProgWP S A)
    (prog : nditprog S A)
    (pre : S -> Prop)
    (kind:approxKindWP)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match kind with
    | SubsetOf =>
        ordProgWP (pp2wp_subset pre post) (obs prog)
    | SupersetOf =>
        ordProgWP (obs prog) (pp2wp_superset pre post)
    end.

  Section tripleWPDefEq.
    Variable S : Type.
    
    Theorem obsDWLP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsDWLP prog) s) p ->
        unOptionT (runStateT (obsDWLP prog) s) q.
    Proof.
      intros s p q H Hp. unfold obsDWLP in *. cbn [runStateT unOptionT] in *.
      destruct (runStateT prog s) as [[outcomes]]. intros oa Hoa.
      specialize (Hp oa Hoa). destruct oa as [r|]; [|exact I].
      exact (H r Hp).
    Qed.
    
    Theorem obsDWP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsDWP prog) s) p ->
        unOptionT (runStateT (obsDWP prog) s) q.
    Proof.
      intros s p q H Hp. unfold obsDWP in *. cbn [runStateT unOptionT] in *.
      destruct (runStateT prog s) as [[outcomes]]. intros oa Hoa.
      specialize (Hp oa Hoa). destruct oa as [r|]; [exact (H r Hp) | exact Hp].
    Qed.
    
    Theorem obsAWLP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsAWLP prog) s) p ->
        unOptionT (runStateT (obsAWLP prog) s) q.
    Proof.
      intros s p q H Hp. unfold obsAWLP in *. cbn [runStateT unOptionT] in *.
      destruct (runStateT prog s) as [[outcomes]]. destruct Hp as [[r [Hr Hpost]] | Hdiv].
      + left. exists r. split; [exact Hr | exact (H r Hpost)].
      + right. exact Hdiv.
    Qed.
    
    Theorem obsAWP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsAWP prog) s) p ->
        unOptionT (runStateT (obsAWP prog) s) q.
    Proof.
      intros s p q H Hp. unfold obsAWP in *. cbn [runStateT unOptionT] in *.
      destruct (runStateT prog s) as [[outcomes]]. destruct Hp as [r [Hr Hpost]].
      exists r. split; [exact Hr | exact (H r Hpost)].
    Qed.
    
    Theorem tripleWPDefEq {A}
      (obs : nditprog S A -> ProgWP S A)
      (prog : nditprog S A)
      (kind:approxKindWP)
      (pre : S -> Prop)
      (post : option (A * S) -> Prop)
      (Hmono : forall s (p q : option (A * S) -> Prop),
          (forall r, p r -> q r) ->
          unOptionT (runStateT (obs prog) s) p ->
          unOptionT (runStateT (obs prog) s) q) :
      tripleWP obs prog pre kind post <-> tripleWPspec obs prog pre kind post.
    Proof.
      unfold tripleWP, tripleWPspec, ordProgWP, pp2wp_subset, pp2wp_superset.
      destruct kind; cbn [runStateT unOptionT]; split.
      - intros H s p [Hpre Hsub]. apply (Hmono s post p Hsub). exact (H s Hpre).
      - intros H s Hpre. apply (H s post). split; [exact Hpre | intros r hr; exact hr].
      - intros H s p Hwp Hsub. apply H. apply (Hmono s p post Hsub). exact Hwp.
      - intros H s Hwp. apply (H s post Hwp). intros r hr; exact hr.
    Qed.
    
  End tripleWPDefEq.

End WPTriples.

(* ================================================================= *)
(** ** WP observation inclusions (Theorem 3.7)                        *)
(* ================================================================= *)

Section NDItWPInclusions.

  Variable S : Type.

  (** Total demonic <= partial demonic: replace [False] with [True]
      in the divergence branch. *)
  Theorem obsDWP_incl_obsDWLP :
    forall A (m : nditprog S A) s post,
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
    forall A (m : nditprog S A) s post,
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
    forall A (m : nditprog S A) s post,
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
    forall A (m : nditprog S A) s post,
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
    forall A (m : nditprog S A) s post,
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
    forall A (m : nditprog S A) s post,
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWP m pre SubsetOf post ->
      tripleWP obsDWLP m pre SubsetOf post.
  Proof.
    intros A m pre post H s Hpre.
    apply obsDWP_incl_obsDWLP. exact (H s Hpre).
  Qed.

  Theorem cc_dwp_implies_dwlp_spec :
    forall A (m: nditprog S A) pre post,
      tripleWPspec obsDWP m pre SubsetOf post ->
      tripleWPspec obsDWLP m pre SubsetOf post.
  Proof.
    (* Both [Under] specs share the same source [pp2wp_under pre post];
       the implication is the [obsDWP <= obsDWLP] inclusion, pointwise. *)
    intros A m pre post H s p Hp.
    apply obsDWP_incl_obsDWLP. apply H. exact Hp.
  Qed.

  Theorem cc_dwp_implies_awp :
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m pre SubsetOf post ->
      tripleWP obsAWLP m pre SubsetOf post.
  Proof.
    intros A m pre post H s Hpre.
    apply obsAWP_incl_obsAWLP. exact (H s Hpre).
  Qed.

  Theorem cc_dwlp_implies_awlp :
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m pre SupersetOf post ->
      tripleWP obsDWP m pre SupersetOf post.
  Proof.
    intros A m pre post H s Hdwp.
    apply H. apply obsDWP_incl_obsDWLP. exact Hdwp.
  Qed.

  Theorem ii_awlp_implies_awp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWLP m pre SupersetOf post ->
      tripleWP obsAWP m pre SupersetOf post.
  Proof.
    intros A m pre post H s Hawp.
    apply H. apply obsAWP_incl_obsAWLP. exact Hawp.
  Qed.

  Theorem ii_awp_implies_dwp :
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWP obsAWP m pre SubsetOf post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply (proj2 (obsAWP_contrapositive_obsDWLP _ _ m s post)).
    intro Hdwlp. exact (Hii s Hdwlp Hpre).
  Qed.

  Theorem ci_awp_dwlp_contrapositive_spec :
    forall A (m: nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWLP m (fun s => ~ (pre s)) SupersetOf (fun r => ~ (post r)) ->
      tripleWP obsDWP m pre SubsetOf post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply (proj2 (obsDWP_contrapositive_obsAWLP _ _ m s post)).
    intro Hawlp. exact (Hii s Hawlp Hpre).
  Qed.

  Theorem ci_dwp_awlp_contrapositive' :
    forall A (m : nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
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

Section MonadMorphismLawsWP.
  Variable S : Type.

  Lemma outcomes_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) sigma ob :
  unOptionT (unOptionT (runStateT (x >>= f) sigma)) ob <->
  (exists oy, unOptionT (unOptionT (runStateT x sigma)) oy /\
    match oy with
    | Some (Some (a, s')) => unOptionT (unOptionT (runStateT (f a) s')) ob
    | Some None => ob = Some None
    | None => ob = None
    end).
  Proof.
  cbn. split.
  - intros [oy [H1 H2]]. exists oy. split; [exact H1|]. destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  - intros [oy [H1 H2]]. exists oy. split; [exact H1|]. destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  Qed.
  
  Lemma obsDWP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsDWP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsDWP_unfold {A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsDWP m) s) post <->
  (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
              match oa with Some r => post r | None => False end).
  Proof. unfold obsDWP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

  (** WP bind adequacy: the Dijkstra [wp_bind] law (same shape for all four
    WP observations; shown for [obsDWP]).  The [None] branch threads [x]'s
    exception through to [post None]. *)
  Lemma obsDWP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
    unOptionT (runStateT (obsDWP (x >>= f)) s) post <->
    unOptionT (runStateT (obsDWP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWP (f a)) s') post
               | None => post None
               end).
  Proof.
  rewrite (obsDWP_unfold (x >>= f) s post). rewrite (obsDWP_unfold x s _).
  setoid_rewrite outcomes_bind. split.
  - intros HL oy Hoy. destruct oy as [[[a s']|]|].
    + cbn beta iota. rewrite obsDWP_unfold. intros ob Hob.
      apply HL. exists (Some (Some (a, s'))). split; [exact Hoy | exact Hob].
    + apply (HL (Some None)). exists (Some None). split; [exact Hoy | reflexivity].
    + apply (HL None). exists None. split; [exact Hoy | reflexivity].
  - intros HR oa [oy [Hoy Hk]]. specialize (HR oy Hoy). destruct oy as [[[a s']|]|].
    + cbn beta iota in HR. rewrite obsDWP_unfold in HR. exact (HR oa Hk).
    + cbn in Hk. subst oa. exact HR.
    + cbn in Hk. subst oa. destruct HR.
  Qed.

  Lemma obsDWLP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsDWLP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsDWLP_unfold {A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsDWLP m) s) post <->
  (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
              match oa with Some r => post r | None => True end).
  Proof. unfold obsDWLP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

  (** [wp_bind] for demonic-liberal WP. *)
  Lemma obsDWLP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
  unOptionT (runStateT (obsDWLP (x >>= f)) s) post <->
  unOptionT (runStateT (obsDWLP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWLP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsDWLP_unfold (x >>= f) s post). rewrite (obsDWLP_unfold x s _).
  setoid_rewrite outcomes_bind. split.
  - intros HL oy Hoy. destruct oy as [[[a s']|]|].
    + cbn beta iota. rewrite obsDWLP_unfold. intros ob Hob.
      apply HL. exists (Some (Some (a, s'))). split; [exact Hoy | exact Hob].
    + apply (HL (Some None)). exists (Some None). split; [exact Hoy | reflexivity].
    + exact I.
  - intros HR oa [oy [Hoy Hk]]. specialize (HR oy Hoy). destruct oy as [[[a s']|]|].
    + cbn beta iota in HR. rewrite obsDWLP_unfold in HR. exact (HR oa Hk).
    + cbn in Hk. subst oa. exact HR.
    + cbn in Hk. subst oa. exact I.
  Qed.

  Lemma obsAWP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsAWP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsAWP_unfold {A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsAWP m) s) post <->
  (exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r).
  Proof. unfold obsAWP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

  (** [wp_bind] for angelic-total WP. *)
  Lemma obsAWP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
  unOptionT (runStateT (obsAWP (x >>= f)) s) post <->
  unOptionT (runStateT (obsAWP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsAWP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsAWP_unfold (x >>= f) s post). rewrite (obsAWP_unfold x s _). split.
  - intros [r [Hr Hpost]]. apply outcomes_bind in Hr. destruct Hr as [oy [Hoy Hk]].
    destruct oy as [[[a s']|]|].
    + exists (Some (a, s')). split; [exact Hoy|].
      cbn beta iota. rewrite obsAWP_unfold. exists r. split; [exact Hk | exact Hpost].
    + cbn in Hk. injection Hk as Hk. subst r. exists None. split; [exact Hoy|]. cbn beta iota. exact Hpost.
    + cbn in Hk. discriminate Hk.
  - intros [rx [Hrx HQ]]. destruct rx as [[a s']|].
    + cbn beta iota in HQ. rewrite obsAWP_unfold in HQ. destruct HQ as [r [Hr Hpost]].
      exists r. split; [|exact Hpost]. apply outcomes_bind.
      exists (Some (Some (a, s'))). split; [exact Hrx | exact Hr].
    + cbn beta iota in HQ. exists None. split; [|exact HQ]. apply outcomes_bind.
      exists (Some None). split; [exact Hrx | reflexivity].
  Qed.

  Lemma obsAWLP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsAWLP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsAWLP_unfold {A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsAWLP m) s) post <->
  ((exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r)
   \/ unOptionT (unOptionT (runStateT m s)) None).
  Proof. unfold obsAWLP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.
  
  (** [wp_bind] for angelic-liberal WP (the divergence disjunct threads
    through both [x] diverging and [f] diverging after [x] converges). *)
  Lemma obsAWLP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
  unOptionT (runStateT (obsAWLP (x >>= f)) s) post <->
  unOptionT (runStateT (obsAWLP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsAWLP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsAWLP_unfold (x >>= f) s post). rewrite (obsAWLP_unfold x s _). split.
  - intros [[r [Hr Hpost]] | Hdiv].
    + apply outcomes_bind in Hr. destruct Hr as [oy [Hoy Hk]]. destruct oy as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoy|].
        cbn beta iota. rewrite obsAWLP_unfold. left. exists r. split; [exact Hk | exact Hpost].
      * cbn in Hk. injection Hk as Hk. subst r. left. exists None. split; [exact Hoy|]. cbn beta iota. exact Hpost.
      * cbn in Hk. discriminate Hk.
    + apply outcomes_bind in Hdiv. destruct Hdiv as [oy [Hoy Hk]]. destruct oy as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoy|].
        cbn beta iota. rewrite obsAWLP_unfold. right. exact Hk.
      * cbn in Hk. discriminate Hk.
      * right. exact Hoy.
  - intros [[rx [Hrx HQ]] | Hdivx].
    + destruct rx as [[a s']|].
      * cbn beta iota in HQ. rewrite obsAWLP_unfold in HQ. destruct HQ as [[r [Hr Hpost]] | Hdivf].
        -- left. exists r. split; [|exact Hpost]. apply outcomes_bind.
           exists (Some (Some (a, s'))). split; [exact Hrx | exact Hr].
        -- right. apply outcomes_bind. exists (Some (Some (a, s'))). split; [exact Hrx | exact Hdivf].
      * cbn beta iota in HQ. left. exists None. split; [|exact HQ]. apply outcomes_bind.
        exists (Some None). split; [exact Hrx | reflexivity].
    + right. apply outcomes_bind. exists None. split; [exact Hdivx | reflexivity].
  Qed.
End MonadMorphismLawsWP.
