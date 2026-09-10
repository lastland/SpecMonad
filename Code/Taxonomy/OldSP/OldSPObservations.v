From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* Original idea for represent sppts in the PredArr monad *)
(* Problem: observations map from computation monad into
     specification arrow - does not really match the story
     of DM4All - computation monad -> specification monad. *)

Module OriginalTripleSP.

  Section NonDetItObservationSP.

    Variable S : Type.

    Definition obsRel {A} (m : stdivexcnd S A)
    : PredArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      match r with
      | Some (a, s') =>
          unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
      | None =>
          unOptionT (unOptionT (runStateT m s)) (Some None)
      end.

    (** Angelic strongest postcondition (total). *)
    Definition obsASP {A} (m : stdivexcnd S A) : ASPostArr S A :=
      mkASP (obsRel m).

    (** Demonic strongest liberal postcondition. *)
    Definition obsDSLP {A} (m : stdivexcnd S A) : DSLPostArr S A :=
      mkDSLP (obsRel m).

    #[program] Definition obsDSP {A} (m : stdivexcnd S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (obsASP m) pre r /\ sp_pt (obsDSLP m) pre r.

    #[program] Definition obsASLP {A} (m : stdivexcnd S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (obsASP m) pre r \/ sp_pt (obsDSLP m) pre r.

    Inductive approximationKind := | Correct | Incorrect.

    (** Typeclass for coercing an SP observation result to a predicate
    transformer [(unit * S -> Prop) -> option (A * S) -> Prop]:
    - a plain predicate transformer is the identity;
    - [ASPostArr S A] and [DSLPostArr S A] (sigma types) have their
      [sp_pt] extracted;
    - a plain relation [PredArr (unit * S) (option (A * S))] is lifted
      angelically via [asp]. *)
    Class AsSPObs {S A : Type} (T : Type) :=
      as_sp_obs : T -> (unit * S -> Prop) -> option (A * S) -> Prop.

    #[global] Instance AsSPObs_fun {S A} :
      @AsSPObs S A ((unit * S -> Prop) -> option (A * S) -> Prop) :=
      fun obs => obs.

    #[global] Instance AsSPObs_ASP {S A} :
      @AsSPObs S A (ASPostArr S A) :=
      fun d => sp_pt (proj1_sig d).
    
    #[global] Instance AsSPObs_DSLP {S A} :
      @AsSPObs S A (DSLPostArr S A) :=
      fun d => sp_pt (proj1_sig d).
    
    #[global] Instance AsSPObs_Pred {S A} :
      @AsSPObs S A (PredArr (unit * S) (option (A * S))) :=
      fun R => asp R.

    Definition tripleSP {S A T} `{@AsSPObs S A T}
      (obs : stdivexcnd S A -> T)
      (prog : stdivexcnd S A)
      (is_correct : approximationKind)
      (pre : S -> Prop)
      (post : option (A * S) -> Prop)
      : Prop :=
      let pre' := fun '(tt, s) => pre s in
      match is_correct with
      | Correct =>
          forall r, as_sp_obs (obs prog) pre' r -> post r
      | Incorrect =>
          forall r, post r -> as_sp_obs (obs prog) pre' r
      end.

  End NonDetItObservationSP.

End OriginalTripleSP.

(* Came from the observation that the arrow can be represented by
   PredArr A B. However, this requires moving the interpretation of
   whether the observation is angelic or demonic into the triple
   definition. While this seems correct at first (and it is good
   that WPred A is indeed a monad), it means that the inclusions
   between predicate transformers (Theorem 3.7 in the taxonomy paper)
   are not meaningful anymore (since the observation does not produce
   a predicate transformer). *)

Module WPredTripleSP.

  Section NonDetItObservationSP.

    Definition obsRel {S A} (m : stdivexcnd S A)
    : PredArr S (option (A * S)) :=
    fun s r =>
      match r with
      | Some (a, s') => unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
      | None => unOptionT (unOptionT (runStateT m s)) (Some None)
      end.

    Definition obsSP {S A} (m : stdivexcnd S A) : PredStExc S A :=
    mkStateT
      (fun s => @mkOptionT PredM.Pred _ (fun r => (obsRel m) s r)).

    Definition asp' {S A} (sp : PredStExc S A) (pre : S -> Prop) : (option (A * S)) -> Prop :=
      fun b => exists a, pre a /\ (unOptionT (runStateT sp a) b).

    Definition dslp' {S A} (sp : PredStExc S A) (pre : S -> Prop) : (option (A * S)) -> Prop :=
      fun b => forall a, (unOptionT (runStateT sp a) b) -> pre a.

    Inductive approximationKind := | Correct | Incorrect.
    
    Definition tripleASP {S A}
      (obs : stdivexcnd S A -> PredStExc S A) 
      (prog : stdivexcnd S A)
      (is_correct : approximationKind)
      (pre : S -> Prop)
      (post : option (A * S) -> Prop)
      : Prop :=
      match is_correct with
      | Correct => forall r, asp' (obs prog) pre r -> post r
      | Incorrect => forall r, post r -> asp' (obs prog) pre r
      end.
    
  End NonDetItObservationSP.
  
End WPredTripleSP.

(* Came from moving the interpretation of whether the obseration is
   angelic or demonic into the observation definition (instead of
   having it in the triple, as above). However, the monad morphism
   laws do not hold. *)

Section NonDetItObservationSP.

  Variable S : Type.

  (** Reachability relation.

      For [Some (a, s')]: there is a converging path.
      For [None]: there is an exception path.

      Divergence is NOT a reachable final state — it is the absence of
      reaching any final state (dual to how divergence in WP is the
      absence of termination). *)
  Definition obsRel {A} (m : stdivexcnd S A)
    : PredArr S (option (A * S)) :=
    fun s r =>
      match r with
      | Some (a, s') =>
          unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
      | None =>
          unOptionT (unOptionT (runStateT m s)) (Some None)
      end.

  (** The four strongest-postcondition transformers are *readings* of the
      single reachability relation [obsRel] — no [ASPostArr]/[SPRecord]
      wrapping.  [asp] (angelic) and [dslp] (demonic-liberal) come from
      [SPostArr.v], as are [spDSP]/[spASLP] (their meet/join). *)
  Definition obsASP {A} (m : stdivexcnd S A)
    : PredArr (S -> Prop) (option (A * S)) := asp (obsRel m). 
  Definition obsDSLP {A} (m : stdivexcnd S A)
    : PredArr (S -> Prop) (option (A * S)) := dslp (obsRel m).
  Definition obsDSP {A} (m : stdivexcnd S A)
    : PredArr (S -> Prop) (option (A * S)) := fun pre r => asp (obsRel m) pre r /\ dslp (obsRel m) pre r.
  Definition obsASLP {A} (m : stdivexcnd S A)
    : PredArr (S -> Prop) (option (A * S)) := fun pre r => asp (obsRel m) pre r \/ dslp (obsRel m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  Theorem obsDSP_sub_obsASP {A} (m : stdivexcnd S A) pre r :
    obsDSP m pre r -> obsASP m pre r.
  Proof. intros [H _]. exact H. Qed.

  Theorem obsDSP_sub_obsDSLP {A} (m : stdivexcnd S A) pre r :
    obsDSP m pre r -> obsDSLP m pre r.
  Proof. intros [_ H]. exact H. Qed.

  Theorem obsASP_sub_obsASLP {A} (m : stdivexcnd S A) pre r :
    obsASP m pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem obsDSLP_sub_obsASLP {A} (m : stdivexcnd S A) pre r :
    obsDSLP m pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : stdivexcnd S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP. symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : stdivexcnd S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP. symmetry. apply aslp_asp_dslp.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.8: Contrapositive transformers SP               *)
  (* -------------------------------------------------------------- *)

  Theorem obsASP_contrapositive {A} (m : stdivexcnd S A) pre r :
    obsASP m pre r <->
    ~ obsDSLP m (fun x => ~ pre x) r.
  Proof.
    unfold obsASP, obsDSLP, asp, dslp. split.
    - intros [a [Hpre Hrel]] Hall.
      exact (Hall a Hrel Hpre).
    - intro Hnn.
      apply NNPP. intro Habs.
      apply Hnn. intros a Hrel Hpre.
      apply Habs. exists a. exact (conj Hpre Hrel).
  Qed.

  Theorem obsDSP_contrapositive {A} (m : stdivexcnd S A) pre r :
    obsDSP m pre r <->
    ~ obsASLP m (fun x => ~ pre x) r.
  Proof.
    unfold obsDSP, obsASLP, asp, dslp.
    split.
    - intros [[a [Hpre Hrel]] Hall] [Hasp | Hdslp].
      + destruct Hasp as [a' [Hnpre Hrel']].
        exact (Hnpre (Hall a' Hrel')).
      + exact (Hdslp a Hrel Hpre).
    - intro Hnaslp.
      assert (Hnasp : ~ exists a, ~ pre a /\ obsRel m a r)
        by (intro; apply Hnaslp; left; assumption).
      assert (Hndslp : ~ forall a, obsRel m a r -> ~ pre a)
        by (intro; apply Hnaslp; right; assumption).
      split.
      + apply NNPP. intro Habs. apply Hndslp.
        intros a Hrel Hpre. apply Habs.
        exists a. exact (conj Hpre Hrel).
      + intros a Hrel. apply NNPP. intro Hn.
        apply Hnasp. exists a. exact (conj Hn Hrel).
  Qed.

End NonDetItObservationSP.

Arguments obsRel {_} {_}.
Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.

(* ================================================================= *)
(** ** SP triples                                                    *)
(* ================================================================= *)

Inductive approximationKind := | Under | Over.

(** [tripleSP obs prog kind pre post]: apply the SP observation [obs prog]
    (a forward predicate transformer) to the precondition [pre] and compare
    with [post] by inclusion.  [obs] is one of
    [obsASP] / [obsDSLP] / [obsDSP] / [obsASLP] — the four readings of the
    single reachability relation [obsRel]. *)
Definition tripleSP {S A}
  (obs : stdivexcnd S A -> PredArr (S -> Prop) (option (A * S)))
  (prog : stdivexcnd S A)
  (kind : approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop :=
    match kind with
    | Over =>
        forall r, obs prog pre r -> post r
    | Under =>
        forall r, post r -> obs prog pre r
    end.

Definition pp2sp_over {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : PredArr (S -> Prop) (option (A * S)) :=
  fun p r => (forall s, p s -> pre s) -> post r.

Definition pp2sp_under {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : PredArr (S -> Prop) (option (A * S)) :=
  fun p r => (forall s, pre s -> p s) /\ post r.

Definition ordSPStExc {S A} (m1 m2 : PredArr (S -> Prop) (option (A * S))) : Prop :=
  forall pre r, m1 pre r -> m2 pre r.

Definition tripleSPspec {S A}
  (obs : stdivexcnd S A -> PredArr (S -> Prop) (option (A * S)))
  (prog : stdivexcnd S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
  match kind with
  | Over  => ordSPStExc (obs prog) (pp2sp_over pre post)
  | Under => ordSPStExc (pp2sp_under pre post) (obs prog)
  end.

Section tripleSPDefEq.
  Variable S : Type.

  (** The direct ([tripleSP]) and refinement ([tripleSPspec]) SP triples coincide
      exactly when [obs prog] is MONOTONE in the precondition.  [obs] is a
      *forward* transformer, so — dually to [tripleWPDefEq], which needed
      monotonicity in the postcondition — here the auxiliary precondition [p]
      ranges over the down-/up-set of [pre] and we move [sp pre] to [sp p] along
      [p <= pre] / [pre <= p].  Without monotonicity only
      [tripleSPspec -> tripleSP] holds (instantiate [p := pre]). *)
  Theorem tripleSPDefEq {A}
  (obs : stdivexcnd S A -> PredArr (S -> Prop) (option (A * S)))
  (prog : stdivexcnd S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  (Hmono : forall (p q : S -> Prop),
     (forall s, p s -> q s) ->
     forall r, obs prog p r -> obs prog q r) :
    tripleSP obs prog kind pre post <-> tripleSPspec obs prog kind pre post.
  Proof.
    unfold tripleSP, tripleSPspec, ordSPStExc, pp2sp_over, pp2sp_under.
    destruct kind; split.
    - intros H p r [Hsub Hpost]. apply (Hmono pre p Hsub r). apply H. exact Hpost.
    - intros H r Hpost. apply (H pre r). split; [intros s hs; exact hs | exact Hpost].
    - intros H p r Hsp Hsub. apply H. apply (Hmono p pre Hsub r). exact Hsp.
    - intros H r Hsp. apply (H pre r Hsp). intros s hs; exact hs.
  Qed.

End tripleSPDefEq.

Section TaxonomySPTransformers.
  Variable S : Type.

  (** ASLP-Correct implies ASP-Correct: the ASP observation is the
      left disjunct of ASLP, so any postcondition entailed by the
      whole disjunction is entailed by ASP alone. *)
  Theorem cc_aslp_implies_asp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsASLP m Over pre post ->
      tripleSP obsASP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. left. exact Hasp.
  Qed.

  Theorem cc_aslp_implies_dslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsASLP m Over pre post ->
      tripleSP obsDSLP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. apply obsDSLP_sub_obsASLP.
    exact Hasp.
  Qed.

  Theorem cc_dslp_implies_dsp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsDSLP m Over pre post ->
      tripleSP obsDSP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. apply obsDSP_sub_obsDSLP.
    exact Hasp.
  Qed.

  Theorem cc_asp_implies_dsp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsASP m Over pre post ->
      tripleSP obsDSP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. apply obsDSP_sub_obsASP.
    exact Hasp.
  Qed.

  Theorem ii_dsp_implies_dslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsDSP m Under pre post ->
      tripleSP obsDSLP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. exact Hasp.
  Qed.

  Theorem ii_dslp_implies_aslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsDSLP m Under pre post ->
      tripleSP obsASLP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply obsDSLP_sub_obsASLP. apply H.
    exact Hasp.
  Qed.

  Theorem ii_asp_implies_aslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsASP m Under pre post ->
      tripleSP obsASLP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply obsASP_sub_obsASLP. apply H.
    exact Hasp.
  Qed.

  Theorem ii_dsp_implies_asp :
    forall A (m: stdivexcnd S A) pre post,
      tripleSP obsDSP m Under pre post ->
      tripleSP obsASP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. exact Hasp.
  Qed.

  Theorem ci_aslp_dsp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsASLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsDSP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost.
    unfold tripleSP, obsASLP, obsDSP, asp, dslp in *.
    split.
    - apply NNPP. intro Hnasp.
      apply (Hii r); [| exact Hpost].
      right. intros sigma Hrel Hpre. apply Hnasp. exists sigma. split; [exact Hpre | exact Hrel].
    - intros sigma Hrel. apply NNPP. intro Hnpre.
      apply (Hii r); [| exact Hpost].
      left. exists sigma. split; [exact Hnpre | exact Hrel].
  Qed.

  Theorem ci_aslp_dsp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsDSP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsASLP m Over pre post.
  Proof.
    intros A m pre post Hii r Haslp.
    unfold tripleSP, obsDSP, obsASLP, asp, dslp in *.
    apply NNPP. intro Hnpost.
    destruct (Hii r Hnpost) as [Hasp_neg Hdslp_neg].
    destruct Haslp as [[sigma [Hpre Hrel]] | Hdp].
    - exact (Hdslp_neg sigma Hrel Hpre).
    - destruct Hasp_neg as [sigma [Hnpre Hrel]]. exact (Hnpre (Hdp sigma Hrel)).
  Qed.

  Theorem ci_asp_dslp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsASP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsDSLP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost.
    unfold tripleSP, obsASP, obsDSLP, asp, dslp in *.
    intros sigma Hrel. apply NNPP. intro Hnpre.
    apply (Hii r); [| exact Hpost].
    exists sigma. split; [exact Hnpre | exact Hrel].
  Qed.

  Theorem ci_asp_dslp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsDSLP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsASP m Over pre post.
  Proof.
    intros A m pre post Hii r Hasp.
    unfold tripleSP, obsASP, obsDSLP, asp, dslp in *.
    destruct Hasp as [sigma [Hpre Hrel]].
    apply NNPP. intro Hnpost.
    exact ((Hii r Hnpost) sigma Hrel Hpre).
  Qed.

  Theorem ci_dslp_asp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsDSLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsASP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost.
    unfold tripleSP, obsASP, obsDSLP, asp, dslp in *.
    apply NNPP. intro Hnasp.
    apply (Hii r); [| exact Hpost].
    intros sigma Hrel Hpre. apply Hnasp. exists sigma. split; [exact Hpre | exact Hrel].
  Qed.

  Theorem ci_dslp_asp_contrapositive' :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsASP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsDSLP m Over pre post.
  Proof.
    intros A m pre post Hii r Hdslp.
    apply NNPP. intro Hnpost.
    unfold tripleSP, obsASP, obsDSLP, asp, dslp in *.
    destruct (Hii r Hnpost) as [sigma [Hnpre Hrel]].
    exact (Hnpre (Hdslp sigma Hrel)).
  Qed.

   Theorem ci_dsp_aslp_contrapositive :
    forall A (m : stdivexcnd S A) pre post,
      tripleSP obsDSP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleSP obsASLP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost.
    unfold tripleSP, obsDSP, obsASLP, asp, dslp in *.
    apply NNPP. intro Hn.
    apply (Hii r); [| exact Hpost].
    split.
    - apply NNPP. intro Hnasp_neg.
      apply Hn. right. intros sigma Hrel. apply NNPP. intro Hnpre.
      apply Hnasp_neg. exists sigma. split; [exact Hnpre | exact Hrel].
    - intros sigma Hrel Hpre.
      apply Hn. left. exists sigma. split; [exact Hpre | exact Hrel].
  Qed.

   Theorem ci_dsp_aslp_contrapositive' :
     forall A (m : stdivexcnd S A) pre post,
       tripleSP obsASLP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
       tripleSP obsDSP m Over pre post.
  Proof.
    intros A m pre post Hii r Hdsp.
    unfold tripleSP, obsDSP, obsASLP, asp, dslp in *.
    destruct Hdsp as [Hasp Hdslp].
    apply NNPP. intro Hnpost.
    destruct (Hii r Hnpost) as [[sigma [Hnpre Hrel]] | Hdp_neg].
    - exact (Hnpre (Hdslp sigma Hrel)).
    - destruct Hasp as [sigma [Hpre Hrel]]. exact (Hdp_neg sigma Hrel Hpre).
  Qed.
End TaxonomySPTransformers.


Section TaxonomyGaloisConnections.
  Variable S : Type.

  (** [obsRel] is exactly the terminating ([Some _]) slice of the
      outcome set: divergence ([None]) is never an [obsRel] reacher. *)
  Lemma obsRel_outcomes {A} (m : stdivexcnd S A) s r :
    obsRel m s r = unOptionT (unOptionT (runStateT m s)) (Some r).
  Proof. unfold obsRel. destruct r as [[a s']|]; reflexivity. Qed.

  (** GaloisArr connection (correctness side): the demonic-liberal WP
      observation and the angelic SP observation induce the same
      [Correct] triples.

      Unfolded, the WP side reads
        [forall s p, (pre s /\ (forall r, post r -> p r))
                       -> (forall r, obsRel m (tt,s) r -> p r)]
      (the divergence branch of [obsDWLP] is identically [True]), and
      the SP side reads
        [forall r, (exists s, pre s /\ obsRel m (tt,s) r) -> post r].

      [<-]: feed the existential witness [(s, pre s, reach)] to the SP
      hypothesis after weakening [p] via [post r -> p r].
      [->]: instantiate the WP hypothesis at [p := post]; its second
      antecedent becomes reflexivity. *)
  Theorem dwlp_asp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsDWLP m pre SubsetOf post <->
        tripleSP obsASP m Over pre post.
  Proof.
    intros A m pre post.
    unfold tripleWP, tripleSP, obsDWLP,
           obsASP.
    unfold asp.
    split.
    - (* SP-ASP-Correct from WP-DWLP-Correct *)
      intros Hwp r [s [Hpre Hrel]].
      rewrite obsRel_outcomes in Hrel.
      specialize (Hwp s Hpre). cbn in Hwp.
      destruct (runStateT m s) as [[outcomes]]. cbn in Hwp, Hrel.
      apply (Hwp (Some r) Hrel).
    - (* WP-DWLP-Correct from SP-ASP-Correct *)
      intros Hsp s Hpre. cbn.
      destruct (runStateT m s) as [[outcomes]] eqn:Hm.
      intros oa Hoa. destruct oa as [r|]; [|exact I].
      apply (Hsp r). exists s. split; [exact Hpre|].
      rewrite obsRel_outcomes, Hm. cbn. exact Hoa.
  Qed.

  (** GaloisArr connection (incorrectness side) — the connection
      [awp⟦m⟧(c) ⊆ b  iff  c ⊆ dslp⟦m⟧(b)] introduced by Zhang &
      Kaminski (OOPSLA 2022) and depicted in Verscht & Kaminski's
      Fig. 5.

      With the *exegesis-style* triple ([tripleWP ... Incorrect] reads
      [awp(post) ⊆ pre], [tripleSP obsDSLP ... Incorrect] reads
      [post ⊆ dslp(pre)]), both sides unfold to the single relational
      condition

        [forall s r, obsRel m (tt,s) r -> post r -> pre s],

      so the connection holds *unconditionally* (no determinism /
      reachability / non-emptiness side conditions are needed — those
      were artefacts of the old [pp2wp] refinement encoding, under which
      [tripleWP obsAWP _ Over] degenerated). *)
  Theorem awp_dslp :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWP m pre SupersetOf post <->
        tripleSP obsDSLP m Under pre post.
  Proof.
    intros A m pre post.
    unfold tripleWP, tripleSP, obsDSLP, obsAWP.
    unfold dslp.
    split.
    - (* awp(post) ⊆ pre  ->  post ⊆ dslp(pre) *)
      intros Hawp r Hpost s Hrel.
      rewrite obsRel_outcomes in Hrel.
      apply Hawp. cbn.
      destruct (runStateT m s) as [[outcomes]]. cbn in Hrel |- *.
      exists r. split; [exact Hrel | exact Hpost].
    - (* post ⊆ dslp(pre)  ->  awp(post) ⊆ pre *)
      intros Hsp s Hawp. cbn in Hawp.
      destruct (runStateT m s) as [[outcomes]] eqn:Hm. cbn in Hawp.
      destruct Hawp as [r [Hr Hpost]].
      apply (Hsp r Hpost s).
      rewrite obsRel_outcomes, Hm. cbn. exact Hr.
  Qed.

  (** The [->] direction in isolation (kept for use by the taxonomy
      implications below). *)
  Theorem awp_implies_dslp_inc :
    forall A (m: stdivexcnd S A) pre post,
      tripleWP obsAWP m pre SupersetOf post ->
        tripleSP obsDSLP m Under pre post.
  Proof. intros A m pre post; apply awp_dslp. Qed.

End TaxonomyGaloisConnections.

Section TripleDefinitions.
  Variable S : Type.
  
  (* UNDER *)
   
  Theorem dwlp_under {A} :
    forall (m : stdivexcnd S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsDWLP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsDWLP m) s) p).
  Proof.
    intros m pre post. split.
    - intros H s p [Hpre Hsub]. specialize (H s Hpre).

      exact (obsDWLP_mono _ m s post p Hsub H).
    - intros H s Hpre.
      apply (H s post). split; [exact Hpre | intros r hr; exact hr].
  Qed.

    Theorem awlp_under {A} :
    forall (m : stdivexcnd S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsAWLP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsAWLP m) s) p).
    Proof.
      intros m pre post. split.
      - intros H s p [Hpre Hsub]. specialize (H s Hpre).

        exact (obsAWLP_mono _ m s post p Hsub H).
      - intros H s Hpre.
        apply (H s post). split; [exact Hpre | intros r hr; exact hr].
    Qed.

    Theorem dwp_under {A} :
    forall (m : stdivexcnd S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsDWP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsDWP m) s) p).
    Proof.
      intros m pre post. split.
      - intros H s p [Hpre Hsub]. specialize (H s Hpre).

        exact (obsDWP_mono _ m s post p Hsub H).
      - intros H s Hpre.
        apply (H s post). split; [exact Hpre | intros r hr; exact hr].
    Qed.

    Theorem awp_under {A} :
    forall (m : stdivexcnd S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsAWP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsAWP m) s) p).
    Proof.
      intros m pre post. split.
      - intros H s p [Hpre Hsub]. specialize (H s Hpre).

        exact (obsAWP_mono _ m s post p Hsub H).
      - intros H s Hpre.
        apply (H s post). split; [exact Hpre | intros r hr; exact hr].
    Qed.

    (* OVER *)
    (** Curried [Over] form: [wp p s] alone is the antecedent, implying the
        rest [(p <= post) -> pre s].  The order constraint [p <= post] is a
        guard on the conclusion (not a conjunct to establish), which is what
        makes this hold — cf. the failing naive form in [dwlp_breaks]. *)
    Theorem dwlp_over {A} :
      forall (m : stdivexcnd S A) pre post,
        (forall s, unOptionT (runStateT (obsDWLP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsDWLP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.

        exact (obsDWLP_mono _ m s p post Hsub Hp).
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.

    Theorem awlp_over {A} :
      forall (m : stdivexcnd S A) pre post,
        (forall s, unOptionT (runStateT (obsAWLP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsAWLP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.

        exact (obsAWLP_mono _ m s p post Hsub Hp).
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.

    Theorem dwp_over {A} :
      forall (m : stdivexcnd S A) pre post,
        (forall s, unOptionT (runStateT (obsDWP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsDWP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.

        exact (obsDWP_mono _ m s p post Hsub Hp).
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.
    
    Theorem awp_over {A} :
      forall (m : stdivexcnd S A) pre post,
        (forall s, unOptionT (runStateT (obsAWP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsAWP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.

        exact (obsAWP_mono _ m s p post Hsub Hp).
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.
End TripleDefinitions.

Section MonadMorphismLawsSP.
  Variable S : Type. 

  Lemma obsRel_ret {A} (a : A) (s : S) :
    obsRel (ret a) s (Some (a, s)).
  Proof. sauto. Qed.
  
(** SP bind adequacy: [obsRel] composes as a Kleisli arrow (state +
    exception). *)
  Lemma obsRel_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) sigma r :
  obsRel (x >>= f) sigma r <->
  (exists a s', obsRel x sigma (Some (a, s')) /\ obsRel (f a) s' r)
  \/ (obsRel x sigma None /\ r = None).
  Proof.
  unfold obsRel. destruct r as [[b s'']|]; rewrite outcomes_bind; split.
  - intros [oy [Hx Hk]]. destruct oy as [[[a s']|]|].
    + left. exists a, s'. split; [exact Hx | exact Hk].
    + cbn in Hk; discriminate Hk.
    + cbn in Hk; discriminate Hk.
  - intros [[a [s' [Hx Hf]]] | [_ Heq]].
    + exists (Some (Some (a, s'))). split; [exact Hx | exact Hf].
    + discriminate Heq.
  - intros [oy [Hx Hk]]. destruct oy as [[[a s']|]|].
    + left. exists a, s'. split; [exact Hx | exact Hk].
    + right. split; [exact Hx | reflexivity].
    + cbn in Hk; discriminate Hk.
  - intros [[a [s' [Hx Hf]]] | [Hx _]].
    + exists (Some (Some (a, s'))). split; [exact Hx | exact Hf].
    + exists (Some None). split; [exact Hx | reflexivity].
  Qed.

  Theorem obsASP_ret {A} (a : A) (pre : S -> Prop) :
    forall s, pre s -> obsASP (ret a) pre (Some (a, s)).
  Proof. sauto. Qed.
  
  (** The derived sequencing rule for the angelic strongest postcondition:
      the [asp] reading of [obsRel_bind].  Existential over the initial
      state commutes with [bind]'s disjunction (turning [exists sigma, pre
      sigma /\ obsRel x sigma _] back into [obsASP x pre _]); on a normal
      intermediate outcome [Some (a, s')] the continuation is observed at
      the *singleton* precondition [eq s'] — [asp] re-localizing the
      precondition to the exact intermediate state (via [asp_singleton]). *)
  Theorem obsASP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B)
          (pre : S -> Prop) (r : option (B * S)) :
    obsASP (x >>= f) pre r <->
    (exists a s', obsASP x pre (Some (a, s')) /\ obsASP (f a) (eq s') r)
    \/ (obsASP x pre None /\ r = None).
  Proof.
    unfold obsASP. split.
    - intros [sigma [Hpre Hrel]].
      apply obsRel_bind in Hrel as [[a [s' [Hx Hf]]] | [Hx Heq]].
      + left. exists a, s'. split.
        * exists sigma. split; [exact Hpre | exact Hx].
        * apply (proj2 (asp_singleton _ _ _)). exact Hf.
      + right. split; [ exists sigma; split; [exact Hpre | exact Hx] | exact Heq ].
    - intros [[a [s' [[sigma [Hpre Hx]] Hf]]] | [[sigma [Hpre Hx]] Heq]].
      + apply (proj1 (asp_singleton _ _ _)) in Hf.
        exists sigma. split; [exact Hpre|].
        apply obsRel_bind. left. exists a, s'. split; [exact Hx | exact Hf].
      + exists sigma. split; [exact Hpre|].
        apply obsRel_bind. right. split; [exact Hx | exact Heq].
  Qed.

  (** *** [obsASP] preserves [ret]/[bind] — but its codomain is not a monad

      The two preceding laws are [obsASP]'s [bind]-preservation; together
      with [obsASP_retG] below they are the monad-morphism *equations* for
      [obsASP : stdivexcnd S A -> PredArr (S -> Prop) (option (A * S))], against
      the unit [retG] and bind [bindG] forced by [obsASP_bind].

      They do NOT promote [obsASP] to a genuine monad morphism, because
      [(PredArr (S -> Prop) (option (_ * S)), retG, bindG)] is not a lawful
      monad: [bindG] feeds the continuation the *singleton* precondition
      [eq s'], so it only sees a continuation through its values on
      singletons, and the left-unit law [bindG (retG a) k ≈ k a] fails
      unless [k a] is [asp]-closed (determined by its singletons —
      [asp_singleton]).  Every [obsASP m] *is* [asp]-closed
      ([obsASP_asp_closed]), so [obsASP] factors through the lawful
      sub-monad of [asp]-closed relations — which is exactly [obsRelM]
      (below) up to the iso [asp]/[asp_inv].  Hence the genuine monad
      morphism is [obsRelM], and [obsASP = asp ∘ obsRel] inherits only the
      equations. *)
  Definition retG {A} (a : A) : PredArr (S -> Prop) (option (A * S)) :=
    fun pre r => exists s, pre s /\ r = Some (a, s).

  Definition bindG {A B}
    (m : PredArr (S -> Prop) (option (A * S)))
    (k : A -> PredArr (S -> Prop) (option (B * S)))
    : PredArr (S -> Prop) (option (B * S)) :=
    fun pre r =>
      (exists a s', m pre (Some (a, s')) /\ k a (eq s') r)
      \/ (m pre None /\ r = None).

  (** Unit law: [obsASP (ret a) ≈ retG a] (the full characterization; the
      [obsASP_ret] above is just its [Some]-direction soundness half). *)
  Lemma obsASP_retG {A} (a : A) :
    forall pre r, obsASP (ret a : stdivexcnd S A) pre r <-> retG a pre r.
  Proof.
    unfold obsASP, asp, retG. intros pre r. split.
    - intros [s [Hpre Hrel]]. exists s. split; [exact Hpre|].
      unfold obsRel in Hrel. destruct r as [[b s']|]; cbn in Hrel; congruence.
    - intros [s [Hpre ->]]. exists s. split; [exact Hpre|].
      unfold obsRel. cbn. reflexivity.
  Qed.

  (** Bind law restated through [bindG] (a repackaging of [obsASP_bind]). *)
  Lemma obsASP_bindG {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    forall pre r,
      obsASP (x >>= f) pre r <-> bindG (obsASP x) (fun a => obsASP (f a)) pre r.
  Proof. intros pre r. apply obsASP_bind. Qed.

  (** Every [obsASP] output is [asp]-closed: determined by its singletons.
      This is what lands [obsASP] in the lawful sub-monad. *)
  Lemma obsASP_asp_closed {A} (m : stdivexcnd S A) (pre : S -> Prop) r :
    obsASP m pre r <-> exists s, pre s /\ obsASP m (eq s) r.
  Proof.
    unfold obsASP, asp. split.
    - intros [s [Hpre Hrel]]. exists s. split; [exact Hpre|]. exists s. auto.
    - intros [s [Hpre [s' [-> Hrel]]]]. exists s'. auto.
  Qed.

End MonadMorphismLawsSP.


(* ================================================================= *)
(** ** [obsASP]'s ret/bind laws by conjugation through an injective reading *)
(* ================================================================= *)

(** This makes precise the claim: the reachability monad morphism is *enough*.
    The SP ret/bind equations for [obsASP] need NOT be proved directly; they
    are the reachability-level laws ([obsRel_ret] / [obsRel_bind], the [tt]-slice
    of the [obsRelM] monad morphism) *conjugated* by the reading [asp] and its
    retract [asp_inv].  The only property of the reading used is its
    injectivity, [asp_asp_inv : asp_inv (asp R) = R].  (For a non-injective
    reading — e.g. [obsDSP = asp /\ dslp] — [asp_inv] has no analogue and this
    transport fails.) *)
(*Section AspConjugation.
  Variable S : Type.

  (** Reachability-level (relation) [ret]/[bind] — the bind is exactly the RHS
      of [obsRel_bind] (state-threaded, exception-propagating). *)
  Definition retRel {A} (a : A) : PredArr S (option (A * S)) :=
    fun s r => r = Some (a, s).
  Definition bindRel {A B}
    (m : PredArr S (option (A * S))) (k : A -> PredArr S (option (B * S)))
    : PredArr S (option (B * S)) :=
    fun s r =>
      (exists a s', m s (Some (a, s')) /\ k a s' r) \/ (m s None /\ r = None).

  (** SP-level [ret]/[bind], DEFINED by conjugation:
      [bindSP = asp ∘ bindRel ∘ asp_inv]. *)
  Definition retSP {A} (a : A) : PredArr (S -> Prop) (option (A * S)) :=
    asp (retRel a).
  Definition bindSP {A B}
    (m : PredArr (S -> Prop) (option (A * S)))
    (k : A -> PredArr (S -> Prop) (option (B * S)))
    : PredArr (S -> Prop) (option (B * S)) :=
    asp (bindRel (asp_inv m) (fun a => asp_inv (k a))).

  (** [asp] and [bindRel] are congruences for pointwise equivalence. *)
  Lemma asp_Proper {A} (R1 R2 : PredArr S (option (A * S))) :
    (forall s r, R1 s r <-> R2 s r) ->
    forall pre r, asp R1 pre r <-> asp R2 pre r.
  Proof.
    intros H pre r. unfold asp. split.
    - intros [s [Hp Hr]]. exists s. split; [exact Hp | exact (proj1 (H s r) Hr)].
    - intros [s [Hp Hr]]. exists s. split; [exact Hp | exact (proj2 (H s r) Hr)].
  Qed.

  Lemma bindRel_Proper {A B} (m1 m2 : PredArr S (option (A * S)))
    (k1 k2 : A -> PredArr S (option (B * S))) :
    (forall s r, m1 s r <-> m2 s r) ->
    (forall a s r, k1 a s r <-> k2 a s r) ->
    forall s r, bindRel m1 k1 s r <-> bindRel m2 k2 s r.
  Proof.
    intros Hm Hk s r. unfold bindRel. split.
    - intros [[a [s' [Hms Hk1]]] | [Hms Heq]].
      + left. exists a, s'.
        split; [ exact (proj1 (Hm s (Some (a, s'))) Hms) | exact (proj1 (Hk a s' r) Hk1) ].
      + right. split; [ exact (proj1 (Hm s None) Hms) | exact Heq ].
    - intros [[a [s' [Hms Hk2]]] | [Hms Heq]].
      + left. exists a, s'.
        split; [ exact (proj2 (Hm s (Some (a, s'))) Hms) | exact (proj2 (Hk a s' r) Hk2) ].
      + right. split; [ exact (proj2 (Hm s None) Hms) | exact Heq ].
  Qed.

  (** THE TRANSPORT LEMMA.  Any reachability bind law [rxf ≈ bindRel rx kf]
      is carried, by the injective reading [asp], to the SP bind law
      [asp rxf ≈ bindSP (asp rx) (asp ∘ kf)].  The proof is pure conjugation:
      unfold [bindSP], cancel [asp_inv ∘ asp] via [asp_asp_inv]. *)
  Lemma asp_conj_bind {A B}
    (rxf : PredArr S (option (B * S)))
    (rx : PredArr S (option (A * S)))
    (kf : A -> PredArr S (option (B * S))) :
    (forall s r, rxf s r <-> bindRel rx kf s r) ->
    forall pre r,
      asp rxf pre r <-> bindSP (asp rx) (fun a => asp (kf a)) pre r.
  Proof.
    intros Hrel pre r. unfold bindSP.
    assert (Hcong : forall s r0,
              bindRel rx kf s r0 <->
              bindRel (asp_inv (asp rx)) (fun a => asp_inv (asp (kf a))) s r0).
    { apply bindRel_Proper.
      - intros s r0. symmetry. apply asp_asp_inv.
      - intros a s r0. symmetry. apply asp_asp_inv. }
    pose proof (asp_Proper _ _ Hrel pre r) as H1.
    pose proof (asp_Proper _ _ Hcong pre r) as H2.
    tauto.
  Qed.

  (** [ret] is transported the same way (no [bindRel] needed). *)
  Lemma obsRel_ret_iff {A} (a : A) s r :
    obsRel (ret a) s r <-> retRel a s r.
  Proof. unfold obsRel, retRel. destruct r as [[b s']|]; cbn; split; intro H; congruence. Qed.

  (* ---- Instantiation: [obsASP]'s ret/bind equations, DERIVED ---- *)

  Lemma obsASP_ret_conj {A} (a : A) pre r :
    obsASP (ret a) pre r <-> retSP a pre r.
  Proof.
    unfold obsASP, retSP. apply asp_Proper. intros s r0. apply obsRel_ret_iff.
  Qed.

  Lemma obsASP_bind_conj {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) pre r :
    obsASP (x >>= f) pre r <->
    bindSP (obsASP x) (fun a => obsASP (f a)) pre r.
  Proof.
    unfold obsASP.
    apply (asp_conj_bind (obsRel (x >>= f)) (obsRel x) (fun a => obsRel (f a))).
    intros s r0. apply obsRel_bind.
  Qed.

End AspConjugation.

(* ----------------------------------------------------------------- *)
(** *** Monad-view SP observation: a genuine monad morphism           *)
(* ----------------------------------------------------------------- *)

(** The [obsRel]/[obsASP] above are the *arrow*/reading view, used to
    state triples; they are not inhabitants of a [Monad] (and the [asp]
    reading would target the flagged-incorrect [SPStExc]).  Here is the
    *monad-view* observation [obsRelM : stdivexcnd S A -> nditPredM S A]
    into the spec monad [nditPredM = stateT S (optionT (optionT (PredArr
    unit)))] (the SP mirror of [WStExc], with base [PredArr unit] instead of
    [SetM]; lawful [Monad] + [MonadLawsE] via [PredArr.v]).  It is the
    lifting along the base iso [SetM ~ PredArr unit] — it copies [stdivexcnd]'s
    full outcome predicate (divergence included) into [PredArr unit].

    [obsRelM] is a genuine monad morphism: [obsRelM_ret] and [obsRelM_bind]
    are its unit/bind laws, stated as [eq1] ([≈]) in [nditPredM] — purely
    in terms of the monads' [ret] / [>>=], with no [asp]/[∃]/[=] unfolding.
    (These are the clean statements that [obsASP (ret a) = ret a] could
    not be, because [obsASP] is a reading, not a monad element.) *)

Section ObsRelM.
  Variable S : Type.

  #[local] Existing Instance Monad_stateT.
  #[local] Existing Instance Monad_optionT.

  (** Codomain is definitionally [nditPredM S A]. *)
  Definition obsRelM {A} (m : stdivexcnd S A)
    : stateT S (optionT (optionT (PredArr unit))) A :=
    mkStateT (fun s =>
      @mkOptionT (optionT (PredArr unit)) (A * S) (
        @mkOptionT (PredArr unit) (option (A * S)) (
          fun (_ : unit) (oa : option (option (A * S))) =>
            unOptionT (unOptionT (runStateT m s)) oa))).

  (** *** Connection to the arrow-view observations [obsRel] / [obsASP] *)

  (** [obsRelM] applied is just [stdivexcnd]'s raw outcome predicate (the
      [unit] slot is ignored) — the [obsX_unfold]-style accessor. *)
  Lemma obsRelM_apply {A} (m : stdivexcnd S A) s u oa :
    unOptionT (unOptionT (runStateT (obsRelM m) s)) u oa
    <-> unOptionT (unOptionT (runStateT m s)) oa.
  Proof. unfold obsRelM. cbn. tauto. Qed.

  (** Hence the arrow-view [obsRel] (and so every SP reading [obsASP =
      asp (obsRel _)], [obsDSLP], [obsDSP], [obsASLP]) is exactly the
      *terminating-slice* reading of [obsRelM] at [tt]: drop divergence,
      keep the [Some r] outcomes.  So [obsRelM] is the monad morphism and
      the observations used in triples are its readings. *)
  Lemma obsRel_obsRelM {A} (m : stdivexcnd S A) s r :
    obsRel m s r <-> unOptionT (unOptionT (runStateT (obsRelM m) s)) tt (Some r).
  Proof. rewrite obsRelM_apply. unfold obsRel. destruct r as [[a s']|]; tauto. Qed.

  (* -------------------------------------------------------------- *)
  (** *** The SP observations as readings of the reachability monad *)
  (* -------------------------------------------------------------- *)

  (** [reach] extracts the reachability *relation* from an element of the
      reachability monad [nditPredM S A = stateT S (optionT (optionT (PredArr
      unit)))]: the terminating ([Some r]) outcomes read off at the trivial
      [tt] precondition slot. *)
  Definition reach {A} (M : stateT S (optionT (optionT (PredArr unit))) A)
    : PredArr S (option (A * S)) :=
    fun s r => unOptionT (unOptionT (runStateT M s)) tt (Some r).

  (** The four strongest-postcondition readings, as functions of a
      reachability-monad element: [asp] (angelic), [dslp] (demonic-liberal),
      and their meet ([DSP]) and join ([ASLP]). *)
  Definition readASP {A} (M : stateT S (optionT (optionT (PredArr unit))) A)
    : PredArr (S -> Prop) (option (A * S)) := asp (reach M).
  Definition readDSLP {A} (M : stateT S (optionT (optionT (PredArr unit))) A)
    : PredArr (S -> Prop) (option (A * S)) := dslp (reach M).
  Definition readDSP {A} (M : stateT S (optionT (optionT (PredArr unit))) A)
    : PredArr (S -> Prop) (option (A * S)) :=
    fun pre r => asp (reach M) pre r /\ dslp (reach M) pre r.
  Definition readASLP {A} (M : stateT S (optionT (optionT (PredArr unit))) A)
    : PredArr (S -> Prop) (option (A * S)) :=
    fun pre r => asp (reach M) pre r \/ dslp (reach M) pre r.

  (** [obsRel] and all four SP observations factor through the monad morphism
      [obsRelM]: [obsX m = readX (obsRelM m)].  So each observation is just a
      fixed reading applied to the program's image [obsRelM m] in the
      reachability monad. *)
  Lemma obsRel_reach {A} (m : stdivexcnd S A) s r :
    obsRel m s r <-> reach (obsRelM m) s r.
  Proof. exact (obsRel_obsRelM m s r). Qed.

  Lemma obsASP_factor {A} (m : stdivexcnd S A) pre r :
    obsASP m pre r <-> readASP (obsRelM m) pre r.
  Proof.
    unfold obsASP, readASP, asp. split.
    - intros [s [Hpre Hr]]. exists s. split;
        [ exact Hpre | exact (proj1 (obsRel_reach m s r) Hr) ].
    - intros [s [Hpre Hr]]. exists s. split;
        [ exact Hpre | exact (proj2 (obsRel_reach m s r) Hr) ].
  Qed.

  Lemma obsDSLP_factor {A} (m : stdivexcnd S A) pre r :
    obsDSLP m pre r <-> readDSLP (obsRelM m) pre r.
  Proof.
    unfold obsDSLP, readDSLP, dslp. split.
    - intros H s Hr. exact (H s (proj2 (obsRel_reach m s r) Hr)).
    - intros H s Hr. exact (H s (proj1 (obsRel_reach m s r) Hr)).
  Qed.

  Lemma obsDSP_factor {A} (m : stdivexcnd S A) pre r :
    obsDSP m pre r <-> readDSP (obsRelM m) pre r.
  Proof.
    unfold obsDSP, readDSP.
    pose proof (obsASP_factor m pre r) as Ha. unfold obsASP, readASP in Ha.
    pose proof (obsDSLP_factor m pre r) as Hd. unfold obsDSLP, readDSLP in Hd.
    tauto.
  Qed.

  Lemma obsASLP_factor {A} (m : stdivexcnd S A) pre r :
    obsASLP m pre r <-> readASLP (obsRelM m) pre r.
  Proof.
    unfold obsASLP, readASLP.
    pose proof (obsASP_factor m pre r) as Ha. unfold obsASP, readASP in Ha.
    pose proof (obsDSLP_factor m pre r) as Hd. unfold obsDSLP, readDSLP in Hd.
    tauto.
  Qed.

  (** [obsDWP_ret]-style return characterization for the monad-view
      observation (clean RHS — the single [ret] outcome — no [asp]/[∃]).
      Reading this through [obsRel_obsRelM] recovers the arrow-view
      [obsRel_ret]; it is the [tt]-slice of the morphism law [obsRelM_ret]. *)
  Lemma obsRelM_ret_apply {A} (a : A) s u oa :
    unOptionT (unOptionT (runStateT (obsRelM (ret a)) s)) u oa <-> oa = Some (Some (a, s)).
  Proof. rewrite obsRelM_apply. cbn. split; intro H; congruence. Qed.

  (** *** The monad-morphism laws (stated as [eq1] in [nditPredM]) *)

  (** Return law of the monad morphism: [obsRelM (ret a) ≈ ret a]. *)
  Lemma obsRelM_ret {A} (a : A) : eq1 (obsRelM (ret a)) (ret a).
  Proof.
    unfold eq1, Eq1_stateT, Eq1_optionT, Eq1_Pred. intros s u oa. cbn.
    split; intro H; congruence.
  Qed.

  (** Bind law of the monad morphism: [obsRelM (x >>= f) ≈ obsRelM x >>=
      (obsRelM ∘ f)].  The two sides are [exists b, (x at b) /\ (cont at
      oa)] decompositions ([SetM]-bind vs [PredArr unit]-bind); they differ
      only by equation orientation in the exception/divergence branches
      ([retPred]), discharged by [congruence]. *)
  Lemma obsRelM_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsRelM (x >>= f)) (obsRelM x >>= (fun a => obsRelM (f a))).
  Proof.
    unfold eq1, Eq1_stateT, Eq1_optionT, Eq1_Pred. intros s u oa.
    cbn. unfold bindPred. cbn.
    split; intros [b [Hb Hk]]; exists b; (split; [exact Hb|]);
      destruct b as [[[v s0]|]|]; cbn in *; (exact Hk || congruence).
  Qed.

End ObsRelM.

(* ================================================================= *)
(** ** [SPStExc]: the strongest-postcondition spec monad              *)
(* INCORRECT DEFINITION *)
(* ================================================================= *)

(** Forward / strongest-postcondition spec monad, dual to
    [WStExc = stateT S (optionT WPure)] (whose backward transformer is
    [WPure A = (A -> Prop) -> Prop]).

    Modelled on the [ForwardPredTransformer] / [SP] monad of *Dijkstra
    Monads for All* (Maillard et al.): there [SP X = { f : forall p:SProp,
    X -> SPropOver p | monotone }] carries a *precondition* [p] forward to
    a postcondition that holds "over [p]" (i.e. implies [p]).  We keep the
    bare transformer (no bundled [over]/monotonicity) to match this
    project's bare [WPure]. *)
Section ProgSPMonad.

  (** [SPPure] = forward predicate transformer: a precondition [Prop] and a
      value determine the strongest postcondition [Prop]. *)
  Definition SPPure (A : Type) : Type := Prop -> A -> Prop.

  Definition SPStExc (S A : Type) : Type := stateT S (optionT SPPure) A.

  (** Refinement-form embeddings of a Hoare pre-/post-condition pair as a
      [SPStExc], split by approximation kind (mirroring [pp2wp_under] /
      [pp2wp_over]).  Both keep DM4All's forward shape
      [pp2sp0 (P, Q) p x := p /\ <body s0 r>]; they differ in the body
      exactly as the WP pair does — [Over] uses an implication ([pre -> post])
      and [Under] a conjunction ([pre /\ post]):

      - [pp2sp_over]:  [p /\ (pre s0 -> post r)]  (used as the *target*,
        [obs ⊑ pp2sp_over], for over-approximation [sp(pre) ⊆ post]);
      - [pp2sp_under]: [p /\ (pre s0 /\ post r)]  (used as the *source*,
        [pp2sp_under ⊑ obs]). *)
  Definition pp2sp_over_PureSP {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : SPStExc S A :=
    mkStateT (fun s0 => @mkOptionT SPPure _
                          (fun p r => p /\ (pre s0 -> post r))).

  Definition pp2sp_under_PureSP {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : SPStExc S A :=
    mkStateT (fun s0 => @mkOptionT SPPure _
                          (fun p r => p /\ (pre s0 /\ post r))).

  (** Pointwise refinement order on [SPStExc] — DM4All's [SP_rel]
      [fun m1 m2 => forall p x, Spr1 m1 p x -> Spr1 m2 p x], threaded through
      the state [s] and precondition [p].  (Suffixed [_PureSP] to avoid
      clashing with the top-level [ordSPStExc] on [(S -> Prop) -> _ -> Prop].) *)
  Definition ordProgSP_PureSP {S A} (m1 m2 : SPStExc S A) : Prop :=
    forall s p r,
      unOptionT (runStateT m1 s) p r -> unOptionT (runStateT m2 s) p r.

End ProgSPMonad.

(* ================================================================= *)
(** ** [SPStExc]-valued observation and refinement-style triple         *)
(* ================================================================= *)

(** The [SPStExc] analogues of the WP observation [obsAWP] and the
    refinement triple, in a module to avoid clashing with the
    [ASPostArr]-valued [obsASP] / [as_sp_obs]-based [tripleSP] above
    (cf. [Observation.WPredObs]).  Refer to them as [ProgSPObs.obsASP]
    and [ProgSPObs.tripleSP]. *)
Module ProgSPObs.

  (** Angelic strongest-postcondition observation as a [SPStExc]: from
      initial state [s] under precondition [p], outcome [r] is in the
      strongest postcondition iff [p] held and [r] is reachable from [s].
      This is DM4All's [SP_ret]-style [fun p y => p s/\ a ≡ y] generalised
      to the reachability relation [obsRel]. *)
  Definition obsASP {S A} (m : stdivexcnd S A) : SPStExc S A :=
    mkStateT (fun s => @mkOptionT SPPure _
                         (fun p r => p /\ obsRel m s r)).

  (** SP triple in the spec-as-element / refinement style, using
      [pp2sp_under] / [pp2sp_over] and [ordSPStExc] (dual to the WP refinement
      triple [tripleWPspec]).

      - [Over]  is over-approximation  [sp(pre) ⊆ post]  (= [obs ⊑ pp2sp_over]);
      - [Under] is under-approximation  (= [pp2sp_under ⊑ obs]).

      The inclusion directions are *flipped* relative to the WP refinement
      triple, since SP is the forward (covariant) transformer.  See the
      [progSP_tripleSP_*_char] checks below for the unfolded meanings. *)
  Definition tripleSP {S A}
    (obs : stdivexcnd S A -> SPStExc S A) (prog : stdivexcnd S A)
    (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordProgSP_PureSP (obs prog) (pp2sp_over_PureSP pre post)
    | Under => ordProgSP_PureSP (pp2sp_under_PureSP pre post) (obs prog)
    end.

End ProgSPObs.

(* ================================================================= *)
(** ** Checks: how the refinement [ProgSPObs.tripleSP] behaves         *)
(* ================================================================= *)

(** [Over] unfolds to the over-approximation [sp(pre) ⊆ post]: every
    outcome reachable from a [pre]-state lies in [post]. *)
Lemma progSP_tripleSP_over_char {S A} (prog : stdivexcnd S A) pre post :
  ProgSPObs.tripleSP ProgSPObs.obsASP prog Over pre post <->
  (forall s r, pre s -> obsRel prog s r -> post r).
Proof.
  unfold ProgSPObs.tripleSP, ProgSPObs.obsASP, ordProgSP_PureSP, pp2sp_over_PureSP.
  cbn. split.
  - intros H s r Hpre Hrel.
    destruct (H s True r (conj I Hrel)) as [_ Himp]. exact (Himp Hpre).
  - intros H s p r [Hp Hrel].
    split; [exact Hp | intro Hpre; exact (H s r Hpre Hrel)].
Qed.

(** [Under] unfolds to the *demonic* under-approximation: every [post]
    outcome is reachable from EVERY [pre]-state.  This is stronger than the
    point reading [post ⊆ sp(pre)] (which needs only SOME pre-state), and it
    holds vacuously when [pre] is empty — see [progSP_under_not_point].
    (Coincides with the point reading when [prog] is state-independent or
    [pre] is a singleton.) *)
Lemma progSP_tripleSP_under_char {S A} (prog : stdivexcnd S A) pre post :
  ProgSPObs.tripleSP ProgSPObs.obsASP prog Under pre post <->
  (forall s r, pre s -> post r -> obsRel prog s r).
Proof.
  unfold ProgSPObs.tripleSP, ProgSPObs.obsASP, ordProgSP_PureSP, pp2sp_under_PureSP.
  cbn. split.
  - intros H s r Hpre Hpost.
    destruct (H s True r (conj I (conj Hpre Hpost))) as [_ Hrel]. exact Hrel.
  - intros H s p r [Hp [Hpre Hpost]].
    split; [exact Hp | exact (H s r Hpre Hpost)].
Qed.

(** [Over] agrees with the point-based [tripleSP] (line ~163, the [asp]
    reading): both are [sp(pre) ⊆ post]. *)
Lemma progSP_tripleSP_over_agrees {S A} (prog : stdivexcnd S A) pre post :
  ProgSPObs.tripleSP ProgSPObs.obsASP prog Over pre post <->
  tripleSP obsASP prog Over pre post.
Proof.
  rewrite progSP_tripleSP_over_char.
  unfold tripleSP, obsASP, asp. split.
  - intros H r [s [Hpre Hrel]]. exact (H s r Hpre Hrel).
  - intros H s r Hpre Hrel. apply H. exists s. exact (conj Hpre Hrel).
Qed.

(** Concrete check: state [42] is reachable from every initial state
    (via [put 42]), so the demonic [Under] triple is provable for [progA]. *)
Example progSP_progA_under_42 :
  ProgSPObs.tripleSP ProgSPObs.obsASP progA Under
    (fun _ => True) (fun r => r = Some (tt, 42)).
Proof.
  apply progSP_tripleSP_under_char. intros s r _ ->.
  unfold obsRel; cbn; sauto.
Qed.

(** But the refinement [Under] is NOT the point under-approximation: with an
    empty [pre] it holds vacuously, while the point reading [post ⊆ sp(pre)]
    fails (no [pre]-state to witness reachability). *)
Example progSP_under_not_point :
  ProgSPObs.tripleSP ProgSPObs.obsASP progA Under (fun _ => False) (fun _ => True)
  /\ ~ tripleSP obsASP progA Under (fun _ => False) (fun _ => True).
Proof.
  split.
  - apply progSP_tripleSP_under_char. intros s r [].
  - unfold tripleSP, obsASP, asp. intro H.
    destruct (H (Some (tt, 42)) I) as [s [[] _]].
Qed.

(* ================================================================= *)
(** ** Faithful forward SP refinement (precondition carried as a predicate) *)
(* ================================================================= *)

(** The [SPStExc]/[ordSPStExc] refinement above threads the initial state via
    [stateT] and quantifies it universally, so the [exists]-over-initial-states
    in under-approximation is lost ([progSP_under_not_point]).  The fix is to
    carry the precondition as a *predicate* [S -> Prop] (the forward input),
    not a single state.  The auxiliary [b] then ranges over preconditions,
    making this the exact dual of the WP [tripleWPspec]:

    - [Over]  : [b] over the *down-set* of [pre] ([b ⊆ pre]), [sp b] in the
      *hypothesis*, embedded by an *implication* ([pp2_over], like [pp2wp_over]);
    - [Under] : [b] over the *up-set* of [pre] ([pre ⊆ b]), [sp b] in the
      *conclusion*, embedded by a *conjunction* ([pp2_under], like [pp2wp_under]).

    Both agree with the point-based [tripleSP] — see the [_agrees] checks. *)
Module SPredObs.

  (** Forward transformer: a precondition predicate determines the reachable
      postcondition over outcomes. *)
  Definition SPredT (S A : Type) : Type := (S -> Prop) -> option (A * S) -> Prop.

  (** Observation = the [asp] reading [exists s, b s /\ obsRel m s r]. *)
  Definition obsASP {S A} (m : stdivexcnd S A)
    : SPredT S A := asp (obsRel m). 
  Definition obsDSLP {S A} (m : stdivexcnd S A)
    : SPredT S A := dslp (obsRel m).
  Definition obsDSP {S A} (m : stdivexcnd S A)
    : SPredT S A := fun pre r => asp (obsRel m) pre r /\ dslp (obsRel m) pre r.
  Definition obsASLP {S A} (m : stdivexcnd S A)
    : SPredT S A := fun pre r => asp (obsRel m) pre r \/ dslp (obsRel m) pre r.

  Definition ordSP {S A} (m1 m2 : SPredT S A) : Prop :=
    forall b r, m1 b r -> m2 b r.

  Definition pp2_over {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : SPredT S A :=
    fun b r => (forall s, b s -> pre s) -> post r.

  Definition pp2_under {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : SPredT S A :=
    fun b r => (forall s, pre s -> b s) /\ post r.

  Definition tripleSP {S A}
    (obs : stdivexcnd S A -> SPredT S A) (prog : stdivexcnd S A)
    (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordSP (obs prog) (pp2_over pre post)
    | Under => ordSP (pp2_under pre post) (obs prog)
    end.

End SPredObs.

(** Check: [Over] agrees with the point-based [tripleSP] ([sp(pre) ⊆ post]). *)
Lemma SPred_tripleSP_over_agrees {S A} (prog : stdivexcnd S A) pre post :
  SPredObs.tripleSP SPredObs.obsASP prog Over pre post <->
  tripleSP obsASP prog Over pre post.
Proof.
  unfold SPredObs.tripleSP, SPredObs.obsASP, SPredObs.ordSP, SPredObs.pp2_over.
  unfold tripleSP, obsASP, asp. split.
  - intros H r [s [Hpre Hrel]]. apply (H pre r).
    + exists s. exact (conj Hpre Hrel).
    + intros s' Hs'. exact Hs'.
  - intros H b r [s [Hbs Hrel]] Hsub. apply H. exists s.
    exact (conj (Hsub s Hbs) Hrel).
Qed.

(** Check: [Under] now ALSO agrees with the point-based [tripleSP]
    ([post ⊆ sp(pre)]) — the existential over initial states is preserved,
    unlike the demonic [ProgSPObs] version. *)
Lemma SPred_tripleSP_under_agrees {S A} (prog : stdivexcnd S A) pre post :
  SPredObs.tripleSP SPredObs.obsASP prog Under pre post <->
  tripleSP obsASP prog Under pre post.
Proof.
  unfold SPredObs.tripleSP, SPredObs.obsASP, SPredObs.ordSP, SPredObs.pp2_under.
  unfold tripleSP, obsASP, asp. split.
  - intros H r Hpost. apply (H pre r).
    split; [intros s Hs; exact Hs | exact Hpost].
  - intros H b r [Hsub Hpost]. destruct (H r Hpost) as [s [Hpre Hrel]].
    exists s. exact (conj (Hsub s Hpre) Hrel).
Qed.

(** Positive [Under] example (mirrors [progA_42]): state [42] is reachable
    from initial state [0], which lies in [pre]. *)
Example SPred_progA_under_42 :
  SPredObs.tripleSP SPredObs.obsASP progA Under
    (fun _ => True) (fun r => r = Some (tt, 42)).
Proof.
  rewrite SPred_tripleSP_under_agrees.
  unfold tripleSP, obsASP, asp. intros r ->.
  exists 0. split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** Faithfulness contrast: with an empty [pre] the faithful [Under] correctly
    FAILS (no witness state), whereas the demonic [ProgSPObs.tripleSP] accepted
    it vacuously ([progSP_under_not_point]). *)
Example SPred_under_empty_pre_fails :
  ~ SPredObs.tripleSP SPredObs.obsASP progA Under (fun _ => False) (fun _ => True).
Proof.
  rewrite SPred_tripleSP_under_agrees.
  unfold tripleSP, obsASP, asp. intro H.
  destruct (H (Some (tt, 42)) I) as [s [[] _]].
Qed.*)

(* Here are my first attempts at looking at a sub-monad of the
   SPostArr monad - additive vs. disjunctive. *)

(* ================================================================= *)
(** ** [SPPure] / [SPStExc]: the spec monad of *additive* strongest-
       postcondition predicate transformers                          *)
(* ================================================================= *)

(** Forward (strongest-postcondition) counterpart of [WPure] / [WStExc].

    A *point* SP transformer has type [SPT A = Prop -> A -> Prop]: it turns
    a precondition (a [Prop] — at a point there is no input value to
    quantify over) into a postcondition on [A].  This is the naive dual of
    [WPure A = (A -> Prop) -> Prop], and it is exactly the (now commented
    out, "INCORRECT DEFINITION") [SPStExc] above.

    The naive version is not a monad.  Sequencing forward transformers is
    relational composition, so [bind m k] must run [k] at the *intermediate*
    postcondition produced by [m]; the only way to write that with the
    continuation seeing a single [Prop] is

      [bind m k p b := exists a, m p a /\ k a True b]

    and then the left-unit law [bind (ret a) k ≈ k a] reduces to
    [p /\ k a True b <-> k a p b], which holds *iff* [k a] is ADDITIVE.

    [AdditiveSP t] is join-preservation ([AdditiveSP_join],
    [AdditiveSP_strict], [AdditiveSP_mono]; conversely [AdditiveSP_of_join]
    recovers it from join-preservation plus congruence).  Over [Prop] every
    [p] is the join [\/_{h : p} True], so join-preservation has the closed
    form [t p a <-> p /\ t True a], which we take as the definition.

    Restricting to additive transformers therefore yields a genuine monad
    [SPPure], with [MonadLawsE] proved below, and hence
    [SPStExc S = stateT S (optionT SPPure)] inherits [MonadLawsE] through the
    generic transformer instances of [Prog.v] — exactly as [WStExc]
    does in [WP.v].

    The closed form is also a *representation theorem*: an additive [t] is
    determined by its value at [True] ([ofSet] / [spSet] are mutually
    inverse, [spSet_ofSet] / [ofSet_spSet]), so [SPPure] is the transformer
    presentation of the powerset monad.  That is the precise sense in which
    "additive strongest postcondition transformer" = "reachability
    relation": it is the same content as [PredMonad.v]'s [PredStExc], but
    packaged as predicate transformers with the laws proved. *)

Section PureSPMonad.

  Definition SPT (A : Type) : Type := Prop -> A -> Prop.

  (** Additivity, in the closed form justified above. *)
  Definition AdditiveSP {A} (t : SPT A) : Prop :=
    forall (p : Prop) (a : A), t p a <-> (p /\ t True a).

  Lemma AdditiveSP_join {A} (t : SPT A) (Ht : AdditiveSP t)
    (I : Type) (f : I -> Prop) (a : A) :
    t (exists i, f i) a <-> exists i, t (f i) a.
  Proof.
    split.
    - intro H. apply Ht in H. destruct H as [[i Hi] Ht0].
      exists i. apply Ht. split; [exact Hi | exact Ht0].
    - intros [i Hi]. apply Ht in Hi. destruct Hi as [Hf Ht0].
      apply Ht. split; [exists i; exact Hf | exact Ht0].
  Qed.

  Lemma AdditiveSP_strict {A} (t : SPT A) (Ht : AdditiveSP t) (a : A) :
    t False a <-> False.
  Proof.
    split; [| contradiction]. intro H. apply Ht in H. exact (proj1 H).
  Qed.

  Lemma AdditiveSP_mono {A} (t : SPT A) (Ht : AdditiveSP t) (p q : Prop) (a : A) :
    (p -> q) -> t p a -> t q a.
  Proof.
    intros Hpq H. apply Ht in H. destruct H as [Hp Ht0].
    apply Ht. split; [exact (Hpq Hp) | exact Ht0].
  Qed.

  (** Converse: join-preservation (plus congruence in the precondition,
      which is needed because [(exists _ : p, True)] is only *logically*
      equal to [p]) implies the closed form. *)
  Lemma AdditiveSP_of_join {A} (t : SPT A)
    (Hcong : forall (p q : Prop) (a : A), (p <-> q) -> (t p a <-> t q a))
    (Hjoin : forall (I : Type) (f : I -> Prop) (a : A),
        t (exists i, f i) a <-> exists i, t (f i) a) :
    AdditiveSP t.
  Proof.
    intros p a.
    assert (Hc : t p a <-> t (exists _ : p, True) a).
    { apply Hcong. split; [intro H; exists H; exact I | intros [H _]; exact H]. }
    pose proof (Hjoin p (fun _ => True) a) as Hj.
    split.
    - intro H. apply Hc in H. apply Hj in H. destruct H as [Hp Ht]. split; assumption.
    - intros [Hp Ht]. apply Hc. apply Hj. exists Hp. exact Ht.
  Qed.

  Definition SPPure (A : Type) : Type := { t : SPT A | AdditiveSP t }.

  Definition spApp {A} (t : SPPure A) : Prop -> A -> Prop := proj1_sig t.

  Lemma spApp_additive {A} (t : SPPure A) (p : Prop) (a : A) :
    spApp t p a <-> (p /\ spApp t True a).
  Proof. exact (proj2_sig t p a). Qed.

  (** The representation: [spSet] reads off the value at [True], [ofSet]
      rebuilds the transformer.  They are mutually inverse. *)
  Definition spSet {A} (t : SPPure A) : A -> Prop := fun a => spApp t True a.

  #[program] Definition ofSet {A} (Q : A -> Prop) : SPPure A :=
    fun p a => p /\ Q a.
  Next Obligation. unfold AdditiveSP. intros. tauto. Qed.

  Lemma spApp_ofSet {A} (Q : A -> Prop) (p : Prop) (a : A) :
    spApp (ofSet Q) p a <-> (p /\ Q a).
  Proof. split; intro H; exact H. Qed.

  Lemma spSet_ofSet {A} (Q : A -> Prop) (a : A) : spSet (ofSet Q) a <-> Q a.
  Proof. unfold spSet. rewrite spApp_ofSet. tauto. Qed.

  Lemma ofSet_spSet {A} (t : SPPure A) (p : Prop) (a : A) :
    spApp (ofSet (spSet t)) p a <-> spApp t p a.
  Proof. rewrite spApp_ofSet. unfold spSet. symmetry. apply spApp_additive. Qed.

  #[program] Definition retSP {A} (a : A) : SPPure A :=
    fun p a' => p /\ a' = a.
  Next Obligation. unfold AdditiveSP. intros. tauto. Qed.

  (** Relational composition: the continuation is run at the intermediate
      postcondition, i.e. at [True] once [a] has been produced. *)
  #[program] Definition bindSP {A B} (m : SPPure A) (k : A -> SPPure B) : SPPure B :=
    fun p b => exists a, spApp m p a /\ spApp (k a) True b.
  Next Obligation.
    unfold AdditiveSP. intros p b. split.
    - intros [a [Hm Hk]]. apply spApp_additive in Hm. destruct Hm as [Hp Hm].
      split; [exact Hp |]. exists a. split; assumption.
    - intros [Hp [a [Hm Hk]]]. exists a. split; [| exact Hk].
      apply spApp_additive. split; assumption.
  Qed.

  Lemma spApp_retSP {A} (a : A) (p : Prop) (a' : A) :
    spApp (retSP a) p a' <-> (p /\ a' = a).
  Proof. split; intro H; exact H. Qed.

  Lemma spApp_bindSP {A B} (m : SPPure A) (k : A -> SPPure B) (p : Prop) (b : B) :
    spApp (bindSP m k) p b <-> (exists a, spApp m p a /\ spApp (k a) True b).
  Proof. split; intro H; exact H. Qed.

  #[global] Instance Monad_PureSP : Monad SPPure :=
    {| ret := fun _ => retSP ;
       bind := fun _ _ => bindSP |}.

End PureSPMonad.

(** [Eq1] is pointwise [iff] (not Leibniz [eq] as for [WPure]: [SPPure] is
    a subset type, so extensional equality is the right notion and no
    functional extensionality is needed anywhere below). *)
Section PureSPLaws.

  #[global] Instance Eq1_PureSP : Eq1 SPPure :=
    fun A m n => forall p a, spApp m p a <-> spApp n p a.

  #[global] Instance Eq1Equivalence_PureSP
    : @Eq1Equivalence SPPure _ Eq1_PureSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a). specialize (H2 p a). tauto.
  Qed.

  (** [bind_ret_l] is where additivity is used: it is exactly
      [k x p b <-> p /\ k x True b]. *)
  #[global] Instance MonadLawsE_PureSP
    : @MonadLawsE SPPure Eq1_PureSP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_PureSP. intros p b.
      rewrite spApp_bindSP. split.
      + intros [a [Hr Hk]]. rewrite spApp_retSP in Hr. destruct Hr as [Hp ->].
        apply spApp_additive. split; assumption.
      + intro H. apply spApp_additive in H. destruct H as [Hp Hk].
        exists x. split; [rewrite spApp_retSP; split; [exact Hp | reflexivity] | exact Hk].
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_PureSP. intros p a.
      rewrite spApp_bindSP. split.
      + intros [a0 [Hx Hr]]. rewrite spApp_retSP in Hr. destruct Hr as [_ ->]. exact Hx.
      + intro Hx. exists a. split; [exact Hx | rewrite spApp_retSP; split; [exact I | reflexivity]].
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_PureSP. intros p c.
      rewrite !spApp_bindSP. split.
      + intros [b [Hb Hg]]. rewrite spApp_bindSP in Hb. destruct Hb as [a [Hx Hf]].
        exists a. split; [exact Hx | rewrite spApp_bindSP; exists b; split; assumption].
      + intros [a [Hx Hbc]]. rewrite spApp_bindSP in Hbc. destruct Hbc as [b [Hf Hg]].
        exists b. split; [rewrite spApp_bindSP; exists a; split; assumption | exact Hg].
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_PureSP in *. intros p b.
      rewrite !spApp_bindSP. split.
      + intros [a [Hx Hf]]. exists a. split; [apply Hxy; exact Hx | apply Hfg; exact Hf].
      + intros [a [Hy Hg]]. exists a. split; [apply Hxy; exact Hy | apply Hfg; exact Hg].
  Qed.

End PureSPLaws.

(* And here I tried naively applying monad transformers -
   this does not give the right shape. The shape it gives is:
   S -> Prop -> option (A * S) -> Prop vs.
   what is needed:
   (S -> Prop) -> option (A * S) -> Prop *)


(** [SPStExc S = stateT S (optionT SPPure)] — the same transformer stack as
    [WStExc S = stateT S (optionT WPure)], with the forward base.  The
    [Monad] / [MonadState] / [MonadExc] bundle mirrors [WP.v]; [Eq1] and
    [MonadLawsE] chain through [Prog.v] exactly as in [WP.v]. *)
Section ProgSPMonad.

  Variable S : Type.

  Definition SPStExc := stateT S (optionT SPPure).

  #[local] Existing Instance Monad_stateT.

  Definition retProgSP {A} (a : A) : SPStExc A :=
    @ret (stateT _ _) _ _ a.

  Definition bindProgSP {A B} (m : SPStExc A) (k : A -> SPStExc B) : SPStExc B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global] Instance Monad__ProgSP : Monad SPStExc :=
    {| ret := fun _ => @retProgSP _ ;
       bind := fun _ _ => @bindProgSP _ _ |}.

  Definition getProgSP : SPStExc S := @get _ (stateT _ _) _.
  Definition putProgSP (s : S) : SPStExc unit := @put _ (stateT _ _) _ s.

  #[global] Instance MonadState__ProgSP : MonadState S SPStExc :=
    {| get := getProgSP ; put := putProgSP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseProgSP {A} (_ : unit) : SPStExc A := @raise _ (stateT _ _) _ _ tt.
  Definition catchProgSP {A} (m : SPStExc A) (c : unit -> SPStExc A) : SPStExc A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global] Instance MonadExc__ProgSP : MonadExc unit SPStExc :=
    {| raise := fun _ => raiseProgSP ; catch := fun _ => catchProgSP |}.

  #[global] Instance Eq1__ProgSP : Eq1 SPStExc := Eq1_stateT S (optionT SPPure).

  Definition MonadLawsE__ProgSP : @MonadLawsE SPStExc Eq1__ProgSP _ :=
    MonadLawsE_stateT S (optionT SPPure).

End ProgSPMonad.

Arguments retProgSP {_} {_}.
Arguments bindProgSP {_} {_} {_}.

(* ----------------------------------------------------------------- *)
(** *** The [SPStExc]-valued SP observation                            *)
(* ----------------------------------------------------------------- *)

(** [obsSP m] packages the reachability relation [obsRel m] as an additive
    forward transformer, one per initial state.  Note the initial state is
    threaded by [stateT], so [obsSP m] carries exactly [obsRel m] — no more
    and no less.  In particular divergence (the outer [None] outcome of
    [stdivexcnd]) is invisible here, as it already is in [obsRel]. *)
Definition obsSP {S A} (m : stdivexcnd S A) : SPStExc S A :=
  mkStateT (fun s => @mkOptionT SPPure _ (ofSet (obsRel m s))).

(** Accessors: [applySP] is the transformer at a given initial state,
    [runSP] its value at precondition [True] (= the underlying relation). *)
Definition applySP {S A} (M : SPStExc S A) (s : S) : Prop -> option (A * S) -> Prop :=
  spApp (unOptionT (runStateT M s)).

Definition runSP {S A} (M : SPStExc S A) : PredArr S (option (A * S)) :=
  fun s r => applySP M s True r.

Lemma applySP_obsSP {S A} (m : stdivexcnd S A) s p r :
  applySP (obsSP m) s p r <-> (p /\ obsRel m s r).
Proof. unfold applySP, obsSP, spApp, ofSet. cbn. tauto. Qed.

Lemma runSP_obsSP {S A} (m : stdivexcnd S A) s r :
  runSP (obsSP m) s r <-> obsRel m s r.
Proof. unfold runSP. rewrite applySP_obsSP. tauto. Qed.

Lemma applySP_ret {S A} (a : A) (s : S) p r :
  applySP (ret a : SPStExc S A) s p r <-> (p /\ r = Some (a, s)).
Proof. split; intro H; exact H. Qed.

Lemma applySP_bind {S A B} (M : SPStExc S A) (K : A -> SPStExc S B) s p r :
  applySP (M >>= K) s p r <->
  (exists oas, applySP M s p oas /\
     match oas with
     | Some (a, s') => applySP (K a) s' True r
     | None => r = None
     end).
Proof.
  split.
  - intros [oas [Hm HK]]. exists oas. split; [exact Hm|].
    destruct oas as [[a s']|]; [exact HK | exact (proj2 HK)].
  - intros [oas [Hm HK]]. exists oas. split; [exact Hm|].
    destruct oas as [[a s']|]; [exact HK | exact (conj I HK)].
Qed.

(* ----------------------------------------------------------------- *)
(** *** The four SP observations as readings of one [SPStExc] element  *)
(* ----------------------------------------------------------------- *)

(** A [SPStExc] element is pointwise in the initial state; to state triples
    the precondition must be a *predicate* [S -> Prop] (this is what the
    old, commented-out [ProgSPObs] got wrong: it universally quantified the
    initial state, so [Under] degenerated — cf. [progSP_under_not_point]).
    The extension along [S] is exactly the [asp] / [dslp] pair of [SPostArr.v]
    applied to [runSP], giving back the four readings verbatim. *)
Definition spASP {S A} (M : SPStExc S A) : (S -> Prop) -> option (A * S) -> Prop :=
  asp (runSP M).
Definition spDSLP {S A} (M : SPStExc S A) : (S -> Prop) -> option (A * S) -> Prop :=
  dslp (runSP M).
Definition spDSP {S A} (M : SPStExc S A) : (S -> Prop) -> option (A * S) -> Prop :=
  fun pre r => asp (runSP M) pre r /\ dslp (runSP M) pre r.
Definition spASLP {S A} (M : SPStExc S A) : (S -> Prop) -> option (A * S) -> Prop :=
  fun pre r => asp (runSP M) pre r \/ dslp (runSP M) pre r.

(** Every SP observation factors through [obsSP]: [obsX m = spX (obsSP m)]. *)
Lemma obsASP_spASP {S A} (m : stdivexcnd S A) pre r :
  obsASP m pre r <-> spASP (obsSP m) pre r.
Proof.
  unfold obsASP, spASP, asp. split.
  - intros [s [Hp Hr]]. exists s. split; [exact Hp | exact (proj2 (runSP_obsSP m s r) Hr)].
  - intros [s [Hp Hr]]. exists s. split; [exact Hp | exact (proj1 (runSP_obsSP m s r) Hr)].
Qed.

Lemma obsDSLP_spDSLP {S A} (m : stdivexcnd S A) pre r :
  obsDSLP m pre r <-> spDSLP (obsSP m) pre r.
Proof.
  unfold obsDSLP, spDSLP, dslp. split.
  - intros H s Hr. exact (H s (proj1 (runSP_obsSP m s r) Hr)).
  - intros H s Hr. exact (H s (proj2 (runSP_obsSP m s r) Hr)).
Qed.

Lemma obsDSP_spDSP {S A} (m : stdivexcnd S A) pre r :
  obsDSP m pre r <-> spDSP (obsSP m) pre r.
Proof.
  pose proof (obsASP_spASP m pre r) as Ha. pose proof (obsDSLP_spDSLP m pre r) as Hd.
  unfold obsASP, spASP in Ha. unfold obsDSLP, spDSLP in Hd.
  unfold obsDSP, spDSP. tauto.
Qed.

Lemma obsASLP_spASLP {S A} (m : stdivexcnd S A) pre r :
  obsASLP m pre r <-> spASLP (obsSP m) pre r.
Proof.
  pose proof (obsASP_spASP m pre r) as Ha. pose proof (obsDSLP_spDSLP m pre r) as Hd.
  unfold obsASP, spASP in Ha. unfold obsDSLP, spDSLP in Hd.
  unfold obsASLP, spASLP. tauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** [tripleSPm]: [tripleSP] over the [SPStExc] monad               *)
(* ----------------------------------------------------------------- *)

(** The SP triple, restated so that the observation is *monad-valued*
    ([obs : stdivexcnd S A -> SPStExc S A]) and the comparison with [post]
    goes through an explicit reading of that element.  Instantiating
    [read] at [spASP] / [spDSLP] / [spDSP] / [spASLP] recovers the four
    old triples on the nose ([tripleSPm_ASP] .. [tripleSPm_ASLP]), so the
    original [tripleSP] and every lemma about it survive unchanged; the
    transported statements are collected below. *)
Definition tripleSPm {S A}
  (read : SPStExc S A -> (S -> Prop) -> option (A * S) -> Prop)
  (obs : stdivexcnd S A -> SPStExc S A)
  (prog : stdivexcnd S A)
  (kind : approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop :=
  match kind with
  | Over  => forall r, read (obs prog) pre r -> post r
  | Under => forall r, post r -> read (obs prog) pre r
  end.

Lemma tripleSPm_ASP {S A} (prog : stdivexcnd S A) kind pre post :
  tripleSPm spASP obsSP prog kind pre post <-> tripleSP obsASP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (obsASP_spASP prog pre r) (H r Hr))
          | exact (proj2 (obsASP_spASP prog pre r) (H r Hr))
          | apply H; exact (proj1 (obsASP_spASP prog pre r) Hr)
          | apply H; exact (proj2 (obsASP_spASP prog pre r) Hr) ].
Qed.

Lemma tripleSPm_DSLP {S A} (prog : stdivexcnd S A) kind pre post :
  tripleSPm spDSLP obsSP prog kind pre post <-> tripleSP obsDSLP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (obsDSLP_spDSLP prog pre r) (H r Hr))
          | exact (proj2 (obsDSLP_spDSLP prog pre r) (H r Hr))
          | apply H; exact (proj1 (obsDSLP_spDSLP prog pre r) Hr)
          | apply H; exact (proj2 (obsDSLP_spDSLP prog pre r) Hr) ].
Qed.

Lemma tripleSPm_DSP {S A} (prog : stdivexcnd S A) kind pre post :
  tripleSPm spDSP obsSP prog kind pre post <-> tripleSP obsDSP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (obsDSP_spDSP prog pre r) (H r Hr))
          | exact (proj2 (obsDSP_spDSP prog pre r) (H r Hr))
          | apply H; exact (proj1 (obsDSP_spDSP prog pre r) Hr)
          | apply H; exact (proj2 (obsDSP_spDSP prog pre r) Hr) ].
Qed.

Lemma tripleSPm_ASLP {S A} (prog : stdivexcnd S A) kind pre post :
  tripleSPm spASLP obsSP prog kind pre post <-> tripleSP obsASLP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (obsASLP_spASLP prog pre r) (H r Hr))
          | exact (proj2 (obsASLP_spASLP prog pre r) (H r Hr))
          | apply H; exact (proj1 (obsASLP_spASLP prog pre r) Hr)
          | apply H; exact (proj2 (obsASLP_spASLP prog pre r) Hr) ].
Qed.

(* ----------------------------------------------------------------- *)
(** *** [obsSP] is a monad morphism [stdivexcnd S ==> SPStExc S]         *)
(* ----------------------------------------------------------------- *)

(** [eqProgSP] is the unfolding of [eq1] at [SPStExc] ([eqProgSP_eq1]:
    they are convertible), kept for readability of the proofs. *)
Definition eqProgSP {S A} (M N : SPStExc S A) : Prop :=
  forall s p r, applySP M s p r <-> applySP N s p r.

Lemma eqProgSP_eq1 {S A} (M N : SPStExc S A) : eqProgSP M N <-> eq1 M N.
Proof. split; intro H; exact H. Qed.

Theorem obsSP_ret {S A} (a : A) : eq1 (obsSP (ret a : stdivexcnd S A)) (ret a).
Proof.
  apply eqProgSP_eq1. intros s p r.
  split.
  - intro H. apply applySP_obsSP in H. destruct H as [Hp Hrel].
    apply applySP_ret. split; [exact Hp|].
    unfold obsRel in Hrel. destruct r as [[b s']|]; cbn in Hrel; congruence.
  - intro H. apply applySP_ret in H. destruct H as [Hp Hrel].
    apply applySP_obsSP. split; [exact Hp|].
    unfold obsRel. destruct r as [[b s']|]; cbn; congruence.
Qed.

(** Divergence is dropped by [obsRel], but this does *not* break the bind
    law: a divergent branch of [x] contributes only the outer [None]
    outcome to [x >>= f], which both sides discard.  Exceptions ([Some
    None]) short-circuit on both sides alike. *)
Theorem obsSP_bind {S A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
  eq1 (obsSP (x >>= f)) (obsSP x >>= (fun a => obsSP (f a))).
Proof.
  apply eqProgSP_eq1. intros s p r. split.
  - intro H. apply applySP_obsSP in H. destruct H as [Hp Hrel].
    apply applySP_bind. apply obsRel_bind in Hrel.
    destruct Hrel as [[a [s' [Hx Hf]]] | [Hx Heq]].
    + exists (Some (a, s')). split.
      * apply applySP_obsSP. split; assumption.
      * apply applySP_obsSP. split; [exact I | exact Hf].
    + exists None. split; [apply applySP_obsSP; split; assumption | exact Heq].
  - intro H. apply applySP_bind in H. destruct H as [oas [Hm HK]].
    apply applySP_obsSP in Hm. destruct Hm as [Hp Hx].
    apply applySP_obsSP. split; [exact Hp|]. apply obsRel_bind.
    destruct oas as [[a s']|].
    + left. exists a, s'. split; [exact Hx|].
      apply applySP_obsSP in HK. exact (proj2 HK).
    + right. split; [exact Hx | exact HK].
Qed.

(* ----------------------------------------------------------------- *)
(** *** What is and is not additive                                   *)
(* ----------------------------------------------------------------- *)

(** [spASP] — the extension of a [SPStExc] element along the precondition
    predicate — is additive, i.e. it preserves arbitrary unions of
    preconditions.  This is the [S]-indexed counterpart of [AdditiveSP]. *)
Theorem spASP_join {S A} (M : SPStExc S A) (I : Type) (F : I -> S -> Prop) r :
  spASP M (fun s => exists i, F i s) r <-> exists i, spASP M (F i) r.
Proof.
  unfold spASP, asp. split.
  - intros [s [[i Hi] Hr]]. exists i, s. split; assumption.
  - intros [i [s [Hi Hr]]]. exists s. split; [exists i; exact Hi | exact Hr].
Qed.

Theorem spASP_join2 {S A} (M : SPStExc S A) (P Q : S -> Prop) r :
  spASP M (fun s => P s \/ Q s) r <-> (spASP M P r \/ spASP M Q r).
Proof.
  unfold spASP, asp. split.
  - intros [s [[HP|HQ] Hr]]; [left|right]; exists s; split; assumption.
  - intros [[s [HP Hr]] | [s [HQ Hr]]]; exists s;
      (split; [ solve [left; exact HP | right; exact HQ] | exact Hr ]).
Qed.

Theorem spASP_monotone {S A} (M : SPStExc S A) (p q : S -> Prop) r :
  (forall s, p s -> q s) -> spASP M p r -> spASP M q r.
Proof. intros Hsub [s [Hp Hr]]. exists s. split; [exact (Hsub s Hp) | exact Hr]. Qed.

(** [obsDSLP] is NOT additive: [progEx] reaches state [42] from every
    initial state, so [dslp] at [Some (tt, 42)] is "[pre] holds
    everywhere", which holds of a union without holding of either
    disjunct. *)
Lemma progEx_reaches_42 : forall s, obsRel progEx s (Some (tt, 42)).
Proof. intro s. unfold obsRel. cbn. sauto. Qed.

Definition preZero : nat -> Prop := fun s => s = 0.
Definition preNonZero : nat -> Prop := fun s => s <> 0.

Theorem obsDSLP_not_additive :
  obsDSLP progEx (fun s => preZero s \/ preNonZero s) (Some (tt, 42))
  /\ ~ obsDSLP progEx preZero (Some (tt, 42))
  /\ ~ obsDSLP progEx preNonZero (Some (tt, 42)).
Proof.
  split; [| split].
  - intros s _. unfold preZero, preNonZero.
    destruct s; [left; reflexivity | right; discriminate].
  - intro H. specialize (H 1 (progEx_reaches_42 1)). unfold preZero in H. discriminate.
  - intro H. specialize (H 0 (progEx_reaches_42 0)). unfold preNonZero in H.
    exact (H eq_refl).
Qed.

(** Consequence, and the honest limitation of this monad: there is no
    [SPStExc] element whose (additive) reading is the demonic-liberal
    transformer.  So the four SP observations cannot be four *different*
    [SPStExc]-valued observations — only [obsASP] is an element of the
    additive monad.  What does hold is the factorization above: all four
    are readings of the single element [obsSP m], because that element
    carries the whole reachability relation. *)
Corollary obsDSLP_not_spASP :
  ~ exists M : SPStExc nat unit, forall pre r, spASP M pre r <-> obsDSLP progEx pre r.
Proof.
  intros [M HM]. destruct obsDSLP_not_additive as [Hj [Hz Hnz]].
  apply (proj2 (HM _ _)) in Hj. apply spASP_join2 in Hj.
  destruct Hj as [H | H]; [apply Hz | apply Hnz]; exact (proj1 (HM _ _) H).
Qed.

(* ----------------------------------------------------------------- *)
(** *** The SP taxonomy, transported to [tripleSPm]                   *)
(* ----------------------------------------------------------------- *)

(** Every statement below is the corresponding theorem earlier in this
    file, with [tripleSP obsX] replaced by [tripleSPm spX obsSP]; each is
    discharged by rewriting with the [tripleSPm_*] agreements. *)
Ltac to_pointwise_sp :=
  repeat first [ rewrite tripleSPm_ASP  | rewrite tripleSPm_DSLP
               | rewrite tripleSPm_DSP  | rewrite tripleSPm_ASLP ].

Theorem m_cc_aslp_implies_asp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASLP obsSP m Over pre post -> tripleSPm spASP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply cc_aslp_implies_asp. Qed.

Theorem m_cc_aslp_implies_dslp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASLP obsSP m Over pre post -> tripleSPm spDSLP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply cc_aslp_implies_dslp. Qed.

Theorem m_cc_dslp_implies_dsp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSLP obsSP m Over pre post -> tripleSPm spDSP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply cc_dslp_implies_dsp. Qed.

Theorem m_cc_asp_implies_dsp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASP obsSP m Over pre post -> tripleSPm spDSP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply cc_asp_implies_dsp. Qed.

Theorem m_ii_dsp_implies_dslp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSP obsSP m Under pre post -> tripleSPm spDSLP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ii_dsp_implies_dslp. Qed.

Theorem m_ii_dslp_implies_aslp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSLP obsSP m Under pre post -> tripleSPm spASLP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ii_dslp_implies_aslp. Qed.

Theorem m_ii_asp_implies_aslp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASP obsSP m Under pre post -> tripleSPm spASLP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ii_asp_implies_aslp. Qed.

Theorem m_ii_dsp_implies_asp : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSP obsSP m Under pre post -> tripleSPm spASP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ii_dsp_implies_asp. Qed.

Theorem m_ci_aslp_dsp_contrapositive : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASLP obsSP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spDSP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_aslp_dsp_contrapositive. Qed.

Theorem m_ci_aslp_dsp_contrapositive' : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSP obsSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spASLP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_aslp_dsp_contrapositive'. Qed.

Theorem m_ci_asp_dslp_contrapositive : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASP obsSP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spDSLP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_asp_dslp_contrapositive. Qed.

Theorem m_ci_asp_dslp_contrapositive' : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSLP obsSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spASP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_asp_dslp_contrapositive'. Qed.

Theorem m_ci_dslp_asp_contrapositive : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSLP obsSP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spASP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_dslp_asp_contrapositive. Qed.

Theorem m_ci_dslp_asp_contrapositive' : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASP obsSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spDSLP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_dslp_asp_contrapositive'. Qed.

Theorem m_ci_dsp_aslp_contrapositive : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spDSP obsSP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spASLP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_dsp_aslp_contrapositive. Qed.

Theorem m_ci_dsp_aslp_contrapositive' : forall S A (m : stdivexcnd S A) pre post,
    tripleSPm spASLP obsSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleSPm spDSP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply ci_dsp_aslp_contrapositive'. Qed.

(** The two GaloisArr connections with the WP side survive verbatim. *)
Theorem m_dwlp_asp : forall S A (m : stdivexcnd S A) pre post,
    tripleWP obsDWLP m pre SubsetOf post <-> tripleSPm spASP obsSP m Over pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply dwlp_asp. Qed.

Theorem m_awp_dslp : forall S A (m : stdivexcnd S A) pre post,
    tripleWP obsAWP m pre SupersetOf post <-> tripleSPm spDSLP obsSP m Under pre post.
Proof. intros S A m pre post. to_pointwise_sp. apply awp_dslp. Qed.

(** Refinement ("spec-as-element") form, and its agreement with the direct
    one — the [SPStExc] counterpart of [tripleSPDefEq].  Monotonicity of the
    reading is [spASP_monotone]. *)
Definition tripleSPmspec {S A}
  (read : SPStExc S A -> (S -> Prop) -> option (A * S) -> Prop)
  (obs : stdivexcnd S A -> SPStExc S A)
  (prog : stdivexcnd S A) (kind : approximationKind)
  (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  match kind with
  | Over  => ordSPStExc (read (obs prog)) (pp2sp_over pre post)
  | Under => ordSPStExc (pp2sp_under pre post) (read (obs prog))
  end.

Lemma tripleSPmspec_ASP {S A} (prog : stdivexcnd S A) kind pre post :
  tripleSPmspec spASP obsSP prog kind pre post <-> tripleSPspec obsASP prog kind pre post.
Proof.
  destruct kind; cbn; unfold ordSPStExc; split; intros H b r Hr;
    first [ exact (H b r (proj1 (obsASP_spASP prog b r) Hr))
          | exact (H b r (proj2 (obsASP_spASP prog b r) Hr))
          | exact (proj1 (obsASP_spASP prog b r) (H b r Hr))
          | exact (proj2 (obsASP_spASP prog b r) (H b r Hr)) ].
Qed.

Theorem m_tripleSPDefEq {S A} (prog : stdivexcnd S A) kind pre post :
  tripleSPm spASP obsSP prog kind pre post <->
  tripleSPmspec spASP obsSP prog kind pre post.
Proof.
  rewrite tripleSPm_ASP, tripleSPmspec_ASP.
  apply tripleSPDefEq. intros p q Hsub r Hr.
  apply (proj2 (obsASP_spASP prog q r)).
  apply (spASP_monotone _ p q r Hsub).
  exact (proj1 (obsASP_spASP prog p r) Hr).
Qed.


(* ================================================================= *)
(** ** [PureSPM] / [ProgSPM]: the *multiplicative* SP spec monad      *)
(* ================================================================= *)

(** The de Morgan dual of [SPPure].  Where an additive transformer
    factors as [t p a <-> p /\ t True a] (a *join* of per-outcome
    contributions), a MULTIPLICATIVE one factors as

      [t p a <-> p \/ t False a]

    which is meet-preservation ([MultiplicativeSP_meet]; the converse
    [MultiplicativeSP_of_meet] recovers the closed form from
    meet-preservation plus congruence, using [p <-> (~p -> False)]).
    The corresponding representation is the *co-set*
    [spCoSet t a := ~ t False a], with [t p a <-> (spCoSet t a -> p)]
    ([spAppM_repr]).  Concretely: an additive transformer says "[p]
    holds AND [a] is reachable"; a multiplicative one says "[a] is
    reachable IMPLIES [p]".

    Sequencing is again relational composition, but written in the
    dual (universal) way:

      [bindSPM m k p b := forall a, m (k a p b) a]

    — a nesting rather than an existential, exactly like [WPure]'s
    continuation-style [bind].  This is a genuine monad ([MonadLawsE]
    below), and [ProgSPM S = stateT S (optionT PureSPM)] inherits the
    laws through [Prog.v] just as [SPStExc] and [WStExc] do.

    Classical logic ([Classical_Prop.classic], already used by this
    file's contrapositive theorems) is needed on this side: the
    representation [t p a <-> (Q a -> p)] passes through [~~p -> p]. *)

Section PureSPMMonad.

  Definition MultiplicativeSP {A} (t : SPT A) : Prop :=
    forall (p : Prop) (a : A), t p a <-> (p \/ t False a).

  Lemma MultiplicativeSP_top {A} (t : SPT A) (Ht : MultiplicativeSP t) (a : A) :
    t True a.
  Proof. apply Ht. left. exact I. Qed.

  Lemma MultiplicativeSP_mono {A} (t : SPT A) (Ht : MultiplicativeSP t)
    (p q : Prop) (a : A) : (p -> q) -> t p a -> t q a.
  Proof.
    intros Hpq H. apply Ht in H. apply Ht.
    destruct H as [Hp | Hf]; [left; exact (Hpq Hp) | right; exact Hf].
  Qed.

  Lemma MultiplicativeSP_meet {A} (t : SPT A) (Ht : MultiplicativeSP t)
    (I : Type) (f : I -> Prop) (a : A) :
    t (forall i, f i) a <-> forall i, t (f i) a.
  Proof.
    split.
    - intros H i. apply (MultiplicativeSP_mono t Ht (forall j, f j) (f i) a); [| exact H].
      intro Hall. exact (Hall i).
    - intro H. apply Ht.
      destruct (classic (t False a)) as [Hf | Hnf]; [right; exact Hf |].
      left. intro i. specialize (H i). apply Ht in H.
      destruct H as [Hfi | Hf]; [exact Hfi | contradiction].
  Qed.

  Lemma MultiplicativeSP_of_meet {A} (t : SPT A)
    (Hcong : forall (p q : Prop) (a : A), (p <-> q) -> (t p a <-> t q a))
    (Hmeet : forall (I : Type) (f : I -> Prop) (a : A),
        t (forall i, f i) a <-> forall i, t (f i) a) :
    MultiplicativeSP t.
  Proof.
    intros p a.
    assert (Hc : t p a <-> t (forall _ : ~ p, False) a).
    { apply Hcong. split; [intros Hp Hnp; exact (Hnp Hp) | intro H; apply NNPP; exact H]. }
    pose proof (Hmeet (~ p) (fun _ => False) a) as Hm.
    split.
    - intro H. pose proof (proj1 Hm (proj1 Hc H)) as H'.
      destruct (classic p) as [Hp | Hnp]; [left; exact Hp | right; exact (H' Hnp)].
    - intros [Hp | Hf].
      + apply Hc. apply Hm. intro Hnp. contradiction.
      + apply Hc. apply Hm. intro Hnp. exact Hf.
  Qed.

  Definition PureSPM (A : Type) : Type := { t : SPT A | MultiplicativeSP t }.

  Definition spAppM {A} (t : PureSPM A) : Prop -> A -> Prop := proj1_sig t.

  Lemma spAppM_mult {A} (t : PureSPM A) (p : Prop) (a : A) :
    spAppM t p a <-> (p \/ spAppM t False a).
  Proof. exact (proj2_sig t p a). Qed.

  (** The co-set representation, dual to [spSet] / [ofSet]. *)
  Definition spCoSet {A} (t : PureSPM A) : A -> Prop := fun a => ~ spAppM t False a.

  #[program] Definition ofCoSet {A} (Q : A -> Prop) : PureSPM A :=
    fun p a => Q a -> p.
  Next Obligation.
    unfold MultiplicativeSP. intros p a. split.
    - intro H. destruct (classic p) as [Hp | Hnp];
        [left; exact Hp | right; intro HQ; exact (Hnp (H HQ))].
    - intros [Hp | Hn] HQ; [exact Hp | destruct (Hn HQ)].
  Qed.

  Lemma spAppM_ofCoSet {A} (Q : A -> Prop) (p : Prop) (a : A) :
    spAppM (ofCoSet Q) p a <-> (Q a -> p).
  Proof. split; intro H; exact H. Qed.

  Lemma spCoSet_ofCoSet {A} (Q : A -> Prop) (a : A) : spCoSet (ofCoSet Q) a <-> Q a.
  Proof.
    unfold spCoSet. rewrite spAppM_ofCoSet. split.
    - intro H. apply NNPP. intro HnQ. apply H. intro HQ. exact (HnQ HQ).
    - intros HQ H. exact (H HQ).
  Qed.

  Lemma spAppM_repr {A} (t : PureSPM A) (p : Prop) (a : A) :
    spAppM t p a <-> (spCoSet t a -> p).
  Proof.
    unfold spCoSet. split.
    - intro H. apply spAppM_mult in H. destruct H as [Hp | Hf];
        [intros _; exact Hp | intro Hn; contradiction].
    - intro H. apply spAppM_mult.
      destruct (classic (spAppM t False a)) as [Hf | Hnf];
        [right; exact Hf | left; exact (H Hnf)].
  Qed.

  Lemma ofCoSet_spCoSet {A} (t : PureSPM A) (p : Prop) (a : A) :
    spAppM (ofCoSet (spCoSet t)) p a <-> spAppM t p a.
  Proof. rewrite spAppM_ofCoSet. symmetry. apply spAppM_repr. Qed.

  Lemma spAppM_cong {A} (t : PureSPM A) (p q : Prop) (a : A) :
    (p <-> q) -> (spAppM t p a <-> spAppM t q a).
  Proof. intro Hpq. rewrite !spAppM_repr. tauto. Qed.

  Definition retSPM {A} (a : A) : PureSPM A := ofCoSet (fun a' => a' = a).

  (** Dual of [bindSP]: a nesting, not an existential. *)
  #[program] Definition bindSPM {A B} (m : PureSPM A) (k : A -> PureSPM B) : PureSPM B :=
    fun p b => forall a, spAppM m (spAppM (k a) p b) a.
  Next Obligation.
    unfold MultiplicativeSP. intros p b. split.
    - intro H. destruct (classic p) as [Hp | Hnp]; [left; exact Hp | right].
      intro a. specialize (H a). rewrite spAppM_repr in H. apply spAppM_repr.
      intro Hm. specialize (H Hm). rewrite spAppM_repr in H. apply spAppM_repr.
      intro Hk. exact (Hnp (H Hk)).
    - intros [Hp | H] a; apply spAppM_repr; intro Hm.
      + apply spAppM_repr. intros _. exact Hp.
      + specialize (H a). rewrite spAppM_repr in H. specialize (H Hm).
        rewrite spAppM_repr in H. apply spAppM_repr. intro Hk. destruct (H Hk).
  Qed.

  Lemma spAppM_retSPM {A} (a : A) (p : Prop) (a' : A) :
    spAppM (retSPM a) p a' <-> (a' = a -> p).
  Proof. unfold retSPM. exact (spAppM_ofCoSet (fun x => x = a) p a'). Qed.

  Lemma spAppM_bindSPM {A B} (m : PureSPM A) (k : A -> PureSPM B) (p : Prop) (b : B) :
    spAppM (bindSPM m k) p b <-> (forall a, spAppM m (spAppM (k a) p b) a).
  Proof. split; intro H; exact H. Qed.

  #[global] Instance Monad_PureSPM : Monad PureSPM :=
    {| ret := fun _ => retSPM ;
       bind := fun _ _ => bindSPM |}.

End PureSPMMonad.

Section PureSPMLaws.

  #[global] Instance Eq1_PureSPM : Eq1 PureSPM :=
    fun A m n => forall p a, spAppM m p a <-> spAppM n p a.

  #[global] Instance Eq1Equivalence_PureSPM
    : @Eq1Equivalence PureSPM _ Eq1_PureSPM.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a). specialize (H2 p a). tauto.
  Qed.

  #[global] Instance MonadLawsE_PureSPM
    : @MonadLawsE PureSPM Eq1_PureSPM _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_PureSPM. intros p b.
      rewrite spAppM_bindSPM. split.
      + intro H. specialize (H x). rewrite spAppM_retSPM in H. exact (H eq_refl).
      + intros H a. rewrite spAppM_retSPM. intro Heq. subst a. exact H.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_PureSPM. intros p a.
      rewrite spAppM_bindSPM. split.
      + intro H. specialize (H a). rewrite spAppM_repr in H. apply spAppM_repr.
        intro Hm. specialize (H Hm). rewrite spAppM_retSPM in H. exact (H eq_refl).
      + intros H a0. apply spAppM_repr. intro Hm.
        rewrite spAppM_retSPM. intro Heq. subst a.
        exact (proj1 (spAppM_repr x p a0) H Hm).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_PureSPM. intros p c.
      rewrite !spAppM_bindSPM. split.
      + intros H a. apply spAppM_repr. intros Hm b.
        specialize (H b). rewrite spAppM_bindSPM in H. specialize (H a).
        rewrite spAppM_repr in H. exact (H Hm).
      + intros H b. rewrite spAppM_bindSPM. intro a.
        apply spAppM_repr. intro Hm. specialize (H a).
        rewrite spAppM_repr in H. exact (H Hm b).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_PureSPM in *. intros p b.
      rewrite !spAppM_bindSPM. split; intros H a; specialize (H a).
      + apply Hxy. exact (proj1 (spAppM_cong x _ _ a (Hfg a p b)) H).
      + apply Hxy. exact (proj2 (spAppM_cong y _ _ a (Hfg a p b)) H).
  Qed.

End PureSPMLaws.

Section ProgSPMMonad.

  Variable S : Type.

  Definition ProgSPM := stateT S (optionT PureSPM).

  #[local] Existing Instance Monad_stateT.

  Definition retProgSPM {A} (a : A) : ProgSPM A := @ret (stateT _ _) _ _ a.
  Definition bindProgSPM {A B} (m : ProgSPM A) (k : A -> ProgSPM B) : ProgSPM B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global] Instance Monad__ProgSPM : Monad ProgSPM :=
    {| ret := fun _ => @retProgSPM _ ;
       bind := fun _ _ => @bindProgSPM _ _ |}.

  Definition getProgSPM : ProgSPM S := @get _ (stateT _ _) _.
  Definition putProgSPM (s : S) : ProgSPM unit := @put _ (stateT _ _) _ s.

  #[global] Instance MonadState__ProgSPM : MonadState S ProgSPM :=
    {| get := getProgSPM ; put := putProgSPM |}.

  #[local] Existing Instance OptionTError.

  Definition raiseProgSPM {A} (_ : unit) : ProgSPM A := @raise _ (stateT _ _) _ _ tt.
  Definition catchProgSPM {A} (m : ProgSPM A) (c : unit -> ProgSPM A) : ProgSPM A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global] Instance MonadExc__ProgSPM : MonadExc unit ProgSPM :=
    {| raise := fun _ => raiseProgSPM ; catch := fun _ => catchProgSPM |}.

  #[global] Instance Eq1__ProgSPM : Eq1 ProgSPM := Eq1_stateT S (optionT PureSPM).

  Definition MonadLawsE__ProgSPM : @MonadLawsE ProgSPM Eq1__ProgSPM _ :=
    MonadLawsE_stateT S (optionT PureSPM).

End ProgSPMMonad.

Arguments retProgSPM {_} {_}.
Arguments bindProgSPM {_} {_} {_}.

Definition applySPM {S A} (M : ProgSPM S A) (s : S) : Prop -> option (A * S) -> Prop :=
  spAppM (unOptionT (runStateT M s)).

Lemma applySPM_ret {S A} (a : A) (s : S) p r :
  applySPM (ret a : ProgSPM S A) s p r <-> (r = Some (a, s) -> p).
Proof. split; intro H; exact H. Qed.

Lemma applySPM_bind {S A B} (M : ProgSPM S A) (K : A -> ProgSPM S B) s p r :
  applySPM (M >>= K) s p r <->
  (forall oas, applySPM M s
     (match oas with
      | Some (a, s') => applySPM (K a) s' p r
      | None => r = None -> p
      end) oas).
Proof.
  split; intros H oas; specialize (H oas); destruct oas as [[a s']|]; exact H.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Readings: join over initial states / meet over initial states *)
(* ----------------------------------------------------------------- *)

(** A [SPStExc] / [ProgSPM] element is pointwise in the initial state.
    Extending it to a precondition *predicate* is a join in the additive
    case and a meet in the multiplicative case — the two readings are
    forced by the two monads, not chosen. *)
Definition readSP {S A} (M : SPStExc S A) (pre : S -> Prop) (r : option (A * S)) : Prop :=
  exists s, applySP M s (pre s) r.

Definition readSPM {S A} (M : ProgSPM S A) (pre : S -> Prop) (r : option (A * S)) : Prop :=
  forall s, applySPM M s (pre s) r.

Lemma readSP_spASP {S A} (M : SPStExc S A) pre r : readSP M pre r <-> spASP M pre r.
Proof.
  unfold readSP, spASP, asp, runSP, applySP. split.
  - intros [s H]. rewrite spApp_additive in H. destruct H as [Hp Hb].
    exists s. split; assumption.
  - intros [s [Hp Hb]]. exists s. rewrite spApp_additive. split; assumption.
Qed.

(** The join reading is strict and join-preserving; the meet reading is
    top-preserving and meet-preserving.  These four facts are what make
    [obsDSP] / [obsASLP] impossible below. *)
Lemma readSP_strict {S A} (M : SPStExc S A) r : ~ readSP M (fun _ => False) r.
Proof. unfold readSP, applySP. intros [s H]. rewrite spApp_additive in H. exact (proj1 H). Qed.

Lemma readSP_join2 {S A} (M : SPStExc S A) (P Q : S -> Prop) r :
  readSP M (fun s => P s \/ Q s) r <-> (readSP M P r \/ readSP M Q r).
Proof.
  unfold readSP, applySP. split.
  - intros [s H]. rewrite spApp_additive in H. destruct H as [[HP|HQ] Hb];
      [left | right]; exists s; rewrite spApp_additive; split; assumption.
  - intros [[s H] | [s H]]; exists s; rewrite spApp_additive in H;
      destruct H as [Hx Hb]; rewrite spApp_additive; split;
      solve [ left; exact Hx | right; exact Hx | exact Hb ].
Qed.

Lemma readSPM_top {S A} (M : ProgSPM S A) r : readSPM M (fun _ => True) r.
Proof. intros s. unfold applySPM. apply spAppM_mult. left. exact I. Qed.

Lemma readSPM_meet2 {S A} (M : ProgSPM S A) (P Q : S -> Prop) r :
  readSPM M (fun s => P s /\ Q s) r <-> (readSPM M P r /\ readSPM M Q r).
Proof.
  unfold readSPM, applySPM. split.
  - intro H. split; intro s; specialize (H s); rewrite spAppM_repr in H;
      apply spAppM_repr; intro Hc; exact (proj1 (H Hc)) || exact (proj2 (H Hc)).
  - intros [H1 H2] s. specialize (H1 s). specialize (H2 s).
    rewrite spAppM_repr in H1. rewrite spAppM_repr in H2. apply spAppM_repr.
    intro Hc. exact (conj (H1 Hc) (H2 Hc)).
Qed.

(* ----------------------------------------------------------------- *)
(** *** Two independent monad-valued SP observations                  *)
(* ----------------------------------------------------------------- *)

(** [obsASP] and [obsDSLP] are now defined *separately*, straight off the
    program's outcome predicate, and land in *different* monads — they
    are no longer two readings ([asp] / [dslp]) applied to one shared
    [obsRel] object.  The shapes are dual:

      [obsASP  m s p r  =  p /\ (m can reach r from s)]      (additive)
      [obsDSLP m s p r  =  (m can reach r from s) -> p]      (multiplicative)

    Each is a monad morphism into its own monad ([obsASPmorph_ret]/[obsASPmorph_bind],
    [obsDSLPmorph_ret]/[obsDSLPmorph_bind]).  That both definitions mention the
    program's outcome set is unavoidable — that is what an observation is;
    what is gone is the single spec object with four readings hung off it. *)
Module SPMonadObs.

  Definition obsASP {S A} (m : stdivexcnd S A) : SPStExc S A :=
    mkStateT (fun s => @mkOptionT SPPure _
      (ofSet (fun r => unOptionT (unOptionT (runStateT m s)) (Some r)))).

  Definition obsDSLP {S A} (m : stdivexcnd S A) : ProgSPM S A :=
    mkStateT (fun s => @mkOptionT PureSPM _
      (ofCoSet (fun r => unOptionT (unOptionT (runStateT m s)) (Some r)))).

  Definition tripleJoin {S A} (obs : stdivexcnd S A -> SPStExc S A)
    (prog : stdivexcnd S A) (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, readSP (obs prog) pre r -> post r
    | Under => forall r, post r -> readSP (obs prog) pre r
    end.

  Definition tripleMeet {S A} (obs : stdivexcnd S A -> ProgSPM S A)
    (prog : stdivexcnd S A) (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, readSPM (obs prog) pre r -> post r
    | Under => forall r, post r -> readSPM (obs prog) pre r
    end.

End SPMonadObs.

Lemma applySP_obsASP {S A} (m : stdivexcnd S A) s p r :
  applySP (SPMonadObs.obsASP m) s p r <-> (p /\ obsRel m s r).
Proof.
  unfold applySP, SPMonadObs.obsASP, spApp, ofSet. cbn.
  rewrite obsRel_outcomes. tauto.
Qed.

Lemma applySPM_obsDSLP {S A} (m : stdivexcnd S A) s p r :
  applySPM (SPMonadObs.obsDSLP m) s p r <-> (obsRel m s r -> p).
Proof.
  unfold applySPM, SPMonadObs.obsDSLP, spAppM, ofCoSet. cbn.
  rewrite obsRel_outcomes. tauto.
Qed.

(** The two readings recover the old [asp] / [dslp] observations, so both
    triples coincide with the original [tripleSP] and the whole SP
    taxonomy transports as before. *)
Lemma readSP_obsASP {S A} (m : stdivexcnd S A) pre r :
  readSP (SPMonadObs.obsASP m) pre r <-> obsASP m pre r.
Proof.
  unfold readSP, obsASP, asp. split.
  - intros [s H]. rewrite applySP_obsASP in H. exists s. exact H.
  - intros [s H]. exists s. rewrite applySP_obsASP. exact H.
Qed.

Lemma readSPM_obsDSLP {S A} (m : stdivexcnd S A) pre r :
  readSPM (SPMonadObs.obsDSLP m) pre r <-> obsDSLP m pre r.
Proof.
  unfold readSPM, obsDSLP, dslp. split.
  - intros H s. specialize (H s). rewrite applySPM_obsDSLP in H. exact H.
  - intros H s. rewrite applySPM_obsDSLP. exact (H s).
Qed.

Lemma tripleJoin_ASP {S A} (prog : stdivexcnd S A) kind pre post :
  SPMonadObs.tripleJoin SPMonadObs.obsASP prog kind pre post <->
  tripleSP obsASP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (readSP_obsASP prog pre r) (H r Hr))
          | exact (proj2 (readSP_obsASP prog pre r) (H r Hr))
          | apply H; exact (proj1 (readSP_obsASP prog pre r) Hr)
          | apply H; exact (proj2 (readSP_obsASP prog pre r) Hr) ].
Qed.

Lemma tripleMeet_DSLP {S A} (prog : stdivexcnd S A) kind pre post :
  SPMonadObs.tripleMeet SPMonadObs.obsDSLP prog kind pre post <->
  tripleSP obsDSLP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (readSPM_obsDSLP prog pre r) (H r Hr))
          | exact (proj2 (readSPM_obsDSLP prog pre r) (H r Hr))
          | apply H; exact (proj1 (readSPM_obsDSLP prog pre r) Hr)
          | apply H; exact (proj2 (readSPM_obsDSLP prog pre r) Hr) ].
Qed.

(* ----------------------------------------------------------------- *)
(** *** Both observations are monad morphisms                         *)
(* ----------------------------------------------------------------- *)

Definition eqProgSPM {S A} (M N : ProgSPM S A) : Prop :=
  forall s p r, applySPM M s p r <-> applySPM N s p r.

Lemma eqProgSPM_eq1 {S A} (M N : ProgSPM S A) : eqProgSPM M N <-> eq1 M N.
Proof. split; intro H; exact H. Qed.

Theorem obsASPmorph_ret {S A} (a : A) :
  eq1 (SPMonadObs.obsASP (ret a : stdivexcnd S A)) (ret a).
Proof.
  apply (proj1 (eqProgSP_eq1 _ _)). intros s p r.
  rewrite applySP_obsASP, applySP_ret. split.
  - intros [Hp Hrel]. split; [exact Hp|].
    unfold obsRel in Hrel. destruct r as [[b s']|]; cbn in Hrel; congruence.
  - intros [Hp Hrel]. split; [exact Hp|].
    unfold obsRel. destruct r as [[b s']|]; cbn; congruence.
Qed.

Theorem obsASPmorph_bind {S A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
  eq1 (SPMonadObs.obsASP (x >>= f))
      (SPMonadObs.obsASP x >>= (fun a => SPMonadObs.obsASP (f a))).
Proof.
  apply (proj1 (eqProgSP_eq1 _ _)). intros s p r.
  rewrite applySP_obsASP, applySP_bind. split.
  - intros [Hp Hrel]. apply obsRel_bind in Hrel.
    destruct Hrel as [[a [s' [Hx Hf]]] | [Hx Heq]].
    + exists (Some (a, s')). split.
      * apply applySP_obsASP. split; assumption.
      * apply applySP_obsASP. split; [exact I | exact Hf].
    + exists None. split; [apply applySP_obsASP; split; assumption | exact Heq].
  - intros [oas [Hm HK]]. rewrite applySP_obsASP in Hm. destruct Hm as [Hp Hx].
    split; [exact Hp|]. apply obsRel_bind. destruct oas as [[a s']|].
    + left. exists a, s'. split; [exact Hx|].
      rewrite applySP_obsASP in HK. exact (proj2 HK).
    + right. split; [exact Hx | exact HK].
Qed.

Theorem obsDSLPmorph_ret {S A} (a : A) :
  eq1 (SPMonadObs.obsDSLP (ret a : stdivexcnd S A)) (ret a).
Proof.
  apply (proj1 (eqProgSPM_eq1 _ _)). intros s p r.
  rewrite applySPM_obsDSLP, applySPM_ret. split.
  - intros H Heq. apply H. subst r. unfold obsRel. cbn. reflexivity.
  - intros H Hrel. apply H.
    unfold obsRel in Hrel. destruct r as [[b s']|]; cbn in Hrel; congruence.
Qed.

Theorem obsDSLPmorph_bind {S A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
  eq1 (SPMonadObs.obsDSLP (x >>= f))
      (SPMonadObs.obsDSLP x >>= (fun a => SPMonadObs.obsDSLP (f a))).
Proof.
  apply (proj1 (eqProgSPM_eq1 _ _)). intros s p r.
  rewrite applySPM_obsDSLP. split.
  - intro H. apply applySPM_bind. intro oas.
    destruct oas as [[a s']|]; apply applySPM_obsDSLP; intro Hx.
    + apply applySPM_obsDSLP. intro Hf. apply H. apply obsRel_bind.
      left. exists a, s'. split; assumption.
    + intro Heq. apply H. apply obsRel_bind. right. split; assumption.
  - intro H. pose proof (proj1 (applySPM_bind _ _ s p r) H) as H'.
    intro Hrel. apply obsRel_bind in Hrel.
    destruct Hrel as [[a [s' [Hx Hf]]] | [Hx Heq]].
    + specialize (H' (Some (a, s'))). rewrite applySPM_obsDSLP in H'.
      specialize (H' Hx). rewrite applySPM_obsDSLP in H'. exact (H' Hf).
    + specialize (H' None). rewrite applySPM_obsDSLP in H'.
      exact (H' Hx Heq).
Qed.

(* ----------------------------------------------------------------- *)
(** *** No-go: [obsDSP] and [obsASLP] fit NEITHER monad               *)
(* ----------------------------------------------------------------- *)

(** The requested signatures [obsDSP : stdivexcnd S A -> ProgSPM S A] and
    [obsASLP : stdivexcnd S A -> SPStExc S A] cannot be realised, and neither
    can the swapped assignment.  The obstruction is sharp: DSP and ASLP
    preserve *binary* meets/joins respectively ([obsDSP_meet2],
    [obsASLP_join2]) but fail the *empty* ones —

      [obsDSP  pre r = (r is reachable at all) /\ (all reachers satisfy pre)]
        so [obsDSP (fun _ => True) r] is FALSE at an unreachable [r]
        (no top-preservation, which every meet reading has);

      [obsASLP pre r = (some reacher satisfies pre) \/ (all reachers do)]
        so [obsASLP (fun _ => False) r] is TRUE at an unreachable [r]
        (no strictness, which every join reading has).

    Both witnesses use [progEx], whose exception outcome [None] is
    unreachable. *)

Lemma progEx_no_exception : forall s, ~ obsRel progEx s None.
Proof. intros s H. unfold obsRel in H. cbn in H. sauto. Qed.

Theorem obsDSP_meet2 {S A} (m : stdivexcnd S A) (P Q : S -> Prop) r :
  obsDSP m (fun s => P s /\ Q s) r <-> (obsDSP m P r /\ obsDSP m Q r).
Proof.
  unfold obsDSP, asp, dslp. split.
  - intros [[s [[HP HQ] Hr]] Hall]. split.
    + split; [exists s; split; assumption | intros s' Hr'; exact (proj1 (Hall s' Hr'))].
    + split; [exists s; split; assumption | intros s' Hr'; exact (proj2 (Hall s' Hr'))].
  - intros [[[s [HP Hr]] HallP] [_ HallQ]].
    split; [exists s; split; [split; [exact HP | exact (HallQ s Hr)] | exact Hr] |].
    intros s' Hr'. split; [exact (HallP s' Hr') | exact (HallQ s' Hr')].
Qed.

Theorem obsASLP_join2 {S A} (m : stdivexcnd S A) (P Q : S -> Prop) r :
  obsASLP m (fun s => P s \/ Q s) r <-> (obsASLP m P r \/ obsASLP m Q r).
Proof.
  unfold obsASLP, asp, dslp. split.
  - intros [[s [[HP|HQ] Hr]] | Hall].
    + left. left. exists s. split; assumption.
    + right. left. exists s. split; assumption.
    + destruct (classic (exists s, obsRel m s r)) as [[s Hr] | Hno].
      * destruct (Hall s Hr) as [HP | HQ];
          [left; left; exists s; split; assumption
          | right; left; exists s; split; assumption].
      * left. right. intros s Hr. exfalso. apply Hno. exists s. exact Hr.
  - intros [[[s [HP Hr]] | Hall] | [[s [HQ Hr]] | Hall]].
    + left. exists s. split; [left; exact HP | exact Hr].
    + right. intros s Hr. left. exact (Hall s Hr).
    + left. exists s. split; [right; exact HQ | exact Hr].
    + right. intros s Hr. right. exact (Hall s Hr).
Qed.

Theorem obsDSP_not_top : ~ obsDSP progEx (fun _ => True) None.
Proof. intros [[s [_ Hrel]] _]. exact (progEx_no_exception s Hrel). Qed.

Theorem obsASLP_not_strict : obsASLP progEx (fun _ => False) None.
Proof. right. intros s Hrel. exact (progEx_no_exception s Hrel). Qed.

Theorem obsDSP_not_join2 :
  obsDSP progEx (fun s => preZero s \/ preNonZero s) (Some (tt, 42))
  /\ ~ obsDSP progEx preZero (Some (tt, 42))
  /\ ~ obsDSP progEx preNonZero (Some (tt, 42)).
Proof.
  split; [| split].
  - split.
    + exists 0. split; [left; reflexivity | exact (progEx_reaches_42 0)].
    + intros s _. unfold preZero, preNonZero.
      destruct s; [left; reflexivity | right; discriminate].
  - intros [_ Hd]. specialize (Hd 1 (progEx_reaches_42 1)).
    unfold preZero in Hd. discriminate.
  - intros [_ Hd]. specialize (Hd 0 (progEx_reaches_42 0)).
    unfold preNonZero in Hd. exact (Hd eq_refl).
Qed.

Theorem obsASLP_not_meet2 :
  ~ obsASLP progEx (fun s => preZero s /\ preNonZero s) (Some (tt, 42))
  /\ obsASLP progEx preZero (Some (tt, 42))
  /\ obsASLP progEx preNonZero (Some (tt, 42)).
Proof.
  split; [| split].
  - intros [[s [[H1 H2] _]] | Hd].
    + exact (H2 H1).
    + destruct (Hd 0 (progEx_reaches_42 0)) as [_ Hne]. exact (Hne eq_refl).
  - left. exists 0. split; [reflexivity | exact (progEx_reaches_42 0)].
  - left. exists 1. split; [discriminate | exact (progEx_reaches_42 1)].
Qed.

(** The requested assignment. *)
Corollary no_ProgSPM_for_obsDSP :
  ~ exists M : ProgSPM nat unit, forall pre r, readSPM M pre r <-> obsDSP progEx pre r.
Proof.
  intros [M HM]. apply obsDSP_not_top.
  apply (proj1 (HM (fun _ => True) None)). apply readSPM_top.
Qed.

Corollary no_ProgSP_for_obsASLP :
  ~ exists M : SPStExc nat unit, forall pre r, readSP M pre r <-> obsASLP progEx pre r.
Proof.
  intros [M HM]. apply (readSP_strict M None).
  apply (proj2 (HM (fun _ => False) None)). exact obsASLP_not_strict.
Qed.

(** The swapped assignment fails too, so there is no rescue by exchanging
    the two monads. *)
Corollary no_ProgSP_for_obsDSP :
  ~ exists M : SPStExc nat unit, forall pre r, readSP M pre r <-> obsDSP progEx pre r.
Proof.
  intros [M HM]. destruct obsDSP_not_join2 as [Hj [Hz Hnz]].
  apply (proj2 (HM _ _)) in Hj. apply readSP_join2 in Hj.
  destruct Hj as [H | H]; [apply Hz | apply Hnz]; exact (proj1 (HM _ _) H).
Qed.

Corollary no_ProgSPM_for_obsASLP :
  ~ exists M : ProgSPM nat unit, forall pre r, readSPM M pre r <-> obsASLP progEx pre r.
Proof.
  intros [M HM]. destruct obsASLP_not_meet2 as [Hn [Hz Hnz]].
  apply Hn. apply (proj1 (HM _ _)). apply readSPM_meet2.
  split; apply (proj2 (HM _ _)); assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** *** What does work for DSP / ASLP: the product monad              *)
(* ----------------------------------------------------------------- *)

(** [ProgSPB S A = SPStExc S A * ProgSPM S A] is the product of the two
    monads (componentwise [ret]/[bind]; [MonadLawsE] componentwise from
    the two factors).  [obsDSP] and [obsASLP] land there — a DSP/ASLP
    observation must carry BOTH the additive and the multiplicative
    element, and the two differ only in how the pair is read (meet vs
    join).  This is forced: [dsp = asp /\ dslp] and [aslp = asp \/ dslp]
    ([SPostArr.v]'s [dsp_asp_dslp] / [aslp_asp_dslp]) are the meet and join
    of the two extremes, and neither is an extreme itself.

    Note this breaks the [stateT S (optionT base)] shape used elsewhere:
    the product is taken at the outer level, which is what makes the
    morphism laws componentwise. *)

Definition ProgSPB (S : Type) : Type -> Type :=
  fun A => (SPStExc S A * ProgSPM S A)%type.

Definition retProgSPB {S A} (a : A) : ProgSPB S A := (ret a, ret a).
Definition bindProgSPB {S A B} (m : ProgSPB S A) (k : A -> ProgSPB S B) : ProgSPB S B :=
  (bind (fst m) (fun a => fst (k a)), bind (snd m) (fun a => snd (k a))).

#[global] Instance Monad__ProgSPB {S} : Monad (ProgSPB S) :=
  {| ret := fun _ => @retProgSPB S _ ;
     bind := fun _ _ => @bindProgSPB S _ _ |}.

#[global] Instance Eq1__ProgSPB {S} : Eq1 (ProgSPB S) :=
  fun A m n => eq1 (fst m) (fst n) /\ eq1 (snd m) (snd n).

#[global] Instance Eq1Equivalence__ProgSPB {S}
  : @Eq1Equivalence (ProgSPB S) _ Eq1__ProgSPB.
Proof.
  intro A. constructor.
  - intro x. split; reflexivity.
  - intros x y [H1 H2]. split; symmetry; assumption.
  - intros x y z [H1 H2] [K1 K2]. split; etransitivity; eassumption.
Qed.

#[local] Existing Instance MonadLawsE__ProgSP.
#[local] Existing Instance MonadLawsE__ProgSPM.

#[global] Instance MonadLawsE__ProgSPB {S}
  : @MonadLawsE (ProgSPB S) Eq1__ProgSPB _.
Proof.
  constructor.
  - intros A B f x. split;
      [ exact (bind_ret_l (M := SPStExc S) A B (fun a => fst (f a)) x)
      | exact (bind_ret_l (M := ProgSPM S) A B (fun a => snd (f a)) x) ].
  - intros A x. split;
      [ exact (bind_ret_r (M := SPStExc S) A (fst x))
      | exact (bind_ret_r (M := ProgSPM S) A (snd x)) ].
  - intros A B C x f g. split;
      [ exact (bind_bind (M := SPStExc S) A B C (fst x)
                 (fun a => fst (f a)) (fun b => fst (g b)))
      | exact (bind_bind (M := ProgSPM S) A B C (snd x)
                 (fun a => snd (f a)) (fun b => snd (g b))) ].
  - intros A B x y [H1 H2] f g Hfg. split;
      [ apply (Proper_bind (M := SPStExc S)) | apply (Proper_bind (M := ProgSPM S)) ];
      solve [ assumption | intro a; exact (proj1 (Hfg a)) | intro a; exact (proj2 (Hfg a)) ].
Qed.

Module SPMonadObsB.

  Definition obsDSP {S A} (m : stdivexcnd S A) : ProgSPB S A :=
    (SPMonadObs.obsASP m, SPMonadObs.obsDSLP m).

  Definition obsASLP {S A} (m : stdivexcnd S A) : ProgSPB S A :=
    (SPMonadObs.obsASP m, SPMonadObs.obsDSLP m).

  Definition readMeet {S A} (M : ProgSPB S A) (pre : S -> Prop) r : Prop :=
    readSP (fst M) pre r /\ readSPM (snd M) pre r.

  Definition readJoin {S A} (M : ProgSPB S A) (pre : S -> Prop) r : Prop :=
    readSP (fst M) pre r \/ readSPM (snd M) pre r.

  Definition tripleMeet {S A} (obs : stdivexcnd S A -> ProgSPB S A)
    (prog : stdivexcnd S A) (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, readMeet (obs prog) pre r -> post r
    | Under => forall r, post r -> readMeet (obs prog) pre r
    end.

  Definition tripleJoin {S A} (obs : stdivexcnd S A -> ProgSPB S A)
    (prog : stdivexcnd S A) (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, readJoin (obs prog) pre r -> post r
    | Under => forall r, post r -> readJoin (obs prog) pre r
    end.

End SPMonadObsB.

Lemma readMeet_obsDSP {S A} (m : stdivexcnd S A) pre r :
  SPMonadObsB.readMeet (SPMonadObsB.obsDSP m) pre r <-> obsDSP m pre r.
Proof.
  unfold SPMonadObsB.readMeet, SPMonadObsB.obsDSP, obsDSP. cbn.
  pose proof (readSP_obsASP m pre r) as Ha. unfold obsASP in Ha.
  pose proof (readSPM_obsDSLP m pre r) as Hd. unfold obsDSLP in Hd.
  tauto.
Qed.

Lemma readJoin_obsASLP {S A} (m : stdivexcnd S A) pre r :
  SPMonadObsB.readJoin (SPMonadObsB.obsASLP m) pre r <-> obsASLP m pre r.
Proof.
  unfold SPMonadObsB.readJoin, SPMonadObsB.obsASLP, obsASLP. cbn.
  pose proof (readSP_obsASP m pre r) as Ha. unfold obsASP in Ha.
  pose proof (readSPM_obsDSLP m pre r) as Hd. unfold obsDSLP in Hd.
  tauto.
Qed.

Theorem obsDSPB_ret {S A} (a : A) :
  eq1 (SPMonadObsB.obsDSP (ret a : stdivexcnd S A)) (ret a).
Proof. split; [exact (obsASPmorph_ret a) | exact (obsDSLPmorph_ret a)]. Qed.

Theorem obsDSPB_bind {S A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
  eq1 (SPMonadObsB.obsDSP (x >>= f))
      (SPMonadObsB.obsDSP x >>= (fun a => SPMonadObsB.obsDSP (f a))).
Proof. split; [exact (obsASPmorph_bind x f) | exact (obsDSLPmorph_bind x f)]. Qed.

Lemma tripleMeet_DSP {S A} (prog : stdivexcnd S A) kind pre post :
  SPMonadObsB.tripleMeet SPMonadObsB.obsDSP prog kind pre post <->
  tripleSP obsDSP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (readMeet_obsDSP prog pre r) (H r Hr))
          | exact (proj2 (readMeet_obsDSP prog pre r) (H r Hr))
          | apply H; exact (proj1 (readMeet_obsDSP prog pre r) Hr)
          | apply H; exact (proj2 (readMeet_obsDSP prog pre r) Hr) ].
Qed.

Lemma tripleJoin_ASLP {S A} (prog : stdivexcnd S A) kind pre post :
  SPMonadObsB.tripleJoin SPMonadObsB.obsASLP prog kind pre post <->
  tripleSP obsASLP prog kind pre post.
Proof.
  destruct kind; cbn; split; intros H r Hr;
    first [ exact (proj1 (readJoin_obsASLP prog pre r) (H r Hr))
          | exact (proj2 (readJoin_obsASLP prog pre r) (H r Hr))
          | apply H; exact (proj1 (readJoin_obsASLP prog pre r) Hr)
          | apply H; exact (proj2 (readJoin_obsASLP prog pre r) Hr) ].
Qed.
