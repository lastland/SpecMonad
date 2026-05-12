(** * Observation functions for [nditprog].

    SP observation: maps [nditprog S A] to [ASPostArr S A].
    The three-valued outcome space ([Some (Some _)], [Some None],
    [None]) is collapsed into [option (A * S)]:
    - [Some (a, s')] from converging outcomes
    - [None] from exceptions OR divergence

    WP observations: [obsDWP] / [obsDWLP] (demonic total / partial)
    and [obsAWP] / [obsAWLP] (angelic total / partial) map into
    [ProgWP S A].  Inclusion proofs: Theorem 3.7. *)

From Coq Require Import Lia Classical_Prop.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg WP Pred SPost.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** SP observations                                                *)
(* ================================================================= *)

Section NonDetItObservationSP.

  Variable S : Type.

  (** Reachability relation.

      For [Some (a, s')]: there is a converging path.
      For [None]: there is an exception path.

      Divergence is NOT a reachable final state — it is the absence of
      reaching any final state (dual to how divergence in WP is the
      absence of termination). *)
  Definition obsRel {A} (m : nditprog S A)
    : Pred (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      match r with
      | Some (a, s') =>
          unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
      | None =>
          unOptionT (unOptionT (runStateT m s)) (Some None)
      end.

  (** Angelic strongest postcondition (total). *)
  Definition obsASP {A} (m : nditprog S A) : ASPostArr S A :=
    mkASP (obsRel m).

  (** Demonic strongest liberal postcondition. *)
  Definition obsDSLP {A} (m : nditprog S A) : DSLPostArr S A :=
    mkDSLP (obsRel m).

  #[program] Definition obsDSP {A} (m : nditprog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (obsASP m) pre r /\ sp_pt (obsDSLP m) pre r.

  #[program] Definition obsASLP {A} (m : nditprog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (obsASP m) pre r \/ sp_pt (obsDSLP m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  #[program] Theorem obsDSP_sub_obsASP {A} (m : nditprog S A) pre r :
    obsDSP m pre r -> sp_pt (obsASP m) pre r.
  Proof. intros [H _]. exact H. Qed.

  #[program] Theorem obsDSP_sub_obsDSLP {A} (m : nditprog S A) pre r :
    obsDSP m pre r -> sp_pt (obsDSLP m) pre r.
  Proof. intros [_ H]. exact H. Qed.

  #[program] Theorem obsASP_sub_obsASLP {A} (m : nditprog S A) pre r :
    sp_pt (obsASP m) pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  #[program] Theorem obsDSLP_sub_obsASLP {A} (m : nditprog S A) pre r :
    sp_pt (obsDSLP m) pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : nditprog S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP, obsASP, obsDSLP; simpl.
    symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : nditprog S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP, obsASP, obsDSLP; simpl.
    symmetry. apply aslp_asp_dslp.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.8: Contrapositive transformers SP               *)
  (* -------------------------------------------------------------- *)

  #[program] Theorem obsASP_contrapositive {A} (m : nditprog S A) pre r :
    sp_pt (obsASP m) pre r <->
    ~ sp_pt (obsDSLP m) (fun x => ~ pre x) r.
  Proof.
    unfold obsASP, obsDSLP; simpl.
    unfold asp, dslp. split.
    - intros [a [Hpre Hrel]] Hall.
      exact (Hall a Hrel Hpre).
    - intro Hnn.
      apply NNPP. intro Habs.
      apply Hnn. intros a Hrel Hpre.
      apply Habs. exists a. exact (conj Hpre Hrel).
  Qed.

  Theorem obsDSP_contrapositive {A} (m : nditprog S A) pre r :
    obsDSP m pre r <->
    ~ obsASLP m (fun x => ~ pre x) r.
  Proof.
    unfold obsDSP, obsASLP, obsASP, obsDSLP.
    simpl. unfold asp, dslp.
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

Inductive approximationKind := | Correct | Incorrect.

(** Typeclass for coercing an SP observation result to a predicate
    transformer [(unit * S -> Prop) -> option (A * S) -> Prop]:
    - a plain predicate transformer is the identity;
    - [ASPostArr S A] and [DSLPostArr S A] (sigma types) have their
      [sp_pt] extracted;
    - a plain relation [Pred (unit * S) (option (A * S))] is lifted
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
  @AsSPObs S A (Pred (unit * S) (option (A * S))) :=
  fun R => asp R.

Definition tripleSP {S A T} `{@AsSPObs S A T}
  (obs : nditprog S A -> T)
  (prog : nditprog S A)
  (is_correct : approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop :=
    let pre' := fun '(tt, s) => pre s in
    if is_correct then
      forall r, as_sp_obs (obs prog) pre' r -> post r
    else
      forall r, post r -> as_sp_obs (obs prog) pre' r.

(* ================================================================= *)
(** ** SP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(** All reachable converging results have state >= 42. *)
Theorem progA_all :
  tripleSP obsRel progA Correct
    (fun _ => True)
    (fun r =>
      match r with
      | Some (_, s') => s' >= 42
      | None => False
      end).
Proof.
  unfold tripleSP, as_sp_obs, AsSPObs_Pred, asp.
  intros r [sigma [_ Hrel]].
  destruct r as [[[] s'] |]; cbn in Hrel; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  tripleSP obsRel progA Incorrect
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP, as_sp_obs, AsSPObs_Pred, asp.
  intros r ->. exists (tt, 0). split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  tripleSP obsRel progA Incorrect
    (fun _ => True)
    (fun r => r = Some (tt, 43)).
Proof.
  unfold tripleSP, as_sp_obs, AsSPObs_Pred, asp.
  intros r ->. exists (tt, 0). split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(* ================================================================= *)
(** ** Examples: nondeterminism + divergence                          *)
(* ================================================================= *)

Example progB : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (spinP _).

(** State 42 is reachable (via the converging branch). *)
Theorem progB_42 :
  tripleSP obsRel progB Incorrect
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP, as_sp_obs, AsSPObs_Pred, asp.
  intros r ->. exists (tt, 0). split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** Failure ([None]) is NOT reachable: the divergent branch does not
    contribute an exception, and divergence is the absence of reaching
    any final state. *)
Theorem progB_not_None :
  tripleSP obsRel progB Correct
    (fun _ => True)
    (fun r => r <> None).
Proof.
  unfold tripleSP, as_sp_obs, AsSPObs_Pred, asp.
  intros r [sigma [_ Hrel]] ->. cbn in Hrel. sauto.
Qed.

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

End NDItObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.

(* ================================================================= *)
(** ** WP triples                                                    *)
(* ================================================================= *)

Definition pp2wp {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : ProgWP S A :=
  mkStateT (fun s0 => @mkOptionT PureWP _ (fun p => pre s0 /\ (forall r, post r -> p r))).

Definition ordProgWP {S A} (m1 m2 : ProgWP S A) : Prop :=
  forall s post, unOptionT (runStateT m1 s) post -> unOptionT (runStateT m2 s) post.

Definition tripleWP {S A} 
  (obs : nditprog S A -> ProgWP S A)
  (prog : nditprog S A)
  (is_correct:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop 
  :=
    if is_correct then
      ordProgWP (pp2wp pre post) (obs prog)
    else 
      ordProgWP (obs prog) (pp2wp pre post).

(* ================================================================= *)
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)


Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  tripleWP obsDWP progA Correct
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP, ordProgWP. cbn. intros s0 p [_ Hpost] [[[]|]|] H.
  - apply Hpost. cbn. sauto.
  - sauto.
  - sauto.
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 : 
  not (
    tripleWP obsDWP progA Correct
      (fun _ => True)
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 42
        | None => False
        end)).
Proof.
  intro contra.
  unfold tripleWP, ordProgWP in contra. cbn in contra.
  specialize (contra 0 _ (conj I (fun r h => h)) (Some (Some (tt, 43)))).
  sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  tripleWP obsAWP progA Correct
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 p [_ Hpost]. cbn.
  exists (Some (tt, 42)). split; [sauto | apply Hpost; sauto].
Qed.

Theorem progA_AWP_43 :
  tripleWP obsAWP progA Correct
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 43
      | None => False
      end).
Proof.
  intros s0 p [_ Hpost]. cbn.
  exists (Some (tt, 43)). split; [sauto | apply Hpost; sauto].
Qed.

(* ================================================================= *)
(** ** WP examples: nondeterminism + divergence                       *)
(* ================================================================= *)

Example progB_DWP := obsDWP progB.
Example progB_DWLP := obsDWLP progB.
Example progB_AWP := obsAWP progB.

(** DWP is unprovable: the divergent branch forces [False]. *)
Theorem progB_DWP_unprovable :
  not (
    tripleWP obsDWP progB Correct
      (fun _ => True)
      (fun r : option (unit * nat) =>
          match r with
          | Some (_, s) => s = 42
          | None => False
          end)).
Proof.
  intro contra.
  unfold tripleWP, ordProgWP in contra. cbn in contra.
  specialize (contra 0 _ (conj I (fun r h => h)) None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored. *)
Theorem progB_DWLP_42 :
  tripleWP obsDWLP progB Correct
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 p [_ Hpost]. cbn. intros [[[]|]|] H;
    [apply Hpost; sauto | sauto | exact I].
Qed.

(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  tripleWP obsAWP progB Correct
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 p [_ Hpost]. cbn.
  exists (Some (tt, 42)). split; [sauto | apply Hpost; sauto].
Qed.

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
      tripleWP obsDWP m Correct pre post ->
      tripleWP obsDWLP m Correct pre post.
  Proof.
    intros A m pre post H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p preH.
    apply obsDWP_incl_obsDWLP.
    exact (H s0 p preH).
  Qed.

  Theorem cc_dwp_implies_awp :
    forall A (m: nditprog S A) pre post,
      (forall s0, pre s0 -> exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsDWP m Correct pre post ->
      tripleWP obsAWP m Correct pre post.
  Proof.
    intros A m pre post Hne H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p preH.
    apply obsDWP_incl_obsAWP.
    - exact (Hne s0 (proj1 preH)).
    - exact (H s0 p preH).
  Qed.

  Theorem cc_awp_implies_awlp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m Correct pre post ->
      tripleWP obsAWLP m Correct pre post.
  Proof.
    intros A m pre post H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p preH.
    apply obsAWP_incl_obsAWLP.
    exact (H s0 p preH).
  Qed.

  Theorem cc_dwlp_implies_awlp :
    forall A (m: nditprog S A) pre post,
      (forall s0, pre s0 -> exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsDWLP m Correct pre post ->
      tripleWP obsAWLP m Correct pre post.
  Proof.
    intros A m pre post Hne H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p preH.
    apply obsDWLP_incl_obsAWLP.
    - exact (Hne s0 (proj1 preH)).
    - exact (H s0 p preH).
  Qed.

  Theorem ii_awlp_implies_dwlp :
    forall A (m: nditprog S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsAWLP m Incorrect pre post ->
      tripleWP obsDWLP m Incorrect pre post.
  Proof.
    intros A m pre post Hne H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p Hdwlp.
    apply H.
    apply obsDWLP_incl_obsAWLP.
    - exact (Hne s0).
    - exact Hdwlp.
  Qed.

  Theorem ii_dwlp_implies_dwp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m Incorrect pre post ->
      tripleWP obsDWP m Incorrect pre post.
  Proof.
    intros A m pre post H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p Hdwp.
    apply H.
    apply obsDWP_incl_obsDWLP.
    exact Hdwp.
  Qed.

  Theorem ii_awlp_implies_awp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWLP m Incorrect pre post ->
      tripleWP obsAWP m Incorrect pre post.
  Proof.
    intros A m pre post H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p Hawp.
    apply H.
    apply obsAWP_incl_obsAWLP.
    exact Hawp.
  Qed.

  Theorem ii_awp_implies_dwp :
    forall A (m: nditprog S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsAWP m Incorrect pre post ->
      tripleWP obsDWP m Incorrect pre post.
  Proof.
    intros A m pre post Hne H.
    unfold tripleWP, ordProgWP in *.
    intros s0 p Hdwp.
    apply H.
    apply obsDWP_incl_obsAWP.
    - exact (Hne s0).
    - exact Hdwp.
  Qed.

  Theorem ci_awp_dwlp_contrapositive :
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m Incorrect (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsAWP m Correct pre post.
  Proof.
    intros A m pre post Hii.
    unfold tripleWP, ordProgWP in *.
    intros s0 p [Hpre _].
    apply NNPP. intro Hnawp.
    assert (Hdwlp : unOptionT (runStateT (obsDWLP m) s0) (fun r => ~ p r)).
    { apply NNPP. intro H.
      apply Hnawp.
      exact (proj2 (obsAWP_contrapositive_obsDWLP _ _ m s0 p) H). }
    exact (proj1 (Hii s0 _ Hdwlp) Hpre).
  Qed.

  Theorem ci_dwp_awlp_contrapositive :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWLP m Incorrect (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsDWP m Correct pre post.
  Proof.
    intros A m pre post Hii.
    unfold tripleWP, ordProgWP in *.
    intros s0 p [Hpre _].
    apply NNPP. intro Hndwp.
    assert (Hawlp : unOptionT (runStateT (obsAWLP m) s0) (fun r => ~ p r)).
    { apply NNPP. intro H.
      apply Hndwp.
      exact (proj2 (obsDWP_contrapositive_obsAWLP _ _ m s0 p) H). }
    exact (proj1 (Hii s0 _ Hawlp) Hpre).
  Qed.

  Theorem ci_awlp_dwp_contrapositive :
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWP m Incorrect (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsAWLP m Correct pre post.
  Proof.
    intros A m pre post Hii.
    unfold tripleWP, ordProgWP in *.
    intros s0 p [Hpre _].
    apply NNPP. intro Hnawlp.
    assert (Hdwp : unOptionT (runStateT (obsDWP m) s0) (fun r => ~ p r)).
    { unfold obsDWP, obsAWLP in *.
      cbn in Hnawlp |- *.
      destruct (runStateT m s0) as [[outcomes]].
      intros oa Hoa. destruct oa as [r|].
      - intro Hr. apply Hnawlp. left. exists r. exact (conj Hoa Hr).
      - exfalso. apply Hnawlp. right. exact Hoa. }
    exact (proj1 (Hii s0 _ Hdwp) Hpre).
  Qed.

  Theorem ci_dwlp_awp_contrapositive :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m Incorrect (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsDWLP m Correct pre post.
  Proof.
    intros A m pre post Hii.
    unfold tripleWP, ordProgWP in *.
    intros s0 p [Hpre _].
    apply NNPP. intro Hndwlp.
    assert (Hawp : unOptionT (runStateT (obsAWP m) s0) (fun r => ~ p r)).
    { unfold obsAWP, obsDWLP in *.
      cbn in Hndwlp |- *.
      destruct (runStateT m s0) as [[outcomes]].
      apply NNPP. intro Hnawp.
      apply Hndwlp.
      intros oa Hoa. destruct oa as [r|].
      - apply NNPP. intro Hr. apply Hnawp. exists r. exact (conj Hoa Hr).
      - exact I. }
    exact (proj1 (Hii s0 _ Hawp) Hpre).
  Qed.
End TaxonomyWPTransformers.

(* ================================================================= *)
(** ** Taxonomy of transformers (connecting the halves of Figure 5)                        *)
(* ================================================================= *)
Section TaxonomyConnection.
  Variable S : Type.

  (** The [obsDWP] triple is vacuous on programs that diverge from
      every state (e.g. [spinP]), so reaching the [obsASP] side requires
      ruling out divergent outcomes and supplying a witness state. *)
  Theorem ii_dwp_implies_asp :
    inhabited S ->
    forall A (m: nditprog S A) pre post,
      (forall s oa, unOptionT (unOptionT (runStateT m s)) oa -> oa <> None) ->
      tripleWP obsDWP m Incorrect pre post ->
      tripleSP obsASP m Incorrect pre post.
  Proof.
    intros [s0] A m pre post Hnd Hwp r Hpost.
    unfold tripleSP, as_sp_obs, AsSPObs_ASP, obsASP.
    simpl proj1_sig. unfold asp, obsRel.
    exists (tt, s0).
    unfold tripleWP, ordProgWP, pp2wp, obsDWP in Hwp. cbn in Hwp.
    specialize (Hwp s0). specialize (Hnd s0). cbn in Hnd.
    destruct (runStateT m s0) as [[outcomes]] eqn:Hm. cbn in Hwp, Hnd.
    assert (Hreach : outcomes (Some r)).
    { apply NNPP. intro Hcontra.
      destruct (Hwp (fun r' => r' <> r)) as [_ Himpl].
      - intros oa Hoa. destruct oa as [r'|].
        + intro Heq. subst r'. exact (Hcontra Hoa).
        + exfalso. exact (Hnd None Hoa eq_refl).
      - exact (Himpl r Hpost eq_refl). }
    split.
    - destruct (Hwp (fun _ => True)) as [Hpre _].
      + intros oa Hoa.
        destruct oa as [r'|]; [exact I | exfalso; exact (Hnd None Hoa eq_refl)].
      + exact Hpre.
    - destruct r as [[a s']|]; exact Hreach.
  Qed.

  (** [obsDWLP] tolerates divergent outcomes, so no no-divergence
      hypothesis is needed; only [S] inhabited. *)
  Theorem ii_dwlp_implies_asp :
    inhabited S ->
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m Incorrect pre post ->
      tripleSP obsASP m Incorrect pre post.
  Proof.
    intros [s0] A m pre post Hwp r Hpost.
    unfold tripleSP, as_sp_obs, AsSPObs_ASP, obsASP.
    simpl proj1_sig. unfold asp, obsRel.
    unfold tripleWP, ordProgWP, pp2wp, obsDWLP in Hwp. cbn in Hwp.
    assert (Hreach : exists s, unOptionT (unOptionT (runStateT m s)) (Some r)).
    { apply NNPP. intro Habs.
      specialize (Hwp s0 (fun r' => r' <> r)).
      destruct (runStateT m s0) as [[outcomes0]] eqn:Hm0. cbn in Hwp.
      destruct Hwp as [_ Himpl].
      - intros oa Hoa. destruct oa as [r'|]; [|exact I].
        intro Heq. subst r'. apply Habs. exists s0.
        rewrite Hm0. cbn. exact Hoa.
      - exact (Himpl r Hpost eq_refl). }
    destruct Hreach as [s Hreach].
    exists (tt, s).
    split.
    - specialize (Hwp s (fun _ => True)).
      destruct (runStateT m s) as [[outcomes]] eqn:Hm. cbn in Hwp.
      destruct Hwp as [Hpre _].
      + intros oa Hoa. destruct oa as [r'|]; exact I.
      + exact Hpre.
    - destruct r as [[a s']|]; exact Hreach.
  Qed.
End TaxonomyConnection.

(* ================================================================= *)
(** ** Counter-example: SP-Inc does NOT imply WP-Inc (DWP or DWLP)    *)
(* ================================================================= *)

(** The implications [ii_dwp_implies_asp] and [ii_dwlp_implies_asp]
    are one-directional.  The reverse implications fail because
    [tripleWP _ Incorrect] universally quantifies over states, while
    [tripleSP obsASP Incorrect] only requires an existential witness.

    Concretely, [pp2wp pre post (s) (p) = pre s /\ (forall r, post r -> p r)],
    so for every state [s] at which the program's WP holds for some
    [p], the precondition [pre s] must hold.  In particular, picking
    [p := fun _ => True] makes the DWP/DWLP antecedent hold whenever
    the program has at least one converging outcome from [s] and (for
    DWP) does not diverge there.  This forces [pre] to be true at
    *every* such state.  No analogous constraint is present in
    [tripleSP obsASP Incorrect].

    The example: a pure return in state [nat] with a pre-/post-
    condition pinning the state to [0].  Reachability from [s = 0]
    establishes the SP triple, but the WP triples both fail at any
    other state. *)

Example progRet : nditprog nat unit := ret tt.

Definition preEq0 : nat -> Prop := fun s => s = 0.
Definition postEq0 : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, 0).

(** The SP-Inc triple holds: state [0] reaches the only post-result. *)
Theorem progRet_asp_inc :
  tripleSP obsASP progRet Incorrect preEq0 postEq0.
Proof.
  unfold tripleSP, as_sp_obs, AsSPObs_ASP, obsASP, preEq0, postEq0.
  simpl proj1_sig. unfold asp, obsRel.
  intros r ->. exists (tt, 0). split; [reflexivity | cbn; reflexivity].
Qed.

(** Yet the DWP-Inc triple fails: instantiating at [s = 1] with
    [p := fun _ => True] satisfies the antecedent (no divergence,
    trivial postcondition), but forces [preEq0 1], i.e. [1 = 0]. *)
Theorem progRet_dwp_inc_fails :
  ~ tripleWP obsDWP progRet Incorrect preEq0 postEq0.
Proof.
  intro H.
  unfold tripleWP, ordProgWP, pp2wp, obsDWP, preEq0 in H. cbn in H.
  assert (Hant : forall oa : option (option (unit * nat)),
            oa = Some (Some (tt, 1)) ->
            match oa with Some _ => True | None => False end).
  { intros oa ->. exact I. }
  destruct (H 1 (fun _ => True) Hant) as [Hcontra _]. discriminate.
Qed.

(** Same counter-example refutes DWLP-Inc — the divergence-tolerant
    [True] branch does not help, because [progRet] never diverges. *)
Theorem progRet_dwlp_inc_fails :
  ~ tripleWP obsDWLP progRet Incorrect preEq0 postEq0.
Proof.
  intro H.
  unfold tripleWP, ordProgWP, pp2wp, obsDWLP, preEq0 in H. cbn in H.
  assert (Hant : forall oa : option (option (unit * nat)),
            oa = Some (Some (tt, 1)) ->
            match oa with Some _ => True | None => True end).
  { intros oa ->. exact I. }
  destruct (H 1 (fun _ => True) Hant) as [Hcontra _]. discriminate.
Qed.

(** Together these show: the WP-to-SP implications are strict, and
    no reverse implication (and hence no Galois connection between
    [tripleWP _ Incorrect] and [tripleSP obsASP Incorrect]) can hold
    without imposing further structural assumptions on [pre] (e.g.
    universality) and on the program's reachability. *)

(* ================================================================= *)
(** ** SP examples: the four reachability classes                    *)
(* ================================================================= *)

(** Program: [s <- get; orP (put (s + 1)) (put 42)]
    From state s, outcomes are: {(tt, s+1), (tt, 42)}.
    - [Some (tt, 1)] is exclusively reachable from s=0 (class 1)
    - [Some (tt, 42)] is reachable from all states (class 2)
    - [None] (exception) is unreachable (class 3)
    - [Some (tt, 99)] is exclusively reachable from s=98 (class 4) *)

Example progEx : nditprog nat unit :=
  s <- get ;;
  orP _ (put (s + 1)) (put 42).

Definition P0 : unit * nat -> Prop := fun '(tt, s) => s = 0.

(** -- Class 1: exclusively reachable from P — all four include it -- *)

#[program] Theorem progEx_asp_1 :
  sp_pt (obsASP progEx) P0 (Some (tt, 1)).
Proof.
  unfold obsASP, P0. simpl proj1_sig. unfold asp.
  exists (tt, 0). split; [reflexivity|].
  unfold obsRel. cbn.
  sauto.
Qed.

#[program] Theorem progEx_dslp_1 :
  sp_pt (obsDSLP progEx) P0 (Some (tt, 1)).
Proof.
  unfold obsDSLP, P0. simpl proj1_sig. unfold dslp.
  intros [[] s] Hrel. unfold obsRel in Hrel. cbn in Hrel.
  f_equal. f_equal. sauto lq: on.
Qed.

Theorem progEx_dsp_1 :
  obsDSP progEx P0 (Some (tt, 1)).
Proof.
  split; [exact progEx_asp_1 | exact progEx_dslp_1].
Qed.

Theorem progEx_aslp_1 :
  obsASLP progEx P0 (Some (tt, 1)).
Proof. left. exact progEx_asp_1. Qed.

(** -- Class 2: reachable from P and ¬P — asp and aslp include,
       dsp and dslp exclude -- *)

#[program] Theorem progEx_asp_42 :
  sp_pt (obsASP progEx) P0 (Some (tt, 42)).
Proof.
  unfold obsASP, P0. simpl proj1_sig. unfold asp.
  exists (tt, 0). split; [reflexivity|].
  unfold obsRel. cbn. sauto.
Qed.

#[program] Theorem progEx_dslp_not_42 :
  ~ sp_pt (obsDSLP progEx) P0 (Some (tt, 42)).
Proof.
  unfold obsDSLP, P0. simpl proj1_sig. unfold dslp.
  intro H. specialize (H (tt, 1)).
  assert (Hreach : obsRel progEx (tt, 1) (Some (tt, 42))).
  { unfold obsRel. cbn. sauto. }
  specialize (H Hreach). simpl in H. discriminate.
Qed.

Theorem progEx_dsp_not_42 :
  ~ obsDSP progEx P0 (Some (tt, 42)).
Proof.
  intros [_ H]. exact (progEx_dslp_not_42 H).
Qed.

Theorem progEx_aslp_42 :
  obsASLP progEx P0 (Some (tt, 42)).
Proof. left. exact progEx_asp_42. Qed.

(** -- Class 3: unreachable — dslp and aslp include,
       asp and dsp exclude -- *)

#[program] Theorem progEx_asp_not_None :
  ~ sp_pt (obsASP progEx) P0 None.
Proof.
  unfold obsASP, P0. simpl proj1_sig. unfold asp.
  intros [[[] s] [HP Hrel]].
  unfold obsRel in Hrel. cbn in Hrel. sauto.
Qed.

#[program] Theorem progEx_dslp_None :
  sp_pt (obsDSLP progEx) P0 None.
Proof.
  unfold obsDSLP, P0. simpl proj1_sig. unfold dslp.
  intros [[] s] Hrel.
  (** None (exception) is unreachable — the ∀ is vacuously true. *)
  unfold obsRel in Hrel. cbn in Hrel. sauto.
Qed.

Theorem progEx_dsp_not_None :
  ~ obsDSP progEx P0 None.
Proof.
  intros [H _]. exact (progEx_asp_not_None H).
Qed.

Theorem progEx_aslp_None :
  obsASLP progEx P0 None.
Proof. right. exact progEx_dslp_None. Qed.

(** -- Class 4: exclusively reachable from ¬P — none include -- *)

#[program] Theorem progEx_asp_not_99 :
  ~ sp_pt (obsASP progEx) P0 (Some (tt, 99)).
Proof.
  unfold obsASP, P0. simpl proj1_sig. unfold asp.
  intros [[[] s] [HP Hrel]]. subst.
  unfold obsRel in Hrel. cbn in Hrel. sauto lq: on.
Qed.

#[program] Theorem progEx_dslp_not_99 :
  ~ sp_pt (obsDSLP progEx) P0 (Some (tt, 99)).
Proof.
  unfold obsDSLP, P0. simpl proj1_sig. unfold dslp.
  intro H. specialize (H (tt, 98)).
  assert (Hreach : obsRel progEx (tt, 98) (Some (tt, 99))).
  { unfold obsRel. cbn. sauto. }
  specialize (H Hreach). simpl in H. discriminate.
Qed.

Theorem progEx_dsp_not_99 :
  ~ obsDSP progEx P0 (Some (tt, 99)).
Proof. intros [H _]. exact (progEx_asp_not_99 H). Qed.

Theorem progEx_aslp_not_99 :
  ~ obsASLP progEx P0 (Some (tt, 99)).
Proof.
  intros [H | H]; [exact (progEx_asp_not_99 H) |
                    exact (progEx_dslp_not_99 H)].
Qed.
