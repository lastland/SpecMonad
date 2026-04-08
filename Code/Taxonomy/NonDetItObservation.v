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
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg WP SPost.

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
    : SPArr (unit * S) (option (A * S)) :=
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
  (** *** Theorem 3.8: Contrapositive transformers                   *)
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
(** ** SP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(** All reachable converging results have state >= 42. *)
Theorem progA_all :
  forall s r,
    obsRel progA (tt, s) r ->
    match r with
    | Some (_, s') => s' >= 42
    | None => False
    end.
Proof.
  intros s [[] |] H; cbn in H; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  forall s, obsRel progA (tt, s) (Some (tt, 42)).
Proof. intros. cbn. sauto. Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  forall s, obsRel progA (tt, s) (Some (tt, 43)).
Proof. intros. cbn. sauto. Qed.

(* ================================================================= *)
(** ** Examples: nondeterminism + divergence                          *)
(* ================================================================= *)

Example progB : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (spinP _).

(** State 42 is reachable (via the converging branch). *)
Theorem progB_42 :
  forall s, obsRel progB (tt, s) (Some (tt, 42)).
Proof. intros. cbn. sauto. Qed.

(** Failure ([None]) is NOT reachable: the divergent branch does not
    contribute an exception, and divergence is the absence of reaching
    any final state. *)
Theorem progB_not_None :
  forall s, ~ obsRel progB (tt, s) None.
Proof.
  intros s H. cbn in H. sauto.
Qed.

(* ================================================================= *)
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  forall s, unOptionT (runStateT progA_DWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s >= 42
            | None => False
            end).
Proof.
  intros. cbn. intros [[[]|]|] H; sauto.
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 :
  not (forall s, unOptionT (runStateT progA_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 (Some (Some (tt, 43)))).
  sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). sauto.
Qed.

Theorem progA_AWP_43 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 43
            | None => False
            end).
Proof.
  intros. cbn.
  exists (Some (tt, 43)). sauto.
Qed.

(* ================================================================= *)
(** ** WP examples: nondeterminism + divergence                       *)
(* ================================================================= *)

Example progB_DWP := obsDWP progB.
Example progB_DWLP := obsDWLP progB.
Example progB_AWP := obsAWP progB.

(** DWP is unprovable: the divergent branch forces [False]. *)
Theorem progB_DWP_unprovable :
  not (forall s, unOptionT (runStateT progB_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored. *)
Theorem progB_DWLP_42 :
  forall s, unOptionT (runStateT progB_DWLP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn. intros [[[]|]|] H; try exact I; sauto.
Qed.

(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  forall s, unOptionT (runStateT progB_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). sauto.
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
