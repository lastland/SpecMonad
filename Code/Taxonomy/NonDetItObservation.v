(** * Observation functions for [nditprog].

    SP observation: maps [nditprog S A] to [ASPostArr S A].
    The three-valued outcome space ([Some (Some _)], [Some None],
    [None]) is collapsed into [option (A * S)]:
    - [Some (a, s')] from converging outcomes
    - [None] from exceptions OR divergence

    WP observations: [obsDWP] / [obsDWLP] (demonic total / partial)
    and [obsAWP] / [obsAWLP] (angelic total / partial) map into
    [ProgWP S A].  Inclusion proofs: Theorem 3.7. *)

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
    : Pred S (option (A * S)) :=
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
      [SPost.v], as are [spDSP]/[spASLP] (their meet/join). *)
  Definition obsASP {A} (m : nditprog S A)
    : Pred (S -> Prop) (option (A * S)) := asp (obsRel m). 
  Definition obsDSLP {A} (m : nditprog S A)
    : Pred (S -> Prop) (option (A * S)) := dslp (obsRel m).
  Definition obsDSP {A} (m : nditprog S A)
    : Pred (S -> Prop) (option (A * S)) := fun pre r => asp (obsRel m) pre r /\ dslp (obsRel m) pre r.
  Definition obsASLP {A} (m : nditprog S A)
    : Pred (S -> Prop) (option (A * S)) := fun pre r => asp (obsRel m) pre r \/ dslp (obsRel m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  Theorem obsDSP_sub_obsASP {A} (m : nditprog S A) pre r :
    obsDSP m pre r -> obsASP m pre r.
  Proof. intros [H _]. exact H. Qed.

  Theorem obsDSP_sub_obsDSLP {A} (m : nditprog S A) pre r :
    obsDSP m pre r -> obsDSLP m pre r.
  Proof. intros [_ H]. exact H. Qed.

  Theorem obsASP_sub_obsASLP {A} (m : nditprog S A) pre r :
    obsASP m pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem obsDSLP_sub_obsASLP {A} (m : nditprog S A) pre r :
    obsDSLP m pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : nditprog S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP. symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : nditprog S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP. symmetry. apply aslp_asp_dslp.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.8: Contrapositive transformers SP               *)
  (* -------------------------------------------------------------- *)

  Theorem obsASP_contrapositive {A} (m : nditprog S A) pre r :
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

  Theorem obsDSP_contrapositive {A} (m : nditprog S A) pre r :
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
  (obs : nditprog S A -> (S -> Prop) -> option (A * S) -> Prop)
  (prog : nditprog S A)
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

(* ================================================================= *)
(** ** SP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(** All reachable converging results have state >= 42. *)
Theorem progA_all :
  tripleSP obsASP progA Over
    (fun _ => True)
    (fun r =>
      match r with
      | Some (_, s') => s' >= 42
      | None => False
      end).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r [sigma [_ Hrel]].
  destruct r as [[[] s'] |]; cbn in Hrel; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  tripleSP obsASP progA Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r ->. exists 0. split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  tripleSP obsASP progA Under
    (fun _ => True)
    (fun r => r = Some (tt, 43)).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r ->. exists 0. split; [exact I | unfold obsRel; cbn; sauto].
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
  tripleSP obsASP progB Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r ->. exists 0. split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** Failure ([None]) is NOT reachable: the divergent branch does not
    contribute an exception, and divergence is the absence of reaching
    any final state. *)
Theorem progB_not_None :
  tripleSP obsASP progB Over
    (fun _ => True)
    (fun r => r <> None).
Proof.
  unfold tripleSP, obsASP, asp.
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

(** Backward (WP) triple, defined as an *exegesis* in the sense of
    Verscht & Kaminski: apply the WP observation to the postcondition
    [post] and compare it (by inclusion) with the precondition [pre].

    - [Under] reads  [pre ⊆ wp⟦m⟧(post)]  (e.g. [b ⊆ dwlp(c)]), partial
      correctness (the precondition under-approximates [wp(post)]).
    - [Over]  reads  [wp⟦m⟧(post) ⊆ pre]  (e.g. [awp(c) ⊆ b], the
      "necessary precondition" reading of partial incorrectness).

    This replaces the earlier [pp2wp]/[ordProgWP] encoding (spec-as-WP-
    element + refinement over *all* predicates).  That encoding agrees
    with this one on [Under] but degenerates on [Over]; the direct
    form is what makes the Galois connections of Fig. 5 provable (see
    [dwlp_asp] and [awp_dslp]). *)
Definition tripleWP {S A}
  (obs : nditprog S A -> ProgWP S A)
  (prog : nditprog S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
    match kind with
    | Under =>
        forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | Over =>
        forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.

(* ================================================================= *)
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  tripleWP obsDWP progA Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 : 
  not (
    tripleWP obsDWP progA Under
      (fun _ => True)
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 42
        | None => False
        end)).
Proof.
  intro contra.
  unfold tripleWP in contra. specialize (contra 0 I). cbn in contra.
  specialize (contra (Some (Some (tt, 43)))). sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  tripleWP obsAWP progA Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

Theorem progA_AWP_43 :
  tripleWP obsAWP progA Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 43
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 43)). split; sauto.
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
    tripleWP obsDWP progB Under
      (fun _ => True)
      (fun r : option (unit * nat) =>
          match r with
          | Some (_, s) => s = 42
          | None => False
          end)).
Proof.
  intro contra.
  unfold tripleWP in contra. specialize (contra 0 I). cbn in contra.
  specialize (contra None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored. *)
Theorem progB_DWLP_42 :
  tripleWP obsDWLP progB Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

Theorem progB_ASP_42 :
  tripleSP obsASP progB Over
    (fun _ => True)
    (fun r : option (unit * nat) =>
       match r with
       | Some (_, s) => s = 42
       | None => False
       end).
Proof.
  unfold tripleSP, obsASP.
  unfold asp, obsRel.
  intros r [sigma [_ Hrel]].
  destruct r as [[[] s']|]; cbn in Hrel; sauto.
Qed.
  
(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  tripleWP obsAWP progB Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

(** "There are divergent branches": divergence (the outermost [None]
    outcome) is *not* a result, so it is invisible to the SP observations
    ([obsRel] only sees the terminating [Some r] slice — cf.
    [progB_not_None]).  It is carried only by the *liberal* WP
    observations: [obsAWLP m s post = (exists terminating r, post r) \/
    (divergence reachable)].  Taking [post := fun _ => False] empties the
    terminating disjunct, so the triple says exactly "from every state,
    SOME branch diverges" (angelic), witnessed here by the [spinP] branch.

    This is the same shape as the (false) [progloom_correct] attempt —
    [progloom] never diverges, [progB] does.  Using [obsDWLP] instead
    would read "ALL branches diverge", which is false for [progB] (the
    [put s] branch converges). *)
Theorem progB_has_divergent_branch :
  tripleWP obsAWLP progB Under (fun _ => True) (fun _ => False).
Proof.
  intros s _. cbn.
  right.
  exists (Some (Some (tt, 42))). split; [reflexivity|].
  cbn. exists (Some (Some (42, 42))). split; [reflexivity|].
  cbn. right. reflexivity.
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
      tripleWP obsDWP m Under pre post ->
      tripleWP obsDWLP m Under pre post.
  Proof.
    intros A m pre post H s Hpre.
    apply obsDWP_incl_obsDWLP. exact (H s Hpre).
  Qed.

  Theorem cc_dwp_implies_awp :
    forall A (m: nditprog S A) pre post,
      (forall s0, pre s0 -> exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsDWP m Under pre post ->
      tripleWP obsAWP m Under pre post.
  Proof.
    intros A m pre post Hne H s Hpre.
    apply obsDWP_incl_obsAWP.
    - exact (Hne s Hpre).
    - exact (H s Hpre).
  Qed.

  Theorem cc_awp_implies_awlp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m Under pre post ->
      tripleWP obsAWLP m Under pre post.
  Proof.
    intros A m pre post H s Hpre.
    apply obsAWP_incl_obsAWLP. exact (H s Hpre).
  Qed.

  Theorem cc_dwlp_implies_awlp :
    forall A (m: nditprog S A) pre post,
      (forall s0, pre s0 -> exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsDWLP m Under pre post ->
      tripleWP obsAWLP m Under pre post.
  Proof.
    intros A m pre post Hne H s Hpre.
    apply obsDWLP_incl_obsAWLP.
    - exact (Hne s Hpre).
    - exact (H s Hpre).
  Qed.

  Theorem ii_awlp_implies_dwlp :
    forall A (m: nditprog S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsAWLP m Over pre post ->
      tripleWP obsDWLP m Over pre post.
  Proof.
    intros A m pre post Hne H s Hdwlp.
    apply H. apply obsDWLP_incl_obsAWLP.
    - exact (Hne s).
    - exact Hdwlp.
  Qed.

  Theorem ii_dwlp_implies_dwp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m Over pre post ->
      tripleWP obsDWP m Over pre post.
  Proof.
    intros A m pre post H s Hdwp.
    apply H. apply obsDWP_incl_obsDWLP. exact Hdwp.
  Qed.

  Theorem ii_awlp_implies_awp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWLP m Over pre post ->
      tripleWP obsAWP m Over pre post.
  Proof.
    intros A m pre post H s Hawp.
    apply H. apply obsAWP_incl_obsAWLP. exact Hawp.
  Qed.

  Theorem ii_awp_implies_dwp :
    forall A (m: nditprog S A) pre post,
      (forall s0, exists oa, unOptionT (unOptionT (runStateT m s0)) oa) ->
      tripleWP obsAWP m Over pre post ->
      tripleWP obsDWP m Over pre post.
  Proof.
    intros A m pre post Hne H s Hdwp.
    apply H. apply obsDWP_incl_obsAWP.
    - exact (Hne s).
    - exact Hdwp.
  Qed.

  Theorem ci_awp_dwlp_contrapositive :
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsAWP m Under pre post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply (proj2 (obsAWP_contrapositive_obsDWLP _ _ m s post)).
    intro Hdwlp. exact (Hii s Hdwlp Hpre).
  Qed.

  Theorem ci_awp_dwlp_contrapositive' :
    forall A (m : nditprog S A) pre post,
      tripleWP obsAWP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsDWLP m Over pre post.
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
      tripleWP obsAWLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsDWP m Under pre post.
  Proof.
    intros A m pre post Hii s Hpre.
    apply (proj2 (obsDWP_contrapositive_obsAWLP _ _ m s post)).
    intro Hawlp. exact (Hii s Hawlp Hpre).
  Qed.

  Theorem ci_dwp_awlp_contrapositive' :
    forall A (m : nditprog S A) pre post,
      tripleWP obsDWP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsAWLP m Over pre post.
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
      tripleWP obsDWP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsAWLP m Under pre post.
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
      tripleWP obsAWLP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsDWP m Over pre post.
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
      tripleWP obsAWP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsDWLP m Under pre post.
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
      tripleWP obsDWLP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleWP obsAWP m Over pre post.
  Proof.
    intros A m pre post Hii s Hawp. apply NNPP. intro Hnpre.
    specialize (Hii s Hnpre).
    unfold obsDWLP, obsAWP in *. cbn in Hii, Hawp.
    destruct (runStateT m s) as [[outcomes]]. cbn in Hii, Hawp.
    destruct Hawp as [r [Hr Hpost]].
    exact (Hii (Some r) Hr Hpost).
  Qed.
End TaxonomyWPTransformers.

Section TaxonomySPTransformers.
  Variable S : Type.

  (** ASLP-Correct implies ASP-Correct: the ASP observation is the
      left disjunct of ASLP, so any postcondition entailed by the
      whole disjunction is entailed by ASP alone. *)
  Theorem cc_aslp_implies_asp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsASLP m Over pre post ->
      tripleSP obsASP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. left. exact Hasp.
  Qed.

  Theorem cc_aslp_implies_dslp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsASLP m Over pre post ->
      tripleSP obsDSLP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. apply obsDSLP_sub_obsASLP.
    exact Hasp.
  Qed.

  Theorem cc_dslp_implies_dsp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsDSLP m Over pre post ->
      tripleSP obsDSP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. apply obsDSP_sub_obsDSLP.
    exact Hasp.
  Qed.

  Theorem cc_asp_implies_dsp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsASP m Over pre post ->
      tripleSP obsDSP m Over pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. apply obsDSP_sub_obsASP.
    exact Hasp.
  Qed.

  Theorem ii_dsp_implies_dslp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsDSP m Under pre post ->
      tripleSP obsDSLP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. exact Hasp.
  Qed.

  Theorem ii_dslp_implies_aslp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsDSLP m Under pre post ->
      tripleSP obsASLP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply obsDSLP_sub_obsASLP. apply H.
    exact Hasp.
  Qed.

  Theorem ii_asp_implies_aslp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsASP m Under pre post ->
      tripleSP obsASLP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply obsASP_sub_obsASLP. apply H.
    exact Hasp.
  Qed.

  Theorem ii_dsp_implies_asp :
    forall A (m: nditprog S A) pre post,
      tripleSP obsDSP m Under pre post ->
      tripleSP obsASP m Under pre post.
  Proof.
    intros A m pre post H r Hasp.
    apply H. exact Hasp.
  Qed.

  Theorem ci_aslp_dsp_contrapositive :
    forall A (m : nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
    forall A (m : nditprog S A) pre post,
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
     forall A (m : nditprog S A) pre post,
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
  Lemma obsRel_outcomes {A} (m : nditprog S A) s r :
    obsRel m s r = unOptionT (unOptionT (runStateT m s)) (Some r).
  Proof. unfold obsRel. destruct r as [[a s']|]; reflexivity. Qed.

  (** Galois connection (correctness side): the demonic-liberal WP
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m Under pre post <->
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

  (** Galois connection (incorrectness side) — the Zhang–Kaminski
      connection [awp⟦m⟧(c) ⊆ b  iff  c ⊆ dslp⟦m⟧(b)] of Verscht &
      Kaminski's Fig. 5.

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
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m Over pre post <->
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m Over pre post ->
        tripleSP obsDSLP m Under pre post.
  Proof. intros A m pre post; apply awp_dslp. Qed.

End TaxonomyGaloisConnections.

(* ================================================================= *)
(** ** Taxonomy of transformers (connecting the halves of Figure 5)                        *)
(* ================================================================= *)
(** REMOVED: [ii_dwlp_implies_dsp], [ii_dwp_implies_dsp] and
    [dwlp_inc_pre_universal].

    These were artefacts of the previous [pp2wp]/[ordProgWP] encoding.
    Under that encoding [tripleWP obsDWLP _ Over] forced [pre] to be
    *universally true* (instantiating the quantified-over predicate at
    [fun _ => True]), which is what made "DWLP/DWP-Incorrect implies
    DSP-Incorrect" go through.  With the corrected exegesis-style triple
    [tripleWP obsDWLP _ Over] reads [dwlp(post) ⊆ pre] and imposes
    no such universality, so these implications no longer hold (and the
    [pre]-universality lemma is simply false).  The genuine WP/SP
    incorrectness connection is [awp_dslp] above (Fig. 5's [awp ⊣ dslp]). *)

(* ================================================================= *)
(** ** Example: WP-Inc and SP-Inc agree under the corrected triple     *)
(* ================================================================= *)

(** A pure return in state [nat] with a pre-/post-condition pinning the
    state to [0].  Under the corrected exegesis-style triple,
    [tripleWP obsDWP _ Over] reads [dwp(post) ⊆ pre]: for the
    deterministic [progRet] the only [post]-forcing state is [0] itself,
    so the WP-Incorrect triples now hold, agreeing with the SP-Incorrect
    one.  (Under the old [pp2wp] encoding these WP triples were instead
    refuted — they degenerated into "[pre] holds at every converging
    state".) *)

Example progRet : nditprog nat unit := ret tt.

Definition preEq0 : nat -> Prop := fun s => s = 0.
Definition postEq0 : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, 0).

(** The SP-Inc triple holds: state [0] reaches the only post-result. *)
Theorem progRet_asp_inc :
  tripleSP obsASP progRet Under preEq0 postEq0.
Proof.
  unfold tripleSP, obsASP, preEq0, postEq0.
  unfold asp, obsRel.
  intros r ->. exists 0. split; [reflexivity | cbn; reflexivity].
Qed.

(** The stronger DSP-Inc triple also holds: the unique reacher of
    [Some (tt, 0)] is the state [0] itself, which satisfies [preEq0]. *)
Theorem progRet_dsp_inc :
  tripleSP obsDSP progRet Under preEq0 postEq0.
Proof.
  unfold tripleSP, preEq0, postEq0.
  intros r ->. apply obsDSP_char. split.
  - exists 0. cbn. reflexivity.
  - intros s Hrel. cbn in Hrel. inversion Hrel. reflexivity.
Qed.

(** The DWP-Inc triple now holds: [dwp(postEq0)(s)] forces [s = 0]. *)
Theorem progRet_dwp_inc :
  tripleWP obsDWP progRet Over preEq0 postEq0.
Proof.
  intros s Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(** Likewise DWLP-Inc holds (the divergence branch is vacuous, since
    [progRet] never diverges). *)
Theorem progRet_dwlp_inc :
  tripleWP obsDWLP progRet Over preEq0 postEq0.
Proof.
  intros s Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

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

Definition P0 : nat -> Prop := fun s => s = 0.

(** -- Class 1: exclusively reachable from P — all four include it -- *)

#[program] Theorem progEx_asp_1 :
  (obsASP progEx) P0 (Some (tt, 1)).
Proof.
  unfold obsASP, P0. unfold asp.
  exists 0. split; [reflexivity|].
  unfold obsRel. cbn.
  sauto.
Qed.

#[program] Theorem progEx_dslp_1 :
  (obsDSLP progEx) P0 (Some (tt, 1)).
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intros s Hrel. unfold obsRel in Hrel. cbn in Hrel.
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
  (obsASP progEx) P0 (Some (tt, 42)).
Proof.
  unfold obsASP, P0. unfold asp.
  exists 0. split; [reflexivity|].
  unfold obsRel. cbn. sauto.
Qed.

#[program] Theorem progEx_dslp_not_42 :
  ~ (obsDSLP progEx) P0 (Some (tt, 42)).
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intro H. specialize (H 1).
  assert (Hreach : obsRel progEx 1 (Some (tt, 42))).
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
  ~ (obsASP progEx) P0 None.
Proof.
  unfold obsASP, P0. unfold asp.
  intros [s [HP Hrel]].
  unfold obsRel in Hrel. cbn in Hrel. sauto.
Qed.

#[program] Theorem progEx_dslp_None :
  (obsDSLP progEx) P0 None.
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intros s Hrel.
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
  ~ (obsASP progEx) P0 (Some (tt, 99)).
Proof.
  unfold obsASP, P0. unfold asp.
  intros [s [HP Hrel]]. subst.
  unfold obsRel in Hrel. cbn in Hrel. sauto lq: on.
Qed.

#[program] Theorem progEx_dslp_not_99 :
  ~ (obsDSLP progEx) P0 (Some (tt, 99)).
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intro H. specialize (H 98).
  assert (Hreach : obsRel progEx 98 (Some (tt, 99))).
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

(* ================================================================= *)
(** ** O'Hearn's Example 3.1, ported to [nditprog] / [tripleSP obsASP] *)
(* ================================================================= *)

(** A port of [ST/Pred.v]'s [OHearnExample] module.  The original
    operates on the pure state monad [state S A := S -> A * S] with a
    bespoke [Incorrect] predicate (reachability of a final state from
    some initial state).  Here we use [nditprog S A] (deterministic in
    this example) and [tripleSP obsASP _ Under].

    Program (O'Hearn, "Incorrectness Logic", Example 3.1): swap [z]
    with [42] when [x] is even and [y] is odd; otherwise leave the
    state alone. *)

Module OHearnExample.

  Definition example_state : nditprog (nat * nat * nat) unit :=
    s <- get ;;
    let '(x, y, _) := s in
    if Nat.even x then
      if negb (Nat.even y) then put (x, y, 42) else ret tt
    else ret tt.

  (** First incorrectness triple (paper-style): from any state whose
      [z] component is [11], there is a final state in which [z = 42],
      [x] is even, and [y] is odd.  Note the SP-Incorrect reading: the
      triple asserts only that *some* such reachable result exists,
      not that every initial state reaches one. *)
  Theorem example_incorrect_1 :
    tripleSP obsASP example_state Under
      (fun '(x, _, z) => z = 11)
      (fun r =>
         match r with
         | Some (tt, (x, y, z)) =>
             z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
         | _ => False
         end).
  Proof.
    unfold tripleSP, obsASP.
    unfold asp, obsRel.
    intros [[[] [[x y] z]]|] H; [|contradiction].
    destruct H as [-> [Hx Hy]].
    exists (x, y, 11). split; [reflexivity|].
    cbn. eexists. split; [reflexivity|].
    cbn. rewrite Hx, Hy. reflexivity.
  Qed.

  (** Weaker incorrectness triple (vacuous precondition): from *some*
      initial state, the program reaches a final state with [z = 42].
      The original proof in [ST/Pred.v] also leaves [x], [y], [z]
      unconstrained and exhibits any state with [x] even and [y]
      odd as the witness. *)
  Theorem example_incorrect_2 :
    tripleSP obsASP example_state Under
      (fun _ => True)
      (fun r =>
         match r with
         | Some (tt, (_, _, z)) => z = 42
         | _ => False
         end).
  Proof.
    unfold tripleSP, obsASP.
    unfold asp, obsRel.
    intros [[[] [[x y] z]]|] H; [|contradiction].
    cbn in H. subst z.
    (* Use the final state itself, [(x, y, 42)], as the initial witness:
       both branches preserve [x, y] and either keep [z = 42] (identity)
       or set it to [42] (put). *)
    exists (x, y, 42). split; [exact I|].
    cbn. eexists. split; [reflexivity|].
    cbn. destruct (Nat.even x); destruct (negb (Nat.even y)); reflexivity.
  Qed.

  (** Unprovable triple (paper-noted): from any state with [z = 11],
      the program reaches a final state with [z = 42].  This is
      [example_3_1_incorrect_unprovable] in [ST/Pred.v]; we mirror
      its failure here.

      Refutation: pick [r = Some (tt, (1, 0, 42))] — it satisfies the
      postcondition (because the post only mentions [z = 42]), but no
      initial state with [z = 11] reaches it.  Indeed the program only
      modifies the state when [x] is even and [y] is odd, and even
      then it preserves the first two components; so reaching
      [(1, 0, 42)] would require starting from [(1, 0, 42)], whose
      [z]-component is [42], not [11]. *)
  Theorem example_incorrect_unprovable :
    ~ tripleSP obsASP example_state Under
        (fun '(_, _, z) => z = 11)
        (fun r =>
           match r with
           | Some (tt, (_, _, z)) => z = 42
           | _ => False
           end).
  Proof.
    intro H.
    specialize (H (Some (tt, (1, 0, 42))) eq_refl).
    destruct H as [[[x y] z] [Hpre Hrel]].
    cbn in Hpre. subst z.
    cbn in Hrel.
    destruct Hrel as [a [Ha Hrel]].
    subst a. cbn in Hrel.
    destruct (Nat.even x) eqn:Hx; destruct (negb (Nat.even y)) eqn:Hy;
      cbn in Hrel; inversion Hrel; subst; try discriminate Hx.
  Qed.


  (* ----------------------------------------------------------------- *)
  (** ** Note on the [obsDWP] (Incorrect) view                          *)
  (* ----------------------------------------------------------------- *)

  (** The previous version refuted three [tripleWP obsDWP _ Over]
      triples for [example_state].  Those refutations relied on the old
      [pp2wp] encoding, under which DWP-Incorrect degenerated into
      "[pre] holds at every (terminating) initial state".  With the
      corrected exegesis-style triple [tripleWP obsDWP _ Over] reads
      [dwp(post) ⊆ pre], a genuine (demonic-total) necessary-precondition
      statement; the earlier counterexamples no longer apply (e.g. the
      [pre := fun _ => True] one becomes trivially valid).  The clean
      WP/SP incorrectness correspondence is [awp_dslp] ([awp ⊣ dslp]). *)

End OHearnExample.

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
    Nat] is the unbounded-choice combinator [pickP] from [NonDetItProg.v].

    "Angelic, [ensures False]": from any positive balance *some* execution
    reaches an acceptable outcome.  A normal return is forbidden
    ([ensures False]); the only acceptable outcome is the exceptional one
    ([None]), so the triple states that the angelic scheduler can always
    drive the session to the [throw].  This is [tripleWP obsAWP _ Under]
    with a postcondition that is [True] on the exception and [False] on
    every normal return.  The [obsDWP] (demonic) reading of the same spec
    is invalid: the demon may pick a small amount and return normally. *)

Module WithdrawExample.

  Definition progloom : nditprog nat unit :=
    amount  <- pickP ;;
    balance <- get ;;
    if Nat.ltb balance amount then raise tt else put (balance - amount).

  (** Angelic spec: pick [amount = S balance > balance] to force the
      [raise], so the exceptional outcome [Some None] is reachable. *)
  Theorem progloom_triple :
    tripleWP obsAWP progloom Under
      (fun balance => balance > 0)
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

      [tripleSP obsASP _ Under] is [post ⊆ asp(pre)] (∀ asserted output,
      ∃ input): "the throw is reachable from *some* [balance > 0]" —
      O'Hearn-style bug *presence*.  [progloom_triple] is the angelic-total
      WP reading [pre ⊆ awp(post)] (∀ input, ∃ output): "the throw is
      reachable from *every* [balance > 0]" — angelic *coverage*.  Same
      program, same postcondition; only the triple and the quantifier
      order over inputs/outputs differ. *)
  Theorem progloom_triple_asp :
    tripleSP obsASP progloom Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
  Proof.
    intros r Hr. destruct r as [[[] n]|]; [ exfalso; exact Hr | ].
    unfold obsASP, asp.
    exists 1. split.
    - exact (ltac:(lia) : 1 > 0).
    - unfold obsRel. cbn.
      exists (Some (Some (2, 1))). split.
      + exists 2. reflexivity.
      + cbn. exists (Some (Some (1, 1))). split.
        * reflexivity.
        * cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
  Qed.

  Definition progloom_harder : nditprog nat unit :=
    amount  <- pickP ;;
    balance <- get ;;
    if Nat.even balance then raise tt else put (balance - amount).

  (** WP coverage FAILS: the throw is reached iff [balance] is even (the
      picked [amount] is irrelevant), so from an odd [balance] (e.g. [1])
      every branch returns normally and the exception is unreachable —
      [awp(post)] is empty there, breaking [pre ⊆ awp(post)]. *)
  Theorem progloom_triple_harder :
    ~ (tripleWP obsAWP progloom_harder Under
      (fun balance => balance > 0)
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
    tripleSP obsASP progloom_harder Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
  Proof.
    intros r Hr. destruct r as [[[] n]|]; [ exfalso; exact Hr | ].
    unfold obsASP, asp.
    exists 2. split.
    - exact (ltac:(lia) : 2 > 0).
    - unfold obsRel. cbn.
      exists (Some (Some (0, 2))). split.
      + exists 0. reflexivity.
      + cbn. exists (Some (Some (2, 2))). split.
        * reflexivity.
        * cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
  Qed.
End WithdrawExample.

Section OHearnRewritingRules.

  Variable S : Type.

  Theorem first_symmetry_rule_1_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Under pre post1 /\
       tripleSP obsASP m Under pre post2) ->
        tripleSP obsASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2.
    unfold tripleSP, obsASP, asp.
    intro H. inversion H as [H1 H2].
    intros r Hr. inversion Hr as [Hr1 | Hr2].
    - apply H1. exact Hr1.
    - apply H2. exact Hr2.
  Qed.

  Theorem first_symmetry_rule_2_asp :
    forall A (m : nditprog S A) pre post1 post2,
      tripleSP obsASP m Under pre (fun r => post1 r \/ post2 r) ->
      (tripleSP obsASP m Under pre post1 /\
       tripleSP obsASP m Under pre post2).
  Proof.
    intros A m pre post1 post2.
    unfold tripleSP, obsASP, asp.
    intro H. split.
    - intros r Hr. apply H. left. exact Hr.
    - intros r Hr. apply H. right. exact Hr.
  Qed.

  Theorem first_symmetry_rule_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Under pre post1 /\
       tripleSP obsASP m Under pre post2) <->
        tripleSP obsASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros. split.
    - apply first_symmetry_rule_1_asp.
    - apply first_symmetry_rule_2_asp.
  Qed.

  Theorem second_symmetry_rule_asp_1 :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Over pre post1 /\
         tripleSP obsASP m Over pre post2) ->
      tripleSP obsASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2.
    intro H. inversion H as [H1 H2].
    intros r Hr. split.
    - apply H1. exact Hr.
    - apply H2. exact Hr.
  Qed.

  Theorem second_symmetry_rule_asp_2 :
    forall A (m : nditprog S A) pre post1 post2,
      tripleSP obsASP m Over pre (fun r => post1 r /\ post2 r) ->
      (tripleSP obsASP m Over pre post1 /\
         tripleSP obsASP m Over pre post2).
  Proof.
    intros A m pre post1 post2.
    unfold tripleSP, obsASP, asp.
    intro H. split.
    - intros r Hr. apply H. exact Hr.
    - intros r Hr. apply H. exact Hr.
  Qed.

  Theorem second_symmetry_rule_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleSP obsASP m Over pre post1 /\
         tripleSP obsASP m Over pre post2) <->
        tripleSP obsASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros. split.
    - apply second_symmetry_rule_asp_1.
    - apply second_symmetry_rule_asp_2.
  Qed.

  Theorem second_symmetry_rule_dwp_1 :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleWP obsDWLP m Under pre post1 /\
         tripleWP obsDWLP m Under pre post2) ->
      tripleWP obsDWLP m Under pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] s Hpre.
    specialize (H1 s Hpre). specialize (H2 s Hpre).
    cbn in H1, H2 |- *.
    destruct (runStateT m s) as [[outcomes]].
    intros oa Hoa.
    specialize (H1 oa Hoa). specialize (H2 oa Hoa).
    destruct oa as [r|]; [|exact I].
    split; assumption.
  Qed.

  Theorem second_symmetry_rule_dwp_2 :
    forall A (m : nditprog S A) pre post1 post2,
      tripleWP obsDWLP m Under pre (fun r => post1 r /\ post2 r) ->
       (tripleWP obsDWLP m Under pre post1 /\
         tripleWP obsDWLP m Under pre post2).
  Proof.
    intros A m pre post1 post2 H.
    split.
    - intros s Hpre. specialize (H s Hpre). cbn in H |- *.
      destruct (runStateT m s) as [[outcomes]].
      intros oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [|exact I]. exact (proj1 H).
    - intros s Hpre. specialize (H s Hpre). cbn in H |- *.
      destruct (runStateT m s) as [[outcomes]].
      intros oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [|exact I]. exact (proj2 H).
  Qed.

  Theorem second_symmetry_rule_dwp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleWP obsDWLP m Under pre post1 /\
         tripleWP obsDWLP m Under pre post2) <->
        tripleWP obsDWLP m Under pre (fun r => post1 r /\ post2 r).
    Proof.
      intros. split.
      - apply second_symmetry_rule_dwp_1.
      - apply second_symmetry_rule_dwp_2.
    Qed.

    (** Rule of consequence for SP-Incorrect: weaken the precondition
        and shrink the postcondition. *)
    Theorem first_imp_symmetry_rule_asp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleSP obsASP m Under pre post /\
           (forall r, pre r -> pre' r) /\ (forall r, post' r -> post r)) -> tripleSP obsASP m Under pre' post'.
    Proof.
      intros A m pre pre' post post' [Htriple [Hpre Hpost]].
      unfold tripleSP, obsASP in *.
      unfold asp in *.
      intros r Hpost'.
      destruct (Htriple r (Hpost r Hpost')) as [s [Hp Hrel]].
      exists s. split; [apply Hpre; exact Hp | exact Hrel].
    Qed.

    (** Rule of consequence for SP-Correct: strengthen the precondition
        and weaken the postcondition. *)
    Theorem second_imp_symmetry_rule_asp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleSP obsASP m Over pre post /\
           (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) -> tripleSP obsASP m Over pre' post'.
    Proof.
      intros A m pre pre' post post' [Htriple [Hpre Hpost]].
      unfold tripleSP, obsASP in *.
      unfold asp in *.
      intros r [s [Hpre' Hrel]].
      apply Hpost. apply Htriple.
      exists s. split; [apply Hpre; exact Hpre' | exact Hrel].
    Qed.

    (** DWLP-Correct implies ASP-Correct (with consequence): a result
        reachable from a [pre']-state is a terminating outcome there, so
        the demonic partial transformer forces the postcondition. *)
    Theorem second_imp_symmetry_rule_dwp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleWP obsDWLP m Under pre post /\
           (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) -> tripleSP obsASP m Over pre' post'.
    Proof.
      intros A m pre pre' post post' [Hwp [Hpre Hpost]].
      unfold tripleWP, obsDWLP in Hwp.
      unfold tripleSP, obsASP.
      unfold asp, obsRel.
      intros r [s0 [Hpre' Hrel]].
      apply Hpost.
      specialize (Hwp s0 (Hpre s0 Hpre')). cbn in Hwp.
      destruct (runStateT m s0) as [[outcomes]] eqn:Hm. cbn in Hwp, Hrel.
      refine (Hwp (Some r) _).
      destruct r as [[a s']|]; exact Hrel.
    Qed.

    (** Principle of agreement (SP): if [u]-reachability witnesses the
        under-approximation [u'] and [u] entails the over-approximation
        precondition [o], then the over-approximation postcondition [o']
        holds of every [u']-result. *)
    Theorem principle_of_agreement_asp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ tripleSP obsASP m Over o o' /\
           (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
    Proof.
      intros A m u u' o o' [Hinc [Hcor Himp]].
      unfold tripleSP, obsASP in *.
      unfold asp in *.
      intros r Hu'.
      destruct (Hinc r Hu') as [s [Hu Hrel]].
      apply Hcor. exists s. split; [apply Himp; exact Hu | exact Hrel].
    Qed.

    (** Principle of agreement, demonic-partial-WP variant. *)
    Theorem principle_of_agreement_dwp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ tripleWP obsDWLP m Under o o' /\
           (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
    Proof.
      intros A m u u' o o' [Hinc [Hwp Himp]].
      unfold tripleSP, obsASP in Hinc.
      unfold asp, obsRel in Hinc.
      unfold tripleWP, obsDWLP in Hwp.
      intros r Hu'.
      destruct (Hinc r Hu') as [s [Hu Hrel]].
      specialize (Hwp s (Himp s Hu)). cbn in Hwp.
      destruct (runStateT m s) as [[outcomes]] eqn:Hm. cbn in Hwp, Hrel.
      refine (Hwp (Some r) _).
      destruct r as [[a s']|]; exact Hrel.
    Qed.

    (** Principle of denial (SP): contrapositive of agreement. *)
    Theorem principle_of_denial_asp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleSP obsASP m Over o o').
    Proof.
      intros A m u u' o o' [Hinc [Himp Hnot]] Hcor.
      apply Hnot.
      apply (principle_of_agreement_asp A m u u' o o').
      exact (conj Hinc (conj Hcor Himp)).
    Qed.

    (** Principle of denial, demonic-partial-WP variant. *)
    Theorem principle_of_denial_dwp :
      forall A (m : nditprog S A) u u' o o',
        (tripleSP obsASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleWP obsDWLP m Under o o').
    Proof.
      intros A m u u' o o' [Hinc [Himp Hnot]] Hwp.
      apply Hnot.
      apply (principle_of_agreement_dwp A m u u' o o').
      exact (conj Hinc (conj Hwp Himp)).
    Qed.

End OHearnRewritingRules.

Section TripleDefinitions.
  Variable S : Type.
  
  (* UNDER *)
  
  Theorem dwlp {A} :
    forall (m : nditprog S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsDWLP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsDWLP m) s) p).
  Proof.
    intros m pre post. split.
    - intros H s p [Hpre Hsub]. specialize (H s Hpre).
      unfold obsDWLP in *. cbn [runStateT unOptionT] in *.
      destruct (runStateT m s) as [[outcomes]].
      intros oa Hoa. specialize (H oa Hoa). destruct oa as [r|]; [|exact I].
      exact (Hsub r H).
    - intros H s Hpre.
      apply (H s post). split; [exact Hpre | intros r hr; exact hr].
  Qed.

    Theorem awlp {A} :
    forall (m : nditprog S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsAWLP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsAWLP m) s) p).
    Proof.
      intros m pre post. split.
      - intros H s p [Hpre Hsub]. specialize (H s Hpre).
        unfold obsAWLP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        destruct H as [[r [Hr Hpost]] | Hdiv].
        + left. exists r. split; [exact Hr | exact (Hsub r Hpost)].
        + right. exact Hdiv.
      - intros H s Hpre.
        apply (H s post). split; [exact Hpre | intros r hr; exact hr].
    Qed.

    Theorem dwp {A} :
    forall (m : nditprog S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsDWP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsDWP m) s) p).
    Proof.
      intros m pre post. split.
      - intros H s p [Hpre Hsub]. specialize (H s Hpre).
        unfold obsDWP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        intros oa Hoa. specialize (H oa Hoa).
        destruct oa as [r|]; [exact (Hsub r H) | exact H].
      - intros H s Hpre.
        apply (H s post). split; [exact Hpre | intros r hr; exact hr].
    Qed.

    Theorem awp {A} :
    forall (m : nditprog S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsAWP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsAWP m) s) p).
    Proof.
      intros m pre post. split.
      - intros H s p [Hpre Hsub]. specialize (H s Hpre).
        unfold obsAWP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        destruct H as [r [Hr Hpost]]. exists r. split; [exact Hr | exact (Hsub r Hpost)].
      - intros H s Hpre.
        apply (H s post). split; [exact Hpre | intros r hr; exact hr].
    Qed.

    (* OVER *)
    Theorem awp_works {A} :
    forall (m : nditprog S A) pre post,
      (forall s p, unOptionT (runStateT (obsAWP m) s) p -> (pre s /\ (forall r, post r -> p r))) ->
      (forall s, unOptionT (runStateT (obsAWP m) s) post -> pre s).
    Proof.
      intros m pre post H s Hs.
      exact (proj1 (H s post Hs)).
    Qed.

    (* ...but the converse [direct -> refinement] is NOT valid in general:
       the direct form [awp(post) ⊆ pre] does not recover the refinement
       form [obsAWP ⊑ pp2wp pre post] (the latter quantifies over *all*
       predicates [p], which the former cannot constrain). The
       [direct -> refinement] is not valid for *all* [m,pre,post],
       witnessed by [m := ret tt], [pre := True], [post := {Some (tt,1)}]:
       direct holds (its conclusion [pre] is [True]), but refinement fails
       at [p := {Some (tt,0)}] (reachable, yet [post ⊄ p]). *)
    Theorem awp_breaks :
      ~ (forall (m : nditprog nat unit) (pre : nat -> Prop)
                (post : option (unit * nat) -> Prop),
           (forall s, unOptionT (runStateT (obsAWP m) s) post -> pre s) ->
           (forall s p, unOptionT (runStateT (obsAWP m) s) p ->
                        (pre s /\ (forall r, post r -> p r)))).
    Proof.
      intro H.
      assert (Hrun : unOptionT (runStateT (obsAWP (ret tt : nditprog nat unit)) 0)
                       (fun r => r = Some (tt, 0))).
      { cbn. exists (Some (tt, 0)). split; sauto. }
      specialize (H (ret tt) (fun _ => True) (fun r => r = Some (tt, 1))
                    (fun _ _ => I) 0 (fun r => r = Some (tt, 0)) Hrun).
      destruct H as [_ Hsub].
      specialize (Hsub (Some (tt, 1)) eq_refl). discriminate.
    Qed.

    (* The same [works]/[breaks] pattern for the other three observations.
       In each case [refinement -> direct] holds (instantiate [p := post]),
       but [direct -> refinement] is not valid in general — same
       counterexample [ret tt], [pre := True], [post := {Some (tt,1)}],
       witnessed at [p := {Some (tt,0)}]. *)

    Theorem dwlp_works {A} :
    forall (m : nditprog S A) pre post,
      (forall s p, unOptionT (runStateT (obsDWLP m) s) p -> (pre s /\ (forall r, post r -> p r))) ->
      (forall s, unOptionT (runStateT (obsDWLP m) s) post -> pre s).
    Proof.
      intros m pre post H s Hs.
      exact (proj1 (H s post Hs)).
    Qed.

    Theorem dwlp_breaks :
      ~ (forall (m : nditprog nat unit) (pre : nat -> Prop)
                (post : option (unit * nat) -> Prop),
           (forall s, unOptionT (runStateT (obsDWLP m) s) post -> pre s) ->
           (forall s p, unOptionT (runStateT (obsDWLP m) s) p ->
                        (pre s /\ (forall r, post r -> p r)))).
    Proof.
      intro H.
      assert (Hrun : unOptionT (runStateT (obsDWLP (ret tt : nditprog nat unit)) 0)
                       (fun r => r = Some (tt, 0))).
      { cbn. sauto. }
      specialize (H (ret tt) (fun _ => True) (fun r => r = Some (tt, 1))
                    (fun _ _ => I) 0 (fun r => r = Some (tt, 0)) Hrun).
      destruct H as [_ Hsub].
      specialize (Hsub (Some (tt, 1)) eq_refl). discriminate.
    Qed.

    Theorem awlp_works {A} :
    forall (m : nditprog S A) pre post,
      (forall s p, unOptionT (runStateT (obsAWLP m) s) p -> (pre s /\ (forall r, post r -> p r))) ->
      (forall s, unOptionT (runStateT (obsAWLP m) s) post -> pre s).
    Proof.
      intros m pre post H s Hs.
      exact (proj1 (H s post Hs)).
    Qed.

    Theorem awlp_breaks :
      ~ (forall (m : nditprog nat unit) (pre : nat -> Prop)
                (post : option (unit * nat) -> Prop),
           (forall s, unOptionT (runStateT (obsAWLP m) s) post -> pre s) ->
           (forall s p, unOptionT (runStateT (obsAWLP m) s) p ->
                        (pre s /\ (forall r, post r -> p r)))).
    Proof.
      intro H.
      assert (Hrun : unOptionT (runStateT (obsAWLP (ret tt : nditprog nat unit)) 0)
                       (fun r => r = Some (tt, 0))).
      { cbn. left. exists (Some (tt, 0)). split; sauto. }
      specialize (H (ret tt) (fun _ => True) (fun r => r = Some (tt, 1))
                    (fun _ _ => I) 0 (fun r => r = Some (tt, 0)) Hrun).
      destruct H as [_ Hsub].
      specialize (Hsub (Some (tt, 1)) eq_refl). discriminate.
    Qed.

    Theorem dwp_works {A} :
    forall (m : nditprog S A) pre post,
      (forall s p, unOptionT (runStateT (obsDWP m) s) p -> (pre s /\ (forall r, post r -> p r))) ->
      (forall s, unOptionT (runStateT (obsDWP m) s) post -> pre s).
    Proof.
      intros m pre post H s Hs.
      exact (proj1 (H s post Hs)).
    Qed.

    Theorem dwp_breaks :
      ~ (forall (m : nditprog nat unit) (pre : nat -> Prop)
                (post : option (unit * nat) -> Prop),
           (forall s, unOptionT (runStateT (obsDWP m) s) post -> pre s) ->
           (forall s p, unOptionT (runStateT (obsDWP m) s) p ->
                        (pre s /\ (forall r, post r -> p r)))).
    Proof.
      intro H.
      assert (Hrun : unOptionT (runStateT (obsDWP (ret tt : nditprog nat unit)) 0)
                       (fun r => r = Some (tt, 0))).
      { cbn. sauto. }
      specialize (H (ret tt) (fun _ => True) (fun r => r = Some (tt, 1))
                    (fun _ _ => I) 0 (fun r => r = Some (tt, 0)) Hrun).
      destruct H as [_ Hsub].
      specialize (Hsub (Some (tt, 1)) eq_refl). discriminate.
    Qed.

End TripleDefinitions.

Section MonadMorphismLaws.
  Variable S : Type.
  
  Lemma obsDWP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsDWP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsDWLP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsDWLP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsAWP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsAWP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.

  Lemma obsAWLP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsAWLP (ret a)) s0) post <->
    unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Proof.
    split; sauto.
  Qed.
End MonadMorphismLaws.
    
(* ================================================================= *)
(** ** Adequacy: the observations are monad morphisms                 *)
(* ================================================================= *)

(** [ret] and [>>=] adequacy.  Each observation preserves the monad
    structure, so the triples reduce on [ret a] (the skip/return rule)
    and decompose on [x >>= f] (the Hoare sequence rule).

    Return: from state [s], [ret a] has the single converging outcome
    [Some (a, s)], so every WP observation collapses to [post (Some (a,s))]
    and [obsRel (ret a) s r <-> r = Some (a, s)].

    Bind: [x >>= f]'s outcomes are obtained by running [f a] from [s']
    on each converging [Some (a, s')] of [x]; exceptions ([None]) and
    divergence propagate. *)

(* --- Return adequacy --- *)

Lemma tripleWP_ret_Under {S A} (a : A) (pre : S -> Prop) post :
  tripleWP obsDWP (ret a) Under pre post <-> (forall s, pre s -> post (Some (a, s))).
Proof.
  unfold tripleWP, obsDWP. cbn. split.
  - intros H s Hpre. exact (H s Hpre (Some (Some (a, s))) eq_refl).
  - intros H s Hpre oa Hoa. cbn in Hoa. subst oa. exact (H s Hpre).
Qed.

Lemma tripleWP_ret_Over {S A} (a : A) (pre : S -> Prop) post :
  tripleWP obsDWP (ret a) Over pre post <-> (forall s, post (Some (a, s)) -> pre s).
Proof.
  unfold tripleWP, obsDWP. cbn. split.
  - intros H s Hp. apply H. intros oa Hoa. cbn in Hoa. subst oa. exact Hp.
  - intros H s Hwp. apply H. exact (Hwp (Some (Some (a, s))) eq_refl).
Qed.

Lemma tripleSP_ret_Over {S A} (a : A) (pre : S -> Prop) post :
  tripleSP obsASP (ret a) Over pre post <-> (forall s, pre s -> post (Some (a, s))).
Proof.
  unfold tripleSP, obsASP, asp, obsRel. cbn. split.
  - intros H s Hpre. apply H. exists s. split; [exact Hpre | sauto].
  - intros H r [s [Hpre Hrel]]. cbn in Hrel. sauto.
Qed.

Lemma tripleSP_ret_Under {S A} (a : A) (pre : S -> Prop) post :
  tripleSP obsASP (ret a) Under pre post <->
  (forall r, post r -> exists s, pre s /\ r = Some (a, s)).
Proof.
  unfold tripleSP, obsASP, asp, obsRel. cbn. split.
  - intros H r Hpost. destruct (H r Hpost) as [s [Hpre Hrel]]. cbn in Hrel.
    exists s. split; [exact Hpre | sauto].
  - intros H r Hpost. destruct (H r Hpost) as [s [Hpre Heq]]. subst r.
    exists s. split; [exact Hpre | sauto].
Qed.

(* --- Bind adequacy --- *)

(** Operational decomposition of [x >>= f]'s outcome set. *)
Lemma outcomes_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) sigma ob :
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

(** SP bind adequacy: [obsRel] composes as a Kleisli arrow (state +
    exception). *)
Lemma obsRel_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) sigma r :
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

Lemma obsDWP_unfold {S A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsDWP m) s) post <->
  (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
              match oa with Some r => post r | None => False end).
Proof. unfold obsDWP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

(** WP bind adequacy: the Dijkstra [wp_bind] law (same shape for all four
    WP observations; shown for [obsDWP]).  The [None] branch threads [x]'s
    exception through to [post None]. *)
Lemma obsDWP_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
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

(** WP triple bind rule (both [Under] and [Over]). *)
Theorem tripleWP_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) kind pre post :
  tripleWP obsDWP (x >>= f) kind pre post <->
  tripleWP obsDWP x kind pre
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWP (f a)) s') post
               | None => post None
               end).
Proof.
  unfold tripleWP. destruct kind; split; intros H s Hs.
  - apply (proj1 (obsDWP_bind x f s post)). exact (H s Hs).
  - apply (proj2 (obsDWP_bind x f s post)). exact (H s Hs).
  - apply H. apply (proj2 (obsDWP_bind x f s post)). exact Hs.
  - apply H. apply (proj1 (obsDWP_bind x f s post)). exact Hs.
Qed.

(** SP (angelic, correctness) sequence rule, via [obsRel_bind]. *)
Theorem tripleSP_seq {S A B} (x : nditprog S A) (f : A -> nditprog S B)
  (pre : S -> Prop) (mid : option (A * S) -> Prop) (post : option (B * S) -> Prop) :
  tripleSP obsASP x Over pre mid ->
  (forall a s', mid (Some (a, s')) -> tripleSP obsASP (f a) Over (eq s') post) ->
  (mid None -> post None) ->
  tripleSP obsASP (x >>= f) Over pre post.
Proof.
  intros Hx Hf Hexc r Hr.
  unfold tripleSP, obsASP, asp in *.
  destruct Hr as [sigma [Hpre Hrel]].
  apply obsRel_bind in Hrel. destruct Hrel as [[a [s' [Hxr Hfr]]] | [HxN HrN]].
  - assert (Hmid : mid (Some (a, s'))).
    { apply Hx. exists sigma. split; [exact Hpre | exact Hxr]. }
    apply (Hf a s' Hmid). exists s'. split; [reflexivity | exact Hfr].
  - subst r. apply Hexc. apply Hx. exists sigma. split; [exact Hpre | exact HxN].
Qed.

(* ----------------------------------------------------------------- *)
(** *** The other working morphisms: the remaining WP observations    *)
(* ----------------------------------------------------------------- *)

(** [obsDWP] above is the canonical (demonic-total) WP morphism, but the
    demonic-liberal [obsDWLP] and the two angelic readings [obsAWP] /
    [obsAWLP] are *also* lawful monad morphisms: each preserves [ret] and
    [bind].  Each [obsX_bind] is the Dijkstra [wp_bind] law in the same
    shape as [obsDWP_bind] (the exception of [x] threads to [post None];
    divergence threads transparently through the liberal/angelic
    disjuncts).  Only the SP meet [obsDSP] and join [obsASLP] fail — see
    the counterexamples at the end of this section. *)

Lemma obsDWLP_unfold {S A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsDWLP m) s) post <->
  (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
              match oa with Some r => post r | None => True end).
Proof. unfold obsDWLP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

Lemma obsAWP_unfold {S A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsAWP m) s) post <->
  (exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r).
Proof. unfold obsAWP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

Lemma obsAWLP_unfold {S A} (m : nditprog S A) s post :
  unOptionT (runStateT (obsAWLP m) s) post <->
  ((exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r)
   \/ unOptionT (unOptionT (runStateT m s)) None).
Proof. unfold obsAWLP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

(** [wp_bind] for demonic-liberal WP. *)
Lemma obsDWLP_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
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

(** [wp_bind] for angelic-total WP. *)
Lemma obsAWP_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
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

(** [wp_bind] for angelic-liberal WP (the divergence disjunct threads
    through both [x] diverging and [f] diverging after [x] converges). *)
Lemma obsAWLP_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) s post :
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

(* ----------------------------------------------------------------- *)
(** *** Monad-view SP observation: a genuine monad morphism           *)
(* ----------------------------------------------------------------- *)

(** The [obsRel]/[obsASP] above are the *arrow*/reading view, used to
    state triples; they are not inhabitants of a [Monad] (and the [asp]
    reading would target the flagged-incorrect [ProgSP]).  Here is the
    *monad-view* observation [obsRelM : nditprog S A -> nditPredM S A]
    into the spec monad [nditPredM = stateT S (optionT (optionT (Pred
    unit)))] (the SP mirror of [ProgWP], with base [Pred unit] instead of
    [SetM]; lawful [Monad] + [MonadLawsE] via [PredFacts.v]).  It is the
    lifting along the base iso [SetM ~ Pred unit] — it copies [nditprog]'s
    full outcome predicate (divergence included) into [Pred unit].

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
  Definition obsRelM {A} (m : nditprog S A)
    : stateT S (optionT (optionT (Pred unit))) A :=
    mkStateT (fun s =>
      @mkOptionT (optionT (Pred unit)) (A * S) (
        @mkOptionT (Pred unit) (option (A * S)) (
          fun (_ : unit) (oa : option (option (A * S))) =>
            unOptionT (unOptionT (runStateT m s)) oa))).

  (** *** Connection to the arrow-view observations [obsRel] / [obsASP] *)

  (** [obsRelM] applied is just [nditprog]'s raw outcome predicate (the
      [unit] slot is ignored) — the [obsX_unfold]-style accessor. *)
  Lemma obsRelM_apply {A} (m : nditprog S A) s u oa :
    unOptionT (unOptionT (runStateT (obsRelM m) s)) u oa
    <-> unOptionT (unOptionT (runStateT m s)) oa.
  Proof. unfold obsRelM. cbn. tauto. Qed.

  (** Hence the arrow-view [obsRel] (and so every SP reading [obsASP =
      asp (obsRel _)], [obsDSLP], [obsDSP], [obsASLP]) is exactly the
      *terminating-slice* reading of [obsRelM] at [tt]: drop divergence,
      keep the [Some r] outcomes.  So [obsRelM] is the monad morphism and
      the observations used in triples are its readings. *)
  Lemma obsRel_obsRelM {A} (m : nditprog S A) s r :
    obsRel m s r <-> unOptionT (unOptionT (runStateT (obsRelM m) s)) tt (Some r).
  Proof. rewrite obsRelM_apply. unfold obsRel. destruct r as [[a s']|]; tauto. Qed.

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
      oa)] decompositions ([SetM]-bind vs [Pred unit]-bind); they differ
      only by equation orientation in the exception/divergence branches
      ([retPred]), discharged by [congruence]. *)
  Lemma obsRelM_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsRelM (x >>= f)) (obsRelM x >>= (fun a => obsRelM (f a))).
  Proof.
    unfold eq1, Eq1_stateT, Eq1_optionT, Eq1_Pred. intros s u oa.
    cbn. unfold bindPred. cbn.
    split; intros [b [Hb Hk]]; exists b; (split; [exact Hb|]);
      destruct b as [[[v s0]|]|]; cbn in *; (exact Hk || congruence).
  Qed.

End ObsRelM.

(* ================================================================= *)
(** ** [ProgSP]: the strongest-postcondition spec monad              *)
(* INCORRECT DEFINITION *)
(* ================================================================= *)

(** Forward / strongest-postcondition spec monad, dual to
    [ProgWP = stateT S (optionT PureWP)] (whose backward transformer is
    [PureWP A = (A -> Prop) -> Prop]).

    Modelled on the [ForwardPredTransformer] / [SP] monad of *Dijkstra
    Monads for All* (Maillard et al.): there [SP X = { f : forall p:SProp,
    X -> SPropOver p | monotone }] carries a *precondition* [p] forward to
    a postcondition that holds "over [p]" (i.e. implies [p]).  We keep the
    bare transformer (no bundled [over]/monotonicity) to match this
    project's bare [PureWP]. *)
Section ProgSPMonad.

  (** [PureSP] = forward predicate transformer: a precondition [Prop] and a
      value determine the strongest postcondition [Prop]. *)
  Definition PureSP (A : Type) : Type := Prop -> A -> Prop.

  Definition ProgSP (S A : Type) : Type := stateT S (optionT PureSP) A.

  (** [pp2sp pre post] embeds a Hoare pre-/post-condition pair as a [ProgSP],
      exactly as DM4All's [pp2sp0 (P, Q) pre x := pre /\ (P -> Q x)]: at
      initial state [s0], outcome [r] is in the strongest postcondition under
      precondition [p] iff [p] holds and [pre s0 -> post r]. *)
  Definition pp2sp {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : ProgSP S A :=
    mkStateT (fun s0 => @mkOptionT PureSP _
                          (fun p r => p /\ (pre s0 -> post r))).

  (** Pointwise refinement order on [ProgSP] — DM4All's [SP_rel]
      [fun m1 m2 => forall p x, Spr1 m1 p x -> Spr1 m2 p x], threaded through
      the state [s] and precondition [p]. *)
  Definition ordProgSP {S A} (m1 m2 : ProgSP S A) : Prop :=
    forall s p r,
      unOptionT (runStateT m1 s) p r -> unOptionT (runStateT m2 s) p r.

End ProgSPMonad.

(* ================================================================= *)
(** ** [ProgSP]-valued observation and refinement-style triple         *)
(* ================================================================= *)

(** The [ProgSP] analogues of the WP observation [obsAWP] and the
    refinement triple, in a module to avoid clashing with the
    [ASPostArr]-valued [obsASP] / [as_sp_obs]-based [tripleSP] above
    (cf. [Observation.WPredObs]).  Refer to them as [ProgSPObs.obsASP]
    and [ProgSPObs.tripleSP]. *)
Module ProgSPObs.

  (** Angelic strongest-postcondition observation as a [ProgSP]: from
      initial state [s] under precondition [p], outcome [r] is in the
      strongest postcondition iff [p] held and [r] is reachable from [s].
      This is DM4All's [SP_ret]-style [fun p y => p s/\ a ≡ y] generalised
      to the reachability relation [obsRel]. *)
  Definition obsASP {S A} (m : nditprog S A) : ProgSP S A :=
    mkStateT (fun s => @mkOptionT PureSP _
                         (fun p r => p /\ obsRel m s r)).

  (** SP triple in the spec-as-element / refinement style, using [pp2sp]
      and [ordProgSP] (dual to the old WP refinement triple).

      - [Over]  is over-approximation  [sp(pre) ⊆ post]  (= [obs ⊑ pp2sp]);
      - [Under] is under-approximation  [post ⊆ sp(pre)]  (= [pp2sp ⊑ obs]).

      The inclusion directions are *flipped* relative to the WP refinement
      triple, since SP is the forward (covariant) transformer. *)
  Definition tripleSP {S A}
    (obs : nditprog S A -> ProgSP S A) (prog : nditprog S A)
    (kind : approximationKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordProgSP (obs prog) (pp2sp pre post)
    | Under => ordProgSP (pp2sp pre post) (obs prog)
    end.

End ProgSPObs.
