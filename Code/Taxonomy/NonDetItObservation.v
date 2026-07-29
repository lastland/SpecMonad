(** * Observation functions for [nditprog].

    SP observation: maps [nditprog S A] to [ASPostArr S A].
    The three-valued outcome space ([Some (Some _)], [Some None],
    [None]) is collapsed into [option (A * S)]:
    - [Some (a, s')] from converging outcomes
    - [None] from exceptions OR divergence

    WP observations: [obsDWP] / [obsDWLP] (demonic total / partial)
    and [obsAWP] / [obsAWLP] (angelic total / partial) map into
    [ProgWP S A].  Inclusion proofs: Theorem 3.7. *)

From Coq Require Import Lia Classical_Prop PeanoNat Morphisms RelationClasses FunctionalExtensionality PropExtensionality.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg NonDetProgFacts NonDetItProgFacts ProgFacts WP Pred PredFacts SPost WPred.

Import MonadNotation.
Open Scope monad_scope.

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

Definition pp2sp_over {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : (S -> Prop) -> option (A * S) -> Prop :=
  fun p r => (forall s, p s -> pre s) -> post r.

Definition pp2sp_under {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : (S -> Prop) -> option (A * S) -> Prop :=
  fun p r => (forall s, pre s -> p s) /\ post r.

Definition ordProgSP {S A} (m1 m2 : (S -> Prop) -> option (A * S) -> Prop) : Prop :=
  forall pre r, m1 pre r -> m2 pre r.

Definition tripleSPspec {S A}
  (obs : nditprog S A -> (S -> Prop) -> option (A * S) -> Prop)
  (prog : nditprog S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
  match kind with
  | Over  => ordProgSP (obs prog) (pp2sp_over pre post)
  | Under => ordProgSP (pp2sp_under pre post) (obs prog)
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
  (obs : nditprog S A -> (S -> Prop) -> option (A * S) -> Prop)
  (prog : nditprog S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  (Hmono : forall (p q : S -> Prop),
     (forall s, p s -> q s) ->
     forall r, obs prog p r -> obs prog q r) :
    tripleSP obs prog kind pre post <-> tripleSPspec obs prog kind pre post.
  Proof.
    unfold tripleSP, tripleSPspec, ordProgSP, pp2sp_over, pp2sp_under.
    destruct kind; split.
    - intros H p r [Hsub Hpost]. apply (Hmono pre p Hsub r). apply H. exact Hpost.
    - intros H r Hpost. apply (H pre r). split; [intros s hs; exact hs | exact Hpost].
    - intros H p r Hsp Hsub. apply H. apply (Hmono p pre Hsub r). exact Hsp.
    - intros H r Hsp. apply (H pre r Hsp). intros s hs; exact hs.
  Qed.

End tripleSPDefEq.

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

Section NonDetItObservationWP.

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

End NonDetItObservationWP.

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
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  tripleWP obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

Theorem progA_DWP_all_spec :
  tripleWPspec obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  (* [tripleWPspec _ Under] is the spec-as-WP-element form
     [(pre s /\ post <= p) -> wp p s]; derive it from the direct form
     [progA_DWP_all] by monotonicity of [obsDWP] in its postcondition. *)
  unfold tripleWPspec, ordProgWP, pp2wp_subset.
  intros s p Hp. cbn [runStateT unOptionT] in Hp. destruct Hp as [_ Hsub].
  pose proof progA_DWP_all as Hall. unfold tripleWP in Hall. specialize (Hall s I).
  unfold obsDWP in Hall |- *. cbn [runStateT unOptionT] in Hall |- *.
  destruct (runStateT progA s) as [[outcomes]].
  intros oa Hoa. specialize (Hall oa Hoa).
  destruct oa as [r|]; [exact (Hsub r Hall) | exact Hall].
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 : 
  not (
    tripleWP obsDWP progA
      (fun _ => True)
      SubsetOf
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
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

Theorem progA_AWP_43 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 43
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 43)). split; sauto.
Qed.

(** AWP, over-approximate ([Over]) reading: [awp(post) ⊆ pre], the
    "necessary precondition" of partial incorrectness — every state from
    which [progA] can *angelically* reach an outcome in [post] must lie in
    [pre].  [progA] overwrites the state with [put 42] and then yields [42]
    or [43], so no run reaches state [100]; hence [awp(reach 100)] is empty
    and even the empty precondition [fun _ => False] is a valid (necessary)
    precondition.  (Contrast: for a *reachable* post like [reach 43],
    [awp] would be all of [nat], forcing [pre] to be [True].) *)
Theorem progA_AWP_100_over :
  tripleWP obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  unfold tripleWP. intros s H. cbn in H.
  destruct H as [r [Hr Heq]]. subst r. cbn in Hr. sauto.
Qed.

Theorem progA_AWP_100_over_spec :
  tripleWPspec obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  (* [tripleWPspec _ Over] is [forall s p, awp p s -> ((p <= post) -> pre s)].
     An angelic witness [r] of [awp p s] satisfies [p], hence [p <= post]
     forces [r = Some (tt, 100)] — unreachable for [progA]. *)
  unfold tripleWPspec, ordProgWP, pp2wp_superset.
  intros s p Hp Hsub. cbn in Hp.
  destruct Hp as [r [Hr Hpr]]. specialize (Hsub r Hpr).
  subst r. cbn in Hr. sauto.
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
    tripleWP obsDWP progB
      (fun _ => True)
      SubsetOf
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
  tripleWP obsDWLP progB
    (fun _ => True)
    SubsetOf
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
  tripleWP obsAWP progB
    (fun _ => True)
    SubsetOf
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
  tripleWP obsAWLP progB (fun _ => True) SubsetOf (fun _ => False).
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

  (** Galois connection (incorrectness side) — the connection
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
    forall A (m: nditprog S A) pre post,
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
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m pre SupersetOf post ->
        tripleSP obsDSLP m Under pre post.
  Proof. intros A m pre post; apply awp_dslp. Qed.

End TaxonomyGaloisConnections.

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
      (tripleWP obsDWLP m pre SubsetOf post1 /\
         tripleWP obsDWLP m pre SubsetOf post2) ->
      tripleWP obsDWLP m pre SubsetOf (fun r => post1 r /\ post2 r).
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
      tripleWP obsDWLP m pre SubsetOf (fun r => post1 r /\ post2 r) ->
       (tripleWP obsDWLP m pre SubsetOf post1 /\
         tripleWP obsDWLP m pre SubsetOf post2).
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
      (tripleWP obsDWLP m pre SubsetOf post1 /\
         tripleWP obsDWLP m pre SubsetOf post2) <->
        tripleWP obsDWLP m pre SubsetOf (fun r => post1 r /\ post2 r).
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
        (tripleWP obsDWLP m pre SubsetOf post /\
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
        (tripleSP obsASP m Under u u' /\ tripleWP obsDWLP m o SubsetOf o' /\
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
        (tripleSP obsASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleWP obsDWLP m o SubsetOf o').
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
   
  Theorem dwlp_under {A} :
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

    Theorem awlp_under {A} :
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

    Theorem dwp_under {A} :
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

    Theorem awp_under {A} :
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
    (** Curried [Over] form: [wp p s] alone is the antecedent, implying the
        rest [(p <= post) -> pre s].  The order constraint [p <= post] is a
        guard on the conclusion (not a conjunct to establish), which is what
        makes this hold — cf. the failing naive form in [dwlp_breaks]. *)
    Theorem dwlp_over {A} :
      forall (m : nditprog S A) pre post,
        (forall s, unOptionT (runStateT (obsDWLP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsDWLP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.
        unfold obsDWLP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        intros oa Hoa. specialize (Hp oa Hoa).
        destruct oa as [r|]; [exact (Hsub r Hp) | exact I].
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.

    Theorem awlp_over {A} :
      forall (m : nditprog S A) pre post,
        (forall s, unOptionT (runStateT (obsAWLP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsAWLP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.
        unfold obsAWLP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        destruct Hp as [[r [Hr Hp]] | Hdiv].
        + left. exists r. split; [exact Hr | exact (Hsub r Hp)].
        + right. exact Hdiv.
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.

    Theorem dwp_over {A} :
      forall (m : nditprog S A) pre post,
        (forall s, unOptionT (runStateT (obsDWP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsDWP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.
        unfold obsDWP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        intros oa Hoa. specialize (Hp oa Hoa).
        destruct oa as [r|]; [exact (Hsub r Hp) | exact Hp].
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.
    
    Theorem awp_over {A} :
      forall (m : nditprog S A) pre post,
        (forall s, unOptionT (runStateT (obsAWP m) s) post -> pre s) <->
          (forall s p, unOptionT (runStateT (obsAWP m) s) p ->
                       ((forall r, p r -> post r) -> pre s)).
    Proof.
      intros m pre post. split.
      - intros H s p Hp Hsub. apply H.
        unfold obsAWP in *. cbn [runStateT unOptionT] in *.
        destruct (runStateT m s) as [[outcomes]].
        destruct Hp as [r [Hr Hp]]. exists r. split; [exact Hr | exact (Hsub r Hp)].
      - intros H s Hpost.
        apply (H s post Hpost). intros r hr; exact hr.
    Qed.
End TripleDefinitions.

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

(* ================================================================= *)
(** ** Two specification categories: monotone predicate transformers   *)
(* ================================================================= *)

(** Everything from here on is organized around a single object -- a
    *monotone predicate transformer* [MonPT X Y] -- and TWO specification
    categories built from it that differ ONLY in the DIRECTION of the
    transformer:

      - weakest precondition (backward):
          hom  S ~> option (A * S)   =   monotone  (option (A*S) -> Prop) -> (S -> Prop)
        a postcondition on outcomes is mapped to a precondition on states;

      - strongest postcondition (forward):
          hom  S ~> option (A * S)   =   monotone  (S -> Prop) -> (option (A*S) -> Prop)
        a precondition on states is mapped to a postcondition on outcomes.

    Both are instances of the same [SpecCategory] over the same underlying
    hom object [MonPT]; the WP category [WPHom] is the SP category [SPHom]
    with its arrows reversed (composition runs the other way).  Over each
    we build a generalized Dijkstra monad, and all three monads -- [Ddwlp]
    (WP), [Dsp] and [Dasp] (SP) -- are the very same construction
    [{ m | w <= obs m }] (or its flip) read through the two directions.
    The membership order is [pt_le], which is [cat_le] in each category. *)

(* --- the abstract specification-category interface --- *)

Class Category (W : Type -> Type -> Type) :=
{
  cat_id : forall {A}, W A A ;
  cat_comp : forall {A B C}, W A B -> W B C -> W A C ;
}.

Class SpecCategory (W : Type -> Type -> Type) {CW : Category W} :=
{
  cat_eq : forall {A B}, W A B -> W A B -> Prop ;
  cat_le : forall {A B}, W A B -> W A B -> Prop ;

  cat_eq_equiv :: forall A B, Equivalence (@cat_eq A B) ;
  cat_le_preorder :: forall A B, PreOrder (@cat_le A B) ;

  cat_comp_id_l : forall {A B} (f : W A B), cat_eq (cat_comp cat_id f) f ;
  cat_comp_id_r : forall {A B} (f : W A B), cat_eq (cat_comp f cat_id) f ;
  cat_comp_assoc : forall {A B C D} (f : W A B) (g : W B C) (h : W C D),
    cat_eq (cat_comp (cat_comp f g) h) (cat_comp f (cat_comp g h)) ;

  cat_comp_proper :: forall A B C,
    Proper (cat_eq ==> cat_eq ==> cat_eq) (@cat_comp W CW A B C) ;

  cat_comp_mono : forall {A B C} (f f' : W A B) (g g' : W B C),
    cat_le f f' -> cat_le g g' -> cat_le (cat_comp f g) (cat_comp f' g') ;
  cat_eq_le : forall {A B} (f g : W A B), cat_eq f g -> cat_le f g ;
}.

(* --- the shared hom object: monotone predicate transformers --- *)

Definition PT (X Y : Type) : Type := (X -> Prop) -> (Y -> Prop).

Definition pt_mono {X Y} (t : PT X Y) : Prop :=
  forall p q, (forall x, p x -> q x) -> forall y, t p y -> t q y.

Definition MonPT (X Y : Type) : Type := { t : PT X Y | pt_mono t }.

(** Refinement order and hom-setoid: pointwise implication / iff. *)
Definition pt_le {X Y} (f g : MonPT X Y) : Prop :=
  forall p y, proj1_sig f p y -> proj1_sig g p y.
Definition pt_eq {X Y} (f g : MonPT X Y) : Prop :=
  forall p y, proj1_sig f p y <-> proj1_sig g p y.

Lemma pt_le_preorder {X Y} : PreOrder (@pt_le X Y).
Proof.
  constructor.
  - intros f p y H; exact H.
  - intros f g h H1 H2 p y H; apply H2, H1, H.
Qed.

Lemma pt_eq_equiv {X Y} : Equivalence (@pt_eq X Y).
Proof.
  constructor.
  - intros f p y; reflexivity.
  - intros f g H p y; symmetry; apply H.
  - intros f g h H1 H2 p y; etransitivity; [ apply H1 | apply H2 ].
Qed.

Lemma pt_eq_iff {X Y} (f g : MonPT X Y) :
  pt_eq f g <-> (pt_le f g /\ pt_le g f).
Proof.
  unfold pt_eq, pt_le; split.
  - intro H; split; intros p y HH;
      [ exact (proj1 (H p y) HH) | exact (proj2 (H p y) HH) ].
  - intros [H1 H2] p y; split; [ apply H1 | apply H2 ].
Qed.

Lemma pt_eq_le {X Y} (f g : MonPT X Y) : pt_eq f g -> pt_le f g.
Proof. intro H; apply pt_eq_iff in H; apply H. Qed.

Lemma id_pt_mono {X} : pt_mono (fun p : X -> Prop => p).
Proof. intros p q Hpq y H; apply Hpq, H. Qed.

Lemma comp_pt_mono {X Y Z} (u : PT X Y) (v : PT Y Z) :
  pt_mono u -> pt_mono v -> pt_mono (fun p => v (u p)).
Proof.
  intros Hu Hv p q Hpq z H.
  eapply Hv; [ | exact H ]. intros y Hy. eapply Hu; [ exact Hpq | exact Hy ].
Qed.

(* --- SP: the forward / strongest-postcondition category --- *)
(** A hom [SPHom A B] is a monotone forward transformer
    [(A -> Prop) -> (B -> Prop)]; composition is forward function
    composition [fun p => g (f p)]. *)

Definition SPHom (A B : Type) : Type := MonPT A B.

#[global] Instance Category_SP : Category SPHom :=
{|
  cat_id := fun A => exist _ (fun p => p) (@id_pt_mono A) ;
  cat_comp := fun A B C f g =>
    exist _ (fun p => proj1_sig g (proj1_sig f p))
          (comp_pt_mono _ _ (proj2_sig f) (proj2_sig g)) ;
|}.

Lemma sp_comp_id_l {A B} (f : SPHom A B) : pt_eq (cat_comp cat_id f) f.
Proof. intros p y; reflexivity. Qed.
Lemma sp_comp_id_r {A B} (f : SPHom A B) : pt_eq (cat_comp f cat_id) f.
Proof. intros p y; reflexivity. Qed.
Lemma sp_comp_assoc {A B C D} (f : SPHom A B) (g : SPHom B C) (h : SPHom C D) :
  pt_eq (cat_comp (cat_comp f g) h) (cat_comp f (cat_comp g h)).
Proof. intros p y; reflexivity. Qed.

Lemma sp_comp_mono {A B C} (f f' : SPHom A B) (g g' : SPHom B C) :
  pt_le f f' -> pt_le g g' -> pt_le (cat_comp f g) (cat_comp f' g').
Proof.
  intros Hf Hg p c H.
  apply (proj2_sig g' (proj1_sig f p) (proj1_sig f' p)).
  - intros b Hb; exact (Hf p b Hb).
  - exact (Hg (proj1_sig f p) c H).
Qed.

Lemma sp_comp_proper {A B C} :
  Proper (pt_eq ==> pt_eq ==> pt_eq) (@cat_comp SPHom _ A B C).
Proof.
  intros f f' Hf g g' Hg.
  apply pt_eq_iff; apply pt_eq_iff in Hf, Hg.
  destruct Hf as [Hf1 Hf2], Hg as [Hg1 Hg2].
  split; apply sp_comp_mono; assumption.
Qed.

#[global] Instance SpecCategory_SP : SpecCategory SPHom :=
{|
  cat_eq := @pt_eq ;
  cat_le := @pt_le ;
  cat_eq_equiv    := @pt_eq_equiv ;
  cat_le_preorder := @pt_le_preorder ;
  cat_comp_id_l   := @sp_comp_id_l ;
  cat_comp_id_r   := @sp_comp_id_r ;
  cat_comp_assoc  := @sp_comp_assoc ;
  cat_comp_proper := @sp_comp_proper ;
  cat_comp_mono   := @sp_comp_mono ;
  cat_eq_le       := @pt_eq_le ;
|}.

(* --- WP: the backward / weakest-precondition category --- *)
(** A hom [WPHom A B] is a monotone backward transformer
    [(B -> Prop) -> (A -> Prop)] -- i.e. [MonPT B A] -- and composition is
    backward function composition [fun p => f (g p)].  This is [SPHom]
    with its arrows reversed. *)

Definition WPHom (A B : Type) : Type := MonPT B A.

#[global] Instance Category_WP : Category WPHom :=
{|
  cat_id := fun A => exist _ (fun p => p) (@id_pt_mono A) ;
  cat_comp := fun A B C f g =>
    exist _ (fun p => proj1_sig f (proj1_sig g p))
          (comp_pt_mono _ _ (proj2_sig g) (proj2_sig f)) ;
|}.

Lemma wp_comp_id_l {A B} (f : WPHom A B) : pt_eq (cat_comp cat_id f) f.
Proof. intros p y; reflexivity. Qed.
Lemma wp_comp_id_r {A B} (f : WPHom A B) : pt_eq (cat_comp f cat_id) f.
Proof. intros p y; reflexivity. Qed.
Lemma wp_comp_assoc {A B C D} (f : WPHom A B) (g : WPHom B C) (h : WPHom C D) :
  pt_eq (cat_comp (cat_comp f g) h) (cat_comp f (cat_comp g h)).
Proof. intros p y; reflexivity. Qed.

Lemma wp_comp_mono {A B C} (f f' : WPHom A B) (g g' : WPHom B C) :
  pt_le f f' -> pt_le g g' -> pt_le (cat_comp f g) (cat_comp f' g').
Proof.
  intros Hf Hg p a H.
  apply (proj2_sig f' (proj1_sig g p) (proj1_sig g' p)).
  - intros b Hb; exact (Hg p b Hb).
  - exact (Hf (proj1_sig g p) a H).
Qed.

Lemma wp_comp_proper {A B C} :
  Proper (pt_eq ==> pt_eq ==> pt_eq) (@cat_comp WPHom _ A B C).
Proof.
  intros f f' Hf g g' Hg.
  apply pt_eq_iff; apply pt_eq_iff in Hf, Hg.
  destruct Hf as [Hf1 Hf2], Hg as [Hg1 Hg2].
  split; apply wp_comp_mono; assumption.
Qed.

#[global] Instance SpecCategory_WP : SpecCategory WPHom :=
{|
  cat_eq := fun A B => @pt_eq B A ;
  cat_le := fun A B => @pt_le B A ;
  cat_eq_equiv    := fun A B => @pt_eq_equiv B A ;
  cat_le_preorder := fun A B => @pt_le_preorder B A ;
  cat_comp_id_l   := @wp_comp_id_l ;
  cat_comp_id_r   := @wp_comp_id_r ;
  cat_comp_assoc  := @wp_comp_assoc ;
  cat_comp_proper := @wp_comp_proper ;
  cat_comp_mono   := @wp_comp_mono ;
  cat_eq_le       := fun A B => @pt_eq_le B A ;
|}.

(* ================================================================= *)
(** ** The generalized Dijkstra monads over the two categories         *)
(* ================================================================= *)

(** For a computation [m : nditprog S A]:
      - its strongest postcondition [obsASP_pt m] is a FORWARD morphism
        [SPHom S (option (A*S))] = monotone [(S->Prop) -> (option(A*S)->Prop)];
      - its demonic weakest-liberal precondition [obsDWLP_pt m] is a
        BACKWARD morphism
        [WPHom S (option (A*S))] = monotone [(option(A*S)->Prop) -> (S->Prop)].
    A generalized Dijkstra monad indexes [m] by a spec morphism [w] and
    records that the observation refines it (or is refined by it), using
    [pt_le] (= [cat_le] in the relevant category). *)

Section GeneralizedDijkstra.
  Variable S : Type.
  #[local] Existing Instance Monad__nditprog.

  (* --- the two observations, as points of the two hom-posets --- *)

  Lemma asp_mono {A B} (R : Pred A B) : pt_mono (asp R).
  Proof.
    intros p q Hpq b H. unfold asp in *. destruct H as [a [Hp HR]].
    exists a. split; [ apply Hpq; exact Hp | exact HR ].
  Qed.

  Definition obsASP_pt {A} (m : nditprog S A) : SPHom S (option (A * S)) :=
    exist _ (obsASP m) (asp_mono (obsRel m)).

  Lemma obsDWLP_pt_mono {A} (m : nditprog S A) :
    pt_mono (fun post s => unOptionT (runStateT (obsDWLP m) s) post).
  Proof. intros p q Hpq s H. exact (obsDWLP_monotonic S m s p q Hpq H). Qed.

  Definition obsDWLP_pt {A} (m : nditprog S A) : WPHom S (option (A * S)) :=
    exist _ (fun post s => unOptionT (runStateT (obsDWLP m) s) post)
          (obsDWLP_pt_mono m).

  (* --- SP incorrectness (under-approximation): [w <= obsASP m] --- *)
  (** Everything [w] declares reachable really is reachable. *)
  Definition Dsp {A} (w : SPHom S (option (A * S))) : Type :=
    { m : nditprog S A | pt_le w (obsASP_pt m) }.

  #[program] Definition Dsp_ret {A} (a : A)
    : Dsp (obsASP_pt (@ret (nditprog S) _ A a)) := @ret (nditprog S) _ A a.
  Next Obligation. intros pre r H. exact H. Qed.

  (** Under-approximation: weakening SHRINKS the spec ([w' <= w]). *)
  #[program] Definition Dsp_wkn {A} {w w' : SPHom S (option (A * S))}
    (d : Dsp w) (Hle : pt_le w' w) : Dsp w' := proj1_sig d.
  Next Obligation. intros pre r H. apply (proj2_sig d). apply Hle. exact H. Qed.

  Lemma Dsp_ret_carrier {A} (a : A) : proj1_sig (Dsp_ret a) = ret a.
  Proof. reflexivity. Qed.
  Lemma Dsp_wkn_carrier {A} {w w' : SPHom S (option (A * S))}
    (d : Dsp w) (Hle : pt_le w' w) : proj1_sig (Dsp_wkn d Hle) = proj1_sig d.
  Proof. reflexivity. Qed.

  (* --- SP partial correctness (over-approximation): [obsASP m <= w] --- *)
  (** Every reachable outcome lies in [w].  Flip of [Dsp]. *)
  Definition Dasp {A} (w : SPHom S (option (A * S))) : Type :=
    { m : nditprog S A | pt_le (obsASP_pt m) w }.

  #[program] Definition Dasp_ret {A} (a : A)
    : Dasp (obsASP_pt (@ret (nditprog S) _ A a)) := @ret (nditprog S) _ A a.
  Next Obligation. intros pre r H. exact H. Qed.

  (** Over-approximation: weakening ENLARGES the spec ([w <= w']). *)
  #[program] Definition Dasp_wkn {A} {w w' : SPHom S (option (A * S))}
    (d : Dasp w) (Hle : pt_le w w') : Dasp w' := proj1_sig d.
  Next Obligation. intros pre r H. apply Hle. apply (proj2_sig d). exact H. Qed.

  Lemma Dasp_ret_carrier {A} (a : A) : proj1_sig (Dasp_ret a) = ret a.
  Proof. reflexivity. Qed.
  Lemma Dasp_wkn_carrier {A} {w w' : SPHom S (option (A * S))}
    (d : Dasp w) (Hle : pt_le w w') : proj1_sig (Dasp_wkn d Hle) = proj1_sig d.
  Proof. reflexivity. Qed.

  (* --- WP partial correctness (sound Hoare): [w <= obsDWLP m] --- *)
  (** The demonic WP guarantees everything [w] requires. *)
  Definition Ddwlp {A} (w : WPHom S (option (A * S))) : Type :=
    { m : nditprog S A | pt_le w (obsDWLP_pt m) }.

  #[program] Definition Ddwlp_ret {A} (a : A)
    : Ddwlp (obsDWLP_pt (@ret (nditprog S) _ A a)) := @ret (nditprog S) _ A a.
  Next Obligation. intros post s H. exact H. Qed.

  (** Requirement reading: weakening SHRINKS the spec ([w' <= w]). *)
  #[program] Definition Ddwlp_wkn {A} {w w' : WPHom S (option (A * S))}
    (d : Ddwlp w) (Hle : pt_le w' w) : Ddwlp w' := proj1_sig d.
  Next Obligation. intros post s H. apply (proj2_sig d). apply Hle. exact H. Qed.

  Lemma Ddwlp_ret_carrier {A} (a : A) : proj1_sig (Ddwlp_ret a) = ret a.
  Proof. reflexivity. Qed.
  Lemma Ddwlp_wkn_carrier {A} {w w' : WPHom S (option (A * S))}
    (d : Ddwlp w) (Hle : pt_le w' w) : proj1_sig (Ddwlp_wkn d Hle) = proj1_sig d.
  Proof. reflexivity. Qed.

  (** The Galois connection [asp -| dwlp] relating the two directions: the
      forward (SP) reading of partial correctness coincides with the
      backward (demonic-WLP) one. *)
  Lemma asp_dwlp_galois {A} (m : nditprog S A)
    (P : S -> Prop) (Q : option (A * S) -> Prop) :
    (forall r, obsASP m P r -> Q r)
    <-> (forall s, P s -> forall r, obsRel m s r -> Q r).
  Proof.
    unfold obsASP, asp. split.
    - intros H s Hs r Hr. apply H. exists s. split; assumption.
    - intros H r [s [Hs Hr]]. exact (H s Hs r Hr).
  Qed.

End GeneralizedDijkstra.

(** [obsDWLP] is exactly the demonic weakest-liberal precondition of the
    reachability relation [obsRel]: the WP over [post] holds iff every
    reachable outcome satisfies [post].  This bridges the WP and SP
    observations of the same computation. *)
Lemma obsDWLP_obsRel {S A} (m : nditprog S A) (s : S)
  (post : option (A * S) -> Prop) :
  unOptionT (runStateT (obsDWLP m) s) post <-> (forall r, obsRel m s r -> post r).
Proof.
  rewrite obsDWLP_unfold. unfold obsRel. split.
  - intros H r Hr. apply (H (Some r)). destruct r as [[a s']|]; exact Hr.
  - intros H oa Hoa. destruct oa as [r|]; [ | exact I ].
    cbn. apply H. destruct r as [[a s']|]; exact Hoa.
Qed.

(* ================================================================= *)
(** ** Example: verifying [incr] in all three Dijkstra monads          *)
(* ================================================================= *)

(** The same program [incr] is verified against a partial-correctness
    property "[incr] leaves the state >= 1" in each of the three monads:
    [Ddwlp] (backward WP), and [Dasp] (forward SP).  Uniform code, only
    the transformer direction differs. *)

Section DijkstraExamples.
  #[local] Existing Instance Monad__nditprog.

  (* --- demonic-liberal WP of the atomic operations --- *)
  Lemma dwlp_get (s : nat) (post : option (nat * nat) -> Prop) :
    unOptionT (runStateT (obsDWLP (get : nditprog nat nat)) s) post
    <-> post (Some (s, s)).
  Proof. rewrite obsDWLP_unfold. cbn. split; sauto limit: 200. Qed.

  Lemma dwlp_put (c s : nat) (post : option (unit * nat) -> Prop) :
    unOptionT (runStateT (obsDWLP (put c : nditprog nat unit)) s) post
    <-> post (Some (tt, c)).
  Proof. rewrite obsDWLP_unfold. cbn. split; sauto limit: 200. Qed.

  (* --- the program: increment the state --- *)
  Definition incr : nditprog nat unit := x <- get ;; put (x + 1).

  (* --- the demonic-liberal WP of [incr], computed compositionally --- *)
  Lemma incr_dwlp (s : nat) post :
    unOptionT (runStateT (obsDWLP incr) s) post <-> post (Some (tt, s + 1)).
  Proof.
    unfold incr. rewrite obsDWLP_bind, dwlp_get. cbv beta iota.
    rewrite dwlp_put. reflexivity.
  Qed.

  (* --- [incr]'s only reachable outcome from [s] is [Some (tt, s+1)] --- *)
  Lemma incr_reach (s : nat) (r : option (unit * nat)) :
    obsRel incr s r -> r = Some (tt, s + 1).
  Proof.
    intro Hr.
    refine (proj1 (obsDWLP_obsRel incr s (fun r' => r' = Some (tt, s + 1))) _ r Hr).
    apply (proj2 (incr_dwlp s (fun r' => r' = Some (tt, s + 1)))). reflexivity.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** (1) WP direction: [Ddwlp] over the backward transformer      *)
  (* --------------------------------------------------------------- *)

  (** Exact spec as a backward WP transformer
      [(option(unit*nat)->Prop) -> (nat->Prop)]. *)
  #[program] Definition incr_spec : WPHom nat (option (unit * nat)) :=
    fun post s => post (Some (tt, s + 1)).
  Next Obligation. intros p q Hpq s H. apply Hpq, H. Qed.

  Program Definition incr_verified : Ddwlp nat incr_spec := incr.
  Next Obligation. intros post s H. exact (proj2 (incr_dwlp s post) H). Qed.

  (** A weaker WP annotation, "final state >= 1", still verifies. *)
  #[program] Definition incr_ge1 : WPHom nat (option (unit * nat)) :=
    fun post s => forall s', 1 <= s' -> post (Some (tt, s')).
  Next Obligation. intros p q Hpq s H s' Hs'. apply Hpq, (H s' Hs'). Qed.

  Program Definition incr_meets_ge1 : Ddwlp nat incr_ge1 := incr.
  Next Obligation.
    intros post s H. cbn in H.
    apply (proj2 (incr_dwlp s post)). apply (H (s + 1)). lia.
  Qed.

  (** ...equivalently by weakening the exact verification. *)
  Lemma incr_ge1_below_spec : pt_le incr_ge1 incr_spec.
  Proof. intros post s H. cbn in *. apply (H (s + 1)). lia. Qed.

  Definition incr_meets_ge1' : Ddwlp nat incr_ge1 :=
    Ddwlp_wkn nat incr_verified incr_ge1_below_spec.

  (* --------------------------------------------------------------- *)
  (** *** (2) SP direction: [Dasp] over the forward transformer        *)
  (* --------------------------------------------------------------- *)

  (** The SAME property as a forward SP transformer
      [(nat->Prop) -> (option(unit*nat)->Prop)]: "every reachable outcome
      leaves the state >= 1". *)
  #[program] Definition sp_ge1 : SPHom nat (option (unit * nat)) :=
    fun _ r => match r with Some (_, s') => 1 <= s' | None => True end.
  Next Obligation. intros p q Hpq b H. exact H. Qed.

  Program Definition incr_meets_ge1_sp : Dasp nat sp_ge1 := incr.
  Next Obligation.
    intros pre r Hasp. destruct Hasp as [s [Hs Hr]].
    apply incr_reach in Hr. subst r. cbn. lia.
  Qed.

End DijkstraExamples.

(* ================================================================= *)
(** ** DM4All-style Dijkstra monad over the spec MONAD [ProgWP S]       *)
(* ================================================================= *)

(** The original "Dijkstra Monads for All" construction indexes
    computations by ELEMENTS of an ordered specification MONAD, not by
    morphisms of a specification category.  Here the spec monad is
    [ProgWP S] (state + exception weakest preconditions), the effect
    observation is [obsDWLP : nditprog S ~> ProgWP S], and the refinement
    order is [ordProgWP].  The [Dtheta] construction (sound direction) is

        Ddwlp_mon w := { m : nditprog S A | w <=[ordProgWP] obsDWLP m }.

    [ProgWP] is a *representable* specification category: a (monotone)
    element [w : ProgWP S A] is the same data as a backward hom-morphism
    [WPHom S (option (A*S))] -- the two are related by currying, [to_hom].
    Consequently this element-indexed Dijkstra monad is EQUIVALENT to the
    morphism-indexed [Ddwlp]: same carriers, and the membership conditions
    coincide (they differ only by swapping [forall s post]). *)

Section DijkstraMonadDM4All.
  Variable S : Type.
  #[local] Existing Instance Monad__nditprog.

  (** Healthiness on the spec monad: monotone in the postcondition. *)
  Definition progwp_mono {A} (w : ProgWP S A) : Prop :=
    forall s (p q : option (A * S) -> Prop),
      (forall r, p r -> q r) ->
      unOptionT (runStateT w s) p -> unOptionT (runStateT w s) q.

  (** The DM4All Dijkstra monad, indexed by a spec-monad element. *)
  Definition Ddwlp_mon {A} (w : ProgWP S A) : Type :=
    { m : nditprog S A | ordProgWP w (obsDWLP m) }.

  (** [ret], specified by its own observed weakest precondition. *)
  #[program] Definition Ddwlp_mon_ret {A} (a : A)
    : Ddwlp_mon (obsDWLP (@ret (nditprog S) _ A a)) := @ret (nditprog S) _ A a.
  Next Obligation. intros s p H. exact H. Qed.

  (** Weakening along [ordProgWP] (sound direction: shrink the spec). *)
  #[program] Definition Ddwlp_mon_wkn {A} {w w' : ProgWP S A}
    (d : Ddwlp_mon w) (Hle : ordProgWP w' w) : Ddwlp_mon w' := proj1_sig d.
  Next Obligation. intros s p H. apply (proj2_sig d). apply Hle. exact H. Qed.

  Lemma Ddwlp_mon_ret_carrier {A} (a : A) : proj1_sig (Ddwlp_mon_ret a) = ret a.
  Proof. reflexivity. Qed.
  Lemma Ddwlp_mon_wkn_carrier {A} {w w' : ProgWP S A}
    (d : Ddwlp_mon w) (Hle : ordProgWP w' w) :
    proj1_sig (Ddwlp_mon_wkn d Hle) = proj1_sig d.
  Proof. reflexivity. Qed.

  (* --- representability: a monotone spec element IS a WP morphism --- *)

  (** Currying [w : ProgWP S A] into the backward hom [WPHom]. *)
  #[program] Definition to_hom {A} (w : ProgWP S A) (H : progwp_mono w)
    : WPHom S (option (A * S)) :=
    fun post s => unOptionT (runStateT w s) post.
  Next Obligation. intros p q Hpq s Hw. exact (H s p q Hpq Hw). Qed.

  (** The observation transported by [to_hom] is exactly [obsDWLP_pt]. *)
  Lemma to_hom_obs {A} (m : nditprog S A) (H : progwp_mono (obsDWLP m)) :
    proj1_sig (to_hom (obsDWLP m) H) = proj1_sig (obsDWLP_pt S m).
  Proof. reflexivity. Qed.

  (* --- the equivalence [Ddwlp_mon w  ~=  Ddwlp (to_hom w H)] --- *)

  (** Membership coincides (up to swapping the two [forall]s). *)
  Lemma Ddwlp_mon_iff {A} (w : ProgWP S A) (H : progwp_mono w)
    (m : nditprog S A) :
    ordProgWP w (obsDWLP m) <-> pt_le (to_hom w H) (obsDWLP_pt S m).
  Proof.
    split.
    - intros HH post s Hp. exact (HH s post Hp).
    - intros HH s post Hp. exact (HH post s Hp).
  Qed.

  (** ...hence a carrier-preserving bijection between the two Dijkstra
      monads at corresponding indices. *)
  #[program] Definition mon_to_cat {A} (w : ProgWP S A) (H : progwp_mono w)
    (d : Ddwlp_mon w) : Ddwlp S (to_hom w H) := proj1_sig d.
  Next Obligation. intros post s Hp. exact (proj2_sig d s post Hp). Qed.

  #[program] Definition cat_to_mon {A} (w : ProgWP S A) (H : progwp_mono w)
    (d : Ddwlp S (to_hom w H)) : Ddwlp_mon w := proj1_sig d.
  Next Obligation. intros s post Hp. exact (proj2_sig d post s Hp). Qed.

  Lemma mon_to_cat_carrier {A} (w : ProgWP S A) (H : progwp_mono w)
    (d : Ddwlp_mon w) : proj1_sig (mon_to_cat w H d) = proj1_sig d.
  Proof. reflexivity. Qed.
  Lemma cat_to_mon_carrier {A} (w : ProgWP S A) (H : progwp_mono w)
    (d : Ddwlp S (to_hom w H)) : proj1_sig (cat_to_mon w H d) = proj1_sig d.
  Proof. reflexivity. Qed.

  (** Both round-trips are the identity on carriers. *)
  Lemma mon_cat_roundtrip {A} (w : ProgWP S A) (H : progwp_mono w)
    (d : Ddwlp_mon w) :
    proj1_sig (cat_to_mon w H (mon_to_cat w H d)) = proj1_sig d.
  Proof. reflexivity. Qed.
  Lemma cat_mon_roundtrip {A} (w : ProgWP S A) (H : progwp_mono w)
    (d : Ddwlp S (to_hom w H)) :
    proj1_sig (mon_to_cat w H (cat_to_mon w H d)) = proj1_sig d.
  Proof. reflexivity. Qed.

End DijkstraMonadDM4All.

(* ================================================================= *)
(** ** Specification monads, and the spec category they induce         *)
(* ================================================================= *)

(** A SPECIFICATION MONAD is a monad whose elements are specifications:
    each [M A] carries a refinement preorder, and [bind] is monotone in
    BOTH arguments.  Following the minimal presentation of
    [SpecCategory], we carry only the preorder [sm_le] and state the
    monad laws up to its symmetric part -- the induced equivalence. *)

Definition sym_part {X} (le : X -> X -> Prop) (x y : X) : Prop :=
  le x y /\ le y x.

Class SpecMonad (M : Type -> Type) :=
{
  sm_ret  : forall {A}, A -> M A ;
  sm_bind : forall {A B}, M A -> (A -> M B) -> M B ;

  sm_le : forall {A}, M A -> M A -> Prop ;
  sm_le_preorder :: forall A, PreOrder (@sm_le A) ;

  (** Monad laws, up to the equivalence induced by [sm_le]. *)
  sm_bind_ret_l : forall {A B} (a : A) (f : A -> M B),
    sym_part sm_le (sm_bind (sm_ret a) f) (f a) ;
  sm_bind_ret_r : forall {A} (m : M A),
    sym_part sm_le (sm_bind m sm_ret) m ;
  sm_bind_assoc : forall {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
    sym_part sm_le (sm_bind (sm_bind m f) g)
                   (sm_bind m (fun a => sm_bind (f a) g)) ;

  (** The [Pos]-enrichment: [bind] is monotone in both arguments. *)
  sm_bind_mono : forall {A B} (m m' : M A) (f f' : A -> M B),
    sm_le m m' -> (forall a, sm_le (f a) (f' a)) ->
    sm_le (sm_bind m f) (sm_bind m' f') ;
}.

(* ----------------------------------------------------------------- *)
(** *** The construction: a spec monad induces a spec CATEGORY         *)
(* ----------------------------------------------------------------- *)

(** Take Kleisli arrows as homs, [ret] as identity, Kleisli composition
    as composition, and order/compare them pointwise.  Every law of the
    spec category is the corresponding monad law, applied at each point:
    the category laws come from the monad laws, and the [Pos]-enrichment
    [cat_comp_mono] comes from [sm_bind_mono].  This is the sense in
    which "the spec category of a spec monad IS its Kleisli category". *)

Section SpecMonadToSpecCategory.
  Variable M : Type -> Type.
  Context {SM : SpecMonad M}.

  Definition Kl (A B : Type) : Type := A -> M B.

  #[global] Instance Category_Kl : Category Kl :=
  {|
    cat_id := fun A => @sm_ret M SM A ;
    cat_comp := fun A B C f g => fun a => sm_bind (f a) g ;
  |}.

  (** Order and hom-setoid: pointwise. *)
  Definition kl_le {A B} (f g : Kl A B) : Prop := forall a, sm_le (f a) (g a).
  Definition kl_eq {A B} (f g : Kl A B) : Prop :=
    forall a, sym_part sm_le (f a) (g a).

  Lemma kl_le_preorder {A B} : PreOrder (@kl_le A B).
  Proof.
    constructor.
    - intros f a; reflexivity.
    - intros f g h H1 H2 a; etransitivity; [ apply H1 | apply H2 ].
  Qed.

  Lemma kl_eq_iff {A B} (f g : Kl A B) :
    kl_eq f g <-> (kl_le f g /\ kl_le g f).
  Proof.
    unfold kl_eq, kl_le, sym_part; split.
    - intro H; split; intro a; apply H.
    - intros [H1 H2] a; split; [ apply H1 | apply H2 ].
  Qed.

  Lemma kl_eq_equiv {A B} : Equivalence (@kl_eq A B).
  Proof.
    constructor.
    - intros f a; split; reflexivity.
    - intros f g H a; destruct (H a); split; assumption.
    - intros f g h H1 H2 a.
      destruct (H1 a) as [P1 Q1], (H2 a) as [P2 Q2].
      split; etransitivity; eassumption.
  Qed.

  Lemma kl_eq_le {A B} (f g : Kl A B) : kl_eq f g -> kl_le f g.
  Proof. intro H; apply kl_eq_iff in H; apply H. Qed.

  (** Category laws = monad laws, pointwise. *)
  Lemma kl_comp_id_l {A B} (f : Kl A B) : kl_eq (cat_comp cat_id f) f.
  Proof. intro a. apply sm_bind_ret_l. Qed.

  Lemma kl_comp_id_r {A B} (f : Kl A B) : kl_eq (cat_comp f cat_id) f.
  Proof. intro a. apply sm_bind_ret_r. Qed.

  Lemma kl_comp_assoc {A B C D} (f : Kl A B) (g : Kl B C) (h : Kl C D) :
    kl_eq (cat_comp (cat_comp f g) h) (cat_comp f (cat_comp g h)).
  Proof. intro a. apply sm_bind_assoc. Qed.

  (** The enrichment = [sm_bind_mono], pointwise. *)
  Lemma kl_comp_mono {A B C} (f f' : Kl A B) (g g' : Kl B C) :
    kl_le f f' -> kl_le g g' -> kl_le (cat_comp f g) (cat_comp f' g').
  Proof. intros Hf Hg a. apply sm_bind_mono; [ apply Hf | apply Hg ]. Qed.

  Lemma kl_comp_proper {A B C} :
    Proper (kl_eq ==> kl_eq ==> kl_eq) (@cat_comp Kl _ A B C).
  Proof.
    intros f f' Hf g g' Hg.
    apply kl_eq_iff; apply kl_eq_iff in Hf, Hg.
    destruct Hf as [Hf1 Hf2], Hg as [Hg1 Hg2].
    split; apply kl_comp_mono; assumption.
  Qed.

  #[global] Instance SpecCategory_Kl : SpecCategory Kl :=
  {|
    cat_eq := @kl_eq ;
    cat_le := @kl_le ;
    cat_eq_equiv    := @kl_eq_equiv ;
    cat_le_preorder := @kl_le_preorder ;
    cat_comp_id_l   := @kl_comp_id_l ;
    cat_comp_id_r   := @kl_comp_id_r ;
    cat_comp_assoc  := @kl_comp_assoc ;
    cat_comp_proper := @kl_comp_proper ;
    cat_comp_mono   := @kl_comp_mono ;
    cat_eq_le       := @kl_eq_le ;
  |}.

End SpecMonadToSpecCategory.

(* ----------------------------------------------------------------- *)
(** *** Instance: the powerset spec monad, whose Kleisli spec           *)
(** ***           category is the category of RELATIONS                *)
(* ----------------------------------------------------------------- *)

(** [SetM A = A -> Prop] with subset order.  Unlike the WP transformers,
    powerset [bind] is monotone in both arguments with no healthiness
    side-condition, so this is a spec monad on the nose.  Its Kleisli
    spec category is [Pred] -- exactly the relational specifications
    that the left-adjoint (join-preserving) SP transformers correspond
    to. *)

Definition setm_ret {A} (a : A) : SetM A := fun x => x = a.
Definition setm_bind {A B} (m : SetM A) (f : A -> SetM B) : SetM B :=
  fun b => exists a, m a /\ f a b.
Definition setm_le {A} (m1 m2 : SetM A) : Prop := forall a, m1 a -> m2 a.

Lemma setm_le_preorder {A} : PreOrder (@setm_le A).
Proof.
  constructor.
  - intros m a H; exact H.
  - intros m1 m2 m3 H1 H2 a H; apply H2, H1, H.
Qed.

Lemma setm_bind_ret_l {A B} (a : A) (f : A -> SetM B) :
  sym_part setm_le (setm_bind (setm_ret a) f) (f a).
Proof.
  unfold sym_part, setm_le, setm_bind, setm_ret; split.
  - intros b [a' [Ha Hf]]. subst a'. exact Hf.
  - intros b Hf. exists a. split; [ reflexivity | exact Hf ].
Qed.

Lemma setm_bind_ret_r {A} (m : SetM A) :
  sym_part setm_le (setm_bind m setm_ret) m.
Proof.
  unfold sym_part, setm_le, setm_bind, setm_ret; split.
  - intros a [a' [Hm Heq]]. subst a. exact Hm.
  - intros a Hm. exists a. split; [ exact Hm | reflexivity ].
Qed.

Lemma setm_bind_assoc {A B C} (m : SetM A) (f : A -> SetM B) (g : B -> SetM C) :
  sym_part setm_le (setm_bind (setm_bind m f) g)
                   (setm_bind m (fun a => setm_bind (f a) g)).
Proof.
  unfold sym_part, setm_le, setm_bind; split.
  - intros c [b [[a [Hm Hf]] Hg]].
    exists a. split; [ exact Hm | exists b; split; assumption ].
  - intros c [a [Hm [b [Hf Hg]]]].
    exists b. split; [ exists a; split; assumption | exact Hg ].
Qed.

Lemma setm_bind_mono {A B} (m m' : SetM A) (f f' : A -> SetM B) :
  setm_le m m' -> (forall a, setm_le (f a) (f' a)) ->
  setm_le (setm_bind m f) (setm_bind m' f').
Proof.
  intros Hm Hf b [a [Hma Hfa]].
  exists a. split; [ apply Hm, Hma | apply Hf, Hfa ].
Qed.

#[global] Instance SpecMonad_SetM : SpecMonad SetM :=
{|
  sm_ret  := @setm_ret ;
  sm_bind := @setm_bind ;
  sm_le   := @setm_le ;
  sm_le_preorder := @setm_le_preorder ;
  sm_bind_ret_l  := @setm_bind_ret_l ;
  sm_bind_ret_r  := @setm_bind_ret_r ;
  sm_bind_assoc  := @setm_bind_assoc ;
  sm_bind_mono   := @setm_bind_mono ;
|}.

(** The induced spec category is literally the category of relations. *)
Lemma Kl_SetM_is_Pred (A B : Type) : Kl SetM A B = Pred A B.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Worked example: verifying [incr] in the spec-MONAD Dijkstra      *)
(** **                 monad [Ddwlp_mon] (the DM4All presentation)      *)
(* ================================================================= *)

(** Same program, same property as the [Ddwlp] examples above, but every
    specification is now an ELEMENT of the specification monad
    [ProgWP nat unit] rather than a morphism of [WPHom]. *)

Section DdwlpMonExample.

  (* --- Step 1: write the spec as an ELEMENT of the spec monad --------
     [ProgWP S = stateT S (optionT PureWP)], so a specification is built
     with [mkStateT]/[mkOptionT]: given the initial state [s], it says
     which postconditions it guarantees. *)
  Definition incr_spec_mon : ProgWP nat unit :=
    mkStateT (fun s => @mkOptionT PureWP _ (fun post => post (Some (tt, s + 1)))).

  (* --- Step 2: verification = inhabiting [Ddwlp_mon] -----------------
     The obligation is [ordProgWP incr_spec_mon (obsDWLP incr)], i.e.
     "everything the spec demands, the demonic WP of [incr] guarantees". *)
  #[program] Definition incr_verified_mon
    : Ddwlp_mon nat incr_spec_mon := incr.
  Next Obligation. intros s post H. exact (proj2 (incr_dwlp s post) H). Qed.

  (* --- Step 3: a weaker annotation, reached by weakening -------------
     "the final state is at least 1", again as a spec-monad element. *)
  Definition incr_ge1_mon : ProgWP nat unit :=
    mkStateT (fun s => @mkOptionT PureWP _
                (fun post => forall s', 1 <= s' -> post (Some (tt, s')))).

  Lemma incr_ge1_below_spec_mon : ordProgWP incr_ge1_mon incr_spec_mon.
  Proof. intros s post H. cbn in *. apply (H (s + 1)). lia. Qed.

  Definition incr_meets_ge1_mon : Ddwlp_mon nat incr_ge1_mon :=
    Ddwlp_mon_wkn nat incr_verified_mon incr_ge1_below_spec_mon.

  (* --- Step 4: the same verification, transported to the category ----
     [incr_spec_mon] is healthy, so it converts to a [WPHom] morphism --
     and that morphism is literally the category-side [incr_spec]. *)
  Lemma incr_spec_mon_mono : progwp_mono nat incr_spec_mon.
  Proof. intros s p q Hpq H. cbn in *. apply Hpq, H. Qed.

  Lemma incr_spec_agree :
    proj1_sig (to_hom nat incr_spec_mon incr_spec_mon_mono)
    = proj1_sig incr_spec.
  Proof. reflexivity. Qed.

  Definition incr_verified_transported
    : Ddwlp nat (to_hom nat incr_spec_mon incr_spec_mon_mono) :=
    mon_to_cat nat incr_spec_mon incr_spec_mon_mono incr_verified_mon.

End DdwlpMonExample.
