(** * Observation functions for [prog].

    Maps [prog S A] (deterministic computation via ITree) to specification
    types.

    WP observations: [obsAWP] and [obsDWP] (total) and [obsAWLP] and [obsDWLP]
    (partial, tolerates divergence) map into [ProgWP S A]. Because [prog S A] is
    deterministic, we show [obsWPCollapse] and [obsWLPCollapse] theorems that
    state [obsAWP] is equivalent to [obsDWP], [obsAWLP] is equivalent to
    [obsDWLP].

    SP observation: [obsASP] and [obsDSLP], then [obsDSP] and [obsASLP] can be
    defined based on the former two. Even though [prog S A] is deterministic, it
    is not necessarily reversible, so we cannot collapse any of the [sp]s. *)

From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy Require Import Prog WP Pred SPost WPred.
From Paco Require Import paco.
From Hammer Require Import Tactics.
From ITree Require Import ITree Eq Props.Infinite.
From ITree.Extra Require Import Dijkstra.PureITreeBasics.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

(** There is no nondeterminism in [prog], so [awp] and [dwp] are the same. We
    only define [wp] here. *)

Section ObservationWP.

  Variable S : Type.

  Definition obsAWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                        | mkOptionT o => exists r, eutt eq o (ret r) /\ post r
                        end)).

  Definition obsAWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (exists r, eutt eq o (ret r) /\ post r) \/
                                           any_infinite o
                        end)).

  Definition obsDWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (forall r, eutt eq o (ret r) -> post r) /\
                                           ~ any_infinite o
                        end)).

  Definition obsDWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o =>
                             (forall r, eutt eq o (ret r) -> post r) : Prop
                         end)).

  Theorem obsWPCollapse :
    forall {A} (m : prog S A) post s0,
      unOptionT (runStateT (obsAWP m) s0) post <->
        unOptionT (runStateT (obsDWP m) s0) post.
  Proof.
    intros. cbn. destruct (runStateT m s0) as [o] eqn:Hs. split.
    - intros [r [He Hp]]. split.
      + intros r' He'. rewrite He' in He. apply eutt_inv_Ret in He. subst. exact Hp.
      + intro Hinf. rewrite He in Hinf. exact (ret_not_div Hinf).
    - intros [Hall Hninf].
      destruct (eutt_reta_or_div o) as [[a Ha] | Hinf]; [| contradiction].
      symmetry in Ha. exists a. auto.
  Qed.

  Theorem obsWLPCollapse :
    forall {A} (m : prog S A) post s0,
      unOptionT (runStateT (obsAWLP m) s0) post <->
        unOptionT (runStateT (obsDWLP m) s0) post.
  Proof.
    intros. cbn. destruct (runStateT m s0) as [o] eqn:Hs. split.
    - intros [[r [He Hp]] | Hinf].
      + intros r' He'. rewrite He' in He. apply eutt_inv_Ret in He. subst. exact Hp.
      + intros r' He'. exfalso. rewrite He' in Hinf. exact (ret_not_div Hinf).
    - intros Hall.
      destruct (eutt_reta_or_div o) as [[a Ha] | Hinf].
      + left. symmetry in Ha. exists a. auto.
      + right. exact Hinf.
  Qed.
  
End ObservationWP.

Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.
Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.

Inductive approximationKind := | Under | Over.

(** Backward (WP) triple, defined as an *exegesis* (apply the WP
    observation to [post], compare by inclusion with [pre]), matching
    [NonDetItObservation.tripleWP].

    - [Under] reads  [pre ⊆ wp⟦m⟧(post)]  (e.g. [b ⊆ dwlp(c)]).
    - [Over]  reads  [wp⟦m⟧(post) ⊆ pre]  (e.g. [awp(c) ⊆ b]).

    This replaces the earlier [pp2wp]/[ordProgWP] (spec-as-element +
    refinement over all predicates) encoding; that encoding agrees with
    this one on [Under] but degenerates on [Over], and only the direct
    form makes the [awp ⊣ dslp] Galois connection provable. *)
Definition tripleWP {S A}
  (obs : prog S A -> ProgWP S A)
  (prog : prog S A)
  (is_correct:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
    match is_correct with
    | Under =>
        forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | Over =>
        forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.

Example progA : prog nat unit :=
  put 42 ;;
  s <- get ;;
  put s.

Example progA_WP := obsDWP progA.

(** [progA] deterministically converges to [(tt, 42)] from any initial
    state. *)
Lemma progA_run :
  forall s, eutt eq (unOptionT (runStateT progA s)) (Ret (Some (tt, 42))).
Proof.
  intro s. unfold progA. cbn.
  repeat (setoid_rewrite bind_ret_l; cbn).
  reflexivity.
Qed.

Theorem progA_WP_all :
  forall s, unOptionT (runStateT progA_WP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end).
Proof.
  intro s. pose proof (progA_run s) as Hrun.
  unfold progA_WP, obsDWP. cbn [runStateT unOptionT].
  destruct (runStateT progA s) as [o] eqn:E. cbn in Hrun.
  split.
  - intros r Hr. rewrite Hrun in Hr. apply eutt_inv_Ret in Hr. subst r. reflexivity.
  - intro Hinf. rewrite Hrun in Hinf. exact (ret_not_div Hinf).
Qed.

Theorem progA_WP_all_triple :
  tripleWP obsDWP progA Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s _.
  pose proof (progA_run s) as Hrun.
  unfold obsDWP. cbn [runStateT unOptionT].
  destruct (runStateT progA s) as [o] eqn:E. cbn in Hrun.
  split.
  - intros r Hr. rewrite Hrun in Hr. apply eutt_inv_Ret in Hr. subst r.
    cbn. auto with arith.
  - intro Hinf. rewrite Hrun in Hinf. exact (ret_not_div Hinf).
Qed.

Theorem progA_WP_not43 :
  not (forall s, unOptionT (runStateT progA_WP s)
                   (fun r : option (unit * nat) =>
                      match r with
                      | Some (_, s) => s = 43
                      | None => False
                      end)).
Proof.
  intro H. specialize (H 0). pose proof (progA_run 0) as Hrun.
  unfold progA_WP, obsDWP in H. cbn [runStateT unOptionT] in H.
  destruct (runStateT progA 0) as [o] eqn:E. cbn in Hrun.
  destruct H as [Hall _].
  specialize (Hall (Some (tt, 42)) Hrun). cbn in Hall. discriminate.
Qed.

(** A [Correct] triple fails exactly when the postcondition excludes a
    reachable outcome: [progA] reaches state [42], which violates [s = 43]. *)
Theorem progA_WP_not43_triple :
  not (tripleWP obsDWP progA Under
      (fun _ => True)
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 43
        | None => False
        end)).
Proof.
  unfold tripleWP. intro H.
  specialize (H 0 I). pose proof (progA_run 0) as Hrun.
  unfold obsDWP in H. cbn [runStateT unOptionT] in H.
  destruct (runStateT progA 0) as [o] eqn:E. cbn in Hrun.
  destruct H as [Hall _].
  specialize (Hall (Some (tt, 42)) Hrun). cbn in Hall. discriminate.
Qed.

(*
monad trans:
(pre : Prop) -> (A -> Prop / pre)

S -> (pre : Prop) -> (A * S -> Prop / pre)

arrow trans:                  
(A -> Prop) -> B -> Prop

S -> (A -> Prop) -> S * B -> Prop     <-- monad trans                    

(S * A -> Prop) -> S * B -> Prop      <-- arrow trans
                
(S * unit -> Prop) -> (A * S -> Prop) <-- specialize
*)
                  
(* ================================================================= *)
(** ** SP observations                                                *)
(* ================================================================= *)

Section ObservationSP.

  Variable S : Type.

  (** [sp]s do not collapse under nondeterminism. They only collapse when
      programs are reversible.

      TODO: Question: Is there a type that we can use to represent reversible
      definitions? *)

  (** Reachability relation for a deterministic [prog]: an initial state
      [s] reaches outcome [r] iff the computation converges to [ret r]. *)
  Definition obsRel {A} (m : prog S A)
    : Pred S (option (A * S)) :=
    fun s r => eutt eq (unOptionT (runStateT m s)) (ret r).

  (** The four SP transformers are readings of the reachability relation
      [obsRel] (no [ASPostArr]/[SPRecord]): [asp]/[dslp]/[spDSP]/[spASLP]
      from [SPost.v]. *)
  Definition obsASP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := asp (obsRel m).
  Definition obsDSLP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := dslp (obsRel m).
  Definition obsDSP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := fun pre r => asp (obsRel m) pre r /\ dslp (obsRel m) pre r.
  Definition obsASLP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := fun pre r => asp (obsRel m) pre r \/ dslp (obsRel m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  Theorem obsDSP_sub_obsASP {A} (m : prog S A) pre r :
    obsDSP m pre r -> obsASP m pre r.
  Proof. intros [H _]. exact H. Qed.

  Theorem obsDSP_sub_obsDSLP {A} (m : prog S A) pre r :
    obsDSP m pre r -> obsDSLP m pre r.
  Proof. intros [_ H]. exact H. Qed.

  Theorem obsASP_sub_obsASLP {A} (m : prog S A) pre r :
    obsASP m pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem obsDSLP_sub_obsASLP {A} (m : prog S A) pre r :
    obsDSLP m pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : prog S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP. symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : prog S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP. symmetry. apply aslp_asp_dslp.
  Qed.

End ObservationSP.

Arguments obsRel {_} {_}.
Arguments obsASP {_} {_}.
Arguments obsASLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsDSLP {_} {_}.

(* ================================================================= *)
(** ** SP observation into [ProgWPred]                                *)
(* ================================================================= *)

(** Alternative strongest-postcondition observations that land directly in
    the set-monad spec type [ProgWPred S A = S -> option (A * S) -> Prop],
    rather than the [SPRecord]/[ASPostArr] arrow encoding above.

    Unlike [ProgWP] (a [PureWP]-based predicate transformer), [ProgWPred]
    has no precondition slot: it maps a state directly to a postcondition
    predicate over outcomes.  We therefore bake in the point precondition
    [pre := eq (tt, s)] determined by the initial state [s].  Specializing
    the four predicate transformers of [SPost.v] to this singleton [pre]
    gives:

    - [asp]  R (eq (tt,s)) o  =  R (tt,s) o
    - [dslp] R (eq (tt,s)) o  =  forall sigma, R sigma o -> sigma = (tt,s)
    - [dsp]  R (eq (tt,s)) o  =  (exists sigma, R sigma o)
                                 /\ (forall sigma, R sigma o -> sigma = (tt,s))
    - [aslp] R (eq (tt,s)) o  =  R (tt,s) o \/ ~ (exists sigma, R sigma o)

    where [R = obsRel m] is the deterministic reachability relation.

    Placed in a module to avoid a name clash with the [ASPostArr]-valued
    observations; to use one at top level, refer to it as e.g.
    [WPredObs.obsASP]. *)

Module WPredObs.

  Section ObservationWPred.

    Variable S : Type.

    (** [(tt, s)] reaches outcome [o] iff the deterministic computation
        converges to [ret o] — the same reachability relation as [obsRel],
        but packaged as a [ProgWPred] value.  This is [asp] specialized to
        the point precondition [eq (tt, s)]. *)
    Definition obsASP {A} (m : prog S A) : ProgWPred S A :=
      mkStateT
        (fun s => mkOptionT
                 (fun o => eutt eq (unOptionT (runStateT m s)) (ret o))).

    (** [dslp] specialized to [eq (tt, s)]: [o] is observed only if every
        initial state reaching [o] is exactly [(tt, s)]. *)
    Definition obsDSLP {A} (m : prog S A) : ProgWPred S A :=
      mkStateT
        (fun s => @mkOptionT WPred (A * S)
                 (fun o => forall sigma, obsRel m sigma o -> sigma = s)).

    (** [dsp] specialized to [eq (tt, s)]: [o] is reachable, and only from
        [(tt, s)].  Equivalently [obsASP m] conjoined with [obsDSLP m]. *)
    Definition obsDSP {A} (m : prog S A) : ProgWPred S A :=
      mkStateT
        (fun s => @mkOptionT WPred (A * S)
                 (fun o => (exists sigma, obsRel m sigma o) /\
                           (forall sigma, obsRel m sigma o -> sigma = s))).

    (** [aslp] specialized to [eq (tt, s)]: [o] is reached from [(tt, s)], or
        else [o] is unreachable from any state.  Equivalently [obsASP m]
        disjoined with [obsDSLP m]. *)
    Definition obsASLP {A} (m : prog S A) : ProgWPred S A :=
      mkStateT
        (fun s => @mkOptionT WPred (A * S)
                 (fun o => obsRel m s o \/
                           ~ (exists sigma, obsRel m sigma o))).
  End ObservationWPred.

  Arguments obsASP {_} {_}.
  Arguments obsDSLP {_} {_}.
  Arguments obsDSP {_} {_}.
  Arguments obsASLP {_} {_}.

  Section SPTriple.
  
  (** The precondition gates the *initial state*: [ordProgSP pre m1 m2]
      only compares the observations at states satisfying [pre].  This
      matches the way [pp2wp] uses [pre] as a vacuity guard on the small
      element (see [gc_asp_dwlp]), unlike a [pre s0 /\ post r] conjunct on
      the output, which would force every reachable state to satisfy [pre]. *)
  Definition pp2sp {S A} (post : option (A * S) -> Prop) : ProgWPred S A :=
    mkStateT (fun _ => @mkOptionT WPred _ (fun r => post r)).

  Definition ordProgSP {S A} (pre : S -> Prop) (m1 m2 : ProgWPred S A) : Prop :=
    forall s r, pre s -> unOptionT (runStateT m1 s) r -> unOptionT (runStateT m2 s) r.

  Definition tripleSP {S A}
    (obs : prog S A -> ProgWPred S A)
    (prog : prog S A)
    (is_correct:approximationKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match is_correct with
    | Under =>
        (** Incorrectness / under-approximation: every [post] outcome is
            reachable from *some* [pre] state.  Existential over initial
            states — the dual of the universal [Over] case.  (A universal
            [ordProgSP pre (pp2sp post) (obs prog)] would wrongly demand
            every [pre] state reach every [post] outcome.) *)
        forall r, post r ->
          exists s, pre s /\ unOptionT (runStateT (obs prog) s) r
    | Over =>
        ordProgSP pre (obs prog) (pp2sp post)
    end.

  Example progA_ASP := obsASP progA.
  
  Theorem progA_all :
    forall s (r : option (unit * nat)),
      unOptionT (runStateT progA_ASP s) r ->
      match r with
      | Some (_, s') => s' = 42
      | None => False
      end.
  Proof.
    intros s r H.
    unfold progA_ASP, obsASP in H. cbn [runStateT unOptionT] in H.
    rewrite (progA_run s) in H.
    apply eutt_inv_Ret in H. subst r. reflexivity.
  Qed.

  Theorem progA_all_triple :
    tripleSP obsASP progA Over
      (fun _ => True)
      (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
  Proof.
    unfold tripleSP, ordProgSP. intros s r _ H.
    unfold obsASP in H. cbn [runStateT unOptionT] in H.
    rewrite (progA_run s) in H. apply eutt_inv_Ret in H. subst r.
    unfold pp2sp. cbn [runStateT unOptionT]. cbn. auto with arith.
  Qed.

  Definition example_state : prog (nat * nat * nat) unit :=
    s <- get ;;
    let '(x, y, _) := s in
    if Nat.even x then
      if negb (Nat.even y) then put (x, y, 42) else ret tt
    else ret tt.

  (** From a state with [x] even and [y] odd, [example_state] sets the
      third component to [42] and leaves [x], [y] unchanged. *)
  Lemma example_run : forall x y z0,
    Nat.even x = true -> negb (Nat.even y) = true ->
    eutt eq (unOptionT (runStateT example_state (x, y, z0)))
            (Ret (Some (tt, (x, y, 42)))).
  Proof.
    intros x y z0 Hx Hy. unfold example_state. cbn.
    setoid_rewrite bind_ret_l. cbn. rewrite Hx, Hy. cbn.
    repeat (setoid_rewrite bind_ret_l; cbn). reflexivity.
  Qed.

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
    unfold tripleSP. intros r Hpost.
    destruct r as [[u [[x y] z]] |]; [| contradiction]. destruct u.
    cbn in Hpost. destruct Hpost as [Hz [Hx Hy]]. subst z.
    exists (x, y, 11). split.
    - reflexivity.
    - unfold obsASP. cbn [runStateT unOptionT].
      apply example_run; assumption.
  Qed.

  Variable S : Type.
  
  (** Galois connection (sp ⊣ wlp): with the precondition gating the
      initial state, the demonic-WLP under-approximation and the
      angelic-SP over-approximation coincide.  Both unfold to
      [forall s r, pre s -> R s r -> post r], where
      [R s r := unOptionT (runStateT m s) ≈ ret r]. *)
  Theorem gc_asp_dwlp :
    forall A (m : prog S A) pre post,
      tripleWP obsDWLP m Under pre post <-> tripleSP obsASP m Over pre post.
  Proof.
    intros A m pre post.
    unfold tripleWP, tripleSP, ordProgSP. split.
    - (* WP-Under -> SP-Over *)
      intros HWP s r Hpre Hobs.
      unfold obsASP in Hobs. cbn [runStateT unOptionT] in Hobs.
      unfold pp2sp. cbn [runStateT unOptionT].
      specialize (HWP s Hpre). unfold obsDWLP in HWP.
      cbn [runStateT unOptionT] in HWP.
      destruct (runStateT m s) as [o] eqn:E. cbn in Hobs, HWP.
      apply (HWP r Hobs).
    - (* SP-Over -> WP-Under *)
      intros HSP s Hpre. unfold obsDWLP. cbn [runStateT unOptionT].
      destruct (runStateT m s) as [o] eqn:E.
      intros r Hr. apply (HSP s r Hpre).
      unfold obsASP. cbn [runStateT unOptionT]. rewrite E. cbn. exact Hr.
  Qed.

  (** Unfolding lemma for the angelic-WP observation: [obsAWP m] applied
      to [post] at [s] says some reachable outcome of [m] from [s] satisfies
      [post]. *)
  Lemma obsAWP_unfold : forall A (m : prog S A) s post,
    unOptionT (runStateT (obsAWP m) s) post <->
    exists r, eutt eq (unOptionT (runStateT m s)) (ret r) /\ post r.
  Proof.
    intros. unfold obsAWP. cbn [runStateT unOptionT].
    destruct (runStateT m s) as [o]. cbn. reflexivity.
  Qed.

  (** Galois connection (awp ⊣ dslp), the Zhang–Kaminski connection
      [awp⟦m⟧(c) ⊆ b  iff  c ⊆ dslp⟦m⟧(b)] (Verscht & Kaminski, Fig. 5).

      With the now-direct [tripleWP], the left-hand side is exactly
      [tripleWP obsAWP m Over pre post] (i.e. [awp(post) ⊆ pre]); the
      right-hand side is [post ⊆ dslp(pre)], with [dslp pre r := forall s,
      R s r -> pre s] and [R s r := runStateT m s ≈ ret r].  Both unfold
      to [forall s r, R s r -> post r -> pre s].

      (The point-based [WPredObs.obsDSLP] bakes in [eq (tt,s)] and cannot
      represent [dslp(pre)] for a general [pre], so the RHS is stated
      relationally rather than as a [tripleSP].  The fully triple-based
      form [tripleWP obsAWP Incorrect <-> tripleSP obsDSLP Incorrect] lives
      in [NonDetItObservation.awp_dslp], whose SP observation is the
      precondition-taking [DSLPostArr].) *)
  Theorem gc_awp_dslp :
    forall A (m : prog S A) (pre : S -> Prop) (post : option (A * S) -> Prop),
      tripleWP obsAWP m Over pre post
      <->
      (forall r s, eutt eq (unOptionT (runStateT m s)) (ret r) -> post r -> pre s).
  Proof.
    intros A m pre post. unfold tripleWP. split.
    - intros HL r s Hreach Hpost. apply HL. apply obsAWP_unfold.
      exists r. split; assumption.
    - intros HR s Hawp. apply obsAWP_unfold in Hawp.
      destruct Hawp as [r [Hreach Hpost]]. exact (HR r s Hreach Hpost).
  Qed.
    
  End SPTriple.
    
End WPredObs.
