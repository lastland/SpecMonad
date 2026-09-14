(** * ASP/DSLP observations of [stdivnd]

    [stdivnd S = stateT S (optionT SetM)] is the divergence-plus-nondeterminism
    monad of [StDivNonDet]: [None] is DIVERGENCE rather than the exception
    of [stexcnd] on the same carrier.  [divergeD] has this outcome from every state.  The
    observations [obsASP]/[obsDSLP] read the FULL outcome payload
    [unOptionT (runStateT m s)] into the arrow-derived specification monads of
    [SPostArrMonad] — divergence is an ordinary outcome, visible to both
    readings — and both are monad morphisms; the raw outcome laws are the
    computation-owned [StExcNonDet.outcomes_ret]/[outcomes_bind] (shared with
    [StExcNonDet_SPostArr], since [stdivnd] uses the same raw dictionaries)
    together with [StDivNonDet.outcomes_diverge], and they apply to this
    module's [retD]/[bindD]/[divergeD] definitionally.  Examples use the
    shared triple judgments of [SPostArrObservation]. *)

From Coq Require Import Morphisms_Prop.
From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Observations and morphism laws                                  *)
(* ================================================================= *)

Section Obs.
  Variable S : Type.

  (** The raw outcome lemmas are owned by the computation modules:
      [StExcNonDet.outcomes_ret]/[outcomes_bind] state the shared
      dictionaries of [stateT S (optionT SetM)], and [stdivnd S] IS that
      carrier with [StDivNonDet] resolving to the same dictionaries, so
      they apply to [retD]/[bindD] by definitional conversion. *)

  Definition obsASP {A} (m : stdivnd S A) : ASPostArr S A :=
    relASP (fun us r => unOptionT (runStateT m (snd us)) r).

  Definition obsDSLP {A} (m : stdivnd S A) : DSLPostArr S A :=
    asp_to_dslp (obsASP m).

  (** Applying an observation IS the corresponding reading of the raw
      outcome payload. *)
  Lemma ASP_rel_obsASP {A} (m : stdivnd S A) (s : S) r :
    ASP_rel (obsASP m) (tt, s) r <-> unOptionT (runStateT m s) r.
  Proof.
    exact (ASP_rel_relASP
             (fun us r => unOptionT (runStateT m (snd us)) r) (tt, s) r).
  Qed.

  Lemma getProgASP_obsASP {A} (m : stdivnd S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r <-> exists s, pre s /\ unOptionT (runStateT m s) r.
  Proof.
    rewrite runASP_rel. setoid_rewrite ASP_rel_obsASP. reflexivity.
  Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivnd S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r <-> forall s, unOptionT (runStateT m s) r -> pre s.
  Proof.
    unfold obsDSLP. rewrite runDSLP_rel.
    setoid_rewrite DSLP_rel_asp_to_dslp. setoid_rewrite ASP_rel_obsASP.
    reflexivity.
  Qed.

  (** The monad morphism laws. *)
  Theorem obsASP_ret {A} (a : A) :
    obsASP (retD S a) = @ret _ (Monad_ASPostArr S) A a.
  Proof.
    apply ASP_rel_ext. intros [[] s] r.
    rewrite ASP_rel_ret, ASP_rel_obsASP,
      (StExcNonDet.outcomes_ret S a s r).
    split; intro H; symmetry; exact H.
  Qed.

  Theorem obsASP_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    obsASP (bindD S m k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof.
    apply ASP_rel_ext. intros [[] s] r.
    rewrite ASP_rel_bind, ASP_rel_obsASP,
      (StExcNonDet.outcomes_bind S m k s r).
    apply ex_iff_morphism. intros [[a t]|];
      rewrite !ASP_rel_obsASP; reflexivity.
  Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (retD S a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof.
    unfold obsDSLP. rewrite obsASP_ret. apply asp_to_dslp_ret.
  Qed.

  Theorem obsDSLP_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    obsDSLP (bindD S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof.
    unfold obsDSLP. rewrite obsASP_bind.
    rewrite <- (asp_to_dslp_bind (obsASP m) (fun a => obsASP (k a))).
    reflexivity.
  Qed.

  (** ** Triples: the shared judgments at the observed arrows *)

  Definition tripleASP {A} (m : stdivnd S A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    SPostArrObservation.tripleASP (obsASP m) kind pre post.

  Definition tripleDSL {A} (m : stdivnd S A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    SPostArrObservation.tripleDSL (obsDSLP m) kind pre post.
End Obs.

Arguments obsASP {S A} m.
Arguments obsDSLP {S A} m.
Arguments ASP_rel_obsASP {S A} m s r.
Arguments getProgASP_obsASP {S A} m pre r.
Arguments getProgDSLP_obsDSLP {S A} m pre r.
Arguments obsASP_ret {S A} a.
Arguments obsASP_bind {S A B} m k.
Arguments obsDSLP_ret {S A} a.
Arguments obsDSLP_bind {S A B} m k.
Arguments tripleASP {S A} m kind pre post.
Arguments tripleDSL {S A} m kind pre post.

(* ================================================================= *)
(** ** Divergence is visible to both readings                         *)
(* ================================================================= *)

(** [divergeD]'s only outcome is the divergence token [None], from every
    state: [StDivNonDet.outcomes_diverge], used below. *)

(** Angelic: some initial state diverges exactly when [pre] is inhabited
    and the outcome looked at is the divergence token. *)
Example diverge_asp : forall (pre : nat -> Prop) r,
  runASP (obsASP (divergeD : stdivnd nat unit)) pre r <->
  r = None /\ exists s, pre s.
Proof.
  intros pre r. rewrite getProgASP_obsASP. destruct r as [p|].
  - split.
    + intros [s [Hpre Hout]].
      split; [exact (proj1 (StDivNonDet.outcomes_diverge nat s (Some p)) Hout)
              | exists s; exact Hpre].
    + intros [Hnone _]. discriminate Hnone.
  - split.
    + intros [s [Hpre Hout]]. split; [reflexivity | exists s; exact Hpre].
    + intros [_ [s Hpre]]. exists s. split; [exact Hpre |].
      apply (StDivNonDet.outcomes_diverge nat s None). reflexivity.
Qed.

(** Demonic: every state may diverge, so the reading of [None] forces [pre]
    everywhere; other outcomes are vacuous. *)
Example diverge_dslp : forall (pre : nat -> Prop) r,
  runDSLP (obsDSLP (divergeD : stdivnd nat unit)) pre r <->
  (r = None -> forall s, pre s).
Proof.
  intros pre r. rewrite getProgDSLP_obsDSLP. destruct r as [p|].
  - split.
    + intros _ Hnone. discriminate Hnone.
    + intros H s Hout.
      apply (proj1 (StDivNonDet.outcomes_diverge nat s (Some p))) in Hout.
      discriminate Hout.
  - split.
    + intros H _ s. apply H.
      apply (StDivNonDet.outcomes_diverge nat s None). reflexivity.
    + intros H s Hout. exact (H eq_refl s).
Qed.

(* ================================================================= *)
(** ** An [orD] program through the triple layer                      *)
(* ================================================================= *)

(** [progA] transposed to [stdivnd]; as in [stexcnd], [put 42] erases the
    initial state, so both branches are reachable from every state. *)
Example progA_nd : stdivnd nat unit :=
  putD nat 42 ;; s <- getD nat ;; orD (putD nat s) (putD nat (s + 1)).

Lemma progA_nd_outcomes (s : nat) r :
  unOptionT (runStateT progA_nd s) r <->
  r = Some (tt, 42) \/ r = Some (tt, 43).
Proof.
  unfold progA_nd. cbn. split; sauto limit: 200.
Qed.

(** Under, incorrectness-style: from [0] both final states are reachable. *)
Example progA_nd_under :
  tripleASP progA_nd Under
    (fun s => s = 0) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r [H42 | H43].
  - apply getProgASP_obsASP. exists 0. split.
    + reflexivity.
    + apply progA_nd_outcomes. exact (or_introl H42).
  - apply getProgASP_obsASP. exists 0. split.
    + reflexivity.
    + apply progA_nd_outcomes. exact (or_intror H43).
Qed.

(** Over: every outcome of the full precondition is one of the two writes. *)
Example progA_nd_asp_over :
  tripleASP progA_nd Over
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r Hrun.
  apply (proj1 (getProgASP_obsASP progA_nd (fun _ => True) r)) in Hrun.
  destruct Hrun as [s [_ Hout]].
  apply progA_nd_outcomes in Hout. exact Hout.
Qed.

(** Under: the predecessors of each outcome comprise every state, so only
    the trivial precondition holds universally. *)
Example progA_nd_dslp_under :
  tripleDSL progA_nd Under
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r Hout. apply getProgDSLP_obsDSLP. intros s _. exact I.
Qed.

(** Over: neither final state is reachable ONLY from [{0}] — each has every
    state as a predecessor. *)
Example progA_nd_dslp_over :
  tripleDSL progA_nd Over
    (fun s => s = 0)
    (fun r => ~ (r = Some (tt, 42) \/ r = Some (tt, 43))).
Proof.
  intros r Hall Hr.
  rewrite getProgDSLP_obsDSLP in Hall.
  destruct Hr as [H42 | H43].
  - specialize (Hall 1 (proj2 (progA_nd_outcomes 1 _) (or_introl H42))).
    discriminate.
  - specialize (Hall 1 (proj2 (progA_nd_outcomes 1 _) (or_intror H43))).
    discriminate.
Qed.

(** The morphism law computes: the observation of a bind chain is the
    arrow-side bind of the observations, with the actual monad
    dictionaries. *)
Example obs_bind_compute :
  obsASP (bindD nat (retD nat tt) (fun _ => putD nat 42)) =
  @bind _ (Monad_ASPostArr nat) unit unit (obsASP (retD nat tt))
    (fun _ => obsASP (putD nat 42)).
Proof.
  rewrite (obsASP_bind (retD nat tt) (fun _ => putD nat 42)).
  reflexivity.
Qed.
