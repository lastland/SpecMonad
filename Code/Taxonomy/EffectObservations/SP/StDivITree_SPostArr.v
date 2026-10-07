(** * Arrow-derived ASP/DSLP observations of [stdivitree].

    The observations record terminating returns, including exceptions
    ([None]); divergence has no visible outcome.  The examples distinguish
    angelic and demonic predecessor readings even for deterministic programs. *)

From ITree Require Import ITree Basics.Monad Eq.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivITree.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Observations, readings, and morphism laws                       *)
(* ================================================================= *)

Section Obs.

  Variable S : Type.

  Definition obsASP {A} (m : stdivitree S A) : ASPostArr S A :=
    relASP (fun us r => eutt eq (unOptionT (runStateT m (snd us))) (Ret r)).

  Definition obsDSLP {A} (m : stdivitree S A) : DSLPostArr S A :=
    asp_to_dslp (obsASP m).

  Lemma getProgASP_obsASP {A} (m : stdivitree S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r <->
    exists s, pre s /\ eutt eq (unOptionT (runStateT m s)) (Ret r).
  Proof.
    rewrite runASP_rel. unfold obsASP. setoid_rewrite ASP_rel_relASP.
    reflexivity.
  Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivitree S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r <->
    forall s, eutt eq (unOptionT (runStateT m s)) (Ret r) -> pre s.
  Proof.
    rewrite runDSLP_rel. unfold obsDSLP, obsASP.
    setoid_rewrite DSLP_rel_asp_to_dslp. setoid_rewrite ASP_rel_relASP.
    reflexivity.
  Qed.

  Theorem obsASP_ret {A} (a : A) :
    obsASP (retP S a) = @ret _ (Monad_ASPostArr S) A a.
  Proof.
    apply ASP_rel_ext. intros [[] s] r.
    unfold obsASP. rewrite ASP_rel_relASP, ASP_rel_ret. cbn.
    split; [apply eutt_inv_Ret | intros ->; reflexivity].
  Qed.

  Local Lemma outcomes_bind {A B} (m : stdivitree S A)
      (k : A -> stdivitree S B) s r :
    eutt eq (unOptionT (runStateT (bindP S m k) s)) (Ret r) <->
    exists om, eutt eq (unOptionT (runStateT m s)) (Ret om) /\
      match om with
      | Some (a, t) => eutt eq (unOptionT (runStateT (k a) t)) (Ret r)
      | None => r = None
      end.
  Proof.
    cbn. split.
    - intro H. apply eutt_inv_bind_ret in H.
      destruct H as [om [Hm Hk]]. exists om. split; [exact Hm |].
      destruct om as [[a t]|]; [exact Hk |].
      apply eutt_inv_Ret in Hk. symmetry. exact Hk.
    - intros [om [Hm Hk]]. rewrite Hm.
      etransitivity; [apply eq_sub_eutt, ITree.Eq.Eqit.bind_ret_l |].
      destruct om as [[a t]|]; [exact Hk |].
      subst r. reflexivity.
  Qed.

  Theorem obsASP_bind {A B} (m : stdivitree S A) (k : A -> stdivitree S B) :
    obsASP (bindP S m k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof.
    apply ASP_rel_ext. intros [[] s] r. rewrite ASP_rel_bind.
    unfold obsASP. rewrite ASP_rel_relASP, outcomes_bind.
    setoid_rewrite ASP_rel_relASP.
    split; intros [om [Hm Hk]]; exists om; split; try exact Hm;
      destruct om as [[a t]|]; cbv beta iota in *;
      try rewrite ASP_rel_relASP in *; exact Hk.
  Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (retP S a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof. unfold obsDSLP. rewrite obsASP_ret. apply asp_to_dslp_ret. Qed.

  Theorem obsDSLP_bind {A B} (m : stdivitree S A) (k : A -> stdivitree S B) :
    obsDSLP (bindP S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof. unfold obsDSLP. rewrite obsASP_bind. apply asp_to_dslp_bind. Qed.

  Definition tripleASP {A} (m : stdivitree S A) kind pre post : Prop :=
    SPostArrObservation.tripleASP (obsASP m) kind pre post.

  Definition tripleDSL {A} (m : stdivitree S A) kind pre post : Prop :=
    SPostArrObservation.tripleDSL (obsDSLP m) kind pre post.

End Obs.

(* ================================================================= *)
(** ** Worked examples (S := nat)                                      *)
(* ================================================================= *)

(** [progA_stdivitree] ([put 42; get; put s]) converges to [(tt, 42)] from
    every initial state, so its outcome relation is a constant function. *)
Lemma progA_itree_outcomes : forall s r,
  eutt eq (unOptionT (runStateT progA_stdivitree s)) (Ret r) <->
  r = Some (tt, 42).
Proof.
  intros s r.
  assert (Hrun : eutt eq (unOptionT (runStateT progA_stdivitree s))
                     (Ret (Some (tt, 42)))).
  { unfold progA_stdivitree. cbn.
    repeat (setoid_rewrite bind_ret_l; cbn).
    reflexivity. }
  rewrite Hrun.
  split.
  - intro H. apply eutt_inv_Ret in H. congruence.
  - intro H. rewrite H. reflexivity.
Qed.

(** Under (incorrectness-style): the unique outcome is reachable. *)
Example progA_itree_under :
  tripleASP nat progA_stdivitree Under
    (fun _ => True) (fun r => r = Some (tt, 42)).
Proof.
  intros r Hr. apply getProgASP_obsASP. exists 0. split; [exact I |].
  apply (proj2 (progA_itree_outcomes 0 r)). exact Hr.
Qed.

(** The two readings of the same deterministic outcome: angelic asks for
    SOME predecessor in [pre], demonic for EVERY predecessor. *)
Lemma progA_itree_runASP : forall pre r,
  runASP (obsASP nat progA_stdivitree) pre r
  <-> (r = Some (tt, 42) /\ exists s, pre s).
Proof.
  intros pre r. rewrite getProgASP_obsASP.
  setoid_rewrite progA_itree_outcomes.
  split.
  - intros [s [Hs Hr]]. split; [exact Hr | exists s; exact Hs].
  - intros [Hr [s Hs]]. exists s. split; [exact Hs | exact Hr].
Qed.

Lemma progA_itree_runDSLP : forall pre r,
  runDSLP (obsDSLP nat progA_stdivitree) pre r
  <-> (r = Some (tt, 42) -> forall s, pre s).
Proof.
  intros pre r. rewrite getProgDSLP_obsDSLP.
  setoid_rewrite progA_itree_outcomes.
  split.
  - intros H Hr s. apply H; exact Hr.
  - intros H s Hr. apply H; exact Hr.
Qed.

(** Determinism does NOT collapse the readings.  At [pre := {0}] the
    reachable outcome [(tt, 42)] passes the angelic reading (state [0] is
    a predecessor) and fails the demonic one (state [1] is another). *)
Example progA_itree_asp_vs_dslp_pre0 :
  runASP (obsASP nat progA_stdivitree) (fun s => s = 0) (Some (tt, 42))
  /\ ~ runDSLP (obsDSLP nat progA_stdivitree) (fun s => s = 0) (Some (tt, 42)).
Proof.
  split.
  - apply (proj2 (progA_itree_runASP (fun s => s = 0) (Some (tt, 42)))).
    split; [reflexivity | exists 0; reflexivity].
  - intros H.
    assert (Hpre : forall s : nat, s = 0)
      by exact (proj1 (progA_itree_runDSLP (fun s => s = 0) (Some (tt, 42))) H
                  eq_refl).
    discriminate (Hpre 1).
Qed.

(** An outcome NO state reaches: at the full precondition the angelic
    reading of it is False (no predecessor at all) while the demonic one
    is True (its predecessor condition is vacuous). *)
Example progA_itree_unreachable :
  ~ runASP (obsASP nat progA_stdivitree) (fun _ => True) (Some (tt, 43))
  /\ runDSLP (obsDSLP nat progA_stdivitree) (fun _ => True) (Some (tt, 43)).
Proof.
  split.
  - intros H.
    destruct (proj1 (progA_itree_runASP (fun _ => True) (Some (tt, 43))) H)
      as [Heq _].
    discriminate Heq.
  - apply (proj2 (progA_itree_runDSLP (fun _ => True) (Some (tt, 43)))).
    intro H. discriminate H.
Qed.

(* ================================================================= *)
(** ** A many-to-one overwrite: DSLP Over at [{0}] excludes the image   *)
(* ================================================================= *)

(** [overwrite] ([get ;; put 0]) reaches [(tt, 0)] from EVERY state: the
    image of [{0}] is [(tt, 0)], but the predecessor set of [(tt, 0)] is
    the full state space. *)
Definition overwrite : stdivitree nat unit :=
  bindP nat (getP nat) (fun s => putP nat 0).

Lemma overwrite_outcomes : forall s r,
  eutt eq (unOptionT (runStateT overwrite s)) (Ret r) <-> r = Some (tt, 0).
Proof.
  intros s r.
  assert (Hrun : eutt eq (unOptionT (runStateT overwrite s))
                     (Ret (Some (tt, 0)))).
  { unfold overwrite. cbn.
    setoid_rewrite bind_ret_l. cbn. reflexivity. }
  rewrite Hrun.
  split.
  - intro H. apply eutt_inv_Ret in H. congruence.
  - intro H. rewrite H. reflexivity.
Qed.

(** Angelic Under at [pre := {0}]: the overwrite outcome is reachable. *)
Example overwrite_under :
  tripleASP nat overwrite Under
    (fun s => s = 0) (fun r => r = Some (tt, 0)).
Proof.
  intros r Hr. apply getProgASP_obsASP. exists 0. split; [reflexivity |].
  apply (proj2 (overwrite_outcomes 0 r)). exact Hr.
Qed.

(** Demonic Over at the same [pre := {0}]: every state reaches [(tt, 0)],
    so the demonic premise fails exactly on the image and the strongest
    post lies OUTSIDE it — the opposite of the angelic Under triple
    above at the same precondition. *)
Example overwrite_dslp_over :
  tripleDSL nat overwrite Over
    (fun s => s = 0) (fun r => r <> Some (tt, 0)).
Proof.
  intros r Hall Hr. subst r.
  rewrite getProgDSLP_obsDSLP in Hall.
  assert (H10 : 1 = 0)
    by exact (Hall 1 (proj2 (overwrite_outcomes 1 (Some (tt, 0)))
                            (eq_refl _))).
  discriminate H10.
Qed.

(* ================================================================= *)
(** ** [obsASP_bind] compute demo                                      *)
(* ================================================================= *)

(** The morphism law turns the observation of a bind into the arrow-side
    bind, which the evaluators then compute on concrete witnesses. *)
Example obsASP_bind_compute :
  runASP (obsASP nat (bindP nat (retP nat tt) (fun _ => putP nat 42)))
         (fun s => s = 0) (Some (tt, 42)).
Proof.
  rewrite obsASP_bind, runASP_bind.
  exists 0, (Some (tt, 0)). split; [reflexivity | split].
  - rewrite obsASP_ret, ASP_rel_ret. reflexivity.
  - unfold obsASP. rewrite ASP_rel_relASP. reflexivity.
Qed.
