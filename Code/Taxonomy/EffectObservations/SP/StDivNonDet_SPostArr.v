(** * ASP/DSLP observations of [stdivnd] into the arrow-derived SP monads

    [stdivnd S = stateT S (optionT SetM)] is the divergence-plus-nondeterminism
    monad of [StDivNonDet], whose outcome [None] is DIVERGENCE — unlike
    [stexcnd] on the same carrier, [divergeD] HAS the outcome [None] from
    every state, so the kernel observes the full option.  This file
    instantiates the generic adapter of [SPostArrObservation] at that kernel:
    divergence is an ordinary outcome visible to both readings — [obsASP]
    says some initial state diverges, [obsDSLP] that every state which may
    diverge satisfies the precondition.  Both observations are monad
    morphisms into [ASPostArr] / [DSLPostArr] by the generic laws; the
    worked examples exercise the divergence and [orD] programs with the
    generic triple layer. *)

From Coq Require Import Morphisms_Prop.
From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivNonDet.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The outcome kernel and the observation aliases                 *)
(* ================================================================= *)

#[program] Definition stdivndKernel (S : Type)
  : @OutcomeKernel S (stdivnd S) (Monad__stdivnd S) :=
  {| kern := fun A (m : stdivnd S A) s r => StDivNonDet.outcomes S m s r |}.
Next Obligation. apply (outcomes_ret S). Qed.
Next Obligation. apply (outcomes_bind S). Qed.

Section Obs.
  Variable S : Type.

  Definition obsASP {A} (m : stdivnd S A) : ASPostArr S A :=
    SPostArrObservation.obsASP (stdivndKernel S) m.

  Definition obsDSLP {A} (m : stdivnd S A) : DSLPostArr S A :=
    SPostArrObservation.obsDSLP (stdivndKernel S) m.

  (** Applying an observation IS the corresponding reading of the outcome
      set of the computation kernel. *)
  Lemma getProgASP_obsASP {A} (m : stdivnd S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r <-> exists s, pre s /\ outcomes S m s r.
  Proof. exact (SPostArrObservation.runASP_obsASP (stdivndKernel S) m pre r). Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivnd S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r <-> forall s, outcomes S m s r -> pre s.
  Proof. exact (SPostArrObservation.runDSLP_obsDSLP (stdivndKernel S) m pre r). Qed.

  (** The monad morphism laws, specialized to this kernel. *)
  Theorem obsASP_ret {A} (a : A) :
    obsASP (@ret _ (Monad__stdivnd S) A a) = @ret _ (Monad_ASPostArr S) A a.
  Proof. exact (SPostArrObservation.obsASP_ret (stdivndKernel S) a). Qed.

  Theorem obsASP_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    obsASP (bindD S m k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof. exact (SPostArrObservation.obsASP_bind (stdivndKernel S) m k). Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (@ret _ (Monad__stdivnd S) A a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof. exact (SPostArrObservation.obsDSLP_ret (stdivndKernel S) a). Qed.

  Theorem obsDSLP_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    obsDSLP (bindD S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof. exact (SPostArrObservation.obsDSLP_bind (stdivndKernel S) m k). Qed.

End Obs.

Arguments obsASP {S A} m.
Arguments obsDSLP {S A} m.
Arguments getProgASP_obsASP {S A} m pre r.
Arguments getProgDSLP_obsDSLP {S A} m pre r.
Arguments obsASP_ret {S A} a.
Arguments obsASP_bind {S A B} m k.
Arguments obsDSLP_ret {S A} a.
Arguments obsDSLP_bind {S A B} m k.

(* ================================================================= *)
(** ** Divergence is visible to both readings                         *)
(* ================================================================= *)

(** [divergeD] has exactly one outcome, [None], from every state. *)
Lemma diverge_outcomes (s : nat) r :
  outcomes nat (divergeD : stdivnd nat unit) s r <-> r = None.
Proof. unfold outcomes, divergeD. cbn. reflexivity. Qed.

(** Angelic: some initial state diverges exactly when [pre] is inhabited
    and the outcome looked at is the divergence token. *)
Example diverge_asp : forall (pre : nat -> Prop) r,
  runASP (obsASP (divergeD : stdivnd nat unit)) pre r <->
  r = None /\ exists s, pre s.
Proof.
  intros pre r. rewrite getProgASP_obsASP. destruct r as [p|].
  - split.
    + intros [s [Hpre Hout]].
      split; [exact (proj1 (diverge_outcomes s (Some p)) Hout) | exists s; exact Hpre].
    + intros [Hnone _]. discriminate Hnone.
  - split.
    + intros [s [Hpre Hout]]. split; [reflexivity | exists s; exact Hpre].
    + intros [_ [s Hpre]]. exists s. split; [exact Hpre |].
      apply diverge_outcomes. reflexivity.
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
    + intros H s Hout. apply (proj1 (diverge_outcomes s (Some p))) in Hout.
      discriminate Hout.
  - split.
    + intros H _ s. apply H. apply diverge_outcomes. reflexivity.
    + intros H s Hout. exact (H eq_refl s).
Qed.

(* ================================================================= *)
(** ** An [orD] program through the generic triple layer              *)
(* ================================================================= *)

(** [progA] transposed to [stdivnd]; as in [stexcnd], [put 42] erases the
    initial state, so both branches are reachable from every state. *)
Example progA_nd : stdivnd nat unit :=
  putD nat 42 ;; s <- getD nat ;; orD (putD nat s) (putD nat (s + 1)).

Lemma progA_nd_outcomes (s : nat) r :
  outcomes nat progA_nd s r <-> r = Some (tt, 42) \/ r = Some (tt, 43).
Proof.
  unfold outcomes, progA_nd. cbn. split; sauto limit: 200.
Qed.

(** Under, incorrectness-style: from [0] both final states are reachable. *)
Example progA_nd_under :
  tripleASP (stdivndKernel nat) progA_nd Under
    (fun s => s = 0) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  unfold tripleASP. intros r [H42 | H43].
  - exists 0. split; [reflexivity |].
    apply progA_nd_outcomes. exact (or_introl H42).
  - exists 0. split; [reflexivity |].
    apply progA_nd_outcomes. exact (or_intror H43).
Qed.

(** Over: every outcome of the full precondition is one of the two writes. *)
Example progA_nd_asp_over :
  tripleASP (stdivndKernel nat) progA_nd Over
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  unfold tripleASP. intros r [s [_ Hout]].
  apply progA_nd_outcomes in Hout. exact Hout.
Qed.

(** Under: the predecessors of each outcome comprise every state, so only
    the trivial precondition holds universally. *)
Example progA_nd_dslp_under :
  tripleDSL (stdivndKernel nat) progA_nd Under
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  unfold tripleDSL. intros r Hout s _. exact I.
Qed.

(** Over: neither final state is reachable ONLY from [{0}] — each has every
    state as a predecessor. *)
Example progA_nd_dslp_over :
  tripleDSL (stdivndKernel nat) progA_nd Over
    (fun s => s = 0)
    (fun r => ~ (r = Some (tt, 42) \/ r = Some (tt, 43))).
Proof.
  unfold tripleDSL. intros r Hall Hr.
  destruct Hr as [H42 | H43].
  - specialize (Hall 1 (proj2 (progA_nd_outcomes 1 _) (or_introl H42))).
    discriminate.
  - specialize (Hall 1 (proj2 (progA_nd_outcomes 1 _) (or_intror H43))).
    discriminate.
Qed.

(** The morphism law computes: the observation of a bind chain is the
    arrow-side bind of the observations. *)
Example obs_bind_compute :
  obsASP (bindD nat (retD nat tt) (fun _ => putD nat 42)) =
  @bind _ (Monad_ASPostArr nat) unit unit (obsASP (retD nat tt))
    (fun _ => obsASP (putD nat 42)).
Proof.
  rewrite (obsASP_bind (retD nat tt) (fun _ => putD nat 42)).
  reflexivity.
Qed.
