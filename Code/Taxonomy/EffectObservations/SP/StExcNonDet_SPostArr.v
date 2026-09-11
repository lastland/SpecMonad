(** * ASP/DSLP observations of [stexcnd] into the arrow-derived SP monads

    [stexcnd S = stateT S (optionT SetM)] is the exception-plus-nondeterminism
    monad of [StExcNonDet], whose outcome [None] is a RAISED EXCEPTION.  This
    file instantiates the generic adapter of [SPostArrObservation] at that
    kernel: the exception is an ordinary outcome visible to both readings —
    [obsASP] exhibits it as reachable, [obsDSLP] constrains every state that
    raises.  Both observations are monad morphisms into [ASPostArr] /
    [DSLPostArr] by the generic laws; the worked examples exercise the
    exception and [orP] programs through the generic triple layer. *)

From Coq Require Import PeanoNat.
From Coq Require Import Morphisms_Prop.
From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The outcome kernel and the observation aliases                 *)
(* ================================================================= *)

#[program] Definition stexcndKernel (S : Type)
  : @OutcomeKernel S (stexcnd S) (Monad__stexcnd S) :=
  {| kern := fun A (m : stexcnd S A) s r => StExcNonDet.outcomes S m s r |}.
Next Obligation. apply (outcomes_ret S). Qed.
Next Obligation. apply (outcomes_bind S). Qed.

Section Obs.
  Variable S : Type.

  Definition obsASP {A} (m : stexcnd S A) : ASPostArr S A :=
    SPostArrObservation.obsASP (stexcndKernel S) m.

  Definition obsDSLP {A} (m : stexcnd S A) : DSLPostArr S A :=
    SPostArrObservation.obsDSLP (stexcndKernel S) m.

  (** Applying an observation IS the corresponding reading of the outcome
      set of the computation kernel. *)
  Lemma getProgASP_obsASP {A} (m : stexcnd S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r <-> exists s, pre s /\ outcomes S m s r.
  Proof. exact (SPostArrObservation.runASP_obsASP (stexcndKernel S) m pre r). Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stexcnd S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r <-> forall s, outcomes S m s r -> pre s.
  Proof. exact (SPostArrObservation.runDSLP_obsDSLP (stexcndKernel S) m pre r). Qed.

  (** The monad morphism laws, specialized to this kernel. *)
  Theorem obsASP_ret {A} (a : A) :
    obsASP (@ret _ (Monad__stexcnd S) A a) = @ret _ (Monad_ASPostArr S) A a.
  Proof. exact (SPostArrObservation.obsASP_ret (stexcndKernel S) a). Qed.

  Theorem obsASP_bind {A B} (m : stexcnd S A) (k : A -> stexcnd S B) :
    obsASP (bindP S m k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof. exact (SPostArrObservation.obsASP_bind (stexcndKernel S) m k). Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (@ret _ (Monad__stexcnd S) A a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof. exact (SPostArrObservation.obsDSLP_ret (stexcndKernel S) a). Qed.

  Theorem obsDSLP_bind {A B} (m : stexcnd S A) (k : A -> stexcnd S B) :
    obsDSLP (bindP S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof. exact (SPostArrObservation.obsDSLP_bind (stexcndKernel S) m k). Qed.

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
(** ** The exception outcome is visible to both readings              *)
(* ================================================================= *)

(** A tiny raiser: [put 43; raise]. *)
Example raiser : stexcnd nat unit :=
  bindP nat (putP nat 43) (fun _ => raiseP nat tt).

Lemma raiser_outcomes (s : nat) r : outcomes nat raiser s r <-> r = None.
Proof.
  unfold outcomes, raiser. cbn. split; sauto limit: 200.
Qed.

(** Angelic: the exception is reachable, so it appears in the ASP reading. *)
Example raiser_may_raise : runASP (obsASP raiser) (fun _ => True) None.
Proof.
  apply getProgASP_obsASP. exists 0. split; [exact I |].
  apply raiser_outcomes. reflexivity.
Qed.

(** Demonic: every state raises, so the DSLP reading of [None] forces the
    precondition everywhere. *)
Example raiser_dslp : forall pre r,
  runDSLP (obsDSLP raiser) pre r <-> (r = None -> forall s, pre s).
Proof.
  intros pre r. rewrite getProgDSLP_obsDSLP. destruct r as [p|].
  - split.
    + intros _ Hnone. discriminate Hnone.
    + intros H s Hout. apply (proj1 (raiser_outcomes s (Some p))) in Hout.
      discriminate Hout.
  - split.
    + intros H _ s. apply H. apply (proj2 (raiser_outcomes s None)). reflexivity.
    + intros H s Hout. exact (H eq_refl s).
Qed.

(* ================================================================= *)
(** ** [progA_stexcnd] through the generic triple layer               *)
(* ================================================================= *)

(** [put 42] erases the initial state, so both branches of the [orP] are
    reachable from EVERY initial state. *)
Lemma progA_outcomes (s : nat) r :
  outcomes nat progA_stexcnd s r <-> r = Some (tt, 42) \/ r = Some (tt, 43).
Proof.
  unfold outcomes, progA_stexcnd. cbn. split; sauto limit: 200.
Qed.

(** Under, incorrectness-style: from [0] both final states are reachable. *)
Example progA_under :
  tripleASP (stexcndKernel nat) progA_stexcnd Under
    (fun s => s = 0) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  unfold tripleASP. intros r [H42 | H43].
  - exists 0. split; [reflexivity |].
    apply progA_outcomes. exact (or_introl H42).
  - exists 0. split; [reflexivity |].
    apply progA_outcomes. exact (or_intror H43).
Qed.

(** Over: every outcome of the full precondition is one of the two writes. *)
Example progA_asp_over :
  tripleASP (stexcndKernel nat) progA_stexcnd Over
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  unfold tripleASP. intros r [s [_ Hout]].
  apply progA_outcomes in Hout. exact Hout.
Qed.

(** Under: the predecessors of each outcome comprise every state, so only
    the trivial precondition holds universally. *)
Example progA_dslp_under :
  tripleDSL (stexcndKernel nat) progA_stexcnd Under
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  unfold tripleDSL. intros r Hout s _. exact I.
Qed.

(** Over: neither final state is reachable ONLY from [{0}] — each has every
    state as a predecessor. *)
Example progA_dslp_over :
  tripleDSL (stexcndKernel nat) progA_stexcnd Over
    (fun s => s = 0)
    (fun r => ~ (r = Some (tt, 42) \/ r = Some (tt, 43))).
Proof.
  unfold tripleDSL. intros r Hall Hr.
  destruct Hr as [H42 | H43].
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_introl H42))).
    discriminate.
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_intror H43))).
    discriminate.
Qed.

(* ================================================================= *)
(** ** The morphism laws compute                                     *)
(* ================================================================= *)

(** The observation of a bind chain computes by the [bind] and [ret] laws. *)
Example obs_bind_compute :
  obsASP (bindP nat progA_stexcnd (fun _ => @ret _ (Monad__stexcnd nat) unit tt)) =
  @bind _ (Monad_ASPostArr nat) unit unit (obsASP progA_stexcnd)
    (fun _ => @ret _ (Monad_ASPostArr nat) unit tt).
Proof.
  rewrite (obsASP_bind progA_stexcnd (fun _ => @ret _ (Monad__stexcnd nat) unit tt)).
  rewrite (obsASP_ret tt).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Result type independent of the state type                      *)
(* ================================================================= *)

(** A regression for parameter independence of the kernel and the
    observations: [S := nat] but [A := bool] here. *)
Definition getEven : stexcnd nat bool :=
  bindP nat (getP nat) (fun s => retP nat (Nat.even s)).

Lemma getP_outcomes (s : nat) (r : option (nat * nat)) :
  outcomes nat (getP nat) s r <-> r = Some (s, s).
Proof. unfold outcomes, getP. cbn. split; intro H; congruence. Qed.

Lemma getEven_outcomes (s : nat) (r : option (bool * nat)) :
  outcomes nat getEven s r <-> r = Some (Nat.even s, s).
Proof.
  unfold getEven.
  rewrite (outcomes_bind nat (getP nat) (fun s => retP nat (Nat.even s)) s r).
  split.
  - intros [oa [Hget Hrest]].
    apply (proj1 (getP_outcomes s oa)) in Hget. subst oa.
    apply (proj1 (outcomes_ret nat (Nat.even s) s r)). exact Hrest.
  - intros ->. exists (Some (s, s)). split.
    + apply (proj2 (getP_outcomes s (Some (s, s)))). reflexivity.
    + apply (proj2 (outcomes_ret nat (Nat.even s) s (Some (Nat.even s, s)))).
      reflexivity.
Qed.

Example getEven_under :
  tripleASP (stexcndKernel nat) getEven Under
    (fun s => s = 1) (fun r => r = Some (Nat.even 1, 1)).
Proof.
  intros r Hr. exists 1. split; [reflexivity |].
  apply getEven_outcomes. exact Hr.
Qed.
