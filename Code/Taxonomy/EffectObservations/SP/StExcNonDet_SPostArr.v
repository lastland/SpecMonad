(** * ASP/DSLP observations of [stexcnd]

    [stexcnd S = stateT S (optionT SetM)] is the exception-plus-nondeterminism
    monad of [StExcNonDet]: outcome [None] is a RAISED EXCEPTION.  The
    observations [obsASP]/[obsDSLP] read the outcome payload
    [unOptionT (runStateT m s)] into the arrow-derived specification monads of
    [SPostArrMonad] — the exception is an ordinary outcome, visible to both
    readings — and both are monad morphisms; the raw outcome normalization is
    shared with [StDivNonDet_SPostArr] in [RawStOpt_SPostArr], which applies
    to this module's [retP]/[bindP] definitionally.  Examples use the shared
    triple judgments of [SPostArrObservation]. *)

From Coq Require Import PeanoNat.
From Coq Require Import Morphisms_Prop.
From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import RawStOpt_SPostArr.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Observations and morphism laws                                  *)
(* ================================================================= *)

Section Obs.
  Variable S : Type.

  (** The raw outcome lemmas live in [RawStOpt_SPostArr]: [stexcnd S] IS
      [stateT S (optionT SetM)] and [StExcNonDet] resolves to the
      dictionaries stated there, so they apply to [retP]/[bindP] by
      definitional conversion. *)

  Definition obsASP {A} (m : stexcnd S A) : ASPostArr S A :=
    relASP (fun us r => unOptionT (runStateT m (snd us)) r).

  Definition obsDSLP {A} (m : stexcnd S A) : DSLPostArr S A :=
    asp_to_dslp (obsASP m).

  (** Applying an observation IS the corresponding reading of the raw
      outcome payload. *)
  Lemma ASP_rel_obsASP {A} (m : stexcnd S A) (s : S) r :
    ASP_rel (obsASP m) (tt, s) r <-> unOptionT (runStateT m s) r.
  Proof.
    exact (ASP_rel_relASP
             (fun us r => unOptionT (runStateT m (snd us)) r) (tt, s) r).
  Qed.

  Lemma getProgASP_obsASP {A} (m : stexcnd S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r <-> exists s, pre s /\ unOptionT (runStateT m s) r.
  Proof.
    rewrite runASP_rel. setoid_rewrite ASP_rel_obsASP. reflexivity.
  Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stexcnd S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r <-> forall s, unOptionT (runStateT m s) r -> pre s.
  Proof.
    unfold obsDSLP. rewrite runDSLP_rel.
    setoid_rewrite DSLP_rel_asp_to_dslp. setoid_rewrite ASP_rel_obsASP.
    reflexivity.
  Qed.

  (** The monad morphism laws. *)
  Theorem obsASP_ret {A} (a : A) :
    obsASP (retP S a) = @ret _ (Monad_ASPostArr S) A a.
  Proof.
    apply ASP_rel_ext. intros [[] s] r.
    rewrite ASP_rel_ret, ASP_rel_obsASP,
      (RawStOpt_SPostArr.outcomes_ret S a s r).
    split; intro H; symmetry; exact H.
  Qed.

  Theorem obsASP_bind {A B} (m : stexcnd S A) (k : A -> stexcnd S B) :
    obsASP (bindP S m k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof.
    apply ASP_rel_ext. intros [[] s] r.
    rewrite ASP_rel_bind, ASP_rel_obsASP,
      (RawStOpt_SPostArr.outcomes_bind S m k s r).
    apply ex_iff_morphism. intros [[a t]|];
      rewrite !ASP_rel_obsASP; reflexivity.
  Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (retP S a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof.
    unfold obsDSLP. rewrite obsASP_ret. apply asp_to_dslp_ret.
  Qed.

  Theorem obsDSLP_bind {A B} (m : stexcnd S A) (k : A -> stexcnd S B) :
    obsDSLP (bindP S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof.
    unfold obsDSLP. rewrite obsASP_bind.
    rewrite <- (asp_to_dslp_bind (obsASP m) (fun a => obsASP (k a))).
    reflexivity.
  Qed.

  (** ** Triples: the shared judgments at the observed arrows *)

  Definition tripleASP {A} (m : stexcnd S A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    SPostArrObservation.tripleASP (obsASP m) kind pre post.

  Definition tripleDSL {A} (m : stexcnd S A) (kind : approxKind)
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
(** ** The exception outcome is visible to both readings              *)
(* ================================================================= *)

(** A tiny raiser: [put 43; raise]. *)
Example raiser : stexcnd nat unit :=
  bindP nat (putP nat 43) (fun _ => raiseP nat tt).

Lemma raiser_outcomes (s : nat) r :
  unOptionT (runStateT raiser s) r <-> r = None.
Proof.
  unfold raiser. cbn. split; sauto limit: 200.
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
(** ** [progA_stexcnd] through the triple layer                        *)
(* ================================================================= *)

(** [put 42] erases the initial state, so both branches of the [orP] are
    reachable from EVERY initial state. *)
Lemma progA_outcomes (s : nat) r :
  unOptionT (runStateT progA_stexcnd s) r <->
  r = Some (tt, 42) \/ r = Some (tt, 43).
Proof.
  unfold progA_stexcnd. cbn. split; sauto limit: 200.
Qed.

(** Under, incorrectness-style: from [0] both final states are reachable. *)
Example progA_under :
  tripleASP progA_stexcnd Under
    (fun s => s = 0) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r [H42 | H43].
  - apply getProgASP_obsASP. exists 0. split.
    + reflexivity.
    + apply progA_outcomes. exact (or_introl H42).
  - apply getProgASP_obsASP. exists 0. split.
    + reflexivity.
    + apply progA_outcomes. exact (or_intror H43).
Qed.

(** Over: every outcome of the full precondition is one of the two writes. *)
Example progA_asp_over :
  tripleASP progA_stexcnd Over
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r Hrun.
  apply (proj1 (getProgASP_obsASP progA_stexcnd (fun _ => True) r)) in Hrun.
  destruct Hrun as [s [_ Hout]].
  apply progA_outcomes in Hout. exact Hout.
Qed.

(** Under: the predecessors of each outcome comprise every state, so only
    the trivial precondition holds universally. *)
Example progA_dslp_under :
  tripleDSL progA_stexcnd Under
    (fun _ => True) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r Hout. apply getProgDSLP_obsDSLP. intros s _. exact I.
Qed.

(** Over: neither final state is reachable ONLY from [{0}] — each has every
    state as a predecessor. *)
Example progA_dslp_over :
  tripleDSL progA_stexcnd Over
    (fun s => s = 0)
    (fun r => ~ (r = Some (tt, 42) \/ r = Some (tt, 43))).
Proof.
  intros r Hall Hr.
  rewrite getProgDSLP_obsDSLP in Hall.
  destruct Hr as [H42 | H43].
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_introl H42))).
    discriminate.
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_intror H43))).
    discriminate.
Qed.

(* ================================================================= *)
(** ** The morphism laws compute                                     *)
(* ================================================================= *)

(** The observation of a bind chain computes by the [bind] and [ret] laws,
    with the actual monad dictionaries. *)
Example obs_bind_compute :
  obsASP (bindP nat progA_stexcnd (fun _ => @ret _ (Monad__stexcnd nat) unit tt)) =
  @bind _ (Monad_ASPostArr nat) unit unit (obsASP progA_stexcnd)
    (fun _ => @ret _ (Monad_ASPostArr nat) unit tt).
Proof.
  rewrite (obsASP_bind progA_stexcnd (fun _ => @ret _ (Monad__stexcnd nat) unit tt)).
  change (@ret _ (Monad__stexcnd nat) unit tt) with (retP nat tt).
  rewrite (obsASP_ret tt).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Result type independent of the state type                      *)
(* ================================================================= *)

(** The observations are parameterized: [S := nat] but [A := bool] here. *)
Definition getEven : stexcnd nat bool :=
  bindP nat (getP nat) (fun s => retP nat (Nat.even s)).

Lemma getP_outcomes (s : nat) (r : option (nat * nat)) :
  unOptionT (runStateT (getP nat) s) r <-> r = Some (s, s).
Proof. unfold getP. cbn. split; intro H; congruence. Qed.

Lemma getEven_outcomes (s : nat) (r : option (bool * nat)) :
  unOptionT (runStateT getEven s) r <-> r = Some (Nat.even s, s).
Proof.
  unfold getEven.
  rewrite (RawStOpt_SPostArr.outcomes_bind nat (getP nat)
             (fun s => retP nat (Nat.even s)) s r).
  split.
  - intros [oa [Hget Hrest]].
    apply (proj1 (getP_outcomes s oa)) in Hget. subst oa.
    apply (proj1 (RawStOpt_SPostArr.outcomes_ret nat (Nat.even s) s r)).
    exact Hrest.
  - intros ->. exists (Some (s, s)). split.
    + apply (proj2 (getP_outcomes s (Some (s, s)))). reflexivity.
    + apply (proj2 (RawStOpt_SPostArr.outcomes_ret nat (Nat.even s) s
                      (Some (Nat.even s, s)))).
      reflexivity.
Qed.

Example getEven_under :
  tripleASP getEven Under (fun s => s = 1) (fun r => r = Some (Nat.even 1, 1)).
Proof.
  intros r Hr. apply getProgASP_obsASP. exists 1. split; [reflexivity |].
  apply getEven_outcomes. exact Hr.
Qed.
