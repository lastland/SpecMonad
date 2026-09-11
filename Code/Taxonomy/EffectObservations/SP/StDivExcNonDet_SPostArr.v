(** * Arrow-derived ASP/DSLP observations of [stdivexcnd].

    Nondeterminism + divergence + exceptions observed into the
    arrow-derived ASP and DSLP monads of [SPostArrMonad], via the generic
    outcome-kernel adapter [SPostArrObservation].  The kernel is the
    double-option outcome relation of [StDivExcNonDet]: normal returns
    and exceptions ([r = None]) are visible, while divergence ([None] at
    the [option (option _)] layer) is INVISIBLE to both readings — a
    program whose every branch diverges has no outcome at all.  The
    monad morphism laws are inherited from the adapter; this file builds
    the kernel, re-exports the readings and laws under local aliases,
    derives kernel-level outcome lemmas for the operations, and works the
    [progA]/[progB]/[progRet]/[progloom] examples: divergence-blindness,
    exception visibility, Under/Over triples, and a compute demo of
    [obsASP_bind]. *)

From Coq Require Import PeanoNat Lia.
From ITree Require Import ITree Basics.Monad.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivExcNonDet.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The outcome kernel                                              *)
(* ================================================================= *)

Definition stdivexcndKernel (S : Type) : OutcomeKernel S (stdivexcnd S) :=
  {| kern := fun A m s r => StDivExcNonDet.outcomes S m s r;
     kern_ret := fun A a s r => StDivExcNonDet.outcomes_ret S a s r;
     kern_bind := fun A B m k s r => StDivExcNonDet.outcomes_bind S m k s r |}.

(* ================================================================= *)
(** ** Kernel-level outcome lemmas for the operations                  *)
(* ================================================================= *)

Section Ops.

  Variable S : Type.

  Lemma outcomes_put (s0 s : S) (r : option (unit * S)) :
    kern (stdivexcndKernel S) (putP S s0) s r <-> r = Some (tt, s0).
  Proof. split; intro H; congruence. Qed.

  Lemma outcomes_get (s : S) (r : option (S * S)) :
    kern (stdivexcndKernel S) (getP S) s r <-> r = Some (s, s).
  Proof. split; intro H; congruence. Qed.

  Lemma outcomes_raise {A} (s : S) (r : option (A * S)) :
    kern (stdivexcndKernel S) (raiseP S tt) s r <-> r = None.
  Proof.
    cbn. split.
    - intros [a [Ha Hr]]. destruct a as [[x|]|]; congruence.
    - intros ->. exists (Some None). split; reflexivity.
  Qed.

  Lemma outcomes_spinP {A} (s : S) (r : option (A * S)) :
    kern (stdivexcndKernel S) (spinP S) s r <-> False.
  Proof. cbn. split; [discriminate | intro F; destruct F]. Qed.

  Lemma outcomes_pickP {A} (s : S) (r : option (A * S)) :
    kern (stdivexcndKernel S) pickP s r <-> exists a, r = Some (a, s).
  Proof.
    cbn. split.
    - intros [a H]. exists a. congruence.
    - intros [a H]. exists a. congruence.
  Qed.

  Lemma outcomes_orP {A} (m1 m2 : stdivexcnd S A) (s : S) (r : option (A * S)) :
    kern (stdivexcndKernel S) (orP S m1 m2) s r
    <-> kern (stdivexcndKernel S) m1 s r \/ kern (stdivexcndKernel S) m2 s r.
  Proof. split; intro H; [exact H | exact H]. Qed.

End Ops.

(* ================================================================= *)
(** ** Observations, readings, and morphism laws                       *)
(* ================================================================= *)

Section Obs.

  Variable S : Type.

  Definition obsASP {A} (m : stdivexcnd S A) : ASPostArr S A :=
    SPostArrObservation.obsASP (stdivexcndKernel S) m.

  Definition obsDSLP {A} (m : stdivexcnd S A) : DSLPostArr S A :=
    SPostArrObservation.obsDSLP (stdivexcndKernel S) m.

  Lemma getProgASP_obsASP {A} (m : stdivexcnd S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r
    <-> exists s, pre s /\ StDivExcNonDet.outcomes S m s r.
  Proof. apply SPostArrObservation.runASP_obsASP. Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivexcnd S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r
    <-> forall s, StDivExcNonDet.outcomes S m s r -> pre s.
  Proof. apply SPostArrObservation.runDSLP_obsDSLP. Qed.

  Theorem obsASP_ret {A} (a : A) :
    obsASP (retP S a) = @ret _ (Monad_ASPostArr S) A a.
  Proof. apply SPostArrObservation.obsASP_ret. Qed.

  Theorem obsASP_bind {A B} (m : stdivexcnd S A) (k : A -> stdivexcnd S B) :
    obsASP (bindP S m k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof. apply SPostArrObservation.obsASP_bind. Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (retP S a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof. apply SPostArrObservation.obsDSLP_ret. Qed.

  Theorem obsDSLP_bind {A B} (m : stdivexcnd S A) (k : A -> stdivexcnd S B) :
    obsDSLP (bindP S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof. apply SPostArrObservation.obsDSLP_bind. Qed.

End Obs.

(* ================================================================= *)
(** ** Worked examples (S := nat)                                      *)
(* ================================================================= *)

(** [progA] reaches [(tt, 42)] and [(tt, 43)] from every state. *)
Lemma progA_outcomes : forall s r,
  kern (stdivexcndKernel nat) progA s r <-> r = Some (tt, 42) \/ r = Some (tt, 43).
Proof.
  intros s r. unfold progA.
  split.
  - intro H.
    apply (proj1 (kern_bind (stdivexcndKernel nat) (putP nat 42) _ s r)) in H.
    destruct H as [oa [Hput Hmid]].
    apply (proj1 (outcomes_put nat 42 s oa)) in Hput. rewrite Hput in Hmid.
    cbv beta iota in Hmid.
    apply (proj1 (kern_bind (stdivexcndKernel nat) (getP nat) _ 42 r)) in Hmid.
    destruct Hmid as [ob [Hget Hrest]].
    apply (proj1 (outcomes_get nat 42 ob)) in Hget. rewrite Hget in Hrest.
    cbv beta iota in Hrest.
    apply (proj1 (outcomes_orP nat _ _ 42 r)) in Hrest.
    destruct Hrest as [H | H].
    + apply (proj1 (outcomes_put nat 42 42 r)) in H. left. exact H.
    + apply (proj1 (outcomes_put nat 43 42 r)) in H. right. exact H.
  - intros [-> | ->].
    + apply (proj2 (kern_bind (stdivexcndKernel nat) (putP nat 42) _ s (Some (tt, 42)))).
      exists (Some (tt, 42)). split.
      * apply (proj2 (outcomes_put nat 42 s (Some (tt, 42)))). reflexivity.
      * apply (proj2 (kern_bind (stdivexcndKernel nat) (getP nat) _ 42 (Some (tt, 42)))).
        exists (Some (42, 42)). split.
        -- apply (proj2 (outcomes_get nat 42 (Some (42, 42)))). reflexivity.
        -- apply (proj2 (outcomes_orP nat (putP nat 42) (putP nat 43) 42
                          (Some (tt, 42)))). left.
           apply (proj2 (outcomes_put nat 42 42 (Some (tt, 42)))). reflexivity.
    + apply (proj2 (kern_bind (stdivexcndKernel nat) (putP nat 42) _ s (Some (tt, 43)))).
      exists (Some (tt, 42)). split.
      * apply (proj2 (outcomes_put nat 42 s (Some (tt, 42)))). reflexivity.
      * apply (proj2 (kern_bind (stdivexcndKernel nat) (getP nat) _ 42 (Some (tt, 43)))).
        exists (Some (42, 42)). split.
        -- apply (proj2 (outcomes_get nat 42 (Some (42, 42)))). reflexivity.
        -- apply (proj2 (outcomes_orP nat (putP nat 42) (putP nat 43) 42
                          (Some (tt, 43)))). right.
           apply (proj2 (outcomes_put nat 43 42 (Some (tt, 43)))). reflexivity.
Qed.

(** [progB]'s spinning branch is divergence, invisible to the SP kernel —
    only the [(tt, 42)] outcome of the [put s] branch survives. *)
Lemma progB_outcomes : forall s r,
  kern (stdivexcndKernel nat) progB s r <-> r = Some (tt, 42).
Proof.
  intros s r. unfold progB.
  split.
  - intro H.
    apply (proj1 (kern_bind (stdivexcndKernel nat) (putP nat 42) _ s r)) in H.
    destruct H as [oa [Hput Hmid]].
    apply (proj1 (outcomes_put nat 42 s oa)) in Hput. rewrite Hput in Hmid.
    cbv beta iota in Hmid.
    apply (proj1 (kern_bind (stdivexcndKernel nat) (getP nat) _ 42 r)) in Hmid.
    destruct Hmid as [ob [Hget Hrest]].
    apply (proj1 (outcomes_get nat 42 ob)) in Hget. rewrite Hget in Hrest.
    cbv beta iota in Hrest.
    apply (proj1 (outcomes_orP nat _ _ 42 r)) in Hrest.
    destruct Hrest as [H | H].
    + apply (proj1 (outcomes_put nat 42 42 r)) in H. exact H.
    + destruct (proj1 (outcomes_spinP nat 42 r) H).
  - intros ->.
    apply (proj2 (kern_bind (stdivexcndKernel nat) (putP nat 42) _ s (Some (tt, 42)))).
    exists (Some (tt, 42)). split.
    + apply (proj2 (outcomes_put nat 42 s (Some (tt, 42)))). reflexivity.
    + apply (proj2 (kern_bind (stdivexcndKernel nat) (getP nat) _ 42 (Some (tt, 42)))).
      exists (Some (42, 42)). split.
      * apply (proj2 (outcomes_get nat 42 (Some (42, 42)))). reflexivity.
      * apply (proj2 (outcomes_orP nat (putP nat 42) (spinP nat) 42
                        (Some (tt, 42)))). left.
        apply (proj2 (outcomes_put nat 42 42 (Some (tt, 42)))). reflexivity.
Qed.

(** [progloom] either raises (amount above the balance) or debits by the
    picked amount. *)
Lemma progloom_outcomes : forall s r,
  kern (stdivexcndKernel nat) progloom s r
  <-> r = None \/ exists k, k <= s /\ r = Some (tt, s - k).
Proof.
  intros s r. unfold progloom.
  split.
  - intro H.
    apply (proj1 (kern_bind (stdivexcndKernel nat) pickP _ s r)) in H.
    destruct H as [oa [Hpick Hmid]].
    apply (proj1 (outcomes_pickP nat s oa)) in Hpick.
    destruct Hpick as [a ->].
    cbv beta iota in Hmid.
    apply (proj1 (kern_bind (stdivexcndKernel nat) (getP nat) _ s r)) in Hmid.
    destruct Hmid as [ob [Hget Hrest]].
    apply (proj1 (outcomes_get nat s ob)) in Hget. rewrite Hget in Hrest.
    cbv beta iota in Hrest.
    destruct (Nat.ltb s a) eqn:E.
    + apply (proj1 (outcomes_raise nat s r)) in Hrest. left. exact Hrest.
    + apply Nat.ltb_ge in E.
      apply (proj1 (outcomes_put nat (s - a) s r)) in Hrest.
      right. exists a. split; [exact E | exact Hrest].
  - intros [-> | [k [Hk ->]]].
    + apply (proj2 (kern_bind (stdivexcndKernel nat) pickP _ s None)).
      exists (Some (S s, s)). split.
      * apply (proj2 (outcomes_pickP nat s (Some (S s, s)))). exists (S s).
        reflexivity.
      * apply (proj2 (kern_bind (stdivexcndKernel nat) (getP nat) _ s None)).
        exists (Some (s, s)). split.
        -- apply (proj2 (outcomes_get nat s (Some (s, s)))). reflexivity.
        -- replace (Nat.ltb s (S s)) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           cbv beta iota.
           apply (proj2 (outcomes_raise nat s None)). reflexivity.
    + apply (proj2 (kern_bind (stdivexcndKernel nat) pickP _ s (Some (tt, s - k)))).
      exists (Some (k, s)). split.
      * apply (proj2 (outcomes_pickP nat s (Some (k, s)))). exists k.
        reflexivity.
      * apply (proj2 (kern_bind (stdivexcndKernel nat) (getP nat) _ s
                        (Some (tt, s - k)))).
        exists (Some (s, s)). split.
        -- apply (proj2 (outcomes_get nat s (Some (s, s)))). reflexivity.
        -- replace (Nat.ltb s k) with false
             by (symmetry; apply Nat.ltb_ge; exact Hk).
           cbv beta iota.
           apply (proj2 (outcomes_put nat (s - k) s (Some (tt, s - k)))).
           reflexivity.
Qed.

(** [progA] Under at [pre := {0}]: both final states are reachable from
    [0] (indeed from every state). *)
Example progA_under :
  tripleASP (stdivexcndKernel nat) progA Under
    (fun s => s = 0) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r Hr. exists 0. split; [reflexivity |].
  apply progA_outcomes. exact Hr.
Qed.

(** Demonic Over at the SAME [pre := {0}]: both final states are
    reachable from every state, so the demonic premise fails on the
    image and the strongest post lies OUTSIDE it — the opposite of the
    angelic Under triple above. *)
Example progA_dslp_over :
  tripleDSL (stdivexcndKernel nat) progA Over
    (fun s => s = 0) (fun r => ~ (r = Some (tt, 42) \/ r = Some (tt, 43))).
Proof.
  intros r Hall Hr.
  destruct Hr as [H42 | H43].
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_introl H42))).
    discriminate.
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_intror H43))).
    discriminate.
Qed.

(** [progB] Under demonstrates divergence-blindness: the postcondition
    holds exactly, even though one branch diverges. *)
Example progB_under :
  tripleASP (stdivexcndKernel nat) progB Under
    (fun _ => True) (fun r => r = Some (tt, 42)).
Proof.
  intros r ->. exists 0. split; [exact I |].
  apply progB_outcomes. reflexivity.
Qed.

(** [progRet] Under at the classic [preEq0]/[postEq0] pair. *)
Example progRet_under :
  tripleASP (stdivexcndKernel nat) progRet Under preEq0 postEq0.
Proof.
  intros r Hr. unfold postEq0 in Hr. subst r.
  exists 0. split; [reflexivity |].
  apply (proj2 (kern_ret (stdivexcndKernel nat) tt 0 (Some (tt, 0)))).
  reflexivity.
Qed.

(** Exception visibility: the angel can pick [amount = S s] and force the
    raise from any state. *)
Example progloom_may_raise :
  runASP (obsASP nat progloom) (fun _ => True) None.
Proof.
  apply (proj2 (getProgASP_obsASP nat progloom (fun _ => True) None)).
  exists 0. split; [exact I |].
  apply progloom_outcomes. left. reflexivity.
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
  - apply (proj2 (ASP_rel_obsASP (stdivexcndKernel nat) (retP nat tt)
                     (tt, 0) (Some (tt, 0)))).
    apply (proj2 (kern_ret (stdivexcndKernel nat) tt 0 (Some (tt, 0)))).
    reflexivity.
  - rewrite (ASP_rel_obsASP (stdivexcndKernel nat) (putP nat 42) (tt, 0)
                (Some (tt, 42))).
    apply (proj2 (outcomes_put nat 42 0 (Some (tt, 42)))). reflexivity.
Qed.
