(** * Arrow-derived ASP/DSLP observations of [stdivexcnd].

    The observations record normal returns and exceptions ([Some None]
    in the double-option computation).  Divergence (outer [None]) is
    invisible.  The examples exercise both predecessor readings. *)

From Coq Require Import PeanoNat Lia.
From Hammer Require Import Tactics.
From ITree Require Import ITree Basics.Monad.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.Taxonomy.Arrows Require Import SPostArrMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import SPostArrObservation.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivExcNonDet.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Visible outcomes of the operations                             *)
(* ================================================================= *)

(** These are SLICE facts: they read raw outcomes at [Some r] only.
    Within that slice an exception is the outcome [None] (the inner
    option failed while the outer one still terminates), and the raw
    outer [None] — divergence — is omitted.  The slice decisions are
    the same as [StDivExcNonDet_SPStExc.v]'s; each fact below is
    derived from the corresponding FULL law owned by the computation
    module, never by unfolding the transformer stack. *)

Section Ops.

  Variable S : Type.

  Lemma outcomes_put (s0 s : S) (r : option (unit * S)) :
    unOptionT (unOptionT (runStateT (putP S s0) s)) (Some r) <-> r = Some (tt, s0).
  Proof.
    apply (iff_trans (StDivExcNonDet.outcomes_put S s0 s (Some r))).
    split; intro H; congruence.
  Qed.

  Lemma outcomes_get (s : S) (r : option (S * S)) :
    unOptionT (unOptionT (runStateT (getP S) s)) (Some r) <-> r = Some (s, s).
  Proof.
    apply (iff_trans (StDivExcNonDet.outcomes_get S s (Some r))).
    split; intro H; congruence.
  Qed.

  (** The exception survives the slice as [r = None]. *)
  Lemma outcomes_raise {A} (s : S) (r : option (A * S)) :
    unOptionT (unOptionT (runStateT (raiseP S tt) s)) (Some r) <-> r = None.
  Proof.
    apply (iff_trans (StDivExcNonDet.outcomes_raise S s (Some r))).
    split; intro H; congruence.
  Qed.

  Lemma outcomes_pickP {A} (s : S) (r : option (A * S)) :
    unOptionT (unOptionT (runStateT pickP s)) (Some r) <-> exists a, r = Some (a, s).
  Proof.
    apply (iff_trans (StDivExcNonDet.outcomes_pickP S s (Some r))).
    split; intros [a H]; exists a; congruence.
  Qed.

End Ops.

(* ================================================================= *)
(** ** Observations, readings, and morphism laws                       *)
(* ================================================================= *)

Section Obs.

  Variable S : Type.

  Definition obsASP {A} (m : stdivexcnd S A) : ASPostArr S A :=
    relASP (fun us r => unOptionT (unOptionT (runStateT m (snd us))) (Some r)).

  Definition obsDSLP {A} (m : stdivexcnd S A) : DSLPostArr S A :=
    asp_to_dslp (obsASP m).

  Lemma getProgASP_obsASP {A} (m : stdivexcnd S A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r
    <-> exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
  Proof.
    rewrite runASP_rel. unfold obsASP. setoid_rewrite ASP_rel_relASP.
    reflexivity.
  Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivexcnd S A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r
    <-> forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
  Proof.
    rewrite runDSLP_rel. unfold obsDSLP, obsASP.
    setoid_rewrite DSLP_rel_asp_to_dslp. setoid_rewrite ASP_rel_relASP.
    reflexivity.
  Qed.

  Theorem obsASP_ret {A} (a : A) :
    obsASP (retP S a) = @ret _ (Monad_ASPostArr S) A a.
  Proof.
    apply ASP_rel_ext. intros [[] s] r.
    unfold obsASP. rewrite ASP_rel_relASP, ASP_rel_ret.
    apply (iff_trans (StDivExcNonDet.outcomes_ret S a s (Some r))).
    split; intro H; congruence.
  Qed.

  (** The slice outcome set of a bind, derived from the FULL
      computation-owned [StDivExcNonDet.outcomes_bind]: a middle normal
      outcome [Some (a, t)] continues into [k]; the exception [None] is
      retained; and the raw outer [None] (divergence) never reaches the
      slice — the [discriminate] below is exactly that omission. *)
  Local Lemma outcomes_bind {A B} (m : stdivexcnd S A)
      (k : A -> stdivexcnd S B) s r :
    unOptionT (unOptionT (runStateT (bindP S m k) s)) (Some r) <->
    exists om, unOptionT (unOptionT (runStateT m s)) (Some om) /\
      match om with
      | Some (a, t) => unOptionT (unOptionT (runStateT (k a) t)) (Some r)
      | None => r = None
      end.
  Proof.
    apply (iff_trans (StDivExcNonDet.outcomes_bind S m k s (Some r))).
    split.
    - intros [oy [Hm Hk]]. destruct oy as [om|]; [|discriminate].
      exists om. split; [exact Hm |].
      destruct om as [[a t]|]; [exact Hk | congruence].
    - intros [om [Hm Hk]]. exists (Some om). split; [exact Hm |].
      destruct om as [[a t]|]; [exact Hk | congruence].
  Qed.

  Theorem obsASP_bind {A B} (m : stdivexcnd S A) (k : A -> stdivexcnd S B) :
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

  Theorem obsDSLP_bind {A B} (m : stdivexcnd S A) (k : A -> stdivexcnd S B) :
    obsDSLP (bindP S m k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof. unfold obsDSLP. rewrite obsASP_bind. apply asp_to_dslp_bind. Qed.

  Definition tripleASP {A} (m : stdivexcnd S A) kind pre post : Prop :=
    SPostArrObservation.tripleASP (obsASP m) kind pre post.

  Definition tripleDSL {A} (m : stdivexcnd S A) kind pre post : Prop :=
    SPostArrObservation.tripleDSL (obsDSLP m) kind pre post.

End Obs.

(* ================================================================= *)
(** ** Primitive checks through the observation interface              *)
(* ================================================================= *)

(** The slice decisions of [Section Ops], read at the OBSERVATION
    interface through [getProgASP_obsASP] and the full computation
    laws — no program or stack unfolding is involved.
    [progloom_may_raise] and [progB_under] below exercise the same two
    facts through programs; these are their primitive counterparts. *)

(** The raised exception is retained: [raiseP] is observed at the
    exceptional slice outcome [None]. *)
Example raiseP_obs_retained :
  runASP (obsASP nat (raiseP nat (A := unit) tt)) (fun _ => True) None.
Proof.
  apply (proj2 (getProgASP_obsASP nat (raiseP nat (A := unit) tt)
                  (fun _ => True) None)).
  exists 0. split; [exact I |].
  apply (StDivExcNonDet.outcomes_raise nat (A := unit) 0 (Some None)).
  reflexivity.
Qed.

(** Divergence is invisible: the slice is read at [Some r], so [spinP]'s
    raw outer [None] token is never observed. *)
Example spinP_obs_invisible (r : option (unit * nat)) :
  ~ runASP (obsASP nat (spinP nat (A := unit))) (fun _ => True) r.
Proof.
  intros H.
  apply (proj1 (getProgASP_obsASP nat (spinP nat (A := unit))
                  (fun _ => True) r)) in H.
  destruct H as [s [_ Hr]].
  apply (StDivExcNonDet.outcomes_spin nat (A := unit) s (Some r)) in Hr.
  discriminate Hr.
Qed.

(* ================================================================= *)
(** ** Worked examples (S := nat)                                      *)
(* ================================================================= *)

(** [progA] reaches [(tt, 42)] and [(tt, 43)] from every state. *)
Lemma progA_outcomes : forall s r,
  unOptionT (unOptionT (runStateT progA s)) (Some r) <->
  r = Some (tt, 42) \/ r = Some (tt, 43).
Proof.
  intros s r. unfold progA. cbn. split; sauto limit: 200.
Qed.

(** [progB]'s spinning branch is divergence, invisible to the observations —
    only the [(tt, 42)] outcome of the [put s] branch survives. *)
Lemma progB_outcomes : forall s r,
  unOptionT (unOptionT (runStateT progB s)) (Some r) <-> r = Some (tt, 42).
Proof.
  intros s r. unfold progB. cbn. split; sauto limit: 200.
Qed.

(** [progloom] either raises (amount above the balance) or debits by the
    picked amount. *)
Lemma progloom_outcomes : forall s r,
  unOptionT (unOptionT (runStateT progloom s)) (Some r)
  <-> r = None \/ exists k, k <= s /\ r = Some (tt, s - k).
Proof.
  intros s r. unfold progloom.
  split.
  - intro H.
    apply (proj1 (outcomes_bind nat pickP _ s r)) in H.
    destruct H as [oa [Hpick Hmid]].
    apply (proj1 (outcomes_pickP nat s oa)) in Hpick.
    destruct Hpick as [a ->].
    cbv beta iota in Hmid.
    apply (proj1 (outcomes_bind nat (getP nat) _ s r)) in Hmid.
    destruct Hmid as [ob [Hget Hrest]].
    apply (proj1 (outcomes_get nat s ob)) in Hget. rewrite Hget in Hrest.
    cbv beta iota in Hrest.
    destruct (Nat.ltb s a) eqn:E.
    + apply (proj1 (outcomes_raise nat s r)) in Hrest. left. exact Hrest.
    + apply Nat.ltb_ge in E.
      apply (proj1 (outcomes_put nat (s - a) s r)) in Hrest.
      right. exists a. split; [exact E | exact Hrest].
  - intros [-> | [k [Hk ->]]].
    + apply (proj2 (outcomes_bind nat pickP _ s None)).
      exists (Some (S s, s)). split.
      * apply (proj2 (outcomes_pickP nat s (Some (S s, s)))). exists (S s).
        reflexivity.
      * apply (proj2 (outcomes_bind nat (getP nat) _ s None)).
        exists (Some (s, s)). split.
        -- apply (proj2 (outcomes_get nat s (Some (s, s)))). reflexivity.
        -- replace (Nat.ltb s (S s)) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           cbv beta iota.
           apply (proj2 (outcomes_raise nat s None)). reflexivity.
    + apply (proj2 (outcomes_bind nat pickP _ s (Some (tt, s - k)))).
      exists (Some (k, s)). split.
      * apply (proj2 (outcomes_pickP nat s (Some (k, s)))). exists k.
        reflexivity.
      * apply (proj2 (outcomes_bind nat (getP nat) _ s
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
  tripleASP nat progA Under
    (fun s => s = 0) (fun r => r = Some (tt, 42) \/ r = Some (tt, 43)).
Proof.
  intros r Hr. apply getProgASP_obsASP. exists 0. split; [reflexivity |].
  apply progA_outcomes. exact Hr.
Qed.

(** Demonic Over at the SAME [pre := {0}]: both final states are
    reachable from every state, so the demonic premise fails on the
    image and the strongest post lies OUTSIDE it — the opposite of the
    angelic Under triple above. *)
Example progA_dslp_over :
  tripleDSL nat progA Over
    (fun s => s = 0) (fun r => ~ (r = Some (tt, 42) \/ r = Some (tt, 43))).
Proof.
  intros r Hall Hr.
  rewrite getProgDSLP_obsDSLP in Hall.
  destruct Hr as [H42 | H43].
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_introl H42))).
    discriminate.
  - specialize (Hall 1 (proj2 (progA_outcomes 1 _) (or_intror H43))).
    discriminate.
Qed.

(** [progB] Under demonstrates divergence-blindness: the postcondition
    holds exactly, even though one branch diverges. *)
Example progB_under :
  tripleASP nat progB Under
    (fun _ => True) (fun r => r = Some (tt, 42)).
Proof.
  intros r ->. apply getProgASP_obsASP. exists 0. split; [exact I |].
  apply progB_outcomes. reflexivity.
Qed.

(** [progRet] Under at the classic [preEq0]/[postEq0] pair. *)
Example progRet_under :
  tripleASP nat progRet Under preEq0 postEq0.
Proof.
  intros r Hr. unfold postEq0 in Hr. subst r.
  apply getProgASP_obsASP.
  exists 0. split; [reflexivity |].
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
  - rewrite obsASP_ret, ASP_rel_ret. reflexivity.
  - unfold obsASP. rewrite ASP_rel_relASP. reflexivity.
Qed.
