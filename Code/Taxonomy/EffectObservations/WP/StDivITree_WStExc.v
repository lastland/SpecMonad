(** * Observation functions for [stdivitree].

    Maps [stdivitree S A] (deterministic computation via ITree) to specification
    types.

    WP observations: [obsAWP] and [obsDWP] (total) and [obsAWLP] and [obsDWLP]
    (partial, tolerates divergence) map into [WStExc S A]. Because [stdivitree S A] is
    deterministic, we show [obsWPCollapse] and [obsWLPCollapse] theorems that
    state [obsAWP] is equivalent to [obsDWP], [obsAWLP] is equivalent to
    [obsDWLP].

    SP observation: [obsASP] and [obsDSLP], then [obsDSP] and [obsASLP] can be
    defined based on the former two. Even though [stdivitree S A] is deterministic, it
    is not necessarily reversible, so we cannot collapse any of the [sp]s. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Paco Require Import paco.
From Hammer Require Import Tactics.
From ITree Require Import ITree Eq Props.Infinite.
From ITree.Extra Require Import Dijkstra.PureITreeBasics.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

(** There is no nondeterminism in [stdivitree], so [awp] and [dwp] are the same. We
    only define [wp] here. *)

Section ObservationWP.

  Variable S : Type.

  Lemma obsAWP_mono {A} (m : stdivitree S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT o => exists r, eutt eq o (ret r) /\ post r
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [o].
    destruct H as [r [He Hp]]. exists r. split; [ exact He | exact (Hpq r Hp) ].
  Qed.

  Definition obsAWP {A} (m : stdivitree S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsAWP_mono m s))).

  Lemma obsAWLP_mono {A} (m : stdivitree S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT o =>
                                (exists r, eutt eq o (ret r) /\ post r) \/ any_infinite o
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [o].
    destruct H as [[r [He Hp]] | Hi];
      [ left; exists r; split; [ exact He | exact (Hpq r Hp) ] | right; exact Hi ].
  Qed.

  Definition obsAWLP {A} (m : stdivitree S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsAWLP_mono m s))).

  Lemma obsDWP_mono {A} (m : stdivitree S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT o =>
                                (forall r, eutt eq o (ret r) -> post r) /\ ~ any_infinite o
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [o].
    destruct H as [Hall Hni]. split; [| exact Hni ].
    intros r He. exact (Hpq r (Hall r He)).
  Qed.

  Definition obsDWP {A} (m : stdivitree S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsDWP_mono m s))).

  Lemma obsDWLP_mono {A} (m : stdivitree S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT o => (forall r, eutt eq o (ret r) -> post r) : Prop
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [o].
    intros r He. exact (Hpq r (H r He)).
  Qed.

  Definition obsDWLP {A} (m : stdivitree S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsDWLP_mono m s))).

  (** Unfolding lemmas: needed because [obs*] now carry a monotonicity
      proof, so a downstream [destruct] cannot abstract through them. *)
  Lemma obsAWP_run {A} (m : stdivitree S A) s post :
    unOptionT (runStateT (obsAWP m) s) post
    <-> match runStateT m s with
        | mkOptionT o => exists r, eutt eq o (ret r) /\ post r end.
  Proof. split; intro H; exact H. Qed.

  Lemma obsAWLP_run {A} (m : stdivitree S A) s post :
    unOptionT (runStateT (obsAWLP m) s) post
    <-> match runStateT m s with
        | mkOptionT o => (exists r, eutt eq o (ret r) /\ post r) \/ any_infinite o end.
  Proof. split; intro H; exact H. Qed.

  Lemma obsDWP_run {A} (m : stdivitree S A) s post :
    unOptionT (runStateT (obsDWP m) s) post
    <-> match runStateT m s with
        | mkOptionT o => (forall r, eutt eq o (ret r) -> post r) /\ ~ any_infinite o end.
  Proof. split; intro H; exact H. Qed.

  Lemma obsDWLP_run {A} (m : stdivitree S A) s post :
    unOptionT (runStateT (obsDWLP m) s) post
    <-> match runStateT m s with
        | mkOptionT o => (forall r, eutt eq o (ret r) -> post r) : Prop end.
  Proof. split; intro H; exact H. Qed.

  Theorem obsWPCollapse :
    forall {A} (m : stdivitree S A) post s0,
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
    forall {A} (m : stdivitree S A) post s0,
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

    This replaces the earlier [pp2wp]/[ordWStExc] (spec-as-element +
    refinement over all predicates) encoding; that encoding agrees with
    this one on [Under] but degenerates on [Over], and only the direct
    form makes the [awp ⊣ dslp] GaloisArr connection provable. *)
Definition tripleWP {S A}
  (obs : stdivitree S A -> WStExc S A)
  (prog : stdivitree S A)
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

Example progA_WP := obsDWP progA_stdivitree.

(** [progA_stdivitree] deterministically converges to [(tt, 42)] from any initial
    state. *)
Lemma progA_run :
  forall s, eutt eq (unOptionT (runStateT progA_stdivitree s)) (Ret (Some (tt, 42))).
Proof.
  intro s. unfold progA_stdivitree. cbn.
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
  unfold progA_WP. rewrite obsDWP_run.
  destruct (runStateT progA_stdivitree s) as [o] eqn:E. cbn in Hrun.
  split.
  - intros r Hr. rewrite Hrun in Hr. apply eutt_inv_Ret in Hr. subst r. reflexivity.
  - intro Hinf. rewrite Hrun in Hinf. exact (ret_not_div Hinf).
Qed.

Theorem progA_WP_all_triple :
  tripleWP obsDWP progA_stdivitree Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s _.
  pose proof (progA_run s) as Hrun.
  rewrite obsDWP_run.
  destruct (runStateT progA_stdivitree s) as [o] eqn:E. cbn in Hrun.
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
  unfold progA_WP in H. rewrite obsDWP_run in H.
  destruct (runStateT progA_stdivitree 0) as [o] eqn:E. cbn in Hrun.
  destruct H as [Hall _].
  specialize (Hall (Some (tt, 42)) Hrun). cbn in Hall. discriminate.
Qed.

(** A [Correct] triple fails exactly when the postcondition excludes a
    reachable outcome: [progA_stdivitree] reaches state [42], which violates [s = 43]. *)
Theorem progA_WP_not43_triple :
  not (tripleWP obsDWP progA_stdivitree Under
      (fun _ => True)
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 43
        | None => False
        end)).
Proof.
  unfold tripleWP. intro H.
  specialize (H 0 I). pose proof (progA_run 0) as Hrun.
  rewrite obsDWP_run in H.
  destruct (runStateT progA_stdivitree 0) as [o] eqn:E. cbn in Hrun.
  destruct H as [Hall _].
  specialize (Hall (Some (tt, 42)) Hrun). cbn in Hall. discriminate.
Qed.
