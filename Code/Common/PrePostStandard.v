From Coq Require Import RelationClasses.
Require Import Coq.Program.Basics.
From Hammer Require Import Hammer Tactics.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Set Implicit Arguments.

Section PrePostMonad.
  Definition PrePost A := prod Prop (A -> Prop).

  Definition ordPrePost {A} (pp1 pp2:PrePost A) : Prop :=
    (fst pp2 -> fst pp1) /\ (forall r, snd pp1 r -> snd pp2 r).

  (** Correctness laws *)
  Theorem strengthen_pre_pp {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordPrePost (P1, Q) (P2, Q).
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post_pp {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordPrePost (P, Q1) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim_pp {A} P (Q1 Q2:A -> Prop) :
    ordPrePost (P, (fun r => Q1 r /\ Q2 r)) (P, Q1) /\
    ordPrePost (P, (fun r => Q1 r /\ Q2 r)) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp {A} (P:Prop) (Q1 Q2:A -> Prop) (m:PrePost A):
    ordPrePost m (P, Q1) ->
    ordPrePost m (P, Q2) ->
    ordPrePost m (P, (fun r => Q1 r /\ Q2 r)).
  Proof. cbv. sfirstorder. Qed.
End PrePostMonad.

Instance : forall {A}, Transitive (@ordPrePost A).
Proof. sfirstorder. Qed.

Instance : forall {A}, Reflexive (@ordPrePost A).
Proof. sfirstorder. Qed.

Section PredMonad.
  Definition Pred A := A -> Prop.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun r => r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun r => exists a, m a /\ k a r.

  Definition ordPred {A} (P1 P2:Pred A) : Prop :=
    forall r, P1 r -> P2 r.
End PredMonad.

Instance : forall {A}, Transitive (@ordPred A).
Proof. sfirstorder. Qed.

Instance : forall {A}, Reflexive (@ordPred A).
Proof. sfirstorder. Qed.

Section RelationPred2PrePost.
  Program Definition p2pp {A} (P:Pred A) : PrePost A :=
    (True, P).

  Program Definition pp2p {A} (pp:PrePost A) : Pred A :=
    fun r => snd pp r.

  Lemma loop_p2pp_pp2p {A} (pp:PrePost A):
    ordPrePost (p2pp (pp2p pp)) pp.
  Proof. cbv. firstorder. Qed. 

  Lemma loop_p2pp_pp2p' {A} (pp:PrePost A):
    ordPrePost pp (p2pp (pp2p pp)).
  Proof. cbv. destruct pp as [P Q]. Abort.

  Lemma inverse_pp2p_p2pp {A} (P:Pred A) :
    ordPred P (pp2p (p2pp P)) /\ ordPred (pp2p (p2pp P)) P.
  Proof. cbv. sfirstorder. Qed.

  Lemma adjunction_pp_p {A} (P:Pred A) (pp:PrePost A) :
    ordPred P (pp2p pp) <-> ordPrePost (p2pp P) pp.
  Proof. sfirstorder. Qed.

  Theorem strengthen_pre_pp2p {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordPred (pp2p (P1, Q)) (pp2p (P2, Q)).
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post_pp2p {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordPred (pp2p (P, Q1)) (pp2p (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim_pp2p {A} P (Q1 Q2:A -> Prop) :
    ordPred (pp2p (P, (fun r => Q1 r /\ Q2 r))) (pp2p (P, Q1)) /\
    ordPred (pp2p (P, (fun r => Q1 r /\ Q2 r))) (pp2p (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp2p {A} (P:Prop) (Q1 Q2:A -> Prop) (m:Pred A):
    ordPred m (pp2p (P, Q1)) ->
    ordPred m (pp2p (P, Q2)) ->
    ordPred m (pp2p (P, (fun r => Q1 r /\ Q2 r))).
  Proof. cbv. sfirstorder. Qed.
End RelationPred2PrePost.