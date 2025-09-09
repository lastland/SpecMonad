(** This file is very similar to PureSpecMonads, but defines ordering
  of PrePosts in the standard way and pp2p (P,Q) = fun r -> Q r.*)

From Coq Require Import RelationClasses.
Require Import Coq.Program.Basics.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Set Implicit Arguments.

Section PrePostMonad.
  Variable A:Type.

  Definition Pre := Prop.
  Definition Post := A -> Prop.
  Definition PrePost := prod Pre Post.

  Definition ordPre (P1 P2:Pre) : Prop := P1 -> P2.
  Definition ordPost (Q1 Q2:Post) : Prop := forall r, Q1 r -> Q2 r.

  Definition ordPrePost (pp1 pp2:PrePost) : Prop :=
    (ordPre (fst pp2) (fst pp1)) /\ (ordPost (snd pp1) (snd pp2)).

  Definition conjPost (Q1 Q2:Post) : Post :=
    fun r => Q1 r /\ Q2 r.

  (** Correctness laws *)
  Theorem strengthen_pre_pp (P1 P2:Pre) (Q:Post) :
    (ordPre P2 P1) ->
    ordPrePost (P1, Q) (P2, Q).
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post_pp (P:Pre) (Q1 Q2:Post) :
    ordPost Q1 Q2 ->
    ordPrePost (P, Q1) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim_pp P (Q1 Q2:Post) :
    ordPrePost (P, conjPost Q1 Q2) (P, Q1) /\
    ordPrePost (P, conjPost Q1 Q2) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp (P:Pre) (Q1 Q2:Post) (m:PrePost) :
    ordPrePost m (P, Q1) ->
    ordPrePost m (P, Q2) ->
    ordPrePost m (P, conjPost Q1 Q2).
  Proof. cbv. sfirstorder. Qed.
End PrePostMonad.

Instance : forall {A}, Transitive (@ordPrePost A).
Proof. sfirstorder. Qed.

Instance : forall {A}, Reflexive (@ordPrePost A).
Proof. sfirstorder. Qed.

Section PredMonad.
  Definition Pred A := Post A.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun r => r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun r => exists a, m a /\ k a r.

  Definition ordPred {A} (P1 P2:Pred A) : Prop :=
    forall r, P1 r -> P2 r.

  #[global] Instance Monad__Pred : Monad (Pred) :=
    {| ret := fun _ => retPred ;
       bind := fun _ _ => bindPred |}.    
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
  Proof. destruct pp as [P Q]. cbv. Abort. (** impossible to prove **)

  Lemma inverse_pp2p_p2pp {A} (P:Pred A) :
    ordPred P (pp2p (p2pp P)) /\ ordPred (pp2p (p2pp P)) P.
  Proof. cbv. sfirstorder. Qed.

  Lemma adjunction_pp_p {A} (P:Pred A) (pp:PrePost A) :
    ordPred P (pp2p pp) <-> ordPrePost (p2pp P) pp.
  Proof. sfirstorder. Qed.

  Theorem strengthen_pre_pp2p {A} (P1 P2:Pre) (Q:Post A) :
    ordPre P2 P1 ->
    ordPred (pp2p (P1, Q)) (pp2p (P2, Q)).
  Proof.
    intros HP2iP1.
    apply adjunction_pp_p.
    pose proof (loop_p2pp_pp2p (P1, Q)).
    pose proof (strengthen_pre_pp Q HP2iP1).
    transitivity (P1, Q); assumption.
  Qed.

  Theorem weaken_post_pp2p {A} (P:Pre) (Q1 Q2:Post A) :
    ordPost Q1 Q2 ->
    ordPred (pp2p (P, Q1)) (pp2p (P, Q2)).
  Proof.
    intros HQ1iQ2.
    apply adjunction_pp_p.
    pose proof (loop_p2pp_pp2p (P, Q1)).
    pose proof (weaken_post_pp P HQ1iQ2).
    transitivity (P, Q1); assumption.
  Qed.

  Theorem post_conj_elim_pp2p {A} P (Q1 Q2:Post A) :
    ordPred (pp2p (P, conjPost Q1 Q2)) (pp2p (P, Q1)) /\
    ordPred (pp2p (P, conjPost Q1 Q2)) (pp2p (P, Q2)).
  Proof. 
    pose proof (post_conj_elim_pp P Q1 Q2).
    destruct H.
    split; apply adjunction_pp_p;
    pose proof (loop_p2pp_pp2p (P, conjPost Q1 Q2));
    transitivity (P, conjPost Q1 Q2); assumption.
   Qed.

  Theorem post_conj_intro_pp2p {A} (P:Pre) (Q1 Q2:Post A) (m:Pred A):
    ordPred m (pp2p (P, Q1)) ->
    ordPred m (pp2p (P, Q2)) ->
    ordPred m (pp2p (P, conjPost Q1 Q2)).
  Proof.
    intros H1 H2.
    apply adjunction_pp_p in H1.
    apply adjunction_pp_p in H2.
    apply adjunction_pp_p.
    pose proof (post_conj_intro_pp H1 H2).
    assumption.
  Qed.
End RelationPred2PrePost.