From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.Notations.

Set Implicit Arguments.

Section PrePostMonad.
  Variable S:Type.
  Variable A:Type.

  Definition Pre := S -> Prop.
  Definition Post := S -> A -> S -> Prop.
  Definition PrePost := prod Pre Post.

  Definition ordPre (P1 P2:Pre) : Prop := forall s0, P1 s0 -> P2 s0.
  Definition ordPost (Q1 Q2:Post) : Prop := forall s0 a s1, Q1 s0 a s1 -> Q2 s0 a s1.

  Definition ordPrePost (pp1 pp2:PrePost) : Prop :=
    (ordPre (fst pp2) (fst pp1)) /\ (forall s0 r s1, fst pp2 s0 -> snd pp1 s0 r s1 -> snd pp2 s0 r s1).

  Definition conjPost (Q1 Q2:Post) : Post :=
    fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1.

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

Instance PreOrder_ordPrePost :
  forall {S A}, PreOrder (@ordPrePost S A).
Proof. sfirstorder. Qed.

Section PredMonad.
  Variable S:Type.
  Definition Pred A := Post S A.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun s0 r s1 => s0 = s1 /\ r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun s0 r s1 => exists a s', m s0 a s' /\ k a s' r s1.

  Definition ordPred {A} (P1 P2:Pred A) : Prop :=
    ordPost P1 P2.

  Program Definition getPred : Pred S :=
    fun s0 r s1 => r = s0 /\ s1 = s0.

  Program Definition putPred (s : S) : Pred unit :=
    fun s0 r s1 => s1 = s.

  #[global] Instance Monad__Pred : Monad (Pred) :=
    {| ret := fun _ => retPred ;
       bind := fun _ _ => bindPred |}.

  #[global] Instance MonadState__Pred : MonadState S Pred :=
    {| get := getPred ;
       put := putPred |}.    
End PredMonad.

Instance PreOrder_ordPred :
  forall {S A}, PreOrder (@ordPred S A).
Proof. sfirstorder. Qed.

Section RelationPred2PrePost.
  Program Definition p2pp {S A} (P:Pred S A) : PrePost S A :=
    (fun _ => True, P).

  Program Definition pp2p {S A} (pp:PrePost S A) : Pred S A :=
    fun s0 r s1 => fst pp s0 -> snd pp s0 r s1.

  Lemma adjunction_pp_p {S A} (P:Pred S A) (pp:PrePost S A) :
    ordPred P (pp2p pp) <-> ordPrePost (p2pp P) pp.
  Proof. sfirstorder. Qed.
End RelationPred2PrePost.
