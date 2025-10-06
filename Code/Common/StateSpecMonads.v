From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.Notations Common.Classes.

Set Implicit Arguments.

Section PrePostMonad.
  Variable S:Type.
  Variable A:Type.

    #[global] Instance StatePre : PreT :=
    {|
      Pre := S -> Prop ;
      ordPre := fun P1 P2 => forall s0, P1 s0 -> P2 s0 
    |}.

  #[global] Instance StatePost : PostT :=
    {|
      Post := fun A => S -> A -> S -> Prop ;
      ordPost := fun _ Q1 Q2 => forall s0 a s1, Q1 s0 a s1 -> Q2 s0 a s1 ;
      conjPost := fun _ Q1 Q2 s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1
    |}.

  #[global] Program Instance StatePrePost : PrePostT StatePre StatePost :=
    {|
      ordPrePost :=
        fun _ pp1 pp2 =>
          (ordPre (fst pp2) (fst pp1)) /\
            (forall s0 r s1, fst pp2 s0 -> snd pp1 s0 r s1 -> snd pp2 s0 r s1)
    |}.

  (** Correctness laws *)
  #[global] Instance PurePrePostLaws : PrePostLaws StatePrePost.
  sfirstorder.
  Qed.
End PrePostMonad.

Section PredMonad.
  
  Variable S:Type.
  
  Definition Pred A := @Post (StatePost S) A.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun s0 r s1 => s0 = s1 /\ r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun s0 r s1 => exists a s', m s0 a s' /\ k a s' r s1.

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

  #[global] Instance PredMonad__Pred : PredMonad Pred :=
    {| monadPred := Monad__Pred ;
       ordPred := fun {A} P1 P2 => ordPost P1 P2 |}.

  #[global] Instance PredMonadLaws__Pred : PredMonadLaws Pred.
  sfirstorder.
  Qed.
End PredMonad.

Section RelationPred2PrePost.

  Variable (S : Type).

  #[global] Program Instance GaloisState :
    GaloisPrePostPred (Pred S) (StatePre S) (StatePost S) :=
    {| p2pp := fun _ P => (fun _ => True, P) ;
       pp2p := fun _ pp s0 r s1 => fst pp s0 -> snd pp s0 r s1
    |}.

  #[global] Instance GaloisPureLaws : 
    GaloisPrePostPredLaws (Pred S) (StatePre S) (StatePost S).
  sfirstorder.
  Qed.
End RelationPred2PrePost.
