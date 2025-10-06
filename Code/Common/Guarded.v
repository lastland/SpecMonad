From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.PureSpecMonads.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Definition guarded (A : Type) : Type :=
    { P : Prop & P -> A }.

Instance Monad_guarded : Monad guarded.
Proof.
  simple refine {|
    ret A x := existT _ True (fun _ => x);
  |}.
  (* bind *)
  intros A B x f. simpl.
  exists (exists (h : projT1 x), projT1 (f (projT2 x h))).
  simple refine (fun h => projT2 (f (projT2 x _)) _).
  - destruct h. assumption.
  - destruct h as [h hf]. assumption.
Defined.

Class GuardedMonad (M : Type -> Type) `{Monad M} := {
    guard : forall (p : Prop), M p
}.

Definition guard' (p:Prop) : guarded p :=
  existT _ p (fun h => h).

Instance ReqMonad_G : @GuardedMonad guarded Monad_guarded := {|
  guard (p: Prop) := guard' p
|}.

Program Definition obsPred (A : Type) (m : guarded A) : Pred A :=
  fun r => forall p, projT2 m p = r.
  (* if a proof of the pre-condition exists,
     then one has a returned value *)

Example test_even (x:nat) : guarded nat :=
  _ <- guard (Nat.even x = true) ;;
  ret x.
  
Example test_even_correct :
  forall x, 
    ordPred (obsPred (test_even x)) (fun r => Nat.even x = true -> x = r).
Proof.
  intro x.
  unfold ordPred, obsPred.
  intros r H Hxeven.
  simpl in *.
  apply H.
  exists Hxeven.
  constructor.
Qed.

Example test_even_correct' :
  forall x, Nat.even x = true ->
    ordPred (obsPred (test_even x)) (fun r => x = r).
Proof.
  intro x.
  unfold ordPred, obsPred.
  intros Hxeven r H.
  simpl in *.
  apply H.
  exists Hxeven.
  constructor.
Qed.