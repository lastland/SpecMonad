
From Coq Require Import Nat Bool.
From ExtLib Require Import Monad MonadState MonadExc.
From Hammer Require Import Tactics.

Set Implicit Arguments.

Section ComputationMonad.

  (* State S; Exception E. *)
  Variables S E : Type.

  Definition M A := S -> (A * S + E) -> Prop.

  #[global]
  Instance Monad_M : Monad M :=
    {|
      ret := fun _ a s r => r = inl (a, s) ;
      bind := fun _ _ m k s b =>
                exists r, m s r /\
                       match r with
                       | inl (a, mid) => k a mid b
                       | inr e => b = inr e
                       end
    |}.
                                  
  #[global]
  Instance MonadState_M : MonadState S M :=
    {|
      get := fun s r => r = inl (s, s) ;
      put := fun n _ r => r = inl (tt, n) 
    |}.

  #[global]
  Instance MonadExc_M : MonadExc E M :=
    {|
      raise := fun _ e _ r => r = inr e ;
      catch := fun _ t c s r =>
                 exists a, t s a /\
                        match a with
                        | inl a => r = inl a
                        | inr e => c e s r
                        end
    |}.

  Definition input {A} : M A :=
    fun s r => exists a, r = inl (a, s). 

End ComputationMonad.

Section WeakestPreTransformer.

  Variables S E : Type.
  
  Definition W A := S -> ((A * S + E) -> Prop) -> Prop.

  #[global]
  Instance Monad_W : Monad W :=
    {|
      ret := fun _ a s post => post (inl (a, s)) ;
      bind := fun _ _ w k s post =>
                (w s (fun r => match r with
                            | inl (a, s') => k a s' post
                            | inr e => post (inr e)
                            end))
    |}.
  
  #[global]
  Instance MonadState_W : MonadState S W :=
    {|
      get := fun s post => post (inl (s, s)) ;
      put := fun n _ post => post (inl (tt, n))
    |}.

    #[global]
    Instance MonadExc_W : MonadExc E W :=
    {|
      raise := fun _ e _ post => post (inr e) ;
      catch := fun _ t c s post =>
                 (t s (fun r => match r with
                             | inl a => post (inl a)
                             | inr e => c e s post
                            end))
    |}.

  (** All possible [input] must satisfy [post]. *)
  Definition inputW {A} : W A :=
    fun s post => forall a, post (inl (a, s)).

End WeakestPreTransformer.

(** This is essentially the same as weakest precondition transformer: the only
    difference happens at the [input] function. Indeed, in Hoare's original
    paper, he mentioned that weakest possible transformer coincides with weakest
    precondition transformer if the language is deterministic. *)
Section WeakestPossiblePreTransformer.

  Variables S E : Type.
  
  Definition WP A := S -> ((A * S + E) -> Prop) -> Prop.

  #[global]
  Instance Monad_WP : Monad WP :=
    {|
      ret := fun _ a s post => post (inl (a, s)) ;
      bind := fun _ _ w k s post =>
                (w s (fun r => match r with
                            | inl (a, s') => k a s' post
                            | inr e => post (inr e)
                            end))
    |}.
  
  #[global]
  Instance MonadState_WP : MonadState S WP :=
    {|
      get := fun s post => post (inl (s, s)) ;
      put := fun n _ post => post (inl (tt, n))
    |}.

  Instance MonadExc_WP : MonadExc E WP :=
    {|
      raise := fun _ e _ post => post (inr e) ;
      catch := fun _ t c s post =>
                 (t s (fun r => match r with
                             | inl a => post (inl a)
                             | inr e => c e s post
                            end))
    |}.

  (** Only one [input] needs to satisfy [post]. *)
  Definition inputWP {A} : WP A :=
    fun s post => exists a, post (inl (a, s)).

End WeakestPossiblePreTransformer.

Open Scope monad_scope.
Import MonadNotation.

Definition example : M nat unit nat :=
  s <- get ;;
  x <- @input _ _ nat ;;   (* Type annotation required. *)
  if (even x && (s =? 10)) then
    raise tt
  else ret x.

Definition exampleW : W nat unit nat :=
  s <- get ;;
  x <- @inputW _ _ nat ;;   (* Type annotation required. *)
  if (even x && (s =? 10)) then
    raise tt
  else ret x.

Definition exampleWP : WP nat unit nat :=
  s <- get ;;
  x <- @inputWP _ _ nat ;;   (* Type annotation required. *)
  if (even x && (s =? 10)) then
    raise tt
  else ret x.

Definition Hoare {S E A} (m : M S E A) (w : W S E A)
  (pre : S -> Prop) (post : (A * S + E) -> Prop) : Prop :=
  forall s, pre s -> w s post /\ w s (m s).

(** Sufficient incorrectness logic based on weakest possible precondition. *)
Definition SIL {S E A} (m : M S E A) (wp : WP S E A)
  (pre : S -> Prop) (post : (A * S + E) -> Prop) : Prop :=
  forall s, pre s -> wp s post /\ wp s (m s).

Theorem exampleHoare : Hoare example exampleW
                         (fun s => s <> 10) (fun r => match r with
                                               | inl _ => True
                                               | inr _ => False
                                              end).
Proof.
  unfold Hoare. intros s pre. split.
  - cbn. unfold inputW. intros a.
    destruct (even a) eqn:evena; sauto.
  - cbn. unfold inputW. intros a.
    destruct (even a) eqn:evena; sauto.
Qed.

(** This cannot be proven. *This is expected*. *)
Theorem exampleHoare' : Hoare example exampleW
                         (fun s => s = 10) (fun r => r = inr tt).
Proof.
  unfold Hoare. intros s pre. split.
  - cbn. unfold inputW. intros a.
    destruct (even a) eqn:evena.
    + sauto. (* This is true when b is even. *)
    + cbn. (* Stuck here because you can't prove the program erros when b is not even. *)
Abort.

(** This can be proven. This is sufficient incorrectness logic. *)
Theorem exampleSIL : SIL example exampleWP
                       (fun s => s = 10) (fun r => r = inr tt).
Proof.
  unfold SIL. intros s pre. split.
  - cbn. unfold inputWP. exists 0. cbn. sauto.
  - cbn. unfold inputWP. exists 0. cbn.
    destruct (PeanoNat.Nat.eqb_spec s 10).
    + exists (inl (s, s)). split; [reflexivity |].
      unfold input. exists (inl (10, 10)).
      sauto.
    + contradiction.
Qed.
  
(** In incorrectness logic of O'Hearn, the program must have the following three
    postconditions in conjunction:
    1. r = inr tt ;
    2. even x ;
    3. s = 10
 *)
