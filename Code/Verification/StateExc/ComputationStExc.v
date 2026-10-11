(** * Computations with state and exceptions:
      [stdivexcndNE S = stateT S (optionT divndNE)]

    The lift of the base monad [divndNE] by the option and state
    transformers -- a lift of the base, not of the state setting -- with its
    operations and the outcome lemmas [outStExc_*].  Outer [None] is
    divergence, [Some None] an exception, [Some (Some (a, s))] a normal
    return. *)

From Coq Require Import Morphisms FunctionalExtensionality PropExtensionality.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import TransformerLaws.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.
From Incorrectness.Verification.Base Require Import DivNonDetNE.

Definition stdivexcndNE (S : Type) : Type -> Type := stateT S (optionT divndNE).
#[global] Instance Monad__stdivexcndNE (S : Type) : Monad (stdivexcndNE S) :=
  @Monad_stateT S (optionT divndNE) (@Monad_optionT divndNE Monad__divndNE).
Definition Eq1__stdivexcndNE (S : Type) : Eq1 (stdivexcndNE S) :=
  @Eq1_stateT S (optionT divndNE) (@Eq1_optionT divndNE Eq1__divndNE).
Definition Eq1Equivalence__stdivexcndNE (S : Type)
  : @Eq1Equivalence (stdivexcndNE S) (Monad__stdivexcndNE S) (Eq1__stdivexcndNE S) :=
  Eq1Equivalence_stateT S (optionT divndNE).
Definition MonadLawsE__stdivexcndNE (S : Type)
  : @MonadLawsE (stdivexcndNE S) (Eq1__stdivexcndNE S) (Monad__stdivexcndNE S) :=
  MonadLawsE_stateT S (optionT divndNE).
#[global] Instance MonadState__stdivexcndNE (S : Type) : MonadState S (stdivexcndNE S) :=
  @MonadState_stateT S (optionT divndNE) (@Monad_optionT divndNE Monad__divndNE).
Definition outStExc {S A} (m : stdivexcndNE S A) (s : S)
  : option (option (A * S)) -> Prop :=
  unOptionT (getNE (unOptionT (runStateT m s))).

Definition orStExc {S A} (m1 m2 : stdivexcndNE S A) : stdivexcndNE S A :=
  mkStateT (fun s =>
    mkOptionT (orNE (unOptionT (runStateT m1 s)) (unOptionT (runStateT m2 s)))).
Definition divergeStExc {S A} : stdivexcndNE S A :=
  mkStateT (fun _ => mkOptionT divergeNE).
Definition raiseStExc {S A} : stdivexcndNE S A :=
  mkStateT (fun _ => mkOptionT (retNE None)).

(** An arbitrary natural number, with the state unchanged. *)
Definition pickStExc {S} : stdivexcndNE S nat :=
  mkStateT (fun s =>
    mkOptionT
      (exist _
         (@mkOptionT SetM _ (fun o => exists n : nat, o = Some (Some (n, s))))
         (ex_intro _ (Some (Some (0, s))) (ex_intro _ 0 eq_refl)))).

(** The outcomes of each operation. *)
Section Outcomes.
  Context {S : Type}.

  Lemma outStExc_ret {A} (a : A) (s : S) (o : option (option (A * S))) :
    outStExc (ret a) s o <-> o = Some (Some (a, s)).
  Proof. reflexivity. Qed.

  Lemma outStExc_bind {A B} (m : stdivexcndNE S A) (k : A -> stdivexcndNE S B) (s : S)
    (o : option (option (B * S))) :
    outStExc (bind m k) s o
    <-> exists o1, outStExc m s o1 /\
          match o1 with
          | Some (Some (a, s')) => outStExc (k a) s' o
          | Some None => o = Some None
          | None => o = None
          end.
  Proof.
    etransitivity;
      [ exact (outcomes_bind (getNE (unOptionT (runStateT m s)))
                 (fun aM => getNE
                    match aM with
                    | Some a => unOptionT (let (v, s') := a in runStateT (k v) s')
                    | None => retNE None
                    end) o) |].
    split; intros [o1 [H1 H2]]; exists o1; (split; [ exact H1 |]);
      destruct o1 as [[[a s']|]|]; exact H2.
  Qed.

  Lemma outStExc_get (s : S) (o : option (option (S * S))) :
    outStExc get s o <-> o = Some (Some (s, s)).
  Proof. reflexivity. Qed.

  Lemma outStExc_put (s' s : S) (o : option (option (unit * S))) :
    outStExc (put s') s o <-> o = Some (Some (tt, s')).
  Proof. reflexivity. Qed.

  Lemma outStExc_or {A} (m1 m2 : stdivexcndNE S A) (s : S)
    (o : option (option (A * S))) :
    outStExc (orStExc m1 m2) s o <-> outStExc m1 s o \/ outStExc m2 s o.
  Proof. reflexivity. Qed.

  Lemma outStExc_diverge {A} (s : S) (o : option (option (A * S))) :
    outStExc (divergeStExc : stdivexcndNE S A) s o <-> o = None.
  Proof. reflexivity. Qed.

  Lemma outStExc_raise {A} (s : S) (o : option (option (A * S))) :
    outStExc (raiseStExc : stdivexcndNE S A) s o <-> o = Some None.
  Proof. reflexivity. Qed.

  Lemma outStExc_pick (s : S) (o : option (option (nat * S))) :
    outStExc pickStExc s o <-> exists n, o = Some (Some (n, s)).
  Proof. reflexivity. Qed.
End Outcomes.
