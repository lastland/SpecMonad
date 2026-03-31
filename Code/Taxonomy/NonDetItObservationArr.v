(** * Arrow-based SP observation for [nditprog].

    Maps [nditprog S A] (nondeterminism + divergence) to
    [ASPostArr S A], the predicate transformer arrow.

    The three-valued outcome space ([Some (Some _)], [Some None],
    [None]) is collapsed into the two-valued [option (A * S)]:
    - [Some (a, s')] from converging outcomes
    - [None] from exceptions OR divergence *)

From Coq Require Import Lia.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg SPostArr.

Import MonadNotation.
Open Scope monad_scope.

Section NonDetItObservationArr.

  Variable S : Type.

  (** Underlying relation: angelic SP.

      For [Some (a, s')]: there is a converging path.
      For [None]: there is an exception path OR a divergent path. *)
  Definition obsRelASP {A} (m : nditprog S A)
    : SPArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      match r with
      | Some (a, s') =>
          unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
      | None =>
          unOptionT (unOptionT (runStateT m s)) (Some None) \/
          unOptionT (unOptionT (runStateT m s)) None
      end.

  (** Wrapped as a predicate transformer arrow. *)
  Definition obsArrowASP {A} (m : nditprog S A) : ASPostArr S A :=
    mkASP (obsRelASP m).

End NonDetItObservationArr.

Arguments obsRelASP {_} {_}.
Arguments obsArrowASP {_} {_}.

(* ================================================================= *)
(** ** Examples: pure nondeterminism (no divergence)                  *)
(* ================================================================= *)

Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(** All reachable converging results have state >= 42. *)
Theorem progA_all :
  forall s r,
    obsRelASP progA (tt, s) r ->
    match r with
    | Some (_, s') => s' >= 42
    | None => False
    end.
Proof.
  intros s [[] |] H; cbn in H.
  - sauto.
  - destruct H as [H | H]; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  forall s, obsRelASP progA (tt, s) (Some (tt, 42)).
Proof. intros. cbn. sauto. Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  forall s, obsRelASP progA (tt, s) (Some (tt, 43)).
Proof. intros. cbn. sauto. Qed.

(* ================================================================= *)
(** ** Examples: nondeterminism + divergence                          *)
(* ================================================================= *)

Example progB : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (spinP _).

(** State 42 is reachable (via the converging branch). *)
Theorem progB_42 :
  forall s, obsRelASP progB (tt, s) (Some (tt, 42)).
Proof. intros. cbn. sauto. Qed.

(** Failure (divergence) is reachable (via the spinning branch). *)
Theorem progB_None :
  forall s, obsRelASP progB (tt, s) None.
Proof.
  intros. cbn. right. sauto.
Qed.
