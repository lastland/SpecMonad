(** * Arrow-based SP observation for [ndprog].

    Maps [ndprog S A] (nondeterministic computation) to
    [SPostArr S A], the predicate transformer arrow.

    The angelic SP simply checks membership in the outcome set. *)

From Coq Require Import Lia.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg SPostArr.

Import MonadNotation.
Open Scope monad_scope.

Section NonDetObservationArr.

  Variable S : Type.

  (** Underlying relation: result [r] is a reachable outcome of [m]
      from state [s]. *)
  Definition obsRelASP {A} (m : ndprog S A)
    : SPArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      unOptionT (runStateT m s) r.

  (** Wrapped as a predicate transformer arrow. *)
  Definition obsArrowASP {A} (m : ndprog S A) : SPostArr S A :=
    mkPSA (obsRelASP m).

End NonDetObservationArr.

Arguments obsRelASP {_} {_}.
Arguments obsArrowASP {_} {_}.

(* ================================================================= *)
(** ** Examples                                                        *)
(* ================================================================= *)

Example progA : ndprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(** All reachable results from precondition [True] have state >= 42. *)
Theorem progA_all :
  forall s r,
    obsRelASP progA (tt, s) r ->
    match r with
    | Some (_, s') => s' >= 42
    | None => False
    end.
Proof.
  intros s [[[] s']|] H; cbn in H; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  forall s, obsRelASP progA (tt, s) (Some (tt, 42)).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). split; [reflexivity|].
  exists (Some (42, 42)). split; [reflexivity|].
  left. reflexivity.
Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  forall s, obsRelASP progA (tt, s) (Some (tt, 43)).
Proof.
  intros. cbn.
  exists (Some (tt, 42)). split; [reflexivity|].
  exists (Some (42, 42)). split; [reflexivity|].
  right. reflexivity.
Qed.
