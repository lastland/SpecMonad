(** * [nditprog]: Nondeterminism + divergence + state + exceptions.

    [nditprog S A = stateT S (optionT (optionT SetM)) A]

    This is the interpreted model of [itree nondetE] with state and
    exceptions.  [iforest E] (sets of itrees, [itree E A -> Prop]) is
    NOT a lawful monad for general [E] (the ITree library proves a
    [bind_bind] counterexample).  However, for [void1], every
    [itree void1 A] either converges to a unique value or diverges, so
    an eutt-closed predicate simplifies to [(A -> Prop) * Prop], which
    is isomorphic to [option A -> Prop = optionT SetM A].  This
    specialization IS a lawful monad.

    Concretely, [nditprog S A] unfolds to
    [S -> option (option (A * S)) -> Prop], with three outcome kinds:
    - [Some (Some (a, s'))] : converges with result [a] and state [s']
    - [Some None]           : raises an exception
    - [None]                : diverges *)

From ITree Require Import
  ITree
  Events.State
  Events.Exception
  Events.Nondeterminism
  Props.Leaf
  Props.Infinite.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness.Taxonomy Require Import
  NonDetProg.

(* ================================================================= *)
(** ** The [nditprog] monad                                           *)
(* ================================================================= *)

Section NonDetItProg.

  Variable S : Type.

  Definition nditprog A := stateT S (optionT (optionT SetM)) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : nditprog A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : nditprog A) (k : A -> nditprog B) : nditprog B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__nditprog : Monad nditprog :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : nditprog S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : nditprog unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__nditprog : MonadState S nditprog :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : nditprog A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : nditprog A) (c : unit -> nditprog A) : nditprog A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__nditprog : MonadExc unit nditprog :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

  (** Nondeterministic choice: union at the [SetM] level. *)
  Definition orP {A} (m1 m2 : nditprog A) : nditprog A :=
    mkStateT (fun s =>
      @mkOptionT (optionT SetM) _ (
        @mkOptionT SetM _ (fun oa =>
          unOptionT (unOptionT (runStateT m1 s)) oa \/
          unOptionT (unOptionT (runStateT m2 s)) oa))).

  (** Divergence: the only outcome is [None] (= spin). *)
  Definition spinP {A} : nditprog A :=
    mkStateT (fun _ =>
      @mkOptionT (optionT SetM) _ (
          @mkOptionT SetM _ (fun oa => oa = None))).

  Definition pickP {A} : nditprog A :=
    mkStateT (fun s =>
                @mkOptionT (optionT SetM) _ (
                    @mkOptionT SetM _ (fun oa => exists a : A, oa = Some (Some (a, s))))).

End NonDetItProg.

Arguments pickP {S A}.

(* ================================================================= *)
(** ** Interpretation from fully uninterpreted itree                  *)
(* ================================================================= *)

Section Denote.

  Variable S : Type.

  (** The fully uninterpreted computation type: an itree with
      state, exception, and nondeterminism effects. *)
  Definition freeprog A :=
    itree (stateE S +' exceptE unit +' nondetE) A.

  (** Interpret a [freeprog] into [nditprog] in three steps:

      1. [run_state] (ITree.Events.State) handles [stateE] by
         threading state, producing
         [itree (exceptE unit +' nondetE) (A * S)].

      2. [throw_prefix] (ITree.Events.Exception) catches exceptions
         and converts them to [inr tt] return values, producing
         [itree (exceptE unit +' nondetE) ((A * S) + unit)].
         After this step no [exceptE] events remain in the tree.

      3. [Leaf] and [any_infinite] (ITree.Props) extract the
         set-of-outcomes representation:
         - [Leaf (inl (s', a))] : some path converges with [(a, s')]
         - [Leaf (inr tt)]      : some path raises an exception
         - [any_infinite]       : some path diverges

      Note: ITree's [run_state] returns [(S * A)] (state first),
      while ExtLib's [stateT] uses [(A * S)] (result first),
      hence the swap in the [Leaf] pattern. *)

  Definition denote {A} (m : freeprog A) : nditprog S A :=
    mkStateT (fun s =>
      let t := throw_prefix (run_state m s) in
      @mkOptionT (optionT SetM) _ (
        @mkOptionT SetM _ (fun oa =>
          match oa with
          | Some (Some (a, s')) => Leaf (inl (s', a)) t
          | Some None           => Leaf (inr tt) t
          | None                => any_infinite t
          end))).

End Denote.
