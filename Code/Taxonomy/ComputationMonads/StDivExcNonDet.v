(** * [stdivexcnd]: Nondeterminism + divergence + state + exceptions.

    [stdivexcnd S A = stateT S (optionT (optionT SetM)) A]

    This is the interpreted model of [itree nondetE] with state and
    exceptions.  [iforest E] (sets of itrees, [itree E A -> Prop]) is
    NOT a lawful monad for general [E] (the ITree library proves a
    [bind_bind] counterexample).  However, for [void1], every
    [itree void1 A] either converges to a unique value or diverges, so
    an eutt-closed predicate simplifies to [(A -> Prop) * Prop], which
    is isomorphic to [option A -> Prop = optionT SetM A].  This
    specialization IS a lawful monad.

    Concretely, [stdivexcnd S A] unfolds to
    [S -> option (option (A * S)) -> Prop], with three outcome kinds:
    - [Some (Some (a, s'))] : converges with result [a] and state [s']
    - [Some None]           : raises an exception
    - [None]                : diverges *)

From ITree Require Import ITree Events.State Events.Exception Events.Nondeterminism Props.Leaf Props.Infinite.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StExcNonDet.

(* ================================================================= *)
(** ** The [stdivexcnd] monad                                           *)
(* ================================================================= *)

Section StDivExcNonDet.

  Variable S : Type.

  Definition stdivexcnd A := stateT S (optionT (optionT SetM)) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : stdivexcnd A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : stdivexcnd A) (k : A -> stdivexcnd B) : stdivexcnd B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__stdivexcnd : Monad stdivexcnd :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : stdivexcnd S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : stdivexcnd unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__stdivexcnd : MonadState S stdivexcnd :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : stdivexcnd A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : stdivexcnd A) (c : unit -> stdivexcnd A) : stdivexcnd A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__stdivexcnd : MonadExc unit stdivexcnd :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

  (** Nondeterministic choice: union at the [SetM] level. *)
  Definition orP {A} (m1 m2 : stdivexcnd A) : stdivexcnd A :=
    mkStateT (fun s =>
      @mkOptionT (optionT SetM) _ (
        @mkOptionT SetM _ (fun oa =>
          unOptionT (unOptionT (runStateT m1 s)) oa \/
          unOptionT (unOptionT (runStateT m2 s)) oa))).

  (** Divergence: the only outcome is [None] (= spin). *)
  Definition spinP {A} : stdivexcnd A :=
    mkStateT (fun _ =>
      @mkOptionT (optionT SetM) _ (
          @mkOptionT SetM _ (fun oa => oa = None))).

  Definition pickP {A} : stdivexcnd A :=
    mkStateT (fun s =>
                @mkOptionT (optionT SetM) _ (
                    @mkOptionT SetM _ (fun oa => exists a : A, oa = Some (Some (a, s))))).

End StDivExcNonDet.

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

  (** Interpret a [freeprog] into [stdivexcnd] in three steps:

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

  (* stdivexcnd S A := option (option (A * S)) -> Prop *)
  (* can you define a recursive program? *)

  Definition denote {A} (m : freeprog A) : stdivexcnd S A :=
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

(* ================================================================= *)
(** * Facts and laws (merged from NonDetItProgFacts.v)                          *)
(* ================================================================= *)

(** * Monad law proofs for [stdivexcnd].

    [stdivexcnd S = stateT S (optionT (optionT SetM))] combines
    state, exceptions, nontermination, and nondeterminism.

    Since [SetM] satisfies [MonadLawsE] (from [StExcNonDet]),
    the generic [optionT] and [stateT] towers from [Prog]
    lift the laws through two [optionT] layers and one [stateT]
    layer with zero additional proof work. *)

From ITree Require Import Basics.Monad.

Section StDivExcNonDet.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_SetM]
      → [Eq1_optionT]  (inner: divergence layer)
      → [Eq1_optionT]  (outer: exception layer)
      → [Eq1_stateT]

      and similarly for [MonadLawsE]. *)

  Definition Eq1__stdivexcnd : Eq1 (stdivexcnd S) :=
    Eq1_stateT S (optionT (optionT SetM)).

  Definition MonadLawsE__stdivexcnd
    : @MonadLawsE (stdivexcnd S) _ (Monad__stdivexcnd S) :=
    MonadLawsE_stateT S (optionT (optionT SetM)).

End StDivExcNonDet.

(* ================================================================= *)
(** ** Outcome kernel for arrow-derived SP observations              *)
(* ================================================================= *)

Section OutcomeKernel.

  Variable S : Type.

  Definition outcomes {A} (m : stdivexcnd S A) (s : S) (r : option (A * S)) : Prop :=
    unOptionT (unOptionT (runStateT m s)) (Some r).

  Lemma outcomes_ret {A} (a : A) (s : S) (r : option (A * S)) :
    outcomes (retP S a) s r <-> r = Some (a, s).
  Proof.
    unfold outcomes, retP. cbn.
    split; intro H; congruence.
  Qed.

  Lemma outcomes_bind {A B} (m : stdivexcnd S A) (k : A -> stdivexcnd S B)
    (s : S) (r : option (B * S)) :
    outcomes (bindP S m k) s r <->
    exists oa, outcomes m s oa /\
      match oa with
      | Some (a, s') => outcomes (k a) s' r
      | None => r = None
      end.
  Proof.
    unfold outcomes, bindP. cbn. split.
    - intros [oy [H1 H2]]. destruct oy as [[p|]|].
      + destruct p as [a s0]. exists (Some (a, s0)). split; [ exact H1 | exact H2 ].
      + exists None. split; [ exact H1 | congruence ].
      + congruence.
    - intros [oy [H1 H2]]. destruct oy as [[a s0]|].
      + exists (Some (Some (a, s0))). split; [ exact H1 | exact H2 ].
      + exists (Some None). split; [ exact H1 | congruence ].
  Qed.

End OutcomeKernel.
