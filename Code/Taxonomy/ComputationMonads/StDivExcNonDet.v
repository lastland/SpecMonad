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


  (** ** The non-empty fragment

      Nothing in [stdivexcnd] forces the outcome set to be inhabited: the
      everywhere-blocking program [mkStateT (fun _ => mkOptionT (mkOptionT
      (fun _ => False)))] is a well-typed element with no outcomes at all —
      it neither converges, nor raises, nor diverges.  Such an element is a
      MIRACLE for the total demonic reading: [obsDWP] quantifies over the
      outcome set, so it establishes every postcondition, including [False].
      Every program built from the operations above does have an outcome
      from every state, so that is carved out here as a subset type, exactly
      as in [StDivNonDet.v]. *)

  Definition nonEmptyOutcomes {A} (m : stdivexcnd A) : Prop :=
    forall s, exists oa, unOptionT (unOptionT (runStateT m s)) oa.

  Definition stdivexcndNE (A : Type) : Type := { m : stdivexcnd A | nonEmptyOutcomes m }.

  Definition getNEx {A} (m : stdivexcndNE A) : stdivexcnd A := proj1_sig m.

  Lemma getNEx_nonEmpty {A} (m : stdivexcndNE A) : nonEmptyOutcomes (getNEx m).
  Proof. exact (proj2_sig m). Qed.

  (** Closure of [nonEmptyOutcomes] under each operation. *)

  Lemma nonEmpty_retP {A} (a : A) : nonEmptyOutcomes (retP a).
  Proof. intro s. exists (Some (Some (a, s))). cbn. reflexivity. Qed.

  Lemma nonEmpty_getP : nonEmptyOutcomes getP.
  Proof. intro s. exists (Some (Some (s, s))). cbn. reflexivity. Qed.

  Lemma nonEmpty_putP (s' : S) : nonEmptyOutcomes (putP s').
  Proof. intro s. exists (Some (Some (tt, s'))). cbn. reflexivity. Qed.

  Lemma nonEmpty_raiseP {A} : nonEmptyOutcomes (@raiseP A tt).
  Proof.
    intro s. exists (Some None). cbn. exists (Some None). split; reflexivity.
  Qed.

  Lemma nonEmpty_spinP {A} : nonEmptyOutcomes (@spinP A).
  Proof. intro s. exists None. cbn. reflexivity. Qed.

  (** [pickP] needs a value to pick: over an empty [A] it IS stuck. *)
  Lemma nonEmpty_pickP {A} (a0 : A) : nonEmptyOutcomes (@pickP A).
  Proof. intro s. exists (Some (Some (a0, s))). cbn. exists a0. reflexivity. Qed.

  Lemma nonEmpty_orP {A} (m1 m2 : stdivexcnd A) :
    nonEmptyOutcomes m1 -> nonEmptyOutcomes (orP m1 m2).
  Proof.
    intros H s. destruct (H s) as [oa Ho]. exists oa. cbn. left. exact Ho.
  Qed.

  Lemma nonEmpty_bindP {A B} (m : stdivexcnd A) (k : A -> stdivexcnd B) :
    nonEmptyOutcomes m -> (forall a, nonEmptyOutcomes (k a)) ->
    nonEmptyOutcomes (bindP m k).
  Proof.
    intros Hm Hk s. destruct (Hm s) as [[[[a s']|]|] Ho].
    - destruct (Hk a s') as [ob Hob]. exists ob. cbn.
      exists (Some (Some (a, s'))). split; [ exact Ho | exact Hob ].
    - exists (Some None). cbn.
      exists (Some None). split; [ exact Ho | reflexivity ].
    - exists None. cbn. exists None. split; [ exact Ho | reflexivity ].
  Qed.

  Lemma nonEmpty_catchP {A} (m : stdivexcnd A) (c : unit -> stdivexcnd A) :
    nonEmptyOutcomes m -> (forall u, nonEmptyOutcomes (c u)) ->
    nonEmptyOutcomes (catchP m c).
  Proof.
    intros Hm Hc s. destruct (Hm s) as [[[[a s']|]|] Ho].
    - exists (Some (Some (a, s'))). cbn.
      exists (Some (Some (a, s'))). split; [ exact Ho | reflexivity ].
    - destruct (Hc tt s) as [ob Hob]. exists ob. cbn.
      exists (Some None). split; [ exact Ho | exact Hob ].
    - exists None. cbn. exists None. split; [ exact Ho | reflexivity ].
  Qed.

  (** The operations, lifted to the subset type. *)

  Definition retNEx {A} (a : A) : stdivexcndNE A :=
    exist _ (retP a) (nonEmpty_retP a).

  Definition bindNEx {A B} (m : stdivexcndNE A) (k : A -> stdivexcndNE B)
    : stdivexcndNE B :=
    exist _ (bindP (getNEx m) (fun a => getNEx (k a)))
            (nonEmpty_bindP (getNEx m) (fun a => getNEx (k a))
               (getNEx_nonEmpty m) (fun a => getNEx_nonEmpty (k a))).

  #[global]
    Instance Monad__stdivexcndNE : Monad stdivexcndNE :=
    {| ret := fun _ => @retNEx _ ;
       bind := fun _ _ => @bindNEx _ _ |}.

  Definition getStNEx : stdivexcndNE S := exist _ getP nonEmpty_getP.

  Definition putStNEx (s' : S) : stdivexcndNE unit :=
    exist _ (putP s') (nonEmpty_putP s').

  #[global]
    Instance MonadState__stdivexcndNE : MonadState S stdivexcndNE :=
    {| get := getStNEx ;
       put := putStNEx |}.

  Definition raiseNEx {A} (_ : unit) : stdivexcndNE A :=
    exist _ (raiseP tt) (@nonEmpty_raiseP A).

  Definition catchNEx {A} (m : stdivexcndNE A) (c : unit -> stdivexcndNE A)
    : stdivexcndNE A :=
    exist _ (catchP (getNEx m) (fun u => getNEx (c u)))
            (nonEmpty_catchP (getNEx m) (fun u => getNEx (c u))
               (getNEx_nonEmpty m) (fun u => getNEx_nonEmpty (c u))).

  #[global]
    Instance MonadExc__stdivexcndNE : MonadExc unit stdivexcndNE :=
    {| raise := fun _ => raiseNEx ;
       catch := fun _ => catchNEx |}.

  Definition spinNEx {A} : stdivexcndNE A := exist _ spinP (@nonEmpty_spinP A).

  Definition orNEx {A} (m1 m2 : stdivexcndNE A) : stdivexcndNE A :=
    exist _ (orP (getNEx m1) (getNEx m2)) (nonEmpty_orP _ _ (getNEx_nonEmpty m1)).

  Definition pickNEx {A} (a0 : A) : stdivexcndNE A :=
    exist _ pickP (nonEmpty_pickP a0).
End StDivExcNonDet.

Arguments pickP {S A}.

Arguments stdivexcndNE _ _.
Arguments nonEmptyOutcomes {_} {_}.
Arguments getNEx {_} {_}.
Arguments retNEx {_} {_}.
Arguments bindNEx {_} {_} {_}.
Arguments raiseNEx {_} {_}.
Arguments catchNEx {_} {_}.
Arguments spinNEx {_} {_}.
Arguments orNEx {_} {_}.
Arguments pickNEx {_} {_}.

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
