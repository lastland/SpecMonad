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
(** ** Raw outcome laws                                                *)
(* ================================================================= *)

(** The laws below expose the operational semantics of the operations
    directly on raw outcomes, [unOptionT (unOptionT (runStateT m s)) r],
    with no accessor indirection.  They are stated as constructive
    pointwise iff (no extensionality needed) and are the single owned
    copy: clients should reuse them instead of unfolding the
    implementation again. *)

(** The everywhere-blocking computation: its outcome set is EMPTY — it
    neither converges, nor raises, nor diverges.  Blocking is an empty
    outcome set, distinct from the divergence token [None].  Defined
    only to state the checked examples below; not an operation of the
    model. *)
Local Definition blockP (S : Type) {A} : stdivexcnd S A :=
  mkStateT (fun _ =>
    @mkOptionT (optionT SetM) _ (
      @mkOptionT SetM _ (fun _ => False))).

Section OutcomeLaws.

  Variable S : Type.

  Lemma outcomes_ret {A} (a : A) (s : S) (r : option (option (A * S))) :
    unOptionT (unOptionT (runStateT (retP S a) s)) r <-> r = Some (Some (a, s)).
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma outcomes_bind {A B} (m : stdivexcnd S A) (k : A -> stdivexcnd S B)
      (s : S) (r : option (option (B * S))) :
    unOptionT (unOptionT (runStateT (bindP S m k) s)) r <->
    (exists oy, unOptionT (unOptionT (runStateT m s)) oy /\
       match oy with
       | Some (Some (a, s')) => unOptionT (unOptionT (runStateT (k a) s')) r
       | Some None => r = Some None
       | None => r = None
       end).
  Proof.
    cbn. split; intros [oy [H1 H2]]; exists oy; split; [exact H1 | | exact H1 |];
      destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  Qed.

  Lemma outcomes_get (s : S) (r : option (option (S * S))) :
    unOptionT (unOptionT (runStateT (getP S) s)) r <-> r = Some (Some (s, s)).
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma outcomes_put (t : S) (s : S) (r : option (option (unit * S))) :
    unOptionT (unOptionT (runStateT (putP S t) s)) r <-> r = Some (Some (tt, t)).
  Proof. cbn. split; intro H; congruence. Qed.

  (** An exception is the outcome [Some None]: the inner option fails,
      the outer one still terminates. *)
  Lemma outcomes_raise {A} (s : S) (r : option (option (A * S))) :
    unOptionT (unOptionT (runStateT (raiseP S tt) s)) r <-> r = Some None.
  Proof.
    cbn. split.
    - intros [a [Ha Hr]]. destruct a as [[x|]|]; congruence.
    - intros ->. exists (Some None). split; reflexivity.
  Qed.

  Lemma outcomes_pickP {A} (s : S) (r : option (option (A * S))) :
    unOptionT (unOptionT (runStateT (pickP (S := S)) s)) r
    <-> exists a, r = Some (Some (a, s)).
  Proof.
    cbn. split.
    - intros [a H]. exists a. congruence.
    - intros [a H]. exists a. congruence.
  Qed.

  (** Divergence is the outcome [None]: the outer option fails. *)
  Lemma outcomes_spin {A} (s : S) (r : option (option (A * S))) :
    unOptionT (unOptionT (runStateT (spinP S) s)) r <-> r = None.
  Proof. cbn. split; intro H; congruence. Qed.

  (** ** Checked examples

      An empty PREFIX blocks; yet an empty CONTINUATION is not a right
      annihilator, because both failure tokens are absorbing under
      [bind] rather than erasing it.  The proofs go through the raw
      laws above, not by unfolding the implementation again. *)

  Lemma blockP_outcomes {A} (s : S) (r : option (option (A * S))) :
    ~ unOptionT (unOptionT (runStateT (blockP S) s)) r.
  Proof. intro H. cbn in H. exact H. Qed.

  (** An empty prefix blocks the whole computation, whatever the
      continuation: no intermediate outcome exists to continue from. *)
  Example blockP_bind_blocks {A B} (k : A -> stdivexcnd S B)
      (s : S) (r : option (option (B * S))) :
    ~ unOptionT (unOptionT (runStateT (bindP S (blockP S) k) s)) r.
  Proof.
    intro H. apply outcomes_bind in H. destruct H as [oa [Hblk _]].
    exact (blockP_outcomes s oa Hblk).
  Qed.

  (** The raised exception survives an empty continuation. *)
  Example raiseP_bind_empty {A B} (s : S) :
    unOptionT (unOptionT (runStateT
      (bindP S (raiseP S tt) (fun _ : A => blockP S (A := B))) s)) (Some None).
  Proof.
    apply outcomes_bind. exists (Some None). split.
    - apply outcomes_raise. reflexivity.
    - reflexivity.
  Qed.

  (** ...and so does divergence. *)
  Example spinP_bind_empty {A B} (s : S) :
    unOptionT (unOptionT (runStateT
      (bindP S (spinP S) (fun _ : A => blockP S (A := B))) s)) None.
  Proof.
    apply outcomes_bind. exists None. split.
    - apply outcomes_spin. reflexivity.
    - reflexivity.
  Qed.

  (** [pickP] over an empty choice type blocks: there is no [a] to
      pick, so the outcome set is empty. *)
  Example pickP_Empty_set_blocks (s : S) (r : option (option (Empty_set * S))) :
    ~ unOptionT (unOptionT (runStateT (pickP (S := S) (A := Empty_set)) s)) r.
  Proof.
    intro H. apply outcomes_pickP in H. destruct H as [a _]. destruct a.
  Qed.

End OutcomeLaws.

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
         [itree (exceptE unit +' nondetE) (S * A)].

      2. [throw_prefix] (ITree.Events.Exception) catches exceptions
         and converts them to [inr tt] return values, producing
         [itree (exceptE unit +' nondetE) ((S * A) + unit)].
         The event type is unchanged, but throws become return values.

      3. [Leaf] and [any_infinite] (ITree.Props) extract the
         set-of-outcomes representation:
         - [Leaf (inl (s', a)) t] selects [Some (Some (a, s'))].
         - [Leaf (inr tt) t] selects [Some None], an exception.
         - [any_infinite t] selects raw [None], divergence.

      Note: ITree's [run_state] returns [(S * A)] (state first),
      while ExtLib's [stateT] uses [(A * S)] (result first),
      hence the swap in the [Leaf] pattern. *)

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
    the generic [optionT] and [stateT] laws from [TransformerLaws.v]
    lift the laws through two [optionT] layers and one [stateT]
    layer. *)

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
