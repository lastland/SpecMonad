(** * [Pred]: the unary predicate monad

        [Pred A := A -> Prop]

        [ret a    := fun x => x = a]
        [bind m k := fun b => exists a, m a /\ k a b]

    A set of values, presented by its characteristic predicate — the
    powerset/nondeterminism monad.  [Eq1] is pointwise logical equivalence,
    so all four laws hold with no extensionality axioms (see
    [PredMonad.v]).

    Wrapped in a module because [Taxonomy/Pred.v] already binds the name
    [Pred] to the BINARY arrow [Pred A B = A -> B -> Prop]; the two are
    different type constructors and a top-level clash would be silent.
    Write [PredM.Pred] here, or [Import PredM] in a file that does not use
    the arrow. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.

Module PredM.

  Definition Pred (A : Type) : Type := A -> Prop.

  Definition retPred {A} (a : A) : Pred A :=
    fun x => x = a.

  Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun b => exists a, m a /\ k a b.

  #[global]
  Instance Monad_Pred : Monad Pred := {
    ret  := @retPred ;
    bind := @bindPred
  }.

  (** Pointwise logical equivalence. *)
  #[global]
  Instance Eq1_Pred : Eq1 Pred :=
    fun A m1 m2 => forall a, m1 a <-> m2 a.

End PredM.

(* ================================================================= *)
(** * Facts and laws (merged from PredMonadFacts.v)                          *)
(* ================================================================= *)

(** * Monad laws for the unary predicate monad [PredM.Pred]

    [Eq1_Pred] is pointwise iff and [bind] is an existential over the
    intermediate value, so each law is a small logical rearrangement and no
    extensionality axioms are needed. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.

Module PredMFacts.
  Import PredM.

  #[global]
  Instance Eq1Equivalence_Pred : @Eq1Equivalence Pred _ Eq1_Pred.
  Proof.
    constructor; repeat intro; unfold eq1, Eq1_Pred in *.
    - reflexivity.
    - symmetry. apply H.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  #[global]
  Instance MonadLawsE_Pred : @MonadLawsE Pred Eq1_Pred _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x b. cbn. unfold bindPred, retPred. split.
      + intros [a [Heq Hk]]. subst a. exact Hk.
      + intro Hk. exists x. split; [ reflexivity | exact Hk ].
    - (* bind_ret_r *)
      intros A m a. cbn. unfold bindPred, retPred. split.
      + intros [a' [Hm Heq]]. subst a'. exact Hm.
      + intro Hm. exists a. split; [ exact Hm | reflexivity ].
    - (* bind_bind *)
      intros A B C m f g c. cbn. unfold bindPred. split.
      + intros [b [[a [Hm Hf]] Hg]]. exists a. split; [ exact Hm |].
        exists b. split; [ exact Hf | exact Hg ].
      + intros [a [Hm [b [Hf Hg]]]]. exists b. split; [| exact Hg ].
        exists a. split; [ exact Hm | exact Hf ].
    - (* Proper_bind *)
      intros A B m1 m2 Hm k1 k2 Hk b. cbn. unfold bindPred.
      unfold eq1, Eq1_Pred in Hm.
      split; intros [a [Hma Hka]]; exists a; split;
        solve [ apply Hm; exact Hma | apply (Hk a b); exact Hka ].
  Qed.

End PredMFacts.

(* ================================================================= *)
(** * The transformer stack: [PredStExc = stateT S (optionT Pred)]                     *)
(* ================================================================= *)

Import PredM PredMFacts.

From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.

Section PredStExc.

  Variable S : Type.

  Definition PredStExc := stateT S (optionT Pred).

  (* Copy-pasted from [Prog.v]. *)
  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : PredStExc A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B}
    (m : PredStExc A) (k : A -> PredStExc B) : PredStExc B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__PredStExc : Monad PredStExc :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : PredStExc S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : PredStExc unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__PredStExc : MonadState S PredStExc :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : PredStExc A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A}
    (m : PredStExc A) (c : unit -> PredStExc A) : PredStExc A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__PredStExc : MonadExc unit PredStExc :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End PredStExc.

(* ================================================================= *)
(** * Facts and laws for the stack                          *)
(* ================================================================= *)

(** * Monad law proofs for [PredStExc].

    [PredStExc S = stateT S (optionT PredM.Pred)] then inherits [MonadLawsE]
    via the generic [optionT] and [stateT] instances from [Prog].
    Unfolded, [PredStExc S A = S -> option (A * S) -> Prop]. *)

From Coq Require Import FunctionalExtensionality PropExtensionality Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.ComputationMonads Require Import Prog.


(* ================================================================= *)
(** ** [MonadLawsE] for [PredStExc S]                                *)
(* ================================================================= *)

Section PredStExc.

  Variable S : Type.

  (** The instance chains through:
        [PredM.Eq1_Pred] (pointwise iff)
      → [Eq1_optionT]   (on the unwrapped [Pred])
      → [Eq1_stateT]    (pointwise eq)

      and similarly for [MonadLawsE]. *)

  Definition Eq1__PredStExc : Eq1 (PredStExc S) :=
    Eq1_stateT S (optionT Pred).

  Definition MonadLawsE__PredStExc
    : @MonadLawsE (PredStExc S) _ (Monad__PredStExc S) :=
    MonadLawsE_stateT S (optionT Pred).

End PredStExc.
