(** * Computations with state: [stdivndNE S = stateT S divndNE]

    The lift of the base monad [divndNE] by the state transformer, lawful by
    the generic transformer laws, with its operations and the outcome lemmas
    [outSt_*].  Non-empty from every start state by construction.

    Programs with state are [stateT S (itree E)]: ExtLib's state
    transformer over ITrees.  [denoteSt] is the base [denote] under the
    transformer, a monad morphism by [MonadMorphism_stateT]. *)

From Coq Require Import Morphisms FunctionalExtensionality PropExtensionality.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad Core.ITreeDefinition Core.ITreeMonad.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import TransformerLaws OrderedMonad.
From Incorrectness.Verification.DivNonDet Require Import Computation.

(* ================================================================= *)
(** * The two stacks: [stdivndNE] and [stdivexcndNE]                  *)
(* ================================================================= *)

(** The state transformer applied to [divndNE], and to [divndNE] under the
    option transformer.  Monad, equality and state operations are ExtLib's
    and [TransformerLaws.v]'s, at the base dictionaries above. *)

Definition stdivndNE (S : Type) : Type -> Type := stateT S divndNE.

#[global] Instance Monad__stdivndNE (S : Type) : Monad (stdivndNE S) :=
  @Monad_stateT S divndNE Monad__divndNE.

Definition Eq1__stdivndNE (S : Type) : Eq1 (stdivndNE S) :=
  @Eq1_stateT S divndNE Eq1__divndNE.

(** The two stacks are lawful: the generic transformer laws, at the base. *)
Definition Eq1Equivalence__stdivndNE (S : Type)
  : @Eq1Equivalence (stdivndNE S) (Monad__stdivndNE S) (Eq1__stdivndNE S) :=
  Eq1Equivalence_stateT S divndNE.
Definition MonadLawsE__stdivndNE (S : Type)
  : @MonadLawsE (stdivndNE S) (Eq1__stdivndNE S) (Monad__stdivndNE S) :=
  MonadLawsE_stateT S divndNE.

#[global] Instance MonadState__stdivndNE (S : Type) : MonadState S (stdivndNE S) :=
  @MonadState_stateT S divndNE Monad__divndNE.

(** The outcomes of a computation from a start state: a non-empty set of
    [option]s, [None] being divergence.  At state+exceptions an outcome that
    is not divergence is itself an [option], [None] being a raised
    exception. *)
Definition outSt {S A} (m : stdivndNE S A) (s : S) : option (A * S) -> Prop :=
  unOptionT (getNE (runStateT m s)).

(** Choice and divergence, pointwise in the start state; raising. *)
Definition orSt {S A} (m1 m2 : stdivndNE S A) : stdivndNE S A :=
  mkStateT (fun s => orNE (runStateT m1 s) (runStateT m2 s)).
Definition divergeSt {S A} : stdivndNE S A :=
  mkStateT (fun _ => divergeNE).

(** The outcomes of each operation. *)
Section Outcomes.
  Context {S : Type}.

  Lemma outSt_ret {A} (a : A) (s : S) (o : option (A * S)) :
    outSt (ret a) s o <-> o = Some (a, s).
  Proof. reflexivity. Qed.

  Lemma outSt_bind {A B} (m : stdivndNE S A) (k : A -> stdivndNE S B) (s : S)
    (o : option (B * S)) :
    outSt (bind m k) s o
    <-> exists o1, outSt m s o1 /\
          match o1 with
          | Some (a, s') => outSt (k a) s' o
          | None => o = None
          end.
  Proof.
    etransitivity;
      [ exact (outcomes_bind (getNE (runStateT m s))
                 (fun vs => getNE (let (v, s') := vs in runStateT (k v) s')) o) |].
    split; intros [o1 [H1 H2]]; exists o1; (split; [ exact H1 |]);
      destruct o1 as [[a s']|]; exact H2.
  Qed.

  Lemma outSt_get (s : S) (o : option (S * S)) :
    outSt get s o <-> o = Some (s, s).
  Proof. reflexivity. Qed.

  Lemma outSt_put (s' s : S) (o : option (unit * S)) :
    outSt (put s') s o <-> o = Some (tt, s').
  Proof. reflexivity. Qed.

  Lemma outSt_or {A} (m1 m2 : stdivndNE S A) (s : S) (o : option (A * S)) :
    outSt (orSt m1 m2) s o <-> outSt m1 s o \/ outSt m2 s o.
  Proof. reflexivity. Qed.

  Lemma outSt_diverge {A} (s : S) (o : option (A * S)) :
    outSt (divergeSt : stdivndNE S A) s o <-> o = None.
  Proof. reflexivity. Qed.
End Outcomes.

(* ================================================================= *)
(** * Programs with state                                             *)
(* ================================================================= *)

(** The monad of programs with state; [get] and [put] are ExtLib's. *)
#[global] Instance Monad__stateT_itree {E} (S : Type) : Monad (stateT S (itree E)) :=
  @Monad_stateT S (itree E) Monad_itree.

Section DenoteSt.
  Context {E : Type -> Type} `{HE : HasAnswers E} (S : Type).

  Definition denoteSt : forall A, stateT S (itree E) A -> stdivndNE S A :=
    stateT_map S (@denote E HE).

  Theorem denoteSt_morphism :
    @MonadMorphism (stateT S (itree E)) (stdivndNE S)
      (@Monad_stateT S (itree E) Monad_itree) (Monad__stdivndNE S)
      (@Eq1_stateT S (itree E) Eq1_ITree) (Eq1__stdivndNE S) denoteSt.
  Proof.
    exact (@MonadMorphism_stateT (itree E) divndNE Monad_itree Monad__divndNE
             Eq1_ITree Eq1__divndNE Eq1Equivalence__divndNE MonadLawsE__divndNE
             S (@denote E HE) denote_morphism).
  Qed.

  (** The outcomes of a program from a start state are those of its tree from
      that state. *)
  Lemma outSt_denoteSt {A} (m : stateT S (itree E) A) (s : S) (o : option (A * S)) :
    outSt (denoteSt A m) s o <-> unOptionT (getNE (denote (runStateT m s))) o.
  Proof. reflexivity. Qed.
End DenoteSt.
