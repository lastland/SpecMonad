(** * The ambient strongest-postcondition transformer

    [ProgSP] is the common predicate-transformer space used by the four SP
    logics.  This module contains only infrastructure shared by those logics:
    the healthiness properties, raw comparison targets, and observed-relation
    operations.  Each healthy monad and its laws live in its corresponding
    module under [Logics/]. *)

From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Recipes.Examples.StExDv Require Import Program.

Import MonadNotation.
Open Scope monad_scope.

Section ProgSPCarrier.
  Variable S : Type.

  Definition ProgSP (A : Type) : Type := (S -> Prop) -> (option (A * S) -> Prop).
End ProgSPCarrier.

Arguments ProgSP {_}.

Section ProgPredicateTransformers.
  Variable S : Type.

  Definition StrictProg {A} (w : ProgSP A) : Prop :=
    forall (r : option (A * S)), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : ProgSP A) : Prop :=
    forall (r : option (A * S)), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : ProgSP A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
End ProgPredicateTransformers.

(* ==================================================================== *)
(** * Ambient comparison targets                                         *)
(* ==================================================================== *)

Section SpecOrders.
  Variable S : Type.

  Definition ordProgSP {A} (m1 m2 : @ProgSP S A) : Prop :=
    forall pre r, m1 pre r -> m2 pre r.

  Definition pp2_over {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : @ProgSP S A :=
    fun p r => (forall s, p s -> pre s) -> post r.

  Definition pp2_under {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : @ProgSP S A :=
    fun p r => (forall s, pre s -> p s) /\ post r.
End SpecOrders.

Arguments ordProgSP {_} {_}.
Arguments pp2_over {_} {_}.
Arguments pp2_under {_} {_}.

(* ==================================================================== *)
(** * The observed relation                                              *)
(* ==================================================================== *)

(** All four observations observe the SAME relation between an initial state
    and a finite outcome; they differ only in how they READ it as a predicate
    transformer.  The relation, its unit and its composition are therefore
    shared, and live in this file. *)

Definition SPRel (S A : Type) : Type := S -> option (A * S) -> Prop.

Definition relLe {S A} (R1 R2 : SPRel S A) : Prop :=
  forall s r, R1 s r -> R2 s r.

Definition retRel {S A} (a : A) : SPRel S A :=
  fun s r => r = Some (a, s).

Definition compRel {S A B} (R : SPRel S A) (K : A -> SPRel S B) : SPRel S B :=
  fun s r =>
    exists o, R s o /\
      match o with
      | Some (a, smid) => K a smid r
      | None => r = None
      end.

Lemma compRel_mono {S A B}
  (R1 R2 : SPRel S A) (K1 K2 : A -> SPRel S B) :
  relLe R1 R2 -> (forall a, relLe (K1 a) (K2 a)) ->
  relLe (compRel R1 K1) (compRel R2 K2).
Proof.
  intros HR HK s r [o [Ho Hk]]. exists o. split; [exact (HR s o Ho) |].
  destruct o as [[a smid]|]; [exact (HK a smid r Hk) | exact Hk].
Qed.

(** The terminating slice of the outcome set of [m] at [s].  This is the
    relation that every observation in [Logics/] reads. *)
Definition obsRel {S A} (m : prog S A) : SPRel S A :=
  fun s r => unOptionT (unOptionT (runStateT m s)) (Some r).

Lemma obsRel_ret {S A} (a : A) :
  forall s r, obsRel (ret a : prog S A) s r <-> retRel a s r.
Proof. intros s [[b s']|]; cbn; split; congruence. Qed.

Lemma obsRel_bind {S A B} (m : prog S A) (k : A -> prog S B) :
  forall s r,
    obsRel (m >>= k) s r <->
    compRel (obsRel m) (fun a => obsRel (k a)) s r.
Proof.
  intros s r. unfold obsRel, compRel.
  rewrite outcomes_bind. split.
  - intros [oa [Hm Hk]]. destruct oa as [[[a s']|]|].
    + exists (Some (a, s')). split; assumption.
    + exists None. split; [exact Hm | congruence].
    + discriminate Hk.
  - intros [[[a s']|] [Hm Hk]].
    + exists (Some (Some (a, s'))). split; assumption.
    + exists (Some None). split; [exact Hm | congruence].
Qed.
