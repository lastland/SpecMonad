(** * Triples as typings with state

    The state instances of [Generic/Typings.v], and the negative results:
    no index has the ASP [Under] triple as its typings
    ([no_asp_under_index]), nor the DSLP [Over] triple
    ([no_dslp_over_index]). *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import Typings.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Typings.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Triples.

Definition wpUnderSt {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A := mkStateT (fun s => wpUnderPure (pre s) post).

Definition wpOverSt {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A := mkStateT (fun s => wpOverPure (pre s) post).

(** For any morphism into the three WP monads, so for all four readings:
    an [Under] triple is a typing in [DM] at [wpUnder], an [Over] triple a
    typing in [DMop] at [wpOver]. *)
Section WPTypings.
  Context {M : Type -> Type}.

  Context {S : Type}.

  Theorem triple_under_wpSt (θ : forall A, M A -> WSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Under pre post <-> ordWSt (θ A m) (wpUnderSt pre post).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpUnderPure (runStateT (θ A m) s) (pre s) post) (H s)).
    - exact (proj2 (le_wpUnderPure (runStateT (θ A m) s) (pre s) post) (H s)).
  Qed.

  Theorem triple_over_wpSt (θ : forall A, M A -> WSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Over pre post <-> ordWSt (wpOverSt pre post) (θ A m).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpOverPure (runStateT (θ A m) s) (pre s) post) (H s)).
    - exact (proj2 (le_wpOverPure (runStateT (θ A m) s) (pre s) post) (H s)).
  Qed.
End WPTypings.

Section SPTypings.
  Context {M : Type -> Type}.

  Context {S : Type}.

  Theorem triple_over_aspSt (θ : forall A, M A -> ASPSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Over pre post
    <-> ordASPSt (θ A m) (aspOver (fun p : unit * S => pre (snd p)) post).
  Proof. exact (le_aspOver (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_under_dslpSt (θ : forall A, M A -> DSLPSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Under pre post
    <-> ordDSLPSt (dslpUnder (fun p : unit * S => pre (snd p)) post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) (fun p => pre (snd p)) post). Qed.
End SPTypings.

(** ** No index at all

    A computation with a prescribed relation between start states and
    results, which may also diverge. *)
Definition progOf {S A} (R : S -> A * S -> Prop) : stdivndNE S A :=
  mkStateT (fun s =>
    exist _
      (@mkOptionT SetM _
         (fun o : option (A * S) =>
            match o with Some r => R s r | None => True end))
      (ex_intro _ None I)).

Lemma progOf_out {S A} (R : S -> A * S -> Prop) (s : S) (r : A * S) :
  outSt (progOf R) s (Some r) <-> R s r.
Proof. reflexivity. Qed.

(** The typings with state, as inclusions into the outcomes. *)
Lemma aspSt_typing_op {S A} (w : ASPSt S A) (m : stdivndNE S A) :
  ordASPSt w (aspSt m)
  <-> (forall s r, aspRel w (tt, s) r -> outSt m s (Some r)).
Proof.
  etransitivity;
    [ exact (le_relASP w (fun us r => outSt m (snd us) (Some r))) |].
  split.
  - intros H s r Hw. exact (H (tt, s) r Hw).
  - intros H [[] s] r Hw. exact (H s r Hw).
Qed.

Lemma dslpSt_typing {S A} (m : stdivndNE S A) (w : DSLPSt S A) :
  ordDSLPSt (dslpSt m) w
  <-> (forall s r, dslpRel w (tt, s) r -> outSt m s (Some r)).
Proof.
  etransitivity;
    [ exact (relDSLP_le (fun us r => outSt m (snd us) (Some r)) w) |].
  split.
  - intros H s r Hw. exact (H (tt, s) r Hw).
  - intros H [[] s] r Hw. exact (H s r Hw).
Qed.

(** The negative results hold at any state type with two distinct states
    and any inhabited result type, which is what the paper's lemma assumes.
    A result [r0] of [A * S] supplies the inhabitant. *)
Section NoIndex.
  Context (S A : Type) (s0 s1 : S) (Hne : s0 <> s1) (r0 : A * S).

  (** Three computations: [r0] is reached from [s0] by the first, from
      [s1] by the second, and by the third from nowhere. *)
  Definition reachFromS0 : stdivndNE S A :=
    progOf (fun s (r : A * S) => s = s0 /\ r = r0).
  Definition reachFromS1 : stdivndNE S A :=
    progOf (fun s (r : A * S) => s = s1 /\ r = r0).
  Definition reachNothing : stdivndNE S A :=
    progOf (fun (_ : S) (_ : A * S) => False).

  (** A typing is an inclusion of relations, so the computations typed by
      one index are closed under intersection of their relations.  The ASP
      [Under] triple is not: the first two computations satisfy it and the
      third, whose relation is their intersection, does not.  So no index
      has the triple as its typings.  This is a fact about the order of the
      ASP monad, not about the Dijkstra construction. *)
  Theorem no_asp_under_index :
    ~ exists w : ASPSt S A,
        forall m : stdivndNE S A,
          ordASPSt w (aspSt m) <->
          triple (@aspSt S) m Under
            (fun _ => True) (fun r : A * S => r = r0).
  Proof.
    intros [w Hiff].
    assert (H1 : ordASPSt w (aspSt reachFromS0)).
    { apply (proj2 (Hiff reachFromS0)). intros r Hr.
      exists (tt, s0). split; [ exact I | exact (conj eq_refl Hr) ]. }
    assert (H2 : ordASPSt w (aspSt reachFromS1)).
    { apply (proj2 (Hiff reachFromS1)). intros r Hr.
      exists (tt, s1). split; [ exact I | exact (conj eq_refl Hr) ]. }
    pose proof (proj1 (aspSt_typing_op w reachFromS0) H1) as R1.
    pose proof (proj1 (aspSt_typing_op w reachFromS1) H2) as R2.
    assert (H0 : ordASPSt w (aspSt reachNothing)).
    { apply (proj2 (aspSt_typing_op w reachNothing)). intros s r Hw.
      destruct (R1 s r Hw) as [E1 _]. destruct (R2 s r Hw) as [E2 _].
      exact (Hne (eq_trans (eq_sym E1) E2)). }
    destruct (proj1 (Hiff reachNothing) H0 r0 eq_refl) as [[[] s] [_ Hr]].
    exact Hr.
  Qed.

  (** The same for the DSLP [Over] triple, at the complements: the result
      [r0] must be reached from somewhere. *)
  Theorem no_dslp_over_index :
    ~ exists w : DSLPSt S A,
        forall m : stdivndNE S A,
          ordDSLPSt (dslpSt m) w <->
          triple (@dslpSt S) m Over
            (fun _ => False) (fun r : A * S => r <> r0).
  Proof.
    intros [w Hiff].
    assert (H1 : ordDSLPSt (dslpSt reachFromS0) w).
    { apply (proj2 (Hiff reachFromS0)). intros r Hd E. subst r.
      exact (Hd (tt, s0) (conj eq_refl eq_refl)). }
    assert (H2 : ordDSLPSt (dslpSt reachFromS1) w).
    { apply (proj2 (Hiff reachFromS1)). intros r Hd E. subst r.
      exact (Hd (tt, s1) (conj eq_refl eq_refl)). }
    pose proof (proj1 (dslpSt_typing reachFromS0 w) H1) as R1.
    pose proof (proj1 (dslpSt_typing reachFromS1 w) H2) as R2.
    assert (H0 : ordDSLPSt (dslpSt reachNothing) w).
    { apply (proj2 (dslpSt_typing reachNothing w)). intros s r Hw.
      destruct (R1 s r Hw) as [E1 _]. destruct (R2 s r Hw) as [E2 _].
      exact (Hne (eq_trans (eq_sym E1) E2)). }
    exact (proj1 (Hiff reachNothing) H0 r0 (fun us Hr => Hr) eq_refl).
  Qed.
End NoIndex.
