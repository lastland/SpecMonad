(** * The four healthiness conditions, stated once

    Both the SP and the WP side carve their monads out of a predicate
    transformer by the same four conditions — strict, terminating, conjunctive,
    disjunctive.  This file states them for the shape the two families have in
    common,

      [PT I := (I -> Prop) -> Prop]

    a transformer taking a predicate over [I] to a [Prop].  Both are instances:

      - [WPureT A = (A -> Prop) -> Prop] IS [PT A], on the nose: there the
        predicate argument is the POSTCONDITION.

      - [SPStExc S A = (S -> Prop) -> option (A * S) -> Prop] is a FAMILY of
        [PT S], one per outcome: there it is the PRECONDITION.
        [SPPredicateTransformers.v] proves the bridge lemmas
        ([StrictProg_pointwise] and friends).

    The four PAIRINGS are shared too, and they are what the monads are cut out
    by — see [AngelicTotal] … [AngelicLiberal] below.

    What is *not* shared is behaviour under [bind].  On the WP side [bind] is
    continuation composition ([bindPT]) and all four conditions are closed
    under it ([Strict_bindPT] … [Disjunctive_bindPT]).  On the SP side [bind]
    is a forward pass over the precondition, under which only the two unmixed
    pairings survive; [DSPStExc] and [ASLPStExc] must instead recover the
    underlying relation.  The asymmetry is one of variance: the postcondition
    slot is where the continuation composes, the precondition slot is upstream
    of it. *)

From Coq Require Import Morphisms RelationClasses.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Definition PT (I : Type) : Type := (I -> Prop) -> Prop.

(** Predicate extensionality, as [SPPredicateTransformers.v]'s [predExt]. *)
Lemma predExtI {I : Type} (P Q : I -> Prop) :
  (forall i, P i <-> Q i) -> P = Q.
Proof.
  intro H. apply functional_extensionality. intro i.
  apply propositional_extensionality. exact (H i).
Qed.

Section Conditions.
  Context {I : Type}.

  Definition MonoPT (w : PT I) : Prop :=
    forall p q : I -> Prop, (forall i, p i -> q i) -> w p -> w q.

  Definition Strict (w : PT I) : Prop := ~ w (fun _ => False).

  Definition Terminating (w : PT I) : Prop := w (fun _ => True).

  Definition Conjunctive (w : PT I) : Prop :=
    forall (K : Type), inhabited K ->
    forall (p : K -> I -> Prop),
      w (fun i => forall k, p k i) <-> forall k, w (p k).

  Definition Disjunctive (w : PT I) : Prop :=
    forall (K : Type), inhabited K ->
    forall (p : K -> I -> Prop),
      w (fun i => exists k, p k i) <-> exists k, w (p k).

  (** Either connective already forces monotonicity — via [P = P /\ Q] and
      [Q = P \/ Q] respectively — so the pairings below never carry it
      separately.  Both use predicate extensionality, exactly as the SP-side
      proofs do. *)

  Theorem Conjunctive_MonoPT (w : PT I) : Conjunctive w -> MonoPT w.
  Proof.
    intros HC p q Hsub Hw.
    assert (Heq : p = (fun i => forall b : bool, if b then p i else q i)).
    { apply predExtI. intro i. split.
      - intros Hp [|]; [ exact Hp | exact (Hsub i Hp) ].
      - intro H. exact (H true). }
    rewrite Heq in Hw.
    exact (proj1 (HC bool (inhabits true)
                    (fun b i => if b then p i else q i)) Hw false).
  Qed.

  Theorem Disjunctive_MonoPT (w : PT I) : Disjunctive w -> MonoPT w.
  Proof.
    intros HD p q Hsub Hw.
    assert (Heq : q = (fun i => exists b : bool, if b then p i else q i)).
    { apply predExtI. intro i. split.
      - intro Hq. exists false. exact Hq.
      - intros [[|] H]; [ exact (Hsub i H) | exact H ]. }
    rewrite Heq.
    apply (proj2 (HD bool (inhabits true) (fun b i => if b then p i else q i))).
    exists true. exact Hw.
  Qed.

  (** ** The four pairings

      Named for the reading each one gives.  [Strict] is the total/excluded-
      miracle end, [Terminating] the liberal end; [Disjunctive] is angelic,
      [Conjunctive] demonic. *)

  Definition AngelicTotal   (w : PT I) : Prop := Strict w      /\ Disjunctive w.
  Definition DemonicLiberal (w : PT I) : Prop := Terminating w /\ Conjunctive w.
  Definition DemonicTotal   (w : PT I) : Prop := Strict w      /\ Conjunctive w.
  Definition AngelicLiberal (w : PT I) : Prop := Terminating w /\ Disjunctive w.

  Lemma AngelicTotal_mono   w : AngelicTotal   w -> MonoPT w.
  Proof. intros [_ H]. exact (Disjunctive_MonoPT w H). Qed.
  Lemma DemonicLiberal_mono w : DemonicLiberal w -> MonoPT w.
  Proof. intros [_ H]. exact (Conjunctive_MonoPT w H). Qed.
  Lemma DemonicTotal_mono   w : DemonicTotal   w -> MonoPT w.
  Proof. intros [_ H]. exact (Conjunctive_MonoPT w H). Qed.
  Lemma AngelicLiberal_mono w : AngelicLiberal w -> MonoPT w.
  Proof. intros [_ H]. exact (Disjunctive_MonoPT w H). Qed.

End Conditions.

(* ================================================================= *)
(** * Closure under the continuation monad structure                  *)
(* ================================================================= *)

(** [PT] is the continuation monad at [Prop].  This is the structure the WP
    side uses; the SP side does NOT, which is the whole source of the
    asymmetry documented at the top of this file. *)

Definition retPT {A} (a : A) : PT A := fun p => p a.

Definition bindPT {A B} (m : PT A) (k : A -> PT B) : PT B :=
  fun p => m (fun a => k a p).

Section RetClosure.
  Context {A : Type}.

  Lemma Strict_retPT      (a : A) : Strict      (retPT a).
  Proof. intros []. Qed.
  Lemma Terminating_retPT (a : A) : Terminating (retPT a).
  Proof. exact I. Qed.
  Lemma Conjunctive_retPT (a : A) : Conjunctive (retPT a).
  Proof. intros K _ p. unfold retPT. split; intros H k; exact (H k). Qed.
  Lemma Disjunctive_retPT (a : A) : Disjunctive (retPT a).
  Proof. intros K _ p. unfold retPT. split; intros [k H]; exists k; exact H. Qed.
End RetClosure.

Section BindClosure.
  Context {A B : Type}.
  Variable m : PT A.
  Variable k : A -> PT B.
  Hypothesis Hm : MonoPT m.

  Lemma Strict_bindPT :
    Strict m -> (forall a, Strict (k a)) -> Strict (bindPT m k).
  Proof.
    intros Hs Hk H. apply Hs.
    exact (Hm (fun a => k a (fun _ => False)) (fun _ => False)
             (fun a Ha => Hk a Ha) H).
  Qed.

  Lemma Terminating_bindPT :
    Terminating m -> (forall a, Terminating (k a)) -> Terminating (bindPT m k).
  Proof.
    intros Ht Hk. unfold bindPT.
    exact (Hm (fun _ => True) (fun a => k a (fun _ => True))
             (fun a _ => Hk a) Ht).
  Qed.

  Lemma Conjunctive_bindPT :
    Conjunctive m -> (forall a, Conjunctive (k a)) -> Conjunctive (bindPT m k).
  Proof.
    intros Hc Hk K HK p. unfold bindPT. split.
    - intro H. apply (Hc K HK (fun j a => k a (p j))).
      exact (Hm (fun a => k a (fun b => forall j, p j b))
               (fun a => forall j, k a (p j))
               (fun a Ha => proj1 (Hk a K HK p) Ha) H).
    - intro H.
      pose proof (proj2 (Hc K HK (fun j a => k a (p j))) H) as H'.
      exact (Hm (fun a => forall j, k a (p j))
               (fun a => k a (fun b => forall j, p j b))
               (fun a Ha => proj2 (Hk a K HK p) Ha) H').
  Qed.

  Lemma Disjunctive_bindPT :
    Disjunctive m -> (forall a, Disjunctive (k a)) -> Disjunctive (bindPT m k).
  Proof.
    intros Hd Hk K HK p. unfold bindPT. split.
    - intro H. apply (Hd K HK (fun j a => k a (p j))).
      exact (Hm (fun a => k a (fun b => exists j, p j b))
               (fun a => exists j, k a (p j))
               (fun a Ha => proj1 (Hk a K HK p) Ha) H).
    - intro H.
      pose proof (proj2 (Hd K HK (fun j a => k a (p j))) H) as H'.
      exact (Hm (fun a => exists j, k a (p j))
               (fun a => k a (fun b => exists j, p j b))
               (fun a Ha => proj2 (Hk a K HK p) Ha) H').
  Qed.

End BindClosure.

(** The four pairings inherit closure, componentwise. *)
Section PairingClosure.
  Context {A B : Type}.
  Variable m : PT A.
  Variable k : A -> PT B.

  Lemma AngelicTotal_bindPT :
    AngelicTotal m -> (forall a, AngelicTotal (k a)) ->
    AngelicTotal (bindPT m k).
  Proof.
    intros [Hs Hd] Hk. pose proof (Disjunctive_MonoPT m Hd) as Hm. split.
    - exact (Strict_bindPT m k Hm Hs (fun a => proj1 (Hk a))).
    - exact (Disjunctive_bindPT m k Hm Hd (fun a => proj2 (Hk a))).
  Qed.

  Lemma DemonicLiberal_bindPT :
    DemonicLiberal m -> (forall a, DemonicLiberal (k a)) ->
    DemonicLiberal (bindPT m k).
  Proof.
    intros [Ht Hc] Hk. pose proof (Conjunctive_MonoPT m Hc) as Hm. split.
    - exact (Terminating_bindPT m k Hm Ht (fun a => proj1 (Hk a))).
    - exact (Conjunctive_bindPT m k Hm Hc (fun a => proj2 (Hk a))).
  Qed.

  Lemma DemonicTotal_bindPT :
    DemonicTotal m -> (forall a, DemonicTotal (k a)) ->
    DemonicTotal (bindPT m k).
  Proof.
    intros [Hs Hc] Hk. pose proof (Conjunctive_MonoPT m Hc) as Hm. split.
    - exact (Strict_bindPT m k Hm Hs (fun a => proj1 (Hk a))).
    - exact (Conjunctive_bindPT m k Hm Hc (fun a => proj2 (Hk a))).
  Qed.

  Lemma AngelicLiberal_bindPT :
    AngelicLiberal m -> (forall a, AngelicLiberal (k a)) ->
    AngelicLiberal (bindPT m k).
  Proof.
    intros [Ht Hd] Hk. pose proof (Disjunctive_MonoPT m Hd) as Hm. split.
    - exact (Terminating_bindPT m k Hm Ht (fun a => proj1 (Hk a))).
    - exact (Disjunctive_bindPT m k Hm Hd (fun a => proj2 (Hk a))).
  Qed.

End PairingClosure.
