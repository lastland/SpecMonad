From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

From Incorrectness.Taxonomy.BaseSpecMonads Require Import Healthiness.

Import MonadNotation.
Open Scope monad_scope.

Section BasePredicateTransformers.
  Definition SPPure (A : Type) : Type := Prop -> A -> Prop.

  Variable S : Type.
  
  Definition SPSt (A : Type) : Type := (S -> Prop) -> (A * S) -> Prop.

  Definition SPStExc (A : Type) : Type := (S -> Prop) -> option (A * S) -> Prop.
End BasePredicateTransformers.

Arguments SPSt {_}.
Arguments SPStExc {_}.
                                                                
Section PurePredicateTransformers.
  Definition Strict {A} (w : SPPure A) : Prop :=
    forall (a : A), ~ w False a.

  Definition Terminating {A} (w : SPPure A) : Prop :=
    forall (a : A), w True a.

  Definition Conjunctive {A} (w : SPPure A) : Prop :=
    forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
      w (forall i, p i) a <-> forall i, w (p i) a.

  Definition Disjunctive {A} (w : SPPure A) : Prop :=
    forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
      w (exists i, p i) a <-> exists i, w (p i) a.
End PurePredicateTransformers.

Section ProgPredicateTransformers.
  Variable S : Type.

  Definition StrictProg {A} (w : SPStExc A) : Prop :=
    forall (r : option (A * S)), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : SPStExc A) : Prop :=
    forall (r : option (A * S)), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : SPStExc A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : SPStExc A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
End ProgPredicateTransformers.

(* ================================================================= *)
(** ** The SP conditions ARE the shared ones, lifted pointwise        *)
(* ================================================================= *)

(** [SPStExc S A] is a family of [PT S], one per outcome, and each [*Prog]
    condition is the corresponding condition of [Healthiness.v] holding at
    every outcome.  These bridges make the sharing with the WP side (where
    [WPureT A] IS [PT A]) a fact rather than an analogy.

    [SPPure] is the one carrier with no bridge: its precondition slot is a bare
    [Prop] rather than a predicate, so it is not of the form [PT I].  That is
    also why the pure SP refinement degenerates — see [SPHealthyMonads.v]. *)

Section SharedConditions.
  Variable S : Type.

  Theorem StrictProg_pointwise {A} (w : @SPStExc S A) :
    StrictProg S w <-> forall r, Healthiness.Strict (fun pre => w pre r).
  Proof. split; intros H r; exact (H r). Qed.

  Theorem TerminatingProg_pointwise {A} (w : @SPStExc S A) :
    TerminatingProg S w <-> forall r, Healthiness.Terminating (fun pre => w pre r).
  Proof. split; intros H r; exact (H r). Qed.

  Theorem ConjunctiveProg_pointwise {A} (w : @SPStExc S A) :
    ConjunctiveProg S w <-> forall r, Healthiness.Conjunctive (fun pre => w pre r).
  Proof.
    split.
    - intros H r K HK p. exact (H K HK p r).
    - intros H K HK p r. exact (H r K HK p).
  Qed.

  Theorem DisjunctiveProg_pointwise {A} (w : @SPStExc S A) :
    DisjunctiveProg S w <-> forall r, Healthiness.Disjunctive (fun pre => w pre r).
  Proof.
    split.
    - intros H r K HK p. exact (H K HK p r).
    - intros H K HK p r. exact (H r K HK p).
  Qed.

  (** Hence the SP carriers are cut out by the same four PAIRINGS the WP monads
      use: [ASPStExc] by [AngelicTotal], [DSLPStExc] by [DemonicLiberal],
      [DSPStExc] by [DemonicTotal], [ASLPStExc] by [AngelicLiberal]. *)

  Theorem ASP_pairing {A} (w : @SPStExc S A) :
    (StrictProg S w /\ DisjunctiveProg S w)
    <-> forall r, Healthiness.AngelicTotal (fun pre => w pre r).
  Proof.
    split.
    - intros [H1 H2] r.
      exact (conj (proj1 (StrictProg_pointwise w) H1 r)
                  (proj1 (DisjunctiveProg_pointwise w) H2 r)).
    - intro H. split.
      + apply StrictProg_pointwise. intro r. exact (proj1 (H r)).
      + apply DisjunctiveProg_pointwise. intro r. exact (proj2 (H r)).
  Qed.

  Theorem DSLP_pairing {A} (w : @SPStExc S A) :
    (TerminatingProg S w /\ ConjunctiveProg S w)
    <-> forall r, Healthiness.DemonicLiberal (fun pre => w pre r).
  Proof.
    split.
    - intros [H1 H2] r.
      exact (conj (proj1 (TerminatingProg_pointwise w) H1 r)
                  (proj1 (ConjunctiveProg_pointwise w) H2 r)).
    - intro H. split.
      + apply TerminatingProg_pointwise. intro r. exact (proj1 (H r)).
      + apply ConjunctiveProg_pointwise. intro r. exact (proj2 (H r)).
  Qed.

  Theorem DSP_pairing {A} (w : @SPStExc S A) :
    (StrictProg S w /\ ConjunctiveProg S w)
    <-> forall r, Healthiness.DemonicTotal (fun pre => w pre r).
  Proof.
    split.
    - intros [H1 H2] r.
      exact (conj (proj1 (StrictProg_pointwise w) H1 r)
                  (proj1 (ConjunctiveProg_pointwise w) H2 r)).
    - intro H. split.
      + apply StrictProg_pointwise. intro r. exact (proj1 (H r)).
      + apply ConjunctiveProg_pointwise. intro r. exact (proj2 (H r)).
  Qed.

  Theorem ASLP_pairing {A} (w : @SPStExc S A) :
    (TerminatingProg S w /\ DisjunctiveProg S w)
    <-> forall r, Healthiness.AngelicLiberal (fun pre => w pre r).
  Proof.
    split.
    - intros [H1 H2] r.
      exact (conj (proj1 (TerminatingProg_pointwise w) H1 r)
                  (proj1 (DisjunctiveProg_pointwise w) H2 r)).
    - intro H. split.
      + apply TerminatingProg_pointwise. intro r. exact (proj1 (H r)).
      + apply DisjunctiveProg_pointwise. intro r. exact (proj2 (H r)).
  Qed.

End SharedConditions.

(* ================================================================= *)
(** * Terminating-slice variant (factored out of SPSimplerSpecMonads.v) *)
(* ================================================================= *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

From Incorrectness.Taxonomy.BaseSpecMonads Require Import Healthiness.

Import MonadNotation.
Open Scope monad_scope.

Module StTrans.
Section Transformers.
  Variable S : Type.

  Definition StrictProg {A} (w : SPSt A) : Prop :=
    forall (r : A * S), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : SPSt A) : Prop :=
    forall (r : A * S), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : SPSt A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : A * S),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : SPSt A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : A * S),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.

End Transformers.


(* ---- orders and generic monotonicity ---- *)

Section StTransOrders.
  Variable S : Type.
  Definition ordSPSt {A} (m1 m2 : @SPSt S A) : Prop :=
    forall pre r, m1 pre r -> m2 pre r.
  (** Pointwise-equivalent preconditions are equal, so a transformer — an
      opaque function of the precondition — cannot tell them apart. *)
  Lemma predExt (X Y : S -> Prop) : (forall s, X s <-> Y s) -> X = Y.
  Proof.
    intro H. apply functional_extensionality. intro s.
    apply propositional_extensionality. exact (H s).
  Qed.

  (** Preserving NON-EMPTY meets already implies monotonicity: index the meet
      by [bool] over the pair {P, Q} and use [P = P /\ Q] when [P <= Q].  The
      empty meet — i.e. strictness — plays no part. *)
  Theorem conjunctive_implies_monotone {A} (w : SPSt A) :
    ConjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HC P Q r Hsub Hw.
    assert (Heq : P = (fun s => forall b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intros Hp [|]; [ exact Hp | exact (Hsub s Hp) ].
      - intro H. exact (H true). }
    rewrite Heq in Hw.
    exact (proj1 (HC bool (inhabits true)
                    (fun b s => if b then P s else Q s) r) Hw false).
  Qed.

  (** Dually, for non-empty joins, via [Q = P \/ Q]. *)
  Theorem disjunctive_implies_monotone {A} (w : SPSt A) :
    DisjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HD P Q r Hsub Hw.
    assert (Heq : Q = (fun s => exists b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intro Hq. exists false. exact Hq.
      - intros [[|] H]; [ exact (Hsub s H) | exact H ]. }
    rewrite Heq.
    apply (HD bool (inhabits true) (fun b s => if b then P s else Q s) r).
    exists true. exact Hw.
  Qed.
End StTransOrders.
Arguments ordSPSt {_} {_}.
End StTrans.

(* ================================================================= *)
(** * Refinement order on the raw transformers, and monotonicity *)
(* ================================================================= *)

Section SPOrders.
  Variable S : Type.
  Definition ordSPStExc {A} (m1 m2 : @SPStExc S A) : Prop :=
    forall pre r, m1 pre r -> m2 pre r.
  (** Pointwise-equivalent preconditions are equal, so a transformer — an
      opaque function of the precondition — cannot tell them apart. *)
  Lemma predExt (X Y : S -> Prop) : (forall s, X s <-> Y s) -> X = Y.
  Proof.
    intro H. apply functional_extensionality. intro s.
    apply propositional_extensionality. exact (H s).
  Qed.

  (** Preserving NON-EMPTY meets already implies monotonicity: index the meet
      by [bool] over the pair {P, Q} and use [P = P /\ Q] when [P <= Q].  The
      empty meet — i.e. strictness — plays no part. *)
  Theorem conjunctive_implies_monotone {A} (w : SPStExc A) :
    ConjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HC P Q r Hsub Hw.
    assert (Heq : P = (fun s => forall b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intros Hp [|]; [ exact Hp | exact (Hsub s Hp) ].
      - intro H. exact (H true). }
    rewrite Heq in Hw.
    exact (proj1 (HC bool (inhabits true)
                    (fun b s => if b then P s else Q s) r) Hw false).
  Qed.

  (** Dually, for non-empty joins, via [Q = P \/ Q]. *)
  Theorem disjunctive_implies_monotone {A} (w : SPStExc A) :
    DisjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HD P Q r Hsub Hw.
    assert (Heq : Q = (fun s => exists b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intro Hq. exists false. exact Hq.
      - intros [[|] H]; [ exact (Hsub s H) | exact H ]. }
    rewrite Heq.
    apply (HD bool (inhabits true) (fun b s => if b then P s else Q s) r).
    exists true. exact Hw.
  Qed.
End SPOrders.

Arguments ordSPStExc {_} {_}.
