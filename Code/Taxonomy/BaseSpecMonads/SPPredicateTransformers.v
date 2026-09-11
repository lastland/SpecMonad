From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

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
(** * Terminating-slice variant (factored out of SPSimplerSpecMonads.v) *)
(* ================================================================= *)


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
      empty meet — i.e. termination — plays no part. *)
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
      empty meet — i.e. termination — plays no part. *)
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
