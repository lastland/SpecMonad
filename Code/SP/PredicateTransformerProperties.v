(** * Predicate-transformer properties from refinement calculus.

    Strictness, termination, conjunctivity, and disjunctivity follow
    Ralph-Johan Back and Joakim von Wright, [Refinement Calculus: A
    Systematic Introduction], Springer, 1998, section 16.1
    (https://doi.org/10.1007/978-1-4612-1674-2).

    Conjunctive and disjunctive transformers preserve arbitrary nonempty
    indexed meets and joins, respectively.  Universally conjunctive and
    universally disjunctive transformers also preserve the empty families.
    The empty meet is [True], so termination supplies that case; the empty
    join is [False], so strictness supplies that case.  The full-preservation
    lemmas below establish these two combinations constructively.

    These properties characterize healthy SP transformer classes.  In the forward
    SP interpretation, [TerminatingArr] means top preservation; it is not
    itself a claim about program termination. *)

From Coq Require Import FunctionalExtensionality PropExtensionality.

(** Healthiness conditions for arbitrary input and output types. *)
Section ArrowPredicateTransformers.
  Context {A B : Type}.

  Definition StrictArr (w : (A -> Prop) -> B -> Prop) : Prop :=
    forall b, ~ w (fun _ => False) b.

  Definition TerminatingArr (w : (A -> Prop) -> B -> Prop) : Prop :=
    forall b, w (fun _ => True) b.

  Definition ConjunctiveArr (w : (A -> Prop) -> B -> Prop) : Prop :=
    forall I : Type, inhabited I -> forall (p : I -> A -> Prop) b,
      w (fun a => forall i, p i a) b <-> forall i, w (p i) b.

  Definition DisjunctiveArr (w : (A -> Prop) -> B -> Prop) : Prop :=
    forall I : Type, inhabited I -> forall (p : I -> A -> Prop) b,
      w (fun a => exists i, p i a) b <-> exists i, w (p i) b.

  Lemma conjunctiveArr_monotone (w : (A -> Prop) -> B -> Prop) :
    ConjunctiveArr w ->
    forall P Q b, (forall a, P a -> Q a) -> w P b -> w Q b.
  Proof.
    intros HC P Q b HPQ Hw.
    assert (HE : P = (fun a => forall i : bool, if i then P a else Q a)).
    { extensionality a. apply propositional_extensionality. split.
      - intros HP [|]; [exact HP | exact (HPQ a HP)].
      - intro H. exact (H true). }
    rewrite HE in Hw.
    exact (proj1 (HC bool (inhabits true)
      (fun i a => if i then P a else Q a) b) Hw false).
  Qed.

  Lemma disjunctiveArr_monotone (w : (A -> Prop) -> B -> Prop) :
    DisjunctiveArr w ->
    forall P Q b, (forall a, P a -> Q a) -> w P b -> w Q b.
  Proof.
    intros HD P Q b HPQ Hw.
    assert (HE : Q = (fun a => exists i : bool, if i then P a else Q a)).
    { extensionality a. apply propositional_extensionality. split.
      - intro HQ. exists false. exact HQ.
      - intros [[|] H]; [exact (HPQ a H) | exact H]. }
    rewrite HE. apply (HD bool (inhabits true)
      (fun i a => if i then P a else Q a) b).
    exists true. exact Hw.
  Qed.

  (** Padding with [None] makes the family inhabited constructively,
      including when [I] itself is empty. *)
  Lemma strict_disjunctiveArr_full_join (w : (A -> Prop) -> B -> Prop) :
    StrictArr w -> DisjunctiveArr w ->
    forall (I : Type) (p : I -> A -> Prop) b,
      w (fun a => exists i, p i a) b <-> exists i, w (p i) b.
  Proof.
    intros HS HD I p b.
    assert (HE : (fun a => exists i, p i a) =
      (fun a => exists i : option I,
        match i with Some i => p i a | None => False end)).
    { extensionality a. apply propositional_extensionality. split.
      - intros [i H]. exists (Some i). exact H.
      - intros [[i|] H]; [exists i; exact H | contradiction]. }
    rewrite HE, (HD (option I) (inhabits None)).
    split.
    - intros [[i|] H]; [exists i; exact H | exfalso; exact (HS b H)].
    - intros [i H]. exists (Some i). exact H.
  Qed.

  Lemma terminating_conjunctiveArr_full_meet
    (w : (A -> Prop) -> B -> Prop) :
    TerminatingArr w -> ConjunctiveArr w ->
    forall (I : Type) (p : I -> A -> Prop) b,
      w (fun a => forall i, p i a) b <-> forall i, w (p i) b.
  Proof.
    intros HT HC I p b.
    assert (HE : (fun a => forall i, p i a) =
      (fun a => forall i : option I,
        match i with Some i => p i a | None => True end)).
    { extensionality a. apply propositional_extensionality. split.
      - intros H [i|]; [exact (H i) | constructor].
      - intros H i. exact (H (Some i)). }
    rewrite HE, (HC (option I) (inhabits None)).
    split.
    - intros H i. exact (H (Some i)).
    - intros H [i|]; [exact (H i) | exact (HT b)].
  Qed.
End ArrowPredicateTransformers.
