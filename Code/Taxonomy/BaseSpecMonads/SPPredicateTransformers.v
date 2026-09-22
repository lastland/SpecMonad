From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
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

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

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



Section SPStMonotone.
  Variable S : Type.

  (* A stateful forward predicate transformer is monotone when it
    is order-preserving as a map from (S -> Prop) to (A × S -> Prop)
    (with pointwise order inherited from Prop) *)
  Definition SPStMonotone  {A} `(sp : @SPSt S A) :=
    forall (pre pre' : S -> Prop) r, (forall s, pre s -> pre' s) -> sp pre r -> sp pre' r.

  (* The (angelic) monadic operations on stateful forward predicate
    transformers (SPSt) lift to monotone forward predicate transformers *)
  Definition SPStMon A := { sp : @SPSt S A | SPStMonotone sp }.

  #[program]
  Definition ret {A} (a : A) : SPStMon A := fun pre r => pre (snd r) /\ fst r = a.
  Next Obligation. red. intuition. Qed.

  #[program]
  Definition bind {A B} (m : SPStMon A) (f : A -> SPStMon B) : SPStMon B :=
    fun pre r => exists a si, m pre (a, si) /\ f a (fun s' => s' = si) r.
  Next Obligation.
    red. intros * ? (? & ? & ? & ?); eexists _, _; intuition eauto.
    eapply (proj2_sig m); eassumption.
  Qed.

  (* We lift the usual pointwise order on forward predicate transformers to
    monotone forward predicate transformers.
    The bind operation is monotone in both arguments with respect to this order. *)
  #[program]
  Definition ordSPStMon {A} (m m' : SPStMon A) := forall pre r, m pre r -> m' pre r.
  Notation "m ≦ m'" := (ordSPStMon m m') (at level 70).
  Notation "m ≈ m'" := (ordSPStMon m m' /\ ordSPStMon m' m).

  Lemma bind_monotone {A B} (m m' : SPStMon A) (f f' : A -> SPStMon B) :
    m ≦ m' -> (forall a, f a ≦ f' a) -> bind m f ≦ bind m' f'.
  Proof.
    intros hm hf pre r (a&si&?&?); exists a, si; split.
    1: now apply hm.
    now apply hf.
  Qed.

  (* These operations satisfy the right unitality and associativity from the usual monadic laws,
    but not the left unitality. In the latter case, we can however retain an inequation. *)

  Lemma runit {A} (m : SPStMon A) : bind m ret ≈ m.
  Proof.
    split; intros ??; cbn.
    - intros (?&?&?&?&?); subst; now rewrite surjective_pairing.
    - intros ?. exists (fst r), (snd r). rewrite <-surjective_pairing.
      easy.
  Qed.

  Lemma assoc {A B C} (m : SPStMon A) (f : A -> SPStMon B) (g : B -> SPStMon C) :
    bind m (fun a => bind (f a) g) ≈ bind (bind m f) g.
  Proof.
    split; intros ??; cbn.
    - intros (a & s1 & hm & b & s2 & hf & hg).
      exists b, s2; split; [|assumption].
      exists a, s1; now split.
    - intros (b & s2 & (a & s1 & hm & hf) & hg).
      exists a, s1; split; [assumption|].
      exists b, s2; now split.
  Qed.

  Lemma lunit {A B} (a : A) (f : A -> SPStMon B) : bind (ret a) f ≦ f a.
  Proof. intros ?? (?&?& [] &?); cbn in *; subst.
    revert H1; apply (proj2_sig (f a)).
    intros; subst; easy.
  Qed.

  Definition inhabited (X : Type) := exists x : X, True.

  Lemma lunitStrictlyLax  : inhabited S -> exists A B (a : A) (f : A -> SPStMon B), ~(f a ≦ bind (ret a) f).
  Proof.
    intros [s0]. unshelve eexists unit, unit, tt, (fun _ => exist _ (fun _ _ => True) _).
    - constructor.
    - intros h. now destruct (h (fun _ => False) (tt, s0) I) as (?&?& [] & ?).
  Qed.

End SPStMonotone.