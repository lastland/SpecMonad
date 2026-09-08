From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.

(** * Nondeterministic, possibly divergent stateful computations

    Same carrier as [stexcnd]: [stateT S (optionT SetM)], whose payload is
    [S -> option (A * S) -> Prop] — a SET of outcomes for each initial state.
    What differs is the reading of the distinguished outcome [None]:

      - in [stexcnd] it is a raised EXCEPTION ([MonadExc__stexcnd]);
      - here it is DIVERGENCE.

    Nothing in the type distinguishes the two; what fixes the meaning is which
    operations are offered.  So this module deliberately provides NO [MonadExc]
    instance — [catch] would be "recover from divergence", which is not an
    observable operation — and instead provides [divergeD], the everywhere-
    divergent program.

    [None] is absorbing under [bind] (see [outcomes_bind] in
    [NonDetObservationNew]), which is exactly the propagation rule divergence
    needs, so the monad structure is unchanged. *)

Section StDivNonDet.

  Variable S : Type.

  Definition stdivnd A := stateT S (optionT SetM) A.

  #[local] Existing Instance Monad_stateT.

  Definition retD {A} (a : A) : stdivnd A :=
    @ret (stateT _ _) _ _ a.

  Definition bindD {A B} (m : stdivnd A) (k : A -> stdivnd B) : stdivnd B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__stdivnd : Monad stdivnd :=
    {| ret := fun _ => @retD _ ;
       bind := fun _ _ => @bindD _ _ |}.

  Definition getD : stdivnd S :=
    @get _ (stateT _ _) _.

  Definition putD (s : S) : stdivnd unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__stdivnd : MonadState S stdivnd :=
    {| get := getD ;
       put := putD |}.

  (** The everywhere-divergent program: from every state its only outcome is
      the divergence token. *)
  Definition divergeD {A} : stdivnd A :=
    mkStateT (fun _ => @mkOptionT SetM _ (fun oa => oa = None)).

  (** Nondeterministic choice: union of outcome sets. *)
  Definition orD {A} (m1 m2 : stdivnd A) : stdivnd A :=
    mkStateT (fun s =>
      @mkOptionT SetM _ (fun oa =>
        unOptionT (runStateT m1 s) oa \/
        unOptionT (runStateT m2 s) oa)).

  (** [m] may diverge from [s]. *)
  Definition mayDiverge {A} (m : stdivnd A) (s : S) : Prop :=
    unOptionT (runStateT m s) None.

  (** ** The non-empty fragment

      Nothing in [stdivnd] forces the outcome set to be inhabited: the
      everywhere-blocking program [mkStateT (fun _ => mkOptionT (fun _ => False))]
      is a well-typed element with no outcomes at all — it neither terminates
      nor diverges.  Every program built from the operations above does have an
      outcome from every state, so that is carved out here as a subset type:
      side conditions of the form [exists oa, unOptionT (runStateT m s) oa]
      become part of the carrier instead of hypotheses on each theorem. *)

  Definition nonEmptyOutcomes {A} (m : stdivnd A) : Prop :=
    forall s, exists oa, unOptionT (runStateT m s) oa.

  Definition stdivndNE (A : Type) : Type := { m : stdivnd A | nonEmptyOutcomes m }.

  Definition getNE {A} (m : stdivndNE A) : stdivnd A := proj1_sig m.

  Lemma getNE_nonEmpty {A} (m : stdivndNE A) : nonEmptyOutcomes (getNE m).
  Proof. exact (proj2_sig m). Qed.

  (** Closure of [nonEmptyOutcomes] under each operation. *)

  Lemma nonEmpty_retD {A} (a : A) : nonEmptyOutcomes (retD a).
  Proof. intro s. exists (Some (a, s)). cbn. reflexivity. Qed.

  Lemma nonEmpty_getD : nonEmptyOutcomes getD.
  Proof. intro s. exists (Some (s, s)). cbn. reflexivity. Qed.

  Lemma nonEmpty_putD (s' : S) : nonEmptyOutcomes (putD s').
  Proof. intro s. exists (Some (tt, s')). cbn. reflexivity. Qed.

  Lemma nonEmpty_divergeD {A} : nonEmptyOutcomes (divergeD : stdivnd A).
  Proof. intro s. exists None. cbn. reflexivity. Qed.

  Lemma nonEmpty_orD {A} (m1 m2 : stdivnd A) :
    nonEmptyOutcomes m1 -> nonEmptyOutcomes (orD m1 m2).
  Proof.
    intros H s. destruct (H s) as [oa Ho]. exists oa. cbn. left. exact Ho.
  Qed.

  Lemma nonEmpty_bindD {A B} (m : stdivnd A) (k : A -> stdivnd B) :
    nonEmptyOutcomes m -> (forall a, nonEmptyOutcomes (k a)) ->
    nonEmptyOutcomes (bindD m k).
  Proof.
    intros Hm Hk s. destruct (Hm s) as [[[a s']|] Ho].
    - destruct (Hk a s') as [ob Hob]. exists ob. cbn.
      exists (Some (a, s')). split; [ exact Ho | exact Hob ].
    - exists None. cbn. exists None. split; [ exact Ho | reflexivity ].
  Qed.

  (** The operations, lifted to the subset type. *)

  Definition retNE {A} (a : A) : stdivndNE A :=
    exist _ (retD a) (nonEmpty_retD a).

  Definition bindNE {A B} (m : stdivndNE A) (k : A -> stdivndNE B) : stdivndNE B :=
    exist _ (bindD (getNE m) (fun a => getNE (k a)))
            (nonEmpty_bindD (getNE m) (fun a => getNE (k a))
               (getNE_nonEmpty m) (fun a => getNE_nonEmpty (k a))).

  #[global]
    Instance Monad__stdivndNE : Monad stdivndNE :=
    {| ret := fun _ => @retNE _ ;
       bind := fun _ _ => @bindNE _ _ |}.

  Definition getStNE : stdivndNE S := exist _ getD nonEmpty_getD.

  Definition putStNE (s' : S) : stdivndNE unit :=
    exist _ (putD s') (nonEmpty_putD s').

  #[global]
    Instance MonadState__stdivndNE : MonadState S stdivndNE :=
    {| get := getStNE ;
       put := putStNE |}.

  Definition divergeNE {A} : stdivndNE A :=
    exist _ divergeD nonEmpty_divergeD.

  Definition orNE {A} (m1 m2 : stdivndNE A) : stdivndNE A :=
    exist _ (orD (getNE m1) (getNE m2)) (nonEmpty_orD _ _ (getNE_nonEmpty m1)).

  (** [m] may diverge from [s], on the non-empty fragment. *)
  Definition mayDivergeNE {A} (m : stdivndNE A) (s : S) : Prop :=
    mayDiverge (getNE m) s.

End StDivNonDet.

Arguments stdivnd _ _.
Arguments divergeD {_} {_}.
Arguments orD {_} {_}.
Arguments mayDiverge {_} {_}.

Arguments stdivndNE _ _.
Arguments getNE {_} {_}.
Arguments retNE {_} {_}.
Arguments bindNE {_} {_} {_}.
Arguments divergeNE {_} {_}.
Arguments orNE {_} {_}.
Arguments nonEmptyOutcomes {_} {_}.
Arguments mayDivergeNE {_} {_}.

(* ================================================================= *)
(** * Facts and laws (merged from NonDetDivProgFacts.v)                          *)
(* ================================================================= *)

(** * Monad laws for the non-empty fragment [stdivndNE]

    [stdivndNE S A = { m : stdivnd S A | nonEmptyOutcomes m }] carries the
    operations of [stdivnd] unchanged — [proj1_sig] of [retNE] / [bindNE] is
    [retD] / [bindD] definitionally — so every law is the corresponding law of
    [stdivnd], transported along [getNE].

    [stdivnd S = stateT S (optionT SetM)] gets its own laws from the generic
    [stateT] and [optionT] instances in [Prog], via [SetM]'s in
    [StExcNonDet]. *)

From Coq Require Import Morphisms.
From ITree Require Import Basics.Monad.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivITree.

Section StDivNonDet.

  Variable S : Type.

  (** Laws for the underlying [stdivnd], i.e. for [stateT S (optionT SetM)]. *)

  Definition Eq1__stdivnd : Eq1 (stdivnd S) :=
    Eq1_stateT S (optionT SetM).

  Definition Eq1Equivalence__stdivnd
    : @Eq1Equivalence (stdivnd S) _ Eq1__stdivnd :=
    Eq1Equivalence_stateT S (optionT SetM).

  Definition MonadLawsE__stdivnd
    : @MonadLawsE (stdivnd S) _ (Monad__stdivnd S) :=
    MonadLawsE_stateT S (optionT SetM).

  (** Equality on the subset type is equality of the underlying programs. *)

  #[global]
    Instance Eq1__stdivndNE : Eq1 (stdivndNE S) :=
    fun A m n => Eq1__stdivnd A (getNE m) (getNE n).

  #[global]
    Instance Eq1Equivalence__stdivndNE
    : @Eq1Equivalence (stdivndNE S) _ Eq1__stdivndNE.
  Proof.
    intro A. destruct (Eq1Equivalence__stdivnd A) as [Erefl Esym Etrans].
    constructor.
    - intro x. exact (Erefl (getNE x)).
    - intros x y H. exact (Esym _ _ H).
    - intros x y z H1 H2. exact (Etrans _ _ _ H1 H2).
  Qed.

  #[global]
    Instance MonadLawsE__stdivndNE
    : @MonadLawsE (stdivndNE S) Eq1__stdivndNE (Monad__stdivndNE S).
  Proof.
    destruct MonadLawsE__stdivnd as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => getNE (f a)) x).
    - intros A x. exact (Lbrr A (getNE x)).
    - intros A B C x f g.
      exact (Lbb A B C (getNE x) (fun a => getNE (f a)) (fun b => getNE (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (getNE x) (getNE y) Hxy
               (fun a => getNE (f a)) (fun a => getNE (g a)) Hfg).
  Qed.

End StDivNonDet.
