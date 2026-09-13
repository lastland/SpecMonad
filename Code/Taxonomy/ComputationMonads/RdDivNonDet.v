From ExtLib Require Import Monad MonadReader ReaderMonad OptionMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet.

(** * Nondeterministic, possibly divergent computations in an environment

    [rddivnd R A = readerT R divnd A] assigns a set of outcomes to each
    environment.  Its unwrapped payload has type [R -> option A -> Prop],
    with [None] read as divergence.

    Unlike the stateful [stdivnd], this reader stack returns no final
    environment.  Their unwrapped payloads differ as follows:

      [stdivnd R A]  =  R -> option (A * R) -> Prop     (state: outcome carries R)
      [rddivnd R A]  =  R -> option  A      -> Prop     (reader: it does not)

    So this file offers [MonadReader] ([ask], [local]) where [StDivNonDet.v]
    offers [MonadState] ([get], [put]).

    As in [DivNonDet.v], the raw option type does not enforce this reading
    of [None].  The module supplies divergence operations and registers no
    exception instance: interpreting [catch] as recovery from divergence
    would conflict with the intended semantics.

    Operation names match the other computation monads ([retD], [bindD],
    [divergeD], [orD], …); references to the underlying [divnd] operations are
    written qualified, as [DivNonDet.divergeD] and so on. *)

Section RdDivNonDet.

  Variable R : Type.

  Definition rddivnd A := readerT R divnd A.

  #[local] Existing Instance Monad_readerT.

  Definition retD {A} (a : A) : rddivnd A :=
    @ret (readerT R divnd) _ _ a.

  Definition bindD {A B} (m : rddivnd A) (k : A -> rddivnd B) : rddivnd B :=
    @bind (readerT R divnd) _ _ _ m k.

  #[global]
    Instance Monad__rddivnd : Monad rddivnd :=
    {| ret := fun _ => @retD _ ;
       bind := fun _ _ => @bindD _ _ |}.

  Definition askD : rddivnd R :=
    @ask _ (readerT R divnd) _.

  Definition localD {A} (f : R -> R) (m : rddivnd A) : rddivnd A :=
    @local _ (readerT R divnd) _ _ f m.

  #[global]
    Instance MonadReader__rddivnd : MonadReader R rddivnd :=
    {| ask := askD ;
       local := fun _ => @localD _ |}.

  (** The everywhere-divergent program: in every environment its only outcome
      is the divergence token. *)
  Definition divergeD {A} : rddivnd A :=
    mkReaderT (fun _ => DivNonDet.divergeD).

  (** Nondeterministic choice: union of outcome sets, environment by
      environment. *)
  Definition orD {A} (m1 m2 : rddivnd A) : rddivnd A :=
    mkReaderT (fun r =>
      DivNonDet.orD (runReaderT m1 r) (runReaderT m2 r)).

  (** [m] may diverge in environment [r]. *)
  Definition mayDiverge {A} (m : rddivnd A) (r : R) : Prop :=
    DivNonDet.mayDiverge (runReaderT m r).

  (** ** The non-empty fragment

      As in [DivNonDet.v] and [StDivNonDet.v], nothing in [rddivnd] forces the
      outcome set to be inhabited, so the blocking program is a well-typed
      element with no outcomes at all.  Every program built from the operations
      above does have an outcome in every environment, and that is carved out
      here as a subset type. *)

  Definition nonEmptyOutcomes {A} (m : rddivnd A) : Prop :=
    forall r, exists oa, unOptionT (runReaderT m r) oa.

  Definition rddivndNE (A : Type) : Type := { m : rddivnd A | nonEmptyOutcomes m }.

  Definition getNE {A} (m : rddivndNE A) : rddivnd A := proj1_sig m.

  Lemma getNE_nonEmpty {A} (m : rddivndNE A) : nonEmptyOutcomes (getNE m).
  Proof. exact (proj2_sig m). Qed.

  (** Closure of [nonEmptyOutcomes] under each operation. *)

  Lemma nonEmpty_retD {A} (a : A) : nonEmptyOutcomes (retD a).
  Proof. intro r. exists (Some a). cbn. reflexivity. Qed.

  Lemma nonEmpty_askD : nonEmptyOutcomes askD.
  Proof. intro r. exists (Some r). cbn. reflexivity. Qed.

  Lemma nonEmpty_localD {A} (f : R -> R) (m : rddivnd A) :
    nonEmptyOutcomes m -> nonEmptyOutcomes (localD f m).
  Proof. intros H r. exact (H (f r)). Qed.

  Lemma nonEmpty_divergeD {A} : nonEmptyOutcomes (divergeD : rddivnd A).
  Proof. intro r. exists None. cbn. reflexivity. Qed.

  Lemma nonEmpty_orD {A} (m1 m2 : rddivnd A) :
    nonEmptyOutcomes m1 -> nonEmptyOutcomes (orD m1 m2).
  Proof.
    intros H r. destruct (H r) as [oa Ho]. exists oa. cbn. left. exact Ho.
  Qed.

  Lemma nonEmpty_bindD {A B} (m : rddivnd A) (k : A -> rddivnd B) :
    nonEmptyOutcomes m -> (forall a, nonEmptyOutcomes (k a)) ->
    nonEmptyOutcomes (bindD m k).
  Proof.
    intros Hm Hk r. destruct (Hm r) as [[a|] Ho].
    - destruct (Hk a r) as [ob Hob]. exists ob. cbn.
      exists (Some a). split; [ exact Ho | exact Hob ].
    - exists None. cbn. exists None. split; [ exact Ho | reflexivity ].
  Qed.

  (** The operations, lifted to the subset type. *)

  Definition retNE {A} (a : A) : rddivndNE A :=
    exist _ (retD a) (nonEmpty_retD a).

  Definition bindNE {A B} (m : rddivndNE A) (k : A -> rddivndNE B) : rddivndNE B :=
    exist _ (bindD (getNE m) (fun a => getNE (k a)))
            (nonEmpty_bindD (getNE m) (fun a => getNE (k a))
               (getNE_nonEmpty m) (fun a => getNE_nonEmpty (k a))).

  #[global]
    Instance Monad__rddivndNE : Monad rddivndNE :=
    {| ret := fun _ => @retNE _ ;
       bind := fun _ _ => @bindNE _ _ |}.

  Definition askNE : rddivndNE R := exist _ askD nonEmpty_askD.

  Definition localNE {A} (f : R -> R) (m : rddivndNE A) : rddivndNE A :=
    exist _ (localD f (getNE m)) (nonEmpty_localD f (getNE m) (getNE_nonEmpty m)).

  #[global]
    Instance MonadReader__rddivndNE : MonadReader R rddivndNE :=
    {| ask := askNE ;
       local := fun _ => @localNE _ |}.

  Definition divergeNE {A} : rddivndNE A :=
    exist _ divergeD nonEmpty_divergeD.

  Definition orNE {A} (m1 m2 : rddivndNE A) : rddivndNE A :=
    exist _ (orD (getNE m1) (getNE m2)) (nonEmpty_orD _ _ (getNE_nonEmpty m1)).

  (** [m] may diverge in environment [r], on the non-empty fragment. *)
  Definition mayDivergeNE {A} (m : rddivndNE A) (r : R) : Prop :=
    mayDiverge (getNE m) r.

End RdDivNonDet.

Arguments rddivnd _ _.
Arguments divergeD {_} {_}.
Arguments orD {_} {_}.
Arguments mayDiverge {_} {_}.
Arguments localD {_} {_}.

Arguments rddivndNE _ _.
Arguments getNE {_} {_}.
Arguments retNE {_} {_}.
Arguments bindNE {_} {_} {_}.
Arguments divergeNE {_} {_}.
Arguments orNE {_} {_}.
Arguments localNE {_} {_}.
Arguments nonEmptyOutcomes {_} {_}.
Arguments mayDivergeNE {_} {_}.

(* ================================================================= *)
(** * Facts and laws                                                  *)
(* ================================================================= *)

(** [rddivndNE R A = { m : rddivnd R A | nonEmptyOutcomes m }] carries the
    operations of [rddivnd] unchanged — [proj1_sig] of [retNE] / [bindNE] is
    [retD] / [bindD] definitionally — so every law is the corresponding law of
    [rddivnd], transported along [getNE].

    [rddivnd R = readerT R divnd] gets its own laws from the generic [readerT]
    instances in [TransformerLaws.v], applied to [divnd]'s in [DivNonDet.v]. *)

From Coq Require Import Morphisms.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

Section RdDivNonDetLaws.

  Variable R : Type.

  (** Laws for the underlying [rddivnd], i.e. for [readerT R divnd]. *)

  Definition Eq1__rddivnd : Eq1 (rddivnd R) :=
    Eq1_readerT R (optionT SetM).

  Definition Eq1Equivalence__rddivnd
    : @Eq1Equivalence (rddivnd R) _ Eq1__rddivnd :=
    Eq1Equivalence_readerT R (optionT SetM).

  Definition MonadLawsE__rddivnd
    : @MonadLawsE (rddivnd R) _ (Monad__rddivnd R) :=
    MonadLawsE_readerT R (optionT SetM).

  (** Equality on the subset type is equality of the underlying programs. *)

  #[global]
    Instance Eq1__rddivndNE : Eq1 (rddivndNE R) :=
    fun A m n => Eq1__rddivnd A (getNE m) (getNE n).

  #[global]
    Instance Eq1Equivalence__rddivndNE
    : @Eq1Equivalence (rddivndNE R) _ Eq1__rddivndNE.
  Proof.
    intro A. destruct (Eq1Equivalence__rddivnd A) as [Erefl Esym Etrans].
    constructor.
    - intro x. exact (Erefl (getNE x)).
    - intros x y H. exact (Esym _ _ H).
    - intros x y z H1 H2. exact (Etrans _ _ _ H1 H2).
  Qed.

  #[global]
    Instance MonadLawsE__rddivndNE
    : @MonadLawsE (rddivndNE R) Eq1__rddivndNE (Monad__rddivndNE R).
  Proof.
    destruct MonadLawsE__rddivnd as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => getNE (f a)) x).
    - intros A x. exact (Lbrr A (getNE x)).
    - intros A B C x f g.
      exact (Lbb A B C (getNE x) (fun a => getNE (f a)) (fun b => getNE (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (getNE x) (getNE y) Hxy
               (fun a => getNE (f a)) (fun a => getNE (g a)) Hfg).
  Qed.

End RdDivNonDetLaws.
