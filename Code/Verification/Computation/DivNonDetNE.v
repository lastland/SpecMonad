(** * The computation monads: non-empty nondeterminism with divergence

    One base monad and two monad transformer stacks over it:

      [divndNE A]                                           base
      [stdivndNE S A]    = [stateT S divndNE A]             state
      [stdivexcndNE S A] = [stateT S (optionT divndNE) A]   state and exceptions

    The base is built in three steps:

      [SetM A  = A -> Prop]          a set of outcomes
      [divnd A = optionT SetM A]     a set of outcomes, [None] being divergence
      [divndNE A]                    the elements of [divnd A] with an outcome

    The two stacks are non-empty from every start state by construction. *)

From Coq Require Import Morphisms FunctionalExtensionality PropExtensionality.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import TransformerLaws.

(* ================================================================= *)
(** * Sets of outcomes: [SetM]                                        *)
(* ================================================================= *)

(** The powerset monad: return is a singleton, bind runs the continuation on
    every outcome of the prefix.  Its laws hold up to Leibniz equality, by
    functional and propositional extensionality. *)

Section SetM.

  Definition SetM A := A -> Prop.

  #[global]
    Instance Monad_SetM : Monad SetM :=
    {| ret := fun _ a => fun x => x = a ;
       bind := fun _ _ m k => fun b => exists a, m a /\ k a b |}.

  #[global]
  Instance Eq1_SetM : Eq1 SetM :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_SetM
    : @Eq1Equivalence SetM _ Eq1_SetM.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_SetM
    : @MonadLawsE SetM Eq1_SetM _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto limit: 200.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto limit: 200.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro c.
      apply propositional_extensionality. sauto limit: 200.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_SetM in *. subst.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split; intros [a [Ha Hk]]; exists a; split; try exact Ha;
        [rewrite <- (Hfg a) | rewrite (Hfg a)]; exact Hk.
  Qed.

End SetM.

(* ================================================================= *)
(** * Nondeterminism with divergence: [divnd]                         *)
(* ================================================================= *)

(** [divnd A = optionT SetM A], whose payload is [option A -> Prop] — a SET of
    outcomes, with the distinguished outcome [None] read as DIVERGENCE.

    Nothing in the type distinguishes divergence from a raised exception;
    what fixes the meaning is which operations are offered.
    So [divnd] deliberately has NO [MonadExc] instance — [catch] would
    be "recover from divergence", which is not an observable operation — and
    instead has [divergeD], the divergent program.

    [None] is absorbing under [bind], which is exactly the propagation rule
    divergence needs, so the monad structure is [optionT]'s unchanged. *)

Section DivNonDet.

  Definition divnd A := optionT SetM A.

  Definition retD {A} (a : A) : divnd A :=
    @ret (optionT SetM) _ _ a.

  Definition bindD {A B} (m : divnd A) (k : A -> divnd B) : divnd B :=
    @bind (optionT SetM) _ _ _ m k.

  #[global]
    Instance Monad__divnd : Monad divnd :=
    {| ret := fun _ => @retD _ ;
       bind := fun _ _ => @bindD _ _ |}.

  (** The divergent program: its only outcome is the divergence token. *)
  Definition divergeD {A} : divnd A :=
    @mkOptionT SetM _ (fun oa => oa = None).

  (** Nondeterministic choice: union of outcome sets. *)
  Definition orD {A} (m1 m2 : divnd A) : divnd A :=
    @mkOptionT SetM _ (fun oa => unOptionT m1 oa \/ unOptionT m2 oa).

  (** [m] may diverge. *)
  Definition mayDiverge {A} (m : divnd A) : Prop :=
    unOptionT m None.

  (** ** Divergence propagates

      Stated pointwise on outcomes rather than as an [eq1]: [Eq1_SetM] is
      Leibniz equality on [option A -> Prop], so the extensional form would
      need functional and propositional extensionality, while these are
      axiom-free and are the shape the monad morphisms consume. *)

  Lemma outcomes_bind {A B} (m : divnd A) (k : A -> divnd B) (ob : option B) :
    unOptionT (bindD m k) ob <->
    (exists oa, unOptionT m oa /\
       match oa with
       | Some a => unOptionT (k a) ob
       | None   => ob = None
       end).
  Proof.
    cbn. split; intros [oa [H1 H2]]; exists oa; split; try exact H1;
      destruct oa as [a|]; exact H2.
  Qed.

  (** [divergeD] is absorbing: nothing after it can run. *)
  Lemma diverge_absorbing {A B} (k : A -> divnd B) (ob : option B) :
    unOptionT (bindD (divergeD : divnd A) k) ob <-> ob = None.
  Proof.
    rewrite outcomes_bind. split.
    - intros [oa [Hd H]]. cbn in Hd. subst oa. exact H.
    - intro Hob. exists None. split; [ reflexivity | exact Hob ].
  Qed.

  (** A divergent prefix makes the whole computation divergent. *)
  Lemma mayDiverge_bind {A B} (m : divnd A) (k : A -> divnd B) :
    mayDiverge m -> mayDiverge (bindD m k).
  Proof.
    intro Hm. unfold mayDiverge. apply outcomes_bind.
    exists None. split; [ exact Hm | reflexivity ].
  Qed.

  (** ** Blocking versus the absorbing [None]

      An empty outcome set is BLOCKING — no bind outcome can be built from
      it — while a divergent prefix survives even an empty continuation,
      because [bind] absorbs [None] without running the continuation. *)

  Definition emptyD {A} : divnd A :=
    @mkOptionT SetM _ (fun _ => False).

  (** An empty prefix blocks: the bind has no outcome either. *)
  Lemma empty_prefix_blocks {A B} (k : A -> divnd B) (ob : option B) :
    ~ unOptionT (bindD (emptyD : divnd A) k) ob.
  Proof.
    intro Hout.
    destruct (proj1 (outcomes_bind emptyD k ob) Hout) as [oa [Hoa _]].
    exact Hoa.
  Qed.

  (** A divergent prefix survives an empty continuation. *)
  Lemma diverge_survives_empty {A B} :
    unOptionT (bindD (divergeD : divnd A) (fun _ => (emptyD : divnd B))) None.
  Proof. apply diverge_absorbing. reflexivity. Qed.

  (** ** Laws

      The generic [optionT] instances of [TransformerLaws.v], at [SetM]. *)

  Definition Eq1__divnd : Eq1 divnd :=
    Eq1_optionT SetM.

  Definition Eq1Equivalence__divnd
    : @Eq1Equivalence divnd _ Eq1__divnd :=
    Eq1Equivalence_optionT SetM.

  Definition MonadLawsE__divnd
    : @MonadLawsE divnd _ Monad__divnd :=
    MonadLawsE_optionT SetM.

End DivNonDet.

Arguments divnd _.
Arguments divergeD {_}.
Arguments orD {_}.
Arguments mayDiverge {_}.
Arguments emptyD {_}.

(* ================================================================= *)
(** * The base monad: [divndNE]                                       *)
(* ================================================================= *)

(** Nothing in [divnd] forces the outcome set to be inhabited: [emptyD] is a
    well-typed element with no outcomes at all — it neither terminates nor
    diverges.  Every program built from [retD], [bindD], [divergeD] and [orD]
    does have an outcome, so that is carved out here as a subset type: side
    conditions of the form [exists oa, unOptionT m oa] become part of the
    carrier instead of hypotheses on each theorem. *)

Definition nonEmptyOutcomes {A} (m : divnd A) : Prop :=
  exists oa, unOptionT m oa.

Definition divndNE (A : Type) : Type := { m : divnd A | nonEmptyOutcomes m }.

Definition getNE {A} (m : divndNE A) : divnd A := proj1_sig m.

Lemma getNE_nonEmpty {A} (m : divndNE A) : nonEmptyOutcomes (getNE m).
Proof. exact (proj2_sig m). Qed.

(** Closure of [nonEmptyOutcomes] under each operation. *)

Lemma nonEmpty_retD {A} (a : A) : nonEmptyOutcomes (retD a).
Proof. exists (Some a). cbn. reflexivity. Qed.

Lemma nonEmpty_divergeD {A} : nonEmptyOutcomes (divergeD : divnd A).
Proof. exists None. cbn. reflexivity. Qed.

Lemma nonEmpty_orD {A} (m1 m2 : divnd A) :
  nonEmptyOutcomes m1 -> nonEmptyOutcomes (orD m1 m2).
Proof. intros [oa Ho]. exists oa. cbn. left. exact Ho. Qed.

Lemma nonEmpty_bindD {A B} (m : divnd A) (k : A -> divnd B) :
  nonEmptyOutcomes m -> (forall a, nonEmptyOutcomes (k a)) ->
  nonEmptyOutcomes (bindD m k).
Proof.
  intros [[a|] Ho] Hk.
  - destruct (Hk a) as [ob Hob]. exists ob. cbn.
    exists (Some a). split; [ exact Ho | exact Hob ].
  - exists None. cbn. exists None. split; [ exact Ho | reflexivity ].
Qed.

(** The operations, lifted to the subset type. *)

Definition retNE {A} (a : A) : divndNE A :=
  exist _ (retD a) (nonEmpty_retD a).

Definition bindNE {A B} (m : divndNE A) (k : A -> divndNE B) : divndNE B :=
  exist _ (bindD (getNE m) (fun a => getNE (k a)))
          (nonEmpty_bindD (getNE m) (fun a => getNE (k a))
             (getNE_nonEmpty m) (fun a => getNE_nonEmpty (k a))).

#[global]
  Instance Monad__divndNE : Monad divndNE :=
  {| ret := fun _ => @retNE _ ;
     bind := fun _ _ => @bindNE _ _ |}.

Definition divergeNE {A} : divndNE A :=
  exist _ divergeD nonEmpty_divergeD.

Definition orNE {A} (m1 m2 : divndNE A) : divndNE A :=
  exist _ (orD (getNE m1) (getNE m2)) (nonEmpty_orD _ _ (getNE_nonEmpty m1)).

(** [m] may diverge, on the non-empty fragment. *)
Definition mayDivergeNE {A} (m : divndNE A) : Prop :=
  mayDiverge (getNE m).


Arguments divndNE _.
Arguments getNE {_}.
Arguments retNE {_}.
Arguments bindNE {_} {_}.
Arguments divergeNE {_}.
Arguments orNE {_}.
Arguments nonEmptyOutcomes {_}.
Arguments mayDivergeNE {_}.

(** [divndNE] carries the operations of [divnd] unchanged — [proj1_sig] of
    [retNE] / [bindNE] is [retD] / [bindD] definitionally — so every law is
    the corresponding law of [divnd], transported along [getNE]. *)

(** Equality on the subset type is equality of the underlying programs. *)

#[global]
  Instance Eq1__divndNE : Eq1 divndNE :=
  fun A m n => Eq1__divnd A (getNE m) (getNE n).

#[global]
  Instance Eq1Equivalence__divndNE
  : @Eq1Equivalence divndNE _ Eq1__divndNE.
Proof.
  intro A. destruct (Eq1Equivalence__divnd A) as [Erefl Esym Etrans].
  constructor.
  - intro x. exact (Erefl (getNE x)).
  - intros x y H. exact (Esym _ _ H).
  - intros x y z H1 H2. exact (Etrans _ _ _ H1 H2).
Qed.

#[global]
  Instance MonadLawsE__divndNE
  : @MonadLawsE divndNE Eq1__divndNE Monad__divndNE.
Proof.
  destruct MonadLawsE__divnd as [Lbrl Lbrr Lbb Lpb].
  constructor.
  - intros A B f x. exact (Lbrl A B (fun a => getNE (f a)) x).
  - intros A x. exact (Lbrr A (getNE x)).
  - intros A B C x f g.
    exact (Lbb A B C (getNE x) (fun a => getNE (f a)) (fun b => getNE (g b))).
  - intros A B x y Hxy f g Hfg.
    exact (Lpb A B (getNE x) (getNE y) Hxy
             (fun a => getNE (f a)) (fun a => getNE (g a)) Hfg).
Qed.


(* ================================================================= *)
(** * The two stacks: [stdivndNE] and [stdivexcndNE]                  *)
(* ================================================================= *)

(** The state transformer applied to [divndNE], and to [divndNE] under the
    option transformer.  Monad, equality and state operations are ExtLib's
    and [TransformerLaws.v]'s, at the base dictionaries above. *)

Definition stdivndNE (S : Type) : Type -> Type := stateT S divndNE.
Definition stdivexcndNE (S : Type) : Type -> Type := stateT S (optionT divndNE).

#[global] Instance Monad__stdivndNE (S : Type) : Monad (stdivndNE S) :=
  @Monad_stateT S divndNE Monad__divndNE.
#[global] Instance Monad__stdivexcndNE (S : Type) : Monad (stdivexcndNE S) :=
  @Monad_stateT S (optionT divndNE) (@Monad_optionT divndNE Monad__divndNE).

Definition Eq1__stdivndNE (S : Type) : Eq1 (stdivndNE S) :=
  @Eq1_stateT S divndNE Eq1__divndNE.
Definition Eq1__stdivexcndNE (S : Type) : Eq1 (stdivexcndNE S) :=
  @Eq1_stateT S (optionT divndNE) (@Eq1_optionT divndNE Eq1__divndNE).

(** The two stacks are lawful: the generic transformer laws, at the base. *)
Definition Eq1Equivalence__stdivndNE (S : Type)
  : @Eq1Equivalence (stdivndNE S) (Monad__stdivndNE S) (Eq1__stdivndNE S) :=
  Eq1Equivalence_stateT S divndNE.
Definition MonadLawsE__stdivndNE (S : Type)
  : @MonadLawsE (stdivndNE S) (Eq1__stdivndNE S) (Monad__stdivndNE S) :=
  MonadLawsE_stateT S divndNE.
Definition Eq1Equivalence__stdivexcndNE (S : Type)
  : @Eq1Equivalence (stdivexcndNE S) (Monad__stdivexcndNE S) (Eq1__stdivexcndNE S) :=
  Eq1Equivalence_stateT S (optionT divndNE).
Definition MonadLawsE__stdivexcndNE (S : Type)
  : @MonadLawsE (stdivexcndNE S) (Eq1__stdivexcndNE S) (Monad__stdivexcndNE S) :=
  MonadLawsE_stateT S (optionT divndNE).

#[global] Instance MonadState__stdivndNE (S : Type) : MonadState S (stdivndNE S) :=
  @MonadState_stateT S divndNE Monad__divndNE.
#[global] Instance MonadState__stdivexcndNE (S : Type) : MonadState S (stdivexcndNE S) :=
  @MonadState_stateT S (optionT divndNE) (@Monad_optionT divndNE Monad__divndNE).

(** The outcomes of a computation from a start state: a non-empty set of
    [option]s, [None] being divergence.  At state+exceptions an outcome that
    is not divergence is itself an [option], [None] being a raised
    exception. *)
Definition outSt {S A} (m : stdivndNE S A) (s : S) : option (A * S) -> Prop :=
  unOptionT (getNE (runStateT m s)).
Definition outStExc {S A} (m : stdivexcndNE S A) (s : S)
  : option (option (A * S)) -> Prop :=
  unOptionT (getNE (unOptionT (runStateT m s))).

(** Choice and divergence, pointwise in the start state; raising. *)
Definition orSt {S A} (m1 m2 : stdivndNE S A) : stdivndNE S A :=
  mkStateT (fun s => orNE (runStateT m1 s) (runStateT m2 s)).
Definition divergeSt {S A} : stdivndNE S A :=
  mkStateT (fun _ => divergeNE).

Definition orStExc {S A} (m1 m2 : stdivexcndNE S A) : stdivexcndNE S A :=
  mkStateT (fun s =>
    mkOptionT (orNE (unOptionT (runStateT m1 s)) (unOptionT (runStateT m2 s)))).
Definition divergeStExc {S A} : stdivexcndNE S A :=
  mkStateT (fun _ => mkOptionT divergeNE).
Definition raiseStExc {S A} : stdivexcndNE S A :=
  mkStateT (fun _ => mkOptionT (retNE None)).

(** An arbitrary natural number, with the state unchanged. *)
Definition pickStExc {S} : stdivexcndNE S nat :=
  mkStateT (fun s =>
    mkOptionT
      (exist _
         (@mkOptionT SetM _ (fun o => exists n : nat, o = Some (Some (n, s))))
         (ex_intro _ (Some (Some (0, s))) (ex_intro _ 0 eq_refl)))).

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

  Lemma outStExc_ret {A} (a : A) (s : S) (o : option (option (A * S))) :
    outStExc (ret a) s o <-> o = Some (Some (a, s)).
  Proof. reflexivity. Qed.

  Lemma outStExc_bind {A B} (m : stdivexcndNE S A) (k : A -> stdivexcndNE S B) (s : S)
    (o : option (option (B * S))) :
    outStExc (bind m k) s o
    <-> exists o1, outStExc m s o1 /\
          match o1 with
          | Some (Some (a, s')) => outStExc (k a) s' o
          | Some None => o = Some None
          | None => o = None
          end.
  Proof.
    etransitivity;
      [ exact (outcomes_bind (getNE (unOptionT (runStateT m s)))
                 (fun aM => getNE
                    match aM with
                    | Some a => unOptionT (let (v, s') := a in runStateT (k v) s')
                    | None => retNE None
                    end) o) |].
    split; intros [o1 [H1 H2]]; exists o1; (split; [ exact H1 |]);
      destruct o1 as [[[a s']|]|]; exact H2.
  Qed.

  Lemma outStExc_get (s : S) (o : option (option (S * S))) :
    outStExc get s o <-> o = Some (Some (s, s)).
  Proof. reflexivity. Qed.

  Lemma outStExc_put (s' s : S) (o : option (option (unit * S))) :
    outStExc (put s') s o <-> o = Some (Some (tt, s')).
  Proof. reflexivity. Qed.

  Lemma outStExc_or {A} (m1 m2 : stdivexcndNE S A) (s : S)
    (o : option (option (A * S))) :
    outStExc (orStExc m1 m2) s o <-> outStExc m1 s o \/ outStExc m2 s o.
  Proof. reflexivity. Qed.

  Lemma outStExc_diverge {A} (s : S) (o : option (option (A * S))) :
    outStExc (divergeStExc : stdivexcndNE S A) s o <-> o = None.
  Proof. reflexivity. Qed.

  Lemma outStExc_raise {A} (s : S) (o : option (option (A * S))) :
    outStExc (raiseStExc : stdivexcndNE S A) s o <-> o = Some None.
  Proof. reflexivity. Qed.

  Lemma outStExc_pick (s : S) (o : option (option (nat * S))) :
    outStExc pickStExc s o <-> exists n, o = Some (Some (n, s)).
  Proof. reflexivity. Qed.
End Outcomes.

(** Equal computations of the base monad have the same outcomes. *)
Lemma eq1_outcomes {A} (x y : divndNE A) :
  eq1 x y -> forall oa, unOptionT (getNE x) oa <-> unOptionT (getNE y) oa.
Proof.
  intros H oa. change (unOptionT (getNE x) = unOptionT (getNE y)) in H.
  rewrite H. reflexivity.
Qed.

