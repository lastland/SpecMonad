(** * The base computation monad: programs and their outcomes

    Programs are interaction trees [itree E A], over any events [E], read as
    nondeterministic: an event may get any of its answers.  What a program
    can do is a non-empty set of outcomes, built in three steps:

      [SetM A  = A -> Prop]          a set of outcomes
      [divnd A = optionT SetM A]     a set of outcomes, [None] being divergence
      [divndNE A]                    the elements of [divnd A] with an outcome

    and [denote : itree E A -> divndNE A] maps a program to its outcomes: the
    values it may return, and divergence if some path is infinite.  It needs
    every event to have an answer ([HasAnswers]), as ITree's
    nondeterministic choice [nondetE] has.  [denote] is a monad morphism up
    to [eutt] ([denote_morphism]).

    The two other settings are monad transformers applied to [divndNE]:
    [stdivndNE S = stateT S divndNE] ([DivNonDetSt/Computation.v]) and
    [stdivexcndNE S = stateT S (optionT divndNE)]
    ([DivNonDetStExc/Computation.v]). *)

From Coq Require Import Morphisms FunctionalExtensionality PropExtensionality.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Paco Require Import paco.
From ITree Require Import Basics.Monad Core.ITreeDefinition Core.ITreeMonad Core.Subevent
  Indexed.Sum Eq.Eqit Eq.Shallow Props.Leaf Props.Infinite.
From ITree Require Events.Nondeterminism.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import TransformerLaws OrderedMonad.
From Incorrectness.Lib Require Import ITreeFacts.

(* ================================================================= *)
(** * Programs                                                        *)
(* ================================================================= *)

(** A program is an interaction tree [itree E A].  An event may get any of
    its answers; for every program to have an outcome, every event must have
    one ([HasAnswers]).  ITree's nondeterministic choice [nondetE] has: its
    one event [Or] answers a [bool]. *)

Class HasAnswers (E : Type -> Type) : Prop :=
  has_answer : forall X (e : E X), inhabited X.

#[global] Instance HasAnswers_nondetE : HasAnswers Nondeterminism.nondetE.
Proof. intros X []. exact (inhabits true). Qed.

#[global] Instance HasAnswers_sum {E F} `{HasAnswers E} `{HasAnswers F} :
  HasAnswers (E +' F).
Proof. intros X [e | f]; [ exact (has_answer X e) | exact (has_answer X f) ]. Qed.

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

(** Equal computations of the base monad have the same outcomes. *)
Lemma eq1_outcomes {A} (x y : divndNE A) :
  eq1 x y -> forall oa, unOptionT (getNE x) oa <-> unOptionT (getNE y) oa.
Proof.
  intros H oa. change (unOptionT (getNE x) = unOptionT (getNE y)) in H.
  rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(** * [denote]                                                        *)
(* ================================================================= *)

Section Denote.
  Context {E : Type -> Type} `{HE : HasAnswers E}.

Definition denoteD {A} (t : itree E A) : divnd A :=
  @mkOptionT SetM _ (fun o => match o with
                              | Some a => Leaf a t
                              | None => any_infinite t
                              end).

#[program] Definition denote {A} (t : itree E A) : divndNE A := denoteD t.
Next Obligation.
  destruct (leaf_or_infinite has_answer t) as [[a Ha] | Hinf];
    [ exists (Some a); exact Ha | exists None; exact Hinf ].
Qed.

Lemma outcomes_denote {A} (t : itree E A) (o : option A) :
  unOptionT (getNE (denote t)) o
  <-> match o with Some a => Leaf a t | None => any_infinite t end.
Proof. reflexivity. Qed.

(** Two computations with the same outcomes are equal. *)
Lemma divndNE_eq1 {A} (x y : divndNE A) :
  (forall o, unOptionT (getNE x) o <-> unOptionT (getNE y) o) -> eq1 x y.
Proof.
  intro H. change (unOptionT (getNE x) = unOptionT (getNE y)).
  apply functional_extensionality. intro o.
  apply propositional_extensionality. exact (H o).
Qed.

Lemma denote_ret {A} (a : A) (o : option A) :
  unOptionT (getNE (denote (Ret a))) o <-> o = Some a.
Proof.
  rewrite outcomes_denote. destruct o as [b|]; split.
  - intro H. f_equal. exact (Leaf_Ret_inv _ _ _ _ H).
  - intro H. injection H as ->. apply Leaf_Ret.
  - intro H. destruct (any_infinite_ret a H).
  - discriminate.
Qed.

Lemma denote_bind {A B} (t : itree E A) (k : A -> itree E B) (o : option B) :
  unOptionT (getNE (denote (ITree.bind t k))) o
  <-> exists oa, unOptionT (getNE (denote t)) oa /\
        match oa with
        | Some a => unOptionT (getNE (denote (k a))) o
        | None => o = None
        end.
Proof.
  rewrite outcomes_denote. destruct o as [b|]; split.
  - intro H. destruct (Leaf_bind_inv _ _ _ H) as [a [Ha Hb]].
    exists (Some a). exact (conj Ha Hb).
  - intros [[a|] [Ha Hb]]; [ exact (Leaf_bind _ _ _ _ Ha Hb) | discriminate ].
  - intro H. destruct (any_infinite_bind_inv _ _ H) as [Hinf | [a [Ha Hinf]]].
    + exists None. exact (conj Hinf eq_refl).
    + exists (Some a). exact (conj Ha Hinf).
  - intros [[a|] [Ha Hb]].
    + exact (any_infinite_bind_leaf _ _ _ Ha Hb).
    + exact (any_infinite_bind_l _ k Ha).
Qed.

Theorem denote_morphism :
  @MonadMorphism (itree E) divndNE Monad_itree Monad__divndNE
    Eq1_ITree Eq1__divndNE (@denote).
Proof.
  constructor.
  - intros A x y Hxy. unfold eq1, Eq1_ITree in Hxy. apply divndNE_eq1.
    intros o. rewrite !outcomes_denote. destruct o as [a|].
    + rewrite Hxy. reflexivity.
    + rewrite Hxy. reflexivity.
  - intros A a. apply divndNE_eq1. intro o. exact (denote_ret a o).
  - intros A B x k. apply divndNE_eq1. intro o.
    etransitivity; [ exact (denote_bind x k o) |].
    symmetry. exact (outcomes_bind (getNE (denote x)) (fun a => getNE (denote (k a))) o).
Qed.

#[global] Instance IsMonadMorphism_denote : IsMonadMorphism (@denote) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ denote_morphism.

(** The operations. *)

Lemma denote_vis {X A} (e : E X) (k : X -> itree E A) (o : option A) :
  unOptionT (getNE (denote (Vis e k))) o
  <-> exists x, unOptionT (getNE (denote (k x))) o.
Proof.
  rewrite outcomes_denote. destruct o as [a|]; split.
  - intro H. exact (Leaf_Vis_inv _ _ _ _ _ _ H).
  - intros [x Hx]. exact (Leaf_Vis _ _ _ e k a x Hx).
  - intro H. punfold H. red in H. cbn in H.
    destruct (any_infiniteF_vis_inv _ _ _ H) as [x Hx]. pclearbot. exists x. exact Hx.
  - intros [x Hx]. pfold. red. cbn. apply (DivVis _ _ e x). left. exact Hx.
Qed.

(** ITree's nondeterministic choice is the union of the outcomes. *)
Lemma denote_or `{Nondeterminism.nondetE -< E} {A} (t1 t2 : itree E A) (o : option A) :
  unOptionT (getNE (denote (Nondeterminism.or t1 t2))) o
  <-> unOptionT (getNE (denote t1)) o \/ unOptionT (getNE (denote t2)) o.
Proof.
  unfold Nondeterminism.or. rewrite denote_vis. split.
  - intros [[] Ho]; [ left | right ]; exact Ho.
  - intros [Ho | Ho]; [ exists true | exists false ]; exact Ho.
Qed.

Lemma denote_spin {A} (o : option A) :
  unOptionT (getNE (denote ITree.spin)) o <-> o = None.
Proof.
  rewrite outcomes_denote. destruct o as [a|]; split.
  - intro H. exfalso. remember ITree.spin as t eqn:Et.
    induction H as [t Ht | t u Ht _ IH | Y e t h y Ht _ IH];
      subst t; cbn in Ht; try discriminate.
    injection Ht as <-. exact (IH eq_refl).
  - discriminate.
  - intros _. reflexivity.
  - intros _. exact spin_infinite.
Qed.
End Denote.
