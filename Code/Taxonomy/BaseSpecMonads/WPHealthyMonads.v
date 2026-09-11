(** * The four WP monads, carved from [WPure] by the shared conditions

    The SP side cuts [SPStExc] into [ASPStExc] / [DSLPStExc] / [DSPStExc] /
    [ASLPStExc] by pairing strict/terminating with disjunctive/conjunctive.
    This file does the same to [WPure], using the SAME four pairings from
    [Healthiness.v]:

    | monad     | pairing          | reading                                  |
    |-----------|------------------|------------------------------------------|
    | [AWPure]  | [AngelicTotal]   | angelic total    — like [ASPStExc]       |
    | [DWLPure] | [DemonicLiberal] | demonic liberal  — like [DSLPStExc]      |
    | [DWPure]  | [DemonicTotal]   | demonic total    — like [DSPStExc]       |
    | [AWLPure] | [AngelicLiberal] | angelic liberal  — like [ASLPStExc]      |

    All four are produced by ONE functor, [HealthyWP], applied to the four
    conditions.  That is possible because on the WP side [bind] is continuation
    composition, so a single closure argument ([Healthiness.v]'s [*_bindPT])
    serves all four — where the SP side needs [DSPMonad.v] and [ASLPMonad.v] to
    recover the underlying relation, at some 2700 lines.  The whole of this
    file is under 150 lines of shared code plus four one-line applications. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import Healthiness WPureMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From ExtLib Require Import StateMonad OptionMonad.

(** ** What a condition has to supply *)

Module Type HEALTHY_COND.
  Parameter Cond : forall (I : Type), PT I -> Prop.
  Parameter Cond_mono : forall (I : Type) (w : PT I), Cond I w -> MonoPT w.
  Parameter Cond_ret : forall (A : Type) (a : A), Cond A (retPT a).
  Parameter Cond_bind : forall (A B : Type) (m : PT A) (k : A -> PT B),
      Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindPT m k).
End HEALTHY_COND.

(** ** The shared construction *)

Module HealthyWP (C : HEALTHY_COND).

  Definition W (A : Type) : Type := { w : WPure A | C.Cond A (runWPure w) }.

  Definition getW {A} (w : W A) : WPure A := proj1_sig w.

  Definition runW {A} (w : W A) : (A -> Prop) -> Prop := runWPure (getW w).

  Lemma getW_cond {A} (w : W A) : C.Cond A (runW w).
  Proof. exact (proj2_sig w). Qed.

  Lemma runW_mono {A} (w : W A) (p q : A -> Prop) :
    (forall a, p a -> q a) -> runW w p -> runW w q.
  Proof. exact (runWPure_mono (getW w) p q). Qed.

  (** [ret] and [bind] are [WPure]'s, with the obligation discharged by the
      shared closure lemmas.  [runW] of each is [retPT] / [bindPT] on the
      nose, which is what makes the transport below definitional. *)

  Definition retW {A} (a : A) : W A :=
    exist _ (retWPure a) (C.Cond_ret A a).

  Definition bindW {A B} (m : W A) (k : A -> W B) : W B :=
    exist _ (bindWPure (getW m) (fun a => getW (k a)))
            (C.Cond_bind A B (runW m) (fun a => runW (k a))
               (getW_cond m) (fun a => getW_cond (k a))).

  #[global] Instance Monad_W : Monad W :=
    {| ret := fun _ => @retW _ ; bind := fun _ _ => @bindW _ _ |}.

  #[global] Instance Eq1_W : Eq1 W :=
    fun A m n => forall p, runW m p <-> runW n p.

  #[global] Instance Eq1Equivalence_W : @Eq1Equivalence W _ Eq1_W.
  Proof.
    intro A. constructor.
    - intros x p. tauto.
    - intros x y H p. specialize (H p). tauto.
    - intros x y z H1 H2 p. specialize (H1 p); specialize (H2 p). tauto.
  Qed.

  #[global] Instance MonadLawsE_W : @MonadLawsE W Eq1_W Monad_W.
  Proof.
    destruct (@MonadLawsE_WPure) as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => getW (f a)) x).
    - intros A x. exact (Lbrr A (getW x)).
    - intros A B C' x f g.
      exact (Lbb A B C' (getW x) (fun a => getW (f a)) (fun b => getW (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (getW x) (getW y) Hxy
               (fun a => getW (f a)) (fun a => getW (g a)) Hfg).
  Qed.

  (** The refinement order, matching the SP side's [ord*]: forward, and a
      variant scoped to one postcondition. *)

  Definition ordW {A} (m1 m2 : W A) : Prop :=
    forall p, runW m1 p -> runW m2 p.

  Definition ordWAt {A} (post : A -> Prop) (m1 m2 : W A) : Prop :=
    runW m1 post -> runW m2 post.

  #[global] Instance ordW_PreOrder {A} : PreOrder (@ordW A).
  Proof.
    constructor.
    - intros x p H. exact H.
    - intros x y z H1 H2 p H. exact (H2 p (H1 p H)).
  Qed.

End HealthyWP.

(** ** The four conditions, and the four monads *)

Module AngelicTotalCond <: HEALTHY_COND.
  Definition Cond (I : Type) (w : PT I) : Prop := AngelicTotal w.
  Definition Cond_mono (I : Type) (w : PT I) : Cond I w -> MonoPT w :=
    AngelicTotal_mono w.
  Definition Cond_ret (A : Type) (a : A) : Cond A (retPT a) :=
    conj (Strict_retPT a) (Disjunctive_retPT a).
  Definition Cond_bind (A B : Type) (m : PT A) (k : A -> PT B)
    : Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindPT m k) :=
    AngelicTotal_bindPT m k.
End AngelicTotalCond.

Module DemonicLiberalCond <: HEALTHY_COND.
  Definition Cond (I : Type) (w : PT I) : Prop := DemonicLiberal w.
  Definition Cond_mono (I : Type) (w : PT I) : Cond I w -> MonoPT w :=
    DemonicLiberal_mono w.
  Definition Cond_ret (A : Type) (a : A) : Cond A (retPT a) :=
    conj (Terminating_retPT a) (Conjunctive_retPT a).
  Definition Cond_bind (A B : Type) (m : PT A) (k : A -> PT B)
    : Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindPT m k) :=
    DemonicLiberal_bindPT m k.
End DemonicLiberalCond.

Module DemonicTotalCond <: HEALTHY_COND.
  Definition Cond (I : Type) (w : PT I) : Prop := DemonicTotal w.
  Definition Cond_mono (I : Type) (w : PT I) : Cond I w -> MonoPT w :=
    DemonicTotal_mono w.
  Definition Cond_ret (A : Type) (a : A) : Cond A (retPT a) :=
    conj (Strict_retPT a) (Conjunctive_retPT a).
  Definition Cond_bind (A B : Type) (m : PT A) (k : A -> PT B)
    : Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindPT m k) :=
    DemonicTotal_bindPT m k.
End DemonicTotalCond.

Module AngelicLiberalCond <: HEALTHY_COND.
  Definition Cond (I : Type) (w : PT I) : Prop := AngelicLiberal w.
  Definition Cond_mono (I : Type) (w : PT I) : Cond I w -> MonoPT w :=
    AngelicLiberal_mono w.
  Definition Cond_ret (A : Type) (a : A) : Cond A (retPT a) :=
    conj (Terminating_retPT a) (Disjunctive_retPT a).
  Definition Cond_bind (A B : Type) (m : PT A) (k : A -> PT B)
    : Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindPT m k) :=
    AngelicLiberal_bindPT m k.
End AngelicLiberalCond.

Module AWP  := HealthyWP AngelicTotalCond.    (** angelic total    *)
Module DWLP := HealthyWP DemonicLiberalCond.  (** demonic liberal  *)
Module DWP  := HealthyWP DemonicTotalCond.    (** demonic total    *)
Module AWLP := HealthyWP AngelicLiberalCond.  (** angelic liberal  *)

(** Convenient aliases, named after the carrier as the SP side is. *)
Definition AWPure  := AWP.W.
Definition DWLPure := DWLP.W.
Definition DWPure  := DWP.W.
Definition AWLPure := AWLP.W.

(* ================================================================= *)
(** * The four are genuinely distinct                                 *)
(* ================================================================= *)

(** Refining a base transformer by the four conditions is only worth doing if
    the four classes are pairwise incomparable.  On [PT A] they are, and four
    witnesses over [bool] suffice.  Note the two axes are independent, not
    exclusive: a transformer can be both strict AND terminating (that is the
    deterministic case), so the statement is incomparability, not disjointness.

    This is exactly what FAILS for the pure SP carrier: there the precondition
    is a bare [Prop], of which there are only two up to propositional
    extensionality, and [Strict] alone already forces [Singleton] — so
    [DemonicTotal] collapses onto [AngelicTotal] and [AngelicLiberal] onto
    [DemonicLiberal].  See [strict_conj_iff_singleton] in [DSPMonad.v] and
    [term_disj_iff_msingleton] in [ASLPMonad.v].  Four conditions, but only two
    monads. *)

Section Separation.

  (** Demonic over a two-point outcome set: conjunctive, not disjunctive. *)
  Definition wDem : PT bool := fun p => p true /\ p false.
  (** Angelic over the same: disjunctive, not conjunctive. *)
  Definition wAng : PT bool := fun p => p true \/ p false.
  (** The miracle and the abort: separate strict from terminating. *)
  Definition wTop : PT bool := fun _ => True.
  Definition wBot : PT bool := fun _ => False.

  Lemma wDem_conjunctive : Conjunctive wDem.
  Proof.
    intros K [k0] p. unfold wDem. split.
    - intros [H1 H2] k. exact (conj (H1 k) (H2 k)).
    - intro H. split; intro k; [ exact (proj1 (H k)) | exact (proj2 (H k)) ].
  Qed.

  Lemma wDem_not_disjunctive : ~ Disjunctive wDem.
  Proof.
    intro H.
    destruct (proj1 (H bool (inhabits true) (fun k a => a = k))
                (conj (ex_intro _ true eq_refl) (ex_intro _ false eq_refl)))
      as [k [H1 H2]].
    destruct k; cbn in *; congruence.
  Qed.

  Lemma wAng_disjunctive : Disjunctive wAng.
  Proof.
    intros K [k0] p. unfold wAng. split.
    - intros [[k H] | [k H]]; exists k; [ left | right ]; exact H.
    - intros [k [H | H]]; [ left | right ]; exists k; exact H.
  Qed.

  Lemma wAng_not_conjunctive : ~ Conjunctive wAng.
  Proof.
    intro H.
    assert (Hall : forall k : bool, wAng (fun a => a = k)).
    { intro k. destruct k; [ left | right ]; reflexivity. }
    destruct (proj2 (H bool (inhabits true) (fun k a => a = k)) Hall) as [H1 | H1];
      [ discriminate (H1 false) | discriminate (H1 true) ].
  Qed.

  Lemma wTop_terminating : Terminating wTop.   Proof. exact I. Qed.
  Lemma wTop_not_strict  : ~ Strict wTop.      Proof. intro H. exact (H I). Qed.
  Lemma wBot_strict      : Strict wBot.        Proof. intros []. Qed.
  Lemma wBot_not_terminating : ~ Terminating wBot. Proof. intros []. Qed.

  (** Hence no containment holds between the classes, in either axis. *)

  Theorem conjunctive_not_disjunctive : exists w : PT bool,
      Conjunctive w /\ ~ Disjunctive w.
  Proof. exists wDem. exact (conj wDem_conjunctive wDem_not_disjunctive). Qed.

  Theorem disjunctive_not_conjunctive : exists w : PT bool,
      Disjunctive w /\ ~ Conjunctive w.
  Proof. exists wAng. exact (conj wAng_disjunctive wAng_not_conjunctive). Qed.

  Theorem terminating_not_strict : exists w : PT bool,
      Terminating w /\ ~ Strict w.
  Proof. exists wTop. exact (conj wTop_terminating wTop_not_strict). Qed.

  Theorem strict_not_terminating : exists w : PT bool,
      Strict w /\ ~ Terminating w.
  Proof. exists wBot. exact (conj wBot_strict wBot_not_terminating). Qed.

End Separation.

(* ================================================================= *)
(** * Stacking                                                        *)
(* ================================================================= *)

(** The WP side stacks: each healthy base monad carries [stateT] and [optionT]
    with no extra work, because the healthiness condition constrains the
    POSTCONDITION slot and neither transformer touches it — [stateT] indexes by
    the initial state, [optionT] widens the outcome type, and the condition is
    then read at the widened outcome, per state.  The laws come from the
    generic instances in [ComputationMonads/TransformerLaws.v].

    So [AWStExc S A = S -> AWPure (option (A * S))] is "one angelic-total
    transformer per initial state, over the full outcome type" — exactly the
    shape an effect observation for [stdivexcnd] lands in.

    The SP side does NOT stack this way, for two independent reasons:

    - Its pure carrier already degenerates: [SPPure]'s precondition slot is a
      bare [Prop], so [DemonicTotal] collapses onto [AngelicTotal] and
      [AngelicLiberal] onto [DemonicLiberal] ([strict_conj_iff_singleton],
      [term_disj_iff_msingleton]).  Four conditions, two monads.

    - And [SPSt] / [SPStExc] are not transformer images of [SPPure] at all:
      the stateful carriers take one SHARED [S -> Prop] precondition, whereas
      any transformer applied to [SPPure] gives a [Prop] PER state.  The
      canonical map from the shared form to the pointwise one is not injective
      (the transformer [fun pre _ => forall s, pre s] and the empty one have
      the same image), so the [SPStExc] monads have to be built directly —
      which is why [DSPMonad.v] and [ASLPMonad.v] exist at their present
      size. *)

Section Stacks.
  Variable S : Type.

  Definition AWSt     := stateT S AWP.W.
  Definition DWLSt    := stateT S DWLP.W.
  Definition DWSt     := stateT S DWP.W.
  Definition AWLSt    := stateT S AWLP.W.

  Definition AWStExc  := stateT S (optionT AWP.W).
  Definition DWLStExc := stateT S (optionT DWLP.W).
  Definition DWStExc  := stateT S (optionT DWP.W).
  Definition AWLStExc := stateT S (optionT AWLP.W).

  (** Laws, entirely inherited.  One line each; nothing about the healthiness
      condition is re-proved, because no transformer touches the slot it
      constrains. *)

  Definition MonadLawsE__AWSt : @MonadLawsE AWSt _ _ := MonadLawsE_stateT S AWP.W.
  Definition MonadLawsE__DWLSt : @MonadLawsE DWLSt _ _ := MonadLawsE_stateT S DWLP.W.
  Definition MonadLawsE__DWSt : @MonadLawsE DWSt _ _ := MonadLawsE_stateT S DWP.W.
  Definition MonadLawsE__AWLSt : @MonadLawsE AWLSt _ _ := MonadLawsE_stateT S AWLP.W.

  Definition MonadLawsE__AWStExc : @MonadLawsE AWStExc _ _ :=
    MonadLawsE_stateT S (optionT AWP.W).
  Definition MonadLawsE__DWLStExc : @MonadLawsE DWLStExc _ _ :=
    MonadLawsE_stateT S (optionT DWLP.W).
  Definition MonadLawsE__DWStExc : @MonadLawsE DWStExc _ _ :=
    MonadLawsE_stateT S (optionT DWP.W).
  Definition MonadLawsE__AWLStExc : @MonadLawsE AWLStExc _ _ :=
    MonadLawsE_stateT S (optionT AWLP.W).

  (** And the payload is the expected shape. *)
  Definition AWStExc_shape (A : Type) (m : AWStExc A) (s : S)
    : (option (A * S) -> Prop) -> Prop :=
    AWP.runW (unOptionT (runStateT m s)).

End Stacks.
