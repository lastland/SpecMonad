(** * [WPure]: the monad of MONOTONE weakest-precondition transformers,
      and its two program-shaped stacks.

    This file contains exactly three developments:

      [WPure  A]      = { f : (A -> Prop) -> Prop | f is monotone }
      [WSt    S A]    = stateT S WPure A            (* W^St     *)
      [WStExc S A]    = stateT S (optionT WPure) A  (* W^StExc  *)

    Monotonicity is part of the carrier, not a side condition: it is exactly
    what the [PrePost -| WPure] adjunctions of [BaseGaloisConnections.v] need, and they
    are false without it.

    Unfolded, [WSt S A = S -> (A * S -> Prop) -> Prop]: every outcome is a
    normal return.  [WStExc S A = S -> (option (A * S) -> Prop) -> Prop]: the
    extra outcome is the raised exception, so this is the stack that carries a
    [MonadExc]. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.

(* ================================================================= *)
(** ** [WPure]                                                       *)
(* ================================================================= *)

Section WPure.

  (** The underlying, unrestricted transformer type.  The arrow presentation
      in [Arrows/WPArr.v] uses this: its [ArrowEq] is Leibniz equality, which
      a subset type cannot support without proof irrelevance. *)
  Definition WPureT (A : Type) : Type := (A -> Prop) -> Prop.

  Definition wpure_mono {A} (f : WPureT A) : Prop :=
    forall p q : A -> Prop, (forall a, p a -> q a) -> f p -> f q.

  Definition WPure (A : Type) : Type := { f : WPureT A | wpure_mono f }.

  Definition runWPure {A} (w : WPure A) : (A -> Prop) -> Prop := proj1_sig w.
  Coercion runWPure : WPure >-> Funclass.

  Lemma runWPure_mono {A} (w : WPure A) (p q : A -> Prop) :
    (forall a, p a -> q a) -> runWPure w p -> runWPure w q.
  Proof. exact (proj2_sig w p q). Qed.

  (** Build an element from a raw transformer and a monotonicity proof. *)
  Definition mkWPure {A} (f : WPureT A) (H : wpure_mono f) : WPure A :=
    exist _ f H.

  (** ret and bind *)

  Lemma retWPure_mono {A} (a : A) : wpure_mono (fun p => p a).
  Proof. intros p q Hpq H. exact (Hpq a H). Qed.

  Definition retWPure {A} (a : A) : WPure A := mkWPure _ (retWPure_mono a).

  Lemma bindWPure_mono {A B} (m : WPure A) (k : A -> WPure B) :
    wpure_mono (fun p => runWPure m (fun a => runWPure (k a) p)).
  Proof.
    intros p q Hpq H.
    apply (runWPure_mono m (fun a => runWPure (k a) p)); [| exact H ].
    intros a Ha. exact (runWPure_mono (k a) p q Hpq Ha).
  Qed.

  Definition bindWPure {A B} (m : WPure A) (k : A -> WPure B) : WPure B :=
    mkWPure _ (bindWPure_mono m k).

  #[global] Instance Monad_WPure : Monad WPure :=
    { ret := @retWPure ; bind := @bindWPure }.

  (** Pointwise logical equivalence of the underlying transformers. *)
  #[global] Instance Eq1_WPure : Eq1 WPure :=
    fun A m1 m2 => forall p, runWPure m1 p <-> runWPure m2 p.

  #[global] Instance Eq1Equivalence_WPure : @Eq1Equivalence WPure _ Eq1_WPure.
  Proof.
    constructor; unfold eq1, Eq1_WPure.
    - intros x p. reflexivity.
    - intros x y H p. symmetry. exact (H p).
    - intros x y z H1 H2 p. etransitivity; [ exact (H1 p) | exact (H2 p) ].
  Qed.

  #[global] Instance MonadLawsE_WPure : @MonadLawsE WPure Eq1_WPure _.
  Proof.
    constructor; unfold eq1, Eq1_WPure; cbn.
    - intros A B f x p. split; intro H; exact H.
    - intros A x p. split; intro H; exact H.
    - intros A B C x f g p. split; intro H; exact H.
    - intros A B x y Hxy f g Hfg p. cbn. split.
      + intro H. apply (proj1 (Hxy (fun a => runWPure (g a) p))).
        apply (runWPure_mono x (fun a => runWPure (f a) p)
                               (fun a => runWPure (g a) p)
                               (fun a Ha => proj1 (Hfg a p) Ha)).
        exact H.
      + intro H. apply (proj2 (Hxy (fun a => runWPure (f a) p))).
        apply (runWPure_mono y (fun a => runWPure (g a) p)
                               (fun a => runWPure (f a) p)
                               (fun a Ha => proj2 (Hfg a p) Ha)).
        exact H.
  Qed.

End WPure.

(** ** The refinement order on [WPure]

    DM4all's order (§3.1): REVERSE pointwise implication — [w1] is below [w2]
    when [w2]'s demand implies [w1]'s, i.e. a WEAKER precondition is lower.
    Note the two stack orders below point the OTHER way; see the note there. *)

Definition WP_le {A} (w1 w2 : WPure A) : Prop :=
  forall k, runWPure w2 k -> runWPure w1 k.

#[global] Instance WP_le_PreOrder {A} : PreOrder (@WP_le A).
Proof.
  constructor; unfold WP_le.
  - intros x k H. exact H.
  - intros x y z H1 H2 k H. exact (H1 k (H2 k H)).
Qed.

(* ================================================================= *)
(** ** [WSt S] = [stateT S WPure]                                    *)
(* ================================================================= *)

Section WSt.

  Variable S : Type.

  Definition WSt := stateT S WPure.

  #[local] Existing Instance Monad_stateT.

  Definition retPs {A} (a : A) : WSt A := @ret (stateT _ _) _ _ a.

  Definition bindPs {A B} (m : WSt A) (k : A -> WSt B) : WSt B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global] Instance Monad__WSt : Monad WSt :=
    {| ret := fun _ => @retPs _ ; bind := fun _ _ => @bindPs _ _ |}.

  Definition getPs : WSt S := @get _ (stateT _ _) _.
  Definition putPs (s : S) : WSt unit := @put _ (stateT _ _) _ s.

  #[global] Instance MonadState__WSt : MonadState S WSt :=
    {| get := getPs ; put := putPs |}.

End WSt.

(** Refinement on [WSt]: FORWARD pointwise implication, i.e. the opposite of
    [WP_le]. This is the direction the triple characterisations in
    [EffectObservations/] use. *)
Definition ordWSt {S A} (w1 w2 : WSt S A) : Prop :=
  forall s post, runStateT w1 s post -> runStateT w2 s post.

(* ================================================================= *)
(** ** [WStExc S] = [stateT S (optionT WPure)]                       *)
(* ================================================================= *)

Section WStExc.

  Variable S : Type.

  Definition WStExc := stateT S (optionT WPure).

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : WStExc A := @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : WStExc A) (k : A -> WStExc B) : WStExc B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global] Instance Monad__WStExc : Monad WStExc :=
    {| ret := fun _ => @retP _ ; bind := fun _ _ => @bindP _ _ |}.

  Definition getP : WStExc S := @get _ (stateT _ _) _.
  Definition putP (s : S) : WStExc unit := @put _ (stateT _ _) _ s.

  #[global] Instance MonadState__WStExc : MonadState S WStExc :=
    {| get := getP ; put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : WStExc A := @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : WStExc A) (c : unit -> WStExc A) : WStExc A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global] Instance MonadExc__WStExc : MonadExc unit WStExc :=
    {| raise := fun _ => raiseP ; catch := fun _ => catchP |}.

End WStExc.

(** Refinement on [WStExc], same forward direction as [ordWSt]. *)
Definition ordWStExc {S A} (m1 m2 : WStExc S A) : Prop :=
  forall s p, unOptionT (runStateT m1 s) p -> unOptionT (runStateT m2 s) p.

(* ================================================================= *)
(** ** Laws for the two stacks                                       *)
(* ================================================================= *)

(** Both chain through the generic [optionT] / [stateT] instances, which are
    [Eq1]-generic, so [Eq1_WPure] (pointwise iff) serves throughout. *)

From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

Section WStLaws.
  Variable S : Type.
  Definition Eq1__WSt : Eq1 (WSt S) := Eq1_stateT S WPure.
  Definition Eq1Equivalence__WSt
    : @Eq1Equivalence (WSt S) _ Eq1__WSt := Eq1Equivalence_stateT S WPure.
  Definition MonadLawsE__WSt
    : @MonadLawsE (WSt S) _ (Monad__WSt S) := MonadLawsE_stateT S WPure.
End WStLaws.

Section WStExcLaws.
  Variable S : Type.
  Definition Eq1__WStExc : Eq1 (WStExc S) := Eq1_stateT S (optionT WPure).
  Definition MonadLawsE__WStExc
    : @MonadLawsE (WStExc S) _ (Monad__WStExc S) :=
    MonadLawsE_stateT S (optionT WPure).
End WStExcLaws.
