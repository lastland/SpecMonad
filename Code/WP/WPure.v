(** * [WPure]: the monad of MONOTONE weakest-precondition transformers,
      and its two program-shaped stacks (paper, Section 2).

    This file contains exactly three developments:

      [WPure  A]      = { f : (A -> Prop) -> Prop | f is monotone }
      [WSt    S A]    = stateT S WPure A            (* W^St     *)
      [WStExc S A]    = stateT S (optionT WPure) A  (* W^StExc  *)

    Monotonicity is part of the carrier.  The adjunction proofs in
    [BaseGaloisConnections.v] and the [Proper_bind] proof below use it.

    The evaluators take an initial state and a postcondition on [A * S]
    for [WSt], or on [option (A * S)] for [WStExc].  The latter stack
    supplies [MonadExc].  These evaluator shapes omit the bundled
    monotonicity proofs and the transformer wrappers.

    The four WP variants carved out of [WPure] are in [WPVariants.v]. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import TransformerLaws.

(* ================================================================= *)
(** ** [WPure]                                                       *)
(* ================================================================= *)

Section WPure.

  (** The underlying, unrestricted transformer type.  The arrow presentation
      in [GaloisConnections/WPArr.v] uses this with Leibniz [ArrowEq].  The [WPure]
      subset below instead uses pointwise logical equivalence for [Eq1]. *)
  Definition WPureT (A : Type) : Type := (A -> Prop) -> Prop.

  Definition wpure_mono {A} (f : WPureT A) : Prop :=
    forall p q : A -> Prop, (forall a, p a -> q a) -> f p -> f q.

  Definition WPure (A : Type) : Type := { f : WPureT A | wpure_mono f }.

  Definition getWPure {A} (w : WPure A) : (A -> Prop) -> Prop := proj1_sig w.
  Coercion getWPure : WPure >-> Funclass.

  Lemma getWPure_mono {A} (w : WPure A) (p q : A -> Prop) :
    (forall a, p a -> q a) -> getWPure w p -> getWPure w q.
  Proof. exact (proj2_sig w p q). Qed.

  (** Build an element from a raw transformer and a monotonicity proof. *)
  Definition mkWPure {A} (f : WPureT A) (H : wpure_mono f) : WPure A :=
    exist _ f H.

  (** ret and bind *)

  #[program] Definition retWPure {A} (a : A) : WPure A :=
    fun p => p a.
  Next Obligation.
    intros p q Hpq H. exact (Hpq a H).
  Qed.

  #[program] Definition bindWPure {A B} (m : WPure A) (k : A -> WPure B) : WPure B :=
    fun p => m (fun a => (k a) p).
  Next Obligation.
    intros p q Hpq H.
    apply (getWPure_mono m (fun a => getWPure (k a) p)); [| exact H ].
    intros a Ha. exact (getWPure_mono (k a) p q Hpq Ha).
  Qed.

  #[global] Instance Monad_WPure : Monad WPure :=
    { ret := @retWPure ; bind := @bindWPure }.

  (** Pointwise logical equivalence of the underlying transformers. *)
  #[global] Instance Eq1_WPure : Eq1 WPure :=
    fun A m1 m2 => forall p, getWPure m1 p <-> getWPure m2 p.

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
      + intro H. apply (proj1 (Hxy (fun a => getWPure (g a) p))).
        apply (getWPure_mono x (fun a => getWPure (f a) p)
                               (fun a => getWPure (g a) p)
                               (fun a Ha => proj1 (Hfg a p) Ha)).
        exact H.
      + intro H. apply (proj2 (Hxy (fun a => getWPure (f a) p))).
        apply (getWPure_mono y (fun a => getWPure (g a) p)
                               (fun a => getWPure (f a) p)
                               (fun a Ha => proj2 (Hfg a p) Ha)).
        exact H.
  Qed.

End WPure.

(** ** The refinement order on [WPure] *)

Definition WP_le {A} (w1 w2 : WPure A) : Prop :=
  forall k, getWPure w2 k -> getWPure w1 k.

#[global] Instance WP_le_PreOrder {A} : PreOrder (@WP_le A).
Proof.
  constructor; unfold WP_le.
  - intros x k H. exact H.
  - intros x y z H1 H2 k H. exact (H1 k (H2 k H)).
Qed.

(** [WPure] is a specification monad for its refinement order. *)
#[global] Instance OrderedMonad_WPure : OrderedMonad WPure (@WP_le).
Proof.
  constructor.
  - intro A. exact WP_le_PreOrder.
  - intros A x y H k Hk. exact (proj2 (H k) Hk).
  - intros A B m1 m2 Hm k1 k2 Hk q H.
    apply (getWPure_mono m1 (fun a => getWPure (k2 a) q)).
    + intros a Ha. exact (Hk a q Ha).
    + exact (Hm _ H).
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

(** Refinement on [WSt]: the generic [stateT] lift of [WP_le]. *)

Definition ordWSt {S A} : relation (WSt S A) := le_stateT (@WP_le) A.

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

(** Refinement on [WStExc]: the same lift, through [optionT]. *)

Definition ordWStExc {S A} : relation (WStExc S A) :=
  le_stateT (le_optionT (@WP_le)) A.

(* ================================================================= *)
(** ** Laws for the three stacks                                     *)
(* ================================================================= *)

(** Both chain through the generic [optionT] / [stateT] instances, which are
    [Eq1]-generic, so [Eq1_WPure] (pointwise iff) serves throughout. *)

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

(** [WSt] and [WStExc] are specification monads: their orders are the lifts
    of [WP_le] through the transformers, so they run backward (a weaker
    precondition is bigger), and the laws are the generic lifts of
    [OrderedMonad_WPure]. *)

Theorem OrderedMonad_WSt S :
  @OrderedMonad (WSt S) (Monad__WSt S) (Eq1__WSt S) (fun A => @ordWSt S A).
Proof. exact (OrderedMonad_stateT _ OrderedMonad_WPure). Qed.

Theorem OrderedMonad_WStExc S :
  @OrderedMonad (WStExc S) (Monad__WStExc S) (Eq1__WStExc S)
    (fun A => @ordWStExc S A).
Proof.
  exact (OrderedMonad_stateT _ (OrderedMonad_optionT _ OrderedMonad_WPure)).
Qed.

