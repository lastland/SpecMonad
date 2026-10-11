(** * [WPure]: the monad of MONOTONE weakest-precondition transformers,
      and its two program-shaped stacks.

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

    The last part of the file carves the four WP flavours [AWP], [DWLP],
    [DWP], [AWLP] out of [WPure] by healthiness, as submonads. *)

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
      in [Arrows/WPArr.v] uses this with Leibniz [ArrowEq].  The [WPure]
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

(* ================================================================= *)
(** * The four WP specification monads: [AWP], [DWLP], [DWP], [AWLP]  *)
(* ================================================================= *)

(** Each is [WPure] cut down by a healthiness condition that [ret] and
    [bind] preserve, so each is a submonad of [WPure], with the state stack
    built as [WSt] is:

      [X]      = { f : WPureT A | f healthy }
      [XSt S]  = [stateT S X]

    The conditions are the homomorphism properties of [Arrows/SPostArr.v],
    stated for a transformer at one input.  All four flavours are monotone:

      [AWP]    strict, disjunctive        some outcome satisfies the postcondition
      [DWLP]   terminating, conjunctive   every outcome does
      [DWP]    strict, conjunctive        every outcome does, and none diverges
      [AWLP]   terminating, disjunctive   some outcome does, or one diverges

    Conjunctivity and disjunctivity quantify over NONEMPTY families;
    strictness and termination are the empty cases.

    These monads are not read off an arrow.  An arrow gives a monad when its
    input is fixed, and a weakest-precondition transformer has its
    postcondition, the output side, as argument.  They are built as [WPure]
    is, and [MonadTaxonomy.v] shows each carrier isomorphic to the arrow
    carrier with its second index fixed.

    The construction is done once, for any healthiness condition closed
    under [ret] and [bind] ([WPHealth], [WPSub]), and instantiated four
    times.

    Each monad carries two orders, both specification-monad orders:
    [WPure]'s refinement [WP_le] restricted to it (reverse implication) and
    its converse. *)

(* ================================================================= *)
(** ** Homomorphism properties of a unary transformer                *)
(* ================================================================= *)

Section Healthiness.
  Context {A : Type}.

  Definition wpure_strict (f : WPureT A) : Prop := ~ f (fun _ => False).

  Definition wpure_terminating (f : WPureT A) : Prop := f (fun _ => True).

  Definition wpure_conjunctive (f : WPureT A) : Prop :=
    forall (I : Type), inhabited I -> forall (q : I -> A -> Prop),
      f (fun a => forall i, q i a) <-> forall i, f (q i).

  Definition wpure_disjunctive (f : WPureT A) : Prop :=
    forall (I : Type), inhabited I -> forall (q : I -> A -> Prop),
      f (fun a => exists i, q i a) <-> exists i, f (q i).

  Lemma wpure_mono_ext (f : WPureT A) (p q : A -> Prop) :
    wpure_mono f -> (forall a, p a <-> q a) -> (f p <-> f q).
  Proof. intros Hm H. split; apply Hm; intro a; apply H. Qed.
End Healthiness.

(** Each property holds of [ret] and is preserved by [bind]. *)

Section RetClosure.
  Context {A : Type} (a : A).

  Lemma wpure_ret_mono : wpure_mono (fun p : A -> Prop => p a).
  Proof. intros p q H Hp. exact (H a Hp). Qed.

  Lemma wpure_ret_strict : wpure_strict (fun p : A -> Prop => p a).
  Proof. intro H. exact H. Qed.

  Lemma wpure_ret_terminating : wpure_terminating (fun p : A -> Prop => p a).
  Proof. exact I. Qed.

  Lemma wpure_ret_conjunctive : wpure_conjunctive (fun p : A -> Prop => p a).
  Proof. intros I _ q. reflexivity. Qed.

  Lemma wpure_ret_disjunctive : wpure_disjunctive (fun p : A -> Prop => p a).
  Proof. intros I _ q. reflexivity. Qed.
End RetClosure.

Section BindClosure.
  Context {A B : Type} (m : WPureT A) (k : A -> WPureT B).

  Lemma wpure_bind_mono :
    wpure_mono m -> (forall a, wpure_mono (k a)) ->
    wpure_mono (fun p => m (fun a => k a p)).
  Proof. intros Hm Hk p q H. apply Hm. intro a. exact (Hk a p q H). Qed.

  Lemma wpure_bind_strict :
    wpure_mono m -> wpure_strict m -> (forall a, wpure_strict (k a)) ->
    wpure_strict (fun p => m (fun a => k a p)).
  Proof.
    intros Hm Hs Hk H. apply Hs. refine (Hm _ _ _ H). intros a Ha. exact (Hk a Ha).
  Qed.

  Lemma wpure_bind_terminating :
    wpure_mono m -> wpure_terminating m -> (forall a, wpure_terminating (k a)) ->
    wpure_terminating (fun p => m (fun a => k a p)).
  Proof. intros Hm Ht Hk. refine (Hm _ _ _ Ht). intros a _. exact (Hk a). Qed.

  Lemma wpure_bind_conjunctive :
    wpure_mono m -> wpure_conjunctive m -> (forall a, wpure_conjunctive (k a)) ->
    wpure_conjunctive (fun p => m (fun a => k a p)).
  Proof.
    intros Hm Hc Hk I HI q.
    transitivity (m (fun a => forall i, k a (q i))).
    - apply (wpure_mono_ext m); [ exact Hm | intro a; exact (Hk a I HI q) ].
    - exact (Hc I HI (fun i a => k a (q i))).
  Qed.

  Lemma wpure_bind_disjunctive :
    wpure_mono m -> wpure_disjunctive m -> (forall a, wpure_disjunctive (k a)) ->
    wpure_disjunctive (fun p => m (fun a => k a p)).
  Proof.
    intros Hm Hd Hk I HI q.
    transitivity (m (fun a => exists i, k a (q i))).
    - apply (wpure_mono_ext m); [ exact Hm | intro a; exact (Hk a I HI q) ].
    - exact (Hd I HI (fun i a => k a (q i))).
  Qed.
End BindClosure.

(* ================================================================= *)
(** ** A healthiness condition cuts a submonad out of [WPure]        *)
(* ================================================================= *)

(** A property of unary transformers that implies monotonicity, holds of
    [ret] and is preserved by [bind]. *)
Record WPHealth : Type := {
  wph :> forall A : Type, WPureT A -> Prop ;
  wph_mono : forall A (f : WPureT A), wph A f -> wpure_mono f ;
  wph_ret : forall A (a : A), wph A (fun p => p a) ;
  wph_bind : forall A B (m : WPureT A) (k : A -> WPureT B),
      wph A m -> (forall a, wph B (k a)) -> wph B (fun p => m (fun a => k a p))
}.

Section WPSub.
  Variable h : WPHealth.

  Definition WPSub (A : Type) : Type := { f : WPureT A | h A f }.

  Definition getWPSub {A} (w : WPSub A) : (A -> Prop) -> Prop := proj1_sig w.

  Lemma getWPSub_mono {A} (w : WPSub A) (p q : A -> Prop) :
    (forall a, p a -> q a) -> getWPSub w p -> getWPSub w q.
  Proof. exact (wph_mono h A _ (proj2_sig w) p q). Qed.

  Definition retWPSub {A} (a : A) : WPSub A :=
    exist _ (fun p => p a) (wph_ret h A a).

  Definition bindWPSub {A B} (m : WPSub A) (k : A -> WPSub B) : WPSub B :=
    exist _ (fun p => getWPSub m (fun a => getWPSub (k a) p))
      (wph_bind h A B _ _ (proj2_sig m) (fun a => proj2_sig (k a))).

  Definition Monad_WPSub : Monad WPSub :=
    {| ret := @retWPSub ; bind := @bindWPSub |}.

  (** Pointwise logical equivalence of the underlying transformers. *)
  Definition Eq1_WPSub : Eq1 WPSub :=
    fun A m1 m2 => forall p, getWPSub m1 p <-> getWPSub m2 p.

  Lemma Eq1Equivalence_WPSub : @Eq1Equivalence WPSub Monad_WPSub Eq1_WPSub.
  Proof.
    constructor; unfold eq1, Eq1_WPSub.
    - intros x p. reflexivity.
    - intros x y H p. symmetry. exact (H p).
    - intros x y z H1 H2 p. etransitivity; [ exact (H1 p) | exact (H2 p) ].
  Qed.

  Lemma MonadLawsE_WPSub : @MonadLawsE WPSub Eq1_WPSub Monad_WPSub.
  Proof.
    constructor; unfold eq1, Eq1_WPSub.
    - intros A B f x p. reflexivity.
    - intros A x p. reflexivity.
    - intros A B C x f g p. reflexivity.
    - intros A B x y Hxy f g Hfg p. cbn. split.
      + intro H. apply (proj1 (Hxy _)).
        refine (getWPSub_mono x _ _ _ H). intros a Ha. exact (proj1 (Hfg a p) Ha).
      + intro H. apply (proj2 (Hxy _)).
        refine (getWPSub_mono y _ _ _ H). intros a Ha. exact (proj2 (Hfg a p) Ha).
  Qed.

  (** The inclusion into [WPure] forgets the condition; it is a monad
      morphism. *)
  Definition toWPure {A} (w : WPSub A) : WPure A :=
    mkWPure (getWPSub w) (wph_mono h A _ (proj2_sig w)).

  Lemma toWPure_ret {A} (a : A) : eq1 (toWPure (retWPSub a)) (ret a).
  Proof. intro p. reflexivity. Qed.

  Lemma toWPure_bind {A B} (m : WPSub A) (k : A -> WPSub B) :
    eq1 (toWPure (bindWPSub m k)) (bind (toWPure m) (fun a => toWPure (k a))).
  Proof. intro p. reflexivity. Qed.

  (** Refinement: [WP_le] along the inclusion. *)
  Definition WPSub_le {A} (w1 w2 : WPSub A) : Prop :=
    forall p, getWPSub w2 p -> getWPSub w1 p.

  Lemma WPSub_le_toWPure {A} (w1 w2 : WPSub A) :
    WPSub_le w1 w2 <-> WP_le (toWPure w1) (toWPure w2).
  Proof. split; intro H; exact H. Qed.

  Lemma toWPure_morphism :
    @MonadMorphism WPSub WPure Monad_WPSub Monad_WPure Eq1_WPSub Eq1_WPure
      (fun A => @toWPure A).
  Proof.
    constructor.
    - intros A x y H. exact H.
    - intros A a. exact (toWPure_ret a).
    - intros A B m k. exact (toWPure_bind m k).
  Qed.

  (** A submonad of [WPure] is a specification monad: its order is that of
      [WPure] along the inclusion. *)
  Lemma OrderedMonad_WPSub : @OrderedMonad WPSub Monad_WPSub Eq1_WPSub (@WPSub_le).
  Proof.
    exact (OrderedMonad_pullback (fun A => @toWPure A) (@WP_le)
             toWPure_morphism OrderedMonad_WPure).
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** The state stack                                             *)
  (* --------------------------------------------------------------- *)

  Section St.
    Variable S : Type.

    Definition WPSubSt : Type -> Type := stateT S WPSub.

    Definition Monad_WPSubSt : Monad WPSubSt := @Monad_stateT S WPSub Monad_WPSub.

    Definition Eq1_WPSubSt : Eq1 WPSubSt := @Eq1_stateT S WPSub Eq1_WPSub.

    Definition Eq1Equivalence_WPSubSt
      : @Eq1Equivalence WPSubSt Monad_WPSubSt Eq1_WPSubSt :=
      @Eq1Equivalence_stateT S WPSub Monad_WPSub Eq1_WPSub Eq1Equivalence_WPSub.

    Definition MonadLawsE_WPSubSt
      : @MonadLawsE WPSubSt Eq1_WPSubSt Monad_WPSubSt :=
      @MonadLawsE_stateT S WPSub Monad_WPSub Eq1_WPSub Eq1Equivalence_WPSub
        MonadLawsE_WPSub.

    Definition WPSubSt_le {A} : relation (WPSubSt A) :=
      @le_stateT S WPSub (@WPSub_le) A.

    Definition OrderedMonad_WPSubSt
      : @OrderedMonad WPSubSt Monad_WPSubSt Eq1_WPSubSt (@WPSubSt_le) :=
      @OrderedMonad_stateT S WPSub Monad_WPSub Eq1_WPSub (@WPSub_le)
        OrderedMonad_WPSub.

    (** The transformer an element denotes: a postcondition on results and
        final states goes to the initial states that guarantee it. *)
    Definition getWPSubSt {A} (w : WPSubSt A) (Q : A * S -> Prop) (s : S) : Prop :=
      getWPSub (runStateT w s) Q.

    Lemma getWPSubSt_mono {A} (w : WPSubSt A) (Q1 Q2 : A * S -> Prop) s :
      (forall r, Q1 r -> Q2 r) -> getWPSubSt w Q1 s -> getWPSubSt w Q2 s.
    Proof. apply getWPSub_mono. Qed.

    Lemma getWPSubSt_ret {A} (a : A) Q s :
      getWPSubSt (@ret WPSubSt Monad_WPSubSt A a) Q s <-> Q (a, s).
    Proof. reflexivity. Qed.

    Lemma getWPSubSt_bind {A B} (m : WPSubSt A) (k : A -> WPSubSt B) Q s :
      getWPSubSt (@bind WPSubSt Monad_WPSubSt A B m k) Q s
      <-> getWPSubSt m (fun r => getWPSubSt (k (fst r)) Q (snd r)) s.
    Proof.
      unfold getWPSubSt. cbn.
      split; apply getWPSub_mono; intros [a s'] H; exact H.
    Qed.

    Lemma eq1_WPSubSt_get {A} (w1 w2 : WPSubSt A) :
      @eq1 WPSubSt Eq1_WPSubSt A w1 w2
      <-> (forall Q s, getWPSubSt w1 Q s <-> getWPSubSt w2 Q s).
    Proof. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ]. Qed.

    Lemma WPSubSt_le_get {A} (w1 w2 : WPSubSt A) :
      WPSubSt_le w1 w2 <-> (forall Q s, getWPSubSt w2 Q s -> getWPSubSt w1 Q s).
    Proof. split; [ intros H Q s; exact (H s Q) | intros H s Q; exact (H Q s) ]. Qed.

    (** The inclusion into [WSt S]. *)
    Definition toWSt {A} (w : WPSubSt A) : WSt S A :=
      mkStateT (fun s => toWPure (runStateT w s)).

    Lemma toWSt_get {A} (w : WPSubSt A) Q s :
      getWPure (runStateT (toWSt w) s) Q <-> getWPSubSt w Q s.
    Proof. reflexivity. Qed.

    Lemma WPSubSt_le_toWSt {A} (w1 w2 : WPSubSt A) :
      WPSubSt_le w1 w2 <-> ordWSt (toWSt w1) (toWSt w2).
    Proof. split; intro H; exact H. Qed.

    Lemma eq1_toWSt {A} (w1 w2 : WPSubSt A) :
      @eq1 WPSubSt Eq1_WPSubSt A w1 w2
      <-> @eq1 (WSt S) (Eq1__WSt S) A (toWSt w1) (toWSt w2).
    Proof. split; intro H; exact H. Qed.

    (** It is a monad morphism. *)
    Lemma toWSt_ret {A} (a : A) :
      @eq1 (WSt S) (Eq1__WSt S) A (toWSt (@ret WPSubSt Monad_WPSubSt A a)) (ret a).
    Proof. intros s Q. reflexivity. Qed.

    Lemma toWSt_bind {A B} (w : WPSubSt A) (k : A -> WPSubSt B) :
      @eq1 (WSt S) (Eq1__WSt S) B
        (toWSt (@bind WPSubSt Monad_WPSubSt A B w k))
        (bind (toWSt w) (fun a => toWSt (k a))).
    Proof.
      intros s Q. cbn. split; apply getWPSub_mono; intros [a s'] H; exact H.
    Qed.
  End St.
End WPSub.

Arguments getWPSub {h} {A}.
Arguments getWPSubSt {h} {S} {A}.
Arguments toWPure {h} {A}.
Arguments toWSt {h} {S} {A}.
Arguments WPSub_le {h} {A}.
Arguments WPSubSt_le {h} {S} {A}.

(* ================================================================= *)
(** ** The four conditions                                           *)
(* ================================================================= *)

Definition awp_health : WPHealth :=
  {| wph := fun A (f : WPureT A) => wpure_mono f /\ wpure_strict f /\ wpure_disjunctive f ;
     wph_mono := fun A f H => proj1 H ;
     wph_ret := fun A a =>
       conj (wpure_ret_mono a) (conj (wpure_ret_strict a) (wpure_ret_disjunctive a)) ;
     wph_bind := fun A B m k Hm Hk =>
       conj (wpure_bind_mono m k (proj1 Hm) (fun a => proj1 (Hk a)))
         (conj (wpure_bind_strict m k (proj1 Hm) (proj1 (proj2 Hm))
                  (fun a => proj1 (proj2 (Hk a))))
               (wpure_bind_disjunctive m k (proj1 Hm) (proj2 (proj2 Hm))
                  (fun a => proj2 (proj2 (Hk a))))) |}.

Definition dwlp_health : WPHealth :=
  {| wph := fun A (f : WPureT A) =>
       wpure_mono f /\ wpure_terminating f /\ wpure_conjunctive f ;
     wph_mono := fun A f H => proj1 H ;
     wph_ret := fun A a =>
       conj (wpure_ret_mono a) (conj (wpure_ret_terminating a) (wpure_ret_conjunctive a)) ;
     wph_bind := fun A B m k Hm Hk =>
       conj (wpure_bind_mono m k (proj1 Hm) (fun a => proj1 (Hk a)))
         (conj (wpure_bind_terminating m k (proj1 Hm) (proj1 (proj2 Hm))
                  (fun a => proj1 (proj2 (Hk a))))
               (wpure_bind_conjunctive m k (proj1 Hm) (proj2 (proj2 Hm))
                  (fun a => proj2 (proj2 (Hk a))))) |}.

Definition dwp_health : WPHealth :=
  {| wph := fun A (f : WPureT A) => wpure_mono f /\ wpure_strict f /\ wpure_conjunctive f ;
     wph_mono := fun A f H => proj1 H ;
     wph_ret := fun A a =>
       conj (wpure_ret_mono a) (conj (wpure_ret_strict a) (wpure_ret_conjunctive a)) ;
     wph_bind := fun A B m k Hm Hk =>
       conj (wpure_bind_mono m k (proj1 Hm) (fun a => proj1 (Hk a)))
         (conj (wpure_bind_strict m k (proj1 Hm) (proj1 (proj2 Hm))
                  (fun a => proj1 (proj2 (Hk a))))
               (wpure_bind_conjunctive m k (proj1 Hm) (proj2 (proj2 Hm))
                  (fun a => proj2 (proj2 (Hk a))))) |}.

Definition awlp_health : WPHealth :=
  {| wph := fun A (f : WPureT A) =>
       wpure_mono f /\ wpure_terminating f /\ wpure_disjunctive f ;
     wph_mono := fun A f H => proj1 H ;
     wph_ret := fun A a =>
       conj (wpure_ret_mono a) (conj (wpure_ret_terminating a) (wpure_ret_disjunctive a)) ;
     wph_bind := fun A B m k Hm Hk =>
       conj (wpure_bind_mono m k (proj1 Hm) (fun a => proj1 (Hk a)))
         (conj (wpure_bind_terminating m k (proj1 Hm) (proj1 (proj2 Hm))
                  (fun a => proj1 (proj2 (Hk a))))
               (wpure_bind_disjunctive m k (proj1 Hm) (proj2 (proj2 Hm))
                  (fun a => proj2 (proj2 (Hk a))))) |}.

(* ================================================================= *)
(** ** [AWP]: angelic, total                                         *)
(* ================================================================= *)

Definition AWP : Type -> Type := WPSub awp_health.

Definition getAWP {A} (w : AWP A) : (A -> Prop) -> Prop := getWPSub w.
Coercion getAWP : AWP >-> Funclass.

#[global] Instance Monad_AWP : Monad AWP := Monad_WPSub awp_health.
#[global] Instance Eq1_AWP : Eq1 AWP := Eq1_WPSub awp_health.
#[global] Instance Eq1Equivalence_AWP : @Eq1Equivalence AWP Monad_AWP Eq1_AWP :=
  Eq1Equivalence_WPSub awp_health.
#[global] Instance MonadLawsE_AWP : @MonadLawsE AWP Eq1_AWP Monad_AWP :=
  MonadLawsE_WPSub awp_health.

Definition ordAWP {A} : relation (AWP A) := @WPSub_le awp_health A.
Definition ordAWPop {A} : relation (AWP A) := fun w1 w2 => ordAWP w2 w1.

#[global] Instance OrderedMonad_AWP : OrderedMonad AWP (@ordAWP) :=
  OrderedMonad_WPSub awp_health.
#[global] Instance OrderedMonad_AWP_op : OrderedMonad AWP (@ordAWPop) :=
  OrderedMonad_flip (@ordAWP) OrderedMonad_AWP.

Definition AWPSt (S : Type) : Type -> Type := WPSubSt awp_health S.

Definition getAWPSt {S A} (w : AWPSt S A) : (A * S -> Prop) -> S -> Prop :=
  getWPSubSt w.

#[global] Instance Monad_AWPSt S : Monad (AWPSt S) := Monad_WPSubSt awp_health S.
#[global] Instance Eq1_AWPSt S : Eq1 (AWPSt S) := Eq1_WPSubSt awp_health S.
#[global] Instance Eq1Equivalence_AWPSt S
  : @Eq1Equivalence (AWPSt S) (Monad_AWPSt S) (Eq1_AWPSt S) :=
  Eq1Equivalence_WPSubSt awp_health S.
#[global] Instance MonadLawsE_AWPSt S
  : @MonadLawsE (AWPSt S) (Eq1_AWPSt S) (Monad_AWPSt S) :=
  MonadLawsE_WPSubSt awp_health S.

Definition ordAWPSt {S A} : relation (AWPSt S A) := @WPSubSt_le awp_health S A.
Definition ordAWPStOp {S A} : relation (AWPSt S A) := fun w1 w2 => ordAWPSt w2 w1.

#[global] Instance OrderedMonad_AWPSt S : OrderedMonad (AWPSt S) (@ordAWPSt S) :=
  OrderedMonad_WPSubSt awp_health S.
#[global] Instance OrderedMonad_AWPSt_op S : OrderedMonad (AWPSt S) (@ordAWPStOp S) :=
  OrderedMonad_flip (@ordAWPSt S) (OrderedMonad_AWPSt S).

(* ================================================================= *)
(** ** [DWLP]: demonic, liberal                                      *)
(* ================================================================= *)

Definition DWLP : Type -> Type := WPSub dwlp_health.

Definition getDWLP {A} (w : DWLP A) : (A -> Prop) -> Prop := getWPSub w.
Coercion getDWLP : DWLP >-> Funclass.

#[global] Instance Monad_DWLP : Monad DWLP := Monad_WPSub dwlp_health.
#[global] Instance Eq1_DWLP : Eq1 DWLP := Eq1_WPSub dwlp_health.
#[global] Instance Eq1Equivalence_DWLP : @Eq1Equivalence DWLP Monad_DWLP Eq1_DWLP :=
  Eq1Equivalence_WPSub dwlp_health.
#[global] Instance MonadLawsE_DWLP : @MonadLawsE DWLP Eq1_DWLP Monad_DWLP :=
  MonadLawsE_WPSub dwlp_health.

Definition ordDWLP {A} : relation (DWLP A) := @WPSub_le dwlp_health A.
Definition ordDWLPop {A} : relation (DWLP A) := fun w1 w2 => ordDWLP w2 w1.

#[global] Instance OrderedMonad_DWLP : OrderedMonad DWLP (@ordDWLP) :=
  OrderedMonad_WPSub dwlp_health.
#[global] Instance OrderedMonad_DWLP_op : OrderedMonad DWLP (@ordDWLPop) :=
  OrderedMonad_flip (@ordDWLP) OrderedMonad_DWLP.

Definition DWLPSt (S : Type) : Type -> Type := WPSubSt dwlp_health S.

Definition getDWLPSt {S A} (w : DWLPSt S A) : (A * S -> Prop) -> S -> Prop :=
  getWPSubSt w.

#[global] Instance Monad_DWLPSt S : Monad (DWLPSt S) := Monad_WPSubSt dwlp_health S.
#[global] Instance Eq1_DWLPSt S : Eq1 (DWLPSt S) := Eq1_WPSubSt dwlp_health S.
#[global] Instance Eq1Equivalence_DWLPSt S
  : @Eq1Equivalence (DWLPSt S) (Monad_DWLPSt S) (Eq1_DWLPSt S) :=
  Eq1Equivalence_WPSubSt dwlp_health S.
#[global] Instance MonadLawsE_DWLPSt S
  : @MonadLawsE (DWLPSt S) (Eq1_DWLPSt S) (Monad_DWLPSt S) :=
  MonadLawsE_WPSubSt dwlp_health S.

Definition ordDWLPSt {S A} : relation (DWLPSt S A) := @WPSubSt_le dwlp_health S A.
Definition ordDWLPStOp {S A} : relation (DWLPSt S A) := fun w1 w2 => ordDWLPSt w2 w1.

#[global] Instance OrderedMonad_DWLPSt S : OrderedMonad (DWLPSt S) (@ordDWLPSt S) :=
  OrderedMonad_WPSubSt dwlp_health S.
#[global] Instance OrderedMonad_DWLPSt_op S : OrderedMonad (DWLPSt S) (@ordDWLPStOp S) :=
  OrderedMonad_flip (@ordDWLPSt S) (OrderedMonad_DWLPSt S).

(* ================================================================= *)
(** ** [DWP]: demonic, total                                         *)
(* ================================================================= *)

Definition DWP : Type -> Type := WPSub dwp_health.

Definition getDWP {A} (w : DWP A) : (A -> Prop) -> Prop := getWPSub w.
Coercion getDWP : DWP >-> Funclass.

#[global] Instance Monad_DWP : Monad DWP := Monad_WPSub dwp_health.
#[global] Instance Eq1_DWP : Eq1 DWP := Eq1_WPSub dwp_health.
#[global] Instance Eq1Equivalence_DWP : @Eq1Equivalence DWP Monad_DWP Eq1_DWP :=
  Eq1Equivalence_WPSub dwp_health.
#[global] Instance MonadLawsE_DWP : @MonadLawsE DWP Eq1_DWP Monad_DWP :=
  MonadLawsE_WPSub dwp_health.

Definition ordDWP {A} : relation (DWP A) := @WPSub_le dwp_health A.
Definition ordDWPop {A} : relation (DWP A) := fun w1 w2 => ordDWP w2 w1.

#[global] Instance OrderedMonad_DWP : OrderedMonad DWP (@ordDWP) :=
  OrderedMonad_WPSub dwp_health.
#[global] Instance OrderedMonad_DWP_op : OrderedMonad DWP (@ordDWPop) :=
  OrderedMonad_flip (@ordDWP) OrderedMonad_DWP.

Definition DWPSt (S : Type) : Type -> Type := WPSubSt dwp_health S.

Definition getDWPSt {S A} (w : DWPSt S A) : (A * S -> Prop) -> S -> Prop :=
  getWPSubSt w.

#[global] Instance Monad_DWPSt S : Monad (DWPSt S) := Monad_WPSubSt dwp_health S.
#[global] Instance Eq1_DWPSt S : Eq1 (DWPSt S) := Eq1_WPSubSt dwp_health S.
#[global] Instance Eq1Equivalence_DWPSt S
  : @Eq1Equivalence (DWPSt S) (Monad_DWPSt S) (Eq1_DWPSt S) :=
  Eq1Equivalence_WPSubSt dwp_health S.
#[global] Instance MonadLawsE_DWPSt S
  : @MonadLawsE (DWPSt S) (Eq1_DWPSt S) (Monad_DWPSt S) :=
  MonadLawsE_WPSubSt dwp_health S.

Definition ordDWPSt {S A} : relation (DWPSt S A) := @WPSubSt_le dwp_health S A.
Definition ordDWPStOp {S A} : relation (DWPSt S A) := fun w1 w2 => ordDWPSt w2 w1.

#[global] Instance OrderedMonad_DWPSt S : OrderedMonad (DWPSt S) (@ordDWPSt S) :=
  OrderedMonad_WPSubSt dwp_health S.
#[global] Instance OrderedMonad_DWPSt_op S : OrderedMonad (DWPSt S) (@ordDWPStOp S) :=
  OrderedMonad_flip (@ordDWPSt S) (OrderedMonad_DWPSt S).

(* ================================================================= *)
(** ** [AWLP]: angelic, liberal                                      *)
(* ================================================================= *)

Definition AWLP : Type -> Type := WPSub awlp_health.

Definition getAWLP {A} (w : AWLP A) : (A -> Prop) -> Prop := getWPSub w.
Coercion getAWLP : AWLP >-> Funclass.

#[global] Instance Monad_AWLP : Monad AWLP := Monad_WPSub awlp_health.
#[global] Instance Eq1_AWLP : Eq1 AWLP := Eq1_WPSub awlp_health.
#[global] Instance Eq1Equivalence_AWLP : @Eq1Equivalence AWLP Monad_AWLP Eq1_AWLP :=
  Eq1Equivalence_WPSub awlp_health.
#[global] Instance MonadLawsE_AWLP : @MonadLawsE AWLP Eq1_AWLP Monad_AWLP :=
  MonadLawsE_WPSub awlp_health.

Definition ordAWLP {A} : relation (AWLP A) := @WPSub_le awlp_health A.
Definition ordAWLPop {A} : relation (AWLP A) := fun w1 w2 => ordAWLP w2 w1.

#[global] Instance OrderedMonad_AWLP : OrderedMonad AWLP (@ordAWLP) :=
  OrderedMonad_WPSub awlp_health.
#[global] Instance OrderedMonad_AWLP_op : OrderedMonad AWLP (@ordAWLPop) :=
  OrderedMonad_flip (@ordAWLP) OrderedMonad_AWLP.

Definition AWLPSt (S : Type) : Type -> Type := WPSubSt awlp_health S.

Definition getAWLPSt {S A} (w : AWLPSt S A) : (A * S -> Prop) -> S -> Prop :=
  getWPSubSt w.

#[global] Instance Monad_AWLPSt S : Monad (AWLPSt S) := Monad_WPSubSt awlp_health S.
#[global] Instance Eq1_AWLPSt S : Eq1 (AWLPSt S) := Eq1_WPSubSt awlp_health S.
#[global] Instance Eq1Equivalence_AWLPSt S
  : @Eq1Equivalence (AWLPSt S) (Monad_AWLPSt S) (Eq1_AWLPSt S) :=
  Eq1Equivalence_WPSubSt awlp_health S.
#[global] Instance MonadLawsE_AWLPSt S
  : @MonadLawsE (AWLPSt S) (Eq1_AWLPSt S) (Monad_AWLPSt S) :=
  MonadLawsE_WPSubSt awlp_health S.

Definition ordAWLPSt {S A} : relation (AWLPSt S A) := @WPSubSt_le awlp_health S A.
Definition ordAWLPStOp {S A} : relation (AWLPSt S A) := fun w1 w2 => ordAWLPSt w2 w1.

#[global] Instance OrderedMonad_AWLPSt S : OrderedMonad (AWLPSt S) (@ordAWLPSt S) :=
  OrderedMonad_WPSubSt awlp_health S.
#[global] Instance OrderedMonad_AWLPSt_op S : OrderedMonad (AWLPSt S) (@ordAWLPStOp S) :=
  OrderedMonad_flip (@ordAWLPSt S) (OrderedMonad_AWLPSt S).
