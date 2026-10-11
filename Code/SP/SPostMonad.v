(** * [SPost]: the strongest-postcondition (forward predicate transformer) monad

        [Over p    := { q : Prop | q -> p }]        propositions implying [p]
        [SPost A   := { f : forall p:Prop, A -> Over p | monotone in p }]

        [ret a    := fun p y => (p /\ a = y)]
        [bind m k := fun p y => exists a, (k a) (m p a) y]

    [SPost] maps a precondition [p] to a predicate on results.  Each output
    proposition implies [p], as recorded by [Over].  Bind passes [m]'s
    postcondition at [a] to [k a] as its precondition.  The formulas above
    omit the [app] and [base] projections used below.

    This is DM4all's [SP] / [ForwardPredTransformer]
    ([sprop/SpecificationMonads.v], [Section StrongestPostcondition]),
    transcribed from [SProp] to [Prop].  [Eq1] compares the underlying
    propositions by logical equivalence, not by equality of bundled values.

    In the associativity proof, [over] recovers the intermediate witness.
    Monotonicity lets the proof replace a precondition by an equivalent one.

    Wrapped in [SPM] to distinguish this unary presentation from the binary
    arrows in [Arrows/SPostArr.v] and [Arrows/RelSPostArr.v].
    [RawSP.v] defines the unrestricted [SPPure] carrier. *)

From ITree Require Import Basics.Monad.
From Incorrectness.SP Require Import RawSP.

Module SPM.

  (* ================================================================= *)
  (** ** [Over p]: propositions implying [p]                           *)
  (* ================================================================= *)

  Record Over (p : Prop) : Type := mkOver { base : Prop ; over : base -> p }.

  Arguments mkOver {p} base over.
  Arguments base {p}.
  Arguments over {p}.

  (* ================================================================= *)
  (** ** The carrier                                                   *)
  (* ================================================================= *)

  Definition SPostT (A : Type) : Type := forall (p : Prop), A -> Over p.

  Definition sp_mono {A} (f : SPostT A) : Prop :=
    forall (p1 p2 : Prop) (a : A),
      (p1 -> p2) -> base (f p1 a) -> base (f p2 a).

  Definition SPost (A : Type) : Type := { f : SPostT A | sp_mono f }.

  (** [app m p a] is [m]'s postcondition at precondition [p] and result [a]. *)
  Definition app {A} (m : SPost A) (p : Prop) (a : A) : Prop :=
    base (proj1_sig m p a).

  Lemma app_over {A} (m : SPost A) (p : Prop) (a : A) : app m p a -> p.
  Proof. exact (over (proj1_sig m p a)). Qed.

  Lemma app_mono {A} (m : SPost A) (p1 p2 : Prop) (a : A) :
    (p1 -> p2) -> app m p1 a -> app m p2 a.
  Proof. exact (proj2_sig m p1 p2 a). Qed.

  (* ================================================================= *)
  (** ** [ret] and [bind]                                              *)
  (* ================================================================= *)

  Definition retSPT {A} (a : A) : SPostT A :=
    fun p y => mkOver (p /\ a = y) (fun H => proj1 H).

  Lemma retSP_mono {A} (a : A) : sp_mono (retSPT a).
  Proof.
    intros p1 p2 y Himp H. cbn in *.
    split; [ exact (Himp (proj1 H)) | exact (proj2 H) ].
  Qed.

  Definition retSP {A} (a : A) : SPost A := exist _ (retSPT a) (retSP_mono a).

  Lemma bind_over {A B} (m : SPost A) (k : A -> SPost B) (p : Prop) (y : B) :
    (exists a, app (k a) (app m p a) y) -> p.
  Proof.
    intros [a H]. exact (app_over m p a (app_over (k a) (app m p a) y H)).
  Qed.

  Definition bindSPT {A B} (m : SPost A) (k : A -> SPost B) : SPostT B :=
    fun p y => mkOver (exists a, app (k a) (app m p a) y) (bind_over m k p y).

  Lemma bindSP_mono {A B} (m : SPost A) (k : A -> SPost B) :
    sp_mono (bindSPT m k).
  Proof.
    intros p1 p2 y Himp H. cbn in *. destruct H as [a H]. exists a.
    exact (app_mono (k a) _ _ y (app_mono m p1 p2 a Himp) H).
  Qed.

  Definition bindSP {A B} (m : SPost A) (k : A -> SPost B) : SPost B :=
    exist _ (bindSPT m k) (bindSP_mono m k).

  #[global]
  Instance Monad_SPost : Monad SPost := {
    ret  := @retSP ;
    bind := @bindSP
  }.

  (** Pointwise equivalence of the underlying propositions. *)
  #[global]
  Instance Eq1_SPost : Eq1 SPost :=
    fun A m1 m2 => forall p a, app m1 p a <-> app m2 p a.

  (** [app] of [ret] and [bind], for rewriting. *)

  Lemma app_ret {A} (a : A) p y : app (retSP a) p y <-> (p /\ a = y).
  Proof. split; intro H; exact H. Qed.

  Lemma app_bind {A B} (m : SPost A) (k : A -> SPost B) p y :
    app (bindSP m k) p y <-> (exists a, app (k a) (app m p a) y).
  Proof. split; intro H; exact H. Qed.

End SPM.

(* ================================================================= *)
(** ** Monad laws                                                    *)
(* ================================================================= *)

Module SPMFacts.
  Import SPM.

  #[global]
  Instance Eq1Equivalence_SPost : @Eq1Equivalence SPost _ Eq1_SPost.
  Proof.
    constructor; repeat intro; unfold eq1, Eq1_SPost in *.
    - reflexivity.
    - symmetry. apply H.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  #[global]
  Instance MonadLawsE_SPost : @MonadLawsE SPost Eq1_SPost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. intros p y. cbn. split.
      + intros [a H].
        (* [over] on the inner application recovers [p /\ x = a] *)
        destruct (app_over (f a) (app (retSP x) p a) y H) as [Hp Heq].
        subst a. exact (app_mono (f x) _ p y (fun H0 => proj1 H0) H).
      + intro H. exists x.
        exact (app_mono (f x) p _ y (fun Hp => conj Hp eq_refl) H).
    - (* bind_ret_r *)
      intros A m p a. cbn. split.
      + intros [a' [H Heq]]. subst a'. exact H.
      + intro H. exists a. split; [ exact H | reflexivity ].
    - (* bind_bind *)
      intros A B C m f g p z. cbn. split.
      + intros [b H].
        (* [over] hands us the intermediate witness the RHS needs *)
        destruct (app_over (g b) _ z H) as [a Ha].
        exists a, b.
        exact (app_mono (g b) _ _ z (fun _ => Ha) H).
      + intros [a [b H]]. exists b.
        exact (app_mono (g b) _ _ z (fun Hf => ex_intro _ a Hf) H).
    - (* Proper_bind *)
      intros A B m1 m2 Hm k1 k2 Hk p y. cbn.
      unfold eq1, Eq1_SPost in Hm, Hk. split.
      + intros [a H]. exists a.
        apply (app_mono (k2 a) (app m1 p a) (app m2 p a) y
                 (fun H0 => proj1 (Hm p a) H0)).
        exact (proj1 (Hk a (app m1 p a) y) H).
      + intros [a H]. exists a.
        apply (app_mono (k1 a) (app m2 p a) (app m1 p a) y
                 (fun H0 => proj2 (Hm p a) H0)).
        exact (proj2 (Hk a (app m2 p a) y) H).
  Qed.

End SPMFacts.

(* ================================================================= *)
(** * Refinement order: [SPost] is a specification monad             *)
(* ================================================================= *)

(** Pointwise implication in the precondition and the result. *)

From Coq Require Import RelationClasses.
From Incorrectness.Lib.Monad Require Import OrderedMonad.

Definition SP_le {A} (m1 m2 : SPM.SPost A) : Prop :=
  forall p a, SPM.app m1 p a -> SPM.app m2 p a.

#[global] Instance SP_le_PreOrder {A} : PreOrder (@SP_le A).
Proof.
  constructor; unfold SP_le.
  - intros x p a H. exact H.
  - intros x y z H1 H2 p a H. exact (H2 p a (H1 p a H)).
Qed.

#[global] Instance OrderedMonad_SPost : OrderedMonad SPM.SPost (@SP_le).
Proof.
  constructor.
  - intro A. exact SP_le_PreOrder.
  - intros A x y H p a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk p b [a H]. exists a.
    apply (Hk a). exact (SPM.app_mono (k1 a) _ _ b (Hm p a) H).
Qed.

(* Initial attempts based on SPost and Kenji's work *)

Section KenjiPureSP.
  Definition Monotone {A} (w : SPPure A) : Prop :=
    forall (p q : Prop) (a : A), (p -> q) -> w p a -> w q a.

  Definition Codomain {A} (w : SPPure A) : Prop :=
    forall (p : Prop) (a : A), w p a -> p.

  Definition KenjiPureSP (A : Type) : Type := { w : SPPure A | Monotone w /\ Codomain w }.

  Definition getKenjiPureSP {A} (w : KenjiPureSP A) : SPPure A := proj1_sig w.

  #[program] Definition retKenjiPureSP {A} (v : A) : KenjiPureSP A :=
    fun pre a => pre /\ a = v.
  Next Obligation.
  Proof.
    split.
    - intros p q a Hpq [Hp Heq]. split; [exact (Hpq Hp) | exact Heq].
    - intros p a [Hp _]. exact Hp.
  Qed.
  
  #[program] Definition bindKenjiPureSP {A B} (m : KenjiPureSP A) (k : A -> KenjiPureSP B) : KenjiPureSP B :=
    fun pre b => exists a, k a (m pre a) b.
  Next Obligation.
  Proof.
    split.
    - (* monotone: weaken [pre] inside [m], then inside [k a] *)
      intros p q b Hpq [a Ha]. exists a.
      apply (proj1 (proj2_sig (k a)) (proj1_sig m p a) (proj1_sig m q a) b);
        [ intro Hm; exact (proj1 (proj2_sig m) p q a Hpq Hm) | exact Ha ].
    - (* codomain: [k a] returns its argument, which [m] returns [p] from *)
      intros p b [a Ha].
      exact (proj2 (proj2_sig m) p a (proj2 (proj2_sig (k a)) (proj1_sig m p a) b Ha)).
  Qed.
  
End KenjiPureSP.

Arguments KenjiPureSP {_}.


Section KenjiPureDSLP.
  Definition CodomainDSLP {A} (w : SPPure A) : Prop :=
    forall (p : Prop) (a : A), p -> w p a.

  Definition KenjiPureDSLP {A} (w : SPPure A) : Prop := Monotone w /\ CodomainDSLP w.
End KenjiPureDSLP.

