(** * Ordered monads: the specification-monad criterion of DM4All

    DM4All ([theories/sprop/SPropMonadicStructures.v], [OrderedMonad]) calls a
    monad [W] a specification monad when each [W A] carries a preorder and
    [bind] is monotone in both arguments.  Its monad laws are equalities; here
    they hold up to [eq1], so the order is additionally required to contain
    [eq1] — otherwise a law could relate two elements the order separates.

    Every monad is ordered by [eq1] itself ([OrderedMonad_eq1], DM4All's
    [DiscreteMonad]), so the criterion only has content relative to a chosen
    order.

    The second half of the file has the other ingredient of an effect
    observation, a monad morphism ([MonadMorphism]).  The triple of a
    computation through one is in [Verification/Triples/Triple.v].

    Lifts through [optionT] / [stateT] are in
    [Lib/Monad/TransformerLaws.v]. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.

Class OrderedMonad (W : Type -> Type) {MonadW : Monad W} {Eq1W : Eq1 W}
  (le : forall A, relation (W A)) : Prop := {
  om_preorder : forall A, PreOrder (le A);
  om_eq1 : forall A (x y : W A), eq1 x y -> le A x y;
  om_bind : forall A B,
    Proper (le A ==> pointwise_relation A (le B) ==> le B) (@bind W _ A B)
}.

Section Generic.
  Context {W : Type -> Type} {MonadW : Monad W} {Eq1W : Eq1 W}.

  Theorem OrderedMonad_eq1 {EqW : @Eq1Equivalence W MonadW Eq1W}
    {LawsW : @MonadLawsE W Eq1W MonadW} :
    OrderedMonad W (fun A => @eq1 W _ A).
  Proof.
    constructor.
    - intro A. destruct (EqW A) as [Hr _ Ht]. constructor; assumption.
    - intros A x y H. exact H.
    - intros A B. apply Proper_bind.
  Qed.

  (** The criterion does not see the direction of the order. *)
  Theorem OrderedMonad_flip {EqW : @Eq1Equivalence W MonadW Eq1W}
    (le : forall A, relation (W A)) :
    OrderedMonad W le -> OrderedMonad W (fun A x y => le A y x).
  Proof.
    intros [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre A) as [Hr Ht].
      constructor; [ intro x; apply Hr | intros x y z H1 H2; exact (Ht _ _ _ H2 H1) ].
    - intros A x y H. apply Heq. destruct (EqW A) as [_ Hs _]. exact (Hs _ _ H).
    - intros A B m1 m2 Hm k1 k2 Hk. exact (Hbind A B m2 m1 Hm k2 k1 Hk).
  Qed.

  (** Transport along a pointwise-equivalent order. *)
  Theorem OrderedMonad_iff (le le' : forall A, relation (W A)) :
    (forall A x y, le A x y <-> le' A x y) ->
    OrderedMonad W le -> OrderedMonad W le'.
  Proof.
    intros E [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre A) as [Hr Ht]. constructor.
      + intro x. apply E. apply Hr.
      + intros x y z H1 H2. apply E. apply E in H1, H2. exact (Ht _ _ _ H1 H2).
    - intros A x y H. apply E. exact (Heq A x y H).
    - intros A B m1 m2 Hm k1 k2 Hk. apply E.
      apply Hbind; [ apply E; exact Hm | intro a; apply E; exact (Hk a) ].
  Qed.

  (** A monad with no ordered structure under [le] cannot be ordered: one
      failing instance of monotonicity in the first argument suffices. *)
  Theorem not_OrderedMonad (le : forall A, relation (W A)) {A B}
    (m1 m2 : W A) (k : A -> W B) :
    (forall a, le B (k a) (k a)) ->
    le A m1 m2 -> ~ le B (bind m1 k) (bind m2 k) ->
    ~ OrderedMonad W le.
  Proof.
    intros Hk Hm Hbad [_ _ Hbind]. exact (Hbad (Hbind A B m1 m2 Hm k k Hk)).
  Qed.
End Generic.

(* ================================================================= *)
(** * Monad morphisms                                                 *)
(* ================================================================= *)

(** [σ : forall A, M A -> W A] is a monad morphism when it respects both
    monads' [eq1] and preserves [ret] and [bind] up to [W]'s [eq1].

    ITree's [Extra/Dijkstra/DijkstraMonad.MonadMorphism] is the special case
    of an effect observation into an ordered monad.  This record asks for no
    order on [W], and it asks the map to respect the source's [eq1], which
    composition needs. *)

Record MonadMorphism {M W : Type -> Type} {MonadM : Monad M} {MonadW : Monad W}
  {Eq1M : Eq1 M} {Eq1W : Eq1 W} (σ : forall A, M A -> W A) : Prop := {
  mm_proper : forall A (x y : M A), eq1 x y -> eq1 (σ A x) (σ A y) ;
  mm_ret : forall A (a : A), eq1 (σ A (ret a)) (ret a) ;
  mm_bind : forall A B (x : M A) (k : A -> M B),
      eq1 (σ B (bind x k)) (bind (σ A x) (fun a => σ B (k a)))
}.

Arguments mm_proper {M W MonadM MonadW Eq1M Eq1W σ} _ {A} x y.
Arguments mm_ret {M W MonadM MonadW Eq1M Eq1W σ} _ {A} a.
Arguments mm_bind {M W MonadM MonadW Eq1M Eq1W σ} _ {A B} x k.

Theorem MonadMorphism_comp {M V W : Type -> Type}
  {MonadM : Monad M} {MonadV : Monad V} {MonadW : Monad W}
  {Eq1M : Eq1 M} {Eq1V : Eq1 V} {Eq1W : Eq1 W}
  {EqW : @Eq1Equivalence W MonadW Eq1W}
  (σ : forall A, M A -> V A) (τ : forall A, V A -> W A) :
  @MonadMorphism M V MonadM MonadV Eq1M Eq1V σ ->
  @MonadMorphism V W MonadV MonadW Eq1V Eq1W τ ->
  @MonadMorphism M W MonadM MonadW Eq1M Eq1W (fun A x => τ A (σ A x)).
Proof.
  intros Hσ Hτ. constructor.
  - intros A x y Hxy. apply (mm_proper Hτ). exact (mm_proper Hσ x y Hxy).
  - intros A a. destruct (EqW A) as [_ _ Ht].
    exact (Ht _ _ _ (mm_proper Hτ _ _ (mm_ret Hσ a)) (mm_ret Hτ a)).
  - intros A B x k. destruct (EqW B) as [_ _ Ht].
    exact (Ht _ _ _ (mm_proper Hτ _ _ (mm_bind Hσ x k))
              (mm_bind Hτ (σ A x) (fun a => σ B (k a)))).
Qed.

(** A map that agrees pointwise with a morphism is one. *)
Theorem MonadMorphism_ext {M W : Type -> Type}
  {MonadM : Monad M} {MonadW : Monad W} {Eq1M : Eq1 M} {Eq1W : Eq1 W}
  {EqW : @Eq1Equivalence W MonadW Eq1W} {LawsW : @MonadLawsE W Eq1W MonadW}
  (σ σ' : forall A, M A -> W A) :
  (forall A (m : M A), eq1 (σ A m) (σ' A m)) ->
  @MonadMorphism M W MonadM MonadW Eq1M Eq1W σ' ->
  @MonadMorphism M W MonadM MonadW Eq1M Eq1W σ.
Proof.
  intros E H. constructor.
  - intros A x y Hxy. destruct (EqW A) as [_ Hs Ht].
    exact (Ht _ _ _ (E A x) (Ht _ _ _ (mm_proper H x y Hxy) (Hs _ _ (E A y)))).
  - intros A a. destruct (EqW A) as [_ _ Ht].
    exact (Ht _ _ _ (E A (ret a)) (mm_ret H a)).
  - intros A B x k. destruct (EqW B) as [_ Hs Ht].
    refine (Ht _ _ _ (E B (bind x k)) (Ht _ _ _ (mm_bind H x k) _)).
    apply Proper_bind; [ exact ((let (_, Hs', _) := EqW A in Hs') _ _ (E A x)) |].
    intro a. exact (Hs _ _ (E B (k a))).
Qed.

(** A map that preserves [ret] and [bind] is a morphism for the finest
    equality on its source. *)
Theorem MonadMorphism_of_laws {M W : Type -> Type}
  {MonadM : Monad M} {MonadW : Monad W} {Eq1W : Eq1 W}
  {EqW : @Eq1Equivalence W MonadW Eq1W}
  (σ : forall A, M A -> W A) :
  (forall A (a : A), eq1 (σ A (ret a)) (ret a)) ->
  (forall A B (x : M A) (k : A -> M B),
      eq1 (σ B (bind x k)) (bind (σ A x) (fun a => σ B (k a)))) ->
  @MonadMorphism M W MonadM MonadW (fun A => @eq (M A)) Eq1W σ.
Proof.
  intros Hr Hb. constructor.
  - intros A x y E. change (x = y) in E. subst y.
    destruct (EqW A) as [Hrefl _ _]. apply Hrefl.
  - exact Hr.
  - exact Hb.
Qed.

(* ================================================================= *)
(** * Specification monads from specification monads                  *)
(* ================================================================= *)

(** The order of a specification monad, pulled back along a monad morphism,
    orders the source of the morphism. *)
Theorem OrderedMonad_pullback {V W : Type -> Type}
  {MonadV : Monad V} {MonadW : Monad W} {Eq1V : Eq1 V} {Eq1W : Eq1 W}
  {EqW : @Eq1Equivalence W MonadW Eq1W}
  (ι : forall A, V A -> W A) (le : forall A, relation (W A)) :
  @MonadMorphism V W MonadV MonadW Eq1V Eq1W ι ->
  @OrderedMonad W MonadW Eq1W le ->
  @OrderedMonad V MonadV Eq1V (fun A x y => le A (ι A x) (ι A y)).
Proof.
  intros Hι [Hpre Heq Hbind]. constructor.
  - intro A. destruct (Hpre A) as [Hr Ht]. constructor.
    + intro x. apply Hr.
    + intros x y z H1 H2. exact (Ht _ _ _ H1 H2).
  - intros A x y H. exact (Heq A _ _ (mm_proper Hι x y H)).
  - intros A B m1 m2 Hm k1 k2 Hk.
    destruct (Hpre B) as [_ Ht]. destruct (EqW B) as [_ Hs _].
    refine (Ht _ _ _ (Heq B _ _ (mm_bind Hι m1 k1)) _).
    refine (Ht _ _ _ _ (Heq B _ _ (Hs _ _ (mm_bind Hι m2 k2)))).
    exact (Hbind A B _ _ Hm _ _ Hk).
Qed.

(** A submonad: the elements that satisfy a predicate closed under [ret]
    and [bind].  It is a specification monad for the order it inherits. *)
Section SubMonad.
  Context {W : Type -> Type} {MonadW : Monad W} {Eq1W : Eq1 W}
    {EqW : @Eq1Equivalence W MonadW Eq1W}.
  Context (P : forall A, W A -> Prop)
    (P_ret : forall A (a : A), P A (ret a))
    (P_bind : forall A B (m : W A) (k : A -> W B),
        P A m -> (forall a, P B (k a)) -> P B (bind m k)).

  Definition SubMonad (A : Type) : Type := { w : W A | P A w }.

  Definition sub_incl (A : Type) (w : SubMonad A) : W A := proj1_sig w.

  Definition Monad_SubMonad : Monad SubMonad :=
    {| ret := fun A a => exist _ (ret a) (P_ret A a) ;
       bind := fun A B m k =>
         exist _ (bind (proj1_sig m) (fun a => proj1_sig (k a)))
           (P_bind A B _ _ (proj2_sig m) (fun a => proj2_sig (k a))) |}.

  Definition Eq1_SubMonad : Eq1 SubMonad :=
    fun A x y => eq1 (proj1_sig x) (proj1_sig y).

  Lemma sub_incl_morphism :
    @MonadMorphism SubMonad W Monad_SubMonad MonadW Eq1_SubMonad Eq1W sub_incl.
  Proof.
    constructor.
    - intros A x y H. exact H.
    - intros A a. destruct (EqW A) as [Hr _ _]. apply Hr.
    - intros A B x k. destruct (EqW B) as [Hr _ _]. apply Hr.
  Qed.

  Theorem OrderedMonad_SubMonad (le : forall A, relation (W A)) :
    @OrderedMonad W MonadW Eq1W le ->
    @OrderedMonad SubMonad Monad_SubMonad Eq1_SubMonad
      (fun A x y => le A (proj1_sig x) (proj1_sig y)).
  Proof. exact (OrderedMonad_pullback sub_incl le sub_incl_morphism). Qed.
End SubMonad.

(** A map together with the structures it is a monad morphism for.  The
    structures are fields, not parameters, so that the morphism is found
    from the map alone. *)
Class IsMonadMorphism {M W : Type -> Type} (θ : forall A, M A -> W A) : Type := {
  mor_monad_src : Monad M ;
  mor_monad_tgt : Monad W ;
  mor_eq1_src : Eq1 M ;
  mor_eq1_tgt : Eq1 W ;
  mor_laws :
    @MonadMorphism M W mor_monad_src mor_monad_tgt mor_eq1_src mor_eq1_tgt θ
}.

(** Composition of maps between monads, and the morphism of a composition.
    There is no general instance for [τ ∘ₘₘ σ]: the structures are fields, so
    those of [σ]'s target and [τ]'s source cannot be shown to agree. *)
Definition mcomp {M V W : Type -> Type} (τ : forall A, V A -> W A)
  (σ : forall A, M A -> V A) : forall A, M A -> W A :=
  fun A x => τ A (σ A x).

Infix "∘ₘₘ" := mcomp (at level 40, left associativity).

Definition IsMonadMorphism_comp {M V W : Type -> Type}
  {MonadM : Monad M} {MonadV : Monad V} {MonadW : Monad W}
  {Eq1M : Eq1 M} {Eq1V : Eq1 V} {Eq1W : Eq1 W}
  {EqW : @Eq1Equivalence W MonadW Eq1W}
  {σ : forall A, M A -> V A} {τ : forall A, V A -> W A}
  (Hσ : @MonadMorphism M V MonadM MonadV Eq1M Eq1V σ)
  (Hτ : @MonadMorphism V W MonadV MonadW Eq1V Eq1W τ) :
  IsMonadMorphism (τ ∘ₘₘ σ) :=
  @Build_IsMonadMorphism M W (τ ∘ₘₘ σ) MonadM MonadW Eq1M Eq1W
    (MonadMorphism_comp σ τ Hσ Hτ).
