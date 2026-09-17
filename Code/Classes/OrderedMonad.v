(** * Ordered monads: the specification-monad criterion of DM4All

    DM4All ([theories/sprop/SPropMonadicStructures.v], [OrderedMonad]) calls a
    monad [W] a specification monad when each [W A] carries a preorder and
    [bind] is monotone in both arguments.  Its monad laws are equalities; here
    they hold up to [eq1], so the order is additionally required to contain
    [eq1] — otherwise a law could relate two elements the order separates.

    Every monad is ordered by [eq1] itself ([OrderedMonad_eq1], DM4All's
    [DiscreteMonad]), so the criterion only has content relative to a chosen
    order.

    Lifts through [optionT] / [stateT] / [readerT] are in
    [Taxonomy/ComputationMonads/TransformerLaws.v]. *)

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
