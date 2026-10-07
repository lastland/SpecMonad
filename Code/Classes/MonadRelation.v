(** * Relations between two monads: the monadic relations of DM4All

    DM4All (Def. 3; [theories/sprop/SPropMonadicStructures.v],
    [MonadRelation]) calls a family of relations [R A] between [M A] and
    [W A] a monadic relation when it holds at [ret] and is preserved by
    [bind].  There [M] is a computational monad, [W] a specification monad,
    and the graph of a monad morphism is the first example.  Here the same
    criterion is stated for any two monads.  It is for a pair of monads
    what monotonicity of [bind] is for one: the order of an ordered monad is
    a monad relation from the monad to itself
    ([MonadRelation_OrderedMonad]).

    Monad morphisms pull a monad relation back ([MonadRelation_pullback]).

    The criterion is modular in the two ways a monad of this development is
    built.

    A monad relation lifts through each monad transformer
    ([MonadRelation_stateT], [MonadRelation_optionT],
    [MonadRelation_readerT]), pointwise, as an order does
    ([ComputationMonads/TransformerLaws.v]).

    For two arrows with relational semantics ([RelArrowCoherence.v]),
    inclusion of the relations denoted is a monad relation between the
    monads the arrows give at a fixed input, and it remains one under the
    arrow transformers: at the base arrows ([MonadRelation_rel_incl]), under
    [stateArrT] ([MonadRelation_rel_incl_state]) and under [stateArrT] over
    [optionArrT] ([MonadRelation_rel_incl_state_option]).  The transformers
    only re-index the base arrow, so the reading is the base arrow's
    throughout.  [MonadRelation_rel_eq] and its two companions are the same
    statements for equality of the relations denoted. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From ExtLib Require Import Monad StateMonad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import OrderedMonad.
From Incorrectness.Classes Require Import Arrow ArrowMonad OptionArrowT StateArrowT
  RelArrowCoherence.

Class MonadRelation (M N : Type -> Type) {MonadM : Monad M} {MonadN : Monad N}
  (R : forall A, M A -> N A -> Prop) : Prop := {
  mr_ret : forall A (a : A), R A (ret a) (ret a);
  mr_bind : forall A B (m : M A) (n : N A) (k : A -> M B) (k' : A -> N B),
    R A m n -> (forall a, R B (k a) (k' a)) -> R B (bind m k) (bind n k')
}.

Section Generic.
  Context {M N : Type -> Type} {MonadM : Monad M} {MonadN : Monad N}.

  (** The criterion does not see which monad is written first. *)
  Theorem MonadRelation_flip (R : forall A, M A -> N A -> Prop) :
    @MonadRelation M N MonadM MonadN R ->
    @MonadRelation N M MonadN MonadM (fun A n m => R A m n).
  Proof.
    intros [Hret Hbind]. constructor.
    - exact Hret.
    - intros A B n m k' k. exact (Hbind A B m n k k').
  Qed.

  (** Transport along a pointwise-equivalent relation. *)
  Theorem MonadRelation_iff (R R' : forall A, M A -> N A -> Prop) :
    (forall A m n, R A m n <-> R' A m n) ->
    @MonadRelation M N MonadM MonadN R -> @MonadRelation M N MonadM MonadN R'.
  Proof.
    intros E [Hret Hbind]. constructor.
    - intros A a. apply E. exact (Hret A a).
    - intros A B m n k k' Hm Hk. apply E.
      apply Hbind; [ apply E; exact Hm | intro a; apply E; exact (Hk a) ].
  Qed.

  (** Two monad relations hold together. *)
  Theorem MonadRelation_conj (R R' : forall A, M A -> N A -> Prop) :
    @MonadRelation M N MonadM MonadN R -> @MonadRelation M N MonadM MonadN R' ->
    @MonadRelation M N MonadM MonadN (fun A m n => R A m n /\ R' A m n).
  Proof.
    intros [Hret Hbind] [Hret' Hbind']. constructor.
    - intros A a. exact (conj (Hret A a) (Hret' A a)).
    - intros A B m n k k' [Hm Hm'] Hk. split.
      + exact (Hbind A B m n k k' Hm (fun a => proj1 (Hk a))).
      + exact (Hbind' A B m n k k' Hm' (fun a => proj2 (Hk a))).
  Qed.

  (** Monad morphisms pull a monad relation back, provided the relation does
      not tell apart what the morphism laws identify. *)
  Theorem MonadRelation_pullback {M' N' : Type -> Type}
    {MonadM' : Monad M'} {MonadN' : Monad N'}
    (R : forall A, M' A -> N' A -> Prop)
    (eqM : forall A, relation (M' A)) (eqN : forall A, relation (N' A))
    (f : forall A, M A -> M' A) (g : forall A, N A -> N' A) :
    (forall A x x' y y', eqM A x x' -> eqN A y y' -> R A x' y' -> R A x y) ->
    (forall A (a : A), eqM A (f A (ret a)) (ret a)) ->
    (forall A B (m : M A) (k : A -> M B),
        eqM B (f B (bind m k)) (bind (f A m) (fun a => f B (k a)))) ->
    (forall A (a : A), eqN A (g A (ret a)) (ret a)) ->
    (forall A B (n : N A) (k : A -> N B),
        eqN B (g B (bind n k)) (bind (g A n) (fun a => g B (k a)))) ->
    @MonadRelation M' N' MonadM' MonadN' R ->
    @MonadRelation M N MonadM MonadN (fun A m n => R A (f A m) (g A n)).
  Proof.
    intros Hresp Hfr Hfb Hgr Hgb [Hret Hbind]. constructor.
    - intros A a. exact (Hresp A _ _ _ _ (Hfr A a) (Hgr A a) (Hret A a)).
    - intros A B m n k k' Hm Hk.
      exact (Hresp B _ _ _ _ (Hfb A B m k) (Hgb A B n k')
               (Hbind A B (f A m) (g A n) (fun a => f B (k a)) (fun a => g B (k' a))
                  Hm Hk)).
  Qed.
End Generic.

Theorem MonadRelation_OrderedMonad {W : Type -> Type} {MonadW : Monad W} {Eq1W : Eq1 W}
  (le : forall A, relation (W A)) :
  OrderedMonad W le -> @MonadRelation W W MonadW MonadW le.
Proof.
  intros [Hpre _ Hbind]. constructor.
  - intros A a. destruct (Hpre A) as [Hr _]. apply Hr.
  - intros A B m n k k' Hm Hk. exact (Hbind A B m n Hm k k' Hk).
Qed.

(* ================================================================= *)
(** ** Monad transformers                                            *)
(* ================================================================= *)

(** Each transformer lifts a monad relation pointwise: in the start state,
    at the result type [option A], in the environment. *)

Section Transformers.
  Context {M N : Type -> Type} {MonadM : Monad M} {MonadN : Monad N}.
  Context (R : forall A, M A -> N A -> Prop).

  Theorem MonadRelation_stateT (St : Type) :
    @MonadRelation M N MonadM MonadN R ->
    @MonadRelation (stateT St M) (stateT St N)
      (@Monad_stateT St M MonadM) (@Monad_stateT St N MonadN)
      (fun A m n => forall s, R (A * St)%type (runStateT m s) (runStateT n s)).
  Proof.
    intros [Hret Hbind]. constructor.
    - intros A a s. cbn. apply Hret.
    - intros A B m n k k' Hm Hk s. cbn.
      apply Hbind; [ exact (Hm s) |].
      intros [a s']. exact (Hk a s').
  Qed.

  Theorem MonadRelation_optionT :
    @MonadRelation M N MonadM MonadN R ->
    @MonadRelation (optionT M) (optionT N)
      (@Monad_optionT M MonadM) (@Monad_optionT N MonadN)
      (fun A m n => R (option A) (unOptionT m) (unOptionT n)).
  Proof.
    intros [Hret Hbind]. constructor.
    - intros A a. cbn. apply Hret.
    - intros A B m n k k' Hm Hk. cbn.
      apply Hbind; [ exact Hm |].
      intros [a|]; [ exact (Hk a) | apply Hret ].
  Qed.

  Theorem MonadRelation_readerT (E : Type) :
    @MonadRelation M N MonadM MonadN R ->
    @MonadRelation (readerT E M) (readerT E N)
      (@Monad_readerT E M MonadM) (@Monad_readerT E N MonadN)
      (fun A m n => forall e, R A (runReaderT m e) (runReaderT n e)).
  Proof.
    intros [Hret Hbind]. constructor.
    - intros A a e. cbn. apply Hret.
    - intros A B m n k k' Hm Hk e. cbn.
      apply Hbind; [ exact (Hm e) | intro a; exact (Hk a e) ].
  Qed.
End Transformers.

(* ================================================================= *)
(** ** Arrow transformers                                            *)
(* ================================================================= *)

(** Two arrows with relational semantics, and the monads they give at a
    fixed input [I].  [ret] denotes the identity and [bind] the composition
    of the relations denoted ([rel_pure], [rel_bind], [relS_bind],
    [relE_pure], [relE_bind]), so inclusion of those relations holds at
    [ret] and is preserved by [bind], at every stack. *)

Section ArrowStacks.
  Context {arr1 : Type -> Type -> Type}
    {HA1 : Arrow arr1} {HAA1 : @ArrowApply arr1 HA1}
    {HR1 : @RelArrow arr1 HA1} {HRA1 : @RelArrowApply arr1 HA1 HAA1 HR1}.
  Context {arr2 : Type -> Type -> Type}
    {HA2 : Arrow arr2} {HAA2 : @ArrowApply arr2 HA2}
    {HR2 : @RelArrow arr2 HA2} {HRA2 : @RelArrowApply arr2 HA2 HAA2 HR2}.

  Local Notation R1 := (@rel_reading arr1 HA1 HR1).
  Local Notation R2 := (@rel_reading arr2 HA2 HR2).

  Theorem MonadRelation_rel_incl (I : Type) :
    @MonadRelation (arr1 I) (arr2 I)
      (@Monad_Arrow arr1 HA1 HAA1 I) (@Monad_Arrow arr2 HA2 HAA2 I)
      (fun A m n => forall x y, R1 m x y -> R2 n x y).
  Proof.
    constructor.
    - intros A a x y H.
      exact (proj2 (@rel_pure arr2 HA2 HR2 I A (fun _ => a) x y)
               (proj1 (@rel_pure arr1 HA1 HR1 I A (fun _ => a) x y) H)).
    - intros A B m n k k' Hm Hk x y H.
      destruct (proj1 (@rel_bind arr1 HA1 HAA1 HR1 HRA1 I A B m k x y) H)
        as [a [H1 H2]].
      apply (proj2 (@rel_bind arr2 HA2 HAA2 HR2 HRA2 I A B n k' x y)).
      exists a. exact (conj (Hm _ _ H1) (Hk a _ _ H2)).
  Qed.

  Theorem MonadRelation_rel_incl_state (S I : Type) :
    @MonadRelation (stateArrT S arr1 I) (stateArrT S arr2 I)
      (@Monad_Arrow (stateArrT S arr1) (@Arrow_stateArrT S arr1 HA1)
         (@ArrowApply_stateArrT S arr1 HA1 HAA1) I)
      (@Monad_Arrow (stateArrT S arr2) (@Arrow_stateArrT S arr2 HA2)
         (@ArrowApply_stateArrT S arr2 HA2 HAA2) I)
      (fun A m n => forall p r, R1 m p r -> R2 n p r).
  Proof.
    constructor.
    - intros A a [i s] r H.
      exact (proj2 (@rel_pure arr2 HA2 HR2 _ _ (fun '(_, s0) => (a, s0)) (i, s) r)
               (proj1 (@rel_pure arr1 HA1 HR1 _ _ (fun '(_, s0) => (a, s0)) (i, s) r) H)).
    - intros A B m n k k' Hm Hk [i s] r H.
      destruct (proj1 (@relS_bind arr1 HA1 HAA1 HR1 HRA1 S I A B m k i s r) H)
        as [a [s' [H1 H2]]].
      apply (proj2 (@relS_bind arr2 HA2 HAA2 HR2 HRA2 S I A B n k' i s r)).
      exists a, s'. exact (conj (Hm _ _ H1) (Hk a _ _ H2)).
  Qed.

  Context {HC1 : @ArrowChoice arr1 HA1} {HRC1 : @RelArrowChoice arr1 HA1 HC1 HR1}.
  Context {HC2 : @ArrowChoice arr2 HA2} {HRC2 : @RelArrowChoice arr2 HA2 HC2 HR2}.

  Theorem MonadRelation_rel_incl_state_option (S I : Type) :
    @MonadRelation (stateArrT S (optionArrT arr1) I) (stateArrT S (optionArrT arr2) I)
      (@Monad_Arrow (stateArrT S (optionArrT arr1))
         (@Arrow_stateArrT S (optionArrT arr1) (@Arrow_optionArrT arr1 HA1 HC1))
         (@ArrowApply_stateArrT S (optionArrT arr1) (@Arrow_optionArrT arr1 HA1 HC1)
            (@ArrowApply_optionArrT arr1 HA1 HC1 HAA1)) I)
      (@Monad_Arrow (stateArrT S (optionArrT arr2))
         (@Arrow_stateArrT S (optionArrT arr2) (@Arrow_optionArrT arr2 HA2 HC2))
         (@ArrowApply_stateArrT S (optionArrT arr2) (@Arrow_optionArrT arr2 HA2 HC2)
            (@ArrowApply_optionArrT arr2 HA2 HC2 HAA2)) I)
      (fun A m n => forall p o, R1 m p o -> R2 n p o).
  Proof.
    constructor.
    - intros A a [i s] o H.
      apply (proj2 (@relE_pure arr2 HA2 HR2 HC2 S I A (fun _ => a) i s o)).
      exact (proj1 (@relE_pure arr1 HA1 HR1 HC1 S I A (fun _ => a) i s o) H).
    - intros A B m n k k' Hm Hk [i s] o H.
      destruct (proj1 (@relE_bind arr1 HA1 HAA1 HR1 HRA1 HC1 HRC1 S I A B m k i s o) H)
        as [o1 [H1 H2]].
      apply (proj2 (@relE_bind arr2 HA2 HAA2 HR2 HRA2 HC2 HRC2 S I A B n k' i s o)).
      exists o1. split; [ exact (Hm _ _ H1) |].
      destruct o1 as [[a s']|]; [ exact (Hk a _ _ H2) | exact H2 ].
  Qed.
End ArrowStacks.

(** Equality of the relations denoted is inclusion both ways. *)

Section ArrowStacksEq.
  Context {arr1 : Type -> Type -> Type}
    {HA1 : Arrow arr1} {HAA1 : @ArrowApply arr1 HA1}
    {HR1 : @RelArrow arr1 HA1} {HRA1 : @RelArrowApply arr1 HA1 HAA1 HR1}.
  Context {arr2 : Type -> Type -> Type}
    {HA2 : Arrow arr2} {HAA2 : @ArrowApply arr2 HA2}
    {HR2 : @RelArrow arr2 HA2} {HRA2 : @RelArrowApply arr2 HA2 HAA2 HR2}.

  Local Notation R1 := (@rel_reading arr1 HA1 HR1).
  Local Notation R2 := (@rel_reading arr2 HA2 HR2).

  Theorem MonadRelation_rel_eq (I : Type) :
    @MonadRelation (arr1 I) (arr2 I)
      (@Monad_Arrow arr1 HA1 HAA1 I) (@Monad_Arrow arr2 HA2 HAA2 I)
      (fun A m n => forall x y, R1 m x y <-> R2 n x y).
  Proof.
    refine (MonadRelation_iff _ _ _
              (MonadRelation_conj _ _
                 (@MonadRelation_rel_incl arr1 HA1 HAA1 HR1 HRA1 arr2 HA2 HAA2 HR2 HRA2 I)
                 (MonadRelation_flip _
                    (@MonadRelation_rel_incl arr2 HA2 HAA2 HR2 HRA2 arr1 HA1 HAA1 HR1 HRA1 I)))).
    intros A m n. split.
    - intros [H12 H21] x y. split; [ apply H12 | apply H21 ].
    - intro H. split; intros x y Hxy; apply H; exact Hxy.
  Qed.

  Theorem MonadRelation_rel_eq_state (S I : Type) :
    @MonadRelation (stateArrT S arr1 I) (stateArrT S arr2 I)
      (@Monad_Arrow (stateArrT S arr1) (@Arrow_stateArrT S arr1 HA1)
         (@ArrowApply_stateArrT S arr1 HA1 HAA1) I)
      (@Monad_Arrow (stateArrT S arr2) (@Arrow_stateArrT S arr2 HA2)
         (@ArrowApply_stateArrT S arr2 HA2 HAA2) I)
      (fun A m n => forall p r, R1 m p r <-> R2 n p r).
  Proof.
    refine (MonadRelation_iff _ _ _
              (MonadRelation_conj _ _
                 (@MonadRelation_rel_incl_state arr1 HA1 HAA1 HR1 HRA1
                    arr2 HA2 HAA2 HR2 HRA2 S I)
                 (MonadRelation_flip _
                    (@MonadRelation_rel_incl_state arr2 HA2 HAA2 HR2 HRA2
                       arr1 HA1 HAA1 HR1 HRA1 S I)))).
    intros A m n. split.
    - intros [H12 H21] p r. split; [ apply H12 | apply H21 ].
    - intro H. split; intros p r Hpr; apply H; exact Hpr.
  Qed.

  Context {HC1 : @ArrowChoice arr1 HA1} {HRC1 : @RelArrowChoice arr1 HA1 HC1 HR1}.
  Context {HC2 : @ArrowChoice arr2 HA2} {HRC2 : @RelArrowChoice arr2 HA2 HC2 HR2}.

  Theorem MonadRelation_rel_eq_state_option (S I : Type) :
    @MonadRelation (stateArrT S (optionArrT arr1) I) (stateArrT S (optionArrT arr2) I)
      (@Monad_Arrow (stateArrT S (optionArrT arr1))
         (@Arrow_stateArrT S (optionArrT arr1) (@Arrow_optionArrT arr1 HA1 HC1))
         (@ArrowApply_stateArrT S (optionArrT arr1) (@Arrow_optionArrT arr1 HA1 HC1)
            (@ArrowApply_optionArrT arr1 HA1 HC1 HAA1)) I)
      (@Monad_Arrow (stateArrT S (optionArrT arr2))
         (@Arrow_stateArrT S (optionArrT arr2) (@Arrow_optionArrT arr2 HA2 HC2))
         (@ArrowApply_stateArrT S (optionArrT arr2) (@Arrow_optionArrT arr2 HA2 HC2)
            (@ArrowApply_optionArrT arr2 HA2 HC2 HAA2)) I)
      (fun A m n => forall p o, R1 m p o <-> R2 n p o).
  Proof.
    refine (MonadRelation_iff _ _ _
              (MonadRelation_conj _ _
                 (@MonadRelation_rel_incl_state_option arr1 HA1 HAA1 HR1 HRA1
                    arr2 HA2 HAA2 HR2 HRA2 HC1 HRC1 HC2 HRC2 S I)
                 (MonadRelation_flip _
                    (@MonadRelation_rel_incl_state_option arr2 HA2 HAA2 HR2 HRA2
                       arr1 HA1 HAA1 HR1 HRA1 HC2 HRC2 HC1 HRC1 S I)))).
    intros A m n. split.
    - intros [H12 H21] p o. split; [ apply H12 | apply H21 ].
    - intro H. split; intros p o Hpo; apply H; exact Hpo.
  Qed.
End ArrowStacksEq.
