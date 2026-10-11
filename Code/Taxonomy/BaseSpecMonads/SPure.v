(** * Unit-input relational specification monads.

    This file fixes the input of the relational state/option arrows:

      [SPSt S A]    = [SPStArr S unit A]
      [SPStExc S A] = [SPStExcArr S unit A] = [progRelArr S A]

    [Arrows/Rel.v] owns the binary carriers, stacks, selected equality/law
    dictionaries, and congruence facts. [Arrows/RelSPostArr.v] owns their
    four SP readings, healthiness, recovery, inclusion, and operation facts.
    Generic semantic normalization lives in [Classes/RelArrowCoherence.v].

    Here the selected [Monad] and [Eq1] interfaces inherit the arrow laws.
    The return/bind formulas preserve the fixed input and thread the
    intermediate state. At the option layer, [None] propagates without
    running the continuation or carrying a final state. Relational inclusion
    and its reverse supply the two orders and their ordered-monad proofs. *)

From Coq Require Import Relation_Definitions RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPostArr.
From Incorrectness.Lib.Arrow Require Import ArrowMonad RelArrowCoherence.

(* ================================================================= *)
(** ** The monad views, at input [unit]                              *)
(* ================================================================= *)

Definition SPSt (S : Type) (A : Type) : Type := SPStArr S unit A.
Definition SPStExc (S : Type) (A : Type) : Type := SPStExcArr S unit A.

#[global] Instance Monad_SPSt (S : Type) : Monad (SPSt S) :=
  Monad_Arrow (SPStArr S) unit.
#[global] Instance Monad_SPStExc (S : Type) : Monad (SPStExc S) :=
  Monad_Arrow (SPStExcArr S) unit.

#[global] Instance Eq1_SPSt (S : Type) : Eq1 (SPSt S) :=
  @Eq1_Arrow (SPStArr S) (ArrowEq_SPStArr S) unit.
#[global] Instance Eq1_SPStExc (S : Type) : Eq1 (SPStExc S) :=
  @Eq1_Arrow (SPStExcArr S) (ArrowEq_SPStExcArr S) unit.

Definition Eq1Equivalence_SPSt (S : Type)
  : @Eq1Equivalence (SPSt S) _ (Eq1_SPSt S) :=
  @Eq1Equivalence_Arrow (SPStArr S) _ _ (ArrowEq_SPStArr S) unit.
Definition Eq1Equivalence_SPStExc (S : Type)
  : @Eq1Equivalence (SPStExc S) _ (Eq1_SPStExc S) :=
  @Eq1Equivalence_Arrow (SPStExcArr S) _ _ (ArrowEq_SPStExcArr S) unit.

(** The monad laws lift the selected core and application arrow laws. *)
Definition MonadLawsE_SPSt (S : Type)
  : @MonadLawsE (SPSt S) (Eq1_SPSt S) (Monad_SPSt S) :=
  @MonadLawsE_Arrow (SPStArr S) _ _ (ArrowEq_SPStArr S)
    (ArrowLaws_SPStArr S) (ArrowApplyLaws_SPStArr S) unit.
Definition MonadLawsE_SPStExc (S : Type)
  : @MonadLawsE (SPStExc S) (Eq1_SPStExc S) (Monad_SPStExc S) :=
  @MonadLawsE_Arrow (SPStExcArr S) _ _ (ArrowEq_SPStExcArr S)
    (ArrowLaws_SPStExcArr S) (ArrowApplyLaws_SPStExcArr S) unit.

(* ================================================================= *)
(** ** What [ret] and [bind] are, relationally                       *)
(* ================================================================= *)

(** The arrow [bind] threads the state: the continuation is run at the
    state the first stage produced.  Everything downstream reads off
    these two. *)

(** Both stacks unfold to the same kind of goal -- a tower of existentials
    whose witnesses are forced by an equation -- so one pair of tactics
    serves both.  [flat] takes such a tower apart, [buildall] puts one
    back together.  [buildall] backtracks: at the [optionArrT] layer a
    witness is a SUM, and which injection is right is decided by a
    scrutinee further up the tower, so committing to [inl] and searching
    on is the only way to find out. *)

Local Ltac flat :=
  repeat match goal with
  | H : False |- _ => destruct H
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | p : _ * _ |- _ => destruct p
  | u : unit |- _ => destruct u
  | H : (_, _) = (_, _) |- _ => inversion H; clear H
  | H : Some _ = Some _ |- _ => inversion H; clear H
  | H : Some _ = None |- _ => discriminate H
  | H : None = Some _ |- _ => discriminate H
  | H : inl _ = inr _ |- _ => discriminate H
  | H : inr _ = inl _ |- _ => discriminate H
  | H : inl _ = inl _ |- _ => inversion H; clear H
  | H : inr _ = inr _ |- _ => inversion H; clear H
  | H : ?x = ?y |- _ => first [ subst x | subst y ]
  | x : option _ |- _ => destruct x
  | x : _ + _ |- _ => destruct x
  | _ => progress cbn in *
  end.

Local Ltac buildall :=
  first [ eassumption
        | reflexivity
        | (progress cbn; buildall)
        | (eexists; split; [ reflexivity | buildall ])
        | (split; [ buildall | buildall ])
        | (eexists (inl _); buildall)
        | (eexists (inr tt); buildall)
        | (eexists (_, _); buildall)
        | (eexists; buildall) ].

Lemma ret_SPSt {S A} (a : A) (s : S) (r : A * S) :
  (@ret (SPSt S) _ A a) (tt, s) r <-> r = (a, s).
Proof. cbn. split; intro H; symmetry; exact H. Qed.

Lemma bind_SPSt {S A B} (m : SPSt S A) (k : A -> SPSt S B) (s : S) (r : B * S) :
  (@bind (SPSt S) _ A B m k) (tt, s) r
  <-> exists a s', m (tt, s) (a, s') /\ k a (tt, s') r.
Proof.
  unfold bind, Monad_SPSt, Monad_Arrow, bind_arrow, SPSt, SPStArr,
    arr_fanout, arr_split, arr_second, arr_id.
  cbn. cbv beta iota delta [state_shuffle_in state_shuffle_out swap].
  split; [ intro H; flat; eauto | intros [a [s' [Hm Hk]]]; buildall ].
Qed.

Lemma ret_SPStExc {S A} (a : A) (s : S) (r : option (A * S)) :
  (@ret (SPStExc S) _ A a) (tt, s) r <-> r = Some (a, s).
Proof. cbn. split; intro H; symmetry; exact H. Qed.

(** The [StExc] counterpart.  The outcome is now an [option]: [None] is
    the EXCEPTIONAL outcome, it is an outcome of the composite in its own
    right, and the continuation does not run on it.  That single extra
    branch is the whole difference from [bind_SPSt], and it is where the
    [optionArrT] plumbing ([to_sum], [collapse], [sequence_option]) goes
    once it is computed away. *)

Lemma bind_SPStExc {S A B} (m : SPStExc S A) (k : A -> SPStExc S B)
  (s : S) (r : option (B * S)) :
  (@bind (SPStExc S) _ A B m k) (tt, s) r
  <-> exists o, m (tt, s) o
                /\ match o with
                   | Some (a, s') => k a (tt, s') r
                   | None => r = None
                   end.
Proof.
  exact (@rel_state_option_bind_fields Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel
    (fun _ _ f => f)
    (fun _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ => iff_refl _)
    S unit A B m k tt s r).
Qed.

(* ================================================================= *)
(** ** Orders                                                        *)
(* ================================================================= *)

(** [ordSP] is relational inclusion; [ordSPop] reverses it, matching
    DSLP transformer inclusion by [dslpOf_incl]. Both stacks use the
    same two orders because they are relations at larger types. *)

Definition ordSP {S A} : relation (SPSt S A) := @Rel_le _ _.
Definition ordSPop {S A} : relation (SPSt S A) := fun m n => Rel_le n m.

Definition ordSPExc {S A} : relation (SPStExc S A) := @Rel_le _ _.
Definition ordSPExcOp {S A} : relation (SPStExc S A) := fun m n => Rel_le n m.

Section Ordered.

  Variable S : Type.

  #[local] Existing Instance Monad_SPSt.
  #[local] Existing Instance Eq1_SPSt.
  #[local] Existing Instance Eq1Equivalence_SPSt.

  #[global] Instance OrderedMonad_SPSt : OrderedMonad (SPSt S) (@ordSP S).
  Proof.
    constructor.
    - intro A. apply Rel_le_PreOrder.
    - intros A x y H a r. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk [[] s] r.
      rewrite !bind_SPSt. intros [a [s' [Hm1 Hk1]]].
      exists a, s'. split; [ exact (Hm _ _ Hm1) | exact (Hk a _ _ Hk1) ].
  Qed.

  (** DSLP's order is the same criterion read backwards. *)
  #[global] Instance OrderedMonad_SPSt_op : OrderedMonad (SPSt S) (@ordSPop S) :=
    OrderedMonad_flip (@ordSP S) OrderedMonad_SPSt.


  (** The same three lines at the exception stack.  Monotonicity now has
      the extra branch: on an exceptional outcome there is no continuation
      to be monotone in, and the outcome carries over unchanged. *)

  #[local] Existing Instance Monad_SPStExc.
  #[local] Existing Instance Eq1_SPStExc.
  #[local] Existing Instance Eq1Equivalence_SPStExc.

  #[global] Instance OrderedMonad_SPStExc
    : OrderedMonad (SPStExc S) (@ordSPExc S).
  Proof.
    constructor.
    - intro A. apply Rel_le_PreOrder.
    - intros A x y H a r. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk [[] s] r.
      rewrite !bind_SPStExc. intros [o [Hm1 Hk1]].
      exists o. split; [ exact (Hm _ _ Hm1) |].
      destruct o as [[a s']|]; [ exact (Hk a _ _ Hk1) | exact Hk1 ].
  Qed.

  #[global] Instance OrderedMonad_SPStExc_op
    : OrderedMonad (SPStExc S) (@ordSPExcOp S) :=
    OrderedMonad_flip (@ordSPExc S) OrderedMonad_SPStExc.
End Ordered.
