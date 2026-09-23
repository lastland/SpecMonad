(** * [SPure]: the relational core of the SP specification monads

    The SP counterpart of [WPure.v].  There the carrier is a
    predicate transformer cut down by a healthiness condition; here it is
    the RELATION a specification denotes:

      [SPureArr A B]   = [PredArr A B]                   = [A -> B -> Prop]
      [SPStArr S]      = [stateArrT S PredArr]
      [SPStExcArr S]   = [stateArrT S (optionArrT PredArr)]

    The four SP flavours are not four carriers.  They are four READINGS of
    one relation -- [aspOf], [dslpOf], [dspOf], [aslpOf] -- and the arrow
    and monad structure belongs to the relation, not to any of them.  So
    the laws are [PredArr]'s, proved once in [Arrows/PredArr.v] and
    inherited here through the generic transformers of [Classes/].

    What the readings still owe, and what this file proves:

      - each reading is automatically HEALTHY ([aspOf_join], [dslpOf_meet]);
      - each is FAITHFUL -- the relation is recovered from the reading
        ([aspOf_rel], [dslpOf_rel]), constructively;
      - each is an ARROW MORPHISM ([aspOf_pure] / [aspOf_comp] and their
        DSLP mirrors): this is what makes one set of laws serve all four;
      - the two ORDERS differ, and only here: transformer inclusion is
        relation inclusion for ASP ([aspOf_incl]) and its REVERSE for DSLP
        ([dslpOf_incl]).  On this carrier that is one [flip], and
        [OrderedMonad_flip] carries the specification-monad criterion
        across.

    DSP and ASLP are the meet and join of the other two readings.  They
    are faithful only classically ([dspOf_rel], [aslpOf_rel]), and they are
    ordered monads for the RELATIONAL order only -- their own reading order
    has no [Pos]-enrichment ([DSPMonad.not_OrderedMonad_DSPSt],
    [ASLPMonad.not_OrderedMonad_ASLPSt]). *)

From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.

(* ================================================================= *)
(** ** The carrier and its two stacks                                *)
(* ================================================================= *)

Notation SPureArr := PredArr (only parsing).

Definition SPStArr (S : Type) := stateArrT S PredArr.
Definition SPStExcArr (S : Type) := stateArrT S (optionArrT PredArr).

(** Every arrow law at every level is [PredArr]'s, reached by typeclass
    resolution through [Classes/StateArrowT] and [Classes/OptionArrowT].
    These are the sanity checks that it does resolve. *)

Definition ArrowLaws_SPStArr (S : Type) : ArrowLaws (SPStArr S) := _.
Definition ArrowChoiceLaws_SPStArr (S : Type) : ArrowChoiceLaws (SPStArr S) := _.
Definition ArrowApplyLaws_SPStArr (S : Type) : ArrowApplyLaws (SPStArr S) := _.

Definition ArrowLaws_SPStExcArr (S : Type) : ArrowLaws (SPStExcArr S) := _.
Definition ArrowChoiceLaws_SPStExcArr (S : Type) : ArrowChoiceLaws (SPStExcArr S) := _.
Definition ArrowApplyLaws_SPStExcArr (S : Type) : ArrowApplyLaws (SPStExcArr S) := _.

(* ================================================================= *)
(** ** The monad views, at input [unit]                              *)
(* ================================================================= *)

Definition SPSt (S : Type) (A : Type) : Type := SPStArr S unit A.
Definition SPStExc (S : Type) (A : Type) : Type := SPStExcArr S unit A.

#[global] Instance Monad_SPSt (S : Type) : Monad (SPSt S) :=
  Monad_Arrow (SPStArr S) unit.
#[global] Instance Monad_SPStExc (S : Type) : Monad (SPStExc S) :=
  Monad_Arrow (SPStExcArr S) unit.

(** Pinned explicitly: [Eq1_Arrow] takes its arrow IMPLICITLY, and the
    [ArrowEq] instances for the two transformers are mutually recursive,
    so leaving either to resolution sends the search exponential. *)
Definition ArrowEq_SPStArr (S : Type) : ArrowEq (SPStArr S) :=
  @ArrowEq_stateArrT S PredArr ArrowEq_Pred.
Definition ArrowEq_SPStExcArr (S : Type) : ArrowEq (SPStExcArr S) :=
  @ArrowEq_stateArrT S (optionArrT PredArr) (@ArrowEq_optionArrT PredArr ArrowEq_Pred).

#[global] Instance Eq1_SPSt (S : Type) : Eq1 (SPSt S) :=
  @Eq1_Arrow (SPStArr S) (ArrowEq_SPStArr S).
#[global] Instance Eq1_SPStExc (S : Type) : Eq1 (SPStExc S) :=
  @Eq1_Arrow (SPStExcArr S) (ArrowEq_SPStExcArr S).

Definition Eq1Equivalence_SPSt (S : Type)
  : @Eq1Equivalence (SPSt S) _ (Eq1_SPSt S) :=
  @Eq1Equivalence_Arrow (SPStArr S) _ _ (ArrowEq_SPStArr S).
Definition Eq1Equivalence_SPStExc (S : Type)
  : @Eq1Equivalence (SPStExc S) _ (Eq1_SPStExc S) :=
  @Eq1Equivalence_Arrow (SPStExcArr S) _ _ (ArrowEq_SPStExcArr S).

(** The monad laws, for both stacks, from [ArrowApplyLaws] alone. *)
Definition MonadLawsE_SPSt (S : Type)
  : @MonadLawsE (SPSt S) (Eq1_SPSt S) (Monad_SPSt S) :=
  @MonadLawsE_Arrow (SPStArr S) _ _ (ArrowEq_SPStArr S) _ _.
Definition MonadLawsE_SPStExc (S : Type)
  : @MonadLawsE (SPStExc S) (Eq1_SPStExc S) (Monad_SPStExc S) :=
  @MonadLawsE_Arrow (SPStExcArr S) _ _ (ArrowEq_SPStExcArr S) _ _.

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
  unfold bind, Monad_SPStExc, Monad_Arrow, bind_arrow, SPStExc, SPStExcArr,
    arr_fanout, arr_split, arr_second, arr_id.
  cbn. cbv beta iota delta [state_shuffle_in state_shuffle_out swap
    to_sum collapse sequence_option opt_rearrange].
  split.
  - intro H. flat.
    all: try (eexists; split;
              [ eassumption | cbn; first [ eassumption | reflexivity ] ]).
  - intros [o [Hm Hk]]. destruct o as [[a s']|]; cbn in Hk;
      [| subst r ]; buildall.
Qed.

(* ================================================================= *)
(** ** The four readings                                             *)
(* ================================================================= *)

Section Readings.

  Context {X Y : Type}.

  (** [asp] is the direct image; [dslp] sends an outcome to the
      preconditions all of whose predecessors it has. *)
  Definition aspOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    fun P y => exists x, P x /\ R x y.

  Definition dslpOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    fun P y => forall x, R x y -> P x.

  Definition dspOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    fun P y => aspOf R P y /\ dslpOf R P y.

  Definition aslpOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    fun P y => aspOf R P y \/ dslpOf R P y.

  (** *** Healthiness is automatic *)

  (** Every [aspOf] preserves joins -- [ASPMonad]'s [asp_join]. *)
  Theorem aspOf_join (R : SPureArr X Y) (P : X -> Prop) (y : Y) :
    aspOf R P y <-> exists x, P x /\ aspOf R (fun z => z = x) y.
  Proof.
    split.
    - intros [x [HP HR]]. exists x. split; [ exact HP |].
      exists x. split; [ reflexivity | exact HR ].
    - intros [x [HP [x' [Heq HR]]]]. subst x'. exists x. split; assumption.
  Qed.

  (** Every [dslpOf] preserves meets -- [DSLPMonad]'s [dslp_meet], whose
      statement is in terms of the relation the transformer denotes. *)
  Theorem dslpOf_meet (R : SPureArr X Y) (P : X -> Prop) (y : Y) :
    dslpOf R P y
    <-> forall x, (forall Q, dslpOf R Q y -> Q x) -> P x.
  Proof.
    split.
    - intros H x Hx. apply Hx. exact H.
    - intros H x HR. apply H. intros Q HQ. exact (HQ x HR).
  Qed.

  (** *** Faithfulness: the relation comes back *)

  (** ASP recovers it by probing at a singleton, DSLP by quantifying over
      accepted preconditions.  BOTH ARE CONSTRUCTIVE -- the classical
      probe of [DSLPMonad] ([~ f (fun z => z <> x) y]) is a different
      characterisation, not a necessary one. *)

  Theorem aspOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    aspOf R (fun z => z = x) y <-> R x y.
  Proof.
    split.
    - intros [x' [Heq HR]]. subst x'. exact HR.
    - intro HR. exists x. split; [ reflexivity | exact HR ].
  Qed.

  Theorem dslpOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    (forall P, dslpOf R P y -> P x) <-> R x y.
  Proof.
    split.
    - intro H. exact (H (fun z => R z y) (fun z HR => HR)).
    - intros HR P HP. exact (HP x HR).
  Qed.

  Corollary aspOf_inj (R R' : SPureArr X Y) :
    (forall P y, aspOf R P y <-> aspOf R' P y) -> Pred_eq R R'.
  Proof.
    intros H x y. rewrite <- (aspOf_rel R), <- (aspOf_rel R'). apply H.
  Qed.

  Corollary dslpOf_inj (R R' : SPureArr X Y) :
    (forall P y, dslpOf R P y <-> dslpOf R' P y) -> Pred_eq R R'.
  Proof.
    intros H x y. rewrite <- (dslpOf_rel R), <- (dslpOf_rel R').
    split; intros HP Q HQ; apply HP; apply H; exact HQ.
  Qed.

  (** DSP and ASLP recover it too, but only with excluded middle: each
      needs the value of the reading at TWO preconditions. *)

  Theorem dspOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    R x y <-> (dspOf R (fun _ => True) y /\ ~ dspOf R (fun z => z <> x) y).
  Proof.
    split.
    - intro HR. split.
      + split; [ exists x; split; [ exact I | exact HR ] | intros z _; exact I ].
      + intros [_ Hd]. exact (Hd x HR eq_refl).
    - intros [[[x0 [_ HR0]] _] Hno]. apply NNPP. intro Hnx.
      apply Hno. split.
      + exists x0. split; [| exact HR0 ].
        intro Heq. subst x0. exact (Hnx HR0).
      + intros z HR Heq. subst z. exact (Hnx HR).
  Qed.

  Theorem aslpOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    R x y <-> (~ aslpOf R (fun _ => False) y /\ aslpOf R (fun z => z = x) y).
  Proof.
    split.
    - intro HR. split.
      + intros [[z [Hf _]] | Hd]; [ exact Hf | exact (Hd x HR) ].
      + left. exists x. split; [ reflexivity | exact HR ].
    - intros [Hne [[z [Heq HR]] | Hd]].
      + subst z. exact HR.
      + apply NNPP. intro Hnx. apply Hne. right. intros z HR.
        rewrite (Hd z HR) in HR. exact (Hnx HR).
  Qed.

  (** *** The order correspondence: this is where the flip lives *)

  (** Transformer inclusion IS relation inclusion for ASP ... *)
  Theorem aspOf_incl (R R' : SPureArr X Y) :
    (forall P y, aspOf R P y -> aspOf R' P y) <-> Pred_le R R'.
  Proof.
    split.
    - intros H x y HR. apply (aspOf_rel R' x y).
      apply H. apply aspOf_rel. exact HR.
    - intros H P y [x [HP HR]]. exists x. split; [ exact HP | exact (H x y HR) ].
  Qed.

  (** ... and its REVERSE for DSLP.  Note [R'] and [R] swap sides. *)
  Theorem dslpOf_incl (R R' : SPureArr X Y) :
    (forall P y, dslpOf R P y -> dslpOf R' P y) <-> Pred_le R' R.
  Proof.
    split.
    - intros H x y HR'. apply (proj1 (dslpOf_rel R x y)).
      intros P HP. exact (H P y HP x HR').
    - intros H P y HP x HR'. exact (HP x (H x y HR')).
  Qed.

End Readings.

Arguments aspOf {X Y}.
Arguments dslpOf {X Y}.
Arguments dspOf {X Y}.
Arguments aslpOf {X Y}.

(* ================================================================= *)
(** ** The readings are arrow morphisms                              *)
(* ================================================================= *)

(** This is the theorem that makes one development serve all four
    flavours: every arrow operation on a reading is the [PredArr]
    operation on the relation.  [dslpOf] is ANTITONE in its relation yet
    still preserves composition COVARIANTLY -- the transposition happens
    twice. *)

Section Morphism.

  Context {X Y Z : Type}.

  Theorem aspOf_pure (h : X -> Y) (P : X -> Prop) (y : Y) :
    aspOf (arr_pure h) P y <-> exists x, P x /\ h x = y.
  Proof. reflexivity. Qed.

  Theorem dslpOf_pure (h : X -> Y) (P : X -> Prop) (y : Y) :
    dslpOf (arr_pure h) P y <-> forall x, h x = y -> P x.
  Proof. reflexivity. Qed.

  Theorem aspOf_comp (R : SPureArr X Y) (T : SPureArr Y Z)
    (P : X -> Prop) (z : Z) :
    aspOf (arr_comp R T) P z <-> aspOf T (aspOf R P) z.
  Proof.
    split.
    - intros [x [HP [y [HR HT]]]].
      exists y. split; [ exists x; split; assumption | exact HT ].
    - intros [y [[x [HP HR]] HT]].
      exists x. split; [ exact HP | exists y; split; assumption ].
  Qed.

  Theorem dslpOf_comp (R : SPureArr X Y) (T : SPureArr Y Z)
    (P : X -> Prop) (z : Z) :
    dslpOf (arr_comp R T) P z <-> dslpOf T (dslpOf R P) z.
  Proof.
    split.
    - intros H y HT x HR. apply H. exists y. split; assumption.
    - intros H x [y [HR HT]]. exact (H y HT x HR).
  Qed.

End Morphism.

(* ================================================================= *)
(** ** ... and they commute with the structural operations too       *)
(* ================================================================= *)

(** [aspOf_comp] / [dslpOf_comp] make the readings monoid morphisms; these
    make them ARROW morphisms.  In each case the reading of the structural
    operation is the same structural operation on the reading -- which is
    what lets a DSP or ASLP arrow be built by splitting, operating on each
    part, and recombining ([DSPMonad.v] / [ASLPMonad.v]). *)

Section MorphismStruct.

  Context {X Y C : Type}.

  Theorem aspOf_first (R : SPureArr X Y) (P : X * C -> Prop) (q : Y * C) :
    aspOf (arr_first R) P q <-> aspOf R (fun x => P (x, snd q)) (fst q).
  Proof.
    destruct q as [b c']. cbn. split.
    - intros [[a c] [HP [HR Hc]]]. subst c. exists a. split; assumption.
    - intros [a [HP HR]]. exists (a, c').
      split; [ exact HP | split; [ exact HR | reflexivity ] ].
  Qed.

  Theorem dslpOf_first (R : SPureArr X Y) (P : X * C -> Prop) (q : Y * C) :
    dslpOf (arr_first R) P q <-> dslpOf R (fun x => P (x, snd q)) (fst q).
  Proof.
    destruct q as [b c']. cbn. split.
    - intros H a HR. exact (H (a, c') (conj HR eq_refl)).
    - intros H [a c] [HR Hc]. subst c. exact (H a HR).
  Qed.

  (** At [inl] the reading is the reading of [R]; at [inr] the value passes
      through, and BOTH readings agree there -- which is why a conjunction
      or a disjunction of them is still the reading of [arr_left R]. *)

  Theorem aspOf_left_inl (R : SPureArr X Y) (P : X + C -> Prop) (b : Y) :
    aspOf (arr_left R) P (inl b) <-> aspOf R (fun x => P (inl x)) b.
  Proof.
    cbn. split.
    - intros [[a|c] [HP HR]]; [ exists a; split; assumption | destruct HR ].
    - intros [a [HP HR]]. exists (inl a). split; assumption.
  Qed.

  Theorem aspOf_left_inr (R : SPureArr X Y) (P : X + C -> Prop) (c' : C) :
    aspOf (arr_left R) P (inr c') <-> P (inr c').
  Proof.
    cbn. split.
    - intros [[a|c] [HP HR]]; [ destruct HR | cbn in HR; subst c; exact HP ].
    - intro HP. exists (inr c'). split; [ exact HP | reflexivity ].
  Qed.

  Theorem dslpOf_left_inl (R : SPureArr X Y) (P : X + C -> Prop) (b : Y) :
    dslpOf (arr_left R) P (inl b) <-> dslpOf R (fun x => P (inl x)) b.
  Proof.
    cbn. split.
    - intros H a HR. exact (H (inl a) HR).
    - intros H [a|c] HR; [ exact (H a HR) | destruct HR ].
  Qed.

  Theorem dslpOf_left_inr (R : SPureArr X Y) (P : X + C -> Prop) (c' : C) :
    dslpOf (arr_left R) P (inr c') <-> P (inr c').
  Proof.
    cbn. split.
    - intro H. exact (H (inr c') eq_refl).
    - intros HP [a|c] HR; [ destruct HR | cbn in HR; subst c; exact HP ].
  Qed.

End MorphismStruct.

(* ================================================================= *)
(** ** [PredArr]'s congruences, usable as rewriting steps            *)
(* ================================================================= *)

(** [comp_proper] / [first_proper] / [left_proper] are [ArrowLaws_Pred]'s and
    [ArrowChoiceLaws_Pred]'s [Proper] fields, restated with [arrow_eq] already
    reduced to [Pred_eq].  That matters: stated through [ArrowEq_Pred] the
    relation sits under a record projection [apply] will not unfold, and any
    congruence step built on them leaves the intermediate type of the
    composition as an evar.  Restated, they apply at the head of a goal.

    [DSPMonad.v] and [ASLPMonad.v] both need them, which is why they live
    here rather than locally in either. *)

Lemma Pred_comp_cong {X Y Z} (R R' : SPureArr X Y) (T T' : SPureArr Y Z) :
  Pred_eq R R' -> Pred_eq T T' ->
  Pred_eq (@arr_comp PredArr _ X Y Z R T) (arr_comp R' T').
Proof.
  intros HR HT.
  exact (@comp_proper PredArr Arrow_Pred ArrowEq_Pred ArrowLaws_Pred
           X Y Z R R' HR T T' HT).
Qed.

Lemma Pred_first_cong {X Y C} (R R' : SPureArr X Y) :
  Pred_eq R R' -> Pred_eq (@arr_first PredArr _ X Y C R) (arr_first R').
Proof.
  intro HR.
  exact (@first_proper PredArr Arrow_Pred ArrowEq_Pred ArrowLaws_Pred
           X Y C R R' HR).
Qed.

Lemma Pred_left_cong {X Y C} (R R' : SPureArr X Y) :
  Pred_eq R R' -> Pred_eq (@arr_left PredArr _ _ X Y C R) (arr_left R').
Proof.
  intro HR.
  exact (@left_proper PredArr Arrow_Pred ArrowChoice_Pred ArrowEq_Pred
           ArrowChoiceLaws_Pred X Y C R R' HR).
Qed.

(* ================================================================= *)
(** ** Orders                                                        *)
(* ================================================================= *)

(** One order on the carrier, and its flip.  [ordSP] is the order the ASP,
    DSP and ASLP readings are monotone for; [ordSPop] is DSLP's, by
    [dslpOf_incl].  Both stacks use the same two, because every level of
    the stack is still a [PredArr] at a larger type. *)

Definition ordSP {S A} : relation (SPSt S A) := @Pred_le _ _.
Definition ordSPop {S A} : relation (SPSt S A) := fun m n => Pred_le n m.

Definition ordSPExc {S A} : relation (SPStExc S A) := @Pred_le _ _.
Definition ordSPExcOp {S A} : relation (SPStExc S A) := fun m n => Pred_le n m.

Section Ordered.

  Variable S : Type.

  #[local] Existing Instance Monad_SPSt.
  #[local] Existing Instance Eq1_SPSt.
  #[local] Existing Instance Eq1Equivalence_SPSt.

  #[global] Instance OrderedMonad_SPSt : OrderedMonad (SPSt S) (@ordSP S).
  Proof.
    constructor.
    - intro A. apply Pred_le_PreOrder.
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
    - intro A. apply Pred_le_PreOrder.
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

(* ================================================================= *)
(** ** [bind] as composition of denoted relations, for any arrow      *)
(* ================================================================= *)

(** An arrow together with a map [rel] reading each element as the relation
    it denotes, such that every arrow operation denotes the corresponding
    [PredArr] operation.  [ASPArrowRel.v] proves [aspRelS_bind] /
    [aspRelE_bind] by hand, using only these five facts; stated once here,
    DSP and ASLP get the same lemmas by instantiation ([RelDenote_DSP],
    [RelDenote_ASLP]). *)

Class RelDenote (arr : Type -> Type -> Type) `{HA : Arrow arr}
  `{HC : @ArrowChoice arr HA} `{HAA : @ArrowApply arr HA}
  (rel : forall X Y, arr X Y -> X -> Y -> Prop) : Prop := {
  rd_pure : forall X Y (h : X -> Y) x y, rel X Y (arr_pure h) x y <-> h x = y ;
  rd_comp : forall X Y Z (f : arr X Y) (g : arr Y Z) x z,
      rel X Z (arr_comp f g) x z <-> exists y, rel X Y f x y /\ rel Y Z g y z ;
  rd_first : forall X Y C (f : arr X Y) (p : X * C) (q : Y * C),
      rel _ _ (arr_first f) p q <-> rel X Y f (fst p) (fst q) /\ snd p = snd q ;
  rd_left : forall X Y C (f : arr X Y) (x : X + C) (y : Y + C),
      rel _ _ (arr_left f) x y <->
      match x, y with
      | inl a, inl b => rel X Y f a b
      | inr c, inr c' => c = c'
      | _, _ => False
      end ;
  rd_app : forall X Y (p : arr X Y * X) y,
      rel _ _ arr_app p y <-> rel X Y (fst p) (snd p) y
}.

Section RelationalBind.
  Context {arr : Type -> Type -> Type} `{HA : Arrow arr}
          `{HC : @ArrowChoice arr HA} `{HAA : @ArrowApply arr HA}
          {rel : forall X Y, arr X Y -> X -> Y -> Prop}
          `{RD : @RelDenote arr HA HC HAA rel}.

  Local Ltac rb_flat :=
    repeat match goal with
    | H : exists _, _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | p : _ * _ |- _ => destruct p
    | H : (_, _) = (_, _) |- _ => inversion H; clear H
    | H : ?x = ?y |- _ => first [ subst x | subst y ]
    | _ => progress cbn in *
    end.

  Local Ltac rb_build :=
    repeat first [ progress cbn | eassumption | reflexivity | split
                 | eexists (_, _) | eexists ].

  Local Ltac rb_simpl :=
    repeat first [ setoid_rewrite rd_comp | setoid_rewrite rd_pure
                 | setoid_rewrite rd_first | setoid_rewrite rd_app ].

  Local Ltac rb_simp_in H := cbv beta iota delta [state_shuffle_in state_shuffle_out swap] in H.

  (** At a fixed input. *)
  Lemma rel_bind {I A B} (m : arr I A) (k : A -> arr I B) i b :
    rel _ _ (@bind_arrow arr _ _ I A B m k) i b
    <-> exists a, rel _ _ m i a /\ rel _ _ (k a) i b.
  Proof.
    unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id. rb_simpl.
    split; [ intro H; rb_flat; eauto | intros [a [Hm Hk]]; rb_build ].
  Qed.

  (** Under [stateArrT S]. *)
  Lemma relS_bind (S : Type) {I A B} (m : stateArrT S arr I A)
    (k : A -> stateArrT S arr I B) i s r :
    rel _ _ (@bind_arrow (stateArrT S arr) _ _ I A B m k) (i, s) r
    <-> exists a s', rel _ _ m (i, s) (a, s') /\ rel _ _ (k a) (i, s') r.
  Proof.
    unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id.
    cbn [arr_comp arr_pure arr_first arr_app Arrow_stateArrT ArrowApply_stateArrT].
    rb_simpl.
    split; [ intro H; rb_flat; eauto | intros [a [s' [Hm Hk]]]; rb_build ].
  Qed.

  (** Under [optionArrT], then [stateArrT S (optionArrT _)]. *)
  Lemma relO_comp {X Y Z} (f : optionArrT arr X Y) (g : optionArrT arr Y Z) x o :
    rel _ _ (@arr_comp (optionArrT arr) _ X Y Z f g) x o <->
    exists o1, rel _ _ f x o1 /\ match o1 with Some y => rel _ _ g y o | None => o = None end.
  Proof.
    cbn [arr_comp Arrow_optionArrT].
    repeat first [ setoid_rewrite rd_comp | setoid_rewrite rd_pure
                 | setoid_rewrite rd_left ].
    split.
    - intros [b [Hf [c [Hc [d [Hd Ho]]]]]]. subst c o. exists b. split; [ exact Hf |].
      destruct b as [y|], d as [z|[]]; cbn in *; solve [ exact Hd | contradiction | reflexivity ].
    - intros [[y|] [Hf Hg]].
      + exists (Some y). split; [ exact Hf |]. exists (inl y). split; [ reflexivity |].
        exists (inl o). split; [ exact Hg | reflexivity ].
      + subst o. exists None. split; [ exact Hf |]. exists (inr tt). split; [ reflexivity |].
        exists (inr tt). split; reflexivity.
  Qed.

  Lemma relO_pure {X Y} (h : X -> Y) x o :
    rel _ _ (@arr_pure (optionArrT arr) _ X Y h) x o <-> o = Some (h x).
  Proof.
    cbn [arr_pure Arrow_optionArrT]. rewrite rd_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma relO_first {X Y C} (f : optionArrT arr X Y) x (c : C) o :
    rel _ _ (@arr_first (optionArrT arr) _ X Y C f) (x, c) o <->
    exists o1, rel _ _ f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    cbn [arr_first arr_comp Arrow_optionArrT].
    rewrite rd_comp. setoid_rewrite rd_first. setoid_rewrite rd_pure.
    split.
    - intros [[o1 c'] [[Hf Hc] Ho]]. cbn in *. subst. exists o1. split; [ exact Hf |].
      destruct o1; reflexivity.
    - intros [o1 [Hf ->]]. exists (o1, c). cbn. split; [ exact (conj Hf eq_refl) |].
      destruct o1; reflexivity.
  Qed.

  Section StExc.
    Variable S : Type.
    Local Notation T := (stateArrT S (optionArrT arr)).

    Lemma relE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
      rel _ _ (@arr_comp T _ X Y Z f g) p o <->
      exists o1, rel _ _ f p o1 /\ match o1 with Some q => rel _ _ g q o | None => o = None end.
    Proof. exact (relO_comp f g p o). Qed.

    Lemma relE_pure {X Y} (h : X -> Y) x s o :
      rel _ _ (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
    Proof. exact (relO_pure _ (x, s) o). Qed.

    Lemma relE_first {X Y C} (f : T X Y) x (c : C) s o :
      rel _ _ (@arr_first T _ X Y C f) ((x, c), s) o <->
      exists o1, rel _ _ f (x, s) o1 /\
        o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
    Proof.
      unfold arr_first at 1; cbn [Arrow_stateArrT].
      rewrite relO_comp. split.
      - intros [o1 [H1 H2]]. apply relO_pure in H1. subst o1. rb_simp_in H2.
        apply relO_comp in H2. destruct H2 as [o2 [H2 H3]].
        apply relO_first in H2. destruct H2 as [o3 [H3' ->]].
        exists o3. split; [ exact H3' |].
        destruct o3 as [[y s']|]; rb_simp_in H3; [ apply relO_pure in H3 |]; exact H3.
      - intros [o1 [Hf ->]]. exists (Some ((x, s), c)). split; [ apply relO_pure; reflexivity |].
        apply relO_comp. exists (match o1 with Some y => Some (y, c) | None => None end).
        split; [ apply relO_first; exists o1; split; [ exact Hf | reflexivity ] |].
        destruct o1 as [[y s']|]; [ apply relO_pure |]; reflexivity.
    Qed.

    Lemma relE_app {X Y} (f : T X Y) x s o :
      rel _ _ (@arr_app T _ _ X Y) ((f, x), s) o <-> rel _ _ f (x, s) o.
    Proof.
      unfold arr_app at 1; cbn [ArrowApply_stateArrT].
      rewrite relO_comp. split.
      - intros [o1 [H1 H2]]. apply relO_pure in H1. subst o1.
        exact (proj1 (rd_app _ _ (f, (x, s)) o) H2).
      - intro H. exists (Some (f, (x, s))). split; [ apply relO_pure; reflexivity |].
        exact (proj2 (rd_app _ _ (f, (x, s)) o) H).
    Qed.

    Lemma relE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
      rel _ _ (@bind_arrow T _ _ I A B m k) (i, s) o
      <-> exists o1, rel _ _ m (i, s) o1 /\
            match o1 with Some (a, s') => rel _ _ (k a) (i, s') o | None => o = None end.
    Proof.
      unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id.
      rewrite relE_comp. split.
      - intros [o1 [H1 H2]].
        apply relE_comp in H1. destruct H1 as [o2 [H1 H3]]. apply relE_pure in H1. subst o2.
        apply relE_comp in H3. destruct H3 as [o3 [H3 H4]].
        apply relE_first in H3. destruct H3 as [o4 [Hm ->]].
        exists o4. split; [ exact Hm |].
        destruct o4 as [[a s']|]; rb_simp_in H4; [| subst o1; exact H2 ].
        apply relE_comp in H4. destruct H4 as [o5 [H4 H5]].
        apply relE_pure in H4. subst o5. rb_simp_in H5.
        apply relE_comp in H5. destruct H5 as [o6 [H5 H6]].
        apply relE_first in H5. destruct H5 as [o7 [H5 ->]].
        apply relE_pure in H5. subst o7. rb_simp_in H6.
        apply relE_pure in H6. subst o1. rb_simp_in H2.
        apply relE_comp in H2. destruct H2 as [o8 [H7 H8]].
        apply relE_pure in H7. subst o8. rb_simp_in H8.
        exact (proj1 (relE_app (k a) i s' o) H8).
      - intros [o1 [Hm Hk]].
        exists (match o1 with Some (a, s') => Some ((a, i), s') | None => None end).
        split.
        + apply relE_comp. exists (Some ((i, i), s)). split; [ apply relE_pure; reflexivity |].
          apply relE_comp.
          exists (match o1 with Some (a, s') => Some ((a, i), s') | None => None end).
          split; [ apply relE_first; exists o1; split; [ exact Hm | reflexivity ] |].
          destruct o1 as [[a s']|]; [| reflexivity ].
          apply relE_comp. exists (Some ((i, a), s')). split; [ apply relE_pure; reflexivity |].
          apply relE_comp. exists (Some ((i, a), s')).
          split; [ apply relE_first; exists (Some (i, s')); split; [ apply relE_pure | ]; reflexivity |].
          apply relE_pure. reflexivity.
        + destruct o1 as [[a s']|]; [| exact Hk ].
          apply relE_comp. exists (Some ((k a, i), s')). split; [ apply relE_pure; reflexivity |].
          exact (proj2 (relE_app (k a) i s' o) Hk).
    Qed.
  End StExc.

End RelationalBind.
