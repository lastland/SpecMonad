(** * The DSLP specification monads

    Three specification monads, all at input [unit]:

      [DSLP]        = [DSLPArr unit]                          (* SLP        *)
      [DSLPSt S]    = [stateArrT S DSLPArr unit]              (* SLP^St     *)
      [DSLPStExc S] = [stateArrT S (optionArrT DSLPArr) unit] (* SLP^StExc  *)

    Fixing the input at [unit] gives a SPECIFICATION MONAD in each case.
    The [MonadLawsE] instances are [MonadLawsE_Arrow] ([Lib/Arrow/ArrowMonad.v])
    at the arrow and at its two transformer stacks; [bind] monotonicity is
    proved from [dslpRel_incl], which runs backwards relative to ASP's.

    [SP/SPostArr.v] owns the binary carrier, operations, recovered-relation
    facts and laws. This module re-exports that infrastructure and fixes the
    input for unary specifications, runners and refinement orders.

    The last part of the file defines the stateless monad directly, with no
    arrow, as [DSLPSP], and shows that it is [DSLP]. It also supplies the
    universal demonic variant [SPostDem.SPost] of Maillard's SP monad and
    proves its equivalence with [DSLP] at input [unit]. The maps preserve
    readings, [ret], and [bind], preserve and reflect refinement order, and
    are inverse up to pointwise logical equivalence of readings.

    Maillard et al. present the existential construction in "Dijkstra Monads
    for All", PACMPL 3 (ICFP 2019), Article 104, section 4.1
    (https://doi.org/10.1145/3341708).

    For the demonic variant, the [MonadLawsE] instance, healthiness, round
    trips, both DSLP morphisms, and [dm4all_dem_to_dslp_order] use only
    [Classical_Prop.classic]. Its [Eq1Equivalence] and [OrderedMonad]
    instances, both reading lemmas, and [dslp_to_dm4all_dem_order] are
    closed under the global context, as checked with [Print Assumptions]. *)

From Coq Require Import Morphisms RelationClasses Setoid Relation_Definitions.
From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Arrow Require Import ArrowMonad.
From Incorrectness.SP Require Export SPostArr.



(* ================================================================= *)
(** ** [DSLP = DSLPArr unit]: a specification monad                *)
(* ================================================================= *)

(** [ret_arrow] / [bind_arrow] ([Lib/Arrow/ArrowMonad.v]) at input [unit], ordered by
    pointwise implication. *)

Section DSLP.

  Definition DSLP (A : Type) : Type := DSLPArr unit A.

  Definition retDSLP {A} (a : A) : DSLP A := @ret_arrow DSLPArr _ unit A a.

  Definition bindDSLP {A B} (m : DSLP A) (k : A -> DSLP B) : DSLP B :=
    @bind_arrow DSLPArr _ _ unit A B m k.

  #[global] Instance Monad_DSLP : Monad DSLP :=
    {| ret := @retDSLP ; bind := @bindDSLP |}.

  #[global] Instance Eq1_DSLP : Eq1 DSLP := fun A => @DSLPArr_eq unit A.

  #[global] Instance Eq1Equivalence_DSLP : @Eq1Equivalence DSLP _ Eq1_DSLP :=
    fun A => DSLPArr_eq_Equivalence.

  (** The two operations, on relations. *)

  Lemma dslpRel_retDSLP {A} (x : A) i a : dslpRel (retDSLP x) i a <-> x = a.
  Proof. apply dslpRel_pure. Qed.

  Lemma dslpRel_bindDSLP {A B} (m : DSLP A) (k : A -> DSLP B) i b :
    dslpRel (bindDSLP m k) i b <-> exists a, dslpRel m i a /\ dslpRel (k a) i b.
  Proof. apply dslpRel_bind. Qed.

  #[global] Instance MonadLawsE_DSLP : @MonadLawsE DSLP Eq1_DSLP _ :=
    @MonadLawsE_Arrow DSLPArr _ _ _ _ _ unit.

  (** Refinement: FORWARD pointwise implication, as for the SP monads. *)
  Definition ordDSLP {A} (m1 m2 : DSLP A) : Prop :=
    forall P a, getDSLPArr m1 P a -> getDSLPArr m2 P a.

  #[global] Instance ordDSLP_PreOrder {A} : PreOrder (@ordDSLP A).
  Proof.
    constructor.
    - intros m P a H. exact H.
    - intros m1 m2 m3 H1 H2 P a H. exact (H2 P a (H1 P a H)).
  Qed.

  #[global] Instance OrderedMonad_DSLP : OrderedMonad DSLP (@ordDSLP).
  Proof.
    constructor.
    - intro A. exact ordDSLP_PreOrder.
    - intros A m1 m2 H P a. unfold eq1, Eq1_DSLP, DSLPArr_eq in H. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk.
      pose proof (proj1 (dslpRel_incl m1 m2) Hm) as Hm'.
      unfold ordDSLP.
      apply (proj2 (dslpRel_incl (bindDSLP m1 k1) (bindDSLP m2 k2))).
      intros i b. rewrite !dslpRel_bindDSLP.
      intros [a [H1 H2]]. exists a.
      split; [ apply Hm', H1 | apply (proj1 (dslpRel_incl (k1 a) (k2 a)) (Hk a)), H2 ].
  Qed.

End DSLP.

(* ================================================================= *)
(** ** [DSLPSt S]: the state stack, again a specification monad   *)
(* ================================================================= *)

Section DSLPSt.
  Variable S : Type.

  Definition DSLPSt (A : Type) : Type := stateArrT S DSLPArr unit A.

  Definition retDSLPSt {A} (a : A) : DSLPSt A :=
    @ret_arrow (stateArrT S DSLPArr) _ unit A a.

  Definition bindDSLPSt {A B} (m : DSLPSt A) (k : A -> DSLPSt B) : DSLPSt B :=
    @bind_arrow (stateArrT S DSLPArr) _ _ unit A B m k.

  #[global] Instance Monad_DSLPSt : Monad DSLPSt :=
    {| ret := @retDSLPSt ; bind := @bindDSLPSt |}.

  #[global] Instance Eq1_DSLPSt : Eq1 DSLPSt := fun A => @DSLPArr_eq (unit * S) (A * S).

  #[global] Instance Eq1Equivalence_DSLPSt : @Eq1Equivalence DSLPSt _ Eq1_DSLPSt :=
    fun A => DSLPArr_eq_Equivalence.

  #[global] Instance MonadLawsE_DSLPSt : @MonadLawsE DSLPSt Eq1_DSLPSt _ :=
    @MonadLawsE_Arrow (stateArrT S DSLPArr) _ _ _ _ _ unit.

  Definition ordDSLPSt {A} (m1 m2 : DSLPSt A) : Prop :=
    forall P r, getDSLPArr m1 P r -> getDSLPArr m2 P r.

  #[global] Instance ordDSLPSt_PreOrder {A} : PreOrder (@ordDSLPSt A).
  Proof.
    constructor.
    - intros m P r H. exact H.
    - intros m1 m2 m3 H1 H2 P r H. exact (H2 P r (H1 P r H)).
  Qed.

  #[global] Instance OrderedMonad_DSLPSt : OrderedMonad DSLPSt (@ordDSLPSt).
  Proof.
    constructor.
    - intro A. exact ordDSLPSt_PreOrder.
    - intros A m1 m2 H P r. unfold eq1, Eq1_DSLPSt, DSLPArr_eq in H. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk.
      pose proof (proj1 (dslpRel_incl m1 m2) Hm) as Hm'.
      unfold ordDSLPSt.
      apply (proj2 (dslpRel_incl (bindDSLPSt m1 k1) (bindDSLPSt m2 k2))).
      intros [[] s] r. unfold bindDSLPSt. rewrite !dslpRelS_bind.
      intros [a [s' [H1 H2]]]. exists a, s'.
      split; [ apply Hm', H1 | apply (proj1 (dslpRel_incl (k1 a) (k2 a)) (Hk a)), H2 ].
  Qed.

End DSLPSt.

(* ================================================================= *)
(** ** [DSLPStExc S]: the state-and-exception stack               *)
(* ================================================================= *)

Section DSLPStExc.
  Variable S : Type.

  Definition DSLPStExc (A : Type) : Type := stateArrT S (optionArrT DSLPArr) unit A.

  Definition retDSLPStExc {A} (a : A) : DSLPStExc A :=
    @ret_arrow (stateArrT S (optionArrT DSLPArr)) _ unit A a.

  Definition bindDSLPStExc {A B} (m : DSLPStExc A) (k : A -> DSLPStExc B)
    : DSLPStExc B :=
    @bind_arrow (stateArrT S (optionArrT DSLPArr)) _ _ unit A B m k.

  #[global] Instance Monad_DSLPStExc : Monad DSLPStExc :=
    {| ret := @retDSLPStExc ; bind := @bindDSLPStExc |}.

  #[global] Instance Eq1_DSLPStExc : Eq1 DSLPStExc :=
    fun A => @DSLPArr_eq (unit * S) (option (A * S)).

  #[global] Instance Eq1Equivalence_DSLPStExc
    : @Eq1Equivalence DSLPStExc _ Eq1_DSLPStExc :=
    fun A => DSLPArr_eq_Equivalence.

  #[global] Instance MonadLawsE_DSLPStExc
    : @MonadLawsE DSLPStExc Eq1_DSLPStExc _ :=
    @MonadLawsE_Arrow (stateArrT S (optionArrT DSLPArr)) _ _ _ _ _ unit.

  Definition ordDSLPStExc {A} (m1 m2 : DSLPStExc A) : Prop :=
    forall P o, getDSLPArr m1 P o -> getDSLPArr m2 P o.

  #[global] Instance ordDSLPStExc_PreOrder {A} : PreOrder (@ordDSLPStExc A).
  Proof.
    constructor.
    - intros m P o H. exact H.
    - intros m1 m2 m3 H1 H2 P o H. exact (H2 P o (H1 P o H)).
  Qed.

  #[global] Instance OrderedMonad_DSLPStExc
    : OrderedMonad DSLPStExc (@ordDSLPStExc).
  Proof.
    constructor.
    - intro A. exact ordDSLPStExc_PreOrder.
    - intros A m1 m2 H P o. unfold eq1, Eq1_DSLPStExc, DSLPArr_eq in H. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk.
      pose proof (proj1 (dslpRel_incl m1 m2) Hm) as Hm'.
      unfold ordDSLPStExc.
      apply (proj2 (dslpRel_incl (bindDSLPStExc m1 k1) (bindDSLPStExc m2 k2))).
      intros [[] s] o. unfold bindDSLPStExc. rewrite !dslpRelE_bind.
      intros [o1 [H1 H2]]. exists o1. split; [ apply Hm', H1 |].
      destruct o1 as [[a s']|]; [ apply (proj1 (dslpRel_incl (k1 a) (k2 a)) (Hk a)), H2 | exact H2 ].
  Qed.

End DSLPStExc.

(* ================================================================= *)
(** ** Reading the three monads at a SHARED precondition             *)
(* ================================================================= *)

(** The mirror of [ASPMonad.v]'s readings.  Everything dualises: where
    [getASP] factors its precondition out as a CONJUNCTION and is strict
    ([~ getASP w False a]), [getDSLP] factors it out as an IMPLICATION and
    is top-preserving ([getDSLP w True a]).  The relation appears in the
    statements because, read demonically, "which inputs reach [r]" is a
    negative position: it cannot be phrased with [getDSLP] alone. *)

Section Readings.

  Definition getDSLP {A} (w : DSLP A) (p : Prop) (a : A) : Prop :=
    getDSLPArr w (fun _ => p) a.

  Definition dslpOfPred {A} (Q : A -> Prop) : DSLP A :=
    ofRelDSLPArr (fun _ => Q).

  Lemma getDSLP_of {A} (Q : A -> Prop) p a :
    getDSLP (dslpOfPred Q) p a <-> (Q a -> p).
  Proof.
    unfold getDSLP, dslpOfPred, ofRelDSLPArr. cbn. split.
    - intros H HQ. exact (H tt HQ).
    - intros H [] HQ. exact (H HQ).
  Qed.

  (** The dual of [getASP_singleton]. *)
  Lemma getDSLP_rel {A} (w : DSLP A) p a :
    getDSLP w p a <-> (dslpRel w tt a -> p).
  Proof.
    unfold getDSLP. rewrite get_dslpRel. split.
    - intros H Hr. exact (H tt Hr).
    - intros H [] Hr. exact (H Hr).
  Qed.

  Lemma getDSLP_mono {A} (w : DSLP A) (p q : Prop) a :
    (p -> q) -> getDSLP w p a -> getDSLP w q a.
  Proof.
    intros Hpq H. apply getDSLP_rel. intro Hr.
    exact (Hpq (proj1 (getDSLP_rel w p a) H Hr)).
  Qed.

  (** [ASP] is strict; [DSLP] is top-preserving. *)
  Lemma getDSLP_top {A} (w : DSLP A) a : getDSLP w True a.
  Proof. apply getDSLP_rel. intros _. exact I. Qed.

  Lemma getDSLP_ret {A} (x : A) p a : getDSLP (retDSLP x) p a <-> (x = a -> p).
  Proof.
    rewrite getDSLP_rel. split; intros H Hx; apply H;
      [ apply dslpRel_retDSLP, Hx | exact (proj1 (dslpRel_retDSLP x tt a) Hx) ].
  Qed.

  Lemma getDSLP_bind {A B} (m : DSLP A) (k : A -> DSLP B) p b :
    getDSLP (bindDSLP m k) p b <->
    (forall a, dslpRel (k a) tt b -> getDSLP m p a).
  Proof.
    rewrite getDSLP_rel. setoid_rewrite getDSLP_rel. split.
    - intros H a Hk Hm. apply H. apply dslpRel_bindDSLP. exists a. auto.
    - intros H Hr. apply dslpRel_bindDSLP in Hr.
      destruct Hr as [a [Hm Hk]]. exact (H a Hk Hm).
  Qed.

  Lemma eq1_DSLP_get {A} (m n : DSLP A) :
    eq1 m n <-> (forall p a, getDSLP m p a <-> getDSLP n p a).
  Proof.
    split.
    - intros H p a. apply H.
    - intros H P a. unfold eq1, Eq1_DSLP, DSLPArr_eq.
      transitivity (getDSLP m (P tt) a);
        [ apply getDSLPArr_ext_iff; intros []; reflexivity |].
      rewrite H. apply getDSLPArr_ext_iff. intros []. reflexivity.
  Qed.

  Lemma ordDSLP_get {A} (m n : DSLP A) :
    ordDSLP m n <-> (forall p a, getDSLP m p a -> getDSLP n p a).
  Proof.
    split.
    - intros H p a. apply H.
    - intros H P a HP.
      apply (getDSLPArr_ext n (fun _ => P tt) P a); [ intros []; reflexivity |].
      apply (H (P tt)). apply (getDSLPArr_ext m P (fun _ => P tt) a);
        [ intros []; reflexivity | exact HP ].
  Qed.

  (* ---- the state stack ---- *)

  Variable S : Type.

  Definition getDSLPSt {A} (w : DSLPSt S A) (pre : S -> Prop) (r : A * S) : Prop :=
    getDSLPArr w (fun p => pre (snd p)) r.

  Definition dslpOfRelSt {A} (R : S -> A * S -> Prop) : DSLPSt S A :=
    ofRelDSLPArr (fun p r => R (snd p) r).

  (** The relation at a single initial state. *)
  Definition dslpRelSt {A} (w : DSLPSt S A) (s : S) (r : A * S) : Prop :=
    dslpRel w (tt, s) r.

  Lemma getDSLPSt_rel {A} (w : DSLPSt S A) pre r :
    getDSLPSt w pre r <-> (forall s, dslpRelSt w s r -> pre s).
  Proof.
    unfold getDSLPSt, dslpRelSt. rewrite get_dslpRel. split.
    - intros H s Hr. exact (H (tt, s) Hr).
    - intros H [[] s] Hr. exact (H s Hr).
  Qed.

  Lemma getDSLPSt_of {A} (R : S -> A * S -> Prop) pre r :
    getDSLPSt (dslpOfRelSt R) pre r <-> (forall s, R s r -> pre s).
  Proof.
    unfold getDSLPSt, dslpOfRelSt, ofRelDSLPArr. cbn. split.
    - intros H s HR. exact (H (tt, s) HR).
    - intros H [[] s] HR. exact (H s HR).
  Qed.

  Lemma dslpRelSt_of {A} (R : S -> A * S -> Prop) s r :
    dslpRelSt (dslpOfRelSt R) s r <-> R s r.
  Proof. unfold dslpRelSt, dslpOfRelSt. rewrite dslpRel_ofRel. reflexivity. Qed.

  Lemma getDSLPSt_cong {A} (w : DSLPSt S A) (P Q : S -> Prop) r :
    (forall s, P s <-> Q s) -> (getDSLPSt w P r <-> getDSLPSt w Q r).
  Proof.
    intro H. unfold getDSLPSt. apply getDSLPArr_ext_iff. intros [[] s]. apply H.
  Qed.

  Lemma getDSLPSt_mono {A} (w : DSLPSt S A) (P Q : S -> Prop) r :
    (forall s, P s -> Q s) -> getDSLPSt w P r -> getDSLPSt w Q r.
  Proof.
    intros H Hw. apply getDSLPSt_rel. intros s Hr.
    apply H. exact (proj1 (getDSLPSt_rel w P r) Hw s Hr).
  Qed.

  Lemma getDSLPSt_top {A} (w : DSLPSt S A) r : getDSLPSt w (fun _ => True) r.
  Proof. apply getDSLPSt_rel. intros _ _. exact I. Qed.

  Lemma getDSLPSt_ret {A} (x : A) pre r :
    getDSLPSt (retDSLPSt S x) pre r <-> (forall s, r = (x, s) -> pre s).
  Proof.
    rewrite getDSLPSt_rel. unfold dslpRelSt. split.
    - intros H s Hr. exact (H s (proj2 (dslpRelS_ret S x tt s r) Hr)).
    - intros H s Hr. exact (H s (proj1 (dslpRelS_ret S x tt s r) Hr)).
  Qed.

  Lemma getDSLPSt_bind {A B} (m : DSLPSt S A) (k : A -> DSLPSt S B) pre r :
    getDSLPSt (bindDSLPSt S m k) pre r <->
    (forall a s', dslpRelSt (k a) s' r -> getDSLPSt m pre (a, s')).
  Proof.
    rewrite getDSLPSt_rel. setoid_rewrite getDSLPSt_rel.
    unfold dslpRelSt, bindDSLPSt. split.
    - intros H a s' Hk s Hm.
      apply H. apply (proj2 (dslpRelS_bind S m k tt s r)). exists a, s'. auto.
    - intros H s Hr.
      destruct (proj1 (dslpRelS_bind S m k tt s r) Hr) as [a [s' [Hm Hk]]].
      exact (H a s' Hk s Hm).
  Qed.

  Lemma eq1_DSLPSt_get {A} (m n : DSLPSt S A) :
    eq1 m n <-> (forall pre r, getDSLPSt m pre r <-> getDSLPSt n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r. unfold eq1, Eq1_DSLPSt, DSLPArr_eq.
      transitivity (getDSLPSt m (fun s => P (tt, s)) r);
        [ apply getDSLPArr_ext_iff; intros [[] s]; reflexivity |].
      rewrite H. apply getDSLPArr_ext_iff. intros [[] s]. reflexivity.
  Qed.

  Definition ordDSLPStAt {A} (pre : S -> Prop) (m n : DSLPSt S A) : Prop :=
    forall r, getDSLPSt m pre r -> getDSLPSt n pre r.

  Lemma ordDSLPSt_get {A} (m n : DSLPSt S A) :
    ordDSLPSt S m n <-> (forall pre r, getDSLPSt m pre r -> getDSLPSt n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r HP.
      apply (getDSLPArr_ext n (fun p => P (tt, snd p)) P r);
        [ intros [[] s]; reflexivity |].
      apply (H (fun s => P (tt, s))).
      apply (getDSLPArr_ext m P (fun p => P (tt, snd p)) r);
        [ intros [[] s]; reflexivity | exact HP ].
  Qed.

  (* ---- the state-and-exception stack ---- *)

  Definition getDSLPStExc {A} (w : DSLPStExc S A) (pre : S -> Prop)
    (r : option (A * S)) : Prop :=
    getDSLPArr w (fun p => pre (snd p)) r.

  Definition dslpOfRelStExc {A} (R : S -> option (A * S) -> Prop) : DSLPStExc S A :=
    ofRelDSLPArr (fun p r => R (snd p) r).

  Definition dslpRelStExc {A} (w : DSLPStExc S A) (s : S) (r : option (A * S)) : Prop :=
    dslpRel w (tt, s) r.

  Lemma getDSLPStExc_rel {A} (w : DSLPStExc S A) pre r :
    getDSLPStExc w pre r <-> (forall s, dslpRelStExc w s r -> pre s).
  Proof.
    unfold getDSLPStExc, dslpRelStExc. rewrite get_dslpRel. split.
    - intros H s Hr. exact (H (tt, s) Hr).
    - intros H [[] s] Hr. exact (H s Hr).
  Qed.

  Lemma getDSLPStExc_of {A} (R : S -> option (A * S) -> Prop) pre r :
    getDSLPStExc (dslpOfRelStExc R) pre r <-> (forall s, R s r -> pre s).
  Proof.
    unfold getDSLPStExc, dslpOfRelStExc, ofRelDSLPArr. cbn. split.
    - intros H s HR. exact (H (tt, s) HR).
    - intros H [[] s] HR. exact (H s HR).
  Qed.

  Lemma dslpRelStExc_of {A} (R : S -> option (A * S) -> Prop) s r :
    dslpRelStExc (dslpOfRelStExc R) s r <-> R s r.
  Proof. unfold dslpRelStExc, dslpOfRelStExc. rewrite dslpRel_ofRel. reflexivity. Qed.

  Lemma getDSLPStExc_cong {A} (w : DSLPStExc S A) (P Q : S -> Prop) r :
    (forall s, P s <-> Q s) -> (getDSLPStExc w P r <-> getDSLPStExc w Q r).
  Proof.
    intro H. unfold getDSLPStExc. apply getDSLPArr_ext_iff. intros [[] s]. apply H.
  Qed.

  Lemma getDSLPStExc_mono {A} (w : DSLPStExc S A) (P Q : S -> Prop) r :
    (forall s, P s -> Q s) -> getDSLPStExc w P r -> getDSLPStExc w Q r.
  Proof.
    intros H Hw. apply getDSLPStExc_rel. intros s Hr.
    apply H. exact (proj1 (getDSLPStExc_rel w P r) Hw s Hr).
  Qed.

  Lemma getDSLPStExc_top {A} (w : DSLPStExc S A) r :
    getDSLPStExc w (fun _ => True) r.
  Proof. apply getDSLPStExc_rel. intros _ _. exact I. Qed.

  Lemma getDSLPStExc_ret {A} (x : A) pre r :
    getDSLPStExc (retDSLPStExc S x) pre r <-> (forall s, r = Some (x, s) -> pre s).
  Proof.
    rewrite getDSLPStExc_rel. unfold dslpRelStExc. split.
    - intros H s Hr. exact (H s (proj2 (dslpRelE_ret S x tt s r) Hr)).
    - intros H s Hr. exact (H s (proj1 (dslpRelE_ret S x tt s r) Hr)).
  Qed.

  Lemma getDSLPStExc_bind {A B} (m : DSLPStExc S A) (k : A -> DSLPStExc S B) pre r :
    getDSLPStExc (bindDSLPStExc S m k) pre r <->
    (forall o, match o with
               | Some (a, s') => dslpRelStExc (k a) s' r
               | None => r = None
               end -> getDSLPStExc m pre o).
  Proof.
    rewrite getDSLPStExc_rel. setoid_rewrite getDSLPStExc_rel.
    unfold dslpRelStExc, bindDSLPStExc. split.
    - intros H o Ho s Hm.
      apply H. apply (proj2 (dslpRelE_bind S m k tt s r)). exists o. auto.
    - intros H s Hr.
      destruct (proj1 (dslpRelE_bind S m k tt s r) Hr) as [o [Hm Ho]].
      exact (H o Ho s Hm).
  Qed.

  Lemma eq1_DSLPStExc_get {A} (m n : DSLPStExc S A) :
    eq1 m n <-> (forall pre r, getDSLPStExc m pre r <-> getDSLPStExc n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r. unfold eq1, Eq1_DSLPStExc, DSLPArr_eq.
      transitivity (getDSLPStExc m (fun s => P (tt, s)) r);
        [ apply getDSLPArr_ext_iff; intros [[] s]; reflexivity |].
      rewrite H. apply getDSLPArr_ext_iff. intros [[] s]. reflexivity.
  Qed.

  Definition ordDSLPStExcAt {A} (pre : S -> Prop) (m n : DSLPStExc S A) : Prop :=
    forall r, getDSLPStExc m pre r -> getDSLPStExc n pre r.

  Lemma ordDSLPStExc_get {A} (m n : DSLPStExc S A) :
    ordDSLPStExc S m n <-> (forall pre r, getDSLPStExc m pre r -> getDSLPStExc n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r HP.
      apply (getDSLPArr_ext n (fun p => P (tt, snd p)) P r);
        [ intros [[] s]; reflexivity |].
      apply (H (fun s => P (tt, s))).
      apply (getDSLPArr_ext m P (fun p => P (tt, snd p)) r);
        [ intros [[] s]; reflexivity | exact HP ].
  Qed.

End Readings.

Arguments getDSLPSt {S} {A}.
Arguments getDSLPStExc {S} {A}.
Arguments dslpOfRelSt {S} {A}.
Arguments dslpOfRelStExc {S} {A}.
Arguments dslpRelSt {S} {A}.
Arguments dslpRelStExc {S} {A}.
Arguments ordDSLPStAt {S} {A}.
Arguments ordDSLPStExcAt {S} {A}.
Arguments ordDSLPSt {S} {A}.
Arguments ordDSLPStExc {S} {A}.
Arguments retDSLPSt {S} {A}.
Arguments bindDSLPSt {S} {A} {B}.
Arguments retDSLPStExc {S} {A}.
Arguments bindDSLPStExc {S} {A} {B}.

(* ================================================================= *)
(** * The directly defined monad [DSLPSP]                             *)
(* ================================================================= *)

(** The dual of [ASPSP] in [ASPMonad.v].  [DSLP] above comes from the arrow
    [DSLPArr] at input [unit]; without state the same monad can be written
    down directly on [SPPure A = Prop -> A -> Prop].  The healthy
    transformers factor the precondition out as a disjunct ([MSingleton]),
    which at a [Prop] precondition is the same as terminating and
    conjunctive ([meet_iff_msingleton]).  [bindDSLPSP] hands the
    postcondition of the prefix to the continuation as its precondition, for
    EVERY intermediate value.

    [DSLPSP] and [DSLP] are the same monad: [dslpsp_to_dslp] and
    [dslp_to_dslpsp] are mutually inverse, preserve [ret] and [bind], and
    carry the orders to each other. *)

From Coq Require Import PropExtensionality Classical_Prop.
From Incorrectness.SP Require Import SPostMonad RawSP.

Section PureDSLPMonad.
  Definition MeetPreserving {A} (w : SPPure A) : Prop :=
    Terminating w /\ Conjunctive w.

  Definition MSingleton {A} (w : SPPure A) : Prop :=
    forall (p : Prop) (a : A), w p a <-> p \/ w False a.

  (** Dually to [join_to_singleton]: at [SPPure] the precondition is a [Prop],
      so [Terminating] alone already forces [MSingleton]; [Conjunctive] is not
      needed here. *)
  Lemma meet_to_msingleton {A} (w : SPPure A) :
    MeetPreserving w -> MSingleton w.
  Proof.
    intros [HT _] p a. destruct (classic p) as [Hp | Hnp].
    - assert (Heq : p = True)
        by (apply propositional_extensionality;
            split; [ intros _; exact I | intros _; exact Hp ]).
      rewrite Heq. split; [ intros _; left; exact I | intros _; exact (HT a) ].
    - assert (Heq : p = False)
        by (apply propositional_extensionality; split; [ exact Hnp | intros [] ]).
      rewrite Heq. split;
        [ intro Hw; right; exact Hw | intros [[] | Hf]; exact Hf ].
  Qed.

  Lemma msingleton_to_meet {A} (w : SPPure A) :
    MSingleton w -> MeetPreserving w.
  Proof.
    intro H. split.
    - intro a. apply H. left. exact I.
    - intros I i0 p a. split.
      + intro Hw. destruct (proj1 (H (forall i, p i) a) Hw) as [Hall | Hf].
        * intro i. apply H. left. exact (Hall i).
        * intro i. apply H. right. exact Hf.
      + intro Hall. apply H.
        destruct (classic (w False a)) as [Hf | Hnf]; [ right; exact Hf |].
        left. intro i. destruct (proj1 (H (p i) a) (Hall i)) as [Hpi | Hf];
          [ exact Hpi | destruct (Hnf Hf) ].
  Qed.

  (** Dually to [strict_to_singleton]: [meet_to_msingleton] uses only its
      [Terminating] half, so [Terminating] alone forces [MSingleton]. *)
  Lemma terminating_to_msingleton {A} (w : SPPure A) :
    Terminating w -> MSingleton w.
  Proof.
    intros HT p a. destruct (classic p) as [Hp | Hnp].
    - assert (Heq : p = True)
        by (apply propositional_extensionality;
            split; [ intros _; exact I | intros _; exact Hp ]).
      rewrite Heq. split; [ intros _; left; exact I | intros _; exact (HT a) ].
    - assert (Heq : p = False)
        by (apply propositional_extensionality; split; [ exact Hnp | intros [] ]).
      rewrite Heq. split; [ intro H; right; exact H | intros [[] | H]; exact H ].
  Qed.

  (** [MSingleton] gives the OTHER connective too. *)
  Lemma msingleton_to_disjunctive {A} (w : SPPure A) :
    MSingleton w -> Disjunctive w.
  Proof.
    intros H I i0 p a. rewrite (H (exists i, p i) a). split.
    - intros [[i Hi] | Hf].
      + exists i. apply H. left. exact Hi.
      + exists i0. apply H. right. exact Hf.
    - intros [i Hi]. destruct (proj1 (H (p i) a) Hi) as [Hp | Hf];
        [ left; exists i; exact Hp | right; exact Hf ].
  Qed.

  Theorem meet_iff_msingleton {A} (w : SPPure A) :
    MeetPreserving w <-> MSingleton w.
  Proof. split; [apply meet_to_msingleton | apply msingleton_to_meet]. Qed.

  Theorem monotone_codomainDSLP_iff_msingleton {A} (w : SPPure A) :
    (Monotone w /\ CodomainDSLP w) <-> MSingleton w.
  Proof.
    split.
    - intros [Hmono Hcod] p a. split.
      + intro Hw. destruct (classic p) as [Hp | Hnp]; [left; exact Hp |].
        right. exact (Hmono p False a Hnp Hw).
      + intros [Hp | Hf];
          [ exact (Hcod p a Hp) | exact (Hmono False p a (False_ind p) Hf) ].
    - intro H. split.
      + intros p q a Hpq Hw. apply H.
        destruct (proj1 (H p a) Hw) as [Hp | Hf];
          [ left; exact (Hpq Hp) | right; exact Hf ].
      + intros p a Hp. apply H. left. exact Hp.
  Qed.

  Definition DSLPSP (A : Type) : Type := { w : SPPure A | MSingleton w }.

  Definition getDSLPSP {A} (w : DSLPSP A) : SPPure A := proj1_sig w.

  Lemma getMSP_singleton {A} (w : DSLPSP A) (p : Prop) (a : A) :
    getDSLPSP w p a <-> (p \/ getDSLPSP w False a).
  Proof. exact (proj2_sig w p a). Qed.

  (** Directed forms, used instead of [rewrite] for the same performance reason
      as [getASPSP_split] / [getASPSP_merge]. *)
  Definition getMSP_split {A} (w : DSLPSP A) (p : Prop) (a : A)
    : getDSLPSP w p a -> (p \/ getDSLPSP w False a) := proj1 (getMSP_singleton w p a).
  Definition getMSP_merge {A} (w : DSLPSP A) (p : Prop) (a : A)
    : (p \/ getDSLPSP w False a) -> getDSLPSP w p a := proj2 (getMSP_singleton w p a).

  Lemma getMSP_mono {A} (w : DSLPSP A) (p q : Prop) (a : A) :
    (p -> q) -> getDSLPSP w p a -> getDSLPSP w q a.
  Proof.
    intros Hpq H. apply getMSP_merge.
    destruct (getMSP_split w p a H) as [Hp | Hf];
      [left; exact (Hpq Hp) | right; exact Hf].
  Qed.

  #[program] Definition retDSLPSP {A} (v : A) : DSLPSP A :=
    fun p a => a = v -> p.
  Next Obligation.
  Proof.
    intros p a. split.
    - intro H. destruct (classic p) as [Hp | Hnp]; [left; exact Hp |].
      right. intro Heq. exact (Hnp (H Heq)).
    - intros [Hp | Hn] Heq; [exact Hp | destruct (Hn Heq)].
  Qed.

  #[program] Definition bindDSLPSP {A B} (m : DSLPSP A) (k : A -> DSLPSP B)
    : DSLPSP B :=
    fun p b => forall a, (k a) (m p a) b.
  Next Obligation.
  Proof.
    intros p b. split.
    - (* [p] fails ==> nothing in the co-set of [m] can meet the co-set of [k] *)
      intro H. destruct (classic p) as [Hp | Hnp]; [left; exact Hp |].
      right. intro a. specialize (H a).
      apply (proj2_sig (k a) (proj1_sig m False a) b).
      destruct (proj1 (proj2_sig (k a) (proj1_sig m p a) b) H) as [Hmp | Hkf];
        [| right; exact Hkf ].
      left. destruct (proj1 (proj2_sig m p a) Hmp) as [Hp | Hmf];
        [ destruct (Hnp Hp) | exact Hmf ].
    - intros [Hp | H] a.
      + apply (proj2_sig (k a) (proj1_sig m p a) b). left.
        apply (proj2_sig m p a). left. exact Hp.
      + specialize (H a).
        apply (proj2_sig (k a) (proj1_sig m p a) b).
        destruct (proj1 (proj2_sig (k a) (proj1_sig m False a) b) H) as [Hmf | Hkf];
          [| right; exact Hkf ].
        left. apply (proj2_sig m p a). right. exact Hmf.
  Qed.

  #[global] Instance Monad_DSLPSP : Monad DSLPSP :=
    {| ret := fun _ => retDSLPSP ;
      bind := fun _ _ => bindDSLPSP |}.

  #[global] Instance Eq1_DSLPSP : Eq1 DSLPSP :=
    fun A m n => forall p a, getDSLPSP m p a <-> getDSLPSP n p a.

  #[global] Instance Eq1Equivalence_DSLPSP
    : @Eq1Equivalence DSLPSP _ Eq1_DSLPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a). specialize (H2 p a). tauto.
  Qed.

  (** Meet preservation and congruence in the [Prop] argument, both derived
      from [MSingleton] — the duals of [getASPSP]'s join and congruence facts. *)
  Lemma getMSP_meet {A} (w : DSLPSP A) (I : Type) (p : I -> Prop) (a : A) :
    getDSLPSP w (forall i, p i) a <-> forall i, getDSLPSP w (p i) a.
  Proof.
    split.
    - intros H i. apply getMSP_merge.
      destruct (getMSP_split w _ a H) as [Hall | Hf];
        [ left; exact (Hall i) | right; exact Hf ].
    - intro Hall. apply getMSP_merge.
      destruct (classic (getDSLPSP w False a)) as [Hf | Hnf]; [ right; exact Hf |].
      left. intro i. destruct (getMSP_split w _ a (Hall i)) as [Hpi | Hf];
        [ exact Hpi | destruct (Hnf Hf) ].
  Qed.

  Lemma getMSP_cong {A} (w : DSLPSP A) (p q : Prop) (a : A) :
    (p <-> q) -> (getDSLPSP w p a <-> getDSLPSP w q a).
  Proof.
    intro Hpq. split; intro H; apply getMSP_merge;
      destruct (getMSP_split w _ a H) as [Hx | Hf].
    - left. exact (proj1 Hpq Hx).
    - right. exact Hf.
    - left. exact (proj2 Hpq Hx).
    - right. exact Hf.
  Qed.

  #[global] Instance MonadLawsE_DSLPSP
    : @MonadLawsE DSLPSP Eq1_DSLPSP _.
  Proof.
    constructor.
    - (* bind_ret_l: only [a = x] contributes; every other [a] gets a
         vacuously-true precondition, on which any [MSingleton] fires *)
      intros A B f x. unfold eq1, Eq1_DSLPSP. intros p b. split.
      + intro H. specialize (H x).
        apply (getMSP_mono (f x) (x = x -> p) p b); [| exact H].
        intro Himp. exact (Himp eq_refl).
      + intros H a. destruct (classic (a = x)) as [Heq | Hne].
        * subst a. apply (getMSP_mono (f x) p (x = x -> p) b); [| exact H].
          intros Hp _. exact Hp.
        * apply (getMSP_mono (f a) True (a = x -> p) b).
          -- intros _ Heq. destruct (Hne Heq).
          -- apply getMSP_merge. left. exact I.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_DSLPSP. intros p a. split.
      + intro H. exact (H a eq_refl).
      + intros H a0 Heq. subst a0. exact H.
    - (* bind_bind: the precondition handed to [g b] is a MEET over [a], and
         [g b] preserves meets — the exact dual of the [bindASPSP] argument *)
      intros A B C x f g. unfold eq1, Eq1_DSLPSP. intros p c. split.
      + intros H a b.
        exact (proj1 (getMSP_meet (g b) A
                        (fun a0 => getDSLPSP (f a0) (getDSLPSP x p a0) b) c) (H b) a).
      + intros H b.
        apply (getMSP_meet (g b) A (fun a => getDSLPSP (f a) (getDSLPSP x p a) b) c).
        intro a. exact (H a b).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_DSLPSP in *. intros p b.
      split; intros H a; specialize (H a).
      + exact (proj1 (Hfg a _ b)
                 (proj1 (getMSP_cong (f a) _ _ b (Hxy p a)) H)).
      + exact (proj2 (getMSP_cong (f a) _ _ b (Hxy p a))
                 (proj2 (Hfg a _ b) H)).
  Qed.
End PureDSLPMonad.

(* ================================================================= *)
(** ** Orders on the pure variant                                     *)
(* ================================================================= *)

Section PureDSLPOrders.
  Definition ordDSLPSP {A} (m1 m2 : DSLPSP A) : Prop :=
    forall p a, getDSLPSP m1 p a -> getDSLPSP m2 p a.
  Definition ordDSLPSPAt {A} (pre : Prop) (m1 m2 : DSLPSP A) : Prop :=
    forall a, getDSLPSP m1 pre a -> getDSLPSP m2 pre a.

  (** Dual to [asp_bot_pure]: [MSingleton] makes every DSLP true at [True]. *)
  Lemma dslp_top_pure {A} (w : DSLPSP A) (a : A) : getDSLPSP w True a.
  Proof. exact (getMSP_merge w True a (or_introl I)). Qed.
End PureDSLPOrders.

(* ================================================================= *)
(** ** [DSLPSP] is [DSLP]                                             *)
(* ================================================================= *)

#[program] Definition dslpsp_to_dslp {A} (w : DSLPSP A) : DSLP A :=
  fun (P : unit -> Prop) (a : A) => getDSLPSP w (P tt) a.
Next Obligation.
  split; [| split ].
  - intros P Q H a Hw. exact (getMSP_mono w (P tt) (Q tt) a (H tt) Hw).
  - intros a. exact (getMSP_merge w True a (or_introl I)).
  - intros I _ p a. exact (getMSP_meet w I (fun i => p i tt) a).
Qed.

(** The reading of [DSLP] at a proposition factors it out as a disjunct. *)
Lemma getDSLP_msingleton {A} (m : DSLP A) p a :
  getDSLP m p a <-> p \/ getDSLP m False a.
Proof.
  rewrite !getDSLP_rel. split.
  - intro H. destruct (classic (dslpRel m tt a)) as [Hr | Hn];
      [ left; exact (H Hr) | right; exact Hn ].
  - intros [Hp | Hn] Hr; [ exact Hp | destruct (Hn Hr) ].
Qed.

Definition dslp_to_dslpsp {A} (m : DSLP A) : DSLPSP A :=
  exist _ (getDSLP m) (getDSLP_msingleton m).

Lemma get_dslpsp_to_dslp {A} (w : DSLPSP A) P a :
  getDSLPArr (dslpsp_to_dslp w) P a <-> getDSLPSP w (P tt) a.
Proof. reflexivity. Qed.

Lemma get_dslp_to_dslpsp {A} (m : DSLP A) p a :
  getDSLPSP (dslp_to_dslpsp m) p a <-> getDSLP m p a.
Proof. reflexivity. Qed.

(** The two maps are mutually inverse. *)

Lemma dslpsp_to_dslp_to_dslpsp {A} (w : DSLPSP A) :
  @eq1 DSLPSP Eq1_DSLPSP A (dslp_to_dslpsp (dslpsp_to_dslp w)) w.
Proof. intros p a. reflexivity. Qed.

Lemma dslp_to_dslpsp_to_dslp {A} (m : DSLP A) :
  @eq1 DSLP Eq1_DSLP A (dslpsp_to_dslp (dslp_to_dslpsp m)) m.
Proof.
  intros P a. apply (getDSLPArr_ext_iff m (fun _ => P tt) P a).
  intros []. reflexivity.
Qed.

(** Both preserve [ret] and [bind]. *)

Theorem dslp_to_dslpsp_morphism :
  @MonadMorphism DSLP DSLPSP Monad_DSLP Monad_DSLPSP Eq1_DSLP Eq1_DSLPSP
    (fun A => @dslp_to_dslpsp A).
Proof.
  constructor.
  - intros A x y H p a. exact (H (fun _ => p) a).
  - intros A x p a. etransitivity; [ exact (getDSLP_ret x p a) |].
    split; intros H E; apply H; symmetry; exact E.
  - intros A B m k p b. etransitivity; [ exact (getDSLP_bind m k p b) |].
    split; intros H a.
    + exact (proj2 (getDSLP_rel (k a) _ b) (H a)).
    + exact (proj1 (getDSLP_rel (k a) _ b) (H a)).
Qed.

Theorem dslpsp_to_dslp_morphism :
  @MonadMorphism DSLPSP DSLP Monad_DSLPSP Monad_DSLP Eq1_DSLPSP Eq1_DSLP
    (fun A => @dslpsp_to_dslp A).
Proof.
  constructor.
  - intros A x y H P a. exact (H (P tt) a).
  - intros A x. apply (proj2 (eq1_DSLP_get _ _)). intros p a.
    etransitivity; [| symmetry; exact (getDSLP_ret x p a) ].
    split; intros H E; apply H; symmetry; exact E.
  - intros A B w k. apply (proj2 (eq1_DSLP_get _ _)). intros p b.
    etransitivity;
      [| symmetry;
         exact (getDSLP_bind (dslpsp_to_dslp w) (fun a => dslpsp_to_dslp (k a)) p b) ].
    split; intros H a.
    + exact (proj1 (getDSLP_rel (dslpsp_to_dslp (k a)) (getDSLPSP w p a) b) (H a)).
    + exact (proj2 (getDSLP_rel (dslpsp_to_dslp (k a)) (getDSLPSP w p a) b) (H a)).
Qed.

(** Both preserve and reflect the order. *)

Lemma ordDSLPSP_dslpsp_to_dslp {A} (w w' : DSLPSP A) :
  ordDSLPSP w w' <-> ordDSLP (dslpsp_to_dslp w) (dslpsp_to_dslp w').
Proof.
  split.
  - intros H P a. exact (H (P tt) a).
  - intros H p a. exact (H (fun _ => p) a).
Qed.

Lemma ordDSLP_dslp_to_dslpsp {A} (m m' : DSLP A) :
  ordDSLP m m' <-> ordDSLPSP (dslp_to_dslpsp m) (dslp_to_dslpsp m').
Proof. exact (ordDSLP_get m m'). Qed.

(** So [DSLPSP] is a specification monad, by [DSLP]'s proof. *)

Theorem OrderedMonad_DSLPSP :
  @OrderedMonad DSLPSP Monad_DSLPSP Eq1_DSLPSP (@ordDSLPSP).
Proof.
  refine (OrderedMonad_iff _ (@ordDSLPSP) _
            (OrderedMonad_pullback (fun A => @dslpsp_to_dslp A) (@ordDSLP)
               dslpsp_to_dslp_morphism OrderedMonad_DSLP)).
  intros A x y. symmetry. exact (ordDSLPSP_dslpsp_to_dslp x y).
Qed.

(** ** Demonic carrier and operations

    The dual retains monotonicity and reverses the codomain implication:
    [p -> w p a], rather than [w p a -> p]. Its [bind] quantifies universally
    over intermediate results. *)
Module SPostDem.
  Definition SPost (A : Type) : Type := { w : SPPure A | Monotone w /\ CodomainDSLP w }.

  Definition app {A} (w : SPost A) : SPPure A := proj1_sig w.

  #[program] Definition retSP {A} (v : A) : SPost A := fun p a => a = v -> p.
  Next Obligation.
    split.
    - intros p q a Hpq H E. exact (Hpq (H E)).
    - intros p a Hp _. exact Hp.
  Qed.

  #[program] Definition bindSP {A B} (m : SPost A) (k : A -> SPost B) : SPost B :=
    fun p b => forall a, k a (m p a) b.
  Next Obligation.
    split.
    - intros p q b Hpq H a.
      exact (proj1 (proj2_sig (k a)) _ _ b
        (proj1 (proj2_sig m) p q a Hpq) (H a)).
    - intros p b Hp a.
      exact (proj2 (proj2_sig (k a)) _ b (proj2 (proj2_sig m) p a Hp)).
  Qed.

  (** ** Pointwise equality, monad laws, and refinement order

      Equality uses pointwise logical equivalence; refinement uses pointwise
      implication. The monad laws reuse the [DSLPSP] law package. *)

  #[global] Instance Monad_SPost : Monad SPost :=
    {| ret := @retSP; bind := @bindSP |}.

  #[global] Instance Eq1_SPost : Eq1 SPost :=
    fun A x y => forall p a, app x p a <-> app y p a.

  #[global] Instance Eq1Equivalence_SPost : @Eq1Equivalence SPost Monad_SPost Eq1_SPost.
  Proof.
    intro A. constructor.
    - intros x p a. reflexivity.
    - intros x y H p a. symmetry. exact (H p a).
    - intros x y z H K p a.
      transitivity (app y p a); [exact (H p a) | exact (K p a)].
  Qed.

  #[program] Definition to_dslpsp {A} (w : SPost A) : DSLPSP A := app w.
  Next Obligation.
    exact (proj1 (monotone_codomainDSLP_iff_msingleton _) (proj2_sig w)).
  Qed.

  #[program] Definition from_dslpsp {A} (w : DSLPSP A) : SPost A :=
    getDSLPSP w.
  Next Obligation.
    exact (proj2 (monotone_codomainDSLP_iff_msingleton _) (proj2_sig w)).
  Qed.

  #[global] Instance MonadLawsE_SPost : @MonadLawsE SPost Eq1_SPost Monad_SPost.
  Proof.
    destruct MonadLawsE_DSLPSP as [Ll Lr La Lp].
    constructor.
    - intros A B f x. exact (Ll A B (fun a => to_dslpsp (f a)) x).
    - intros A x. exact (Lr A (to_dslpsp x)).
    - intros A B C x f g.
      exact (La A B C (to_dslpsp x)
        (fun a => to_dslpsp (f a)) (fun b => to_dslpsp (g b))).
    - intros A B x y H f g K.
      exact (Lp A B (to_dslpsp x) (to_dslpsp y) H
        (fun a => to_dslpsp (f a)) (fun a => to_dslpsp (g a)) K).
  Qed.

  Definition le {A} (x y : SPost A) : Prop := forall p a, app x p a -> app y p a.

  #[global] Instance OrderedMonad_SPost : @OrderedMonad SPost Monad_SPost Eq1_SPost (@le).
  Proof.
    constructor.
    - intro A. constructor.
      + intros x p a H. exact H.
      + intros x y z H K p a V. exact (K p a (H p a V)).
    - intros A x y H p a. exact (proj1 (H p a)).
    - intros A B x y H f g K p b V a.
      apply (K a). exact (proj1 (proj2_sig (f a)) _ _ b (H p a) (V a)).
  Qed.

  Theorem to_dslpsp_morphism :
    @MonadMorphism SPost DSLPSP Monad_SPost Monad_DSLPSP
      Eq1_SPost Eq1_DSLPSP (fun A => @to_dslpsp A).
  Proof.
    constructor.
    - intros A x y H. exact H.
    - intros A x p a. reflexivity.
    - intros A B x k p b. reflexivity.
  Qed.

  Theorem from_dslpsp_morphism :
    @MonadMorphism DSLPSP SPost Monad_DSLPSP Monad_SPost
      Eq1_DSLPSP Eq1_SPost (fun A => @from_dslpsp A).
  Proof.
    constructor.
    - intros A x y H. exact H.
    - intros A x p a. reflexivity.
    - intros A B x k p b. reflexivity.
  Qed.
End SPostDem.

(** ** DSLP healthiness and ordered-monad equivalence at input [unit]

    The demonic transformers are monotone, preserve top, and preserve
    arbitrary nonempty meets. The maps through [DSLPSP] establish the
    equivalence with the arrow-derived [DSLP] monad. *)

Definition dm4all_dem_to_dslp {A} (w : SPostDem.SPost A) : DSLP A :=
  dslpsp_to_dslp (SPostDem.to_dslpsp w).

Definition dslp_to_dm4all_dem {A} (w : DSLP A) : SPostDem.SPost A :=
  SPostDem.from_dslpsp (dslp_to_dslpsp w).

Theorem dm4all_dem_healthiness {A} (w : SPostDem.SPost A) :
  sp_monotone (fun (P : unit -> Prop) a => SPostDem.app w (P tt) a) /\
  sp_terminating (fun (P : unit -> Prop) a => SPostDem.app w (P tt) a) /\
  sp_conjunctive (fun (P : unit -> Prop) a => SPostDem.app w (P tt) a).
Proof. exact (proj2_sig (dm4all_dem_to_dslp w)). Qed.

Lemma dm4all_dem_to_dslp_reading {A} (w : SPostDem.SPost A) P a :
  getDSLPArr (dm4all_dem_to_dslp w) P a <-> SPostDem.app w (P tt) a.
Proof. reflexivity. Qed.

Lemma dslp_to_dm4all_dem_reading {A} (w : DSLP A) p a :
  SPostDem.app (dslp_to_dm4all_dem w) p a <-> getDSLP w p a.
Proof. reflexivity. Qed.

Lemma dm4all_dem_round_trip {A} (w : SPostDem.SPost A) :
  @eq1 SPostDem.SPost SPostDem.Eq1_SPost A
    (dslp_to_dm4all_dem (dm4all_dem_to_dslp w)) w.
Proof. intros p a. reflexivity. Qed.

Lemma dslp_dm4all_dem_round_trip {A} (w : DSLP A) :
  @eq1 DSLP Eq1_DSLP A
    (dm4all_dem_to_dslp (dslp_to_dm4all_dem w)) w.
Proof. exact (dslp_to_dslpsp_to_dslp w). Qed.

Theorem dm4all_dem_to_dslp_morphism :
  @MonadMorphism SPostDem.SPost DSLP SPostDem.Monad_SPost Monad_DSLP
    SPostDem.Eq1_SPost Eq1_DSLP (fun A => @dm4all_dem_to_dslp A).
Proof.
  exact (@MonadMorphism_comp SPostDem.SPost DSLPSP DSLP
    SPostDem.Monad_SPost Monad_DSLPSP Monad_DSLP
    SPostDem.Eq1_SPost Eq1_DSLPSP Eq1_DSLP Eq1Equivalence_DSLP
    (fun A => @SPostDem.to_dslpsp A) (fun A => @dslpsp_to_dslp A)
    SPostDem.to_dslpsp_morphism dslpsp_to_dslp_morphism).
Qed.

Theorem dslp_to_dm4all_dem_morphism :
  @MonadMorphism DSLP SPostDem.SPost Monad_DSLP SPostDem.Monad_SPost
    Eq1_DSLP SPostDem.Eq1_SPost (fun A => @dslp_to_dm4all_dem A).
Proof.
  exact (@MonadMorphism_comp DSLP DSLPSP SPostDem.SPost
    Monad_DSLP Monad_DSLPSP SPostDem.Monad_SPost
    Eq1_DSLP Eq1_DSLPSP SPostDem.Eq1_SPost SPostDem.Eq1Equivalence_SPost
    (fun A => @dslp_to_dslpsp A) (fun A => @SPostDem.from_dslpsp A)
    dslp_to_dslpsp_morphism SPostDem.from_dslpsp_morphism).
Qed.

Lemma dm4all_dem_to_dslp_order {A} (w w' : SPostDem.SPost A) :
  SPostDem.le w w' <->
  ordDSLP (dm4all_dem_to_dslp w) (dm4all_dem_to_dslp w').
Proof.
  exact (ordDSLPSP_dslpsp_to_dslp
    (SPostDem.to_dslpsp w) (SPostDem.to_dslpsp w')).
Qed.

Lemma dslp_to_dm4all_dem_order {A} (w w' : DSLP A) :
  ordDSLP w w' <->
  SPostDem.le (dslp_to_dm4all_dem w) (dslp_to_dm4all_dem w').
Proof. exact (ordDSLP_get w w'). Qed.
