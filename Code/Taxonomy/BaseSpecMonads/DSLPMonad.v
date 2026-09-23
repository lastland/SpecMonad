(** * The DSLP specification monads

    Three specification monads, all at input [unit]:

      [DSLP]        = [DSLPArr unit]                          (* SLP        *)
      [DSLPSt S]    = [stateArrT S DSLPArr unit]              (* SLP^St     *)
      [DSLPStExc S] = [stateArrT S (optionArrT DSLPArr) unit] (* SLP^StExc  *)

    Fixing the input at [unit] gives a SPECIFICATION MONAD in each case.
    The [MonadLawsE] instances are [MonadLawsE_Arrow] ([Arrows/SPostArr.v])
    at the arrow and at its two transformer stacks; [bind] monotonicity is
    proved from [dslpRel_incl], which runs backwards relative to ASP's.

    The arrow itself is in [DSLPArrowCore.v] and the relation it denotes in
    [DSLPArrowRel.v]; both are re-exported here, so a client still needs
    only [Require Import DSLPMonad]. *)

From Coq Require Import Morphisms RelationClasses Setoid Relation_Definitions.
From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Export DSLPArrowCore DSLPArrowRel.



(* ================================================================= *)
(** ** [DSLP = DSLPArr unit]: a specification monad                *)
(* ================================================================= *)

(** [ret_arrow] / [bind_arrow] ([SPostArr.v]) at input [unit], ordered by
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
    @MonadLawsE_Arrow DSLPArr _ _ _ _ _.

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
    @MonadLawsE_Arrow (stateArrT S DSLPArr) _ _ _ _ _.

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
    @MonadLawsE_Arrow (stateArrT S (optionArrT DSLPArr)) _ _ _ _ _.

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
