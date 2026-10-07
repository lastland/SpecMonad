(** * The ASP specification monads

    Three specification monads, all at input [unit]:

      [ASP]        = [ASPArr unit]                          (* SP        *)
      [ASPSt S]    = [stateArrT S ASPArr unit]              (* SP^St     *)
      [ASPStExc S] = [stateArrT S (optionArrT ASPArr) unit] (* SP^StExc  *)

    Fixing the input at [unit] gives a SPECIFICATION MONAD in each case: a
    monad ([MonadLawsE]) whose refinement order is a preorder for which
    [bind] is monotone in both arguments ([OrderedMonad],
    [Classes/OrderedMonad.v]).

    The [MonadLawsE] instances are [MonadLawsE_Arrow] ([Classes/ArrowMonad.v])
    at the arrow and at its two transformer stacks.  The orders are not
    generic -- [bind] monotonicity is proved below from [aspRel_incl].

    [Arrows/SPostArr.v] owns the binary carrier, operations, recovered-relation
    facts and laws. This module re-exports that infrastructure and fixes the
    input for unary specifications, runners and refinement orders. *)

From Coq Require Import Morphisms RelationClasses Setoid.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Classes Require Import ArrowMonad.
From Incorrectness.Taxonomy.Arrows Require Export SPostArr.
(* ================================================================= *)
(** ** [ASP = ASPArr unit]: a specification monad                *)
(* ================================================================= *)

(** [ret_arrow] / [bind_arrow] ([Classes/ArrowMonad.v]) at input [unit], ordered by
    pointwise implication. *)

Section ASP.

  Definition ASP (A : Type) : Type := ASPArr unit A.

  Definition retASP {A} (a : A) : ASP A := @ret_arrow ASPArr _ unit A a.

  Definition bindASP {A B} (m : ASP A) (k : A -> ASP B) : ASP B :=
    @bind_arrow ASPArr _ _ unit A B m k.

  #[global] Instance Monad_ASP : Monad ASP :=
    {| ret := @retASP ; bind := @bindASP |}.

  #[global] Instance Eq1_ASP : Eq1 ASP := fun A => @ASPArr_eq unit A.

  #[global] Instance Eq1Equivalence_ASP : @Eq1Equivalence ASP _ Eq1_ASP :=
    fun A => ASPArr_eq_Equivalence.

  (** The two operations, on relations. *)

  Lemma aspRel_retASP {A} (x : A) i a : aspRel (retASP x) i a <-> x = a.
  Proof. apply aspRel_pure. Qed.

  Lemma aspRel_bindASP {A B} (m : ASP A) (k : A -> ASP B) i b :
    aspRel (bindASP m k) i b <-> exists a, aspRel m i a /\ aspRel (k a) i b.
  Proof. apply aspRel_bind. Qed.

  #[global] Instance MonadLawsE_ASP : @MonadLawsE ASP Eq1_ASP _ :=
    @MonadLawsE_Arrow ASPArr _ _ _ _ _ unit.

  (** Refinement: FORWARD pointwise implication, as for the SP monads. *)
  Definition ordASP {A} (m1 m2 : ASP A) : Prop :=
    forall P a, getASPArr m1 P a -> getASPArr m2 P a.

  #[global] Instance ordASP_PreOrder {A} : PreOrder (@ordASP A).
  Proof.
    constructor.
    - intros m P a H. exact H.
    - intros m1 m2 m3 H1 H2 P a H. exact (H2 P a (H1 P a H)).
  Qed.

  #[global] Instance OrderedMonad_ASP : OrderedMonad ASP (@ordASP).
  Proof.
    constructor.
    - intro A. exact ordASP_PreOrder.
    - intros A m1 m2 H P a. unfold eq1, Eq1_ASP, ASPArr_eq in H. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk.
      pose proof (proj1 (aspRel_incl m1 m2) Hm) as Hm'.
      unfold ordASP.
      apply (proj2 (aspRel_incl (bindASP m1 k1) (bindASP m2 k2))).
      intros i b. rewrite !aspRel_bindASP.
      intros [a [H1 H2]]. exists a.
      split; [ apply Hm', H1 | apply (proj1 (aspRel_incl (k1 a) (k2 a)) (Hk a)), H2 ].
  Qed.

End ASP.

(* ================================================================= *)
(** ** [ASPSt S]: the state stack, again a specification monad   *)
(* ================================================================= *)

Section ASPSt.
  Variable S : Type.

  Definition ASPSt (A : Type) : Type := stateArrT S ASPArr unit A.

  Definition retASPSt {A} (a : A) : ASPSt A :=
    @ret_arrow (stateArrT S ASPArr) _ unit A a.

  Definition bindASPSt {A B} (m : ASPSt A) (k : A -> ASPSt B) : ASPSt B :=
    @bind_arrow (stateArrT S ASPArr) _ _ unit A B m k.

  #[global] Instance Monad_ASPSt : Monad ASPSt :=
    {| ret := @retASPSt ; bind := @bindASPSt |}.

  #[global] Instance Eq1_ASPSt : Eq1 ASPSt := fun A => @ASPArr_eq (unit * S) (A * S).

  #[global] Instance Eq1Equivalence_ASPSt : @Eq1Equivalence ASPSt _ Eq1_ASPSt :=
    fun A => ASPArr_eq_Equivalence.

  #[global] Instance MonadLawsE_ASPSt : @MonadLawsE ASPSt Eq1_ASPSt _ :=
    @MonadLawsE_Arrow (stateArrT S ASPArr) _ _ _ _ _ unit.

  Definition ordASPSt {A} (m1 m2 : ASPSt A) : Prop :=
    forall P r, getASPArr m1 P r -> getASPArr m2 P r.

  #[global] Instance ordASPSt_PreOrder {A} : PreOrder (@ordASPSt A).
  Proof.
    constructor.
    - intros m P r H. exact H.
    - intros m1 m2 m3 H1 H2 P r H. exact (H2 P r (H1 P r H)).
  Qed.

  #[global] Instance OrderedMonad_ASPSt : OrderedMonad ASPSt (@ordASPSt).
  Proof.
    constructor.
    - intro A. exact ordASPSt_PreOrder.
    - intros A m1 m2 H P r. unfold eq1, Eq1_ASPSt, ASPArr_eq in H. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk.
      pose proof (proj1 (aspRel_incl m1 m2) Hm) as Hm'.
      unfold ordASPSt.
      apply (proj2 (aspRel_incl (bindASPSt m1 k1) (bindASPSt m2 k2))).
      intros [[] s] r. unfold bindASPSt. rewrite !aspRelS_bind.
      intros [a [s' [H1 H2]]]. exists a, s'.
      split; [ apply Hm', H1 | apply (proj1 (aspRel_incl (k1 a) (k2 a)) (Hk a)), H2 ].
  Qed.

End ASPSt.

(* ================================================================= *)
(** ** [ASPStExc S]: the state-and-exception stack               *)
(* ================================================================= *)

Section ASPStExc.
  Variable S : Type.

  Definition ASPStExc (A : Type) : Type := stateArrT S (optionArrT ASPArr) unit A.

  Definition retASPStExc {A} (a : A) : ASPStExc A :=
    @ret_arrow (stateArrT S (optionArrT ASPArr)) _ unit A a.

  Definition bindASPStExc {A B} (m : ASPStExc A) (k : A -> ASPStExc B)
    : ASPStExc B :=
    @bind_arrow (stateArrT S (optionArrT ASPArr)) _ _ unit A B m k.

  #[global] Instance Monad_ASPStExc : Monad ASPStExc :=
    {| ret := @retASPStExc ; bind := @bindASPStExc |}.

  #[global] Instance Eq1_ASPStExc : Eq1 ASPStExc :=
    fun A => @ASPArr_eq (unit * S) (option (A * S)).

  #[global] Instance Eq1Equivalence_ASPStExc
    : @Eq1Equivalence ASPStExc _ Eq1_ASPStExc :=
    fun A => ASPArr_eq_Equivalence.

  #[global] Instance MonadLawsE_ASPStExc
    : @MonadLawsE ASPStExc Eq1_ASPStExc _ :=
    @MonadLawsE_Arrow (stateArrT S (optionArrT ASPArr)) _ _ _ _ _ unit.

  Definition ordASPStExc {A} (m1 m2 : ASPStExc A) : Prop :=
    forall P o, getASPArr m1 P o -> getASPArr m2 P o.

  #[global] Instance ordASPStExc_PreOrder {A} : PreOrder (@ordASPStExc A).
  Proof.
    constructor.
    - intros m P o H. exact H.
    - intros m1 m2 m3 H1 H2 P o H. exact (H2 P o (H1 P o H)).
  Qed.

  #[global] Instance OrderedMonad_ASPStExc
    : OrderedMonad ASPStExc (@ordASPStExc).
  Proof.
    constructor.
    - intro A. exact ordASPStExc_PreOrder.
    - intros A m1 m2 H P o. unfold eq1, Eq1_ASPStExc, ASPArr_eq in H. apply H.
    - intros A B m1 m2 Hm k1 k2 Hk.
      pose proof (proj1 (aspRel_incl m1 m2) Hm) as Hm'.
      unfold ordASPStExc.
      apply (proj2 (aspRel_incl (bindASPStExc m1 k1) (bindASPStExc m2 k2))).
      intros [[] s] o. unfold bindASPStExc. rewrite !aspRelE_bind.
      intros [o1 [H1 H2]]. exists o1. split; [ apply Hm', H1 |].
      destruct o1 as [[a s']|]; [ apply (proj1 (aspRel_incl (k1 a) (k2 a)) (Hk a)), H2 | exact H2 ].
  Qed.

End ASPStExc.

(* ================================================================= *)
(** ** Reading the three monads at a SHARED precondition             *)
(* ================================================================= *)

(** The arrows take a precondition on their whole input, [unit] or
    [unit * S]; the SP monads of this directory take one on [S] alone.  The
    two agree, since [unit] has one element, and this section provides the
    monad-shaped interface: a constructor from a relation, the reading
    [getASP*] at a shared precondition, and the facts join preservation
    supplies — singletons, congruence, monotonicity, strictness.  It is what
    a client of [ASPMonad.v] needs in order to use these monads instead. *)

Section Readings.

  Definition getASP {A} (w : ASP A) (p : Prop) (a : A) : Prop :=
    getASPArr w (fun _ => p) a.

  Definition aspOfPred {A} (Q : A -> Prop) : ASP A :=
    ofRelASPArr (fun _ => Q).

  Lemma getASP_of {A} (Q : A -> Prop) p a : getASP (aspOfPred Q) p a <-> p /\ Q a.
  Proof.
    unfold getASP, aspOfPred, ofRelASPArr. cbn. split.
    - intros [[] [Hp HQ]]. exact (conj Hp HQ).
    - intros [Hp HQ]. exists tt. exact (conj Hp HQ).
  Qed.

  Lemma getASP_singleton {A} (w : ASP A) p a : getASP w p a <-> p /\ getASP w True a.
  Proof.
    unfold getASP. rewrite !get_aspRel. split.
    - intros [[] [Hp Hr]]. split; [ exact Hp | exists tt; auto ].
    - intros [Hp [[] [_ Hr]]]. exists tt. auto.
  Qed.

  Lemma getASP_mono {A} (w : ASP A) (p q : Prop) a : (p -> q) -> getASP w p a -> getASP w q a.
  Proof.
    intros Hpq H. apply getASP_singleton in H.
    apply getASP_singleton. split; [ apply Hpq, (proj1 H) | exact (proj2 H) ].
  Qed.

  Lemma getASP_bot {A} (w : ASP A) a : ~ getASP w False a.
  Proof. intro H. exact (proj1 (proj1 (getASP_singleton w False a) H)). Qed.

  Lemma getASP_ret {A} (x : A) p a : getASP (retASP x) p a <-> p /\ x = a.
  Proof.
    unfold getASP. rewrite get_aspRel. split.
    - intros [[] [Hp Hr]]. apply aspRel_retASP in Hr. auto.
    - intros [Hp Hx]. exists tt. split; [ exact Hp | apply aspRel_retASP, Hx ].
  Qed.

  Lemma getASP_bind {A B} (m : ASP A) (k : A -> ASP B) p b :
    getASP (bindASP m k) p b <-> exists a, getASP m p a /\ getASP (k a) True b.
  Proof.
    unfold getASP in *. split.
    - intro H. apply (proj1 (get_aspRel _ _ _)) in H. destruct H as [[] [Hp H]].
      apply aspRel_bindASP in H. destruct H as [a [Hm Hk]].
      exists a. split; apply (proj2 (get_aspRel _ _ _)); exists tt; auto.
    - intros [a [Hm Hk]].
      apply (proj1 (get_aspRel _ _ _)) in Hm. destruct Hm as [[] [Hp Hm]].
      apply (proj1 (get_aspRel _ _ _)) in Hk. destruct Hk as [[] [_ Hk]].
      apply (proj2 (get_aspRel _ _ _)). exists tt. split; [ exact Hp |].
      apply aspRel_bindASP. exists a. auto.
  Qed.

  Lemma eq1_ASP_get {A} (m n : ASP A) :
    eq1 m n <-> (forall p a, getASP m p a <-> getASP n p a).
  Proof.
    split.
    - intros H p a. apply H.
    - intros H P a. unfold eq1, Eq1_ASP, ASPArr_eq.
      transitivity (getASP m (P tt) a); [ apply getASPArr_ext_iff; intros []; reflexivity |].
      rewrite H. apply getASPArr_ext_iff. intros []. reflexivity.
  Qed.

  Lemma ordASP_get {A} (m n : ASP A) :
    ordASP m n <-> (forall p a, getASP m p a -> getASP n p a).
  Proof.
    split.
    - intros H p a. apply H.
    - intros H P a HP.
      apply (getASPArr_ext n (fun _ => P tt) P a); [ intros []; reflexivity |].
      apply (H (P tt)). apply (getASPArr_ext m P (fun _ => P tt) a);
        [ intros []; reflexivity | exact HP ].
  Qed.

  (* ---- the state stack ---- *)

  Variable S : Type.

  Definition getASPSt {A} (w : ASPSt S A) (pre : S -> Prop) (r : A * S) : Prop :=
    getASPArr w (fun p => pre (snd p)) r.

  Definition aspOfRelSt {A} (R : S -> A * S -> Prop) : ASPSt S A :=
    ofRelASPArr (fun p r => R (snd p) r).

  Lemma getASPSt_of {A} (R : S -> A * S -> Prop) pre r :
    getASPSt (aspOfRelSt R) pre r <-> exists s, pre s /\ R s r.
  Proof.
    unfold getASPSt, aspOfRelSt, ofRelASPArr. cbn. split.
    - intros [[[] s] [Hp HR]]. exists s. exact (conj Hp HR).
    - intros [s [Hp HR]]. exists (tt, s). exact (conj Hp HR).
  Qed.

  Lemma getASPSt_singleton {A} (w : ASPSt S A) pre r :
    getASPSt w pre r <-> exists s0, pre s0 /\ getASPSt w (fun s => s = s0) r.
  Proof.
    unfold getASPSt. split.
    - intro H. apply (proj1 (get_aspRel _ _ _)) in H. destruct H as [[[] s0] [Hp Hr]].
      exists s0. split; [ exact Hp |]. apply (proj2 (get_aspRel _ _ _)).
      exists (tt, s0). cbn. auto.
    - intros [s0 [Hp H]]. apply (proj1 (get_aspRel _ _ _)) in H.
      destruct H as [[[] s] [Hs Hr]]. cbn in Hs. subst s.
      apply (proj2 (get_aspRel _ _ _)). exists (tt, s0). cbn. auto.
  Qed.

  Lemma getASPSt_cong {A} (w : ASPSt S A) (P Q : S -> Prop) r :
    (forall s, P s <-> Q s) -> (getASPSt w P r <-> getASPSt w Q r).
  Proof.
    intro H. unfold getASPSt. apply getASPArr_ext_iff. intros [[] s]. apply H.
  Qed.

  Lemma getASPSt_mono {A} (w : ASPSt S A) (P Q : S -> Prop) r :
    (forall s, P s -> Q s) -> getASPSt w P r -> getASPSt w Q r.
  Proof.
    intros H Hw. apply getASPSt_singleton in Hw. destruct Hw as [s0 [Hp Hr]].
    apply getASPSt_singleton. exists s0. split; [ apply H, Hp | exact Hr ].
  Qed.

  Lemma getASPSt_bot {A} (w : ASPSt S A) r : ~ getASPSt w (fun _ => False) r.
  Proof.
    intro H. apply getASPSt_singleton in H. destruct H as [s0 [[] _]].
  Qed.

  Lemma getASPSt_ret {A} (x : A) pre r :
    getASPSt (retASPSt S x) pre r <-> exists s, pre s /\ r = (x, s).
  Proof.
    unfold getASPSt. rewrite get_aspRel. split.
    - intros [[[] s] [Hp Hr]]. apply aspRelS_ret in Hr. exists s. auto.
    - intros [s [Hp ->]]. exists (tt, s). split; [ exact Hp | apply aspRelS_ret; reflexivity ].
  Qed.

  Lemma getASPSt_bind {A B} (m : ASPSt S A) (k : A -> ASPSt S B) pre r :
    getASPSt (bindASPSt S m k) pre r <->
    exists a s', getASPSt m pre (a, s') /\ getASPSt (k a) (fun t => t = s') r.
  Proof.
    unfold getASPSt in *. split.
    - intro H. apply (proj1 (get_aspRel _ _ _)) in H. destruct H as [[[] s] [Hp H]].
      apply aspRelS_bind in H. destruct H as [a [s' [Hm Hk]]].
      exists a, s'. split; apply (proj2 (get_aspRel _ _ _));
        [ exists (tt, s) | exists (tt, s') ]; cbn; auto.
    - intros [a [s' [Hm Hk]]].
      apply (proj1 (get_aspRel _ _ _)) in Hm. destruct Hm as [[[] s] [Hp Hm]].
      apply (proj1 (get_aspRel _ _ _)) in Hk. destruct Hk as [[[] s''] [Hs Hk]].
      cbn in Hs. subst s''. apply (proj2 (get_aspRel _ _ _)).
      exists (tt, s). split; [ exact Hp |]. apply aspRelS_bind. exists a, s'. auto.
  Qed.

  Lemma eq1_ASPSt_get {A} (m n : ASPSt S A) :
    eq1 m n <-> (forall pre r, getASPSt m pre r <-> getASPSt n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r. unfold eq1, Eq1_ASPSt, ASPArr_eq.
      transitivity (getASPSt m (fun s => P (tt, s)) r);
        [ apply getASPArr_ext_iff; intros [[] s]; reflexivity |].
      rewrite H. apply getASPArr_ext_iff. intros [[] s]. reflexivity.
  Qed.

  Definition ordASPStAt {A} (pre : S -> Prop) (m n : ASPSt S A) : Prop :=
    forall r, getASPSt m pre r -> getASPSt n pre r.

  Lemma ordASPSt_get {A} (m n : ASPSt S A) :
    ordASPSt S m n <-> (forall pre r, getASPSt m pre r -> getASPSt n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r HP.
      apply (getASPArr_ext n (fun p => P (tt, snd p)) P r);
        [ intros [[] s]; reflexivity |].
      apply (H (fun s => P (tt, s))). apply (getASPArr_ext m P (fun p => P (tt, snd p)) r);
        [ intros [[] s]; reflexivity | exact HP ].
  Qed.

  (* ---- the state-and-exception stack ---- *)

  Definition getASPStExc {A} (w : ASPStExc S A) (pre : S -> Prop) (r : option (A * S))
    : Prop := getASPArr w (fun p => pre (snd p)) r.

  Definition aspOfRelStExc {A} (R : S -> option (A * S) -> Prop) : ASPStExc S A :=
    ofRelASPArr (fun p r => R (snd p) r).

  Lemma getASPStExc_of {A} (R : S -> option (A * S) -> Prop) pre r :
    getASPStExc (aspOfRelStExc R) pre r <-> exists s, pre s /\ R s r.
  Proof.
    unfold getASPStExc, aspOfRelStExc, ofRelASPArr. cbn. split.
    - intros [[[] s] [Hp HR]]. exists s. exact (conj Hp HR).
    - intros [s [Hp HR]]. exists (tt, s). exact (conj Hp HR).
  Qed.

  Lemma getASPStExc_singleton {A} (w : ASPStExc S A) pre r :
    getASPStExc w pre r <-> exists s0, pre s0 /\ getASPStExc w (fun s => s = s0) r.
  Proof.
    unfold getASPStExc. split.
    - intro H. apply (proj1 (get_aspRel _ _ _)) in H. destruct H as [[[] s0] [Hp Hr]].
      exists s0. split; [ exact Hp |]. apply (proj2 (get_aspRel _ _ _)).
      exists (tt, s0). cbn. auto.
    - intros [s0 [Hp H]]. apply (proj1 (get_aspRel _ _ _)) in H.
      destruct H as [[[] s] [Hs Hr]]. cbn in Hs. subst s.
      apply (proj2 (get_aspRel _ _ _)). exists (tt, s0). cbn. auto.
  Qed.

  Lemma getASPStExc_cong {A} (w : ASPStExc S A) (P Q : S -> Prop) r :
    (forall s, P s <-> Q s) -> (getASPStExc w P r <-> getASPStExc w Q r).
  Proof.
    intro H. unfold getASPStExc. apply getASPArr_ext_iff. intros [[] s]. apply H.
  Qed.

  Lemma getASPStExc_mono {A} (w : ASPStExc S A) (P Q : S -> Prop) r :
    (forall s, P s -> Q s) -> getASPStExc w P r -> getASPStExc w Q r.
  Proof.
    intros H Hw. apply getASPStExc_singleton in Hw. destruct Hw as [s0 [Hp Hr]].
    apply getASPStExc_singleton. exists s0. split; [ apply H, Hp | exact Hr ].
  Qed.

  Lemma getASPStExc_bot {A} (w : ASPStExc S A) r : ~ getASPStExc w (fun _ => False) r.
  Proof.
    intro H. apply getASPStExc_singleton in H. destruct H as [s0 [[] _]].
  Qed.

  Lemma getASPStExc_ret {A} (x : A) pre r :
    getASPStExc (retASPStExc S x) pre r <-> exists s, pre s /\ r = Some (x, s).
  Proof.
    unfold getASPStExc. rewrite get_aspRel. split.
    - intros [[[] s] [Hp Hr]]. apply aspRelE_ret in Hr. exists s. auto.
    - intros [s [Hp ->]]. exists (tt, s).
      split; [ exact Hp | apply aspRelE_ret; reflexivity ].
  Qed.

  Lemma getASPStExc_bind {A B} (m : ASPStExc S A) (k : A -> ASPStExc S B) pre r :
    getASPStExc (bindASPStExc S m k) pre r <->
    (exists a s', getASPStExc m pre (Some (a, s')) /\
                  getASPStExc (k a) (fun t => t = s') r)
    \/ (r = None /\ getASPStExc m pre None).
  Proof.
    unfold getASPStExc in *. split.
    - intro H. apply (proj1 (get_aspRel _ _ _)) in H. destruct H as [[[] s] [Hp H]].
      apply aspRelE_bind in H. destruct H as [[[a s']|] [Hm Hk]].
      + left. exists a, s'. split; apply (proj2 (get_aspRel _ _ _));
          [ exists (tt, s) | exists (tt, s') ]; cbn; auto.
      + right. split; [ exact Hk |]. apply (proj2 (get_aspRel _ _ _)).
        exists (tt, s). cbn. auto.
    - intros [[a [s' [Hm Hk]]] | [-> Hm]].
      + apply (proj1 (get_aspRel _ _ _)) in Hm. destruct Hm as [[[] s] [Hp Hm]].
        apply (proj1 (get_aspRel _ _ _)) in Hk. destruct Hk as [[[] s''] [Hs Hk]].
        cbn in Hs. subst s''. apply (proj2 (get_aspRel _ _ _)).
        exists (tt, s). split; [ exact Hp |].
        apply aspRelE_bind. exists (Some (a, s')). auto.
      + apply (proj1 (get_aspRel _ _ _)) in Hm. destruct Hm as [[[] s] [Hp Hm]].
        apply (proj2 (get_aspRel _ _ _)). exists (tt, s). split; [ exact Hp |].
        apply aspRelE_bind. exists None. auto.
  Qed.

  Lemma eq1_ASPStExc_get {A} (m n : ASPStExc S A) :
    eq1 m n <-> (forall pre r, getASPStExc m pre r <-> getASPStExc n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r. unfold eq1, Eq1_ASPStExc, ASPArr_eq.
      transitivity (getASPStExc m (fun s => P (tt, s)) r);
        [ apply getASPArr_ext_iff; intros [[] s]; reflexivity |].
      rewrite H. apply getASPArr_ext_iff. intros [[] s]. reflexivity.
  Qed.

  Definition ordASPStExcAt {A} (pre : S -> Prop) (m n : ASPStExc S A) : Prop :=
    forall r, getASPStExc m pre r -> getASPStExc n pre r.

  Lemma ordASPStExc_get {A} (m n : ASPStExc S A) :
    ordASPStExc S m n <-> (forall pre r, getASPStExc m pre r -> getASPStExc n pre r).
  Proof.
    split.
    - intros H pre r. apply H.
    - intros H P r HP.
      apply (getASPArr_ext n (fun p => P (tt, snd p)) P r);
        [ intros [[] s]; reflexivity |].
      apply (H (fun s => P (tt, s))). apply (getASPArr_ext m P (fun p => P (tt, snd p)) r);
        [ intros [[] s]; reflexivity | exact HP ].
  Qed.

End Readings.

Arguments getASPSt {S} {A}.
Arguments getASPStExc {S} {A}.
Arguments aspOfRelSt {S} {A}.
Arguments aspOfRelStExc {S} {A}.
Arguments ordASPSt {S} {A}.
Arguments ordASPStExc {S} {A}.
Arguments ordASPStAt {S} {A}.
Arguments ordASPStExcAt {S} {A}.
Arguments retASPSt {S} {A}.
Arguments bindASPSt {S} {A} {B}.
Arguments retASPStExc {S} {A}.
Arguments bindASPStExc {S} {A} {B}.
