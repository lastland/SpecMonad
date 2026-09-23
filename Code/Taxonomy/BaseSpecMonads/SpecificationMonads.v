(** * Which base monads are specification monads

    Each monad of this directory is checked against DM4All's criterion
    ([Classes/OrderedMonad.v]) under the refinement order its own file
    defines.  The verdicts:

    | monad                       | order                  | ordered? |
    |-----------------------------|------------------------|----------|
    | [PredM.Pred]                | [Pred_le]              | yes      |
    | [PredStExc S]               | [ordPredStExc]         | yes      |
    | [PPM.PrePost]               | [PP_le]                | yes      |
    | [SPM.SPost]                 | [SP_le]                | yes      |
    | [WPure]                     | [WP_le]                | yes      |
    | [WSt S]                     | [ordWSt]               | yes      |
    | [WStExc S]                  | [ordWStExc]            | yes      |
    | [RPPM.RelPrePost]           | [MR_le]                | yes      |
    | [ASPSP] / [DSLPSP]          | [ordASPSP] / [ordDSLPSP] | yes    |
    | [ASPStExc S] / [DSLPStExc S] | [ordASPStExc] / [ordDSLPStExc] | yes |
    | [StASP.ASPSt S] / [StDSLP.DSLPSt S] | [ordASPSt] / [ordDSLPSt] | yes |
    | [ASPRd R] / [DSLPRd R]      | [ordASPRd] / [ordDSLPRd] | yes    |
    | [DSPSP] / [ASLPSP]          | [ordDSPSP] / [ordASLPSP] | yes    |
    | [DSPRd R] / [ASLPRd R]      | [ordDSPRd] / [ordASLPRd] | yes    |
    | [DSPStExc S] / [ASLPStExc S] | [ordDSPStExc] / [ordASLPStExc] | NO |
    | [StDSP.DSPSt S] / [StASLP.ASLPSt S] | [ordDSPSt] / [ordASLPSt] | NO |

    [ordPredStExc] ([PredMonad.v]) is the pointwise lift of [Pred_le]; it runs
    FORWARD (more outcomes is bigger), where [ordWSt] / [ordWStExc] are the
    lifts of [WP_le] and so run backward (a weaker precondition is bigger).

    The four failures are at [S = bool], and in the first argument of [bind]
    alone.  They are failures of the ORDER, not of the carrier: each of the
    four is an ordered monad under inclusion of the relation it denotes
    ([ordDSPStExcRel] &c.).  Pointwise implication is not that inclusion,
    because a DSP/ASLP assertion bounds the relation from both sides.  The
    pure and reader variants escape because at a [Prop] precondition DSP
    collapses onto ASP and ASLP onto DSLP. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From ExtLib Require Import Monad StateMonad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import PredMonad PrePostMonad SPostMonad WPureMonad RelPrePostMonad BaseGaloisConnections SPPredicateTransformers SPBindOrderCounterexample.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.

(* ================================================================= *)
(** ** The five DM4All monads                                        *)
(* ================================================================= *)

#[global] Instance OrderedMonad_Pred : OrderedMonad PredM.Pred (@Pred_le).
Proof.
  constructor.
  - intro A. exact Pred_le_PreOrder.
  - intros A x y H a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk b [a [Ha Hb]].
    exists a. split; [ exact (Hm a Ha) | exact (Hk a b Hb) ].
Qed.

#[global] Instance OrderedMonad_PrePost : OrderedMonad PPM.PrePost (@PP_le).
Proof.
  constructor.
  - intro A. exact PP_le_PreOrder.
  - intros A x y [Hp Hq].
    split; [ exact (proj2 Hp) | intro a; exact (proj1 (Hq a)) ].
  - intros A B m1 m2 [Hmp Hmq] k1 k2 Hk. split.
    + intros [H1 H2]. split; [ exact (Hmp H1) |].
      intros a Ha. exact (proj1 (Hk a) (H2 a (Hmq a Ha))).
    + intros b [a [Ha Hb]].
      exists a. split; [ exact (Hmq a Ha) | exact (proj2 (Hk a) b Hb) ].
Qed.

#[global] Instance OrderedMonad_SPost : OrderedMonad SPM.SPost (@SP_le).
Proof.
  constructor.
  - intro A. exact SP_le_PreOrder.
  - intros A x y H p a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk p b [a H]. exists a.
    apply (Hk a). exact (SPM.app_mono (k1 a) _ _ b (Hm p a) H).
Qed.

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

#[global] Instance OrderedMonad_RelPrePost
  : OrderedMonad RPPM.RelPrePost (@MR_le).
Proof.
  constructor.
  - intro A. exact MR_le_PreOrder.
  - intros A x y H p post Hy. exact (proj2 (H p post) Hy).
  - intros A B m1 m2 Hm f1 f2 Hf p post H.
    apply (RPPM.runRPP_mono m1 p p
             (fun a => RPPM.runRPP (f1 a) p post)
             (fun a => RPPM.runRPP (f2 a) p post) (fun h => h)).
    + intros a Ha. exact (Hf a p post Ha).
    + exact (Hm p _ H).
Qed.

(* ================================================================= *)
(** ** Their stacks                                                  *)
(* ================================================================= *)

Theorem OrderedMonad_PredStExc S :
  @OrderedMonad (PredStExc S) (Monad__PredStExc S) (Eq1__PredStExc S)
    (fun A => @ordPredStExc S A).
Proof.
  refine (OrderedMonad_iff (le_stateT (le_optionT (@Pred_le))) _ _
            (OrderedMonad_stateT _ (OrderedMonad_optionT _ OrderedMonad_Pred))).
  intros A x y. split; intro H; exact H.
Qed.

Theorem OrderedMonad_WSt S :
  @OrderedMonad (WSt S) (Monad__WSt S) (Eq1__WSt S) (fun A => @ordWSt S A).
Proof. exact (OrderedMonad_stateT _ OrderedMonad_WPure). Qed.

Theorem OrderedMonad_WStExc S :
  @OrderedMonad (WStExc S) (Monad__WStExc S) (Eq1__WStExc S)
    (fun A => @ordWStExc S A).
Proof.
  exact (OrderedMonad_stateT _ (OrderedMonad_optionT _ OrderedMonad_WPure)).
Qed.

Theorem OrderedMonad_WRd R :
  @OrderedMonad (WRd R) (Monad__WRd R) (Eq1__WRd R) (fun A => @ordWRd R A).
Proof. exact (OrderedMonad_readerT _ OrderedMonad_WPure). Qed.

(* ================================================================= *)
(** ** ASP and DSLP: every variant                                   *)
(* ================================================================= *)

#[global] Instance OrderedMonad_ASPSP : OrderedMonad ASPSP (@ordASPSP).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p a H; exact H | intros x y z H1 H2 p a H; exact (H2 p a (H1 p a H)) ].
  - intros A x y H p a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk p b [a H]. exists a.
    apply (Hk a). apply getASP_merge.
    destruct (getASP_split (k1 a) _ b H) as [Hm1 HT].
    split; [ exact (Hm p a Hm1) | exact HT ].
Qed.

#[global] Instance OrderedMonad_DSLPSP : OrderedMonad DSLPSP (@ordDSLPSP).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p a H; exact H | intros x y z H1 H2 p a H; exact (H2 p a (H1 p a H)) ].
  - intros A x y H p a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk p b H a.
    apply (Hk a). exact (getMSP_mono (k1 a) _ _ b (Hm p a) (H a)).
Qed.

Theorem OrderedMonad_ASPStExc S :
  @OrderedMonad (ASPStExc S) (Monad__ASPStExc S) (Eq1__ASPStExc S)
    (fun A => @ordASPStExc S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p r H; exact H | intros x y z H1 H2 p r H; exact (H2 p r (H1 p r H)) ].
  - intros A x y H p r. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk pre r [[a H] | [Hr Hn]].
    + left. exists a. apply (Hk a).
      apply (aspMono S (k1 a) (fun s0 => getASPStExc m1 pre (Some (a, s0)))); [| exact H ].
      intros s0 H0. exact (Hm pre _ H0).
    + right. split; [ exact Hr | exact (Hm pre None Hn) ].
Qed.

Theorem OrderedMonad_DSLPStExc S :
  @OrderedMonad (DSLPStExc S) (Monad__DSLPStExc S) (Eq1__DSLPStExc S)
    (fun A => @ordDSLPStExc S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p r H; exact H | intros x y z H1 H2 p r H; exact (H2 p r (H1 p r H)) ].
  - intros A x y H p r. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk pre r [H Hn]. split.
    + intro a. apply (Hk a).
      apply (dslpMono S (k1 a) (fun s0 => getDSLPStExc m1 pre (Some (a, s0)))); [| exact (H a) ].
      intros s0 H0. exact (Hm pre _ H0).
    + intro Hr. exact (Hm pre None (Hn Hr)).
Qed.

Theorem OrderedMonad_ASPSt S :
  @OrderedMonad (StASP.ASPSt S) (StASP.Monad__ASPSt S) (StASP.Eq1__ASPSt S)
    (fun A => @StASP.ordASPSt S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p r H; exact H | intros x y z H1 H2 p r H; exact (H2 p r (H1 p r H)) ].
  - intros A x y H p r. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk pre r [a H]. exists a. apply (Hk a).
    apply (StASP.aspMono S (k1 a) (fun s0 => StASP.getASPSt m1 pre (a, s0))); [| exact H ].
    intros s0 H0. exact (Hm pre _ H0).
Qed.

Theorem OrderedMonad_DSLPSt S :
  @OrderedMonad (StDSLP.DSLPSt S) (StDSLP.Monad__DSLPSt S) (StDSLP.Eq1__DSLPSt S)
    (fun A => @StDSLP.ordDSLPSt S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p r H; exact H | intros x y z H1 H2 p r H; exact (H2 p r (H1 p r H)) ].
  - intros A x y H p r. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk pre r H a. apply (Hk a).
    apply (StDSLP.dslpMono S (k1 a) (fun s0 => StDSLP.getDSLPSt m1 pre (a, s0))); [| exact (H a) ].
    intros s0 H0. exact (Hm pre _ H0).
Qed.

Theorem OrderedMonad_ASPRd R :
  @OrderedMonad (ASPRd R) (Monad__ASPRd R) (Eq1__ASPRd R) (fun A => @ordASPRd R A).
Proof.
  refine (OrderedMonad_iff (le_readerT (@ordASPSP)) _ _
            (OrderedMonad_readerT _ OrderedMonad_ASPSP)).
  intros A x y. split; intro H; exact H.
Qed.

Theorem OrderedMonad_DSLPRd R :
  @OrderedMonad (DSLPRd R) (Monad__DSLPRd R) (Eq1__DSLPRd R) (fun A => @ordDSLPRd R A).
Proof.
  refine (OrderedMonad_iff (le_readerT (@ordDSLPSP)) _ _
            (OrderedMonad_readerT _ OrderedMonad_DSLPSP)).
  intros A x y. split; intro H; exact H.
Qed.

(* ================================================================= *)
(** ** DSP and ASLP without state: inherited from ASP and DSLP       *)
(* ================================================================= *)

#[global] Instance OrderedMonad_DSPSP : OrderedMonad DSPSP (@ordDSPSP).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p a H; exact H | intros x y z H1 H2 p a H; exact (H2 p a (H1 p a H)) ].
  - intros A x y H p a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk.
    exact (@om_bind _ _ _ _ OrderedMonad_ASPSP A B
             (dsp_to_asp m1) (dsp_to_asp m2) Hm
             (fun a => dsp_to_asp (k1 a)) (fun a => dsp_to_asp (k2 a)) Hk).
Qed.

#[global] Instance OrderedMonad_ASLPSP : OrderedMonad ASLPSP (@ordASLPSP).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x p a H; exact H | intros x y z H1 H2 p a H; exact (H2 p a (H1 p a H)) ].
  - intros A x y H p a. apply H.
  - intros A B m1 m2 Hm k1 k2 Hk.
    exact (@om_bind _ _ _ _ OrderedMonad_DSLPSP A B
             (aslp_to_dslp m1) (aslp_to_dslp m2) Hm
             (fun a => aslp_to_dslp (k1 a)) (fun a => aslp_to_dslp (k2 a)) Hk).
Qed.

Theorem OrderedMonad_DSPRd R :
  @OrderedMonad (DSPRd R) (Monad__DSPRd R) (Eq1__DSPRd R) (fun A => @ordDSPRd R A).
Proof.
  refine (OrderedMonad_iff (le_readerT (@ordDSPSP)) _ _
            (OrderedMonad_readerT _ OrderedMonad_DSPSP)).
  intros A x y. split; intro H; exact H.
Qed.

Theorem OrderedMonad_ASLPRd R :
  @OrderedMonad (ASLPRd R) (Monad__ASLPRd R) (Eq1__ASLPRd R) (fun A => @ordASLPRd R A).
Proof.
  refine (OrderedMonad_iff (le_readerT (@ordASLPSP)) _ _
            (OrderedMonad_readerT _ OrderedMonad_ASLPSP)).
  intros A x y. split; intro H; exact H.
Qed.

(* ================================================================= *)
(** ** DSP and ASLP with state: not ordered under their own orders   *)
(* ================================================================= *)

Theorem not_OrderedMonad_DSPSt :
  ~ @OrderedMonad (StDSP.DSPSt bool) (StDSP.Monad__DSPSt bool) (StDSP.Eq1__DSPSt bool)
      (fun A => @StDSP.ordDSPSt bool A).
Proof.
  intros [Hpre _ Hbind]. apply SPBindOrderCounterexample.dsp_bind_not_monotone.
  intros m0 m1 k Hle. apply (Hbind _ _ m0 m1 Hle k k).
  intro a. apply (Hpre unit).
Qed.

Theorem not_OrderedMonad_ASLPSt :
  ~ @OrderedMonad (StASLP.ASLPSt bool) (StASLP.Monad__ASLPSt bool) (StASLP.Eq1__ASLPSt bool)
      (fun A => @StASLP.ordASLPSt bool A).
Proof.
  intros [Hpre _ Hbind]. apply SPBindOrderCounterexample.aslp_bind_not_monotone.
  intros m0 m1 k Hle. apply (Hbind _ _ m0 m1 Hle k k).
  intro a. apply (Hpre unit).
Qed.

(** The same witnesses as [SPBindOrderCounterexample], with the terminating
    outcome [(tt, s)] read as [Some (tt, s)]. *)

Module StExcBindOrderCounterexample.

  Local Obligation Tactic := idtac.

  #[program] Definition dspOf {A} (R : bool -> option (A * bool) -> Prop)
    : DSPStExc bool A :=
    fun p r => (exists s, p s /\ R s r) /\ (forall s, R s r -> p s).
  Next Obligation. intros A R. exact (dsp_shape_wf bool R). Qed.

  #[program] Definition aslpOf {A} (R : bool -> option (A * bool) -> Prop)
    : ASLPStExc bool A :=
    fun p r => (exists s, p s /\ R s r) \/ (forall s, R s r -> p s).
  Next Obligation. intros A R. exact (aslp_shape_wf bool R). Qed.

  Definition R0 (s : bool) (r : option (unit * bool)) :=
    s = false /\ r = Some (tt, false).

  Definition R1 (s : bool) (r : option (unit * bool)) :=
    r = Some (tt, s).

  Definition K (_ : unit) (_ : bool) (r : option (unit * bool)) :=
    r = Some (tt, false).

  Theorem not_OrderedMonad_DSPStExc :
    ~ @OrderedMonad (DSPStExc bool) (Monad__DSPStExc bool) (Eq1__DSPStExc bool)
        (fun A => @ordDSPStExc bool A).
  Proof.
    apply (not_OrderedMonad _ (dspOf R0) (dspOf R1) (fun a => dspOf (K a))).
    - intros a pre r H. exact H.
    - intros p r [[s [Hp [Hs Hr]]] Hall]. subst s r. split.
      + exists false. split; [ exact Hp | reflexivity ].
      + intros t H. injection H as <-. exact Hp.
    - intro H.
      assert (HL : getDSPStExc (bindDSPStExc (dspOf R0) (fun a => dspOf (K a)))
                     (fun s => s = false) (Some (tt, false))).
      { apply (bindDSPProg_dsp bool). split.
        - exists false. split; [ reflexivity |].
          exists (Some (tt, false)). split.
          + exact (proj2 (dsp_recov bool R0 false _) (conj eq_refl eq_refl)).
          + exact (proj2 (dsp_recov bool (K tt) false _) eq_refl).
        - intros s [o [Ho Hk]].
          exact (proj1 (proj1 (dsp_recov bool R0 s o) Ho)). }
      destruct (proj1 (bindDSPProg_dsp bool _ _ _ _) (H _ _ HL)) as [_ Hall].
      assert (E : true = false).
      { apply Hall. exists (Some (tt, true)). split.
        - exact (proj2 (dsp_recov bool R1 true _) eq_refl).
        - exact (proj2 (dsp_recov bool (K tt) true _) eq_refl). }
      discriminate E.
  Qed.

  Theorem not_OrderedMonad_ASLPStExc :
    ~ @OrderedMonad (ASLPStExc bool) (Monad__ASLPStExc bool) (Eq1__ASLPStExc bool)
        (fun A => @ordASLPStExc bool A).
  Proof.
    apply (not_OrderedMonad _ (aslpOf R1) (aslpOf R0) (fun a => aslpOf (K a))).
    - intros a pre r H. exact H.
    - intros p r [[s [Hp Hr]] | Hall].
      + unfold R1 in Hr. subst r. destruct s.
        * right. intros t [_ Hr]. discriminate Hr.
        * left. exists false. split; [ exact Hp | split; reflexivity ].
      + right. intros t [Ht Hr]. subst t r. apply (Hall false). reflexivity.
    - intro H.
      assert (HL : getASLPStExc (bindASLPStExc (aslpOf R1) (fun a => aslpOf (K a)))
                     (fun s => s = true) (Some (tt, false))).
      { apply (bindASLPProg_aslp bool). left.
        exists true. split; [ reflexivity |].
        exists (Some (tt, true)). split.
        - exact (proj2 (aslp_recov bool R1 true _) eq_refl).
        - exact (proj2 (aslp_recov bool (K tt) true _) eq_refl). }
      destruct (proj1 (bindASLPProg_aslp bool _ _ _ _) (H _ _ HL))
        as [[s [Hp [o [Ho _]]]] | Hall].
      + destruct (proj1 (aslp_recov bool R0 s o) Ho) as [Hs _]. congruence.
      + assert (E : false = true).
        { apply Hall. exists (Some (tt, false)). split.
          - exact (proj2 (aslp_recov bool R0 false _) (conj eq_refl eq_refl)).
          - exact (proj2 (aslp_recov bool (K tt) false _) eq_refl). }
        discriminate E.
  Qed.

End StExcBindOrderCounterexample.

(* ================================================================= *)
(** ** ... but ordered under inclusion of the denoted relation        *)
(* ================================================================= *)

Theorem OrderedMonad_DSPStExcRel S :
  @OrderedMonad (DSPStExc S) (Monad__DSPStExc S) (Eq1__DSPStExc S)
    (fun A => @ordDSPStExcRel S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x s r H; exact H | intros x y z H1 H2 s r H; exact (H2 s r (H1 s r H)) ].
  - intros A x y H s r [HT Hn].
    split; [ exact (proj1 (H _ r) HT) | intro Hy; exact (Hn (proj2 (H _ r) Hy)) ].
  - intros A B m1 m2 Hm k1 k2 Hk s r H.
    apply (proj2 (rec_bindDSPProg S m2 k2 s r)).
    destruct (proj1 (rec_bindDSPProg S m1 k1 s r) H) as [o [Ho Hko]].
    exists o. split; [ exact (Hm s o Ho) |].
    destruct o as [[a smid]|]; [ exact (Hk a smid r Hko) | exact Hko ].
Qed.

Theorem OrderedMonad_ASLPStExcRel S :
  @OrderedMonad (ASLPStExc S) (Monad__ASLPStExc S) (Eq1__ASLPStExc S)
    (fun A => @ordASLPStExcRel S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x s r H; exact H | intros x y z H1 H2 s r H; exact (H2 s r (H1 s r H)) ].
  - intros A x y H s r [Hn HT].
    split; [ intro Hy; exact (Hn (proj2 (H _ r) Hy)) | exact (proj1 (H _ r) HT) ].
  - intros A B m1 m2 Hm k1 k2 Hk s r H.
    apply (proj2 (rec_bindASLPProg S m2 k2 s r)).
    destruct (proj1 (rec_bindASLPProg S m1 k1 s r) H) as [o [Ho Hko]].
    exists o. split; [ exact (Hm s o Ho) |].
    destruct o as [[a smid]|]; [ exact (Hk a smid r Hko) | exact Hko ].
Qed.

Theorem OrderedMonad_DSPStRel S :
  @OrderedMonad (StDSP.DSPSt S) (StDSP.Monad__DSPSt S) (StDSP.Eq1__DSPSt S)
    (fun A => @StDSP.ordDSPStRel S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x s r H; exact H | intros x y z H1 H2 s r H; exact (H2 s r (H1 s r H)) ].
  - intros A x y H s r [HT Hn].
    split; [ exact (proj1 (H _ r) HT) | intro Hy; exact (Hn (proj2 (H _ r) Hy)) ].
  - intros A B m1 m2 Hm k1 k2 Hk s r H.
    apply (proj2 (StDSP.rec_bindDSPProg S m2 k2 s r)).
    destruct (proj1 (StDSP.rec_bindDSPProg S m1 k1 s r) H) as [a [smid [Ho Hko]]].
    exists a, smid. split; [ exact (Hm s _ Ho) | exact (Hk a smid r Hko) ].
Qed.

Theorem OrderedMonad_ASLPStRel S :
  @OrderedMonad (StASLP.ASLPSt S) (StASLP.Monad__ASLPSt S) (StASLP.Eq1__ASLPSt S)
    (fun A => @StASLP.ordASLPStRel S A).
Proof.
  constructor.
  - intro A. constructor;
      [ intros x s r H; exact H | intros x y z H1 H2 s r H; exact (H2 s r (H1 s r H)) ].
  - intros A x y H s r [Hn HT].
    split; [ intro Hy; exact (Hn (proj2 (H _ r) Hy)) | exact (proj1 (H _ r) HT) ].
  - intros A B m1 m2 Hm k1 k2 Hk s r H.
    apply (proj2 (StASLP.rec_bindASLPProg S m2 k2 s r)).
    destruct (proj1 (StASLP.rec_bindASLPProg S m1 k1 s r) H) as [a [smid [Ho Hko]]].
    exists a, smid. split; [ exact (Hm s _ Ho) | exact (Hk a smid r Hko) ].
Qed.
