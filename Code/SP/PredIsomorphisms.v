(** * [SPost_ang] and [SPost_dem] are isomorphic to [Pred] (paper, Section 4.4)

    Without state, a healthy sp transformer is determined by one predicate
    on results, so both SP monads are isomorphic, as monads, to
    [PredM.Pred A = A -> Prop]:

      angelic   [R ↦ fun p a => p /\ R a]      [w ↦ fun a => w True a]
      demonic   [R ↦ fun p a => R a -> p]      [w ↦ fun a => ~ w False a]

    The angelic side is [SPM.SPost] (Maillard et al., ICFP 2019), healthy by
    [Singleton]; the demonic side is [SPostDem.SPost], healthy by
    [MSingleton].  Each isomorphism is proved at the directly defined monad
    ([ASPSP], [DSLPSP]) and composed with the existing morphisms to reach
    [SPM.SPost] and [SPostDem.SPost] ([pred_to_dm4all_morphism],
    [pred_to_dm4all_dem_morphism] and their inverses).  The angelic map
    preserves and reflects the order; the demonic one reverses it.  Only
    the demonic side is classical: its map into [Pred] reads [~ w False a]. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Relational Require Import PredMonad.
From Incorrectness.SP Require Import RawSP SPostMonad ASPMonad DSLPMonad.

Import PredM PredMFacts.

(* ================================================================= *)
(** ** Angelic: [Pred] and [ASPSP]                                    *)
(* ================================================================= *)

#[program] Definition pred_to_aspsp {A} (R : Pred A) : ASPSP A :=
  fun p a => p /\ R a.
Next Obligation. intros p a. tauto. Qed.

Definition aspsp_to_pred {A} (w : ASPSP A) : Pred A :=
  fun a => getASPSP w True a.

Lemma aspsp_to_pred_to_aspsp {A} (w : ASPSP A) :
  @eq1 ASPSP Eq1_ASPSP A (pred_to_aspsp (aspsp_to_pred w)) w.
Proof. intros p a. symmetry. exact (getASPSP_singleton w p a). Qed.

Lemma pred_to_aspsp_to_pred {A} (R : Pred A) :
  @eq1 Pred Eq1_Pred A (aspsp_to_pred (pred_to_aspsp R)) R.
Proof. intro a. cbn. tauto. Qed.

Theorem pred_to_aspsp_morphism :
  @MonadMorphism Pred ASPSP Monad_Pred Monad_ASPSP Eq1_Pred Eq1_ASPSP
    (fun A => @pred_to_aspsp A).
Proof.
  constructor.
  - intros A x y H p a. cbn. rewrite (H a). reflexivity.
  - intros A x p a. reflexivity.
  - intros A B m k p b. cbn. unfold bindPred. split.
    + intros [Hp [a [Hm Hk]]]. exists a. tauto.
    + intros [a [[Hp Hm] Hk]]. split; [ exact Hp | exists a; tauto ].
Qed.

Theorem aspsp_to_pred_morphism :
  @MonadMorphism ASPSP Pred Monad_ASPSP Monad_Pred Eq1_ASPSP Eq1_Pred
    (fun A => @aspsp_to_pred A).
Proof.
  constructor.
  - intros A x y H a. exact (H True a).
  - intros A x a. cbn. unfold retPred. tauto.
  - intros A B m k b. cbn. unfold aspsp_to_pred, bindPred. split.
    + intros [a H]. exists a. exact (getASPSP_split (k a) _ b H).
    + intros [a H]. exists a. exact (getASPSP_merge (k a) _ b H).
Qed.

Lemma pred_to_aspsp_order {A} (R R' : Pred A) :
  Pred_le R R' <-> ordASPSP (pred_to_aspsp R) (pred_to_aspsp R').
Proof.
  split.
  - intros H p a [Hp HR]. exact (conj Hp (H a HR)).
  - intros H a HR. exact (proj2 (H True a (conj I HR))).
Qed.

(* ================================================================= *)
(** ** Angelic: [Pred] and [SPost_ang] ([SPM.SPost])                  *)
(* ================================================================= *)

Definition pred_to_dm4all {A} (R : Pred A) : SPM.SPost A :=
  aspsp_to_dm4all (pred_to_aspsp R).

Definition dm4all_to_pred {A} (w : SPM.SPost A) : Pred A :=
  aspsp_to_pred (dm4all_to_aspsp w).

Theorem pred_to_dm4all_morphism :
  @MonadMorphism Pred SPM.SPost Monad_Pred SPM.Monad_SPost
    Eq1_Pred SPM.Eq1_SPost (fun A => @pred_to_dm4all A).
Proof.
  exact (@MonadMorphism_comp Pred ASPSP SPM.SPost
    Monad_Pred Monad_ASPSP SPM.Monad_SPost
    Eq1_Pred Eq1_ASPSP SPM.Eq1_SPost SPMFacts.Eq1Equivalence_SPost
    (fun A => @pred_to_aspsp A) (fun A => @aspsp_to_dm4all A)
    pred_to_aspsp_morphism aspsp_to_dm4all_morphism).
Qed.

Theorem dm4all_to_pred_morphism :
  @MonadMorphism SPM.SPost Pred SPM.Monad_SPost Monad_Pred
    SPM.Eq1_SPost Eq1_Pred (fun A => @dm4all_to_pred A).
Proof.
  exact (@MonadMorphism_comp SPM.SPost ASPSP Pred
    SPM.Monad_SPost Monad_ASPSP Monad_Pred
    SPM.Eq1_SPost Eq1_ASPSP Eq1_Pred Eq1Equivalence_Pred
    (fun A => @dm4all_to_aspsp A) (fun A => @aspsp_to_pred A)
    dm4all_to_aspsp_morphism aspsp_to_pred_morphism).
Qed.

Lemma dm4all_to_pred_to_dm4all {A} (w : SPM.SPost A) :
  @eq1 SPM.SPost SPM.Eq1_SPost A (pred_to_dm4all (dm4all_to_pred w)) w.
Proof. exact (aspsp_to_pred_to_aspsp (dm4all_to_aspsp w)). Qed.

Lemma pred_to_dm4all_to_pred {A} (R : Pred A) :
  @eq1 Pred Eq1_Pred A (dm4all_to_pred (pred_to_dm4all R)) R.
Proof. exact (pred_to_aspsp_to_pred R). Qed.

Lemma pred_to_dm4all_order {A} (R R' : Pred A) :
  Pred_le R R' <-> SP_le (pred_to_dm4all R) (pred_to_dm4all R').
Proof. exact (pred_to_aspsp_order R R'). Qed.

(* ================================================================= *)
(** ** Demonic: [Pred] and [DSLPSP]                                   *)
(* ================================================================= *)

#[program] Definition pred_to_dslpsp {A} (R : Pred A) : DSLPSP A :=
  fun p a => R a -> p.
Next Obligation.
  intros p a. split.
  - intro H. destruct (classic (R a)) as [HR | HnR];
      [ left; exact (H HR) | right; exact HnR ].
  - intros [Hp | Hn] HR; [ exact Hp | destruct (Hn HR) ].
Qed.

Definition dslpsp_to_pred {A} (w : DSLPSP A) : Pred A :=
  fun a => ~ getDSLPSP w False a.

Lemma dslpsp_to_pred_to_dslpsp {A} (w : DSLPSP A) :
  @eq1 DSLPSP Eq1_DSLPSP A (pred_to_dslpsp (dslpsp_to_pred w)) w.
Proof.
  intros p a. cbn. unfold dslpsp_to_pred. split.
  - intro H. apply getMSP_merge.
    destruct (classic (getDSLPSP w False a)) as [Hf | Hnf];
      [ right; exact Hf | left; exact (H Hnf) ].
  - intros H Hnf. destruct (getMSP_split w p a H) as [Hp | Hf];
      [ exact Hp | destruct (Hnf Hf) ].
Qed.

Lemma pred_to_dslpsp_to_pred {A} (R : Pred A) :
  @eq1 Pred Eq1_Pred A (dslpsp_to_pred (pred_to_dslpsp R)) R.
Proof. intro a. cbn. unfold dslpsp_to_pred. cbn. split; [ apply NNPP | tauto ]. Qed.

Theorem pred_to_dslpsp_morphism :
  @MonadMorphism Pred DSLPSP Monad_Pred Monad_DSLPSP Eq1_Pred Eq1_DSLPSP
    (fun A => @pred_to_dslpsp A).
Proof.
  constructor.
  - intros A x y H p a. cbn. rewrite (H a). reflexivity.
  - intros A x p a. reflexivity.
  - intros A B m k p b. cbn. unfold bindPred. split.
    + intros H a Hk Hm. exact (H (ex_intro _ a (conj Hm Hk))).
    + intros H [a [Hm Hk]]. exact (H a Hk Hm).
Qed.

Theorem dslpsp_to_pred_morphism :
  @MonadMorphism DSLPSP Pred Monad_DSLPSP Monad_Pred Eq1_DSLPSP Eq1_Pred
    (fun A => @dslpsp_to_pred A).
Proof.
  constructor.
  - intros A x y H a. unfold dslpsp_to_pred. rewrite (H False a). reflexivity.
  - intros A x a. cbn. unfold dslpsp_to_pred, retPred. cbn. split.
    + apply NNPP.
    + intros E H. exact (H E).
  - intros A B m k b. cbn. unfold dslpsp_to_pred, bindPred. cbn. split.
    + intro H. apply NNPP. intro Hno. apply H. intro a.
      apply getMSP_merge.
      destruct (classic (getDSLPSP m False a)) as [Hm | Hnm]; [ left; exact Hm |].
      destruct (classic (getDSLPSP (k a) False b)) as [Hk | Hnk]; [ right; exact Hk |].
      destruct (Hno (ex_intro _ a (conj Hnm Hnk))).
    + intros [a [Hnm Hnk]] H.
      destruct (getMSP_split (k a) _ b (H a)) as [Hm | Hk];
        [ exact (Hnm Hm) | exact (Hnk Hk) ].
Qed.

(** Refinement is reversed: a smaller set of results is a stronger
    demonic postcondition. *)

Lemma pred_to_dslpsp_order {A} (R R' : Pred A) :
  Pred_le R R' <-> ordDSLPSP (pred_to_dslpsp R') (pred_to_dslpsp R).
Proof.
  split.
  - intros H p a H' HR. exact (H' (H a HR)).
  - intros H a HR. exact (H (R' a) a (fun H' => H') HR).
Qed.

(* ================================================================= *)
(** ** Demonic: [Pred] and [SPost_dem] ([SPostDem.SPost])            *)
(* ================================================================= *)

Definition pred_to_dm4all_dem {A} (R : Pred A) : SPostDem.SPost A :=
  SPostDem.from_dslpsp (pred_to_dslpsp R).

Definition dm4all_dem_to_pred {A} (w : SPostDem.SPost A) : Pred A :=
  dslpsp_to_pred (SPostDem.to_dslpsp w).

Theorem pred_to_dm4all_dem_morphism :
  @MonadMorphism Pred SPostDem.SPost Monad_Pred SPostDem.Monad_SPost
    Eq1_Pred SPostDem.Eq1_SPost (fun A => @pred_to_dm4all_dem A).
Proof.
  exact (@MonadMorphism_comp Pred DSLPSP SPostDem.SPost
    Monad_Pred Monad_DSLPSP SPostDem.Monad_SPost
    Eq1_Pred Eq1_DSLPSP SPostDem.Eq1_SPost SPostDem.Eq1Equivalence_SPost
    (fun A => @pred_to_dslpsp A) (fun A => @SPostDem.from_dslpsp A)
    pred_to_dslpsp_morphism SPostDem.from_dslpsp_morphism).
Qed.

Theorem dm4all_dem_to_pred_morphism :
  @MonadMorphism SPostDem.SPost Pred SPostDem.Monad_SPost Monad_Pred
    SPostDem.Eq1_SPost Eq1_Pred (fun A => @dm4all_dem_to_pred A).
Proof.
  exact (@MonadMorphism_comp SPostDem.SPost DSLPSP Pred
    SPostDem.Monad_SPost Monad_DSLPSP Monad_Pred
    SPostDem.Eq1_SPost Eq1_DSLPSP Eq1_Pred Eq1Equivalence_Pred
    (fun A => @SPostDem.to_dslpsp A) (fun A => @dslpsp_to_pred A)
    SPostDem.to_dslpsp_morphism dslpsp_to_pred_morphism).
Qed.

Lemma dm4all_dem_to_pred_to_dm4all_dem {A} (w : SPostDem.SPost A) :
  @eq1 SPostDem.SPost SPostDem.Eq1_SPost A (pred_to_dm4all_dem (dm4all_dem_to_pred w)) w.
Proof. exact (dslpsp_to_pred_to_dslpsp (SPostDem.to_dslpsp w)). Qed.

Lemma pred_to_dm4all_dem_to_pred {A} (R : Pred A) :
  @eq1 Pred Eq1_Pred A (dm4all_dem_to_pred (pred_to_dm4all_dem R)) R.
Proof. exact (pred_to_dslpsp_to_pred R). Qed.

Lemma pred_to_dm4all_dem_order {A} (R R' : Pred A) :
  Pred_le R R' <-> SPostDem.le (pred_to_dm4all_dem R') (pred_to_dm4all_dem R).
Proof. exact (pred_to_dslpsp_order R R'). Qed.
