(** * [DWLPArr]: the arrow of demonic weakest-liberal-precondition
      transformers.

      [DWLPArr A B] = { w : WPArr A B | w monotone, terminating, conjunctive }

    The carrier refines [Arrows/WPArr.WPArr] by homomorphism properties, the
    weakest-precondition counterparts of [DSLPArr]'s; [dwlp_meet_iff] shows
    they are exactly meet preservation, the form the proofs below use.  The
    operations are those of [WPArr]; [arrow_eq] is pointwise logical
    equivalence, which the carrier makes a congruence.  This file is the
    arrow and its laws: [Arrow] / [ArrowApply] and their two law bundles.

    [GaloisTranspose.v] shows that [DWLPArr] is isomorphic to [ASPArr], each
    element being the right adjoint of exactly one ASP transformer. *)

From Coq Require Import Morphisms RelationClasses Setoid.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy.Arrows Require Import WPArr.

(* ================================================================= *)
(** ** [DWLPArr]                                                     *)
(* ================================================================= *)

Section DWLPArr.

  (** The relation a raw transformer denotes: [b] satisfies every
      postcondition the transformer guarantees from [a]. *)
  Definition dwlpRelT {A B} (w : WPArr A B) (a : A) (b : B) : Prop :=
    forall Q, w a Q -> Q b.

  Definition dwlp_meet {A B} (w : WPArr A B) : Prop :=
    forall a Q, w a Q <-> forall b, dwlpRelT w a b -> Q b.

  Lemma dwlp_meet_hom {A B} (w : WPArr A B) :
    dwlp_meet w -> wp_monotone w /\ wp_terminating w /\ wp_conjunctive w.
  Proof.
    intro H. split; [| split ].
    - intros a Q1 Q2 HQ Hw. apply H. intros b Hr. exact (HQ b (proj1 (H a Q1) Hw b Hr)).
    - intro a. apply H. intros b _. exact I.
    - intros I _ Q a. rewrite (H a). split.
      + intros Hall i. apply H. intros b Hr. exact (Hall b Hr i).
      + intros Hall b Hr i. exact (proj1 (H a _) (Hall i) b Hr).
  Qed.

  (** Backwards, [w] accepts from [a] the meet of every postcondition it
      accepts there, a family that top preservation makes nonempty, and
      that meet lies below [Q]. *)
  Lemma dwlp_hom_meet {A B} (w : WPArr A B) :
    wp_monotone w /\ wp_terminating w /\ wp_conjunctive w -> dwlp_meet w.
  Proof.
    intros [Hm [Ht Hc]] a Q. split.
    - intros Hw b Hr. exact (Hr Q Hw).
    - intro H.
      apply (Hm a (fun b => forall i : { Q' : B -> Prop | w a Q' }, proj1_sig i b)).
      + intros b Hb. apply H. intros Q' HQ'. exact (Hb (exist _ Q' HQ')).
      + exact (proj2 (Hc _ (inhabits (exist (fun Q' => w a Q') (fun _ => True) (Ht a)))
                       (fun i => proj1_sig i) a) (fun i => proj2_sig i)).
  Qed.

  Theorem dwlp_meet_iff {A B} (w : WPArr A B) :
    dwlp_meet w <-> wp_monotone w /\ wp_terminating w /\ wp_conjunctive w.
  Proof. split; [ apply dwlp_meet_hom | apply dwlp_hom_meet ]. Qed.

  Definition DWLPArr (A B : Type) : Type :=
    { w : WPArr A B | wp_monotone w /\ wp_terminating w /\ wp_conjunctive w }.

  Definition getDWLPArr {A B} (w : DWLPArr A B) : A -> (B -> Prop) -> Prop :=
    proj1_sig w.
  Coercion getDWLPArr : DWLPArr >-> Funclass.

  Lemma getDWLPArr_meet {A B} (w : DWLPArr A B) a Q :
    w a Q <-> forall b, dwlpRelT (getDWLPArr w) a b -> Q b.
  Proof. exact (dwlp_hom_meet _ (proj2_sig w) a Q). Qed.

  Definition mkDWLPArr {A B} (w : WPArr A B) (H : dwlp_meet w) : DWLPArr A B :=
    exist _ w (dwlp_meet_hom w H).

  Lemma getDWLPArr_mono {A B} (w : DWLPArr A B) a (Q1 Q2 : B -> Prop) :
    (forall b, Q1 b -> Q2 b) -> w a Q1 -> w a Q2.
  Proof. exact (proj1 (proj2_sig w) a Q1 Q2). Qed.

  Lemma getDWLPArr_ext_iff {A B} (w : DWLPArr A B) a (Q1 Q2 : B -> Prop) :
    (forall b, Q1 b <-> Q2 b) -> w a Q1 <-> w a Q2.
  Proof. intro H. split; apply getDWLPArr_mono; intro b; apply H. Qed.

  (** The arrow of a relation: its demonic weakest liberal precondition. *)
  #[program] Definition ofRelDWLPArr {A B} (R : A -> B -> Prop) : DWLPArr A B :=
    fun a Q => forall b, R a b -> Q b.
  Next Obligation.
    apply dwlp_meet_hom. intros a Q. split.
    - intros H b Hr. apply H. apply (Hr (R a)). intros b' Hr'. exact Hr'.
    - intros H b Hr. apply H. intros Q' HQ'. exact (HQ' b Hr).
  Qed.

  (** pure, comp, first, app *)

  #[program] Definition pureDWLP {A B} (h : A -> B) : DWLPArr A B :=
    fun a Q => Q (h a).
  Next Obligation.
    apply dwlp_meet_hom. intros a Q. split.
    - intros H b Hr. exact (Hr Q H).
    - intro H. apply H. intros Q' HQ'. exact HQ'.
  Qed.

  #[program] Definition compDWLP {A B C} (f : DWLPArr A B) (g : DWLPArr B C)
    : DWLPArr A C :=
    fun a Q => f a (fun b => g b Q).
  Next Obligation.
    apply dwlp_meet_hom. intros a Q. split.
    - intros H c Hr. exact (Hr Q H).
    - intro H. apply (getDWLPArr_meet f). intros b Hf.
      apply (getDWLPArr_meet g). intros c Hg.
      apply H. intros Q' HQ'. exact (Hg Q' (Hf _ HQ')).
  Qed.

  #[program] Definition firstDWLP {A B C} (f : DWLPArr A B)
    : DWLPArr (A * C) (B * C) :=
    fun ac Q => f (fst ac) (fun b => Q (b, snd ac)).
  Next Obligation.
    apply dwlp_meet_hom. intros [a c] Q. cbn [fst snd]. split.
    - intros H bc Hr. exact (Hr Q H).
    - intro H. apply (getDWLPArr_meet f). intros b Hf.
      apply H. intros Q' HQ'. exact (Hf _ HQ').
  Qed.

  #[program] Definition appDWLP {A B} : DWLPArr (DWLPArr A B * A) B :=
    fun fa Q => fst fa (snd fa) Q.
  Next Obligation.
    apply dwlp_meet_hom. intros [f a] Q. cbn [fst snd]. split.
    - intros H b Hr. exact (Hr Q H).
    - intro H. apply (getDWLPArr_meet f). intros b Hf.
      apply H. intros Q' HQ'. exact (Hf _ HQ').
  Qed.

  #[global] Instance Arrow_DWLPArr : Arrow DWLPArr :=
    {| arr_pure := @pureDWLP ; arr_comp := @compDWLP ; arr_first := @firstDWLP |}.

  #[global] Instance ArrowApply_DWLPArr : ArrowApply DWLPArr :=
    {| arr_app := @appDWLP |}.

  (** Pointwise logical equivalence of the underlying transformers. *)
  Definition DWLPArr_eq {A B} (f g : DWLPArr A B) : Prop :=
    forall a Q, f a Q <-> g a Q.

  #[global] Instance DWLPArr_eq_Equivalence {A B} : Equivalence (@DWLPArr_eq A B).
  Proof.
    constructor.
    - intros f a Q. reflexivity.
    - intros f g H a Q. symmetry. apply H.
    - intros f g h H1 H2 a Q. etransitivity; [ apply H1 | apply H2 ].
  Qed.

  #[global] Instance ArrowEq_DWLPArr : ArrowEq DWLPArr :=
    {| arrow_eq := @DWLPArr_eq |}.

End DWLPArr.

(* ================================================================= *)
(** ** Each operation, unfolded once                                 *)
(* ================================================================= *)

Section GetDWLP.
  Lemma getDWLP_pure {A B} (h : A -> B) :
    getDWLPArr (pureDWLP h) = fun a Q => Q (h a).
  Proof. reflexivity. Qed.
  Lemma getDWLP_comp {A B C} (f : DWLPArr A B) (g : DWLPArr B C) :
    getDWLPArr (compDWLP f g) = fun a Q => f a (fun b => g b Q).
  Proof. reflexivity. Qed.
  Lemma getDWLP_first {A B C} (f : DWLPArr A B) :
    getDWLPArr (@firstDWLP A B C f) = fun ac Q => f (fst ac) (fun b => Q (b, snd ac)).
  Proof. reflexivity. Qed.
  Lemma getDWLP_app {A B} :
    getDWLPArr (@appDWLP A B) = fun fa Q => fst fa (snd fa) Q.
  Proof. reflexivity. Qed.
End GetDWLP.

(* ================================================================= *)
(** ** Arrow laws                                                    *)
(* ================================================================= *)

Local Ltac dwlp_simpl :=
  cbn [arrow_eq ArrowEq_DWLPArr DWLPArr_eq arr_id arr_comp arr_pure arr_first
       arr_app Arrow_DWLPArr ArrowApply_DWLPArr];
  repeat rewrite ?getDWLP_comp, ?getDWLP_pure, ?getDWLP_first, ?getDWLP_app;
  cbv beta; cbn [fst snd].

Local Ltac dwlp_intro := cbn [arrow_eq ArrowEq_DWLPArr]; unfold DWLPArr_eq.

#[global] Instance ArrowLaws_DWLPArr : ArrowLaws DWLPArr.
Proof.
  constructor; intros; dwlp_intro.
  - (* comp_id_l *) intros a Q. dwlp_simpl. reflexivity.
  - (* comp_id_r *) intros a Q. dwlp_simpl. reflexivity.
  - (* comp_assoc *) intros a Q. dwlp_simpl. reflexivity.
  - (* pure_comp *) intros a Q. dwlp_simpl. reflexivity.
  - (* first_pure *) intros [a c] Q. dwlp_simpl. reflexivity.
  - (* first_comp *) intros [a d] Q. dwlp_simpl. reflexivity.
  - (* first_fst *) intros [a c] Q. dwlp_simpl. reflexivity.
  - (* first_assoc *) intros [[a c] d] Q. dwlp_simpl. reflexivity.
  - (* comp_proper *)
    intros f f' Hf g g' Hg a Q. dwlp_simpl.
    transitivity (f a (fun b => g' b Q)).
    + apply getDWLPArr_ext_iff. intro b. apply Hg.
    + apply Hf.
  - (* first_proper *)
    intros f f' Hf [a c] Q. dwlp_simpl. apply Hf.
Qed.

#[global] Instance ArrowApplyLaws_DWLPArr : ArrowApplyLaws DWLPArr.
Proof.
  constructor.
  - (* app_law *) intros A B f. dwlp_intro. intros a Q. dwlp_simpl. reflexivity.
  - (* app_pair *) intros A B. dwlp_intro. intros [a b] Q. dwlp_simpl. reflexivity.
  - (* app_post *) intros A B C h. dwlp_intro. intros [f a] Q. dwlp_simpl. reflexivity.
  - (* app_ext *)
    intros X A B u v t Huv. dwlp_intro. intros x Q. dwlp_simpl. apply Huv.
Qed.
