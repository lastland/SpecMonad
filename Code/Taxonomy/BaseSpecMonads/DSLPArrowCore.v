(** * [DSLPArr]: the arrow of demonic-liberal strongest-postcondition
      transformers.

      [DSLPArr A B] = { f : SPArrT A B | f monotone, terminating, conjunctive }

    The carrier refines [Arrows/SPArr.SPArrT] by homomorphism properties, the
    duals of [ASPArr]'s; [dslp_meet_iff] shows they are exactly meet
    preservation, the form the proofs below use.  This file is the arrow and
    its laws only: [Arrow] / [ArrowChoice] / [ArrowApply] and the three law
    bundles.

    The RELATION an arrow denotes lives in [DSLPArrowRel.v], and the
    specification monads built over it in [DSLPMonad.v]. *)

From Coq Require Import Morphisms RelationClasses Setoid Relation_Definitions.
From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import SPArr.

(* ================================================================= *)
(** ** [DSLPArr]                                                     *)
(* ================================================================= *)

Section DSLPArr.

  (** The relation a raw transformer denotes: [a] lies in every
      precondition the transformer accepts for [b]. *)
  Definition dslpRelT {A B} (f : SPArrT A B) (a : A) (b : B) : Prop :=
    forall P, f P b -> P a.

  Definition dslp_meet {A B} (f : SPArrT A B) : Prop :=
    forall P b, f P b <-> forall a, dslpRelT f a b -> P a.

  Lemma dslp_meet_hom {A B} (f : SPArrT A B) :
    dslp_meet f -> sp_monotone f /\ sp_terminating f /\ sp_conjunctive f.
  Proof.
    intro H. split; [| split ].
    - intros P Q HPQ b Hf. apply H. intros a Hr. exact (HPQ a (proj1 (H P b) Hf a Hr)).
    - intro b. apply (H _ b). intros a _. exact I.
    - intros I _ P b. rewrite (H _ b). split.
      + intros Hall i. apply (H _ b). intros a Hr. exact (Hall a Hr i).
      + intros Hall a Hr i. exact (proj1 (H _ b) (Hall i) a Hr).
  Qed.

  (** Backwards, [f] accepts at [b] the meet of every precondition it
      accepts there, a family that top preservation makes nonempty, and
      that meet lies below [P]. *)
  Lemma dslp_hom_meet {A B} (f : SPArrT A B) :
    sp_monotone f /\ sp_terminating f /\ sp_conjunctive f -> dslp_meet f.
  Proof.
    intros [Hm [Ht Hc]] P b. split.
    - intros Hf a Hr. exact (Hr P Hf).
    - intro H.
      apply (Hm (fun a => forall i : { Q : A -> Prop | f Q b }, proj1_sig i a)).
      + intros a Ha. apply H. intros Q HQ. exact (Ha (exist _ Q HQ)).
      + exact (proj2 (Hc _ (inhabits (exist (fun Q => f Q b) (fun _ => True) (Ht b)))
                       (fun i => proj1_sig i) b) (fun i => proj2_sig i)).
  Qed.

  Theorem dslp_meet_iff {A B} (f : SPArrT A B) :
    dslp_meet f <-> sp_monotone f /\ sp_terminating f /\ sp_conjunctive f.
  Proof. split; [ apply dslp_meet_hom | apply dslp_hom_meet ]. Qed.

  Definition DSLPArr (A B : Type) : Type :=
    { f : SPArrT A B | sp_monotone f /\ sp_terminating f /\ sp_conjunctive f }.

  Definition getDSLPArr {A B} (f : DSLPArr A B) : (A -> Prop) -> B -> Prop :=
    proj1_sig f.
  Coercion getDSLPArr : DSLPArr >-> Funclass.

  Lemma getDSLPArr_meet {A B} (f : DSLPArr A B) P b :
    f P b <-> forall a, dslpRelT (getDSLPArr f) a b -> P a.
  Proof. exact (dslp_hom_meet _ (proj2_sig f) P b). Qed.

  Definition mkDSLPArr {A B} (f : SPArrT A B) (H : dslp_meet f) : DSLPArr A B :=
    exist _ f (dslp_meet_hom f H).

  Lemma getDSLPArr_ext_iff {A B} (f : DSLPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b <-> f Q b.
  Proof.
    intro H. rewrite !(getDSLPArr_meet f _ b).
    split; intros HP a Hr; solve [ apply H, HP, Hr | apply H; apply HP, Hr ].
  Qed.

  Lemma getDSLPArr_ext {A B} (f : DSLPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b -> f Q b.
  Proof. intro H. apply (getDSLPArr_ext_iff f P Q b H). Qed.

  (** Every element is monotone in its precondition: a bigger [P] is
      accepted by more outcomes. *)
  Lemma getDSLPArr_mono {A B} (f : DSLPArr A B) (P Q : A -> Prop) b :
    (forall a, P a -> Q a) -> f P b -> f Q b.
  Proof. intro H. exact (proj1 (proj2_sig f) P Q H b). Qed.

  (** The arrow of a relation: its inverse image. *)
  #[program] Definition ofRelDSLPArr {A B} (R : A -> B -> Prop) : DSLPArr A B :=
    fun P b => forall a, R a b -> P a.
  Next Obligation.
    apply dslp_meet_hom. intros P b. split.
    - intros H a Hr. apply H. apply (Hr (fun x => R x b)). intros a' Hr'. exact Hr'.
    - intros H a Hr. apply H. intros Q HQ. exact (HQ a Hr).
  Qed.

  (** pure, comp, first, left, app *)

  #[program] Definition pureDSLP {A B} (h : A -> B) : DSLPArr A B :=
    fun P b => forall a, h a = b -> P a.
  Next Obligation.
    apply dslp_meet_hom. intros P b. split.
    - intros H a Hr. apply H. apply (Hr (fun x => h x = b)). intros a' Hr'. exact Hr'.
    - intros H a Hr. apply H. intros Q HQ. exact (HQ a Hr).
  Qed.

  #[program] Definition compDSLP {A B C} (f : DSLPArr A B) (g : DSLPArr B C)
    : DSLPArr A C :=
    fun P c => g (f P) c.
  Next Obligation.
    apply dslp_meet_hom. intros P c. split.
    - intros H a Hr. exact (Hr P H).
    - intros H.
      (* peel [g], then [f], and feed each [a] back through [H] *)
      apply (getDSLPArr_meet g (f P) c). intros b Hg.
      apply (getDSLPArr_meet f P b). intros a Hf.
      apply H. intros Q HQ.
      apply (proj1 (getDSLPArr_meet f Q b)); [| exact Hf ].
      apply (proj1 (getDSLPArr_meet g (f Q) c)); [ exact HQ | exact Hg ].
  Qed.

  #[program] Definition firstDSLP {A B C} (f : DSLPArr A B)
    : DSLPArr (A * C) (B * C) :=
    fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Next Obligation.
    apply dslp_meet_hom. intros P [b c]. cbn [fst snd]. split.
    - intros H [a c'] Hr. exact (Hr P H).
    - intros H.
      apply (getDSLPArr_meet f (fun a => P (a, c)) b). intros a Hf.
      apply H. intros Q HQ. cbn [fst snd] in HQ.
      apply (proj1 (getDSLPArr_meet f (fun a0 => Q (a0, c)) b)); [ exact HQ | exact Hf ].
  Qed.

  Definition leftDSLPT {A B C} (f : DSLPArr A B) : SPArrT (A + C) (B + C) :=
    fun P y => match y with
               | inl b => f (fun a => P (inl a)) b
               | inr c => P (inr c)
               end.

  #[program] Definition leftDSLP {A B C} (f : DSLPArr A B)
    : DSLPArr (A + C) (B + C) :=
    leftDSLPT f.
  Next Obligation.
    apply dslp_meet_hom. intros P [b | c]; cbn.
    - split.
      + intros H [a | c'] Hr; exact (Hr P H).
      + intros H.
        apply (getDSLPArr_meet f (fun a => P (inl a)) b). intros a Hf.
        apply (H (inl a)). intros Q HQ. cbn in HQ.
        apply (proj1 (getDSLPArr_meet f (fun a0 => Q (inl a0)) b)); [ exact HQ | exact Hf ].
    - split.
      + intros H [a | c'] Hr; exact (Hr P H).
      + intro H. apply (H (inr c)). intros Q HQ. cbn in HQ. exact HQ.
  Qed.

  #[program] Definition appDSLP {A B} : DSLPArr (DSLPArr A B * A) B :=
    fun P b => forall f a, dslpRelT (getDSLPArr f) a b -> P (f, a).
  Next Obligation.
    apply dslp_meet_hom. intros P b. split.
    - intros H [f a] Hr. exact (Hr P H).
    - intros H f a Hr. apply H. intros Q HQ. exact (HQ f a Hr).
  Qed.

  #[global] Instance Arrow_DSLPArr : Arrow DSLPArr :=
    {| arr_pure := @pureDSLP ; arr_comp := @compDSLP ; arr_first := @firstDSLP |}.

  #[global] Instance ArrowChoice_DSLPArr : ArrowChoice DSLPArr :=
    {| arr_left := @leftDSLP |}.

  #[global] Instance ArrowApply_DSLPArr : ArrowApply DSLPArr :=
    {| arr_app := @appDSLP |}.

  (** Pointwise logical equivalence of the underlying transformers. *)
  Definition DSLPArr_eq {A B} (f g : DSLPArr A B) : Prop :=
    forall P b, f P b <-> g P b.

  #[global] Instance DSLPArr_eq_Equivalence {A B} : Equivalence (@DSLPArr_eq A B).
  Proof.
    constructor.
    - intros f P b. reflexivity.
    - intros f g H P b. symmetry. apply H.
    - intros f g h H1 H2 P b. etransitivity; [ apply H1 | apply H2 ].
  Qed.

  #[global] Instance ArrowEq_DSLPArr : ArrowEq DSLPArr :=
    {| arrow_eq := @DSLPArr_eq |}.

End DSLPArr.

(* ================================================================= *)
(** ** Each operation, unfolded once                                 *)
(* ================================================================= *)

Section Get.
  Lemma get_pure {A B} (h : A -> B) :
    getDSLPArr (pureDSLP h) = fun P b => forall a, h a = b -> P a.
  Proof. reflexivity. Qed.
  Lemma get_comp {A B C} (f : DSLPArr A B) (g : DSLPArr B C) :
    getDSLPArr (compDSLP f g) = fun P c => g (f P) c.
  Proof. reflexivity. Qed.
  Lemma get_first {A B C} (f : DSLPArr A B) :
    getDSLPArr (@firstDSLP A B C f) = fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Proof. reflexivity. Qed.
  Lemma get_left {A B C} (f : DSLPArr A B) :
    getDSLPArr (@leftDSLP A B C f) = leftDSLPT f.
  Proof. reflexivity. Qed.
  Lemma get_app {A B} :
    getDSLPArr (@appDSLP A B) =
    fun P b => forall f a, dslpRelT (getDSLPArr f) a b -> P (f, a).
  Proof. reflexivity. Qed.
End Get.
