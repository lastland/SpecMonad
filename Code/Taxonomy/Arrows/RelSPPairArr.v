(** * Predicate transformers and bundled predicate transformer arrows.

    We define the two predicate transformers on [PredArr] relations:

    [asp R pre b = exists a, pre a /\ R a b]   (angelic / existential)
    [dslp R pre b = forall a, R a b -> pre a]  (demonic / universal)

    Both [PureASPostArr] and [PureDSLPostArr] are sigma types over
    [RelSPPair], a record that couples a strongest-postcondition
    transformer with its underlying relation arrow.  They differ only
    in the correctness condition:

    [PureASPostArr A B] requires [spost d pre b <-> asp (rel d) pre b]
    [PureDSLPostArr A B] requires [spost d pre b <-> dslp (rel d) pre b]

    Both use the same relational composition, so both satisfy
    the arrow laws (proved in this file).  The property-only presentation
    lives in [SPostArr.v]; [SPostArrEquiv.v] relates the two presentations.

    Composed types for specifications:

    [ASPostArr S A = stateArrT S (optionArrT PureASPostArr) unit A]
    [DSLPostArr S A = stateArrT S (optionArrT PureDSLPostArr) unit A]

    Both unfold to [Pure(A/DSL)PostArr (unit * S) (option (A * S))]. *)

From Coq Require Import Program.Tactics Classical_Prop.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import PredArr.
From Incorrectness.Classes Require Export ArrowMonad.

(* ================================================================= *)
(** ** Predicate transformers and shared record                         *)
(* ================================================================= *)

(** Predicate transformer view: strongest postcondition (angelic / existential).
  *)
Definition asp {A B} (R : PredArr A B) (pre : A -> Prop) : B -> Prop :=
  fun b => exists a, pre a /\ R a b.

(* [asp] goes from predicate arrow to strongest postcondition arrow; [asp_inv] is
   the inverse. Similar to the relation described in Kenji's Ph.D. thesis, we
   can show that predicate monads and strongest postcondition monads are
   equivalent, by showing [asp_asp_inv] and [asp_inv_asp] below.  The option and
   state transformer stacks preserve this correspondence; see [SPostArrEquiv.v]. *)
Definition asp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : PredArr A B :=
  fun a b => pt (fun a' => a = a') b.

Theorem asp_asp_inv : forall {A B} (R : PredArr A B) a b,
    asp_inv (asp R) a b <-> R a b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? ?]]. subst. assumption.
  - intros. exists a. tauto.
Qed.

(** [asp] at a singleton precondition [eq a] recovers the relation at [a].
    This is [asp_asp_inv] with [asp_inv] unfolded ([asp_inv pt a := pt (eq a)]),
    packaged for rewriting in strongest-postcondition sequencing laws. *)
Corollary asp_singleton : forall {A B} (R : PredArr A B) (a : A) (b : B),
    asp R (eq a) b <-> R a b.
Proof.
  intros. unfold asp. split.
  - intros [a' [<- H]]. exact H.
  - intro H. exists a. auto.
Qed.

(* Cannot prove this for arbitrary [(A -> Prop) -> B -> Prop]. *)
Theorem asp_inv_asp : forall {A B} (R : PredArr A B) pre b,
    asp (asp_inv (asp R)) pre b <-> asp R pre b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? [? [? ?]]]]. subst.
    exists x0. tauto.
  - intros [? [? ?]].
    exists x. split; [assumption |].
    exists x. tauto.
Qed.

(** Demonic predicate transformer: universal dual of [asp]. *)
Definition dslp {A B} (R : PredArr A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

(* This shows a different equivalence between predicate arrows and strongest
   postcondition arrows. We can figure this out by "reverse engineering"
   [dslp_dslp_inv], but why does this one make sense? *)
Definition dslp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : PredArr A B :=
  fun a b => forall pre, pt pre b -> pre a.

Theorem dslp_dslp_inv : forall {A B} (R : PredArr A B) a b,
    dslp_inv (dslp R) a b <-> R a b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros ?. apply H. auto.
  - intros. auto.
Qed.

Theorem dslp_inv_dslp : forall {A B} (R : PredArr A B) pre b,
    dslp (dslp_inv (dslp R)) pre b <-> dslp R pre b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros. apply H; intros. auto.
  - intros. apply H0. apply H.
Qed.

(* ================================================================= *)
(** ** Characterizations of [dsp] and [aslp] (paper §3.2.4)           *)
(* ================================================================= *)

(** The four SP variants of the Verscht & Kaminski taxonomy are built
    from the same reachability relation [R] but differ in quantifier
    structure:

    - [asp]  = existential (angelic, total)
    - [dslp] = universal   (demonic, liberal)
    - [dsp]  = [asp /\ dslp] (demonic, total)
    - [aslp] = [asp \/ dslp] (angelic, liberal)

    These two theorems match [dsp] and [aslp] with the paper's
    Definitions 3.5 and 3.6, which guard the quantifier by whether the
    inverse image is empty. *)

Section SPCharacterizations.

  Variables A B : Type.
  Variable R : PredArr A B.

  Theorem dsp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, R a b) /\ forall a, R a b -> pre a) <->
    (asp R pre b /\ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [[a0 HRa0] Hall].
      split; [exists a0; auto | exact Hall].
    - intros [[a0 [Hpre HRa0]] Hall].
      split; [exists a0; exact HRa0 | exact Hall].
  Qed.

  Theorem aslp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, pre a /\ R a b) \/ ~ exists a, R a b) <->
    (asp R pre b \/ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [Hsp | Hunreach].
      + left. exact Hsp.
      + right. intros a HRab. exfalso. apply Hunreach. exists a. exact HRab.
    - intros [Hsp | Hdp].
      + left. exact Hsp.
      + destruct (classic (exists a, R a b)) as [[a0 HRa0] | Hunreach].
        * left. exists a0. split; [exact (Hdp a0 HRa0) | exact HRa0].
        * right. exact Hunreach.
  Qed.

End SPCharacterizations.

(** Couple a strongest-postcondition transformer with its underlying
    relation arrow.  Using a record avoids universe issues that [prod]
    causes when combined with [Eq1] from ExtLib. *)
Record RelSPPair (A B : Type) := mkRelSPPair {
  spost : (A -> Prop) -> B -> Prop ;
  rel : PredArr A B
}.
Arguments mkRelSPPair {A B}.
Arguments spost {A B}.
Arguments rel {A B}.

(* ================================================================= *)
(** ** Angelic: [PureASPostArr]                                       *)
(* ================================================================= *)

(** [PureASPostArr] does not strictly need [RelSPPair] — it could remain
    as [{ f | IsASP f }] with a Prop-level existential (see
    [Taxonomy/deprecated/SPostArr.v]).  Using the shared record lets us
    reuse arrow operations, equality lemmas, and monad infrastructure
    between the angelic and demonic variants. *)
Definition PureASPostArr (A B : Type) : Type :=
  { d : RelSPPair A B |
    forall pre b, spost d pre b <-> asp (rel d) pre b }.

(** Smart constructor: wrap a relation with [asp]. *)
#[program] Definition mkASP {A B} (R : PredArr A B) : PureASPostArr A B :=
  mkRelSPPair (asp R) R.
Next Obligation. reflexivity. Qed.

Section PureASPostArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureASPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_ASP {A B} (f : A -> B) : PureASPostArr A B :=
    mkRelSPPair (fun pre b => exists a, pre a /\ f a = b) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_ASP {A B C}
    (f : PureASPostArr A B) (g : PureASPostArr B C) : PureASPostArr A C :=
    mkRelSPPair (fun pre c => spost g (spost f pre) c)
               (fun a c => exists b, rel f a b /\ rel g b c).
  Next Obligation.
    split.
    - intro H. unfold asp. apply (proj2_sig g) in H. unfold asp in H.
      destruct H as [b0 [Hfb Hrgbc]].
      apply (proj2_sig f) in Hfb. unfold asp in Hfb.
      destruct Hfb as [a0 [Hpre Hrfab]].
      exists a0. split; [exact Hpre | exists b0; auto].
    - intros [a0 [Hpre [b0 [Hrfab Hrgbc]]]].
      apply (proj2_sig g). unfold asp.
      exists b0. split.
      + apply (proj2_sig f). unfold asp. exists a0. auto.
      + exact Hrgbc.
  Qed.

  #[local]
  #[program] Definition arr_first_ASP {A B C}
    (f : PureASPostArr A B) : PureASPostArr (A * C)%type (B * C)%type :=
    mkRelSPPair
      (fun pre '(b, d) => spost f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => rel f a b /\ d = d').
  Next Obligation.
    unfold asp. split.
    - intro H. apply (proj2_sig f) in H. unfold asp in H.
      destruct H as [a [Hpre Hrf]].
      exists (a, c). simpl. auto.
    - intros [[a d0] [Hpre [Hrf Heq]]]. simpl in *. subst d0.
      apply (proj2_sig f). unfold asp. exists a. auto.
  Qed.

  #[global]
  Instance Arrow_PureASPostArr : Arrow PureASPostArr := {
    arr_pure := @arr_pure_ASP ;
    arr_comp := @arr_comp_ASP ;
    arr_first := @arr_first_ASP
  }.

  #[local]
  #[program] Definition arr_app_ASP {A B}
    : PureASPostArr (PureASPostArr A B * A)%type B :=
    mkRelSPPair
      (fun pre b => exists f a, pre (f, a) /\ rel (proj1_sig f) a b)
      (fun fa b => rel (proj1_sig (fst fa)) (snd fa) b).
  Next Obligation.
    unfold asp. split.
    - intros [f [a [Hpre Hfab]]].
      exists (f, a). auto.
    - intros [[f a] [Hpre Hfab]].
      exists f, a. auto.
  Qed.

  #[global]
  Instance ArrowApply_PureASPostArr : ArrowApply PureASPostArr := {
    arr_app := @arr_app_ASP
  }.

  (* -------------------------------------------------------------- *)
  (** *** ArrowChoice instance for [PureASPostArr]                    *)
  (* -------------------------------------------------------------- *)

  Definition left_rel {A B C} (R : PredArr A B) : PredArr (A + C) (B + C) :=
    fun x y => match x, y with
      | inl a, inl b => R a b
      | inr c, inr c' => c = c'
      | _, _ => False
    end.

  #[local]
  #[program] Definition arr_left_ASP {A B C}
    (f : PureASPostArr A B) : PureASPostArr (A + C)%type (B + C)%type :=
    mkRelSPPair
      (fun pre y => match y with
        | inl b => spost f (fun a => pre (inl a)) b
        | inr c => pre (inr c)
      end)
      (left_rel (rel f)).
  Next Obligation.
    destruct b as [b0|c0]; unfold asp, left_rel; cbn.
    - split.
      + intro H. apply (proj2_sig f) in H. unfold asp in H.
        destruct H as [a [Hpre Hrf]]. exists (inl a). auto.
      + intros [[a|c'] [Hpre Hrx]]; [| contradiction].
        apply (proj2_sig f). unfold asp. exists a; auto.
    - split.
      + intros Hpre. exists (inr c0). auto.
      + intros [[a|c'] [Hpre Hrx]]; [contradiction |].
        simpl in Hrx. subst c'. exact Hpre.
  Qed.

  #[global]
  Instance ArrowChoice_PureASPostArr : ArrowChoice PureASPostArr := {
    arr_left := @arr_left_ASP
  }.

End PureASPostArr.

(* ================================================================= *)
(** ** Demonic: [PureDSLPostArr]                                       *)
(* ================================================================= *)

Definition PureDSLPostArr (A B : Type) : Type :=
  { d : RelSPPair A B |
    forall pre b, spost d pre b <-> dslp (rel d) pre b }.

(** Smart constructor: wrap a relation with [dslp]. *)
#[program] Definition mkDSLP {A B} (R : PredArr A B) : PureDSLPostArr A B :=
  mkRelSPPair (dslp R) R.
Next Obligation. reflexivity. Qed.

Section PureDSLPostArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureDSLPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_DSLP {A B} (f : A -> B) : PureDSLPostArr A B :=
    mkRelSPPair (fun pre b => forall a, f a = b -> pre a) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_DSLP {A B C}
    (f : PureDSLPostArr A B) (g : PureDSLPostArr B C) : PureDSLPostArr A C :=
    mkRelSPPair (fun pre c => spost g (spost f pre) c)
               (fun a c => exists b, rel f a b /\ rel g b c).
  Next Obligation.
    split.
    - intro H. unfold dslp. intros a [b0 [Hrf Hrg]].
      apply (proj2_sig g) in H. unfold dslp in H.
      apply H in Hrg. apply (proj2_sig f) in Hrg. unfold dslp in Hrg.
      exact (Hrg a Hrf).
    - intros Hall. apply (proj2_sig g). unfold dslp.
      intros b0 Hrg. apply (proj2_sig f). unfold dslp. intros a Hrf.
      exact (Hall a (ex_intro _ b0 (conj Hrf Hrg))).
  Qed.

  #[local]
  #[program] Definition arr_first_DSLP {A B C}
    (f : PureDSLPostArr A B) : PureDSLPostArr (A * C)%type (B * C)%type :=
    mkRelSPPair
      (fun pre '(b, d) => spost f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => rel f a b /\ d = d').
  Next Obligation.
    unfold dslp. split.
    - intro H. apply (proj2_sig f) in H. unfold dslp in H.
      intros [a d0] [Hrf Heq]. simpl in *. subst d0.
      exact (H a Hrf).
    - intros Hall. apply (proj2_sig f). unfold dslp. intros a Hrf.
      exact (Hall (a, _) (conj Hrf eq_refl)).
  Qed.

  #[global]
  Instance Arrow_PureDSLPostArr : Arrow PureDSLPostArr := {
    arr_pure := @arr_pure_DSLP ;
    arr_comp := @arr_comp_DSLP ;
    arr_first := @arr_first_DSLP
  }.

  #[local]
  #[program] Definition arr_app_DSLP {A B}
    : PureDSLPostArr (PureDSLPostArr A B * A)%type B :=
    mkRelSPPair
      (fun pre b => forall f a, rel (proj1_sig f) a b -> pre (f, a))
      (fun '(f, a) b => rel f a b).
  Next Obligation.
    unfold dslp. split.
    - intros H [f0 a] Hfab. exact (H f0 a Hfab).
    - intros H f0 a Hfab. exact (H (f0, a) Hfab).
  Qed.

  #[global]
  Instance ArrowApply_PureDSLPostArr : ArrowApply PureDSLPostArr := {
    arr_app := @arr_app_DSLP
  }.

  (* -------------------------------------------------------------- *)
  (** *** ArrowChoice instance for [PureDSLPostArr]                   *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_left_DSLP {A B C}
    (f : PureDSLPostArr A B) : PureDSLPostArr (A + C)%type (B + C)%type :=
    mkRelSPPair
      (fun pre y => match y with
        | inl b => spost f (fun a => pre (inl a)) b
        | inr c => pre (inr c)
      end)
      (left_rel (rel f)).
  Next Obligation.
    destruct b as [b0|c0]; unfold dslp, left_rel; cbn.
    - split.
      + intro H. apply (proj2_sig f) in H. unfold dslp in H.
        intros [a|c'] Hrx; [exact (H a Hrx) | contradiction].
      + intros Hall. apply (proj2_sig f). unfold dslp.
        intros a Hrf. exact (Hall (inl a) Hrf).
    - split.
      + intros Hpre [a|c'] Hrx; [contradiction |].
        simpl in Hrx. subst c'. exact Hpre.
      + intros Hall. exact (Hall (inr c0) eq_refl).
  Qed.

  #[global]
  Instance ArrowChoice_PureDSLPostArr : ArrowChoice PureDSLPostArr := {
    arr_left := @arr_left_DSLP
  }.

End PureDSLPostArr.

(* ================================================================= *)
(** ** Angelic and demonic option transformers                        *)
(* ================================================================= *)

(** [optionASPArr] and [optionDSLPArr] get their [Arrow], [ArrowChoice],
    and [ArrowApply] instances from the generic transformers in
    [OptionArrowT.v], via [ArrowChoice_PureASPostArr] and
    [ArrowChoice_PureDSLPostArr]. *)

Definition optionASPArr := optionArrT PureASPostArr.
Definition optionDSLPArr := optionArrT PureDSLPostArr.

(* ================================================================= *)
(** ** Composed types for specifications                              *)
(* ================================================================= *)

Section ComposedTypes.

  Variable S : Type.

  (** [ASPostArr S A] is the angelic strongest postcondition arrow.
      [ASPostArr S A = PureASPostArr (unit * S) (option (A * S))] *)
  Definition ASPostArr (A : Type) : Type :=
    stateArrT S optionASPArr unit A.

  (** [DSLPostArr S A] is the demonic strongest liberal postcondition arrow.
      [DSLPostArr S A = PureDSLPostArr (unit * S) (option (A * S))] *)
  Definition DSLPostArr (A : Type) : Type :=
    stateArrT S optionDSLPArr unit A.

End ComposedTypes.

(* ================================================================= *)
(** * Facts and laws                                                       *)
(* ================================================================= *)

(** * Arrow law proofs for angelic and demonic predicate transformer arrows.

    Angelic laws ([PureASPostArr], [optionASPArr]) are proved by
    [PureASPostArr_eq] and then transferring through [IsASP] to work
    with raw existentials.

    Demonic laws ([PureDSLPostArr], [optionDSLPArr]) follow the same
    structure, using [IsDSLP] and raw universals. *)

From Coq Require Import FunctionalExtensionality PropExtensionality ProofIrrelevance Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import Monad StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import PredArr.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

(* ================================================================= *)
(** ** Utilities                                                       *)
(* ================================================================= *)

Lemma PureASPostArr_eq {A B} (f g : PureASPostArr A B) :
  (forall pre b, spost (proj1_sig f) pre b <-> spost (proj1_sig g) pre b) -> f = g.
Proof.
  intro Heq.
  destruct f as [[fpt frel] fp], g as [[gpt grel] gp]; simpl in *.
  assert (Hpt : fpt = gpt).
  { extensionality pre. extensionality b.
    apply propositional_extensionality. apply Heq. }
  subst gpt.
  assert (Hrel : frel = grel).
  { extensionality a. extensionality b.
    apply propositional_extensionality.
    assert (Hsp : forall pre b0, asp frel pre b0 <-> asp grel pre b0).
    { intros pre0 b0. split; intro H.
      - apply gp. apply fp. exact H.
      - apply fp. apply gp. exact H. }
    split; intro Hab.
    - specialize (Hsp (eq a) b). unfold asp in Hsp.
      destruct (proj1 Hsp (ex_intro _ a (conj eq_refl Hab))) as [a' [Heq' Hrel]].
      subst a'. exact Hrel.
    - specialize (Hsp (eq a) b). unfold asp in Hsp.
      destruct (proj2 Hsp (ex_intro _ a (conj eq_refl Hab))) as [a' [Heq' Hrel]].
      subst a'. exact Hrel. }
  subst grel.
  f_equal. apply proof_irrelevance.
Qed.

Lemma IsASP_rewrite {A B} (f : PureASPostArr A B) :
  exists R : PredArr A B,
    forall pre b, spost (proj1_sig f) pre b <-> exists a, pre a /\ R a b.
Proof.
  exists (rel (proj1_sig f)). intros pre b.
  apply (proj2_sig f).
Qed.

(** [spost] of any PureASPostArr rewrites to existential form. *)
Lemma ASP_asp {A B} (f : PureASPostArr A B) (R : PredArr A B)
  (HR : forall pre b, spost (proj1_sig f) pre b <-> exists a, pre a /\ R a b) :
  forall P b, spost (proj1_sig f) P b <-> exists a, P a /\ R a b.
Proof. exact HR. Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [PureASPostArr]                                 *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PureASPostArr : ArrowEq PureASPostArr := {
  arrow_eq := fun A B => @eq (PureASPostArr A B)
}.

Lemma id_pred {A} (pre : A -> Prop) :
  (fun b => exists a, pre a /\ a = b) = pre.
Proof.
  extensionality b. apply propositional_extensionality. sauto limit: 200.
Qed.

#[global]
Instance ArrowLaws_PureASPostArr : ArrowLaws PureASPostArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureASPostArr_eq; intros pre b. cbn.
    rewrite id_pred. reflexivity.

  - (* comp_id_r: arr_comp f arr_id = f *)
    apply PureASPostArr_eq; intros pre b. cbn. sauto limit: 200.

  - (* comp_assoc *)
    apply PureASPostArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp *)
    apply PureASPostArr_eq; intros pre c. cbn. sauto limit: 200.

  - (* first_pure *)
    apply PureASPostArr_eq; intros pre [b d]. cbn. sauto limit: 200.

  - (* first_comp *)
    apply PureASPostArr_eq; intros pre [c d]. cbn. reflexivity.

  - (* first_fst — requires IsASP for additivity *)
    apply PureASPostArr_eq; intros pre b. cbn.
    destruct (IsASP_rewrite f) as [R_f H_f].
    split.
    + intros [[b0 c] [Hfc Heq]]; cbn in Heq; subst.
      rewrite H_f in Hfc. destruct Hfc as [a [Hpre Hra]].
      rewrite H_f. exists a. split.
      * exists (a, c). cbn. auto.
      * exact Hra.
    + intro Hfb.
      rewrite H_f in Hfb. destruct Hfb as [a [Hfst Hra]].
      destruct Hfst as [[a0 c] [Hpre Heq]]; cbn in Heq; subst.
      exists (b, c). split.
      * rewrite H_f. eexists; eauto.
      * cbn. reflexivity.

  - (* first_assoc *)
    apply PureASPostArr_eq; intros pre [b [c d]]. cbn.
    destruct (IsASP_rewrite f) as [R_f H_f].
    split.
    + intros [[[b0 c0] d0] [Hff Hassoc]].
      unfold assoc_prod in Hassoc. inversion Hassoc; subst.
      rewrite H_f in Hff. destruct Hff as [a [Hpre Hra]].
      rewrite H_f. exists a. split.
      * exists ((a, c), d). split; [exact Hpre | reflexivity].
      * exact Hra.
    + intro Hf0.
      rewrite H_f in Hf0. destruct Hf0 as [a [Hpure Hra]].
      destruct Hpure as [[[a0 c0] d0] [Hpre Hassoc]].
      unfold assoc_prod in Hassoc.
      assert (Ha0 : a0 = a) by congruence.
      assert (Hc0 : c0 = c) by congruence.
      assert (Hd0 : d0 = d) by congruence.
      subst a0 c0 d0.
      exists ((b, c), d). split.
      * rewrite H_f. exists a. auto.
      * reflexivity.

  - (* comp_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureASPostArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureASPostArr;
    intros; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** [ArrowChoiceLaws] for [PureASPostArr]                           *)
(* ================================================================= *)

#[global]
Instance ArrowChoiceLaws_PureASPostArr : ArrowChoiceLaws PureASPostArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    apply PureASPostArr_eq; intros pre [b|c]; cbn; unfold sum_bimap; sauto limit: 200.
  - (* left_comp *)
    apply PureASPostArr_eq; intros pre [c|d]; cbn; reflexivity.
  - (* left_inl *)
    apply PureASPostArr_eq; intros pre [b|c]; cbn.
    + destruct (IsASP_rewrite f) as [Rf Hf]. split.
      * intros [b0 [Hfb Hinl]].
        injection Hinl as Hinl. subst.
        rewrite Hf in Hfb. destruct Hfb as [a [Hp Hra]].
        rewrite Hf. exists a. split; [exists a; auto | exact Hra].
      * intro Hfb. rewrite Hf in Hfb. destruct Hfb as [a [[a0 [Hp Hinl]] Hra]].
        injection Hinl as Hinl. subst.
        exists b. split; [rewrite Hf; exists a; auto | reflexivity].
    + sauto limit: 200.
  - (* left_assoc *)
    apply PureASPostArr_eq; intros pre [b | [c | d]]; cbn.
    + (* inl b *)
      destruct (IsASP_rewrite f) as [Rf Hf]. split.
      * intros [x [Hleft Hassoc]].
        destruct x as [[b'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        cbn in Hleft. rewrite Hf in Hleft. destruct Hleft as [a [Hp Hra]].
        rewrite Hf. exists a. split; [exists (inl (inl a)); auto | exact Hra].
      * intro Hfb. rewrite Hf in Hfb. destruct Hfb as [a [Hex Hra]].
        destruct Hex as [x [Hp Hassoc]].
        destruct x as [[a'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exists (inl (inl b)). split; [cbn; rewrite Hf; exists a; auto | reflexivity].
    + (* inr (inl c) *)
      split.
      * intros [x [Hleft Hassoc]].
        destruct x as [[b'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exists (inl (inr c)). cbn. auto.
      * intros [x [Hp Hassoc]].
        destruct x as [[a'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exists (inl (inr c)). cbn. auto.
    + (* inr (inr d) *)
      split.
      * intros [x [Hleft Hassoc]].
        destruct x as [[b'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exists (inr d). cbn. auto.
      * intros [x [Hp Hassoc]].
        destruct x as [[a'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exists (inr d). cbn. auto.
    - (* left_inr *)
      apply PureASPostArr_eq; intros pre [b|c']; cbn.
      + (* inl b: both sides should be False *)
        destruct (IsASP_rewrite f) as [Rf Hf].
        rewrite Hf. unfold asp.
        split; intros H; exfalso.
        * destruct H as [a [[c0 [_ Habs]] _]]. discriminate.
        * destruct H as [c0 [_ Habs]]. discriminate.
      + (* inr c': both sides give pre c' after simplification *)
        sauto limit: 200.
    - (* left_natural *)
      apply PureASPostArr_eq; intros pre [b|d]; cbn; unfold sum_bimap.
      + destruct (IsASP_rewrite f) as [Rf Hf].
        split.
        * intros [[a'|c'] [Hex Heq]]; [| discriminate].
          injection Heq as Heq. subst. cbn in Hex. rewrite Hf in Hex.
          destruct Hex as [a0 [Hpre Hra]].
          rewrite Hf. exists a0. split.
          -- exists (inl a0). split; [exact Hpre | reflexivity].
          -- exact Hra.
        * intro Hfb. rewrite Hf in Hfb. destruct Hfb as [a [[x [Hpre Heq]] Hra]].
          destruct x as [a'|c']; [injection Heq as Heq; subst | discriminate].
          exists (inl b). split; [cbn; rewrite Hf; exists a; auto | reflexivity].
      + split.
        * intros [[b'|d'] [Hex Heq]]; [discriminate |].
          injection Heq as Heq. subst.
          exists (inr d'). split; [exact Hex | reflexivity].
        * intros [x [Hpre Heq]].
          destruct x as [b'|d']; [discriminate |].
          injection Heq as Heq. subst.
          exists (inr d'). split; [exact Hpre | reflexivity].
    - (* first_left_dist *)
      apply PureASPostArr_eq; intros pre y.
      destruct y as [[b d]|[c d]]; cbn; unfold sum_prod_dist.
      + (* inl (b, d) *)
        destruct (IsASP_rewrite f) as [Rf Hf]. split.
        * intros [[[b'|c'] d'] [Hleft Hsd]].
          -- injection Hsd as Hb Hd. subst.
             cbn in Hleft. rewrite Hf in Hleft. destruct Hleft as [a [Hpre Hra]].
             rewrite Hf. exists a. split.
             ++ exists (inl a, d). split; [exact Hpre | reflexivity].
             ++ exact Hra.
          -- discriminate.
        * intros Hfb. rewrite Hf in Hfb. destruct Hfb as [a [Hex Hra]].
          destruct Hex as [[[a'|c'] d0] [Hpre Hsd]]; cbn in Hsd; [| discriminate].
          injection Hsd as Ha Hd. subst.
          exists (inl b, d). split.
          -- cbn. rewrite Hf. exists a. auto.
          -- reflexivity.
      + (* inr (c, d) *)
        split.
        * intros [[[b'|c'] d'] [Hleft Hsd]].
          -- discriminate.
          -- injection Hsd as Hc Hd. subst. cbn in Hleft.
             exists (inr c, d). split; [exact Hleft | reflexivity].
        * intros [[[a'|c'] d'] [Hpre Hsd]]; cbn in Hsd; [discriminate |].
          injection Hsd as Hc Hd. subst.
          exists (inr c, d). split.
          -- cbn. exact Hpre.
          -- reflexivity.
    - (* left_proper *)
      unfold Proper, respectful, arrow_eq, ArrowEq_PureASPostArr;
      intros; subst; reflexivity.
Qed.
(* ================================================================= *)
(** ** Utilities for [PureDSLPostArr]                                   *)
(* ================================================================= *)

Lemma PureDSLPostArr_eq {A B} (f g : PureDSLPostArr A B) :
  (forall pre b, spost (proj1_sig f) pre b <-> spost (proj1_sig g) pre b) -> f = g.
Proof.
  intro Heq.
  destruct f as [[fpt frel] fp], g as [[gpt grel] gp]; simpl in *.
  assert (Hpt : fpt = gpt).
  { extensionality pre. extensionality b.
    apply propositional_extensionality. apply Heq. }
  subst gpt.
  assert (Hrel : frel = grel).
  { extensionality a. extensionality b.
    apply propositional_extensionality.
    assert (Hdp : forall pre b0, dslp frel pre b0 <-> dslp grel pre b0).
    { intros pre0 b0. split; intro H.
      - apply gp. apply fp. exact H.
      - apply fp. apply gp. exact H. }
    split; intro Hab.
    - assert (Htmp : dslp frel (fun a' => grel a' b) b).
      { apply Hdp. unfold dslp. auto. }
      unfold dslp in Htmp. exact (Htmp a Hab).
    - assert (Htmp : dslp grel (fun a' => frel a' b) b).
      { apply Hdp. unfold dslp. auto. }
      unfold dslp in Htmp. exact (Htmp a Hab). }
  subst grel.
  f_equal. apply proof_irrelevance.
Qed.

Lemma IsDSLP_rewrite {A B} (f : PureDSLPostArr A B) :
  exists R : PredArr A B,
    forall pre b, spost (proj1_sig f) pre b <-> forall a, R a b -> pre a.
Proof.
  exists (rel (proj1_sig f)). intros pre b.
  apply (proj2_sig f).
Qed.

Lemma DSLP_dslp {A B} (f : PureDSLPostArr A B) (R : PredArr A B)
  (HR : forall pre b, spost (proj1_sig f) pre b <-> forall a, R a b -> pre a) :
  forall P b, spost (proj1_sig f) P b <-> forall a, R a b -> P a.
Proof. exact HR. Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [PureDSLPostArr]                                *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PureDSLPostArr : ArrowEq PureDSLPostArr := {
  arrow_eq := fun A B => @eq (PureDSLPostArr A B)
}.

Lemma id_pred_dslp {A} (pre : A -> Prop) :
  (fun b => forall a, a = b -> pre a) = pre.
Proof.
  extensionality b. apply propositional_extensionality. sauto limit: 200.
Qed.

#[global]
Instance ArrowLaws_PureDSLPostArr : ArrowLaws PureDSLPostArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureDSLPostArr_eq; intros pre b. cbn.
    rewrite id_pred_dslp. reflexivity.

  - (* comp_id_r *)
    apply PureDSLPostArr_eq; intros pre b. cbn. sauto limit: 200.

  - (* comp_assoc *)
    apply PureDSLPostArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp *)
    apply PureDSLPostArr_eq; intros pre c. cbn. sauto limit: 200.

  - (* first_pure *)
    apply PureDSLPostArr_eq; intros pre [b d]. cbn. sauto limit: 200.

  - (* first_comp *)
    apply PureDSLPostArr_eq; intros pre [c d]. cbn. reflexivity.

  - (* first_fst — requires IsDSLP for multiplicativity.
       Both sides reduce (via IsDSLP) to quantifier reordering:
       ∀c ∀a, R a b → pre(a,c) ↔ ∀a, R a b → ∀c, pre(a,c). *)
    apply PureDSLPostArr_eq; intros pre b.
    destruct (IsDSLP_rewrite f) as [R_f H_f].
    cbn. split.
    + intros H. rewrite H_f. intros a Hra p Heq.
      destruct p as [a0 c]; cbn in Heq; subst.
      assert (Hc := H (b, c) eq_refl).
      rewrite H_f in Hc. exact (Hc a Hra).
    + intros Hfb p Heq. destruct p as [b0 c]; cbn in Heq; subst.
      rewrite H_f. intros a Hra.
      rewrite H_f in Hfb. specialize (Hfb a Hra).
      exact (Hfb (a, c) eq_refl).

  - (* first_assoc *)
    apply PureDSLPostArr_eq; intros pre [b [c d]].
    destruct (IsDSLP_rewrite f) as [R_f H_f].
    cbn. split.
    + intros H. rewrite H_f. intros a Hra p Hassoc.
      destruct p as [[a0 c0] d0].
      unfold assoc_prod in Hassoc.
      assert (Ha : a0 = a) by congruence.
      assert (Hc : c0 = c) by congruence.
      assert (Hd : d0 = d) by congruence.
      subst.
      assert (Hcd := H ((b, c), d) eq_refl).
      rewrite H_f in Hcd. exact (Hcd a Hra).
    + intros Hfb p Hassoc.
      destruct p as [[b0 c0] d0].
      unfold assoc_prod in Hassoc.
      assert (Hb : b0 = b) by congruence.
      assert (Hc : c0 = c) by congruence.
      assert (Hd : d0 = d) by congruence.
      subst.
      rewrite H_f. intros a Hra.
      rewrite H_f in Hfb. specialize (Hfb a Hra).
      exact (Hfb ((a, c), d) eq_refl).

  - (* comp_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureDSLPostArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureDSLPostArr;
    intros; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** [ArrowChoiceLaws] for [PureDSLPostArr]                          *)
(* ================================================================= *)

#[global]
Instance ArrowChoiceLaws_PureDSLPostArr : ArrowChoiceLaws PureDSLPostArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    apply PureDSLPostArr_eq; intros pre [b|c]; cbn; unfold sum_bimap;
    sauto limit: 200.
  - (* left_comp *)
    apply PureDSLPostArr_eq; intros pre [c|d]; cbn; reflexivity.
  - (* left_inl *)
    apply PureDSLPostArr_eq; intros pre [b|c]; cbn.
    + destruct (IsDSLP_rewrite f) as [Rf Hf]. split.
      * intros H. rewrite Hf. intros a Hra a0 Hinl.
        injection Hinl as Hinl. subst.
        assert (Hfa := H b eq_refl).
        rewrite Hf in Hfa. exact (Hfa a Hra).
      * intro Hfb. intros b0 Heq.
        injection Heq as Heq. subst.
        rewrite Hf. intros a Hra.
        rewrite Hf in Hfb. specialize (Hfb a Hra (a) eq_refl). exact Hfb.
    + split; intros _ ? H; discriminate H.
  - (* left_assoc *)
    apply PureDSLPostArr_eq; intros pre [b | [c | d]]; cbn.
    + destruct (IsDSLP_rewrite f) as [Rf Hf]. split.
      * intro H. rewrite Hf. intros a Hra x Hassoc.
        destruct x as [[a'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        assert (Hfa := H (inl (inl b)) eq_refl).
        cbn in Hfa. rewrite Hf in Hfa. exact (Hfa a Hra).
      * intro Hfb. rewrite Hf in Hfb. intros x Hassoc.
        destruct x as [[b'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        cbn. rewrite Hf. intros a Hra. exact (Hfb a Hra (inl (inl a)) eq_refl).
    + split.
      * intros H x Hassoc.
        destruct x as [[a'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exact (H (inl (inr c)) eq_refl).
      * intros Hpre [[b'|c0]|d0] Hassoc; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst. exact (Hpre (inl (inr c)) eq_refl).
    + split.
      * intros H x Hassoc.
        destruct x as [[a'|c0]|d0]; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst.
        exact (H (inr d) eq_refl).
      * intros Hpre [[b'|c0]|d0] Hassoc; cbn in Hassoc; try discriminate.
        injection Hassoc as Hassoc. subst. exact (Hpre (inr d) eq_refl).
    - (* left_inr *)
      apply PureDSLPostArr_eq; intros pre [b|c']; cbn.
      + destruct (IsDSLP_rewrite f) as [Rf Hf]. split.
        * intros _ c0 Habs. discriminate.
        * intros _. rewrite Hf. intros a _ c0 Habs. discriminate.
      + split; intros H c0 Heq; injection Heq as Heq; subst; exact (H c' eq_refl).
    - (* left_natural *)
      apply PureDSLPostArr_eq; intros pre [b|d]; cbn; unfold sum_bimap.
      + destruct (IsDSLP_rewrite f) as [Rf Hf]. split.
        * intros H. rewrite Hf. intros a Hra [a'|c'] Heq; [| discriminate].
          injection Heq as Heq. subst.
          specialize (H (inl b) eq_refl). cbn in H. rewrite Hf in H.
          exact (H a Hra).
        * intro Hfb. rewrite Hf in Hfb.
          intros [b'|c'] Heq; [| discriminate].
          injection Heq as Heq. subst. cbn.
          rewrite Hf. intros a Hra.
          exact (Hfb a Hra (inl a) eq_refl).
      + split.
        * intros H [a'|c'] Heq; [discriminate |].
          injection Heq as Heq. apply (H (inr c')). f_equal. exact Heq.
        * intros H [b'|c'] Heq; [discriminate |].
          injection Heq as Heq. apply (H (inr c')). f_equal. exact Heq.
    - (* first_left_dist *)
      apply PureDSLPostArr_eq; intros pre y.
      destruct y as [[b d]|[c d]]; cbn; unfold sum_prod_dist.
      + destruct (IsDSLP_rewrite f) as [Rf Hf]. split.
        * intros H. rewrite Hf. intros a Hra [[a'|c'] d'] Hsd; cbn in Hsd;
            [| discriminate].
          injection Hsd as Ha Hd. subst.
          assert (Hx := H (inl b, d) eq_refl). cbn in Hx. rewrite Hf in Hx.
          exact (Hx a Hra).
        * intro Hfb. rewrite Hf in Hfb.
          intros [[b'|c'] d'] Heq; cbn in Heq; [| discriminate].
          injection Heq as Hb Hd. subst. cbn.
          rewrite Hf. intros a Hra.
          exact (Hfb a Hra (inl a, d) eq_refl).
      + split.
        * intros H [[a'|c'] d'] Hsd; cbn in Hsd; [discriminate |].
          injection Hsd as Hc Hd. subst.
          exact (H (inr c, d) eq_refl).
        * intros Hall [[b'|c'] d'] Heq; cbn in Heq; [discriminate |].
          injection Heq as Hc Hd. subst. cbn.
          exact (Hall (inr c, d) eq_refl).
    - (* left_proper *)
      unfold Proper, respectful, arrow_eq, ArrowEq_PureDSLPostArr;
      intros; subst; reflexivity.
Qed.


(* ================================================================= *)
(** ** [ArrowApplyLaws] for [PureASPostArr] and [PureDSLPostArr]       *)
(* ================================================================= *)

#[global]
Instance ArrowApplyLaws_PureASPostArr : ArrowApplyLaws PureASPostArr.
Proof.
  constructor; intros.
  - (* app_law *)
    apply PureASPostArr_eq; intros pre b. cbn. split.
    + intros [f0 [a [[a' [Hpre Hpair]] Hfa]]].
      inversion Hpair; subst f0 a.
      apply (proj2_sig f). unfold asp. exists a'. auto.
    + intros Hfb. apply (proj2_sig f) in Hfb. unfold asp in Hfb.
      destruct Hfb as [a [Hpre Hra]].
      exists f, a. split; [exists a; auto | exact Hra].
  - (* app_pair *)
    apply PureASPostArr_eq; intros pre q. cbn. split.
    + intros [f0 [y [[x [Hpre Hfx]] Hrel]]].
      subst f0. cbn in Hrel. subst q. exists (x, y). auto.
    + intros [p [Hpre Heq]]. subst q. destruct p as [x y].
      exists (@arr_pure PureASPostArr Arrow_PureASPostArr B (A * B)%type
                (fun y' : B => (x, y'))), y.
      split; [ exists x; cbn; auto | cbn; reflexivity ].
  - (* app_post *)
    apply PureASPostArr_eq; intros pre c. cbn. split.
    + intros [g [a [[f [Hpre Hgf]] Hrel]]].
      subst g. cbn in Hrel. destruct Hrel as [b [Hf Hh]].
      apply (proj2_sig h). unfold asp.
      exists b. split; [| exact Hh ]. exists f, a. auto.
    + intros Hc. apply (proj2_sig h) in Hc. unfold asp in Hc.
      destruct Hc as [b [[f [a [Hpre Hf]]] Hh]].
      exists (arr_comp f h), a. split; [ exists f; cbn; auto |].
      cbn. exists b. auto.
  - (* app_ext *)
    match goal with
    | [ Hx : forall _, arrow_eq _ _ |- _ ] => rename Hx into Huv
    end.
    assert (Heq : u = v) by (extensionality x; exact (Huv x)).
    subst v. reflexivity.
Qed.

#[global]
Instance ArrowApplyLaws_PureDSLPostArr : ArrowApplyLaws PureDSLPostArr.
Proof.
  constructor; intros.
  - (* app_law *)
    apply PureDSLPostArr_eq; intros pre b. cbn. split.
    + intros H. apply (proj2_sig f). intros a Hra.
      exact (H f a Hra a eq_refl).
    + intros Hfb f0 a0 Hrel a' Heq.
      injection Heq as Hfeq Haeq. subst a' f0.
      apply (proj2_sig f) in Hfb. exact (Hfb a0 Hrel).
  - (* app_pair *)
    apply PureDSLPostArr_eq; intros pre q. cbn. split.
    + intros H p Hpq. subst q. destruct p as [x y].
      refine (H (arr_pure (fun y' : B => (x, y'))) y _ x eq_refl).
      cbn. reflexivity.
    + intros H g a Hrel x Hgx. subst g. cbn in Hrel. subst q.
      exact (H (x, a) eq_refl).
  - (* app_post *)
    apply PureDSLPostArr_eq; intros pre c. cbn. split.
    + intros H. apply (proj2_sig h). intros b Hh f a Hf.
      refine (H (arr_comp f h) a _ f eq_refl).
      cbn. exists b. auto.
    + intros H g a Hrel f Hgf. subst g. cbn in Hrel.
      destruct Hrel as [b [Hf Hh]].
      apply (proj2_sig h) in H. exact (H b Hh f a Hf).
  - (* app_ext *)
    match goal with
    | [ Hx : forall _, arrow_eq _ _ |- _ ] => rename Hx into Huv
    end.
    assert (Heq : u = v) by (extensionality x; exact (Huv x)).
    subst v. reflexivity.
Qed.

(* ================================================================= *)
(** ** Monad from ArrowApply (general construction)                   *)
(* ================================================================= *)

(** [Classes/ArrowMonad] supplies the generic arrow-monad operations.
    The concrete [MonadLawsE] proofs below concern the direct relational
    monads defined here. *)

Section PureASPostArrMonad.

  Variable I : Type.

  #[global]
  Instance Eq1_PureASPostArr : Eq1 (PureASPostArr I) :=
    fun _ => eq.

  #[global]
  Instance Eq1Equivalence_PureASPostArr
    : @Eq1Equivalence (PureASPostArr I) _ Eq1_PureASPostArr.
  Proof. constructor; typeclasses eauto. Qed.

  (** Define a direct monad on [PureASPostArr I] using relational
      composition, then show it equals [Monad_Arrow]. *)

  Definition ret_ASP {A} (a : A) : PureASPostArr I A :=
    mkASP (fun _ a' => a = a').

  (** For the angelic bind, we extract the underlying relation directly
      via [rel (proj1_sig ...)], mirroring the demonic bind. *)
  Definition bind_ASP {A B}
    (m : PureASPostArr I A) (k : A -> PureASPostArr I B)
    : PureASPostArr I B :=
    mkASP (fun i c => exists b,
             rel (proj1_sig m) i b /\
             rel (proj1_sig (k b)) i c).

  Instance Monad_PureASPostArr : Monad (PureASPostArr I) := {
    ret := @ret_ASP ;
    bind := @bind_ASP
  }.

  #[global]
  Instance MonadLawsE_PureASPostArr
    : @MonadLawsE (PureASPostArr I) Eq1_PureASPostArr
                   Monad_PureASPostArr.
  Proof.
    constructor; unfold eq1, Eq1_PureASPostArr.
    - (* bind_ret_l *)
      intros A B k x.
      apply PureASPostArr_eq; intros pre b. cbn.
      split.
      + intros [i [Hpre [b0 [Heq Hrel]]]]. subst b0.
        apply (proj2_sig (k x)). exists i. auto.
      + intros Hkx.
        apply (proj2_sig (k x)) in Hkx. destruct Hkx as [i [Hpre Hrel]].
        exists i. split; [exact Hpre|]. exists x. auto.
    - (* bind_ret_r *)
      intros A m.
      apply PureASPostArr_eq; intros pre b. cbn.
      split.
      + intros [i [Hpre [b0 [Hrel Heq]]]]. subst b0.
        apply (proj2_sig m). exists i. auto.
      + intros Hm.
        apply (proj2_sig m) in Hm. destruct Hm as [i [Hpre Hrel]].
        exists i. split; [exact Hpre|]. exists b. auto.
    - (* bind_bind *)
      intros A B C m f g.
      apply PureASPostArr_eq; intros pre c. cbn.
      split.
      + intros [i [Hpre [b0 [[a [Hm Hfa]] Hgb]]]].
        exists i. split; [exact Hpre|]. exists a. split; [exact Hm|].
        exists b0. auto.
      + intros [i [Hpre [a [Hm [b0 [Hfa Hgb]]]]]].
        exists i. split; [exact Hpre|]. exists b0. split.
        * exists a. auto.
        * exact Hgb.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. subst.
      assert (f = g) as -> by (apply functional_extensionality; exact Hfg).
      reflexivity.
  Qed.

End PureASPostArrMonad.

Section PureDSLPostArrMonad.

  Variable I : Type.

  #[global]
  Instance Eq1_PureDSLPostArr : Eq1 (PureDSLPostArr I) :=
    fun _ => eq.

  #[global]
  Instance Eq1Equivalence_PureDSLPostArr
    : @Eq1Equivalence (PureDSLPostArr I) _ Eq1_PureDSLPostArr.
  Proof. constructor; typeclasses eauto. Qed.

  Definition ret_DSLP {A} (a : A) : PureDSLPostArr I A :=
    mkDSLP (fun _ a' => a = a').

  (** For the demonic bind, we extract the underlying relation directly
      via [rel (proj1_sig ...)], avoiding classical axioms. *)
  Definition bind_DSLP {A B}
    (m : PureDSLPostArr I A) (k : A -> PureDSLPostArr I B)
    : PureDSLPostArr I B :=
    mkDSLP (fun i c => exists b,
             rel (proj1_sig m) i b /\
             rel (proj1_sig (k b)) i c).

  Instance Monad_PureDSLPostArr : Monad (PureDSLPostArr I) := {
    ret := @ret_DSLP ;
    bind := @bind_DSLP
  }.

  Lemma proj_mkDSLP {J B} (R : PredArr J B) pre b :
    spost (proj1_sig (mkDSLP R)) pre b <-> dslp R pre b.
  Proof. reflexivity. Qed.

  #[global]
  Instance MonadLawsE_PureDSLPostArr
    : @MonadLawsE (PureDSLPostArr I) Eq1_PureDSLPostArr
                   Monad_PureDSLPostArr.
  Proof.
    constructor; unfold eq1, Eq1_PureDSLPostArr.
    - (* bind_ret_l *)
      intros A B k x.
      apply PureDSLPostArr_eq; intros pre b. cbn.
      split.
      + intros H. apply (proj2_sig (k x)). intros a Hra.
        exact (H a (ex_intro _ x (conj eq_refl Hra))).
      + intros Hkx i [b0 [Heq Hrel]]. subst b0.
        apply (proj2_sig (k x)) in Hkx. exact (Hkx i Hrel).
    - (* bind_ret_r *)
      intros A m.
      apply PureDSLPostArr_eq; intros pre b. cbn.
      split.
      + intros H. apply (proj2_sig m). intros a Hra.
        exact (H a (ex_intro _ b (conj Hra eq_refl))).
      + intros Hm i [b0 [Hrel Heq]]. subst b0.
        apply (proj2_sig m) in Hm. exact (Hm i Hrel).
    - (* bind_bind *)
      intros A B C m f g.
      apply PureDSLPostArr_eq; intros pre c. cbn.
      split; intros H i Hex; apply H.
      + destruct Hex as [a [Hm [b0 [Hfa Hgb]]]].
        exists b0. split; [exists a; auto | exact Hgb].
      + destruct Hex as [b0 [[a [Hm Hfa]] Hgb]].
        exists a. split; [exact Hm | exists b0; auto].
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. subst.
      assert (f = g) as -> by (apply functional_extensionality; exact Hfg).
      reflexivity.
  Qed.

End PureDSLPostArrMonad.

(* ================================================================= *)
(** ** [optionT] and composed types: monad instances for free         *)
(* ================================================================= *)

(** [optionArrT arr I] is definitionally [optionT (arr I)], so the generic
    [MonadLawsE_optionT] and [MonadLawsE_stateT] from [TransformerLaws]
    extend [Monad_PureASPostArr] and [Monad_PureDSLPostArr] to
    [optionT (PureASPostArr I)] / [optionT (PureDSLPostArr I)] and their
    state stacks; typeclass resolution finds these instances automatically
    when they are needed. *)

(* ================================================================= *)
(** ** Arrow laws for composed types: [ASPostArr] and [DSPostArr]      *)
(* ================================================================= *)

(** All law instances below follow from the generic transformer laws
    in [OptionArrowT] and [StateArrowT].  We declare them explicitly
    to document which composed types carry which structure, and use
    [typeclasses eauto] or [:= _] to show that automatic resolution
    finds the proof. *)

Section OptionArrowLaws.

  (** Option-level laws: direct consequences of [ArrowLaws_optionArrT],
      [ArrowChoiceLaws_optionArrT], and [ArrowApplyLaws_optionArrT]
      applied to [PureASPostArr] / [PureDSLPostArr]. *)

  Local Instance ArrowEq_optionASPArr : ArrowEq optionASPArr := _.
  Local Instance ArrowLaws_optionASPArr : ArrowLaws optionASPArr := _.
  Local Instance ArrowChoiceLaws_optionASPArr : ArrowChoiceLaws optionASPArr := _.
  Local Instance ArrowApplyLaws_optionASPArr : ArrowApplyLaws optionASPArr := _.

  Local Instance ArrowEq_optionDSLPArr : ArrowEq optionDSLPArr := _.
  Local Instance ArrowLaws_optionDSLPArr : ArrowLaws optionDSLPArr := _.
  Local Instance ArrowChoiceLaws_optionDSLPArr : ArrowChoiceLaws optionDSLPArr := _.
  Local Instance ArrowApplyLaws_optionDSLPArr : ArrowApplyLaws optionDSLPArr := _.

End OptionArrowLaws.

Section ComposedArrowLaws.

  Variable S : Type.

  (** Composed-type laws: [stateArrT] applied to the option types above. *)

  #[global] Instance ArrowEq_stateOptASP :
    ArrowEq (stateArrT S optionASPArr) := _.
  #[global] Instance ArrowLaws_stateOptASP :
    ArrowLaws (stateArrT S optionASPArr) := _.
  #[global] Instance ArrowChoice_stateOptASP :
    ArrowChoice (stateArrT S optionASPArr) := _.
  #[global] Instance ArrowApply_stateOptASP :
    ArrowApply (stateArrT S optionASPArr) := _.
  #[global] Instance ArrowChoiceLaws_stateOptASP :
    ArrowChoiceLaws (stateArrT S optionASPArr) := _.
  #[global] Instance ArrowApplyLaws_stateOptASP :
    ArrowApplyLaws (stateArrT S optionASPArr) := _.

  #[global] Instance ArrowEq_stateOptDSLP :
    ArrowEq (stateArrT S optionDSLPArr) := _.
  #[global] Instance ArrowLaws_stateOptDSLP :
    ArrowLaws (stateArrT S optionDSLPArr) := _.
  #[global] Instance ArrowChoice_stateOptDSLP :
    ArrowChoice (stateArrT S optionDSLPArr) := _.
  #[global] Instance ArrowApply_stateOptDSLP :
    ArrowApply (stateArrT S optionDSLPArr) := _.
  #[global] Instance ArrowChoiceLaws_stateOptDSLP :
    ArrowChoiceLaws (stateArrT S optionDSLPArr) := _.
  #[global] Instance ArrowApplyLaws_stateOptDSLP :
    ArrowApplyLaws (stateArrT S optionDSLPArr) := _.

End ComposedArrowLaws.
