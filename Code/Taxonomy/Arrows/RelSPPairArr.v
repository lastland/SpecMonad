(** * Predicate transformers and bundled predicate transformer arrows.

    Two readings turn a [Rel] relation into an SP transformer:

    [asp R pre b = exists a, pre a /\ R a b]   (angelic / existential)
    [dslp R pre b = forall a, R a b -> pre a]  (demonic liberal / universal)

    Both [PureRelASPPairArr] and [PureRelDSLPPairArr] are sigma types over
    [RelSPPair], a record that couples a strongest-postcondition
    transformer with its underlying relation arrow.  They differ only
    in the required agreement between transformer and relation:

    [PureRelASPPairArr A B] requires [spost d pre b <-> asp (rel d) pre b]
    [PureRelDSLPPairArr A B] requires [spost d pre b <-> dslp (rel d) pre b]

    Both use the same relational composition, so both satisfy
    the arrow laws (proved in this file).  The property-only presentation
    lives in [SPostArr.v]; [SPostArrEquiv.v] relates the two presentations.

    Composed types for specifications:

    [ASPostArr S A = stateArrT S (optionArrT PureRelASPPairArr) unit A]
    [DSLPostArr S A = stateArrT S (optionArrT PureRelDSLPPairArr) unit A]

    Their underlying arrows have input [unit * S] and output [option (A * S)].
    Qualify [ASPostArr] and [DSLPostArr] when the property-only presentation
    is also in scope: the two files use the same stack names. *)

From Coq Require Import Classical_Prop.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Classes Require Export ArrowMonad.

(* ================================================================= *)
(** ** Predicate transformers and shared record                         *)
(* ================================================================= *)

(** Predicate transformer view: strongest postcondition (angelic / existential).
  *)
Definition asp {A B} (R : Rel A B) (pre : A -> Prop) : B -> Prop :=
  fun b => exists a, pre a /\ R a b.

(* [asp_inv] evaluates singleton preconditions.  It recovers [R] from [asp R]
   by [asp_asp_inv].  The reverse round trip, [asp_inv_asp], is stated only
   for transformers in the image of [asp], not for arbitrary raw transformers.
   [SPostArrEquiv.v] relates the well-formed presentations and their stacks. *)
Definition asp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : Rel A B :=
  fun a b => pt (fun a' => a = a') b.

Theorem asp_asp_inv : forall {A B} (R : Rel A B) a b,
    asp_inv (asp R) a b <-> R a b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? ?]]. subst. assumption.
  - intros. exists a. tauto.
Qed.

(** [asp] at a singleton precondition [eq a] recovers the relation at [a].
    This is [asp_asp_inv] with [asp_inv] unfolded ([asp_inv pt a := pt (eq a)]),
    packaged for rewriting in strongest-postcondition sequencing laws. *)
Corollary asp_singleton : forall {A B} (R : Rel A B) (a : A) (b : B),
    asp R (eq a) b <-> R a b.
Proof.
  intros. unfold asp. split.
  - intros [a' [<- H]]. exact H.
  - intro H. exists a. auto.
Qed.

(* Cannot prove this for arbitrary [(A -> Prop) -> B -> Prop]. *)
Theorem asp_inv_asp : forall {A B} (R : Rel A B) pre b,
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
Definition dslp {A B} (R : Rel A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

(* [dslp_inv] intersects the preconditions accepted at [b].  For a [dslp R]
   reading, an input belongs to every such precondition exactly when it is
   a predecessor of [b]; [dslp_dslp_inv] proves that recovery. *)
Definition dslp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : Rel A B :=
  fun a b => forall pre, pt pre b -> pre a.

Theorem dslp_dslp_inv : forall {A B} (R : Rel A B) a b,
    dslp_inv (dslp R) a b <-> R a b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros ?. apply H. auto.
  - intros. auto.
Qed.

Theorem dslp_inv_dslp : forall {A B} (R : Rel A B) pre b,
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
  Variable R : Rel A B.

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
  rel : Rel A B
}.
Arguments mkRelSPPair {A B}.
Arguments spost {A B}.
Arguments rel {A B}.

(* ================================================================= *)
(** ** Angelic: [PureRelASPPairArr]                                       *)
(* ================================================================= *)

(** [PureRelASPPairArr] does not strictly need [RelSPPair] — it could remain
    as [{ f | IsASP f }] with a Prop-level existential (see
    [Taxonomy/deprecated/SPostArr.v]).  Using the shared record lets us
    reuse arrow operations, equality lemmas, and monad infrastructure
    between the angelic and demonic variants. *)
Definition PureRelASPPairArr (A B : Type) : Type :=
  { d : RelSPPair A B |
    forall pre b, spost d pre b <-> asp (rel d) pre b }.

(** Smart constructor: wrap a relation with [asp]. *)
#[program] Definition mkASP {A B} (R : Rel A B) : PureRelASPPairArr A B :=
  mkRelSPPair (asp R) R.
Next Obligation. reflexivity. Qed.

Section PureRelASPPairArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureRelASPPairArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_ASP {A B} (f : A -> B) : PureRelASPPairArr A B :=
    mkRelSPPair (fun pre b => exists a, pre a /\ f a = b) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_ASP {A B C}
    (f : PureRelASPPairArr A B) (g : PureRelASPPairArr B C) : PureRelASPPairArr A C :=
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
    (f : PureRelASPPairArr A B) : PureRelASPPairArr (A * C)%type (B * C)%type :=
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
  Instance Arrow_PureRelASPPairArr : Arrow PureRelASPPairArr := {
    arr_pure := @arr_pure_ASP ;
    arr_comp := @arr_comp_ASP ;
    arr_first := @arr_first_ASP
  }.

  #[local]
  #[program] Definition arr_app_ASP {A B}
    : PureRelASPPairArr (PureRelASPPairArr A B * A)%type B :=
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
  Instance ArrowApply_PureRelASPPairArr : ArrowApply PureRelASPPairArr := {
    arr_app := @arr_app_ASP
  }.

  (* -------------------------------------------------------------- *)
  (** *** ArrowChoice instance for [PureRelASPPairArr]                    *)
  (* -------------------------------------------------------------- *)

  Definition left_rel {A B C} (R : Rel A B) : Rel (A + C) (B + C) :=
    fun x y => match x, y with
      | inl a, inl b => R a b
      | inr c, inr c' => c = c'
      | _, _ => False
    end.

  #[local]
  #[program] Definition arr_left_ASP {A B C}
    (f : PureRelASPPairArr A B) : PureRelASPPairArr (A + C)%type (B + C)%type :=
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
  Instance ArrowChoice_PureRelASPPairArr : ArrowChoice PureRelASPPairArr := {
    arr_left := @arr_left_ASP
  }.

End PureRelASPPairArr.

(* ================================================================= *)
(** ** Demonic: [PureRelDSLPPairArr]                                       *)
(* ================================================================= *)

Definition PureRelDSLPPairArr (A B : Type) : Type :=
  { d : RelSPPair A B |
    forall pre b, spost d pre b <-> dslp (rel d) pre b }.

(** Smart constructor: wrap a relation with [dslp]. *)
#[program] Definition mkDSLP {A B} (R : Rel A B) : PureRelDSLPPairArr A B :=
  mkRelSPPair (dslp R) R.
Next Obligation. reflexivity. Qed.

Section PureRelDSLPPairArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureRelDSLPPairArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_DSLP {A B} (f : A -> B) : PureRelDSLPPairArr A B :=
    mkRelSPPair (fun pre b => forall a, f a = b -> pre a) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_DSLP {A B C}
    (f : PureRelDSLPPairArr A B) (g : PureRelDSLPPairArr B C) : PureRelDSLPPairArr A C :=
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
    (f : PureRelDSLPPairArr A B) : PureRelDSLPPairArr (A * C)%type (B * C)%type :=
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
  Instance Arrow_PureRelDSLPPairArr : Arrow PureRelDSLPPairArr := {
    arr_pure := @arr_pure_DSLP ;
    arr_comp := @arr_comp_DSLP ;
    arr_first := @arr_first_DSLP
  }.

  #[local]
  #[program] Definition arr_app_DSLP {A B}
    : PureRelDSLPPairArr (PureRelDSLPPairArr A B * A)%type B :=
    mkRelSPPair
      (fun pre b => forall f a, rel (proj1_sig f) a b -> pre (f, a))
      (fun '(f, a) b => rel f a b).
  Next Obligation.
    unfold dslp. split.
    - intros H [f0 a] Hfab. exact (H f0 a Hfab).
    - intros H f0 a Hfab. exact (H (f0, a) Hfab).
  Qed.

  #[global]
  Instance ArrowApply_PureRelDSLPPairArr : ArrowApply PureRelDSLPPairArr := {
    arr_app := @arr_app_DSLP
  }.

  (* -------------------------------------------------------------- *)
  (** *** ArrowChoice instance for [PureRelDSLPPairArr]                   *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_left_DSLP {A B C}
    (f : PureRelDSLPPairArr A B) : PureRelDSLPPairArr (A + C)%type (B + C)%type :=
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
  Instance ArrowChoice_PureRelDSLPPairArr : ArrowChoice PureRelDSLPPairArr := {
    arr_left := @arr_left_DSLP
  }.

End PureRelDSLPPairArr.

(* ================================================================= *)
(** ** Angelic and demonic option transformers                        *)
(* ================================================================= *)

(** [optionASPArr] and [optionDSLPArr] get their [Arrow], [ArrowChoice],
    and [ArrowApply] instances from the generic transformers in
    [OptionArrowT.v], via [ArrowChoice_PureRelASPPairArr] and
    [ArrowChoice_PureRelDSLPPairArr]. *)

Definition optionASPArr := optionArrT PureRelASPPairArr.
Definition optionDSLPArr := optionArrT PureRelDSLPPairArr.

(* ================================================================= *)
(** ** Composed types for specifications                              *)
(* ================================================================= *)

Section ComposedTypes.

  Variable S : Type.

  (** [ASPostArr S A] is the angelic strongest postcondition arrow.
      [ASPostArr S A = PureRelASPPairArr (unit * S) (option (A * S))] *)
  Definition ASPostArr (A : Type) : Type :=
    stateArrT S optionASPArr unit A.

  (** [DSLPostArr S A] is the demonic strongest liberal postcondition arrow.
      [DSLPostArr S A = PureRelDSLPPairArr (unit * S) (option (A * S))] *)
  Definition DSLPostArr (A : Type) : Type :=
    stateArrT S optionDSLPArr unit A.

End ComposedTypes.

(* ================================================================= *)
(** * Facts and laws                                                       *)
(* ================================================================= *)

(** * Arrow law proofs for angelic and demonic predicate transformer arrows.

    Angelic laws ([PureRelASPPairArr], [optionASPArr]) are proved by
    [PureRelASPPairArr_eq] and then transferring through [IsASP] to work
    with raw existentials.

    Demonic laws ([PureRelDSLPPairArr], [optionDSLPArr]) follow the same
    structure, using [IsDSLP] and raw universals. *)

From Coq Require Import FunctionalExtensionality PropExtensionality Morphisms.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.

(* ================================================================= *)
(** ** Utilities                                                       *)
(* ================================================================= *)

Lemma PureRelASPPairArr_eq {A B} (f g : PureRelASPPairArr A B) :
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

(** Faithfulness makes the generic relational application laws available
    here, before constructing the strengthened arrow law instances. *)
Lemma ASP_rel_ext {A B} (f g : PureRelASPPairArr A B) :
  (forall a b, rel (proj1_sig f) a b <-> rel (proj1_sig g) a b) -> f = g.
Proof.
  intro Hrel. apply PureRelASPPairArr_eq. intros pre b.
  split; intro H.
  - apply (proj2_sig f) in H. apply (proj2_sig g).
    destruct H as [a [Hpre Hr]]. exists a. split; [exact Hpre |].
    apply Hrel. exact Hr.
  - apply (proj2_sig g) in H. apply (proj2_sig f).
    destruct H as [a [Hpre Hr]]. exists a. split; [exact Hpre |].
    apply Hrel. exact Hr.
Qed.

Definition ASP_rel_presentation :
  RelArrowPresentation PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowChoice_PureRelASPPairArr ArrowApply_PureRelASPPairArr := {|
  present_rel := fun A B f => rel (proj1_sig f);
  present_ext := @ASP_rel_ext;
  present_pure := fun _ _ _ _ _ => iff_refl _;
  present_comp := fun _ _ _ _ _ _ _ => iff_refl _;
  present_first := fun _ _ _ _ _ _ _ _ => iff_refl _;
  present_left := fun _ _ _ _ _ _ => iff_refl _;
  present_app := fun _ _ _ _ _ => iff_refl _
|}.

Lemma IsASP_rewrite {A B} (f : PureRelASPPairArr A B) :
  exists R : Rel A B,
    forall pre b, spost (proj1_sig f) pre b <-> exists a, pre a /\ R a b.
Proof.
  exists (rel (proj1_sig f)). intros pre b.
  apply (proj2_sig f).
Qed.

(** [spost] of any PureRelASPPairArr rewrites to existential form. *)
Lemma ASP_asp {A B} (f : PureRelASPPairArr A B) (R : Rel A B)
  (HR : forall pre b, spost (proj1_sig f) pre b <-> exists a, pre a /\ R a b) :
  forall P b, spost (proj1_sig f) P b <-> exists a, P a /\ R a b.
Proof. exact HR. Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [PureRelASPPairArr]                                 *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PureRelASPPairArr : ArrowEq PureRelASPPairArr := {
  arrow_eq := fun A B => @eq (PureRelASPPairArr A B)
}.

Lemma id_pred {A} (pre : A -> Prop) :
  (fun b => exists a, pre a /\ a = b) = pre.
Proof.
  extensionality b. apply propositional_extensionality. sauto limit: 200.
Qed.

#[global]
Instance ArrowLaws_PureRelASPPairArr : ArrowLaws PureRelASPPairArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureRelASPPairArr_eq; intros pre b. cbn.
    rewrite id_pred. reflexivity.

  - (* comp_id_r: arr_comp f arr_id = f *)
    apply PureRelASPPairArr_eq; intros pre b. cbn. sauto limit: 200.

  - (* comp_assoc *)
    apply PureRelASPPairArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp *)
    apply PureRelASPPairArr_eq; intros pre c. cbn. sauto limit: 200.

  - (* first_pure *)
    apply PureRelASPPairArr_eq; intros pre [b d]. cbn. sauto limit: 200.

  - (* first_comp *)
    apply PureRelASPPairArr_eq; intros pre [c d]. cbn. reflexivity.

  - (* first_fst — requires IsASP for additivity *)
    apply PureRelASPPairArr_eq; intros pre b. cbn.
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
    apply PureRelASPPairArr_eq; intros pre [b [c d]]. cbn.
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
    unfold Proper, respectful, arrow_eq, ArrowEq_PureRelASPPairArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureRelASPPairArr;
    intros; subst; reflexivity.
  - (* first_natural *)
    apply ASP_rel_ext; intros [a c] [b d]. cbn. split.
    + intros [[b0 c0] [[Hf Hc] Heq]]. cbn in Heq. subst c0.
      injection Heq as Hb Hd. subst b0 d.
      exists (a, g c). cbn. auto.
    + intros [[a0 d0] [Heq [Hf Hd]]].
      injection Heq as Ha Hg. subst a0 d0 d.
      exists (b, c). cbn. auto.
Qed.

(* ================================================================= *)
(** ** [ArrowChoiceLaws] for [PureRelASPPairArr]                           *)
(* ================================================================= *)

#[global]
Instance ArrowChoiceLaws_PureRelASPPairArr : ArrowChoiceLaws PureRelASPPairArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    apply PureRelASPPairArr_eq; intros pre [b|c]; cbn; unfold sum_bimap; sauto limit: 200.
  - (* left_comp *)
    apply PureRelASPPairArr_eq; intros pre [c|d]; cbn; reflexivity.
  - (* left_inl *)
    apply PureRelASPPairArr_eq; intros pre [b|c]; cbn.
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
    apply PureRelASPPairArr_eq; intros pre [b | [c | d]]; cbn.
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
      apply PureRelASPPairArr_eq; intros pre [b|c']; cbn.
      + (* inl b: both sides should be False *)
        destruct (IsASP_rewrite f) as [Rf Hf].
        rewrite Hf. unfold asp.
        split; intros H; exfalso.
        * destruct H as [a [[c0 [_ Habs]] _]]. discriminate.
        * destruct H as [c0 [_ Habs]]. discriminate.
      + (* inr c': both sides give pre c' after simplification *)
        sauto limit: 200.
    - (* left_natural *)
      apply PureRelASPPairArr_eq; intros pre [b|d]; cbn; unfold sum_bimap.
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
      apply PureRelASPPairArr_eq; intros pre y.
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
      unfold Proper, respectful, arrow_eq, ArrowEq_PureRelASPPairArr;
      intros; subst; reflexivity.
Qed.
(* ================================================================= *)
(** ** Utilities for [PureRelDSLPPairArr]                                   *)
(* ================================================================= *)

Lemma PureRelDSLPPairArr_eq {A B} (f g : PureRelDSLPPairArr A B) :
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

Lemma DSLP_rel_ext {A B} (f g : PureRelDSLPPairArr A B) :
  (forall a b, rel (proj1_sig f) a b <-> rel (proj1_sig g) a b) -> f = g.
Proof.
  intro Hrel. apply PureRelDSLPPairArr_eq. intros pre b.
  split; intro H.
  - apply (proj2_sig f) in H. apply (proj2_sig g).
    intros a Hr. apply H. apply Hrel. exact Hr.
  - apply (proj2_sig g) in H. apply (proj2_sig f).
    intros a Hr. apply H. apply Hrel. exact Hr.
Qed.

Definition DSLP_rel_presentation :
  RelArrowPresentation PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
    ArrowChoice_PureRelDSLPPairArr ArrowApply_PureRelDSLPPairArr := {|
  present_rel := fun A B f => rel (proj1_sig f);
  present_ext := @DSLP_rel_ext;
  present_pure := fun _ _ _ _ _ => iff_refl _;
  present_comp := fun _ _ _ _ _ _ _ => iff_refl _;
  present_first := fun _ _ _ _ _ _ _ _ => iff_refl _;
  present_left := fun _ _ _ _ _ _ => iff_refl _;
  present_app := fun _ _ _ _ _ => iff_refl _
|}.

Lemma IsDSLP_rewrite {A B} (f : PureRelDSLPPairArr A B) :
  exists R : Rel A B,
    forall pre b, spost (proj1_sig f) pre b <-> forall a, R a b -> pre a.
Proof.
  exists (rel (proj1_sig f)). intros pre b.
  apply (proj2_sig f).
Qed.

Lemma DSLP_dslp {A B} (f : PureRelDSLPPairArr A B) (R : Rel A B)
  (HR : forall pre b, spost (proj1_sig f) pre b <-> forall a, R a b -> pre a) :
  forall P b, spost (proj1_sig f) P b <-> forall a, R a b -> P a.
Proof. exact HR. Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [PureRelDSLPPairArr]                                *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PureRelDSLPPairArr : ArrowEq PureRelDSLPPairArr := {
  arrow_eq := fun A B => @eq (PureRelDSLPPairArr A B)
}.

Lemma id_pred_dslp {A} (pre : A -> Prop) :
  (fun b => forall a, a = b -> pre a) = pre.
Proof.
  extensionality b. apply propositional_extensionality. sauto limit: 200.
Qed.

#[global]
Instance ArrowLaws_PureRelDSLPPairArr : ArrowLaws PureRelDSLPPairArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureRelDSLPPairArr_eq; intros pre b. cbn.
    rewrite id_pred_dslp. reflexivity.

  - (* comp_id_r *)
    apply PureRelDSLPPairArr_eq; intros pre b. cbn. sauto limit: 200.

  - (* comp_assoc *)
    apply PureRelDSLPPairArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp *)
    apply PureRelDSLPPairArr_eq; intros pre c. cbn. sauto limit: 200.

  - (* first_pure *)
    apply PureRelDSLPPairArr_eq; intros pre [b d]. cbn. sauto limit: 200.

  - (* first_comp *)
    apply PureRelDSLPPairArr_eq; intros pre [c d]. cbn. reflexivity.

  - (* first_fst — requires IsDSLP for multiplicativity.
       Both sides reduce (via IsDSLP) to quantifier reordering:
       ∀c ∀a, R a b → pre(a,c) ↔ ∀a, R a b → ∀c, pre(a,c). *)
    apply PureRelDSLPPairArr_eq; intros pre b.
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
    apply PureRelDSLPPairArr_eq; intros pre [b [c d]].
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
    unfold Proper, respectful, arrow_eq, ArrowEq_PureRelDSLPPairArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureRelDSLPPairArr;
    intros; subst; reflexivity.
  - (* first_natural *)
    apply DSLP_rel_ext; intros [a c] [b d]. cbn. split.
    + intros [[b0 c0] [[Hf Hc] Heq]]. cbn in Heq. subst c0.
      injection Heq as Hb Hd. subst b0 d.
      exists (a, g c). cbn. auto.
    + intros [[a0 d0] [Heq [Hf Hd]]].
      injection Heq as Ha Hg. subst a0 d0 d.
      exists (b, c). cbn. auto.
Qed.

(* ================================================================= *)
(** ** [ArrowChoiceLaws] for [PureRelDSLPPairArr]                          *)
(* ================================================================= *)

#[global]
Instance ArrowChoiceLaws_PureRelDSLPPairArr : ArrowChoiceLaws PureRelDSLPPairArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    apply PureRelDSLPPairArr_eq; intros pre [b|c]; cbn; unfold sum_bimap;
    sauto limit: 200.
  - (* left_comp *)
    apply PureRelDSLPPairArr_eq; intros pre [c|d]; cbn; reflexivity.
  - (* left_inl *)
    apply PureRelDSLPPairArr_eq; intros pre [b|c]; cbn.
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
    apply PureRelDSLPPairArr_eq; intros pre [b | [c | d]]; cbn.
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
      apply PureRelDSLPPairArr_eq; intros pre [b|c']; cbn.
      + destruct (IsDSLP_rewrite f) as [Rf Hf]. split.
        * intros _ c0 Habs. discriminate.
        * intros _. rewrite Hf. intros a _ c0 Habs. discriminate.
      + split; intros H c0 Heq; injection Heq as Heq; subst; exact (H c' eq_refl).
    - (* left_natural *)
      apply PureRelDSLPPairArr_eq; intros pre [b|d]; cbn; unfold sum_bimap.
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
      apply PureRelDSLPPairArr_eq; intros pre y.
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
      unfold Proper, respectful, arrow_eq, ArrowEq_PureRelDSLPPairArr;
      intros; subst; reflexivity.
Qed.


(* ================================================================= *)
(** ** [ArrowApplyLaws] for [PureRelASPPairArr] and [PureRelDSLPPairArr]       *)
(* ================================================================= *)

#[global]
Instance ArrowApplyLaws_PureRelASPPairArr : ArrowApplyLaws PureRelASPPairArr.
Proof.
  constructor.
  - intros A B f. apply PureRelASPPairArr_eq; intros pre b. cbn.
    split.
    + (* Forward: (∃f0 a, (∃a', pre a' ∧ (f,a')=(f0,a)) ∧ rel f0 a b) → spost f pre b *)
      intros [f0 [a [[a' [Hpre Hpair]] Hfa]]].
      inversion Hpair; subst f0 a.
      apply (proj2_sig f). unfold asp. exists a'. auto.
    + (* Backward: spost f pre b → ... *)
      intros Hfb.
      apply (proj2_sig f) in Hfb. unfold asp in Hfb.
      destruct Hfb as [a [Hpre Hra]].
      exists f, a. split; [exists a; auto | exact Hra].
  - exact (rel_app_unit ASP_rel_presentation).
  - intros A B C g. exact (rel_app_precompose ASP_rel_presentation g).
  - intros A B C h. exact (rel_app_postcompose ASP_rel_presentation h).
  - intros X A B u v H.
    assert (Heq : u = v).
    { extensionality x. specialize (H x).
      destruct (u x) as [f a], (v x) as [g b].
      cbn in H. destruct H as [-> ->]. reflexivity. }
    subst v. reflexivity.
Qed.

#[global]
Instance ArrowApplyLaws_PureRelDSLPPairArr : ArrowApplyLaws PureRelDSLPPairArr.
Proof.
  constructor.
  - intros A B f. apply PureRelDSLPPairArr_eq; intros pre b. cbn.
    split.
    + (* Forward: (∀f0 a, rel (proj1_sig f0) a b → pre (f, a)) → spost (proj1_sig f) pre b *)
      intros H. apply (proj2_sig f). intros a Hra.
      exact (H f a Hra a eq_refl).
    + (* Backward: spost (proj1_sig f) pre b → (∀f0 a, rel (proj1_sig f0) a b → pre (f, a)) *)
      intros Hfb f0 a0 Hrel a' Heq.
      injection Heq as Hfeq Haeq. subst a' f0.
      apply (proj2_sig f) in Hfb. exact (Hfb a0 Hrel).
  - exact (rel_app_unit DSLP_rel_presentation).
  - intros A B C g. exact (rel_app_precompose DSLP_rel_presentation g).
  - intros A B C h. exact (rel_app_postcompose DSLP_rel_presentation h).
  - intros X A B u v H.
    assert (Heq : u = v).
    { extensionality x. specialize (H x).
      destruct (u x) as [f a], (v x) as [g b].
      cbn in H. destruct H as [-> ->]. reflexivity. }
    subst v. reflexivity.
Qed.

(* ================================================================= *)
(** ** Monad from ArrowApply (general construction)                   *)
(* ================================================================= *)

(** [Classes/ArrowMonad] supplies the operations and laws through generic
    instances.  Only [Eq1] is registered here, to select the arrow
    equality; the concrete monad/law dictionaries, the compact
    relational [ret]/[bind] descriptions, and their agreement facts are
    collected in [Tests/ArrowMonadInstances.v]. *)

Section PureRelASPPairArrMonad.

  Variable I : Type.

  #[global]
  Instance Eq1_PureRelASPPairArr : Eq1 (PureRelASPPairArr I) :=
    @Eq1_Arrow PureRelASPPairArr ArrowEq_PureRelASPPairArr I.

End PureRelASPPairArrMonad.

Section PureRelDSLPPairArrMonad.

  Variable I : Type.

  #[global]
  Instance Eq1_PureRelDSLPPairArr : Eq1 (PureRelDSLPPairArr I) :=
    @Eq1_Arrow PureRelDSLPPairArr ArrowEq_PureRelDSLPPairArr I.

End PureRelDSLPPairArrMonad.

(** The generic [MonadLawsE_optionT] and [MonadLawsE_stateT] instances from
    [TransformerLaws] extend these arrow-derived monads to
    [optionT (PureRelASPPairArr I)] / [optionT (PureRelDSLPPairArr I)] and
    their state stacks.  Generic instances handle typeclass resolution;
    no per-stack dictionaries are registered for the coupled
    presentation.  The option-level and state-over-option resolution
    checks live in [Tests/ArrowTransformerInstances.v]. *)
