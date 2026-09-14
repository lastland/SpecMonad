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

    The structural equations below specialize the generic relational
    coherence lemmas from [RelArrowCoherence] through the coupled reading
    [fun A B f => rel (proj1_sig f)]: every per-operation relational law
    is definitionally [iff_refl] (see [ASP_rel_presentation] and
    [DSLP_rel_presentation]), and faithfulness is [ASP_rel_ext] /
    [DSLP_rel_ext].  The Proper fields remain direct equality
    substitutions.  [PureRelASPPairArr_eq] and [PureRelDSLPPairArr_eq]
    are still used by the application-law fields below. *)

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
Instance RelArrow_PureRelASPPairArr : RelArrow PureRelASPPairArr := {
  rel_reading := fun A B f => rel (proj1_sig f);
  rel_pure := fun _ _ _ _ _ => iff_refl _;
  rel_comp := fun _ _ _ _ _ _ _ => iff_refl _;
  rel_first := fun _ _ _ _ _ _ _ _ => iff_refl _;
}.

#[global]
Instance RelArrowChoice_PureRelASPPairArr : RelArrowChoice PureRelASPPairArr := {
  rel_left := fun _ _ _ _ _ _ => iff_refl _;
}.

#[global]
Instance RelArrowApply_PureRelASPPairArr : RelArrowApply PureRelASPPairArr := {
  rel_app := fun _ _ _ _ _ => iff_refl _;
}.

#[global]
Instance RelArrowEq_PureRelASPPairArr : RelArrowEq PureRelASPPairArr :=
  relArrowEq_leibniz ArrowEq_PureRelASPPairArr
    (fun _ _ _ _ => iff_refl _) (@ASP_rel_ext).

#[global]
Instance ArrowLaws_PureRelASPPairArr : ArrowLaws PureRelASPPairArr :=
  rel_arrow_laws.

#[global]
Instance ArrowChoiceLaws_PureRelASPPairArr : ArrowChoiceLaws PureRelASPPairArr :=
  rel_arrow_choice_laws.

#[global]
Instance ArrowApplyLaws_PureRelASPPairArr : ArrowApplyLaws PureRelASPPairArr :=
  rel_arrow_apply_laws.

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
Instance RelArrow_PureRelDSLPPairArr : RelArrow PureRelDSLPPairArr := {
  rel_reading := fun A B f => rel (proj1_sig f);
  rel_pure := fun _ _ _ _ _ => iff_refl _;
  rel_comp := fun _ _ _ _ _ _ _ => iff_refl _;
  rel_first := fun _ _ _ _ _ _ _ _ => iff_refl _;
}.

#[global]
Instance RelArrowChoice_PureRelDSLPPairArr : RelArrowChoice PureRelDSLPPairArr := {
  rel_left := fun _ _ _ _ _ _ => iff_refl _;
}.

#[global]
Instance RelArrowApply_PureRelDSLPPairArr : RelArrowApply PureRelDSLPPairArr := {
  rel_app := fun _ _ _ _ _ => iff_refl _;
}.

#[global]
Instance RelArrowEq_PureRelDSLPPairArr : RelArrowEq PureRelDSLPPairArr :=
  relArrowEq_leibniz ArrowEq_PureRelDSLPPairArr
    (fun _ _ _ _ => iff_refl _) (@DSLP_rel_ext).

#[global]
Instance ArrowLaws_PureRelDSLPPairArr : ArrowLaws PureRelDSLPPairArr :=
  rel_arrow_laws.

#[global]
Instance ArrowChoiceLaws_PureRelDSLPPairArr : ArrowChoiceLaws PureRelDSLPPairArr :=
  rel_arrow_choice_laws.

#[global]
Instance ArrowApplyLaws_PureRelDSLPPairArr : ArrowApplyLaws PureRelDSLPPairArr :=
  rel_arrow_apply_laws.

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
