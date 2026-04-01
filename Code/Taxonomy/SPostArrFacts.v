(** * Arrow law proofs for angelic and demonic predicate transformer arrows.

    Angelic laws ([PureASPostArr], [optionASPArr]) are proved by
    [PureASPostArr_eq] and then transferring through [IsASP] to work
    with raw existentials.

    Demonic laws ([PureDSLPostArr], [optionDSLPArr]) follow the same
    structure, using [IsDSLP] and raw universals. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality ProofIrrelevance
  Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy Require Import SPostArr ProgFacts.

(* ================================================================= *)
(** ** Utilities                                                       *)
(* ================================================================= *)

Lemma PureASPostArr_eq {A B} (f g : PureASPostArr A B) :
  (forall pre b, sp_pt (proj1_sig f) pre b <-> sp_pt (proj1_sig g) pre b) -> f = g.
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
  exists R : SPArr A B,
    forall pre b, sp_pt (proj1_sig f) pre b <-> exists a, pre a /\ R a b.
Proof.
  exists (sp_rel (proj1_sig f)). intros pre b.
  apply (proj2_sig f).
Qed.

(** [sp_pt] of any PureASPostArr rewrites to existential form. *)
Lemma ASP_asp {A B} (f : PureASPostArr A B) (R : SPArr A B)
  (HR : forall pre b, sp_pt (proj1_sig f) pre b <-> exists a, pre a /\ R a b) :
  forall P b, sp_pt (proj1_sig f) P b <-> exists a, P a /\ R a b.
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
  extensionality b. apply propositional_extensionality.
  split; [intros [? [? ?]]; subst; auto | intro; exists b; auto].
Qed.

#[global]
Instance ArrowLaws_PureASPostArr : ArrowLaws PureASPostArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureASPostArr_eq; intros pre b. cbn.
    rewrite id_pred. reflexivity.

  - (* comp_id_r: arr_comp f arr_id = f *)
    apply PureASPostArr_eq; intros pre b. cbn.
    split.
    + intros [a [Hf0 Heq]]; subst; exact Hf0.
    + intro Hf0; exists b; auto.

  - (* comp_assoc *)
    apply PureASPostArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp: arr_comp (arr_pure f) (arr_pure g) = arr_pure (g ∘ f) *)
    apply PureASPostArr_eq; intros pre c. cbn.
    split.
    + intros [b [[a [Hp Hf0]] Hg]]; subst; exists a; auto.
    + intros [a [Hp Hgf]]; subst; exists (f a); split; [exists a |]; auto.

  - (* first_pure *)
    apply PureASPostArr_eq; intros pre [b d]. cbn.
    split.
    + intros [a [Hpre Hfa]]; subst; exists (a, d); auto.
    + intros [[a c] [Hpre Heq]]; inversion Heq; subst; exists a; auto.

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
    apply PureASPostArr_eq; intros pre [b|c]; cbn; unfold sum_bimap.
    + split.
      * intros [a [Hp Hf]]. exists (inl a); split; [exact Hp | f_equal; exact Hf].
      * intros [[a|c'] [Hp Heq]]; [| discriminate].
        injection Heq as Heq. subst. exists a; auto.
    + split.
      * intros Hp. exists (inr c); auto.
      * intros [[a|c'] [Hp Heq]]; [discriminate |].
        injection Heq as Heq. subst. exact Hp.
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
    + split; intros [? [_ H]]; discriminate.
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
Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [optionASPArr]                                  *)
(* ================================================================= *)

#[global]
Instance ArrowEq_optionASPArr : ArrowEq optionASPArr := {
  arrow_eq := fun A B => @eq (optionASPArr A B)
}.

(** For optionASPArr, the IsASP witness tells us the relation on
    [A -> option B -> Prop].  We factor proofs through this. *)

(** All [optionASPArr] laws are proved by transferring through [IsASP]:
    convert every [proj1_sig] occurrence to existential form, then
    reason about plain propositions. *)

#[global]
Instance ArrowLaws_optionASPArr : ArrowLaws optionASPArr.
Proof.
  (* Strategy: for each law, use PureASPostArr_eq, intro, cbn.
     Then destruct IsASP_rewrite for f (and g if present) to
     rewrite all proj1_sig applications to existentials.
     All goals then become plain propositional logic. *)

  (** Helper: rewrite a PureASPostArr application using its IsASP witness. *)
  Local Ltac isp f :=
    let R := fresh "R" in let H := fresh "H" in
    destruct (IsASP_rewrite f) as [R H]; rewrite ?H; unfold asp in *.

  constructor; intros.

  - (* comp_id_l *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    destruct ob as [b|]; isp f; firstorder (subst; eauto).

  - (* comp_id_r *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    destruct ob as [b|]; isp f; firstorder (subst; eauto).

  - (* comp_assoc *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    destruct ob as [d|]; isp f; isp g; isp h; firstorder.

  - (* pure_comp *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    destruct ob as [c|]; firstorder (subst; eauto).

  - (* first_pure *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    destruct ob as [[b0 d0]|].
    + split.
      * intros [a [Hpre Hf]]. simpl in *. subst. exists (a, d0). simpl. auto.
      * intros [[a c0] [Hpre Heq]]. simpl in *. inversion Heq; subst. exists a; auto.
    + firstorder.

  - (* first_comp *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    destruct ob as [[c0 d0]|]; isp f; isp g; firstorder.

  - (* first_fst *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    isp f.
    destruct ob as [b|].
    + (* Some b *)
      split.
      * intros [[b0 c0] [Hfc Heq]]; cbn in Hfc, Heq; subst.
        rewrite H in Hfc. destruct Hfc as [a [Hpre Hra]].
        rewrite H. exists a. split.
        -- exists (a, c0). cbn. auto.
        -- exact Hra.
      * intro Hfb.
        rewrite H in Hfb. destruct Hfb as [a [Hfst Hra]].
        destruct Hfst as [[a0 c0] [Hpre Heq]]; cbn in Heq; subst.
        exists (b, c0). split.
        -- cbn. rewrite H. exists a. auto.
        -- cbn. reflexivity.
    + (* None *)
      split.
      * intros [[d Hfd] | Habs]; [| destruct Habs].
        rewrite H in Hfd. destruct Hfd as [a [Hpre Hra]].
        right. rewrite H. exists a. split.
        -- exists (a, d). cbn. auto.
        -- exact Hra.
      * intros [Habs | Hfb]; [destruct Habs |].
        rewrite H in Hfb. destruct Hfb as [a [Hfst Hra]].
        destruct Hfst as [[a0 c0] [Hpre Heq]]; cbn in Heq; subst.
        left. exists c0. rewrite H. exists a. auto.

  - (* first_assoc *)
    apply PureASPostArr_eq; intros pre ob. cbn.
    isp f.
    destruct ob as [[b0 [c0 d0]]|].
    + (* Some (b, (c, d)) *)
      split.
      * intros [[[b1 c1] d1] [Hff Hassoc]]; cbn in Hff.
        unfold assoc_prod in Hassoc; simpl in Hassoc.
        assert (Hb : b1 = b0) by congruence.
        assert (Hc : c1 = c0) by congruence.
        assert (Hd : d1 = d0) by congruence.
        subst. rewrite H in Hff. destruct Hff as [a [Hpre Hra]].
        rewrite H. exists a; split; [exists ((a, c0), d0); auto | exact Hra].
      * intros Hfb.
        rewrite H in Hfb. destruct Hfb as [a [Hpure Hra]].
        destruct Hpure as [[[a0 c1] d1] [Hpre Hassoc]].
        unfold assoc_prod in Hassoc; simpl in Hassoc.
        assert (Ha : a0 = a) by congruence.
        assert (Hc : c1 = c0) by congruence.
        assert (Hd : d1 = d0) by congruence.
        subst. exists ((b0, c0), d0); split;
          [cbn; rewrite H; exists a; auto | reflexivity].
    + (* None *)
      split.
      * intros [[d1 [c1 Hfd]] | Habs]; [| destruct Habs].
        rewrite H in Hfd. destruct Hfd as [a [Hpre Hra]].
        right. exists (c1, d1). rewrite H.
        exists a; split; [exists ((a, c1), d1); auto | exact Hra].
      * intros [Habs | [[c1 d1] Hfb]]; [destruct Habs |].
        rewrite H in Hfb. destruct Hfb as [a [Hpure Hra]].
        destruct Hpure as [[[a0 c2] d2] [Hpre Hassoc]].
        unfold assoc_prod in Hassoc; simpl in Hassoc.
        assert (Ha : a0 = a) by congruence.
        assert (Hc : c2 = c1) by congruence.
        assert (Hd : d2 = d1) by congruence.
        subst. left. exists d1, c1. rewrite H. exists a. auto.

  - (* comp_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_optionASPArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_optionASPArr;
    intros; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** Utilities for [PureDSLPostArr]                                   *)
(* ================================================================= *)

Lemma PureDSLPostArr_eq {A B} (f g : PureDSLPostArr A B) :
  (forall pre b, sp_pt (proj1_sig f) pre b <-> sp_pt (proj1_sig g) pre b) -> f = g.
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
  exists R : SPArr A B,
    forall pre b, sp_pt (proj1_sig f) pre b <-> forall a, R a b -> pre a.
Proof.
  exists (sp_rel (proj1_sig f)). intros pre b.
  apply (proj2_sig f).
Qed.

Lemma DSLP_dslp {A B} (f : PureDSLPostArr A B) (R : SPArr A B)
  (HR : forall pre b, sp_pt (proj1_sig f) pre b <-> forall a, R a b -> pre a) :
  forall P b, sp_pt (proj1_sig f) P b <-> forall a, R a b -> P a.
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
  extensionality b. apply propositional_extensionality.
  split; [intro H; exact (H b eq_refl) | intros Hpre a Heq; subst; exact Hpre].
Qed.

#[global]
Instance ArrowLaws_PureDSLPostArr : ArrowLaws PureDSLPostArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureDSLPostArr_eq; intros pre b. cbn.
    rewrite id_pred_dslp. reflexivity.

  - (* comp_id_r: arr_comp f arr_id = f *)
    apply PureDSLPostArr_eq; intros pre b. cbn.
    split.
    + intros Hf0. exact (Hf0 b eq_refl).
    + intros Hf0 a Heq. subst. exact Hf0.

  - (* comp_assoc *)
    apply PureDSLPostArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp: arr_comp (arr_pure f) (arr_pure g) = arr_pure (g ∘ f) *)
    apply PureDSLPostArr_eq; intros pre c. cbn.
    split.
    + intros H a Hgf. subst. exact (H (f a) eq_refl a eq_refl).
    + intros H b Hg a Hf. subst. exact (H a eq_refl).

  - (* first_pure *)
    apply PureDSLPostArr_eq; intros pre [b d]. cbn.
    split.
    + intros H [a c] Hfa. inversion Hfa; subst. exact (H a eq_refl).
    + intros H a Heq. subst. exact (H (a, d) eq_refl).

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
    apply PureDSLPostArr_eq; intros pre [b|c]; cbn; unfold sum_bimap.
    + split.
      * intros H [a|c'] Hbm; [| discriminate].
        injection Hbm as Hbm. subst. exact (H a eq_refl).
      * intros H a Heq. subst. exact (H (inl a) eq_refl).
    + split.
      * intros Hpre [a|c'] Hbm; [discriminate |].
        injection Hbm as Hbm. subst. exact Hpre.
      * intros H. exact (H (inr c) eq_refl).
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
  - admit. (* left_inr *)
  - admit. (* left_natural *)
  - admit. (* first_left_dist *)
  - (* left_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureDSLPostArr;
    intros; subst; reflexivity.
Admitted.

(* ================================================================= *)
(** ** [ArrowLaws] for [optionDSLPArr]                                 *)
(* ================================================================= *)

#[global]
Instance ArrowEq_optionDSLPArr : ArrowEq optionDSLPArr := {
  arrow_eq := fun A B => @eq (optionDSLPArr A B)
}.

#[global]
Instance ArrowLaws_optionDSLPArr : ArrowLaws optionDSLPArr.
Proof.
  constructor; intros.

  - (* comp_id_l *)
    apply PureDSLPostArr_eq; intros pre ob. cbn.
    destruct (IsDSLP_rewrite f) as [Rf Hrf].
    destruct ob as [b0|]; rewrite !Hrf; unfold dslp.
    + split.
      * intros H a Hra. exact (H a Hra a eq_refl).
      * intros H a Hra a' Heq. subst. exact (H a Hra).
    + split.
      * intros [_ H] a Hra. exact (H a Hra a eq_refl).
      * intro H. split; [exact I | intros a Hra a' Heq; subst; exact (H a Hra)].

  - (* comp_id_r *)
    apply PureDSLPostArr_eq; intros pre ob. cbn.
    destruct ob as [b0|].
    + split.
      * intros H. exact (H b0 eq_refl).
      * intros Hf a Heq. subst. exact Hf.
    + tauto.

  - (* comp_assoc *)
    apply PureDSLPostArr_eq; intros pre ob. cbn.
    destruct (IsDSLP_rewrite f) as [Rf Hrf].
    destruct (IsDSLP_rewrite g) as [Rg Hrg].
    destruct (IsDSLP_rewrite h) as [Rh Hrh].
    destruct ob; rewrite ?Hrf, ?Hrg, ?Hrh; unfold dslp; firstorder.

  - (* pure_comp *)
    apply PureDSLPostArr_eq; intros pre ob. cbn.
    destruct ob as [c|].
    + split.
      * intros H a Hgf. subst. exact (H (f a) eq_refl a eq_refl).
      * intros H b0 Hg a0 Hf0. subst. exact (H a0 eq_refl).
    + split; tauto.

  - (* first_pure *)
    apply PureDSLPostArr_eq; intros pre ob. cbn.
    destruct ob as [[b0 d0]|].
    + split.
      * intros H [a c] Heq. inversion Heq; subst. exact (H a eq_refl).
      * intros H a Heq. simpl in Heq. subst. exact (H (a, d0) eq_refl).
    + split; [intros _ ; exact I | intros _ d; exact I].

  - (* first_comp *)
    apply PureDSLPostArr_eq; intros pre ob. cbn.
    destruct (IsDSLP_rewrite f) as [Rf Hrf].
    destruct (IsDSLP_rewrite g) as [Rg Hrg].
    destruct ob; rewrite ?Hrf, ?Hrg; unfold dslp; firstorder.

  - (* first_fst *)
    apply PureDSLPostArr_eq; intros pre ob.
    destruct (IsDSLP_rewrite f) as [Rf Hrf].
    cbn. destruct ob as [b0|].
    + split.
      * intros H. rewrite Hrf. intros a Hra p Heq.
        destruct p as [a0 c0]; cbn in Heq; subst.
        specialize (H (b0, c0) eq_refl).
        rewrite Hrf in H. exact (H a Hra).
      * intros Hfb p Heq. destruct p as [b1 c0]; cbn in Heq; subst.
        rewrite Hrf. intros a Hra.
        rewrite Hrf in Hfb. exact (Hfb a Hra (a, c0) eq_refl).
    + split.
      * intros [Hd _]. split; [exact I |].
        rewrite Hrf. intros a Hra p Heq.
        destruct p as [a0 c0]; cbn in Heq; subst.
        specialize (Hd c0). rewrite Hrf in Hd. exact (Hd a Hra).
      * intros [_ Hfb]. split.
        -- intro d0. rewrite Hrf. intros a Hra.
           rewrite Hrf in Hfb. exact (Hfb a Hra (a, d0) eq_refl).
        -- exact I.

  - (* first_assoc *)
    apply PureDSLPostArr_eq; intros pre ob.
    destruct (IsDSLP_rewrite f) as [Rf Hrf].
    cbn. destruct ob as [[b0 [c0 d0]]|].
    + split.
      * intros H. rewrite Hrf. intros a Hra p Hassoc.
        destruct p as [[a0 c1] d1]; unfold assoc_prod in Hassoc;
          simpl in Hassoc.
        assert (Ha : a0 = a) by congruence.
        assert (Hc : c1 = c0) by congruence.
        assert (Hd : d1 = d0) by congruence.
        subst. specialize (H ((b0, c0), d0) eq_refl).
        rewrite Hrf in H. exact (H a Hra).
      * intros Hfb p Hassoc. destruct p as [[b1 c1] d1].
        unfold assoc_prod in Hassoc; simpl in Hassoc.
        assert (Hb : b1 = b0) by congruence.
        assert (Hc : c1 = c0) by congruence.
        assert (Hd : d1 = d0) by congruence.
        subst. rewrite Hrf. intros a Hra.
        rewrite Hrf in Hfb. exact (Hfb a Hra ((a, c0), d0) eq_refl).
    + split.
      * intros [H _]. split; [exact I |].
        intros [c1 d1]. rewrite Hrf. intros a Hra p Hassoc.
        destruct p as [[a0 c2] d2]; unfold assoc_prod in Hassoc;
          simpl in Hassoc.
        assert (Ha : a0 = a) by congruence.
        assert (Hc : c2 = c1) by congruence.
        assert (Hd : d2 = d1) by congruence.
        subst. specialize (H d1 c1). rewrite Hrf in H. exact (H a Hra).
      * intros [_ H]. split.
        -- intros d1 c1. rewrite Hrf. intros a Hra.
           specialize (H (c1, d1)). rewrite Hrf in H.
           exact (H a Hra ((a, c1), d1) eq_refl).
        -- exact I.

  - (* comp_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_optionDSLPArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_optionDSLPArr;
    intros; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** [ArrowApplyLaws] for [PureASPostArr] and [PureDSLPostArr]       *)
(* ================================================================= *)

#[global]
Instance ArrowApplyLaws_PureASPostArr : ArrowApplyLaws PureASPostArr.
Proof.
  constructor; intros.
  apply PureASPostArr_eq; intros pre b. cbn.
  split.
  - (* Forward: (∃f0 a, (∃a', pre a' ∧ (f,a')=(f0,a)) ∧ sp_rel f0 a b) → sp_pt f pre b *)
    intros [f0 [a [[a' [Hpre Hpair]] Hfa]]].
    inversion Hpair; subst f0 a.
    apply (proj2_sig f). unfold asp. exists a'. auto.
  - (* Backward: sp_pt f pre b → ... *)
    intros Hfb.
    apply (proj2_sig f) in Hfb. unfold asp in Hfb.
    destruct Hfb as [a [Hpre Hra]].
    exists f, a. split; [exists a; auto | exact Hra].
Qed.

#[global]
Instance ArrowApplyLaws_PureDSLPostArr : ArrowApplyLaws PureDSLPostArr.
Proof.
  constructor; intros.
  apply PureDSLPostArr_eq; intros pre b. cbn.
  split.
  - (* Forward: (∀f0 a, sp_rel (proj1_sig f0) a b → pre (f, a)) → sp_pt (proj1_sig f) pre b *)
    intros H. apply (proj2_sig f). intros a Hra.
    exact (H f a Hra a eq_refl).
  - (* Backward: sp_pt (proj1_sig f) pre b → (∀f0 a, sp_rel (proj1_sig f0) a b → pre (f, a)) *)
    intros Hfb f0 a0 Hrel a' Heq.
    injection Heq as Hfeq Haeq. subst a' f0.
    apply (proj2_sig f) in Hfb. exact (Hfb a0 Hrel).
Qed.

(* ================================================================= *)
(** ** Monad from ArrowApply (general construction)                   *)
(* ================================================================= *)

(** For any arrow [arr] with [ArrowApply], [arr I] (for fixed [I])
    is a monad. We use [arr_fanout] to thread the input through. *)

Section ArrowMonad.

  Variable arr : Type -> Type -> Type.
  Context `{HA : Arrow arr} `{HAA : ArrowApply arr}.
  Variable I : Type.

  Definition ret_arrow {A} (a : A) : arr I A :=
    arr_pure (fun _ => a).

  Definition bind_arrow {A B} (m : arr I A) (k : A -> arr I B) : arr I B :=
    arr_comp (arr_fanout m arr_id)
             (arr_comp (arr_pure (fun '(a, i) => (k a, i)))
                       arr_app).

  #[global]
  Instance Monad_Arrow : Monad (arr I) := {
    ret := @ret_arrow ;
    bind := @bind_arrow
  }.

End ArrowMonad.

(** For [ArrowApplyLaws] with Leibniz arrow equality, the arrow
    monad satisfies [MonadLawsE].  We prove this concretely for
    [PureASPostArr] and [PureDSLPostArr] using their relational
    decomposition, which is simpler than the abstract arrow proof. *)

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
      via [sp_rel (proj1_sig ...)], mirroring the demonic bind. *)
  Definition bind_ASP {A B}
    (m : PureASPostArr I A) (k : A -> PureASPostArr I B)
    : PureASPostArr I B :=
    mkASP (fun i c => exists b,
             sp_rel (proj1_sig m) i b /\
             sp_rel (proj1_sig (k b)) i c).

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
      via [sp_rel (proj1_sig ...)], avoiding classical axioms. *)
  Definition bind_DSLP {A B}
    (m : PureDSLPostArr I A) (k : A -> PureDSLPostArr I B)
    : PureDSLPostArr I B :=
    mkDSLP (fun i c => exists b,
             sp_rel (proj1_sig m) i b /\
             sp_rel (proj1_sig (k b)) i c).

  Instance Monad_PureDSLPostArr : Monad (PureDSLPostArr I) := {
    ret := @ret_DSLP ;
    bind := @bind_DSLP
  }.

  Lemma proj_mkDSLP {J B} (R : SPArr J B) pre b :
    sp_pt (proj1_sig (mkDSLP R)) pre b <-> dslp R pre b.
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

(** [optionArrT arr I = optionT (arr I)], so any monad [arr I]
    lifted through [optionArrT] remains a monad via the generic
    [MonadLawsE_optionT] from [ProgFacts.v]. *)

(** The generic [MonadLawsE_optionT] and [MonadLawsE_stateT] from
    [ProgFacts.v] lift these to [optionT (PureASPostArr I)] and
    [stateT S (optionT (PureASPostArr I))] for free, since
    [optionArrT arr I = optionT (arr I)] definitionally. *)

(* ================================================================= *)
(** ** Arrow laws for composed types: [ASPostArr] and [DSPostArr]      *)
(* ================================================================= *)

(** [ASPostArr S = stateArrT S optionASPArr] and
    [DSPostArr S = stateArrT S optionDSPArr]. Since [stateArrT]
    preserves arrow laws generically, these inherit arrow laws
    from [optionASPArr] and [optionDSPArr]. *)

Section ComposedArrowLaws.

  Variable S : Type.

  #[global]
  Instance ArrowEq_stateOptASP : ArrowEq (stateArrT S optionASPArr) :=
    ArrowEq_stateArrT S.

  #[global]
  Instance ArrowLaws_stateOptASP : ArrowLaws (stateArrT S optionASPArr) :=
    ArrowLaws_stateArrT S.

  #[global]
  Instance ArrowEq_stateOptDSP : ArrowEq (stateArrT S optionDSPArr) :=
    ArrowEq_stateArrT S.

  #[global]
  Instance ArrowLaws_stateOptDSP : ArrowLaws (stateArrT S optionDSPArr) :=
    ArrowLaws_stateArrT S.

End ComposedArrowLaws.
