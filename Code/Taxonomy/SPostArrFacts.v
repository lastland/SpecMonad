(** * Arrow law proofs for [PureSPostArr] and [optionPSArr].

    Every law is proved by [PureSPostArr_eq] and then transferring
    through [IsSP] to work with raw existentials. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality ProofIrrelevance
  Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow OptionArrowT.
From Incorrectness.Taxonomy Require Import SPostArr.

(* ================================================================= *)
(** ** Utilities                                                       *)
(* ================================================================= *)

Lemma PureSPostArr_eq {A B} (f g : PureSPostArr A B) :
  (forall pre b, proj1_sig f pre b <-> proj1_sig g pre b) -> f = g.
Proof.
  intro Heq.
  destruct f as [fv fp], g as [gv gp]; cbn in *.
  assert (fv = gv) as ->.
  { extensionality pre. extensionality b.
    apply propositional_extensionality. apply Heq. }
  f_equal. apply proof_irrelevance.
Qed.

Lemma IsSP_rewrite {A B} (f : PureSPostArr A B) :
  exists R : SPArr A B,
    forall pre b, proj1_sig f pre b <-> exists a, pre a /\ R a b.
Proof.
  destruct (proj2_sig f) as [R HR]. exists R. intros pre b.
  rewrite HR. unfold sp. reflexivity.
Qed.

(** [proj1_sig] of any PureSPostArr rewrites to existential form. *)
Lemma PSA_sp {A B} (f : PureSPostArr A B) (R : SPArr A B)
  (HR : forall pre b, proj1_sig f pre b <-> exists a, pre a /\ R a b) :
  forall P b, proj1_sig f P b <-> exists a, P a /\ R a b.
Proof. exact HR. Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [PureSPostArr]                                 *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PureSPostArr : ArrowEq PureSPostArr := {
  arrow_eq := fun A B => @eq (PureSPostArr A B)
}.

Lemma id_pred {A} (pre : A -> Prop) :
  (fun b => exists a, pre a /\ a = b) = pre.
Proof.
  extensionality b. apply propositional_extensionality.
  split; [intros [? [? ?]]; subst; auto | intro; exists b; auto].
Qed.

#[global]
Instance ArrowLaws_PureSPostArr : ArrowLaws PureSPostArr.
Proof.
  constructor; intros.

  - (* comp_id_l: arr_comp arr_id f = f *)
    apply PureSPostArr_eq; intros pre b. cbn.
    rewrite id_pred. reflexivity.

  - (* comp_id_r: arr_comp f arr_id = f *)
    apply PureSPostArr_eq; intros pre b. cbn.
    split.
    + intros [a [Hf0 Heq]]; subst; exact Hf0.
    + intro Hf0; exists b; auto.

  - (* comp_assoc *)
    apply PureSPostArr_eq; intros pre d0. cbn. reflexivity.

  - (* pure_comp: arr_comp (arr_pure f) (arr_pure g) = arr_pure (g ∘ f) *)
    apply PureSPostArr_eq; intros pre c. cbn.
    split.
    + intros [b [[a [Hp Hf0]] Hg]]; subst; exists a; auto.
    + intros [a [Hp Hgf]]; subst; exists (f a); split; [exists a |]; auto.

  - (* first_pure *)
    apply PureSPostArr_eq; intros pre [b d]. cbn.
    split.
    + intros [a [Hpre Hfa]]; subst; exists (a, d); auto.
    + intros [[a c] [Hpre Heq]]; inversion Heq; subst; exists a; auto.

  - (* first_comp *)
    apply PureSPostArr_eq; intros pre [c d]. cbn. reflexivity.

  - (* first_fst — requires IsSP for additivity *)
    apply PureSPostArr_eq; intros pre b. cbn.
    destruct (IsSP_rewrite f) as [R_f H_f].
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
    apply PureSPostArr_eq; intros pre [b [c d]]. cbn.
    destruct (IsSP_rewrite f) as [R_f H_f].
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
    unfold Proper, respectful, arrow_eq, ArrowEq_PureSPostArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PureSPostArr;
    intros; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** [ArrowLaws] for [optionPSArr]                                  *)
(* ================================================================= *)

#[global]
Instance ArrowEq_optionPSArr : ArrowEq optionPSArr := {
  arrow_eq := fun A B => @eq (optionPSArr A B)
}.

(** For optionPSArr, the IsSP witness tells us the relation on
    [A -> option B -> Prop].  We factor proofs through this. *)

(** All [optionPSArr] laws are proved by transferring through [IsSP]:
    convert every [proj1_sig] occurrence to existential form, then
    reason about plain propositions. *)

#[global]
Instance ArrowLaws_optionPSArr : ArrowLaws optionPSArr.
Proof.
  (* Strategy: for each law, use PureSPostArr_eq, intro, cbn.
     Then destruct IsSP_rewrite for f (and g if present) to
     rewrite all proj1_sig applications to existentials.
     All goals then become plain propositional logic. *)

  (** Helper: rewrite a PureSPostArr application using its IsSP witness. *)
  Local Ltac isp f :=
    let R := fresh "R" in let H := fresh "H" in
    destruct (IsSP_rewrite f) as [R H]; rewrite ?H; unfold sp in *.

  constructor; intros.

  - (* comp_id_l *)
    apply PureSPostArr_eq; intros pre ob. cbn.
    destruct ob as [b|]; isp f; firstorder (subst; eauto).

  - (* comp_id_r *)
    apply PureSPostArr_eq; intros pre ob. cbn.
    destruct ob as [b|]; isp f; firstorder (subst; eauto).

  - (* comp_assoc *)
    apply PureSPostArr_eq; intros pre ob. cbn.
    destruct ob as [d|]; isp f; isp g; isp h; firstorder.

  - (* pure_comp *)
    apply PureSPostArr_eq; intros pre ob. cbn.
    destruct ob as [c|]; firstorder (subst; eauto).

  - (* first_pure *)
    apply PureSPostArr_eq; intros pre ob. cbn.
    destruct ob as [[b0 d0]|].
    + split.
      * intros [a [Hpre Hf]]; subst. exists (a, d0); auto.
      * intros [[a c] [Hpre Heq]]; inversion Heq; subst. exists a; auto.
    + firstorder.

  - (* first_comp *)
    apply PureSPostArr_eq; intros pre ob. cbn.
    destruct ob as [[c0 d0]|]; isp f; isp g; firstorder.

  - (* first_fst *)
    apply PureSPostArr_eq; intros pre ob. cbn.
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
    apply PureSPostArr_eq; intros pre ob. cbn.
    isp f.
    destruct ob as [[b0 [c0 d0]]|].
    + (* Some (b, (c, d)) *)
      split.
      * intros [[[b1 c1] d1] [Hff Hassoc]]; cbn in Hff.
        unfold assoc_prod in Hassoc.
        assert (Hb : b1 = b0) by congruence.
        assert (Hc : c1 = c0) by congruence.
        assert (Hd : d1 = d0) by congruence.
        subst. rewrite H in Hff. destruct Hff as [a [Hpre Hra]].
        rewrite H. exists a; split; [exists ((a, c0), d0); auto | exact Hra].
      * intros Hfb.
        rewrite H in Hfb. destruct Hfb as [a [Hpure Hra]].
        destruct Hpure as [[[a0 c1] d1] [Hpre Hassoc]].
        unfold assoc_prod in Hassoc.
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
        unfold assoc_prod in Hassoc.
        assert (Ha : a0 = a) by congruence.
        assert (Hc : c2 = c1) by congruence.
        assert (Hd : d2 = d1) by congruence.
        subst. left. exists d1, c1. rewrite H. exists a. auto.

  - (* comp_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_optionPSArr;
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_optionPSArr;
    intros; subst; reflexivity.
Qed.
