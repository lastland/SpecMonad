(** * Laws for the [PrePost] arrow and monad.

    Proves [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws] for the
    arrow instances, and [Eq1Equivalence] + [MonadLawsE] for the
    monad-in-[B] instance, all from [Taxonomy/PrePost.v].  Uses the
    [PrePost_eq] helper to bridge pointwise iff to structural
    equality via funext + propext. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.
From Hammer Require Import Tactics.
From Incorrectness Require Import Taxonomy.PrePost.

(* ================================================================= *)
(** ** Arrow laws                                                     *)
(* ================================================================= *)

#[global]
Instance ArrowLaws_PrePost : ArrowLaws PrePost.
Proof.
  constructor; intros.
  - (* comp_id_l *) split; cbn; sauto limit: 200.
  - (* comp_id_r *) split; cbn; sauto limit: 200.
  - (* comp_assoc *) split; cbn; sauto limit: 200.
  - (* pure_comp *) split; cbn; sauto limit: 200.
  - (* first_pure *)
    split; cbn.
    + intros [a c]. simpl. reflexivity.
    + intros [a c] [b c']. simpl. sauto limit: 200.
  - (* first_comp *)
    split; cbn.
    + intros [a d]. simpl. split.
      * intros [HP HQ]. split; [exact HP |].
        intros [b d'] [HRf Hd]. simpl in *. subst d'. apply HQ. exact HRf.
      * intros [HP HQ]. split; [exact HP |].
        intros b HRf. apply (HQ (b, d)). simpl.
        split; [exact HRf | reflexivity].
    + intros [a d] [c d']. simpl. split.
      * intros [[b [HRf HRg]] Hdd]. subst d'.
        exists (b, d). simpl. sauto limit: 200.
      * intros [[b d''] [[HRf Hd1] [HRg Hd2]]]. simpl in *.
        subst d'' d'. sauto limit: 200.
  - (* first_fst *)
    split; cbn.
    + intros [a0 c]. simpl. sauto limit: 200.
    + intros [a0 c] b. simpl. split.
      * intros [[b' c'] [[HRf Hcc] Hbb]]. simpl in *. subst c' b'.
        exists a0. sauto limit: 200.
      * intros [a [Haa HRf]]. subst a. exists (b, c). simpl.
        sauto limit: 200.
  - (* first_assoc *)
    split; cbn.
    + intros [[a c] d]. simpl. sauto limit: 200 unfold: assoc_prod.
    + intros [[a c] d] [b' [c' d']]. simpl. unfold assoc_prod. split.
      * intros [[[b c''] d''] [[[HRf Hcc] Hdd] Heq]]. simpl in *.
        exists (a, (c, d)). sauto.
      * intros [[a' [c'' d'']] [Heq [HRf Hcd]]]. simpl in *.
        exists ((b', c), d). simpl. sauto.
  - (* comp_proper *)
    intros f1 f2 [HfP HfR] g1 g2 [HgP HgR].
    cbv [arrow_eq ArrowEq_PrePost PrePost_eq]; split; cbn.
    + intros a. rewrite HfP. sauto limit: 200.
    + intros a c. sauto limit: 200.
  - (* first_proper *)
    intros f1 f2 [HfP HfR].
    cbv [arrow_eq ArrowEq_PrePost PrePost_eq]; split; cbn.
    + intros [a c]. apply HfP.
    + intros [a c] [b c']. cbn. sauto limit: 200.
Qed.

(* ================================================================= *)
(** ** ArrowChoice laws                                               *)
(* ================================================================= *)

#[global]
Instance ArrowChoiceLaws_PrePost : ArrowChoiceLaws PrePost.
Proof.
  constructor; intros.
  - (* left_pure *)
    split; cbn.
    + intros [a|c]; cbn; reflexivity.
    + intros [a|c] [b|c']; cbn; sauto limit: 200.
  - (* left_comp *)
    split.
    + intros [a|d]; cbn.
      * split.
        -- intros [HPf HFg]. split; [exact HPf |].
           intros [b|d'] Hr; cbn in Hr; [exact (HFg b Hr) | contradiction].
        -- intros [HPf HFg]. split; [exact HPf |].
           intros b Hr. exact (HFg (inl b) Hr).
      * split; intros _; [split; [exact I|] | exact I].
        intros [b|d'] Hr; cbn in Hr; [contradiction | subst d'; exact I].
    + intros [a|d] [c|d']; cbn;
      (split;
       [intros [b [Hr Hs]]; exists (inl b); cbn; exact (conj Hr Hs)
       | intros [[b|d''] [Hr Hs]]; cbn in *; [| contradiction]; exists b; exact (conj Hr Hs)])
      || (split; [intros []
                 | intros [[b|d''] [Hr Hs]]; cbn in *; contradiction])
      || (split;
          [intros ->; exists (inr d'); cbn; exact (conj eq_refl eq_refl)
          | intros [[b|d''] [Hr Hs]]; cbn in *; [contradiction | subst d'' d'; reflexivity]]).
  - (* left_inl *)
    split; cbn; sauto limit: 200.
  - (* left_assoc *)
    split.
    + intros [[a|c]|d]; cbn; sauto limit: 200 unfold: assoc_sum.
    + intros x y. cbn. split.
      * intros [z [Hr Heq]]. unfold assoc_sum in Heq. subst y.
        destruct x as [[a|c]|d]; destruct z as [[b|c']|d']; cbn in Hr;
          try contradiction.
        -- exists (inl a). split; [reflexivity | cbn; exact Hr].
        -- subst c'. exists (inr (inl c)). split; [reflexivity | cbn; reflexivity].
        -- subst d'. exists (inr (inr d)). split; [reflexivity | cbn; reflexivity].
      * intros [z [Heq Hr]]. unfold assoc_sum in Heq. subst z.
        destruct x as [[a|c]|d]; cbn in Hr; destruct y as [b|[c'|d']];
          cbn in Hr; try contradiction; try discriminate.
        -- exists (inl (inl b)). cbn. split; [exact Hr | reflexivity].
        -- inversion Hr. subst. exists (inl (inr c')). cbn. split; reflexivity.
        -- inversion Hr. subst. exists (inr d'). cbn. split; reflexivity.
  - (* left_inr *)
    split; cbn; sauto limit: 200.
  - (* left_natural *)
    split.
    + intros [a|c]; cbn; sauto limit: 200.
    + intros x y. cbn. split.
      * intros [z [Hr Heq]]. subst y.
        destruct x as [a|c]; destruct z as [b|c']; cbn in Hr; try contradiction.
        -- exists (inl a). cbn. split; [reflexivity | exact Hr].
        -- subst c'. exists (inr (g c)). cbn. split; [reflexivity | reflexivity].
      * intros [z [Heq Hr]]. subst z.
        destruct x as [a|c]; cbn in Hr; destruct y as [b|d']; cbn in Hr; try contradiction.
        -- exists (inl b). cbn. split; [exact Hr | reflexivity].
        -- subst d'. exists (inr c). cbn. split; [reflexivity | reflexivity].
  - (* first_left_dist *)
    split.
    + intros [[a|c] d]; cbn; sauto limit: 200.
    + intros [x d] y. cbn. split.
      * intros [[y' d''] [[Hr Hd] Heq]]. cbn in *. subst d''.
        destruct x as [a|c]; destruct y' as [b|c']; cbn in Hr; try contradiction.
        -- subst y. exists (inl (a, d)). cbn. split; [reflexivity | split; [exact Hr | reflexivity]].
        -- subst c' y. exists (inr (c, d)). cbn. split; reflexivity.
      * intros [z [Heq Hr]].
        destruct x as [a|c]; cbn in Heq; subst z; cbn in Hr.
        -- destruct y as [[b d']|[c' d']]; cbn in Hr; try contradiction.
           destruct Hr as [Hr Hd]. subst d'.
           exists (inl b, d). cbn. split; [split; [exact Hr | reflexivity] | reflexivity].
        -- destruct y as [[b d']|[c' d']]; cbn in Hr; try contradiction.
           inversion Hr. subst.
           exists (inr c', d'). cbn. split; [split; reflexivity | reflexivity].
  - (* left_proper *)
    intros f1 f2 [HfP HfR].
    cbv [arrow_eq ArrowEq_PrePost PrePost_eq]; split; cbn.
    + intros [a|c]; [apply HfP | reflexivity].
    + intros [a|c] [b|c']; cbn; try reflexivity. apply HfR.
Qed.

(* ================================================================= *)
(** ** ArrowApply laws                                                *)
(* ================================================================= *)

#[global]
Instance ArrowApplyLaws_PrePost : ArrowApplyLaws PrePost.
Proof.
  constructor; intros. split; cbn; sauto limit: 200.
Qed.

(* ================================================================= *)
(** ** Eq1 equivalence and monad laws                                 *)
(* ================================================================= *)

Section PrePostMonadFacts.

  Context {A : Type}.

  #[global]
  Instance Eq1Equivalence_PrePost
    : @Eq1Equivalence (PrePost A) _ Eq1_PrePost.
  Proof.
    intros B; constructor.
    - intros m. unfold eq1, Eq1_PrePost. split; intros; reflexivity.
    - intros m1 m2 H. unfold eq1, Eq1_PrePost in *.
      destruct H as [HP HR]. split; intros; symmetry; auto.
    - intros m1 m2 m3 H1 H2. unfold eq1, Eq1_PrePost in *.
      destruct H1 as [HP1 HR1]. destruct H2 as [HP2 HR2].
      split; intros; etransitivity; eauto.
  Qed.

  #[global]
  Instance MonadLawsE_PrePost
    : @MonadLawsE (PrePost A) Eq1_PrePost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros B C f x. unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost, retPrePost. cbn.
      split; sauto limit: 200.
    - (* bind_ret_r *)
      intros B m. unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost, retPrePost. cbn.
      split; sauto limit: 200.
    - (* bind_bind *)
      intros B C D m f g. unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost. cbn.
      split; sauto limit: 200.
    - (* Proper_bind *)
      intros B C m1 m2 Hm k1 k2 Hk.
      unfold eq1, Eq1_PrePost in *.
      destruct Hm as [HmP HmR].
      cbn. unfold bindPrePost. cbn.
      split.
      + intros a. split; intros [HP HRf]; split;
          [apply HmP | | apply HmP |]; try exact HP; intros b HR;
          [assert (snd m1 a b) by (apply HmR; exact HR) |
           assert (snd m2 a b) by (apply HmR; exact HR)];
          destruct (Hk b) as [HkP _]; apply HkP; sauto limit: 200.
      + intros a c. split; intros [b [HR HRf]]; exists b; split;
          [apply HmR | destruct (Hk b) as [_ HkR]; apply HkR |
           apply HmR | destruct (Hk b) as [_ HkR]; apply HkR]; eauto.
  Qed.

End PrePostMonadFacts.
