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
From Incorrectness Require Import Taxonomy.PrePost.

(* ================================================================= *)
(** ** Arrow laws                                                     *)
(* ================================================================= *)

#[global]
Instance ArrowLaws_PrePost : ArrowLaws PrePost.
Proof.
  constructor; intros.
  - (* comp_id_l: arr_pure id ⨟ f = f *)
    split; cbn.
    + intros a. split.
      * intros [_ HP]. exact (HP a eq_refl).
      * intros HP. split; [exact I |]. intros b ->. exact HP.
    + intros a c. split.
      * intros [b [-> HR]]. exact HR.
      * intros HR. exists a. split; [reflexivity | exact HR].
  - (* comp_id_r: f ⨟ arr_pure id = f *)
    split; cbn.
    + intros a. split.
      * intros [HP _]. exact HP.
      * intros HP. split; [exact HP | intros _ _; exact I].
    + intros a c. split.
      * intros [b [HR ->]]. exact HR.
      * intros HR. exists c. split; [exact HR | reflexivity].
  - (* comp_assoc *)
    split; cbn.
    + intros a. split.
      * intros [[HP HQ] HFh]. split; [exact HP |]. intros b HRf.
        split; [exact (HQ b HRf) |]. intros c HRg.
        apply HFh. exists b. split; [exact HRf | exact HRg].
      * intros [HP HFgh]. split.
        -- split; [exact HP |]. intros b HRf. exact (proj1 (HFgh b HRf)).
        -- intros c [b [HRf HRg]]. exact (proj2 (HFgh b HRf) c HRg).
    + intros a d. split.
      * intros [c [[b [HRf HRg]] HRh]].
        exists b. split; [exact HRf |]. exists c. split; [exact HRg | exact HRh].
      * intros [b [HRf [c [HRg HRh]]]].
        exists c. split; [exists b; split; [exact HRf | exact HRg] | exact HRh].
  - (* pure_comp *)
    split; cbn.
    + intros a. split.
      * intros _. exact I.
      * intros _. split; [exact I | intros _ _; exact I].
    + intros a c. split.
      * intros [b [<- ->]]. reflexivity.
      * intros <-. exists (f a). split; reflexivity.
  - (* first_pure *)
    split; cbn.
    + intros [a c]. simpl. reflexivity.
    + intros [a c] [b c']. simpl. split.
      * intros [-> ->]. reflexivity.
      * intros Heq. inversion Heq. subst. split; reflexivity.
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
        exists (b, d). simpl. split.
        -- split; [exact HRf | reflexivity].
        -- split; [exact HRg | reflexivity].
      * intros [[b d''] [[HRf Hd1] [HRg Hd2]]]. simpl in *.
        subst d'' d'.
        split; [| reflexivity]. exists b. split; [exact HRf | exact HRg].
  - (* first_fst *)
    split; cbn.
    + intros [a0 c]. simpl. split.
      * intros [HP _]. split; [exact I |]. intros a ->. exact HP.
      * intros [_ HQ]. split.
        -- exact (HQ a0 eq_refl).
        -- intros _ _. exact I.
    + intros [a0 c] b. simpl. split.
      * intros [[b' c'] [[HRf Hcc] Hbb]]. simpl in *. subst c' b'.
        exists a0. split; [reflexivity | exact HRf].
      * intros [a [Haa HRf]]. subst a. exists (b, c). simpl.
        split; [split; [exact HRf | reflexivity] | reflexivity].
  - (* first_assoc *)
    split; cbn.
    + intros [[a c] d]. simpl. split.
      * intros [HP _]. split; [exact I |].
        intros q Heq. unfold assoc_prod in Heq. subst q. simpl. exact HP.
      * intros [_ HQ]. split.
        -- exact (HQ (a, (c, d)) eq_refl).
        -- intros _ _. exact I.
    + intros [[a c] d] [b' [c' d']]. simpl. split.
      * intros [[[b c''] d''] [[[HRf Hcc] Hdd] Heq]]. simpl in *.
        unfold assoc_prod in Heq.
        exists (a, (c, d)). split.
        -- unfold assoc_prod. reflexivity.
        -- simpl. split.
           ++ replace b' with b by congruence. exact HRf.
           ++ congruence.
      * intros [[a' [c'' d'']] [Heq [HRf Hcd]]]. simpl in *.
        unfold assoc_prod in Heq.
        exists ((b', c), d). simpl. split.
        -- split; [split; [| reflexivity] | reflexivity].
           replace a' with a in HRf by congruence. exact HRf.
        -- unfold assoc_prod. congruence.
  - (* comp_proper *)
    intros f1 f2 [HfP HfR] g1 g2 [HgP HgR].
    cbv [arrow_eq ArrowEq_PrePost PrePost_eq]; split; cbn.
    + intros a. rewrite HfP. split; intros [H1 H2]; split; try assumption.
      * intros b Hr. apply HgP, H2, HfR, Hr.
      * intros b Hr. apply HgP, H2, HfR, Hr.
    + intros a c. split; intros [b [Hr1 Hr2]]; exists b;
        split; solve [apply HfR; assumption | apply HgR; assumption].
  - (* first_proper *)
    intros f1 f2 [HfP HfR].
    cbv [arrow_eq ArrowEq_PrePost PrePost_eq]; split; cbn.
    + intros [a c]. apply HfP.
    + intros [a c] [b c']. cbn. split; intros [Hf Hc]; split;
        solve [apply HfR; assumption | assumption].
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
    + intros a. destruct a as [a|c]; cbn; reflexivity.
    + intros a b. destruct a as [a|c]; destruct b as [b|c']; cbn;
      (split; [intros Heq; subst; reflexivity | intros Heq; inversion Heq; reflexivity])
      || (split; [intros []; reflexivity | intros Heq; inversion Heq])
      || (split; [intros Heq; inversion Heq; reflexivity | intros Heq; subst; reflexivity])
      || (split; intros Heq; inversion Heq).
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
    split.
    + intros a. cbn. split.
      * intros [HP _]. split; [exact I|]. intros x Heq. subst x. exact HP.
      * intros [_ HQ]. split; [exact (HQ (inl a) eq_refl) | intros _ _; exact I].
    + intros a y. cbn. split.
      * intros [b [HR Heq]]. subst y. exists (inl a). split; [reflexivity | exact HR].
      * intros [x [Heq Hr]]. subst x. destruct y as [b|c]; cbn in Hr; [| contradiction].
        exists b. split; [exact Hr | reflexivity].
  - (* left_assoc *)
    split.
    + intros x. cbn. split.
      * intros [HP _]. split; [exact I |].
        intros y Heq. destruct x as [[a|c]|d]; unfold assoc_sum in Heq; subst y; cbn; try exact I; exact HP.
      * intros [_ HQ]. split.
        -- destruct x as [[a|c]|d]; cbn;
           [exact (HQ (inl a) eq_refl) | exact I | exact I].
        -- intros _ _. exact I.
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
    split.
    + intros c. cbn. split.
      * intros _. exact I.
      * intros _. split; [exact I|]. intros x Heq. subst x. cbn. exact I.
    + intros c y. cbn. split.
      * intros [x [Heq Hr]]. subst x. cbn in Hr.
        destruct y as [b|c']; [contradiction | subst c'; reflexivity].
      * intros Heq. subst y. exists (inr c). cbn. split; reflexivity.
  - (* left_natural *)
    split.
    + intros x. cbn. split.
      * intros [HP _]. split.
        -- exact I.
        -- intros y Heq. subst y. cbn.
           destruct x as [a|c]; cbn in HP; [exact HP | exact I].
      * intros [_ HQ]. split.
        -- destruct x as [a|c]; cbn.
           ++ exact (HQ (inl a) eq_refl).
           ++ exact I.
        -- intros _ _. exact I.
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
    + intros [x d]. cbn. split.
      * intros [HP _]. split.
        -- exact I.
        -- intros z Heq. subst z. destruct x as [a|c]; cbn in *; [exact HP | exact I].
      * intros [_ HQ]. split.
        -- destruct x as [a|c]; cbn in *.
           ++ exact (HQ (inl (a, d)) eq_refl).
           ++ exact I.
        -- intros _ _. exact I.
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
  constructor; intros.
  split.
  - intros a. cbn. split.
    + intros [_ HP]. exact (HP (f, a) eq_refl).
    + intros HP. split; [exact I|]. intros [f' a'] Heq. inversion Heq. subst. exact HP.
  - intros a b. cbn. split.
    + intros [[f' a'] [Heq Hr]]. inversion Heq. subst. exact Hr.
    + intros Hr. exists (f, a). split; [reflexivity | exact Hr].
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
    - (* Reflexive *)
      intros m. unfold eq1, Eq1_PrePost.
      split; intros; reflexivity.
    - (* Symmetric *)
      intros m1 m2 H. unfold eq1, Eq1_PrePost in *.
      destruct H as [HP HR]. split; intros.
      + symmetry. apply HP.
      + symmetry. apply HR.
    - (* Transitive *)
      intros m1 m2 m3 H1 H2. unfold eq1, Eq1_PrePost in *.
      destruct H1 as [HP1 HR1]. destruct H2 as [HP2 HR2].
      split; intros.
      + etransitivity; [apply HP1 | apply HP2].
      + etransitivity; [apply HR1 | apply HR2].
  Qed.

  #[global]
  Instance MonadLawsE_PrePost
    : @MonadLawsE (PrePost A) Eq1_PrePost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros B C f x.
      unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost, retPrePost. cbn.
      split.
      + intros a. split.
        * intros [_ HP]. exact (HP x eq_refl).
        * intros HP. split; [exact I |]. intros b ->. exact HP.
      + intros a c. split.
        * intros [b [-> HR]]. exact HR.
        * intros HR. exists x. split; [reflexivity | exact HR].
    - (* bind_ret_r *)
      intros B m.
      unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost, retPrePost. cbn.
      split.
      + intros a. split.
        * intros [HP _]. exact HP.
        * intros HP. split; [exact HP | intros _ _; exact I].
      + intros a b. split.
        * intros [b' [HR ->]]. exact HR.
        * intros HR. exists b. split; [exact HR | reflexivity].
    - (* bind_bind *)
      intros B C D m f g.
      unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost. cbn.
      split.
      + intros a. split.
        * intros [[HP HRf] HFg].
          split; [exact HP |]. intros b HR.
          split; [exact (HRf b HR) |]. intros c HRf'.
          apply HFg. exists b. split; [exact HR | exact HRf'].
        * intros [HP HFgh]. split.
          -- split; [exact HP |]. intros b HR.
             exact (proj1 (HFgh b HR)).
          -- intros c [b [HR HRf']].
             exact (proj2 (HFgh b HR) c HRf').
      + intros a d. split.
        * intros [c [[b [HR HRf]] HRg]].
          exists b. split; [exact HR |].
          exists c. split; [exact HRf | exact HRg].
        * intros [b [HR [c [HRf HRg]]]].
          exists c. split; [exists b; split; [exact HR | exact HRf] | exact HRg].
    - (* Proper_bind *)
      intros B C m1 m2 Hm k1 k2 Hk.
      unfold eq1, Eq1_PrePost in *.
      destruct Hm as [HmP HmR].
      cbn. unfold bindPrePost. cbn.
      split.
      + intros a. split.
        * intros [HP HRf]. split; [apply HmP; exact HP |].
          intros b HR2. assert (HR1 : snd m1 a b) by (apply HmR; exact HR2).
          specialize (HRf b HR1).
          destruct (Hk b) as [HkP _]. apply HkP. exact HRf.
        * intros [HP HRf]. split; [apply HmP; exact HP |].
          intros b HR1. assert (HR2 : snd m2 a b) by (apply HmR; exact HR1).
          specialize (HRf b HR2).
          destruct (Hk b) as [HkP _]. apply HkP. exact HRf.
      + intros a c. split.
        * intros [b [HR1 HRf]].
          exists b. split; [apply HmR; exact HR1 |].
          destruct (Hk b) as [_ HkR]. apply HkR. exact HRf.
        * intros [b [HR2 HRf]].
          exists b. split; [apply HmR; exact HR2 |].
          destruct (Hk b) as [_ HkR]. apply HkR. exact HRf.
  Qed.

End PrePostMonadFacts.
