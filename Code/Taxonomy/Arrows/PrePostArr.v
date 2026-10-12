(** * The pre/post relational arrow [PrePostArr].

    [PrePostArr A B := (A -> Prop) * (A -> B -> Prop)] packages a Hoare
    specification with precondition [P] and post-relation [R].  The
    post-relation retains the input [a], so [arr_pure id] can express
    the diagonal [fun a b => a = b].  The arrow laws use pointwise iff
    on both components, without coarsening that equivalence.

    This file defines the type [PrePostArr], the pointwise-iff
    equivalence [PrePost_eq], the partial-correctness Hoare order
    [PrePost_le] (stronger pre, weaker post), the [ArrowEq] /
    [Arrow] / [ArrowChoice] / [ArrowApply] instances, the [Eq1]
    selecting the arrow equality, and all the corresponding arrow laws
    ([ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws]).  The
    arrow-derived monad dictionaries ([Monad], [Eq1Equivalence],
    [MonadLawsE]) are generic and are collected with their
    resolution checks in [Tests/ArrowMonadInstances.v].

    Galois connections relating [PrePostArr] to [Rel] and monotone
    [WPArr] values are collected in [GaloisArr.v]. *)

From Coq Require Import RelationClasses.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad.

(* ================================================================= *)
(** ** Type definition                                                *)
(* ================================================================= *)

Definition PrePostArr (A B : Type) : Type :=
  ((A -> Prop) * (A -> B -> Prop))%type.

(** Pointwise iff equivalence on both components — no extensionality
    axioms required. *)
Definition PrePost_eq {A B} (pq1 pq2 : PrePostArr A B) : Prop :=
  (forall a, fst pq1 a <-> fst pq2 a) /\
  (forall a b, snd pq1 a b <-> snd pq2 a b).

#[global]
Instance PrePost_eq_Equivalence {A B} : Equivalence (@PrePost_eq A B).
Proof.
  constructor.
  - intros pq. split; reflexivity.
  - intros pq1 pq2 [HP HR]. split; intros; [symmetry; apply HP | symmetry; apply HR].
  - intros pq1 pq2 pq3 [HP12 HR12] [HP23 HR23]. split; intros.
    + etransitivity; [apply HP12 | apply HP23].
    + etransitivity; [apply HR12 | apply HR23].
Qed.

(** Partial-correctness Hoare order: strengthen the precondition,
    weaken the post-relation.  [pq1 ≤ pq2] iff [fst pq2 ⊆ fst pq1]
    and [snd pq1 ⊆ snd pq2].  Pairs with covariant [Rel_le] to make
    [α R := (True, R)], [γ pq := snd pq] a Galois connection (see
    [GaloisArr.v]). *)
Definition PrePost_le {A B} (pq1 pq2 : PrePostArr A B) : Prop :=
  (forall a,   fst pq2 a   -> fst pq1 a) /\
  (forall a b, snd pq1 a b -> snd pq2 a b).

#[global]
Instance PrePost_le_PreOrder {A B} : PreOrder (@PrePost_le A B).
Proof.
  constructor.
  - intros [P R]. split; intros; assumption.
  - intros [P1 R1] [P2 R2] [P3 R3] [HP12 HR12] [HP23 HR23].
    split; intros.
    + apply HP12, HP23. assumption.
    + apply HR23, HR12. assumption.
Qed.

(* ================================================================= *)
(** ** Arrow instances                                                *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PrePost : ArrowEq PrePostArr := {
  arrow_eq := @PrePost_eq
}.

#[global]
Instance Arrow_PrePost : Arrow PrePostArr := {
  arr_pure := fun A B f =>
    (fun _ : A => True, fun a b => f a = b) ;
  arr_comp := fun A B C pq1 pq2 =>
    ( fun a => fst pq1 a /\ (forall b, snd pq1 a b -> fst pq2 b)
    , fun a c => exists b, snd pq1 a b /\ snd pq2 b c ) ;
  arr_first := fun A B C pq =>
    ( fun p : (A * C)%type => fst pq (fst p)
    , fun p q => snd pq (fst p) (fst q) /\ snd p = snd q )
}.

#[global]
Instance ArrowChoice_PrePost : ArrowChoice PrePostArr := {
  arr_left := fun A B C pq =>
    ( fun x => match x with
               | inl a => fst pq a
               | inr _ => True
               end
    , fun x y => match x, y with
                 | inl a, inl b => snd pq a b
                 | inr c, inr c' => c = c'
                 | _, _ => False
                 end
    )
}.

#[global]
Instance ArrowApply_PrePost : ArrowApply PrePostArr := {
  arr_app := fun A B =>
    ( fun p : (PrePostArr A B * A)%type => fst (fst p) (snd p)
    , fun p b => snd (fst p) (snd p) b )
}.

(* ================================================================= *)
(** ** Arrow-derived monad (second argument, [A] fixed)               *)
(* ================================================================= *)

(** For every fixed source type [A], typeclass resolution derives a
    monad on [PrePostArr A] from the arrow via [Monad_Arrow]; no
    compact helper is consumed by production proofs, so the monad
    dictionaries and the compact [ret]/[bind] descriptions live in
    [Tests/ArrowMonadInstances.v]. *)

Section PrePostMonad.

  Context {A : Type}.

  #[global]
  Instance Eq1_PrePost : Eq1 (PrePostArr A) :=
    @Eq1_Arrow PrePostArr ArrowEq_PrePost A.

End PrePostMonad.

(** Galois connections with other specification types are in [GaloisArr.v]. *)

(* ================================================================= *)
(** * Facts and laws (merged from PrePostArrFacts.v)                          *)
(* ================================================================= *)

(** * Laws for the [PrePostArr] arrow.

    The proofs establish [ArrowLaws], [ArrowChoiceLaws], and
    [ArrowApplyLaws] under [PrePost_eq].  They reason directly with
    pointwise iff, not by converting it to structural equality.
    The generic arrow-to-monad construction supplies the monad laws. *)

From Hammer Require Import Tactics.


(* ================================================================= *)
(** ** Arrow laws                                                     *)
(* ================================================================= *)

#[global]
Instance ArrowLaws_PrePost
  : @ArrowLaws PrePostArr Arrow_PrePost ArrowEq_PrePost.
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
        exists (a, (c, d)). sauto limit: 200.
      * intros [[a' [c'' d'']] [Heq [HRf Hcd]]]. simpl in *.
        exists ((b', c), d). simpl. sauto limit: 200.
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
  - (* first_natural *)
    split; cbn.
    + intros [a c]. cbn. sauto limit: 200.
    + intros [a c] [b d]. cbn. split.
      * intros [[b' c'] [[Hf Hc] Heq]]. cbn in *. subst c'.
        inversion Heq; subst. exists (a, g c). cbn. auto.
      * intros [[a' d'] [Heq [Hf Hd]]]. cbn in *.
        inversion Heq; subst. exists (b, c). cbn. auto.
  - (* pure_proper *)
    intros f g H. split; cbn.
    + intro a. reflexivity.
    + intros a b. rewrite (H a). reflexivity.
Qed.

(* ================================================================= *)
(** ** ArrowChoice laws                                               *)
(* ================================================================= *)

#[global]
Instance ArrowChoiceLaws_PrePost : ArrowChoiceLaws PrePostArr.
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
Instance ArrowApplyLaws_PrePost
  : @ArrowApplyLaws PrePostArr Arrow_PrePost ArrowApply_PrePost ArrowEq_PrePost.
Proof.
  constructor; [intros | intros | intros | intros | intros X A B u v H].
  - (* app_law *) split; cbn; sauto limit: 200.
  - (* app_unit *)
    split; cbn.
    + intros [a b]. cbn. sauto limit: 200.
    + intros [a b] [a' b']. cbn. split.
      * intros [[f b0] [[Hf Hb] Hout]]. cbn in *. subst f b0.
        exact Hout.
      * intros Heq.
        exists ((fun _ => True, fun y p => (a, y) = p), b).
        cbn. split; [split; reflexivity | exact Heq].
  - (* app_precompose *)
    split; cbn; unfold swap.
    + intros [f a]. cbn.
      transitivity (fst g a /\ forall b, snd g a b -> fst f b).
      * split.
        -- intros [_ Hpre].
           apply (Hpre (@arr_comp PrePostArr Arrow_PrePost A B C g f, a)).
           split; reflexivity.
        -- intros Hpre. split; [exact I|].
           intros [k a'] [Hk Ha]. cbn in *. subst k a'. exact Hpre.
      * split.
        -- intros [Hg Hf]. split.
           ++ split; [exact I|]. intros [a' f'] Heq.
              inversion Heq; subst. cbn. split; [exact Hg|].
              intros _ _. exact I.
           ++ intros [f' b] [[a' f''] [Hp [[b' f'''] [[Hgb Hff] Hswap]]]].
              cbn in *. inversion Hp; subst.
              inversion Hswap; subst. apply Hf. exact Hgb.
        -- intros [[_ Hg] Hf]. split.
           ++ exact (proj1 (Hg (a, f) eq_refl)).
           ++ intros b Hgb. apply (Hf (f, b)).
              exists (a, f). split; [reflexivity|].
              exists (b, f). cbn. auto.
    + intros [f a] c. cbn. split.
      * intros [[k a'] [[Hk Ha] Hout]]. cbn in *. subst k a'.
        destruct Hout as [b [Hg Hf]].
        exists (f, b). split; [|exact Hf].
        exists (a, f). split; [reflexivity|].
        exists (b, f). cbn. auto.
      * intros [[f' b] [[p [Hp [q [Hg Hq]]]] Hf]].
        destruct p as [a' f''], q as [b' f''']; cbn in *.
        injection Hp as Ha Hf0. subst a' f''.
        destruct Hg as [Hg Hff]. subst f'''.
        injection Hq as Hf0 Hb. subst f' b'.
        exists (@arr_comp PrePostArr Arrow_PrePost A B C g f, a).
        cbn. split; [split; reflexivity | exists b; auto].
  - (* app_postcompose *)
    split; cbn.
    + intros [f a]. cbn. split.
      * intros [_ Hpre].
        apply (Hpre (@arr_comp PrePostArr Arrow_PrePost A B C f h, a)).
        split; reflexivity.
      * intros Hpre. split; [exact I|].
        intros [k a'] [Hk Ha]. cbn in *. subst k a'. exact Hpre.
    + intros [f a] c. cbn. split.
      * intros [[k a'] [[Hk Ha] Hout]]. cbn in *. subst k a'.
        exact Hout.
      * intros Hout.
        exists (@arr_comp PrePostArr Arrow_PrePost A B C f h, a).
        cbn. split; [split; reflexivity | exact Hout].
  - (* app_ext *)
    split; cbn.
    + intros x. specialize (H x).
      destruct (u x) as [f a], (v x) as [g a']; cbn in *.
      destruct H as [[HP HR] Ha]. change (a = a') in Ha. subst a'.
      split; intros [_ Hpre]; split; [exact I| |exact I|]; intros p <-.
      * apply HP. exact (Hpre (f, a) eq_refl).
      * apply HP. exact (Hpre (g, a) eq_refl).
    + intros x b. specialize (H x).
      destruct (u x) as [f a], (v x) as [g a']; cbn in *.
      destruct H as [[HP HR] Ha]. change (a = a') in Ha. subst a'.
      split; intros [p [<- Hout]]; cbn in Hout.
      * exists (g, a). split; [reflexivity|]. apply HR. exact Hout.
      * exists (f, a). split; [reflexivity|]. apply HR. exact Hout.
Qed.
