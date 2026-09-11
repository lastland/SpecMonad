(** * The relational strongest-postcondition arrow [PredArr] and
      composed spec types.

    [PredArr A B := A -> B -> Prop] is a relation from [A] to [B], the
    category of relations interpreted as forward predicate
    transformers (strongest-postcondition arrows).  Using relations as
    the base ensures all arrow laws are provable without requiring
    monotonicity or additivity constraints.

    This file provides the arrow-view instances ([Arrow],
    [ArrowChoice], [ArrowApply], [ArrowLoop]) plus the complementary
    monad view: for every fixed [A], the partially applied type
    [fun B => PredArr A B] is a monad in [B] via relational composition.

    With both views available, we expose composed specification types
    for the three computation monads ([stdivitree], [stexcnd], [stdivexcnd]) in
    two equivalent styles:

    - Arrow view — applies [stateArrT] and [optionArrT] to [PredArr]:

        [progPredArr S A = stateArrT S (optionArrT PredArr) unit A]
        [nditPredArr S A = stateArrT S (optionArrT (optionArrT PredArr)) unit A]

    - Monad view — applies [stateT] and [optionT] (from ExtLib) to
      [PredArr unit] (the unary-in-[B] monad specialization):

        [progPredM S A = stateT S (optionT (PredArr unit)) A]
        [nditPredM S A = stateT S (optionT (optionT (PredArr unit))) A]

    The monad view inherits [MonadLawsE] automatically via the generic
    [MonadLawsE_optionT] and [MonadLawsE_stateT] instances in
    [Taxonomy/Prog.v].

    This file holds only the definitions and instances.  Their laws
    ([ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws], [ArrowLoopLaws],
    [Eq1Equivalence], [MonadLawsE]) are proved in
    [Taxonomy/PredArr.v]. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StDivITree.

(* ================================================================= *)
(** ** [PredArr]: definition and arrow instances                         *)
(* ================================================================= *)

Definition PredArr (A B : Type) : Type := A -> B -> Prop.

(** Pointwise iff is the intrinsic equivalence on relations — no
    extensionality axioms required. *)
Definition Pred_eq {A B} (f g : PredArr A B) : Prop :=
  forall a b, f a b <-> g a b.

#[global]
Instance Pred_eq_Equivalence {A B} : Equivalence (@Pred_eq A B).
Proof.
  constructor.
  - intros f a b. reflexivity.
  - intros f g H a b. symmetry. apply H.
  - intros f g h H1 H2 a b. etransitivity; [apply H1 | apply H2].
Qed.

#[global]
Instance ArrowEq_Pred : ArrowEq PredArr := {
  arrow_eq := @Pred_eq
}.

(** Covariant inclusion: [R1 ≤ R2] iff [R1 ⊆ R2]. A larger relation
    is "above" a smaller one. This pairs with the partial-correctness
    Hoare order on [PrePostArr] in [Taxonomy/GaloisArr.v]. *)
Definition Pred_le {A B} (R1 R2 : PredArr A B) : Prop :=
  forall a b, R1 a b -> R2 a b.

#[global]
Instance Pred_le_PreOrder {A B} : PreOrder (@Pred_le A B).
Proof.
  constructor.
  - intros R a b H. exact H.
  - intros R1 R2 R3 H12 H23 a b H. apply H23, H12, H.
Qed.

#[global]
Instance Arrow_Pred : Arrow PredArr := {
  arr_pure := fun A B f a b => f a = b ;
  arr_comp := fun A B C f g a c => exists b, f a b /\ g b c ;
  arr_first := fun A B C f p q =>
    let '(a, c) := p in let '(b, c') := q in f a b /\ c = c'
}.

#[global]
Instance ArrowChoice_Pred : ArrowChoice PredArr := {
  arr_left := fun A B C f x y =>
    match x, y with
    | inl a, inl b => f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end
}.

#[global]
Instance ArrowApply_Pred : ArrowApply PredArr := {
  arr_app := fun A B p b =>
    let '(f, a) := p in f a b
}.

#[global]
Instance ArrowLoop_Pred : ArrowLoop PredArr := {
  arr_loop := fun A B C f a b => exists c, f (a, c) (b, c)
}.

(* ================================================================= *)
(** ** [PredArr A] is a monad in its second argument                     *)
(* ================================================================= *)

(** For every fixed source type [A], [fun B => PredArr A B = A -> B -> Prop]
    is a monad in [B] via relational composition.  The source [A] is
    threaded as a shared "context" through [ret] and [bind]:

        ret b    := fun _ b' => b = b'
        bind m k := fun a  c => exists b, m a b /\ k b a c

    The monad laws hold under pointwise logical equivalence
    ([Eq1_Pred]), with no extensionality axioms required. *)

Section PredMonad.
  Context {A : Type}.

  Definition retPred {B} (b : B) : PredArr A B :=
    fun _ b' => b = b'.

  Definition bindPred {B C}
    (m : PredArr A B) (k : B -> PredArr A C) : PredArr A C :=
    fun a c => exists b, m a b /\ k b a c.

  #[global]
  Instance Monad_Pred : Monad (PredArr A) := {
    ret := @retPred ;
    bind := @bindPred
  }.

  #[global]
  Instance Eq1_Pred : Eq1 (PredArr A) :=
    fun B m1 m2 => forall a b, m1 a b <-> m2 a b.

End PredMonad.

(* ================================================================= *)
(** ** [optionPred] alias                                             *)
(* ================================================================= *)

(** The generic [optionArrT] transformer specializes cleanly to
    [PredArr].  [ArrowChoice], [ArrowApply] and [ArrowLoop] instances are
    inherited from the generic [ArrowChoice_optionArrT] etc. in
    [Classes/OptionArrowT]; their laws likewise come through the
    generic [ArrowChoiceLaws_optionArrT] etc. applied to [PredArr]'s own
    arrow laws. *)

Definition optionPred := optionArrT PredArr.

(** Pointwise iff for [optionPred].  [optionPred A B = PredArr A (option B)]
    so this is just [Pred_eq] at that type. *)
Definition optionPred_eq {A B} (f g : optionPred A B) : Prop :=
  forall a ob, f a ob <-> g a ob.

(* ================================================================= *)
(** ** Arrow-view specification types                                 *)
(* ================================================================= *)

Section ArrowSpec.

  Variable S : Type.

  (** For [stdivitree] and [stexcnd]: stateful computation with possible
      failure.  Unfolds to [(unit * S) -> option (A * S) -> Prop]. *)
  Definition progPredArr (A : Type) : Type :=
    stateArrT S (optionArrT PredArr) unit A.

  (** For [stdivexcnd]: stateful computation with failure and
      divergence.  Unfolds to [(unit * S) -> option (option (A * S)) -> Prop].
      The outer [option] represents exceptions; the inner [option]
      represents divergence. *)
  Definition nditPredArr (A : Type) : Type :=
    stateArrT S (optionArrT (optionArrT PredArr)) unit A.

End ArrowSpec.

(* ================================================================= *)
(** ** Monad-view specification types                                 *)
(* ================================================================= *)

Section MonadSpec.

  Variable S : Type.

  (** For [stdivitree]/[stexcnd].  Chains: base [PredArr unit] through [optionT]
      and [stateT], inheriting [Monad], [Eq1], and [MonadLawsE] from
      the transformer instances in [Prog.v]. *)
  Definition progPredM (A : Type) : Type :=
    stateT S (optionT (PredArr unit)) A.

  (** For [stdivexcnd] (double [optionT] for exception + divergence). *)
  Definition nditPredM (A : Type) : Type :=
    stateT S (optionT (optionT (PredArr unit))) A.

End MonadSpec.

(* ================================================================= *)
(** * Facts and laws (merged from PredArrFacts.v)                          *)
(* ================================================================= *)

(** * Laws for [PredArr] and [optionPred].

    This file proves [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws],
    and [ArrowLoopLaws] for the relational arrow [PredArr], plus
    [Eq1Equivalence] and [MonadLawsE] for the second-argument monad
    instance on [PredArr A].  The [ArrowLaws] / [ArrowChoiceLaws] /
    [ArrowApplyLaws] for [optionPred] are inherited from the generic
    transformer laws in [Classes/OptionArrowT] applied to these. *)

From Coq Require Import FunctionalExtensionality PropExtensionality Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivITree.
From Hammer Require Import Tactics.


(* ================================================================= *)
(** ** Arrow laws for [PredArr]                                          *)
(* ================================================================= *)

(** Helper: [arr_second] simplifies for [PredArr].  This is stated as a
    Leibniz equality (using [funext] + [propext] internally) so that
    plain [rewrite] works on it.  [X] is the "extra" (untouched) type. *)
Lemma arr_second_Pred {X A B} (f : PredArr A B) :
  @arr_second _ _ A B X f =
  fun (p : X * A) (q : X * B) =>
    let '(c, a) := p in let '(c', b) := q in f a b /\ c = c'.
Proof.
  extensionality p. extensionality q.
  apply propositional_extensionality.
  destruct p as [c a], q as [c' b].
  unfold arr_second, arr_comp, arr_first, arr_pure, swap; cbn.
  split.
  - intros [[a0 c0] [Heq [[b1 c1] [Hf Hswap]]]].
    inversion Heq; subst. simpl in *. inversion Hswap; subst. exact Hf.
  - intros [Hf Heq]. subst.
    exists (a, c'). split; [reflexivity|].
    exists (b, c'). simpl. split; [exact (conj Hf eq_refl)|reflexivity].
Qed.

Create HintDb Pred_ops.
#[local] Hint Unfold arr_id arr_comp arr_first arr_pure arr_loop
  arr_left arr_app assoc_prod unassoc_prod swap : Pred_ops.

Local Ltac unfold_Pred_full :=
  autounfold with Pred_ops; unfold Arrow_Pred; simpl;
  repeat match goal with [p : _ * _ |- _] => destruct p end;
  repeat match goal with
  | [H : context[let '(_, _) := ?p in _] |- _] => destruct p
  | [|- context[let '(_, _) := ?p in _]] => destruct p
  end.

(** After [intros a b] the goal [arrow_eq f g] (which unfolds to
    [forall a b, f a b <-> g a b] via [ArrowEq_Pred] / [Pred_eq]) is
    just [f a b <-> g a b]. *)

#[global]
Instance ArrowLaws_Pred : @ArrowLaws PredArr Arrow_Pred ArrowEq_Pred.
Proof.
  constructor; intros.
  1-4: intros a b; unfold_Pred_full; sauto limit: 200.
  - (* first_pure *)
    intros [? ?] [? ?]; unfold_Pred_full; sauto limit: 200.
  - (* first_comp *)
    intros [? ?] [? ?]; unfold_Pred_full. split.
    + intros [[b [Hf Hg]] Heq]. subst.
      exists (b, d0); simpl; eauto.
    + intros [[b0 d1] [H1 H2]]; simpl in *.
      destruct H1, H2; subst; split; [exists b0|]; eauto.
  - (* first_fst *)
    intros [? ?] ?; unfold_Pred_full. split.
    + intros [[b0 c0] [H1 H2]]; simpl in *.
      destruct H1; subst; exists a; eauto.
    + intros [a0 [? ?]]; subst. exists (b, c); simpl; eauto.
  - (* first_assoc *)
    intros [[? ?] ?] [? [? ?]]; unfold_Pred_full. split.
    + intros [[[? ?] ?] [H1 H2]]; simpl in *.
      destruct H1 as [[? ?] ?]; inversion H2; subst.
      eexists (a, (_, _)); simpl; eauto.
    + intros [[? [? ?]] [H1 H2]]; simpl in *.
      inversion H1; subst. destruct H2 as [? H2]; inversion H2; subst.
      eexists (_, _, _); simpl; eauto.
  - (* comp_proper *)
    intros f1 f2 Hf g1 g2 Hg a c.
    cbv [arrow_eq ArrowEq_Pred Pred_eq] in Hf, Hg.
    unfold_Pred_full. sauto limit: 200.
  - (* first_proper *)
    intros f1 f2 Hf [a c] [b c'].
    cbv [arrow_eq ArrowEq_Pred Pred_eq] in Hf.
    unfold_Pred_full. sauto limit: 200.
  - (* first_natural *)
    intros [a c] [b d]; cbn. split.
    + intros [[b' c'] [[Hf Hc] Heq]]. cbn in Heq. subst c'.
      inversion Heq; subst. exists (a, g c). cbn. auto.
    + intros [[a' d'] [Heq [Hf Hd]]]. inversion Heq; subst.
      exists (b, c). cbn. auto.
Qed.

#[global]
Instance ArrowChoiceLaws_Pred : ArrowChoiceLaws PredArr.
Proof.
  constructor; intros.
  - (* left_pure *)
    intros [a|c] [b|c']; unfold_Pred_full;
    unfold sum_bimap; sauto limit: 200.
  - (* left_comp *)
    intros [a|d] [c|d']; unfold_Pred_full.
    + split.
      * intros [b [Hf Hg]]. exists (inl b); eauto.
      * intros [x [H1 H2]]; destruct x as [b|d0];
        [exists b; eauto | simpl in *; contradiction].
    + sauto limit: 200.
    + sauto limit: 200.
    + split.
      * intros Heq; subst; exists (inr d'); eauto.
      * intros [[b|d0] [H1 H2]]; simpl in *; [contradiction | congruence].
  - (* left_inl *)
    intros a [b|c]; unfold_Pred_full.
    + split.
      * intros [b0 [Hf Heq]]; injection Heq as ->;
        exists (inl a); eauto.
      * intros [[a0|c0] [Heq Hf]]; [injection Heq as ->; exists b; eauto |
        simpl in *; destruct Hf].
    + split.
      * intros [b0 [Hf Heq]]; discriminate Heq.
      * intros [[a0|c0] [Heq Hf]]; [injection Heq as ->; simpl in *; destruct Hf |
        discriminate Heq].
  - (* left_assoc *)
    intros [[a|c]|d] [b|[c'|d']]; unfold_Pred_full;
    unfold assoc_sum; (split; intro H; destruct H as [x [H1 H2]];
      (destruct x as [[?|?]|?] || destruct x as [?|[?|?]]);
      simpl in *; try contradiction; try discriminate; subst;
      repeat match goal with
      | [H0 : inl _ = inl _ |- _] => injection H0; intros; subst; clear H0
      | [H0 : inr _ = inr _ |- _] => injection H0; intros; subst; clear H0
      end).
    all: first [ exists (inl a) | exists (inl (inl b))
                | exists (inr (inl c')) | exists (inl (inr c'))
                | exists (inr (inr d')) | exists (inr d') ]; eauto.
  - (* left_inr *)
    intros c y; unfold_Pred_full. split.
    + intros [x [Hinr Hleft]]. subst x.
      destruct y as [b|c']; simpl in Hleft; [contradiction | f_equal; exact Hleft].
    + intros Heq. subst y. exists (inr c). simpl. auto.
  - (* left_natural *)
    intros x y.
    destruct x as [a0|c0]; destruct y as [b0|d0]; unfold_Pred_full;
    unfold sum_bimap; simpl.
    all: split; intros [z [H1 H2]]; destruct z; simpl in *;
         try contradiction; try discriminate.
    all: repeat match goal with
         | [H : inl _ = inl _ |- _] => injection H; clear H; intros; subst
         | [H : inr _ = inr _ |- _] => injection H; clear H; intros; subst
         end.
    1-2: eexists (inl _); simpl; eauto.
    1-2: eexists (inr _); simpl; eauto.
  - (* first_left_dist *)
    intros [[a0|c0] d0] [[b0 d1]|[c1 d1]];
    unfold_Pred_full; unfold sum_prod_dist; simpl.
    all: split; intro H.
    all: repeat match goal with
      | [H : exists _, _ |- _] => destruct H
      | [H : _ /\ _ |- _] => destruct H
      | [H : (_ + _)%type |- _] => destruct H
      | [H : (_ * _)%type |- _] => destruct H
      | [p : (_ + _)%type |- _] => destruct p
      end; simpl in *;
      try contradiction; try discriminate;
      repeat match goal with
      | [H : inl _ = inl _ |- _] => injection H; clear H; intros; subst
      | [H : inr _ = inr _ |- _] => injection H; clear H; intros; subst
      | [H : (_, _) = (_, _) |- _] => injection H; clear H; intros; subst
      end.
    all: try (eexists (inl (_, _)); simpl; split; [reflexivity |]; eexists (_, _); simpl; eauto; fail).
    all: try (eexists (inr (_, _)); simpl; split; [reflexivity |]; eexists (_, _); simpl; eauto; fail).
    all: try (eexists (inl _, _); simpl; split; [eexists (inl _); simpl; eauto |]; eauto; fail).
    all: try (eexists (inr _, _); simpl; split; [eexists (inr _); simpl; eauto |]; eauto; fail).
    -- exists (inl (a0, d1)). auto.
    -- exists (inl b0, d1). simpl. auto.
    -- exists (inr (c1, d1)). auto.
    -- exists (inr c1, d1). simpl. auto.
  - (* left_proper *)
    intros f1 f2 Hf [a|c] [b|c'];
    cbv [arrow_eq ArrowEq_Pred Pred_eq] in Hf; unfold_Pred_full;
    try tauto.
    apply Hf.
Qed.

#[global]
Instance ArrowApplyLaws_Pred
  : @ArrowApplyLaws PredArr Arrow_Pred ArrowApply_Pred ArrowEq_Pred.
Proof.
  constructor; intros.
  - (* app_law *)
    intros a b; unfold_Pred_full. sauto limit: 200.
  - (* app_unit *)
    intros [a b] [a' b']; cbn. split.
    + intros [[f b0] [[Hf Hb] Hout]]. cbn in *. subst f b0.
      exact Hout.
    + intros Heq. exists ((fun y p => (a, y) = p), b).
      cbn. split; [split; reflexivity | exact Heq].
  - (* app_precompose *)
    intros [f a] c.
    rewrite arr_second_Pred. cbn. split.
    + intros [[h a'] [[Hh Ha] Hout]]. cbn in *. subst h a'.
      destruct Hout as [b [Hg Hf]].
      exists (f, b). cbn. auto.
    + intros [[f' b] [[Hg Hf] Hout]]. cbn in *. subst f'.
      exists ((fun a c => exists b, g a b /\ f b c), a).
      cbn. split; [split; reflexivity | exists b; auto].
  - (* app_postcompose *)
    intros [f a] c; cbn. split.
    + intros [[k a'] [[Hk Ha] Hout]]. cbn in *. subst k a'.
      exact Hout.
    + intros Hout.
      exists ((fun a c => exists b, f a b /\ h b c), a).
      cbn. split; [split; reflexivity | exact Hout].
  - (* app_ext *)
    intros x b. cbn. specialize (H x).
    destruct (u x) as [f a], (v x) as [g a']; cbn in H.
    destruct H as [Hfg Ha]. subst a'.
    change ((exists p, (f, a) = p /\ (let '(k, a0) := p in k a0 b)) <->
            (exists p, (g, a) = p /\ (let '(k, a0) := p in k a0 b))).
    split; intros [p [<- Hout]].
    + exists (g, a). split; [reflexivity | apply Hfg; exact Hout].
    + exists (f, a). split; [reflexivity | apply Hfg; exact Hout].
Qed.

#[global]
Instance ArrowLoopLaws_Pred : ArrowLoopLaws PredArr.
Proof.
  constructor; intros.
  - (* loop_left_tightening *)
    intros a b. unfold_Pred_full. split.
    + intros [c [[b0 c0] [[Hh Heq] Hf]]]. subst c0.
      exists b0; split; [exact Hh | exists c; exact Hf].
    + intros [b0 [Hh [c Hf]]].
      exists c; exists (b0, c); sauto limit: 200.
  - (* loop_right_tightening *)
    intros a c. unfold_Pred_full. split.
    + intros [d [[b0 d0] [Hf [Hg Heq]]]]. subst d0.
      exists b0; split; [exists d; exact Hf | exact Hg].
    + intros [b0 [[d Hf] Hg]].
      exists d; exists (b0, d); sauto limit: 200.
  - (* loop_sliding *)
    intros a b.
    rewrite !arr_second_Pred.
    unfold arr_loop, arr_comp, arr_pure, Arrow_Pred; simpl. split.
    + intros [c [[b0 c0] [Hf [Hk Heq]]]]. subst b0. subst c.
      exists c0. exists (a, k c0). sauto limit: 200.
    + intros [c [[a0 c0] [[Hk Heq] Hf]]]. subst a0.
      exists c0. exists (b, c). sauto limit: 200.
  - (* loop_vanishing *)
    intros a b.
    unfold arr_loop, arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Pred; simpl.
    split.
    + intros [c [d Hf]]. exists (c, d); exists ((a, c), d); split; [reflexivity|].
      exists ((b, c), d); sauto limit: 200.
    + intros [[c d] [p [Heq1 [q [Hf Heq2]]]]].
      inversion Heq1; subst.
      destruct q as [[? ?] ?]; simpl in Heq2; inversion Heq2; subst.
      exists c; exists d; exact Hf.
  - (* loop_superposing *)
    intros [c a0] [c' b0].
    rewrite arr_second_Pred.
    unfold arr_loop; cbn.
    unfold arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Pred, swap; cbn.
    split.
    + intros [[d Hf] Heq]. subst c'.
      exists d; exists (c, (a0, d)); split; [reflexivity|].
      exists (c, (b0, d)); split.
      * exists ((a0, d), c); split; [reflexivity|].
        exists ((b0, d), c); sauto limit: 200.
      * reflexivity.
    + intros [d [p [Heq1 [q [Hmid Heq2]]]]].
      inversion Heq1; subst.
      destruct Hmid as [r [Hr [s [Hfs Hs]]]].
      destruct r as [[? ?] ?]; simpl in Hr; inversion Hr; subst.
      destruct s as [[? ?] ?]; simpl in *.
      destruct Hfs as [Hf Hc]. subst.
      inversion Heq2; subst.
      split; [eexists; exact Hf | reflexivity].
Qed.

(* ================================================================= *)
(** ** [PredArr A] monad laws                                            *)
(* ================================================================= *)

#[global]
Instance Eq1Equivalence_Pred {A}
  : @Eq1Equivalence (PredArr A) _ Eq1_Pred.
Proof.
  constructor; repeat intro; unfold eq1, Eq1_Pred in *.
  - reflexivity.
  - symmetry. apply H.
  - etransitivity; [apply H | apply H0].
Qed.

#[global]
Instance MonadLawsE_Pred {A} : @MonadLawsE (PredArr A) Eq1_Pred _.
Proof.
  constructor.
  - (* bind_ret_l *)
    intros B C f x a c.
    cbn. unfold bindPred, retPred. sauto limit: 200.
  - (* bind_ret_r *)
    intros B x a b.
    cbn. unfold bindPred, retPred. sauto limit: 200.
  - (* bind_bind *)
    intros B C D x f g a d.
    cbn. unfold bindPred. sauto limit: 200.
  - (* Proper_bind *)
    intros B C m1 m2 Hm k1 k2 Hk a c.
    cbn. unfold bindPred.
    unfold eq1, Eq1_Pred in Hm.
    split; intros [b [Hm1 Hk1]]; exists b; split;
      [apply Hm | apply (Hk b a c) | apply Hm | apply (Hk b a c)]; assumption.
Qed.

(* ================================================================= *)
(** ** [optionPred] law instances via generic [optionArrT] laws       *)
(* ================================================================= *)

(** Because [PredArr] already has [ArrowLaws], [ArrowChoiceLaws], and
    [ArrowApplyLaws] instances, [optionPred = optionArrT PredArr]
    inherits the transformer laws from [Classes/OptionArrowT] without
    any custom proof.  These definitions are sanity checks that
    confirm typeclass resolution succeeds. *)

Definition ArrowLaws_optionPred : ArrowLaws optionPred := _.
Definition ArrowChoiceLaws_optionPred : ArrowChoiceLaws optionPred := _.
Definition ArrowApplyLaws_optionPred : ArrowApplyLaws optionPred := _.

(* ================================================================= *)
(** ** Monad-view spec type sanity checks                             *)
(* ================================================================= *)

(** Sanity check: confirm [MonadLawsE] resolves through the
    transformer stack down to [MonadLawsE_Pred]. *)
Definition MonadLawsE__progPredM (S : Type)
  : @MonadLawsE (progPredM S) _ _ :=
  MonadLawsE_stateT S (optionT (PredArr unit)).

Definition MonadLawsE__nditPredM (S : Type)
  : @MonadLawsE (nditPredM S) _ _ :=
  MonadLawsE_stateT S (optionT (optionT (PredArr unit))).
