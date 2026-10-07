(** * Binary relational arrows and specification stacks.

    [Rel A B := A -> B -> Prop] represents a relation from [A] to [B].
    Its composition existentially joins relations at an intermediate
    value.  The arrow laws use pointwise iff; no predicate-transformer
    well-formedness proofs are stored in this carrier.

    This file provides the arrow-view instances ([Arrow],
    [ArrowChoice], [ArrowApply], [ArrowLoop]) plus the complementary
    monad view: for every fixed [A], the partially applied type
    [fun B => Rel A B] is a monad in [B] via relational composition.

    The state/option specification stacks have two presentations:

    - Arrow view — applies [stateArrT] and [optionArrT] to [Rel]:

        [progRelArr S A = stateArrT S (optionArrT Rel) unit A]
        [nditRelArr S A = stateArrT S (optionArrT (optionArrT Rel)) unit A]

    - Monad view — applies [stateT] and [optionT] (from ExtLib) to
      [Rel unit] (the unary-in-[B] monad specialization):

        [progRelM S A = stateT S (optionT (Rel unit)) A]
        [nditRelM S A = stateT S (optionT (optionT (Rel unit))) A]

    The arrow view uses [Classes/ArrowMonad.v] after stacking effects;
    the monad view uses the generic [optionT] / [stateT] laws from
    [ComputationMonads/TransformerLaws.v].  Named dictionaries and
    resolution checks live in [Tests/ArrowMonadInstances.v] and
    [Tests/ArrowTransformerInstances.v].  This file owns the binary
    [SPureArr], [SPStArr], and [SPStExcArr] compatibility names, their
    selected equality/law dictionaries, and relational congruence facts.
    [BaseSpecMonads/SPure.v] supplies their unit-input monad interfaces
    and orders; [RelSPostArr.v] supplies the four SP readings.

    This file proves the base arrow laws, including [ArrowLoopLaws];
    loop laws do not extend to [optionRel] (see [OptionLoop.v]). *)

From Coq Require Import RelationClasses.
From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

(* ================================================================= *)
(** ** [Rel]: definition and arrow instances                         *)
(* ================================================================= *)

Definition Rel (A B : Type) : Type := A -> B -> Prop.

(** Pointwise iff is the intrinsic equivalence on relations — no
    extensionality axioms required. *)
Definition Rel_eq {A B} (f g : Rel A B) : Prop :=
  forall a b, f a b <-> g a b.

#[global]
Instance Rel_eq_Equivalence {A B} : Equivalence (@Rel_eq A B).
Proof.
  constructor.
  - intros f a b. reflexivity.
  - intros f g H a b. symmetry. apply H.
  - intros f g h H1 H2 a b. etransitivity; [apply H1 | apply H2].
Qed.

#[global]
Instance ArrowEq_Rel : ArrowEq Rel := {
  arrow_eq := @Rel_eq
}.

(** Covariant inclusion: [R1 ≤ R2] iff [R1 ⊆ R2]. A larger relation
    is "above" a smaller one. This pairs with the partial-correctness
    Hoare order on [PrePostArr] in [GaloisArr.v]. *)
Definition Rel_le {A B} (R1 R2 : Rel A B) : Prop :=
  forall a b, R1 a b -> R2 a b.

#[global]
Instance Rel_le_PreOrder {A B} : PreOrder (@Rel_le A B).
Proof.
  constructor.
  - intros R a b H. exact H.
  - intros R1 R2 R3 H12 H23 a b H. apply H23, H12, H.
Qed.

#[global]
Instance Arrow_Rel : Arrow Rel := {
  arr_pure := fun A B f a b => f a = b ;
  arr_comp := fun A B C f g a c => exists b, f a b /\ g b c ;
  arr_first := fun A B C f p q =>
    let '(a, c) := p in let '(b, c') := q in f a b /\ c = c'
}.

#[global]
Instance ArrowChoice_Rel : ArrowChoice Rel := {
  arr_left := fun A B C f x y =>
    match x, y with
    | inl a, inl b => f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end
}.

#[global]
Instance ArrowApply_Rel : ArrowApply Rel := {
  arr_app := fun A B p b =>
    let '(f, a) := p in f a b
}.

#[global]
Instance ArrowLoop_Rel : ArrowLoop Rel := {
  arr_loop := fun A B C f a b => exists c, f (a, c) (b, c)
}.

(* ================================================================= *)
(** ** [Rel A] is a monad in its second argument                     *)
(* ================================================================= *)

(** For every fixed source type [A], [fun B => Rel A B = A -> B -> Prop]
    is a monad in [B] via relational composition.  The source [A] is
    threaded as a shared "context" through [ret] and [bind]:

        ret b    := fun _ b' => b = b'
        bind m k := fun a  c => exists b, m a b /\ k b a c

    Typeclass resolution derives the monad from the arrow via
    [Monad_Arrow]; the compact helpers below are the operational
    reading used by the [OldSP] observations.  They agree with the
    generic operations under pointwise logical equivalence ([Eq1_Rel]);
    the agreement lemmas and named monad/law dictionaries are collected
    in [Tests/ArrowMonadInstances.v]. *)

Section RelMonad.
  Context {A : Type}.

  Definition retRel {B} (b : B) : Rel A B :=
    fun _ b' => b = b'.

  Definition bindRel {B C}
    (m : Rel A B) (k : B -> Rel A C) : Rel A C :=
    fun a c => exists b, m a b /\ k b a c.

  #[global]
  Instance Eq1_Rel : Eq1 (Rel A) :=
    @Eq1_Arrow Rel ArrowEq_Rel A.

End RelMonad.

(* ================================================================= *)
(** ** [optionRel] alias                                             *)
(* ================================================================= *)

(** [optionRel] inherits [Arrow], [ArrowChoice], [ArrowApply], and their
    laws through [Classes/OptionArrowT].  It does not inherit lawful
    [ArrowLoop]: [OptionLoop.v] refutes unrestricted left tightening
    for these option operations, using an empty feedback type. *)

Definition optionRel := optionArrT Rel.

(** Pointwise iff for [optionRel].  [optionRel A B = Rel A (option B)]
    so this is just [Rel_eq] at that type. *)
Definition optionRel_eq {A B} (f g : optionRel A B) : Prop :=
  forall a ob, f a ob <-> g a ob.

(* ================================================================= *)
(** ** Binary relational specification aliases                      *)
(* ================================================================= *)

Notation SPureArr := Rel (only parsing).

Definition SPStArr (S : Type) := stateArrT S Rel.
Definition SPStExcArr (S : Type) := stateArrT S optionRel.

(** Pin the base equality dictionaries explicitly to avoid recursive
    option/state typeclass search. These aliases add no registrations. *)
Definition ArrowEq_SPStArr (S : Type) : ArrowEq (SPStArr S) :=
  @ArrowEq_stateArrT S Rel ArrowEq_Rel.
Definition ArrowEq_SPStExcArr (S : Type) : ArrowEq (SPStExcArr S) :=
  @ArrowEq_stateArrT S optionRel (@ArrowEq_optionArrT Rel ArrowEq_Rel).

(* ================================================================= *)
(** ** Arrow-view specification types                                 *)
(* ================================================================= *)

Section ArrowSpec.

  Variable S : Type.

  (** Single-option stateful specifications, with carrier
      [(unit * S) -> option (A * S) -> Prop].  The observation determines
      whether [None] describes an exception or divergence. *)
  Definition progRelArr (A : Type) : Type :=
    stateArrT S (optionArrT Rel) unit A.

  (** For [stdivexcnd]: stateful computation with failure and
      divergence.  Unfolds to [(unit * S) -> option (option (A * S)) -> Prop].
      In the [stdivexcnd] reading, raw [None] is divergence,
      [Some None] is an exception, and [Some (Some (a, s'))] is a return. *)
  Definition nditRelArr (A : Type) : Type :=
    stateArrT S (optionArrT (optionArrT Rel)) unit A.

End ArrowSpec.

(* ================================================================= *)
(** ** Monad-view specification types                                 *)
(* ================================================================= *)

Section MonadSpec.

  Variable S : Type.

  (** For [stdivitree]/[stexcnd].  Chains: base [Rel unit] through [optionT]
      and [stateT], inheriting [Monad], [Eq1], and [MonadLawsE] from
      the transformer instances in [ComputationMonads/TransformerLaws.v]. *)
  Definition progRelM (A : Type) : Type :=
    stateT S (optionT (Rel unit)) A.

  (** For [stdivexcnd] (double [optionT] for exception + divergence). *)
  Definition nditRelM (A : Type) : Type :=
    stateT S (optionT (optionT (Rel unit))) A.

End MonadSpec.

(* ================================================================= *)
(** * Relational facts and laws                                      *)
(* ================================================================= *)

(** * Laws for [Rel] and [optionRel].

    This file proves [ArrowLaws], [ArrowChoiceLaws], [ArrowApplyLaws],
    and [ArrowLoopLaws] for the relational arrow [Rel], plus
    [Eq1Equivalence] and [MonadLawsE] for the second-argument monad
    instance on [Rel A].  The [ArrowLaws] / [ArrowChoiceLaws] /
    [ArrowApplyLaws] for [optionRel] are inherited from the generic
    transformer laws in [Classes/OptionArrowT] applied to these. *)

From Coq Require Import FunctionalExtensionality PropExtensionality.
From Hammer Require Import Tactics.


(* ================================================================= *)
(** ** Arrow laws for [Rel]                                          *)
(* ================================================================= *)

(** Helper: [arr_second] simplifies for [Rel].  This is stated as a
    Leibniz equality (using [funext] + [propext] internally) so that
    plain [rewrite] works on it.  [X] is the "extra" (untouched) type. *)
Lemma arr_second_Rel {X A B} (f : Rel A B) :
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

Create HintDb Rel_ops.
#[local] Hint Unfold arr_id arr_comp arr_first arr_pure arr_loop
  arr_left arr_app assoc_prod unassoc_prod swap : Rel_ops.

Local Ltac unfold_Rel_full :=
  autounfold with Rel_ops; unfold Arrow_Rel; simpl;
  repeat match goal with [p : _ * _ |- _] => destruct p end;
  repeat match goal with
  | [H : context[let '(_, _) := ?p in _] |- _] => destruct p
  | [|- context[let '(_, _) := ?p in _]] => destruct p
  end.

(** After [intros a b] the goal [arrow_eq f g] (which unfolds to
    [forall a b, f a b <-> g a b] via [ArrowEq_Rel] / [Rel_eq]) is
    just [f a b <-> g a b]. *)

#[global]
Instance ArrowLaws_Rel : @ArrowLaws Rel Arrow_Rel ArrowEq_Rel.
Proof.
  constructor; intros.
  1-4: intros a b; unfold_Rel_full; sauto limit: 200.
  - (* first_pure *)
    intros [? ?] [? ?]; unfold_Rel_full; sauto limit: 200.
  - (* first_comp *)
    intros [? ?] [? ?]; unfold_Rel_full. split.
    + intros [[b [Hf Hg]] Heq]. subst.
      exists (b, d0); simpl; eauto.
    + intros [[b0 d1] [H1 H2]]; simpl in *.
      destruct H1, H2; subst; split; [exists b0|]; eauto.
  - (* first_fst *)
    intros [? ?] ?; unfold_Rel_full. split.
    + intros [[b0 c0] [H1 H2]]; simpl in *.
      destruct H1; subst; exists a; eauto.
    + intros [a0 [? ?]]; subst. exists (b, c); simpl; eauto.
  - (* first_assoc *)
    intros [[? ?] ?] [? [? ?]]; unfold_Rel_full. split.
    + intros [[[? ?] ?] [H1 H2]]; simpl in *.
      destruct H1 as [[? ?] ?]; inversion H2; subst.
      eexists (a, (_, _)); simpl; eauto.
    + intros [[? [? ?]] [H1 H2]]; simpl in *.
      inversion H1; subst. destruct H2 as [? H2]; inversion H2; subst.
      eexists (_, _, _); simpl; eauto.
  - (* comp_proper *)
    intros f1 f2 Hf g1 g2 Hg a c.
    cbv [arrow_eq ArrowEq_Rel Rel_eq] in Hf, Hg.
    unfold_Rel_full. sauto limit: 200.
  - (* first_proper *)
    intros f1 f2 Hf [a c] [b c'].
    cbv [arrow_eq ArrowEq_Rel Rel_eq] in Hf.
    unfold_Rel_full. sauto limit: 200.
  - (* first_natural *)
    intros [a c] [b d]; cbn. split.
    + intros [[b' c'] [[Hf Hc] Heq]]. cbn in Heq. subst c'.
      inversion Heq; subst. exists (a, g c). cbn. auto.
    + intros [[a' d'] [Heq [Hf Hd]]]. inversion Heq; subst.
      exists (b, c). cbn. auto.
Qed.

#[global]
Instance ArrowChoiceLaws_Rel : ArrowChoiceLaws Rel.
Proof.
  constructor; intros.
  - (* left_pure *)
    intros [a|c] [b|c']; unfold_Rel_full;
    unfold sum_bimap; sauto limit: 200.
  - (* left_comp *)
    intros [a|d] [c|d']; unfold_Rel_full.
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
    intros a [b|c]; unfold_Rel_full.
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
    intros [[a|c]|d] [b|[c'|d']]; unfold_Rel_full;
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
    intros c y; unfold_Rel_full. split.
    + intros [x [Hinr Hleft]]. subst x.
      destruct y as [b|c']; simpl in Hleft; [contradiction | f_equal; exact Hleft].
    + intros Heq. subst y. exists (inr c). simpl. auto.
  - (* left_natural *)
    intros x y.
    destruct x as [a0|c0]; destruct y as [b0|d0]; unfold_Rel_full;
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
    unfold_Rel_full; unfold sum_prod_dist; simpl.
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
    cbv [arrow_eq ArrowEq_Rel Rel_eq] in Hf; unfold_Rel_full;
    try tauto.
    apply Hf.
Qed.

#[global]
Instance ArrowApplyLaws_Rel
  : @ArrowApplyLaws Rel Arrow_Rel ArrowApply_Rel ArrowEq_Rel.
Proof.
  constructor; intros.
  - (* app_law *)
    intros a b; unfold_Rel_full. sauto limit: 200.
  - (* app_unit *)
    intros [a b] [a' b']; cbn. split.
    + intros [[f b0] [[Hf Hb] Hout]]. cbn in *. subst f b0.
      exact Hout.
    + intros Heq. exists ((fun y p => (a, y) = p), b).
      cbn. split; [split; reflexivity | exact Heq].
  - (* app_precompose *)
    intros [f a] c.
    unfold arr_second. cbn. unfold swap. split.
    + intros [[h a'] [[Hh Ha] Hout]]. cbn in *. subst h a'.
      destruct Hout as [b [Hg Hf]].
      exists (f, b). split; [|exact Hf].
      exists (a, f). split; [reflexivity|].
      exists (b, f). cbn. auto.
    + intros [[f' b] [[p [Hp [q [Hg Hq]]]] Hf]].
      destruct p as [a' f''], q as [b' f''']; cbn in *.
      injection Hp as Ha Hf0. subst a' f''.
      destruct Hg as [Hg Hff]. subst f'''.
      injection Hq as Hf0 Hb. subst f' b'.
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
Instance ArrowLoopLaws_Rel : ArrowLoopLaws Rel.
Proof.
  constructor; intros.
  - (* loop_left_tightening *)
    intros a b. unfold_Rel_full. split.
    + intros [c [[b0 c0] [[Hh Heq] Hf]]]. subst c0.
      exists b0; split; [exact Hh | exists c; exact Hf].
    + intros [b0 [Hh [c Hf]]].
      exists c; exists (b0, c); sauto limit: 200.
  - (* loop_right_tightening *)
    intros a c. unfold_Rel_full. split.
    + intros [d [[b0 d0] [Hf [Hg Heq]]]]. subst d0.
      exists b0; split; [exists d; exact Hf | exact Hg].
    + intros [b0 [[d Hf] Hg]].
      exists d; exists (b0, d); sauto limit: 200.
  - (* loop_sliding *)
    intros a b.
    rewrite !arr_second_Rel.
    unfold arr_loop, arr_comp, arr_pure, Arrow_Rel; simpl. split.
    + intros [c [[b0 c0] [Hf [Hk Heq]]]]. subst b0. subst c.
      exists c0. exists (a, k c0). sauto limit: 200.
    + intros [c [[a0 c0] [[Hk Heq] Hf]]]. subst a0.
      exists c0. exists (b, c). sauto limit: 200.
  - (* loop_vanishing *)
    intros a b.
    unfold arr_loop, arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Rel; simpl.
    split.
    + intros [c [d Hf]]. exists (c, d); exists ((a, c), d); split; [reflexivity|].
      exists ((b, c), d); sauto limit: 200.
    + intros [[c d] [p [Heq1 [q [Hf Heq2]]]]].
      inversion Heq1; subst.
      destruct q as [[? ?] ?]; simpl in Heq2; inversion Heq2; subst.
      exists c; exists d; exact Hf.
  - (* loop_superposing *)
    intros [c a0] [c' b0].
    rewrite arr_second_Rel.
    unfold arr_loop; cbn.
    unfold arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Rel, swap; cbn.
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
(** ** Selected law witnesses for the binary specification stacks    *)
(* ================================================================= *)

(** All stack laws lift the existing [Rel] laws through the generic
    state/option transformers. Explicit dictionaries keep the selected
    operations and pointwise iff equality fixed. *)

Definition ArrowLaws_SPStArr (S : Type) : ArrowLaws (SPStArr S) :=
  @ArrowLaws_stateArrT S Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel.
Definition ArrowChoiceLaws_SPStArr (S : Type) : ArrowChoiceLaws (SPStArr S) :=
  @ArrowChoiceLaws_stateArrT S Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
    ArrowLaws_Rel ArrowChoiceLaws_Rel.
Definition ArrowApplyLaws_SPStArr (S : Type) : ArrowApplyLaws (SPStArr S) :=
  @ArrowApplyLaws_stateArrT S Rel Arrow_Rel ArrowApply_Rel ArrowEq_Rel
    ArrowLaws_Rel ArrowApplyLaws_Rel.

Definition ArrowLaws_SPStExcArr (S : Type) : ArrowLaws (SPStExcArr S) :=
  @ArrowLaws_stateArrT S optionRel
    (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowEq_optionArrT Rel ArrowEq_Rel)
    (@ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
      ArrowLaws_Rel ArrowChoiceLaws_Rel).
Definition ArrowChoiceLaws_SPStExcArr (S : Type) : ArrowChoiceLaws (SPStExcArr S) :=
  @ArrowChoiceLaws_stateArrT S optionRel
    (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowChoice_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowEq_optionArrT Rel ArrowEq_Rel)
    (@ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
      ArrowLaws_Rel ArrowChoiceLaws_Rel)
    (@ArrowChoiceLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
      ArrowLaws_Rel ArrowChoiceLaws_Rel).
Definition ArrowApplyLaws_SPStExcArr (S : Type) : ArrowApplyLaws (SPStExcArr S) :=
  @ArrowApplyLaws_stateArrT S optionRel
    (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
    (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel)
    (@ArrowEq_optionArrT Rel ArrowEq_Rel)
    (@ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
      ArrowLaws_Rel ArrowChoiceLaws_Rel)
    (@ArrowApplyLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel
      ArrowEq_Rel ArrowLaws_Rel ArrowChoiceLaws_Rel ArrowApplyLaws_Rel).

(* ================================================================= *)
(** ** Relational congruences for rewriting                          *)
(* ================================================================= *)

(** These restate the existing properness fields with [arrow_eq] reduced
    to [Rel_eq], so congruence applies directly at the head of a goal. *)

Lemma Rel_comp_cong {X Y Z} (R R' : SPureArr X Y) (T T' : SPureArr Y Z) :
  Rel_eq R R' -> Rel_eq T T' ->
  Rel_eq (@arr_comp Rel _ X Y Z R T) (arr_comp R' T').
Proof.
  intros HR HT.
  exact (@comp_proper Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel
           X Y Z R R' HR T T' HT).
Qed.

Lemma Rel_first_cong {X Y C} (R R' : SPureArr X Y) :
  Rel_eq R R' -> Rel_eq (@arr_first Rel _ X Y C R) (arr_first R').
Proof.
  intro HR.
  exact (@first_proper Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel
           X Y C R R' HR).
Qed.

Lemma Rel_left_cong {X Y C} (R R' : SPureArr X Y) :
  Rel_eq R R' -> Rel_eq (@arr_left Rel _ _ X Y C R) (arr_left R').
Proof.
  intro HR.
  exact (@left_proper Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
           ArrowChoiceLaws_Rel X Y C R R' HR).
Qed.
