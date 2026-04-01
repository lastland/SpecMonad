(** * Option arrow transformer.

    [optionArrT arr A B := arr A (option B)] lifts an arrow with
    option-aware composition (failure propagation).

    A generic [Arrow] instance is provided for any base arrow with
    [ArrowChoice], using the encoding [option B ≅ B + unit].

    Concrete instances for [optionArrT SPArr] are also given. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Definition                                                      *)
(* ================================================================= *)

Definition optionArrT (arr : Type -> Type -> Type) A B := arr A (option B).

(* ================================================================= *)
(** ** Helper functions                                                *)
(* ================================================================= *)

Definition to_sum {B} (ob : option B) : B + unit :=
  match ob with Some b => inl b | None => inr tt end.

Definition collapse {C} (x : option C + unit) : option C :=
  match x with inl oc => oc | inr _ => None end.

Definition sequence_option {A B} (p : option A * B) : option (A * B) :=
  match p with (Some a, b) => Some (a, b) | (None, _) => None end.

(* ================================================================= *)
(** ** Generic [Arrow] instance for [optionArrT]                      *)
(* ================================================================= *)

(** For any arrow with [ArrowChoice], [optionArrT arr] is an arrow.
    The key idea: [arr_left] routes [Some] values through the next
    arrow while propagating [None] unchanged.

    - [arr_pure f := arr_pure (Some ∘ f)]
    - [arr_comp f g := f >>> pure to_sum >>> left g >>> pure collapse]
    - [arr_first f := first f >>> pure sequence_option] *)

Section GenericOptionArrT.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}.

  #[global]
  Instance Arrow_optionArrT : Arrow (optionArrT arr) := {
    arr_pure := fun A B f =>
      @arr_pure arr HA _ _ (fun a => Some (f a)) ;
    arr_comp := fun A B C f g =>
      @arr_comp arr HA _ _ _ f
        (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ to_sum)
          (@arr_comp arr HA _ _ _ (@arr_left arr HA HC _ _ _ g)
            (@arr_pure arr HA _ _ collapse))) ;
    arr_first := fun A B C f =>
      @arr_comp arr HA _ _ _
        (@arr_first arr HA _ _ _ f)
        (@arr_pure arr HA _ _ sequence_option)
  }.

  #[global]
  Instance ArrowT_optionArrT : ArrowT optionArrT := {
    arrowT_lift := fun arr0 _ A B f => arr_comp f (arr_pure (@Some B))
  }.

End GenericOptionArrT.

(* ================================================================= *)
(** ** Generic [ArrowEq] for [optionArrT]                             *)
(* ================================================================= *)

Section GenericOptionArrTEq.

  Context {arr : Type -> Type -> Type} `{HE : ArrowEq arr}.

  #[global]
  Instance ArrowEq_optionArrT : ArrowEq (optionArrT arr) := {
    arrow_eq := fun A B => @arrow_eq arr HE A (option B) ;
    arrow_eq_equiv := fun A B => @arrow_eq_equiv arr HE A (option B)
  }.

End GenericOptionArrTEq.

(* ================================================================= *)
(** ** Instances for [optionArrT SPArr]                                *)
(* ================================================================= *)

Section OptionSPArrInstances.

  Definition optionSPArr := optionArrT SPArr.

  Lemma optionSPArr_eq {A B} (f g : optionSPArr A B) :
    (forall a ob, f a ob <-> g a ob) -> f = g.
  Proof.
    intros H. extensionality a. extensionality ob.
    apply propositional_extensionality. apply H.
  Qed.

  (** The generic [Arrow_optionArrT] gives the correct SPArr instance
      via [ArrowChoice_SPArr].  We verify this matches the manual
      definitions by providing simplified characterizations. *)

  (** Unfold the generic comp for SPArr into a direct relational form. *)
  Lemma optionArrT_comp_SPArr {A B C}
    (f : optionSPArr A B) (g : optionSPArr B C) :
    @arr_comp _ Arrow_optionArrT A B C f g =
    fun a oc => match oc with
      | Some c => exists b, f a (Some b) /\ g b (Some c)
      | None => f a None \/ exists b, f a (Some b) /\ g b None
    end.
  Proof.
    apply optionSPArr_eq; intros a oc.
    unfold arr_comp at 1, Arrow_optionArrT, Arrow_SPArr, ArrowChoice_SPArr.
    cbn. unfold to_sum, collapse.
    destruct oc as [c|].
    - (* Some c *)
      split.
      + intros [ob [Hf [x [Hts [y [Hleft Hcoll]]]]]].
        destruct ob as [b|]; simpl in Hts; subst x;
        destruct y as [[c0|]|[]]; simpl in *;
        try destruct Hleft; try discriminate.
        injection Hcoll as ->. exists b. auto.
      + intros [b [Hf Hg]].
        exists (Some b). split; [exact Hf|].
        exists (inl b). split; [reflexivity|].
        exists (inl (Some c)). split; [exact Hg | reflexivity].
    - (* None *)
      split.
      + intros [ob [Hf [x [Hts [y [Hleft Hcoll]]]]]].
        destruct ob as [b|]; simpl in Hts; subst x;
        destruct y as [[c0|]|[]]; simpl in *;
        try destruct Hleft; try discriminate.
        * right. exists b. auto.
        * left. exact Hf.
      + intros [Hf | [b [Hf Hg]]].
        * exists None. split; [exact Hf|].
          exists (inr tt). split; [reflexivity|].
          exists (inr tt). split; [reflexivity | reflexivity].
        * exists (Some b). split; [exact Hf|].
          exists (inl b). split; [reflexivity|].
          exists (inl None). split; [exact Hg | reflexivity].
  Qed.

  (** Unfold the generic first for SPArr. *)
  Lemma optionArrT_first_SPArr {A B C}
    (f : optionSPArr A B) :
    @arr_first _ Arrow_optionArrT A B C f =
    fun p oq => let '(a, c) := p in
      match oq with
      | Some (b, c') => f a (Some b) /\ c = c'
      | None => f a None
      end.
  Proof.
    apply optionSPArr_eq; intros [a c] oq.
    unfold arr_first at 1, Arrow_optionArrT, Arrow_SPArr.
    cbn. unfold sequence_option.
    destruct oq as [[b c']|].
    - split.
      + intros [[ob d] [[Hf Hd] Heq]]. simpl in *.
        destruct ob; [injection Heq as -> -> | discriminate].
        exact (conj Hf Hd).
      + intros [Hf Hc]. subst. exists (Some b, c'). auto.
    - split.
      + intros [[ob d] [[Hf Hd] Heq]]. simpl in *.
        destruct ob; [discriminate | ]. subst. exact Hf.
      + intros Hf. exists (None, c). simpl. auto.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** ArrowChoice, ArrowApply, ArrowLoop for [optionSPArr]        *)
  (* -------------------------------------------------------------- *)

  #[global]
  Instance ArrowChoice_optionSPArr : ArrowChoice optionSPArr := {
    arr_left := fun A B C f x oy =>
      match x, oy with
      | inl a, Some (inl b) => f a (Some b)
      | inl a, None => f a None
      | inr c, Some (inr c') => c = c'
      | _, _ => False
      end
  }.

  #[global]
  Instance ArrowApply_optionSPArr : ArrowApply optionSPArr := {
    arr_app := fun A B p ob =>
      let '(f, a) := p in f a ob
  }.

  #[global]
  Instance ArrowLoop_optionSPArr : ArrowLoop optionSPArr := {
    arr_loop := fun A B C f a ob =>
      match ob with
      | Some b => exists c, f (a, c) (Some (b, c))
      | None => exists c, f (a, c) None
      end
  }.

  (* -------------------------------------------------------------- *)
  (** *** ArrowLaws for [optionSPArr]                                  *)
  (* -------------------------------------------------------------- *)

  Local Ltac unfold_optionSPArr :=
    unfold optionSPArr, optionArrT, arr_id, arr_second;
    try rewrite optionArrT_comp_SPArr;
    try rewrite optionArrT_first_SPArr;
    unfold arr_comp, arr_first, arr_pure, arr_loop,
           arr_left, arr_app, Arrow_optionArrT,
           swap; simpl.

  Local Ltac destruct_options :=
    repeat match goal with
    | [ob : option _ |- _] => destruct ob
    | [p : _ * _ |- _] => destruct p
    | [s : _ + _ |- _] => destruct s
    end; simpl in *.

  #[global]
  Instance ArrowLaws_optionSPArr : ArrowLaws optionSPArr.
  Proof.
    constructor; intros.
    - (* comp_id_l *)
      apply optionSPArr_eq; intros a [c|]; rewrite optionArrT_comp_SPArr;
      unfold arr_pure, Arrow_optionArrT; cbn.
      + split; [intros [b [Heq Hf]]; injection Heq as Heq; subst; exact Hf |
                intros Hf; exists a; eauto].
      + split; [intros [Habs | [b [Heq Hf]]]; [discriminate Habs | injection Heq as Heq; subst; exact Hf] |
                intros Hf; right; exists a; eauto].
    - (* comp_id_r *)
      apply optionSPArr_eq; intros a [c|]; rewrite optionArrT_comp_SPArr;
      unfold arr_pure, Arrow_optionArrT; cbn.
      + split; [intros [b [Hf Heq]]; injection Heq as Heq; subst; exact Hf |
                intros Hf; exists c; eauto].
      + split; [intros [H | [b [Hf Habs]]]; [exact H | discriminate Habs] |
                intros Hf; left; exact Hf].
    - (* comp_assoc *)
      apply optionSPArr_eq; intros a [d|]; rewrite !optionArrT_comp_SPArr.
      + split.
        * intros [c [[b [Hf Hg]] Hh]]. exists b; split; [exact Hf|]. exists c; eauto.
        * intros [b [Hf [c [Hg Hh]]]]. exists c; split; [exists b|]; eauto.
      + split.
        * intros [[Hf | [b [Hf Hg]]] | [c [[b [Hf Hg]] Hh]]].
          -- left. exact Hf.
          -- right. exists b; split; [exact Hf | left; exact Hg].
          -- right. exists b; split; [exact Hf | right; exists c; eauto].
        * intros [Hf | [b [Hf [Hg | [c [Hg Hh]]]]]].
          -- left. left. exact Hf.
          -- left. right. exists b; eauto.
          -- right. exists c; split; [exists b; eauto | exact Hh].
    - (* pure_comp *)
      apply optionSPArr_eq; intros a [c|]; rewrite optionArrT_comp_SPArr;
      unfold arr_pure, Arrow_optionArrT; cbn.
      + split; [intros [b [Heq1 Heq2]]; injection Heq1 as Heq1; injection Heq2 as Heq2; subst; reflexivity |
                intros Heq; exists (f a); eauto].
      + split; [intros [H | [? [_ H]]]; discriminate H | intros H; discriminate H].
    - (* first_pure *)
      apply optionSPArr_eq; intros [a c] [[b c']|]; rewrite optionArrT_first_SPArr;
      unfold arr_pure, Arrow_optionArrT; cbn.
      + split; [intros [Heq Hc]; injection Heq as Heq; subst; reflexivity |
                intro H; injection H as H1 H2; subst; eauto].
      + split; [intros H; discriminate H | intros H; discriminate H].
    - (* first_comp *)
      apply optionSPArr_eq; intros [a d] [[c d']|];
      rewrite optionArrT_first_SPArr, !optionArrT_comp_SPArr;
      rewrite !optionArrT_first_SPArr.
      + split.
        * intros [[b [Hf Hg]] Heq]; subst d'.
          exists (b, d); simpl; eauto.
        * intros [[b0 d0] H]; simpl in H.
          destruct H as [[Hf Heq1] [Hg Heq2]]; subst.
          split; [exists b0; eauto | reflexivity].
      + split.
        * intros [Hf | [b [Hf Hg]]].
          -- left. exact Hf.
          -- right. exists (b, d); simpl; eauto.
        * intros [Hf | [[b d0] H]]; simpl in *.
          -- left. exact Hf.
          -- destruct H as [[Hf Heq] Hg]; subst.
             right. exists b; eauto.
    - (* first_fst *)
      apply optionSPArr_eq; intros [a c] [b|];
      rewrite !optionArrT_comp_SPArr;
      rewrite !optionArrT_first_SPArr;
      unfold arr_pure, Arrow_optionArrT; cbn.
      + split.
        * intros [[b0 c0] H]; simpl in H.
          destruct H as [[Hf Hc] Heq]; injection Heq as Heq; subst.
          exists a; eauto.
        * intros [a0 [Heq Hf]]; injection Heq as Heq; subst.
          exists (b, c); simpl; eauto.
      + split.
        * intros [Hf | [[b0 c0] H]]; simpl in *.
          -- right. exists a; eauto.
          -- destruct H as [_ Habs]; discriminate Habs.
        * intros [Habs | [a0 [Heq Hf]]].
          -- discriminate Habs.
          -- injection Heq as Heq; subst. left. exact Hf.
    - (* first_assoc *)
      apply optionSPArr_eq; intros [[a c] d] [ob|];
      rewrite !optionArrT_comp_SPArr, !optionArrT_first_SPArr;
      unfold arr_pure, Arrow_optionArrT, assoc_prod; cbn.
      + destruct ob as [b [c' d']]. split.
        * intros [[[b0 c0] d0] H]; simpl in H.
          destruct H as [[[Hf Hc] Hd] Heq].
          subst c0 d0. inversion Heq; subst.
          exists (a, (c', d')); simpl; split; [reflexivity|].
          split; [exact Hf | reflexivity].
        * intros [[a0 [c0 d0]] H]; simpl in H.
          destruct H as [Hassoc Hrest].
          inversion Hassoc; subst.
          destruct Hrest as [Hf Heq_cd].
          inversion Heq_cd; subst.
          eexists (_, _, _); simpl; eauto.
      + split.
        * intros [Hf | [[[b0 c0] d0] [_ Habs]]]; [| discriminate Habs].
          right. exists (a, (c, d)). split; [reflexivity | exact Hf].
        * intros [Habs | [[a0 [c0 d0]] [Heq Hf]]]; [discriminate Habs | ].
          inversion Heq; subst. left. exact Hf.
    - (* comp_proper *)
      unfold Proper, respectful; intros;
      cbv [arrow_eq ArrowEq_optionArrT ArrowEq_SPArr] in *;
      subst; reflexivity.
    - (* first_proper *)
      unfold Proper, respectful; intros;
      cbv [arrow_eq ArrowEq_optionArrT ArrowEq_SPArr] in *;
      subst; reflexivity.
  Qed.

End OptionSPArrInstances.
