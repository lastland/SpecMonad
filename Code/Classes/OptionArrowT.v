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
(** ** Helper for [ArrowChoice] on [optionArrT]                       *)
(* ================================================================= *)

Definition opt_rearrange {B C} (x : option B + C) : option (B + C) :=
  match x with
  | inl (Some b) => Some (inl b)
  | inl None     => None
  | inr c        => Some (inr c)
  end.

(* ================================================================= *)
(** ** Generic [ArrowChoice] and [ArrowApply] for [optionArrT]        *)
(* ================================================================= *)

Section GenericOptionArrTChoice.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}.

  #[global]
  Instance ArrowChoice_optionArrT : ArrowChoice (optionArrT arr) := {
    arr_left := fun A B C f =>
      @arr_comp arr HA _ _ _ (@arr_left arr HA HC _ _ _ f)
        (@arr_pure arr HA _ _ opt_rearrange)
  }.

End GenericOptionArrTChoice.

Section GenericOptionArrTApply.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HAA : @ArrowApply arr HA}.

  #[global]
  Instance ArrowApply_optionArrT : ArrowApply (optionArrT arr) := {
    arr_app := fun A B => @arr_app arr HA HAA A (option B)
  }.

End GenericOptionArrTApply.

(* ================================================================= *)
(** ** Generic [ArrowLaws] for [optionArrT]                           *)
(* ================================================================= *)

Section GenericOptionArrTLaws.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HCL : @ArrowChoiceLaws arr HA HC HE}.

  (* Use explicit law applications to avoid typeclass resolution picking
     the ArrowLaws_optionArrT instance being defined. *)
  Local Notation cassoc   := (@comp_assoc arr HA HE HL).
  Local Notation cidl     := (@comp_id_l arr HA HE HL).
  Local Notation cidr     := (@comp_id_r arr HA HE HL).
  Local Notation pcomp    := (@pure_comp arr HA HE HL).
  Local Notation cprop    := (@comp_proper arr HA HE HL).
  Local Notation fprop    := (@first_proper arr HA HE HL).
  Local Notation fpure    := (@first_pure arr HA HE HL).
  Local Notation fcomp    := (@first_comp arr HA HE HL).
  Local Notation ffst     := (@first_fst arr HA HE HL).
  Local Notation fassoc   := (@first_assoc arr HA HE HL).
  Local Notation lpure    := (@left_pure arr HA HC HE HCL).
  Local Notation lcomp    := (@left_comp arr HA HC HE HCL).
  Local Notation linl     := (@left_inl arr HA HC HE HCL).
  Local Notation lassoc   := (@left_assoc arr HA HC HE HCL).
  Local Notation linr     := (@left_inr arr HA HC HE HCL).
  Local Notation lnat     := (@left_natural arr HA HC HE HCL).
  Local Notation lprop    := (@left_proper arr HA HC HE HCL).

  Local Lemma arr_pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro H. replace f with g by (extensionality x; symmetry; apply H). reflexivity.
  Qed.

  Local Ltac pure_ext :=
    apply arr_pure_ext; intros; try reflexivity; simpl;
    repeat (match goal with [p : _ * _ |- _] => destruct p end);
    try reflexivity.

  Local Ltac opt_unfold :=
    unfold arr_id, arr_comp, arr_pure, arr_first, Arrow_optionArrT,
           arrow_eq, arrow_eq_equiv, ArrowEq_optionArrT;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_left arr HA HC) (@arrow_eq arr HE) (@arrow_eq_equiv arr HE).

  Local Ltac oetrans :=
    etransitivity; [opt_unfold |]; opt_unfold.

  #[global]
  Instance ArrowLaws_optionArrT : ArrowLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros.
    - (* comp_id_l: [Some] >>> [ts] >>> L f >>> [c] = f *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
      (* [inl] >>> L f >>> [c] — now use left_inl to get f >>> [inl] >>> [c] *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity. symmetry. apply linl. }
      (* f >>> [inl] >>> [c] *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
      apply cidr.
    - (* comp_id_r: f >>> [ts] >>> L [Some] >>> [c] = f *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply lpure. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
      (* f >>> [collapse . sum_bimap Some id . to_sum] = f *)
      assert (Hid : @arrow_eq arr HE (option B) (option B)
        (@arr_pure arr HA _ _
          (fun x : option B =>
           collapse (sum_bimap (fun a : B => Some a) (fun c : unit => c) (to_sum x))))
        (@arr_pure arr HA _ _ (fun x => x))).
      { apply arr_pure_ext. intros [?|]; reflexivity. }
      etransitivity. { apply cprop. 1: reflexivity. exact Hid. }
      apply cidr.
    - (* comp_assoc *)
      (* LHS (unfolded): (f >>> [ts] >>> L g >>> [c]) >>> [ts] >>> L h >>> [c]
         RHS (unfolded): f >>> [ts] >>> L (g >>> [ts] >>> L h >>> [c]) >>> [c]

         Strategy:
         1. Rewrite [ts.c] = L[ts] >>> [assoc] >>> [sbm id (const tt)] (pure fun eq)
         2. Use lnat: [sbm id (const tt)] >>> Lh = L_{uu}h >>> [sbm id (const tt)]
         3. Use lassoc: L(Lh) >>> [assoc] = [assoc] >>> L_{uu}h
         4. [assoc] >>> [sbm id (const tt)] >>> [c] = L[c] >>> [c] (pure fun eq)
         5. Collapse with lcomp *)
      (* Core helper: [ts.c] >>> Lh >>> [c] = L([ts] >>> Lh >>> [c]) >>> [c]

         Chain (all fully right-associated):
         E0: [ts.c] >>> Lh >>> [c]
         E1: [sbm ts id] >>> [assoc] >>> [sbm id ctt] >>> Lh >>> [c]
         E2: [sbm ts id] >>> [assoc] >>> L_{uu}h >>> [sbm id ctt] >>> [c]
         E3: [sbm ts id] >>> L(Lh) >>> [assoc] >>> [sbm id ctt] >>> [c]
         E4: [sbm ts id] >>> L(Lh) >>> [sbm c id] >>> [c]
         E5: L[ts] >>> L(Lh) >>> L[c] >>> [c]
         E6: L([ts] >>> Lh >>> [c]) >>> [c]

         E0=E1: pure function equality (Hdecomp + cassoc)
         E1=E2: lnat (naturality)
         E2=E3: lassoc
         E3=E4: pure function equality (Htail)
         E4=E5: lpure (2x)
         E5=E6: lcomp (2x) *)

      (* We express each Ei as a single term and assert the chain.
         To avoid deep cprop navigation, we use cassoc to flatten,
         then apply one law at the boundary. *)

      (* All five-component right-associated compositions *)
      (* No local notations needed - work with explicit terms *)

      assert (Hcore : @arrow_eq arr HE (option C + unit) (option D)
        (@arr_comp arr HA _ _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (fun x : option C + unit => to_sum (collapse x)))
            (@arr_left arr HA HC _ _ _ h))
          (@arr_pure arr HA _ _ (@collapse D)))
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ _
            (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ (@to_sum C))
              (@arr_comp arr HA _ _ _ (@arr_left arr HA HC _ _ _ h)
                (@arr_pure arr HA _ _ (@collapse D)))))
          (@arr_pure arr HA _ _ (@collapse D)))).
      { admit. (* Hcore: requires explicit transitivity terms to avoid evar issues *) }
      (* Now use Hcore to prove the main equation *)
      (* LHS = (f >>> [ts] >>> Lg >>> [c]) >>> [ts] >>> Lh >>> [c]
         RHS = f >>> [ts] >>> L(g >>> [ts] >>> Lh >>> [c]) >>> [c] *)
      (* Step 1: Right-assoc LHS *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cassoc. }
      (* f >>> [ts] >>> Lg >>> ([c] >>> ([ts] >>> Lh >>> [c])) *)
      (* Step 2: [c] >>> [ts] -> [ts.c] *)
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* f >>> [ts] >>> Lg >>> ([ts.c] >>> Lh >>> [c]) *)
      (* Step 3: Left-associate ([ts.c] >>> Lh) >>> [c] for Hcore *)
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. symmetry. apply cassoc. }
      (* f >>> [ts] >>> Lg >>> (([ts.c] >>> Lh) >>> [c]) *)
      (* Step 4: Apply Hcore *)
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. exact Hcore. }
      (* f >>> [ts] >>> Lg >>> (L([ts]>>>Lh>>>[c]) >>> [c]) *)
      (* Step 5: Left-associate Lg >>> L(...) and apply lcomp *)
      apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. symmetry. apply lcomp.
    - (* pure_comp *)
      (* LHS: [Some . f] >>> [ts] >>> L [Some . g] >>> [c]
         RHS: [Some . (g . f)] *)
      (* Pre-prove: [Some . f] >>> [ts] = [inl . f] *)
      assert (H1 : @arrow_eq arr HE A (B + unit)
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a => Some (f a)))
          (@arr_pure arr HA _ _ to_sum))
        (@arr_pure arr HA _ _ (fun a => inl (f a)))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros x. reflexivity. }
      (* Pre-prove: L [Some . g] = [sum_bimap (Some . g) id] *)
      assert (H2 : @arrow_eq arr HE (B + unit) (option C + unit)
        (@arr_left arr HA HC _ _ _ (@arr_pure arr HA _ _ (fun b => Some (g b))))
        (@arr_pure arr HA _ _ (sum_bimap (fun b => Some (g b)) (fun c : unit => c)))).
      { apply lpure. }
      (* Pre-prove: [inl . f] >>> [sum_bimap (Some . g) id] = [inl . Some . g . f] *)
      assert (H3 : @arrow_eq arr HE A (option C + unit)
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a => inl (f a)))
          (@arr_pure arr HA _ _ (sum_bimap (fun b => Some (g b)) (fun c : unit => c))))
        (@arr_pure arr HA _ _ (fun a => @inl (option C) unit (Some (g (f a)))))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros x. reflexivity. }
      (* Pre-prove: [inl . Some . g . f] >>> [c] = [Some . g . f] *)
      assert (H4 : @arrow_eq arr HE A (option C)
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a => @inl (option C) unit (Some (g (f a)))))
          (@arr_pure arr HA _ _ collapse))
        (@arr_pure arr HA _ _ (fun a => Some (g (f a))))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros x. reflexivity. }
      (* Chain: LHS = [Some.f] >>> ([ts] >>> L [Some.g] >>> [c]) *)
      (* right-associate *)
      etransitivity. { symmetry. apply cassoc. }
      (* = ([Some.f] >>> [ts]) >>> L [Some.g] >>> [c] *)
      etransitivity. { apply cprop. 2: reflexivity. exact H1. }
      (* = [inl.f] >>> L [Some.g] >>> [c] *)
      etransitivity. { symmetry. apply cassoc. }
      (* = ([inl.f] >>> L [Some.g]) >>> [c] *)
      etransitivity. { apply cprop. 2: reflexivity.
        etransitivity. { apply cprop. 1: reflexivity. exact H2. }
        exact H3. }
      (* = [inl . Some . g . f] >>> [c] *)
      exact H4.
    - (* first_pure *)
      etransitivity. { apply cprop. 2: reflexivity. apply fpure. }
      etransitivity. { apply pcomp. }
      apply arr_pure_ext. intros [a c]. reflexivity.
    - (* first_comp *)
      (* LHS: F (f >>> [ts] >>> L g >>> [c]) >>> [seq] *)
      (* = F f >>> F [ts] >>> F (L g) >>> F [c] >>> [seq] *)
      admit.
    - (* first_fst *)
      admit.
    - (* first_assoc *)
      admit.
    - (* comp_proper *)
      unfold Proper, respectful. intros f' g' Hfg h' k' Hhk.
      opt_unfold.
      apply cprop; [assumption |].
      apply cprop; [reflexivity |].
      apply cprop; [| reflexivity].
      apply lprop. assumption.
    - (* first_proper *)
      unfold Proper, respectful. intros f' g' Hfg.
      apply cprop; [| reflexivity].
      apply fprop. assumption.
  Admitted.

End GenericOptionArrTLaws.

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
