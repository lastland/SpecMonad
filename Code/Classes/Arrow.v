(** * Arrow typeclasses, laws, and the relational SP arrow.

    We define Hughes-style Arrow typeclasses with their laws,
    then instantiate them with [Pred A B = A -> B -> Prop],
    the category of relations interpreted as forward predicate
    transformers (strongest postcondition arrows).

    Using relations as the base ensures all arrow laws are provable
    without requiring monotonicity or additivity constraints. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From Hammer Require Import Tactics.

(* ================================================================= *)
(** ** Helper functions for products and sums                         *)
(* ================================================================= *)

Definition swap {A B} (p : A * B) : B * A :=
  let '(a, b) := p in (b, a).

Definition assoc_prod {A B C} (p : (A * B) * C) : A * (B * C) :=
  let '((a, b), c) := p in (a, (b, c)).

Definition unassoc_prod {A B C} (p : A * (B * C)) : (A * B) * C :=
  let '(a, (b, c)) := p in ((a, b), c).

Definition sum_bimap {A B C D} (f : A -> C) (g : B -> D) (x : A + B) : C + D :=
  match x with inl a => inl (f a) | inr b => inr (g b) end.

Definition assoc_sum {A B C} (x : (A + B) + C) : A + (B + C) :=
  match x with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition sum_prod_dist {A C D} (p : (A + C) * D) : (A * D) + (C * D) :=
  let '(ac, d) := p in
  match ac with inl a => inl (a, d) | inr c => inr (c, d) end.

Definition swap_sum {A B} (x : A + B) : B + A :=
  match x with inl a => inr a | inr b => inl b end.

(* ================================================================= *)
(** ** Arrow typeclass                                                *)
(* ================================================================= *)

Class Arrow (arr : Type -> Type -> Type) := {
  arr_pure : forall {A B}, (A -> B) -> arr A B ;
  arr_comp : forall {A B C}, arr A B -> arr B C -> arr A C ;
  arr_first : forall {A B C}, arr A B -> arr (A * C)%type (B * C)%type
}.

Section ArrowDerived.
  Context {arr : Type -> Type -> Type} `{Arrow arr}.

  Definition arr_id {A} : arr A A :=
    arr_pure (fun x => x).

  Definition arr_second {A B C} (f : arr A B) : arr (C * A)%type (C * B)%type :=
    arr_comp (arr_pure swap) (arr_comp (arr_first f) (arr_pure swap)).

  Definition arr_split {A B C D} (f : arr A B) (g : arr C D)
    : arr (A * C)%type (B * D)%type :=
    arr_comp (arr_first f) (arr_second g).

  Definition arr_fanout {A B C} (f : arr A B) (g : arr A C)
    : arr A (B * C)%type :=
    arr_comp (arr_pure (fun a => (a, a))) (arr_split f g).
End ArrowDerived.

(* ================================================================= *)
(** ** Arrow equality and laws                                        *)
(* ================================================================= *)

Class ArrowEq (arr : Type -> Type -> Type) := {
  arrow_eq : forall {A B}, arr A B -> arr A B -> Prop ;
  arrow_eq_equiv :: forall A B, Equivalence (@arrow_eq A B)
}.

Class ArrowLaws (arr : Type -> Type -> Type)
  `{Harr : Arrow arr} `{Heq : ArrowEq arr} := {
  comp_id_l : forall {A B} (f : arr A B),
    arrow_eq (arr_comp arr_id f) f ;
  comp_id_r : forall {A B} (f : arr A B),
    arrow_eq (arr_comp f arr_id) f ;
  comp_assoc : forall {A B C D} (f : arr A B) (g : arr B C) (h : arr C D),
    arrow_eq (arr_comp (arr_comp f g) h) (arr_comp f (arr_comp g h)) ;
  pure_comp : forall {A B C} (f : A -> B) (g : B -> C),
    arrow_eq (arr_comp (arr_pure f) (arr_pure g))
             (arr_pure (fun x => g (f x))) ;
  first_pure : forall {A B C} (f : A -> B),
    arrow_eq (@arr_first _ _ A B C (arr_pure f))
             (arr_pure (fun p : A * C => let '(a, c) := p in (f a, c))) ;
  first_comp : forall {A B C D} (f : arr A B) (g : arr B C),
    arrow_eq (@arr_first _ _ _ _ D (arr_comp f g))
             (arr_comp (arr_first f) (arr_first g)) ;
  first_fst : forall {A B C} (f : arr A B),
    arrow_eq (arr_comp (@arr_first _ _ _ _ C f) (arr_pure fst))
             (arr_comp (arr_pure fst) f) ;
  first_assoc : forall {A B C D} (f : arr A B),
    arrow_eq
      (arr_comp (@arr_first _ _ _ _ D (@arr_first _ _ A B C f))
                (arr_pure assoc_prod))
      (arr_comp (arr_pure assoc_prod) (@arr_first _ _ A B (C * D) f)) ;
  comp_proper :: forall (X Y Z : Type),
    Proper (@arrow_eq arr Heq X Y ==> @arrow_eq arr Heq Y Z ==>
            @arrow_eq arr Heq X Z) (@arr_comp arr Harr X Y Z) ;
  first_proper :: forall (X Y Z : Type),
    Proper (@arrow_eq arr Heq X Y ==>
            @arrow_eq arr Heq (X*Z)%type (Y*Z)%type) (@arr_first arr Harr X Y Z)
}.

(* ================================================================= *)
(** ** ArrowChoice                                                    *)
(* ================================================================= *)

Class ArrowChoice (arr : Type -> Type -> Type) `{Arrow arr} := {
  arr_left : forall {A B C}, arr A B -> arr (A + C)%type (B + C)%type
}.

Section ArrowChoiceDerived.
  Context {arr : Type -> Type -> Type} `{ArrowChoice arr}.

  Definition arr_right {A B C} (f : arr A B) : arr (C + A)%type (C + B)%type :=
    arr_comp (arr_pure swap_sum) (arr_comp (arr_left f) (arr_pure swap_sum)).
End ArrowChoiceDerived.

Class ArrowChoiceLaws (arr : Type -> Type -> Type)
  `{ArrowChoice arr} `{ArrowEq arr} := {
  left_pure : forall {A B C} (f : A -> B),
    arrow_eq (@arr_left _ _ _ A B C (arr_pure f))
             (arr_pure (fun x => sum_bimap f (fun c : C => c) x)) ;
  left_comp : forall {A B C D} (f : arr A B) (g : arr B C),
    arrow_eq (@arr_left _ _ _ _ _ D (arr_comp f g))
             (arr_comp (arr_left f) (arr_left g)) ;
  left_inl : forall {A B C} (f : arr A B),
    arrow_eq (arr_comp f (arr_pure (@inl B C)))
             (arr_comp (arr_pure inl) (arr_left f)) ;
  left_assoc : forall {A B C D} (f : arr A B),
    arrow_eq
      (arr_comp (@arr_left _ _ _ _ _ D (@arr_left _ _ _ A B C f))
                (arr_pure assoc_sum))
      (arr_comp (arr_pure assoc_sum) (@arr_left _ _ _ A B (C + D) f)) ;
  left_inr : forall {A B C} (f : arr A B),
    arrow_eq (arr_comp (arr_pure (@inr A C)) (@arr_left _ _ _ A B C f))
             (arr_pure (@inr B C)) ;
  left_natural : forall {A B C D} (f : arr A B) (g : C -> D),
    arrow_eq (arr_comp (@arr_left _ _ _ A B C f)
                       (arr_pure (fun x => sum_bimap (fun b : B => b) g x)))
             (arr_comp (arr_pure (fun x => sum_bimap (fun a : A => a) g x))
                       (@arr_left _ _ _ A B D f)) ;
  first_left_dist : forall {A B C D} (f : arr A B),
    arrow_eq
      (arr_comp (@arr_first _ _ _ _ D (@arr_left _ _ _ A B C f))
                (arr_pure sum_prod_dist))
      (arr_comp (arr_pure sum_prod_dist)
                (@arr_left _ _ _ _ _ (C * D)%type (arr_first f))) ;
  left_proper : forall {A B C},
    Proper (@arrow_eq arr _ A B ==> @arrow_eq arr _ (A + C)%type (B + C)%type)
           (@arr_left _ _ _ A B C)
}.

(* ================================================================= *)
(** ** ArrowApply                                                     *)
(* ================================================================= *)

Class ArrowApply (arr : Type -> Type -> Type) `{Arrow arr} := {
  arr_app : forall {A B}, arr (arr A B * A)%type B
}.

Class ArrowApplyLaws (arr : Type -> Type -> Type)
  `{ArrowApply arr} `{ArrowEq arr} := {
  app_law : forall {A B} (f : arr A B),
    arrow_eq (arr_comp (arr_pure (fun a => (f, a))) arr_app) f
}.

(* ================================================================= *)
(** ** ArrowLoop                                                      *)
(* ================================================================= *)

Class ArrowLoop (arr : Type -> Type -> Type) `{Arrow arr} := {
  arr_loop : forall {A B C}, arr (A * C)%type (B * C)%type -> arr A B
}.

Class ArrowLoopLaws (arr : Type -> Type -> Type)
  `{ArrowLoop arr} `{ArrowEq arr} := {
  loop_left_tightening : forall {A B C D}
    (h : arr A B) (f : arr (B * D)%type (C * D)%type),
    arrow_eq (arr_loop (arr_comp (arr_first h) f))
             (arr_comp h (arr_loop f)) ;
  loop_right_tightening : forall {A B C D}
    (f : arr (A * D)%type (B * D)%type) (g : arr B C),
    arrow_eq (arr_loop (arr_comp f (arr_first g)))
             (arr_comp (arr_loop f) g) ;
  loop_sliding : forall {A B C}
    (f : arr (A * C)%type (B * C)%type) (k : C -> C),
    arrow_eq (arr_loop (arr_comp f (arr_second (arr_pure k))))
             (arr_loop (arr_comp (arr_second (arr_pure k)) f)) ;
  loop_vanishing : forall {A B C D}
    (f : arr ((A * C) * D)%type ((B * C) * D)%type),
    arrow_eq (arr_loop (arr_loop f))
             (arr_loop (arr_comp (arr_pure unassoc_prod)
                         (arr_comp f (arr_pure assoc_prod)))) ;
  loop_superposing : forall {A B C D}
    (f : arr (A * D)%type (B * D)%type),
    arrow_eq (@arr_second _ _ A B C (arr_loop f))
             (arr_loop (arr_comp (arr_pure assoc_prod)
                         (arr_comp (@arr_second _ _ (A*D) (B*D) C f)
                                   (arr_pure unassoc_prod))))
}.

(* ================================================================= *)
(** ** [Pred]: The relational strongest-postcondition arrow          *)
(* ================================================================= *)

(** [Pred A B] is a relation from [A] to [B].  The predicate
    transformer view ([sp], [dp]) is defined in [SPostArr.v]. *)

Definition Pred (A B : Type) : Type := A -> B -> Prop.

(* ================================================================= *)
(** ** [Pred] instances                                              *)
(* ================================================================= *)

Section PredInstances.

  Lemma Pred_eq {A B} (f g : Pred A B) :
    (forall a b, f a b <-> g a b) -> f = g.
  Proof.
    intros H. extensionality a. extensionality b.
    apply propositional_extensionality. apply H.
  Qed.

  #[global]
  Instance ArrowEq_Pred : ArrowEq Pred := {
    arrow_eq := fun A B => @eq (Pred A B)
  }.

  #[global]
  Instance Arrow_Pred : Arrow Pred := {
    arr_pure := fun A B f a b => f a = b ;
    arr_comp := fun A B C f g a c => exists b, f a b /\ g b c ;
    arr_first := fun A B C f p q =>
      let '(a, c) := p in let '(b, c') := q in f a b /\ c = c'
  }.

  #[global]
  Instance ArrowChoice_Pred : ArrowChoice Pred := {
    arr_left := fun A B C f x y =>
      match x, y with
      | inl a, inl b => f a b
      | inr c, inr c' => c = c'
      | _, _ => False
      end
  }.

  #[global]
  Instance ArrowApply_Pred : ArrowApply Pred := {
    arr_app := fun A B p b =>
      let '(f, a) := p in f a b
  }.

  #[global]
  Instance ArrowLoop_Pred : ArrowLoop Pred := {
    arr_loop := fun A B C f a b => exists c, f (a, c) (b, c)
  }.

  (** Helper: [arr_second] simplifies for [Pred]. *)
  Lemma arr_second_Pred {A B C} (f : Pred A B) :
    @arr_second _ _ A B C f =
    fun (p : C * A) (q : C * B) =>
      let '(c, a) := p in let '(c', b) := q in f a b /\ c = c'.
  Proof.
    apply Pred_eq; intros [c a] [c' b].
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

  Ltac unfold_Pred :=
    autounfold with Pred_ops; cbn;
    try rewrite arr_second_Pred.

  (* -------------------------------------------------------------- *)
  (** *** ArrowLaws                                                   *)
  (* -------------------------------------------------------------- *)

  Local Ltac unfold_Pred_full :=
    autounfold with Pred_ops; unfold Arrow_Pred; simpl;
    repeat match goal with [p : _ * _ |- _] => destruct p end;
    repeat match goal with
    | [H : context[let '(_, _) := ?p in _] |- _] => destruct p
    | [|- context[let '(_, _) := ?p in _]] => destruct p
    end.

  #[global]
  Instance ArrowLaws_Pred : ArrowLaws Pred.
  Proof.
    constructor; intros.
    1-4: apply Pred_eq; intros; unfold_Pred_full;
         firstorder (subst; eauto; try congruence).
    - (* first_pure *)
      apply Pred_eq; intros [? ?] [? ?]; unfold_Pred_full;
      firstorder congruence.
    - (* first_comp *)
      apply Pred_eq; intros [? ?] [? ?]; unfold_Pred_full.
      split.
      + intros [[b [Hf Hg]] Heq]. subst.
        exists (b, d0); simpl; eauto.
      + intros [[b0 d1] [H1 H2]]; simpl in *.
        destruct H1, H2; subst; split; [exists b0|]; eauto.
    - (* first_fst *)
      apply Pred_eq; intros [? ?] ?; unfold_Pred_full.
      split.
      + intros [[b0 c0] [H1 H2]]; simpl in *.
        destruct H1; subst; exists a; eauto.
      + intros [a0 [? ?]]; subst. exists (b, c); simpl; eauto.
    - (* first_assoc *)
      apply Pred_eq; intros [[? ?] ?] [? [? ?]]; unfold_Pred_full.
      split.
      + intros [[[? ?] ?] [H1 H2]]; simpl in *.
        destruct H1 as [[? ?] ?]; inversion H2; subst.
        eexists (a, (_, _)); simpl; eauto.
      + intros [[? [? ?]] [H1 H2]]; simpl in *.
        inversion H1; subst. destruct H2 as [? H2]; inversion H2; subst.
        eexists (_, _, _); simpl; eauto.
    - unfold Proper, respectful, arrow_eq, ArrowEq_Pred;
      intros; subst; reflexivity.
    - unfold Proper, respectful, arrow_eq, ArrowEq_Pred;
      intros; subst; reflexivity.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** ArrowChoiceLaws                                             *)
  (* -------------------------------------------------------------- *)

  #[global]
  Instance ArrowChoiceLaws_Pred : ArrowChoiceLaws Pred.
  Proof.
    constructor; intros.
    - (* left_pure *)
      apply Pred_eq; intros [a|c] [b|c']; unfold_Pred;
      unfold sum_bimap; firstorder congruence.
    - (* left_comp *)
      apply Pred_eq; intros [a|d] [c|d']; unfold_Pred.
      + split.
        * intros [b [Hf Hg]]. exists (inl b); eauto.
        * intros [x [H1 H2]]; destruct x as [b|d0];
          [exists b; eauto | simpl in *; contradiction].
      + split; [tauto | intros [x Hx]; destruct x; simpl in *; tauto].
      + split; [tauto | intros [x Hx]; destruct x; simpl in *; tauto].
      + split.
        * intros Heq; subst; exists (inr d'); eauto.
        * intros [[b|d0] [H1 H2]]; simpl in *; [contradiction | congruence].
    - (* left_inl *)
      apply Pred_eq; intros a [b|c]; unfold_Pred.
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
      apply Pred_eq; intros [[a|c]|d] [b|[c'|d']]; unfold_Pred;
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
      apply Pred_eq; intros c y; unfold_Pred.
      split.
      + intros [x [Hinr Hleft]]. subst x.
        destruct y as [b|c']; simpl in Hleft; [contradiction | f_equal; exact Hleft].
      + intros Heq. subst y. exists (inr c). simpl. auto.
    - (* left_natural *)
      apply Pred_eq. intros x y.
      destruct x as [a0|c0]; destruct y as [b0|d0]; unfold_Pred;
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
      apply Pred_eq. intros [[a0|c0] d0] [[b0 d1]|[c1 d1]];
      unfold_Pred; unfold sum_prod_dist; simpl.
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
      unfold Proper, respectful, arrow_eq, ArrowEq_Pred;
      intros; subst; reflexivity.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** ArrowApplyLaws                                              *)
  (* -------------------------------------------------------------- *)

  #[global]
  Instance ArrowApplyLaws_Pred : ArrowApplyLaws Pred.
  Proof.
    constructor; intros.
    apply Pred_eq; intros a b; unfold_Pred.
    split.
    - intros [[g a'] [Heq Happ]]. inversion Heq; subst. exact Happ.
    - intros Hf. exists (f, a). exact (conj eq_refl Hf).
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** ArrowLoopLaws                                               *)
  (* -------------------------------------------------------------- *)

  #[global]
  Instance ArrowLoopLaws_Pred : ArrowLoopLaws Pred.
  Proof.
    constructor; intros; apply Pred_eq; intros.
    - (* loop_left_tightening *)
      unfold_Pred. split.
      + intros [c [[b0 c0] [[Hh Heq] Hf]]]. subst c0.
        exists b0; split; [exact Hh | exists c; exact Hf].
      + intros [b0 [Hh [c Hf]]].
        exists c; exists (b0, c); split; [split; [exact Hh | reflexivity] | exact Hf].
    - (* loop_right_tightening *)
      unfold_Pred. split.
      + intros [d [[b0 d0] [Hf [Hg Heq]]]]. subst d0.
        exists b0; split; [exists d; exact Hf | exact Hg].
      + intros [b0 [[d Hf] Hg]].
        exists d; exists (b0, d); split; [exact Hf | split; [exact Hg | reflexivity]].
    - (* loop_sliding *)
      rewrite !arr_second_Pred.
      unfold arr_loop, arr_comp, arr_pure, Arrow_Pred; simpl. split.
      + intros [c [[b0 c0] [Hf [Hk Heq]]]]. subst b0.
        subst c. exists c0; exists (a, k c0); split; [split; reflexivity | exact Hf].
      + intros [c [[a0 c0] [[Hk Heq] Hf]]]. subst a0.
        exists c0; exists (b, c); split; [exact Hf | split; [exact Hk | reflexivity]].
    - (* loop_vanishing *)
      unfold arr_loop, arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Pred; simpl.
      split.
      + intros [c [d Hf]]. exists (c, d); exists ((a, c), d); split; [reflexivity|].
        exists ((b, c), d); split; [exact Hf | reflexivity].
      + intros [[c d] [p [Heq1 [q [Hf Heq2]]]]].
        inversion Heq1; subst.
        destruct q as [[? ?] ?]; simpl in Heq2; inversion Heq2; subst.
        exists c; exists d; exact Hf.
    - (* loop_superposing *)
      rewrite arr_second_Pred.
      unfold arr_loop; cbn.
      unfold arr_comp, arr_pure, assoc_prod, unassoc_prod, Arrow_Pred, swap; cbn.
      destruct a as [c a0]; destruct b as [c' b0]. split.
      + intros [[d Hf] Heq]. subst c'.
        exists d; exists (c, (a0, d)); split; [reflexivity|].
        exists (c, (b0, d)); split.
        * exists ((a0, d), c); split; [reflexivity|].
          exists ((b0, d), c); split; [split; [exact Hf | reflexivity] | reflexivity].
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

End PredInstances.

(* ================================================================= *)
(** ** Arrow Transformer                                              *)
(* ================================================================= *)

(** An arrow transformer lifts arrows from one type to another,
    analogous to monad transformers. *)

Class ArrowT (T : (Type -> Type -> Type) -> Type -> Type -> Type) := {
  arrowT_lift : forall {arr : Type -> Type -> Type} `{Arrow arr} {A B},
    arr A B -> T arr A B
}.
