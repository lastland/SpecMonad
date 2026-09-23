From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.OptionArrowT Require Import Core ArrowLaws.

(* ================================================================= *)
(** ** Generic [ArrowApplyLaws] for [optionArrT]                      *)
(* ================================================================= *)

Section GenericOptionArrTApplyLaws.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HAA : @ArrowApply arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HCL : @ArrowChoiceLaws arr HA HC HE}
          `{HAAL : @ArrowApplyLaws arr HA HAA HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl   := (@comp_id_l arr HA HE HL).
  Local Notation cidr   := (@comp_id_r arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation linl   := (@left_inl arr HA HC HE HCL).
  Local Notation alaw   := (@app_law arr HA HAA HE HAAL).

  (** Base-arrow shorthands: each goal below is an equality of BASE
      arrows once the [optionArrT] operations are unfolded. *)
  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 41, right associativity).
  Local Notation pur := (@arr_pure arr HA _ _).
  Local Notation app0 := (@arr_app arr HA HAA _ _).
  Local Notation lft := (@arr_left arr HA HC _ _ _).
  Local Notation "f == g" := (@arrow_eq arr HE _ _ f g) (at level 70).

  Local Lemma pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) -> pur f == pur g.
  Proof. apply arr_pure_ext. Qed.

  (** *** The shape every [optionArrT] law presents                    *)

  (** Composing with [T.app] on the right: the [Some] injected by
      [T.pure] is exactly what [to_sum]/[arr_left]/[collapse] strip
      again, so the whole stack is one base [app] after one pure. *)
  Local Lemma app_option_pure {X A B} (psi : X -> (optionArrT arr A B * A)) :
    pur (fun x => Some (psi x))
      >>> (pur to_sum >>> (lft app0 >>> pur collapse))
    == pur psi >>> app0.
  Proof.
    etransitivity; [ symmetry; apply cassoc |].
    etransitivity.
    { apply cprop; [ apply pcomp | reflexivity ]. }
    etransitivity.
    { apply cprop; [| reflexivity ].
      apply (pure_ext _ (fun x => inl (psi x))). intro x. reflexivity. }
    etransitivity.
    { apply cprop; [| reflexivity ]. symmetry.
      apply (pcomp psi (@inl (optionArrT arr A B * A)%type unit)). }
    etransitivity; [ apply cassoc |].
    apply cprop; [ reflexivity |].
    etransitivity; [ symmetry; apply cassoc |].
    etransitivity.
    { apply cprop; [| reflexivity ]. symmetry. apply linl. }
    etransitivity; [ apply cassoc |].
    etransitivity.
    { apply cprop; [ reflexivity |].
      etransitivity; [ apply pcomp |].
      apply (pure_ext _ (fun x => x)). intro x. reflexivity. }
    apply cidr.
  Qed.

  (** The same after a [T.first], which parks the argument in the second
      component. *)
  Local Lemma app_option_first {X A B} (phi : X -> optionArrT arr A B) :
    ((@arr_first arr HA _ _ _ (pur (fun x => Some (phi x))))
       >>> pur sequence_option)
      >>> (pur to_sum >>> (lft app0 >>> pur collapse))
    == pur (fun p : X * A => (phi (fst p), snd p)) >>> app0.
  Proof.
    etransitivity.
    { apply cprop; [| reflexivity ].
      etransitivity; [ apply cprop; [ apply first_pure | reflexivity ] |].
      etransitivity; [ apply pcomp |].
      apply (pure_ext _ (fun p : X * A => Some (phi (fst p), snd p))).
      intros [x a]. reflexivity. }
    apply app_option_pure.
  Qed.

  #[global]
  Instance ArrowApplyLaws_optionArrT : ArrowApplyLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros.
    all: unfold arr_id, arr_comp, arr_pure, arr_first, arr_app,
                Arrow_optionArrT, ArrowApply_optionArrT,
                arrow_eq, ArrowEq_optionArrT;
         fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
              (@arr_left arr HA HC) (@arr_app arr HA HAA) (@arrow_eq arr HE).
    - (* app_law *)
      etransitivity; [ apply (app_option_pure (fun a => (f, a))) |].
      apply alaw.
    - (* app_pair *)
      etransitivity; [ apply app_option_first |].
      etransitivity.
      { apply (@app_ext_at arr HA HAA HE HAAL (A * B)%type B (option (A * B))%type
                 _ (fun p : A * B =>
                      pur (fun y : B => (fst p, y)) >>> pur (@Some (A * B)))
                 (fun p : A * B => snd p)).
        intro p. symmetry.
        etransitivity; [ apply pcomp |].
        apply pure_ext. intro y. reflexivity. }
      etransitivity;
        [ apply (@app_post_at arr HA HAA HE HL HAAL _ _ _ _
                   (fun p : A * B => pur (fun y : B => (fst p, y)))
                   (fun p : A * B => snd p) (pur (@Some (A * B)))) |].
      etransitivity.
      { apply cprop; [| reflexivity ].
        apply (@app_pair_at arr HA HAA HE HL HAAL _ _ _
                 (fun p : A * B => fst p) (fun p : A * B => snd p)). }
      etransitivity; [ apply pcomp |].
      apply pure_ext. intros [a b]. reflexivity.
    - (* app_post *)
      etransitivity; [ apply app_option_first |].
      etransitivity;
        [ apply (@app_post_at arr HA HAA HE HL HAAL _ _ _ _
                   (fun p : optionArrT arr A B * A => fst p)
                   (fun p : optionArrT arr A B * A => snd p)
                   (pur to_sum >>> (lft h >>> pur collapse))) |].
      apply cprop; [| reflexivity ].
      etransitivity.
      { apply cprop; [| reflexivity ].
        apply (pure_ext _ (fun p : optionArrT arr A B * A => p)).
        intros [f a]. reflexivity. }
      apply cidl.
    - (* app_ext *)
      etransitivity; [ apply (app_option_pure (fun x => (u x, t x))) |].
      etransitivity.
      { apply (@app_ext_at arr HA HAA HE HAAL X A (option B) u v t).
        intro x. apply H. }
      symmetry. apply (app_option_pure (fun x => (v x, t x))).
  Qed.

End GenericOptionArrTApplyLaws.
