From Incorrectness.Classes Require Import Arrow ArrowApplyFacts.
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

  Local Notation alaw   := (@app_law arr HA HAA HE HAAL).
  Local Notation aext   := (@app_ext arr HA HAA HE HAAL).

  Local Notation OA := (@Arrow_optionArrT arr HA HC).
  Local Notation OE := (@ArrowEq_optionArrT arr HE).
  Local Notation OL := (@ArrowLaws_optionArrT arr HA HC HE HL HCL).
  Local Notation OApp := (@ArrowApply_optionArrT arr HA HC HAA).
  Local Notation ocassoc := (@comp_assoc _ OA OE OL).
  Local Notation ocidr := (@comp_id_r _ OA OE OL).
  Local Notation ocidl := (@comp_id_l _ OA OE OL).
  Local Notation opcomp := (@pure_comp _ OA OE OL).
  Local Notation ocprop := (@comp_proper _ OA OE OL).
  Local Notation ofpure := (@first_pure _ OA OE OL).
  Local Notation offst := (@first_fst _ OA OE OL).
  Local Notation ofnat := (@first_natural _ OA OE OL).

  Local Lemma option_arr_ext {A B} (f g : optionArrT arr A B) :
    (forall a : A, @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun _ : unit => a)) f)
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun _ : unit => a)) g)) ->
    @arrow_eq _ OE _ _ f g.
  Proof.
    intro H. apply (@ArrowApplyFacts.arrow_ext arr HA HAA HE HL HAAL). intro a.
    etransitivity. { symmetry. apply optionArrT_comp_pure_l. }
    etransitivity. { apply H. }
    apply optionArrT_comp_pure_l.
  Qed.

  Local Lemma option_app_law {A B} (f : optionArrT arr A B) :
    @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun a => (f, a)))
        (@arr_app _ OA OApp _ _)) f.
  Proof.
    etransitivity. { apply optionArrT_comp_pure_l. }
    apply alaw.
  Qed.

  Local Lemma option_app_const {A B} (f : optionArrT arr A B) (a : A) :
    @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun _ : unit => (f, a)))
        (@arr_app _ OA OApp _ _))
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun _ : unit => a)) f).
  Proof.
    symmetry.
    etransitivity.
    { apply ocprop. 1: reflexivity. symmetry. apply option_app_law. }
    etransitivity. { symmetry. apply ocassoc. }
    apply ocprop. 2: reflexivity.
    etransitivity. { apply opcomp. } reflexivity.
  Qed.

  (** Naturality and [first_fst] allow a fixed value to pass beside an
      arbitrary effectful arrow. *)
  Local Lemma option_first_const {A B C}
    (f : optionArrT arr A B) (c : C) :
    @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun a => (a, c)))
        (@arr_first _ OA _ _ _ f))
      (@arr_comp _ OA _ _ _ f (@arr_pure _ OA _ _ (fun b => (b, c)))).
  Proof.
    assert (Hhead : @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _
        (@arr_pure _ OA _ _ (fun a : A => (a, tt)))
        (@arr_pure _ OA _ _ (fun '(a, _) => (a, c))))
      (@arr_pure _ OA _ _ (fun a : A => (a, c)))).
    { etransitivity. { apply opcomp. } reflexivity. }
    assert (Htail : @arrow_eq _ OE _ _
      (@arr_pure _ OA _ _ (fun p : B * unit => let '(b, _) := p in (b, c)))
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (@fst B unit))
        (@arr_pure _ OA _ _ (fun b => (b, c))))).
    { symmetry. etransitivity. { apply opcomp. }
      unfold arr_pure, Arrow_optionArrT.
      apply (@ArrowApplyFacts.pure_ext arr HA HAA HE HL HAAL).
      intros [b []]. reflexivity. }
    etransitivity. { apply ocprop. 2: reflexivity. symmetry. exact Hhead. }
    etransitivity. { apply ocassoc. }
    etransitivity. { apply ocprop. 1: reflexivity. symmetry. apply ofnat. }
    etransitivity.
    { apply ocprop. 1: reflexivity. apply ocprop. 1: reflexivity. exact Htail. }
    etransitivity.
    { apply ocprop. 1: reflexivity. symmetry. apply ocassoc. }
    etransitivity.
    { apply ocprop. 1: reflexivity. apply ocprop. 2: reflexivity. apply offst. }
    etransitivity. { apply ocprop. 1: reflexivity. apply ocassoc. }
    etransitivity. { symmetry. apply ocassoc. }
    etransitivity. { apply ocprop. 2: reflexivity. apply opcomp. }
    apply ocidl.
  Qed.

  Local Lemma option_second_const {A B C}
    (f : optionArrT arr A B) (c : C) :
    @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun a => (c, a)))
        (@arr_second _ OA _ _ _ f))
      (@arr_comp _ OA _ _ _ f (@arr_pure _ OA _ _ (fun b => (c, b)))).
  Proof.
    unfold arr_second.
    etransitivity. { symmetry. apply ocassoc. }
    etransitivity. { apply ocprop. 2: reflexivity. apply opcomp. }
    etransitivity. { symmetry. apply ocassoc. }
    etransitivity. { apply ocprop. 2: reflexivity. apply option_first_const. }
    etransitivity. { apply ocassoc. }
    apply ocprop. 1: reflexivity.
    etransitivity. { apply opcomp. } reflexivity.
  Qed.

  #[global]
  Instance ArrowApplyLaws_optionArrT : ArrowApplyLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor.
    - exact (@option_app_law).
    - (* app_unit *)
      intros A B. apply option_arr_ext. intros [a b].
      etransitivity. { symmetry. apply ocassoc. }
      etransitivity.
      { apply ocprop. 2: reflexivity.
        apply ocprop. 1: reflexivity. apply ofpure. }
      etransitivity. { apply ocprop. 2: reflexivity. apply opcomp. }
      etransitivity. { apply option_app_const. }
      etransitivity. { apply opcomp. }
      symmetry. apply ocidr.
    - (* app_precompose *)
      intros A B C g. apply option_arr_ext. intros [f a].
      etransitivity. { symmetry. apply ocassoc. }
      etransitivity.
      { apply ocprop. 2: reflexivity.
        apply ocprop. 1: reflexivity. apply ofpure. }
      etransitivity. { apply ocprop. 2: reflexivity. apply opcomp. }
      etransitivity. { apply option_app_const. }
      symmetry.
      etransitivity. { symmetry. apply ocassoc. }
      assert (Hpair : @arrow_eq _ OE _ _
        (@arr_pure _ OA _ _ (fun _ : unit => (f, a)))
        (@arr_comp _ OA _ _ _
          (@arr_pure _ OA _ _ (fun _ : unit => a))
          (@arr_pure _ OA _ _ (fun b => (f, b))))).
      { symmetry. etransitivity. { apply opcomp. } reflexivity. }
      etransitivity.
      { apply ocprop. 2: reflexivity.
        etransitivity. { apply ocprop. 2: reflexivity. exact Hpair. }
        etransitivity. { apply ocassoc. }
        apply ocprop. 1: reflexivity. apply option_second_const. }
      etransitivity. { apply ocassoc. }
      apply ocprop. 1: reflexivity.
      etransitivity. { apply ocassoc. }
      apply ocprop. 1: reflexivity. apply option_app_law.
    - (* app_postcompose *)
      intros A B C h. apply option_arr_ext. intros [f a].
      etransitivity. { symmetry. apply ocassoc. }
      etransitivity.
      { apply ocprop. 2: reflexivity.
        apply ocprop. 1: reflexivity. apply ofpure. }
      etransitivity. { apply ocprop. 2: reflexivity. apply opcomp. }
      etransitivity. { apply option_app_const. }
      symmetry.
      etransitivity. { symmetry. apply ocassoc. }
      etransitivity. { apply ocprop. 2: reflexivity. apply option_app_const. }
      apply ocassoc.
    - (* app_ext is inherited directly by the underlying application. *)
      intros X A B u v H.
      etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry. apply aext. exact H.
  Qed.

End GenericOptionArrTApplyLaws.
