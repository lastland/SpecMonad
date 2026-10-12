(** Preservation laws for the option lift. *)
From Coq Require Import Morphisms.
From Incorrectness.Classes Require Import Arrow ArrowApplyFacts.
From Incorrectness.Classes.OptionArrowT Require Import Core ArrowLaws.

Section OptionLift.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HE : ArrowEq arr}
    (HL : @ArrowLaws arr HA HE) (HCL : @ArrowChoiceLaws arr HA HC HE).
  Local Existing Instance HL.
  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 50, left associativity).
  Local Notation pure := (@arr_pure arr HA _ _).
  Local Notation eqA := (@arrow_eq arr HE _ _).

  #[global] Instance ArrowTLaw_optionArrT :
    ArrowTLaw optionArrT ArrowT_optionArrT arr HA HE
      (@Arrow_optionArrT arr HA HC) (@ArrowEq_optionArrT arr HE).
  Proof.
    constructor.
    - intros A B f g H. apply (@comp_proper arr HA HE HL); [exact H | reflexivity].
    - intros A B f. apply (@pure_comp arr HA HE HL).
    - intros A B C f g.
      cbn [arrowT_lift ArrowT_optionArrT arrow_eq ArrowEq_optionArrT
        arr_comp Arrow_optionArrT].
      symmetry. rewrite (@comp_assoc arr HA HE HL).
      transitivity (f >>> (g >>> pure (@Some C))).
      + apply (@comp_proper arr HA HE HL). 1: reflexivity.
        change (eqA
          (@arr_comp _ (@Arrow_optionArrT arr HA HC) B B C
            (@arr_pure _ (@Arrow_optionArrT arr HA HC) B B (fun x => x))
            (g >>> pure (@Some C))) (g >>> pure (@Some C))).
        etransitivity.
        { apply (@optionArrT_comp_pure_l arr HA HC HE HL HCL). }
        apply (@comp_id_l arr HA HE HL).
      + symmetry. apply (@comp_assoc arr HA HE HL).
    - intros A B C f.
      cbn [arrowT_lift ArrowT_optionArrT arrow_eq ArrowEq_optionArrT
        arr_first Arrow_optionArrT].
      rewrite (@first_comp arr HA HE HL).
      rewrite (@comp_assoc arr HA HE HL).
      apply (@comp_proper arr HA HE HL). 1: reflexivity.
      symmetry. etransitivity.
      { apply (@comp_proper arr HA HE HL). 2: reflexivity.
        apply (@first_pure arr HA HE HL). }
      apply (@pure_comp_ext arr HA HE HL (@arr_pure_ext arr HA HE)).
      intros [b c]. reflexivity.
  Qed.

  #[global] Instance ArrowChoiceTLaw_optionArrT :
    ArrowChoiceTLaw optionArrT ArrowT_optionArrT arr HA HC HE
      (@Arrow_optionArrT arr HA HC) (@ArrowChoice_optionArrT arr HA HC)
      (@ArrowEq_optionArrT arr HE).
  Proof.
    constructor. intros A B C f.
    cbn [arrowT_lift ArrowT_optionArrT arrow_eq ArrowEq_optionArrT
      arr_left ArrowChoice_optionArrT].
    rewrite (@left_comp arr HA HC HE HCL).
    rewrite (@comp_assoc arr HA HE HL).
    apply (@comp_proper arr HA HE HL). 1: reflexivity.
    symmetry. etransitivity.
    { apply (@comp_proper arr HA HE HL). 2: reflexivity.
      apply (@left_pure arr HA HC HE HCL). }
    apply (@pure_comp_ext arr HA HE HL (@arr_pure_ext arr HA HE)).
    intros [b|c]; reflexivity.
  Qed.

  Context {HX : @ArrowApply arr HA} (HXL : @ArrowApplyLaws arr HA HX HE).
  #[global] Instance ArrowApplyTLaw_optionArrT :
    ArrowApplyTLaw optionArrT ArrowT_optionArrT arr HA HX HE
      (@Arrow_optionArrT arr HA HC) (@ArrowApply_optionArrT arr HA HC HX)
      (@ArrowEq_optionArrT arr HE).
  Proof.
    constructor. intros A B. symmetry.
    etransitivity.
    { apply (@optionArrT_comp_pure_l arr HA HC HE HL HCL). }
    change (eqA
      (pure (fun '(f, a) => (f >>> pure (@Some B), a)) >>>
        @arr_app arr HA HX A (option B))
      (@arr_app arr HA HX A B >>> pure (@Some B))).
    assert (Hmap : eqA
      (pure (fun p : arr A B * A => let '(f, a) := p in (f >>> pure (@Some B), a)))
      (pure (fun p : arr A B * A => (fst p >>> pure (@Some B), snd p)))).
    { f_equiv. intros [f a]. reflexivity. }
    rewrite Hmap.
    etransitivity.
    { exact (@app_postcompose_pure arr HA HX HE HL HXL
        (arr A B * A)%type A B (option B) fst snd (pure (@Some B))). }
    apply (@comp_proper arr HA HE HL). 2: reflexivity.
    assert (Hid : eqA (pure (fun p : arr A B * A => (fst p, snd p)))
      (@arr_id arr HA _)).
    { unfold arr_id. f_equiv. intros [f a]. reflexivity. }
    rewrite Hid. apply (@comp_id_l arr HA HE HL).
  Qed.
End OptionLift.
