(** Preservation laws for the state lift, independently of transformed laws. *)
From Incorrectness.Classes Require Import Arrow ArrowApplyFacts.
From Incorrectness.Classes.StateArrowT Require Import Core.

Section StateLift.
  Context (S : Type) {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HE : ArrowEq arr} (HL : @ArrowLaws arr HA HE).
  Local Existing Instance HL.
  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 50, left associativity).
  Local Notation pure := (@arr_pure arr HA _ _).
  Local Notation first := (@arr_first arr HA _ _ _).
  Local Notation eqA := (@arrow_eq arr HE _ _).

  #[global] Instance ArrowTLaw_stateArrT :
    ArrowTLaw (stateArrT S) (ArrowT_stateArrT S) arr HA HE
      (@Arrow_stateArrT S arr HA) (@ArrowEq_stateArrT S arr HE).
  Proof.
    constructor.
    - intros A B. exact (@first_proper arr HA HE HL A B S).
    - intros. exact (@first_pure arr HA HE HL _ _ S f).
    - intros. exact (@first_comp arr HA HE HL _ _ _ S f g).
    - intros A B C f.
    change (eqA (first (@arr_first arr HA A B C f))
      (pure (@state_shuffle_in S A C) >>>
        (first (@arr_first arr HA A B S f) >>> pure (@state_shuffle_out S B C)))).
    assert (Hswap : eqA
      (pure (@assoc_prod A C S) >>> pure (fun '(a, cs) => (a, swap cs)))
      (pure (@state_shuffle_in S A C) >>> pure (@assoc_prod A S C))).
    { etransitivity. { apply pure_comp. }
      symmetry. apply (@pure_comp_ext arr HA HE HL).
      intros [[a c] s]. reflexivity. }
    assert (Hmid : eqA
      (first (@arr_first arr HA A B C f) >>>
        pure (@assoc_prod B C S) >>> pure (fun '(b, cs) => (b, swap cs)))
      (pure (@state_shuffle_in S A C) >>>
        (first (@arr_first arr HA A B S f) >>> pure (@assoc_prod B S C)))).
    { etransitivity. { apply comp_proper. 2: reflexivity. apply first_assoc. }
      etransitivity. { apply comp_assoc. }
      etransitivity. { apply comp_proper. 1: reflexivity. apply first_natural. }
      etransitivity. { symmetry. apply comp_assoc. }
      etransitivity. { apply comp_proper. 2: reflexivity. exact Hswap. }
      etransitivity. { apply comp_assoc. }
      apply comp_proper. 1: reflexivity. symmetry. apply first_assoc. }
    assert (Htail : eqA
      (pure (@assoc_prod B C S) >>> pure (fun '(b, cs) => (b, swap cs)) >>>
        pure (@unassoc_prod B S C) >>> pure (@state_shuffle_out S B C))
      (@arr_id arr HA _)).
    { etransitivity. { apply comp_proper. 2: reflexivity.
        apply comp_proper. 2: reflexivity. apply pure_comp. }
      etransitivity. { apply comp_proper. 2: reflexivity. apply pure_comp. }
      apply (@pure_comp_ext arr HA HE HL).
      intros [[b c] s]. reflexivity. }
    transitivity ((first (@arr_first arr HA A B C f) >>>
      pure (@assoc_prod B C S) >>> pure (fun '(b, cs) => (b, swap cs))) >>>
      pure (@unassoc_prod B S C) >>> pure (@state_shuffle_out S B C)).
    + symmetry. repeat rewrite (@comp_assoc arr HA HE HL).
      etransitivity. { apply comp_proper. 1: reflexivity.
        repeat rewrite <- (@comp_assoc arr HA HE HL). exact Htail. }
      apply comp_id_r.
    + rewrite Hmid. repeat rewrite (@comp_assoc arr HA HE HL).
      apply comp_proper. 1: reflexivity.
      etransitivity. { apply comp_proper. 1: reflexivity.
        rewrite <- (@comp_assoc arr HA HE HL).
        etransitivity. { apply comp_proper. 2: reflexivity.
          transitivity (@arr_id arr HA ((B * S) * C)%type).
          2: reflexivity.
          apply (@pure_comp_ext arr HA HE HL).
          intros [[b s] c]. reflexivity. }
        apply comp_id_l. }
      reflexivity.
  Qed.

End StateLift.

Section StateChoiceLift.
  Context (S : Type) {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HE : ArrowEq arr}
    (HL : @ArrowLaws arr HA HE) (HCL : @ArrowChoiceLaws arr HA HC HE).
  Local Existing Instance HL.
  #[global] Instance ArrowChoiceTLaw_stateArrT :
    ArrowChoiceTLaw (stateArrT S) (ArrowT_stateArrT S) arr HA HC HE
      (@Arrow_stateArrT S arr HA) (@ArrowChoice_stateArrT S arr HA HC)
      (@ArrowEq_stateArrT S arr HE).
  Proof.
    constructor. intros A B C f.
    change (@arrow_eq arr HE _ _
      (@arr_first arr HA _ _ S (@arr_left arr HA HC A B C f))
      (arr_comp (arr_pure (@sum_distribute A C S))
        (arr_comp (arr_left (@arr_first arr HA A B S f))
          (arr_pure (@sum_undistribute B C S))))).
    assert (Hcancel : @arrow_eq arr HE _ _
      (arr_comp (arr_pure (@sum_distribute B C S))
        (arr_pure (@sum_undistribute B C S))) (@arr_id arr HA _)).
    { apply (@pure_comp_ext arr HA HE HL).
      intros [[b|c] s]; reflexivity. }
    transitivity (arr_comp
      (arr_comp (arr_first (arr_left f)) (arr_pure (@sum_distribute B C S)))
      (arr_pure (@sum_undistribute B C S))).
    - symmetry. rewrite (@comp_assoc arr HA HE HL), Hcancel.
      apply (@comp_id_r arr HA HE HL).
    - rewrite (@first_left_dist arr HA HC HE HCL).
      apply (@comp_assoc arr HA HE HL).
  Qed.
End StateChoiceLift.

Section StateApplyLift.
  Context (S : Type) {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HX : @ArrowApply arr HA} {HE : ArrowEq arr}
    (HL : @ArrowLaws arr HA HE) (HXL : @ArrowApplyLaws arr HA HX HE).
  Local Existing Instance HL.
  #[global] Instance ArrowApplyTLaw_stateArrT :
    ArrowApplyTLaw (stateArrT S) (ArrowT_stateArrT S) arr HA HX HE
      (@Arrow_stateArrT S arr HA) (@ArrowApply_stateArrT S arr HA HX)
      (@ArrowEq_stateArrT S arr HE).
  Proof.
    constructor. intros A B.
    cbn [arrowT_lift ArrowT_stateArrT arrow_eq ArrowEq_stateArrT
      arr_comp arr_pure arr_app Arrow_stateArrT ArrowApply_stateArrT].
    apply (@arrow_ext arr HA HX HE HL HXL). intros [[f a] s].
    assert (Hleft : @arrow_eq arr HE _ _
      (arr_comp (arr_pure (fun _ : unit => ((f, a), s)))
        (arr_first (@arr_app arr HA HX A B)))
      (arr_comp (arr_pure (fun _ : unit => (a, s))) (arr_first f))).
    { etransitivity.
      { apply (@comp_proper arr HA HE HL). 2: reflexivity.
        transitivity (arr_comp (arr_pure (fun _ : unit => (f, a)))
          (arr_pure (fun p : arr A B * A => (p, s)))).
        2: reflexivity. symmetry. apply (@pure_comp arr HA HE HL). }
      rewrite (@comp_assoc arr HA HE HL).
      rewrite (@first_constant arr HA HE HL).
      rewrite <- (@comp_assoc arr HA HE HL).
      rewrite (@app_constant arr HA HX HE HL _ _ _ f a
        (@app_law arr HA HX HE HXL _ _ f)).
      rewrite (@comp_assoc arr HA HE HL).
      rewrite <- (@first_constant arr HA HE HL A B S f s).
      rewrite <- (@comp_assoc arr HA HE HL).
      apply (@comp_proper arr HA HE HL). 2: reflexivity.
      apply (@pure_comp arr HA HE HL). }
    transitivity (arr_comp (arr_pure (fun _ : unit => (a, s))) (arr_first f)).
    - exact Hleft.
    - symmetry. repeat rewrite <- (@comp_assoc arr HA HE HL).
      etransitivity.
      { apply (@comp_proper arr HA HE HL). 2: reflexivity.
        etransitivity. { apply (@comp_proper arr HA HE HL). 2: reflexivity.
          apply (@pure_comp arr HA HE HL). }
        apply (@pure_comp arr HA HE HL). }
      apply (@app_constant arr HA HX HE HL).
      apply (@app_law arr HA HX HE HXL).
  Qed.
End StateApplyLift.
