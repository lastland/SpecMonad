From Incorrectness.Classes Require Import Arrow ArrowApplyFacts.
From Incorrectness.Classes.OptionArrowT Require Import Core ArrowLaws TransformerLaws.

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
  Local Notation opcomp := (@pure_comp _ OA OE OL).
  Local Notation ocprop := (@comp_proper _ OA OE OL).
  Local Notation ofpure := (@first_pure _ OA OE OL).

  (** Use the core lift contract, not the application instance under construction. *)
  Local Notation opure_congr :=
    (@lift_pure_congr optionArrT ArrowT_optionArrT arr HA HE OA OE
      (@ArrowTLaw_optionArrT arr HA HC HE HL HCL)
      (@ArrowApplyFacts.pure_ext arr HA HAA HE HL HAAL)).

  (** This ranges over all option arrows, not just arrows in the lift's
      image. It bootstraps application coherence using base extensionality. *)
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

  (** The static equation is needed before the complete transformed law
      dictionary exists; later fields use it through [app_constant]. *)
  Local Lemma option_app_law {A B} (f : optionArrT arr A B) :
    @arrow_eq _ OE _ _
      (@arr_comp _ OA _ _ _ (@arr_pure _ OA _ _ (fun a => (f, a)))
        (@arr_app _ OA OApp _ _)) f.
  Proof.
    etransitivity. { apply optionArrT_comp_pure_l. }
    apply alaw.
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
      etransitivity.
      { exact (@ArrowApplyFacts.app_constant _ OA OApp OE OL unit _ _ _ _
          (option_app_law _)). }
      etransitivity. { apply opcomp. }
      symmetry. apply ocidr.
    - (* app_precompose *)
      intros A B C g. apply option_arr_ext. intros [f a].
      etransitivity. { symmetry. apply ocassoc. }
      etransitivity.
      { apply ocprop. 2: reflexivity.
        apply ocprop. 1: reflexivity. apply ofpure. }
      etransitivity. { apply ocprop. 2: reflexivity. apply opcomp. }
      etransitivity.
      { exact (@ArrowApplyFacts.app_constant _ OA OApp OE OL unit _ _ _ _
          (option_app_law _)). }
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
        apply ocprop. 1: reflexivity.
        apply (@Arrow.second_constant _ OA OE OL (@opure_congr)). }
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
      etransitivity.
      { exact (@ArrowApplyFacts.app_constant _ OA OApp OE OL unit _ _ _ _
          (option_app_law _)). }
      symmetry.
      etransitivity. { symmetry. apply ocassoc. }
      etransitivity.
      { apply ocprop. 2: reflexivity.
        exact (@ArrowApplyFacts.app_constant _ OA OApp OE OL unit _ _ _ _
          (option_app_law _)). }
      apply ocassoc.
    - (* app_ext is inherited directly by the underlying application. *)
      intros X A B u v H.
      etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry. apply aext. exact H.
  Qed.

End GenericOptionArrTApplyLaws.
