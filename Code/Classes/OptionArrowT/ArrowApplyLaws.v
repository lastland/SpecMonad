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

  Local Lemma arr_pure_ext_apply {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro H. replace g with f by (extensionality x; apply H).
    reflexivity.
  Qed.

  (** The single law: [pure (fun a => (f, a)) >>> app = f].

      After unfolding optionArrT operations:
      [[
        [fun a => Some (f, a)] >>> [to_sum] >>> L(base_app) >>> [collapse] = f
      ]]

      Proof strategy:
      1. Fuse [Some . pair] >>> [to_sum] via pure_comp to [inl . pair]
      2. Split [inl . pair] = [pair] >>> [inl] (pcomp sym)
      3. Use left_inl (sym): [inl] >>> L(app) = app >>> [inl]
      4. Use base app_law: [pair] >>> base_app = f
      5. Then f >>> [inl] >>> [collapse] -> f >>> [id] -> f by comp_id_r *)

  #[global]
  Instance ArrowApplyLaws_optionArrT : ArrowApplyLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros.
    unfold arr_id, arr_comp, arr_pure, arr_first, arr_app,
           Arrow_optionArrT, ArrowApply_optionArrT,
           arrow_eq, ArrowEq_optionArrT;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_left arr HA HC) (@arr_app arr HA HAA) (@arrow_eq arr HE).
    (* Goal: [fun a => Some (f, a)] >>> [to_sum] >>> L(base_app) >>> [collapse] = f *)

    (* Step 1: Fuse [Some . pair] >>> [to_sum] to [inl . pair] *)
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
    (* [inl . pair] >>> L(app) >>> [collapse] *)

    (* Step 2: [inl . pair] >>> L(app) = [pair] >>> app >>> [inl]
       By: [inl . pair] = [pair] >>> [inl]  (pcomp sym)
       Then [pair] >>> [inl] >>> L(app) = [pair] >>> app >>> [inl]  (linl sym) *)
    etransitivity. { symmetry. apply cassoc. }
    etransitivity.
    { apply cprop. 2: reflexivity.
      (* Need: [inl.pair] >>> L(app) = [pair] >>> app >>> [inl] *)
      (* First: [inl.pair] = [pair] >>> [inl] *)
      assert (Hsplit : @arrow_eq arr HE A _
        (@arr_pure arr HA _ _ (fun a : A => @inl (optionArrT arr A B * A) unit (f, a)))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a : A => (f, a)))
          (@arr_pure arr HA _ _ (@inl (optionArrT arr A B * A) unit)))).
      { symmetry. etransitivity. { apply pcomp. }
        apply arr_pure_ext_apply. intro; reflexivity. }
      etransitivity. { apply cprop. 2: reflexivity. exact Hsplit. }
      (* ([pair] >>> [inl]) >>> L(app) *)
      etransitivity. { apply cassoc. }
      (* [pair] >>> ([inl] >>> L(app)) *)
      apply cprop. 1: reflexivity.
      (* [inl] >>> L(app) = app >>> [inl] *)
      symmetry. apply linl. }
    (* ([pair] >>> app) >>> [inl] >>> [collapse] *)

    (* Step 3: Reassociate: ([pair] >>> (app >>> [inl])) >>> [c]
              = (([pair] >>> app) >>> [inl]) >>> [c] *)
    etransitivity.
    { apply cprop. 2: reflexivity.
      symmetry. apply cassoc. }
    (* (([pair] >>> app) >>> [inl]) >>> [c] *)

    (* Step 4: Use base app_law: [pair] >>> base_app = f *)
    etransitivity.
    { apply cprop. 2: reflexivity.
      apply cprop. 2: reflexivity. apply alaw. }
    (* (f >>> [inl]) >>> [c] *)

    (* Step 5: Fuse f >>> [inl] >>> [c] to f >>> [id] = f *)
    etransitivity. { apply cassoc. }
    etransitivity.
    { apply cprop. 1: reflexivity. apply pcomp. }
    etransitivity.
    { apply cprop. 1: reflexivity.
      apply arr_pure_ext_apply. intro x. reflexivity. }
    apply cidr.
  Qed.

End GenericOptionArrTApplyLaws.
