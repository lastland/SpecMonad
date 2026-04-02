From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.StateArrowT Require Import Core.

(* ================================================================= *)
(** ** ArrowApplyLaws for [stateArrT]                                 *)
(* ================================================================= *)

Section StateArrowTApplyLaws.

  Variable S : Type.
  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HAAL : @ArrowApplyLaws arr HA HAA HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl   := (@comp_id_l arr HA HE HL).
  Local Notation cidr   := (@comp_id_r arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation alaw   := (@app_law arr HA HAA HE HAAL).

  Local Lemma arr_pure_ext'' {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro Hext. replace g with f by (extensionality x; apply Hext).
    reflexivity.
  Qed.

  #[global]
  Instance ArrowApplyLaws_stateArrT : ArrowApplyLaws (stateArrT S arr).
  Proof.
    constructor; intros.
    unfold arr_id, arr_comp, arr_pure, arr_first, arr_app,
           Arrow_stateArrT, ArrowApply_stateArrT,
           arrow_eq, ArrowEq_stateArrT;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_app arr HA HAA) (@arrow_eq arr HE).
    (* Goal: [fun '(a,s) => (f, (a,s))] >>> app ≃ f *)
    (* = [fun '(a,s) => ((f, a), s)] ... wait, let me check:
       stateArrT pure (fun a => (f, a)) = arr_pure (fun '(a,s) => ((f,a), s))
       Then stateArrT app = [fun '((g,a),s) => (g, (a,s))] >>> base_app
       LHS = [fun '(a,s) => ((f,a),s)] >>> [fun '((g,a),s) => (g,(a,s))] >>> base_app *)
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
    (* [fun '(a,s) => (f, (a,s))] >>> base_app *)
    etransitivity.
    { apply cprop. 2: reflexivity.
      apply arr_pure_ext''. intros (a0, s0); reflexivity. }
    apply alaw.
  Qed.

End StateArrowTApplyLaws.
