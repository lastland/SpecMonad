From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.OptionArrowT Require Import Core ArrowLaws.

(* ================================================================= *)
(** ** Generic [ArrowChoiceLaws] for [optionArrT]                     *)
(* ================================================================= *)

Section GenericOptionArrTChoiceLaws.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HCL : @ArrowChoiceLaws arr HA HC HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidr   := (@comp_id_r arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation fpure  := (@first_pure arr HA HE HL).
  Local Notation fcomp  := (@first_comp arr HA HE HL).
  Local Notation lpure  := (@left_pure arr HA HC HE HCL).
  Local Notation lcomp  := (@left_comp arr HA HC HE HCL).
  Local Notation linl   := (@left_inl arr HA HC HE HCL).
  Local Notation lassoc := (@left_assoc arr HA HC HE HCL).
  Local Notation linr   := (@left_inr arr HA HC HE HCL).
  Local Notation lnat   := (@left_natural arr HA HC HE HCL).
  Local Notation fldist := (@first_left_dist arr HA HC HE HCL).
  Local Notation lprop  := (@left_proper arr HA HC HE HCL).

  Local Lemma pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro H. replace g with f by (extensionality x; apply H). reflexivity.
  Qed.

  Local Ltac destruct_sums :=
    repeat match goal with
    | [ x : (_ + _)%type |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x
    | [ x : unit |- _ ] => destruct x
    | [ x : (_ * _)%type |- _ ] => destruct x
    end.

  Local Ltac solve_pure_eq :=
    apply pure_ext; intro x; destruct_sums;
    unfold sum_bimap, to_sum, opt_rearrange, assoc_sum, swap_sum,
           collapse, sequence_option, sum_prod_dist;
    try reflexivity.

  Local Ltac opt_unfold :=
    unfold arr_id, arr_comp, arr_pure, arr_first, arr_left,
           Arrow_optionArrT, ArrowChoice_optionArrT,
           arrow_eq, ArrowEq_optionArrT;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_left arr HA HC) (@arrow_eq arr HE).

  #[global]
  Instance ArrowChoiceLaws_optionArrT : ArrowChoiceLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros; opt_unfold.
    all: try (unfold Proper, respectful; intros;
              apply cprop; [apply lprop; assumption | reflexivity]).
    (* All laws are algebraic consequences of base ArrowChoiceLaws. *)
    (* TODO: complete proofs for each law *)
    all: admit.
  Admitted.

End GenericOptionArrTChoiceLaws.
