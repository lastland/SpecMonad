(** * Option arrow transformer.

    [optionArrT arr A B := arr A (option B)] lifts an arrow with
    option-aware composition (failure propagation).

    A generic [Arrow] instance is provided for any base arrow with
    [ArrowChoice], using the encoding [option B ≅ B + unit].

    Concrete instances for [optionArrT Pred] are also given. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
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
