(** * Generic state arrow transformer.

    [stateArrT S arr A B := arr (A * S) (B * S)] threads state
    through an arrow by transforming both input and output. *)

From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Definition and Arrow instance                                   *)
(* ================================================================= *)

Definition stateArrT (S : Type) (arr : Type -> Type -> Type) A B :=
  arr (A * S)%type (B * S)%type.

Section StateArrowTInstances.

  Variable S : Type.
  Context {arr : Type -> Type -> Type} `{Arrow arr}.

  Definition state_shuffle_in {A C : Type} :
    (A * C * S)%type -> (A * S * C)%type :=
    fun '((a, c), s) => ((a, s), c).

  Definition state_shuffle_out {B C : Type} :
    (B * S * C)%type -> (B * C * S)%type :=
    fun '((b, s), c) => ((b, c), s).

  #[global]
  Instance Arrow_stateArrT : Arrow (stateArrT S arr) := {
    arr_pure := fun A B f =>
      @arr_pure arr H _ _ (fun '(a, s) => (f a, s)) ;
    arr_comp := fun A B C f g =>
      @arr_comp arr H _ _ _ f g ;
    arr_first := fun A B C f =>
      @arr_comp arr H _ _ _
        (@arr_pure arr H _ _ state_shuffle_in)
        (@arr_comp arr H _ _ _
          (@arr_first arr H _ _ _ f)
          (@arr_pure arr H _ _ state_shuffle_out))
  }.

End StateArrowTInstances.

Arguments Arrow_stateArrT {_} {_} {_}.
