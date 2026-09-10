(** * Monad operations from higher-order arrow application.

    For a fixed input [I], [arr I] supports return and bind.  This module
    defines the operations; it does not derive monad laws from the current
    one-field [ArrowApplyLaws] class. *)

From ExtLib Require Import Monad.
From Incorrectness.Classes Require Import Arrow.

Section ArrowMonad.
  Variable arr : Type -> Type -> Type.
  Context `{HA : Arrow arr} `{HAA : ArrowApply arr}.
  Variable I : Type.

  Definition ret_arrow {A} (a : A) : arr I A :=
    arr_pure (fun _ => a).

  Definition bind_arrow {A B} (m : arr I A) (k : A -> arr I B) : arr I B :=
    arr_comp (arr_fanout m arr_id)
      (arr_comp (arr_pure (fun '(a, i) => (k a, i))) arr_app).

  #[global] Instance Monad_Arrow : Monad (arr I) := {
    ret := @ret_arrow;
    bind := @bind_arrow
  }.
End ArrowMonad.
