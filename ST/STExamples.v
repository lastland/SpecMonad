From ExtLib Require Import Monad MonadState StateMonad.
From Coq Require Import Nat Lia PeanoNat.

Open Scope monad_scope.
Open Scope nat_scope.
Import MonadNotation.

Definition read_inc_write : state nat unit :=
  x <- get ;; put (x + 1).

Definition read_if_inc_write : state nat unit :=
  x <- get ;; if (42 <=? x) then put (x + 1) else put 0.
