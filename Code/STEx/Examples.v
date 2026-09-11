From ExtLib Require Import Monad MonadState StateMonad MonadExc EitherMonad.
From Coq Require Import Lia PeanoNat.

Open Scope monad_scope.
Open Scope nat_scope.
Import MonadNotation.

Existing Instance Monad_stateT.

Definition read_inc_write : stateT nat (sum unit) unit :=
  x <- get ;; put (x + 1).

Definition read_if_inc_write : stateT nat (sum unit) unit :=
  x <- get ;; if (42 <=? x) then put (x + 1) else raise tt.
