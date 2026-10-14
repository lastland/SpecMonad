(** * Pre- and postconditions shared by the triple examples *)

Definition preEq0 : nat -> Prop := fun s => s = 0.
Definition postEq0 : option (unit * nat) -> Prop := fun r => r = Some (tt, 0).

