Definition conj2 {A B} (p1 p2 : A -> B -> Prop) : A -> B -> Prop :=
  fun a b => p1 a b /\ p2 a b.

Definition disj2 {A B} (p1 p2 : A -> B -> Prop) : A -> B -> Prop :=
  fun a b => p1 a b \/ p2 a b.
