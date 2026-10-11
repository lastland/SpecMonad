(** * O'Hearn-style rewriting rules, for the ASP reading of any relation

    The rewriting rules of O'Hearn's "Incorrectness Logic" over
    [aspHolds R k P Q]: [Under] is the incorrectness triple (every result in
    [Q] is reached from a start point in [P]) and [Over] the correctness one
    (every result reached from [P] is in [Q]).  Every ASP triple at every
    setting is such a judgement on the relation between start points and
    terminating outcomes ([triple_aspPure], [triple_aspSt],
    [triple_aspStExc]), so each setting's [InCorrectnessPrinciples.v]
    instantiates these rules, and derives the demonic liberal WP variants
    through its Galois edge. *)

From Incorrectness.Relational Require Import Rel.
From Incorrectness.Verification.Generic Require Import Triple.

Section OHearnRules.
  Context {X Y : Type} (R : Rel X Y).

  Theorem first_symmetry_rule_1 (P : X -> Prop) (Q1 Q2 : Y -> Prop) :
    aspHolds R Under P Q1 /\ aspHolds R Under P Q2 ->
    aspHolds R Under P (fun y => Q1 y \/ Q2 y).
  Proof.
    intros [H1 H2] y [Hy | Hy]; [ exact (H1 y Hy) | exact (H2 y Hy) ].
  Qed.

  Theorem first_symmetry_rule_2 (P : X -> Prop) (Q1 Q2 : Y -> Prop) :
    aspHolds R Under P (fun y => Q1 y \/ Q2 y) ->
    aspHolds R Under P Q1 /\ aspHolds R Under P Q2.
  Proof.
    intros H. split; intros y Hy;
      [ exact (H y (or_introl Hy)) | exact (H y (or_intror Hy)) ].
  Qed.

  Theorem second_symmetry_rule_1 (P : X -> Prop) (Q1 Q2 : Y -> Prop) :
    aspHolds R Over P Q1 /\ aspHolds R Over P Q2 ->
    aspHolds R Over P (fun y => Q1 y /\ Q2 y).
  Proof.
    intros [H1 H2] y Hy. exact (conj (H1 y Hy) (H2 y Hy)).
  Qed.

  Theorem second_symmetry_rule_2 (P : X -> Prop) (Q1 Q2 : Y -> Prop) :
    aspHolds R Over P (fun y => Q1 y /\ Q2 y) ->
    aspHolds R Over P Q1 /\ aspHolds R Over P Q2.
  Proof.
    intros H. split; intros y Hy;
      [ exact (proj1 (H y Hy)) | exact (proj2 (H y Hy)) ].
  Qed.

  (** Rule of consequence, [Under]: WEAKEN the precondition and SHRINK the
      postcondition -- the opposite of the [Over] direction, because [Under]
      has the transformer's value in the conclusion. *)
  Theorem first_imp_symmetry_rule (P P' : X -> Prop) (Q Q' : Y -> Prop) :
    aspHolds R Under P Q /\ (forall x, P x -> P' x) /\ (forall y, Q' y -> Q y) ->
    aspHolds R Under P' Q'.
  Proof.
    intros [H [HP HQ]] y Hy.
    destruct (H y (HQ y Hy)) as [x [Hx Hr]].
    exact (ex_intro _ x (conj (HP x Hx) Hr)).
  Qed.

  Theorem second_imp_symmetry_rule (P P' : X -> Prop) (Q Q' : Y -> Prop) :
    aspHolds R Over P Q /\ (forall x, P' x -> P x) /\ (forall y, Q y -> Q' y) ->
    aspHolds R Over P' Q'.
  Proof.
    intros [H [HP HQ]] y [x [Hx Hr]].
    exact (HQ y (H y (ex_intro _ x (conj (HP x Hx) Hr)))).
  Qed.

  (** A result witnessed by the under-approximation is reached from a
      [U]-point; if [U] entails [O], the over-approximation must accept it. *)
  Theorem principle_of_agreement (U O : X -> Prop) (U' O' : Y -> Prop) :
    aspHolds R Under U U' /\ aspHolds R Over O O' /\ (forall x, U x -> O x) ->
    forall y, U' y -> O' y.
  Proof.
    intros [Hinc [Hcor Himp]] y Hy.
    destruct (Hinc y Hy) as [x [Hx Hr]].
    exact (Hcor y (ex_intro _ x (conj (Himp x Hx) Hr))).
  Qed.

  Theorem principle_of_denial (U O : X -> Prop) (U' O' : Y -> Prop) :
    aspHolds R Under U U' /\ (forall x, U x -> O x) /\ ~ (forall y, U' y -> O' y) ->
    ~ aspHolds R Over O O'.
  Proof.
    intros [Hinc [Himp Hnot]] Hcor.
    exact (Hnot (principle_of_agreement U O U' O' (conj Hinc (conj Hcor Himp)))).
  Qed.
End OHearnRules.
