(** * Monotonicity-only counterexamples to [first_fst]. *)

From Incorrectness.Lib.Arrow Require Import Arrow.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.PTMonadTaxonomy Require Import TransformerRelations.

(** Monotonicity alone does not validate [first_fst] for these operations.

    Work through the two modules on the predicate [diagonal]. In ASP, projecting
    after [first] asks for one Boolean shared by both conjuncts; projecting
    before the witness lets each conjunct choose its own Boolean. In DSLP,
    projecting after [first] allows the disjunct to depend on the universally
    quantified Boolean; projecting before the witness chooses a disjunct first.

    The carrier is the existing [MonoPT], not the production ASP/DSLP carrier:
    no join/meet preservation condition is imposed. The conclusion concerns
    exactly the plain operation dictionaries below, not every possible arrow
    structure on monotone transformers. No instances are registered here. *)
Module MonotoneFirstFst.
Local Obligation Tactic := idtac.

(** Reuse the production pure lifts, retaining only their monotonicity proofs.
    Each following obligation checks closure in the monotone subset. *)
#[program] Definition pure_asp {A B} (h : A -> B) : MonoPT A B :=
  getASPArr (pureASP h).
Next Obligation.
  intros A B h.
  exact (proj1 (proj2_sig (pureASP h))).
Qed.

#[program] Definition pure_dslp {A B} (h : A -> B) : MonoPT A B :=
  getDSLPArr (pureDSLP h).
Next Obligation.
  intros A B h.
  exact (proj1 (proj2_sig (pureDSLP h))).
Qed.

(** Composition runs [f] first, then [g]. Transport predicate inclusion
    through [f], then through [g]; no stronger preservation law is needed. *)
#[program] Definition compose {A B C}
  (f : MonoPT A B) (g : MonoPT B C) : MonoPT A C :=
  fun P c => g (f P) c.
Next Obligation.
  intros A B C f g P Q HPQ c H.
  apply (getPT_mono g (f P) (f Q) c).
  - intros b Hfb.
    exact (getPT_mono f P Q b HPQ Hfb).
  - exact H.
Qed.

(** [first] freezes the second coordinate. Predicate inclusion restricts to
    that slice, so the monotonicity of [f] suffices. *)
#[program] Definition first {A B C}
  (f : MonoPT A B) : MonoPT (A * C) (B * C) :=
  fun P bc => f (fun a => P (a, snd bc)) (fst bc).
Next Obligation.
  intros A B C f P Q HPQ [b c] H.
  apply (getPT_mono f (fun a => P (a, c)) (fun a => Q (a, c)) b).
  - intro a.
    apply HPQ.
  - exact H.
Qed.

Definition asp_arrow : Arrow MonoPT := {|
  arr_pure := @pure_asp; arr_comp := @compose; arr_first := @first
|}.
Definition dslp_arrow : Arrow MonoPT := {|
  arr_pure := @pure_dslp; arr_comp := @compose; arr_first := @first
|}.
Definition equality : ArrowEq MonoPT := {|
  arrow_eq := @pt_eq;
  arrow_eq_equiv := fun A B => @pt_eq_Equivalence A B
|}.

Definition diagonal (p : bool * bool) : Prop := fst p = snd p.

(** ** ASP: one shared choice versus two independent choices. *)
Module ASP.
(** Both input Booleans must satisfy the supplied predicate. *)
#[program] Definition witness : MonoPT bool unit :=
  fun Q _ => Q true /\ Q false.
Next Obligation.
  intros P Q HPQ b [Ht Hf].
  split.
  - apply HPQ.
    exact Ht.
  - apply HPQ.
    exact Hf.
Qed.

(** These are the two sides of the actual [Arrow.first_fst] field, using
    explicit dictionaries to avoid any implicit choice of operations. *)
Definition first_then_fst : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_first MonoPT asp_arrow bool unit bool witness)
    (@arr_pure MonoPT asp_arrow _ _ (@fst unit bool)).
Definition fst_then_arrow : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_pure MonoPT asp_arrow _ _ (@fst bool bool)) witness.

Lemma first_then_fst_rejects : ~ first_then_fst diagonal tt.
Proof.
  (* One existential choice of [snd q] must equal both true and false.
     Inspect the goal after [change] before splitting on that choice. *)
  change (~ exists q : unit * bool,
    (true = snd q /\ false = snd q) /\ fst q = tt).
  intros [[[] c] [[Htrue Hfalse] _]].
  destruct c.
  - discriminate Hfalse.
  - discriminate Htrue.
Qed.

Lemma fst_then_arrow_accepts : fst_then_arrow diagonal tt.
Proof.
  (* The conjunction is now outside the existential choices. Each conjunct
     has its own diagonal pair, so the choices need not agree. *)
  change ((exists p : bool * bool, fst p = snd p /\ fst p = true) /\
          (exists p : bool * bool, fst p = snd p /\ fst p = false)).
  split.
  - exists (true, true).
    split.
    + reflexivity.
    + reflexivity.
  - exists (false, false).
    split.
    + reflexivity.
    + reflexivity.
Qed.

Theorem first_fst_fails :
  ~ @arrow_eq MonoPT equality _ _ first_then_fst fst_then_arrow.
Proof.
  intro H.
  (* Pointwise iff would transfer acceptance from right to left. *)
  apply first_then_fst_rejects.
  apply (proj2 (H diagonal tt)).
  exact fst_then_arrow_accepts.
Qed.

Corollary no_arrow_laws : ~ @ArrowLaws MonoPT asp_arrow equality.
Proof.
  intro H.
  apply first_fst_fails.
  (* Extract the real field, specialized to our types and witness. *)
  exact (@first_fst MonoPT asp_arrow equality H bool unit bool witness).
Qed.
End ASP.

(** ** DSLP: a Boolean-dependent disjunct versus one fixed disjunct. *)
Module DSLP.
(** At least one input Boolean must satisfy the supplied predicate. *)
#[program] Definition witness : MonoPT bool unit :=
  fun Q _ => Q true \/ Q false.
Next Obligation.
  intros P Q HPQ b [Ht | Hf].
  - left.
    apply HPQ.
    exact Ht.
  - right.
    apply HPQ.
    exact Hf.
Qed.

Definition first_then_fst : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_first MonoPT dslp_arrow bool unit bool witness)
    (@arr_pure MonoPT dslp_arrow _ _ (@fst unit bool)).
Definition fst_then_arrow : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_pure MonoPT dslp_arrow _ _ (@fst bool bool)) witness.

Lemma first_then_fst_accepts : first_then_fst diagonal tt.
Proof.
  (* The universal choice comes before the disjunction. Choose the matching
     disjunct separately for each Boolean [snd q]. *)
  change (forall q : unit * bool,
    fst q = tt -> true = snd q \/ false = snd q).
  intros [[] c] _.
  destruct c.
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

Lemma fst_then_arrow_rejects : ~ fst_then_arrow diagonal tt.
Proof.
  (* Now one disjunct must work for every pair in its projection fiber.
     Each fiber contains an off-diagonal pair, refuting that disjunct. *)
  change (~ ((forall p : bool * bool, fst p = true -> fst p = snd p) \/
             (forall p : bool * bool, fst p = false -> fst p = snd p))).
  intros [Htrue | Hfalse].
  - pose proof (Htrue (true, false) eq_refl) as H.
    discriminate H.
  - pose proof (Hfalse (false, true) eq_refl) as H.
    discriminate H.
Qed.

Theorem first_fst_fails :
  ~ @arrow_eq MonoPT equality _ _ first_then_fst fst_then_arrow.
Proof.
  intro H.
  (* Here the contradiction uses the other direction of pointwise iff. *)
  apply fst_then_arrow_rejects.
  apply (proj1 (H diagonal tt)).
  exact first_then_fst_accepts.
Qed.

Corollary no_arrow_laws : ~ @ArrowLaws MonoPT dslp_arrow equality.
Proof.
  intro H.
  apply first_fst_fails.
  exact (@first_fst MonoPT dslp_arrow equality H bool unit bool witness).
Qed.
End DSLP.
End MonotoneFirstFst.
