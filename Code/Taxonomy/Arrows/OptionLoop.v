(** * The [ArrowLoop] boundary for option relational arrows.

    With the existing [optionArrT] operations and pointwise logical
    equivalence, no [ArrowLoop] on [optionRel] can satisfy even left
    tightening.  The law quantifies over arbitrary Coq types, including
    [Empty_set] as the feedback type.

    For empty feedback, [arr_comp (arr_first h) body] has an empty
    domain, so every prefix [h] gives the same loop body.  Outside the
    loop, however, a prefix with no outcomes and a prefix that raises
    [None] remain distinguishable: option composition propagates the
    latter failure.  Left tightening would equate both composites with
    the same loop result, yielding a contradiction.

    Functional extensionality identifies the empty-domain bodies by
    Leibniz equality.  Thus the proof requires no [loop_proper]
    hypothesis; functional extensionality is its only axiom. *)

From Coq Require Import FunctionalExtensionality.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT.
From Incorrectness.Taxonomy.Arrows Require Import Rel.

(** Fix the existing operation and equality dictionaries explicitly. *)
Local Notation OA := (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel).
Local Notation OE := (@ArrowEq_optionArrT Rel ArrowEq_Rel).

(** Every candidate loop operation fails left tightening when feedback
    ranges over all [Type], including [Empty_set]. *)
Theorem optionRel_no_left_tightening :
  forall L : @ArrowLoop optionRel OA,
    ~ (forall (A B C D : Type) (h : optionRel A B)
         (f : optionRel (B * D) (C * D)),
       @arrow_eq optionRel OE A C
         (@arr_loop optionRel OA L A C D
           (@arr_comp optionRel OA _ _ _
             (@arr_first optionRel OA A B D h) f))
         (@arr_comp optionRel OA _ _ _ h
           (@arr_loop optionRel OA L B C D f))).
Proof.
  intros L Htight.
  set (zero := (fun _ _ => False) : optionRel unit unit).
  set (raises := (fun _ ob => ob = None) : optionRel unit unit).
  set (body := (fun _ _ => False)
    : optionRel (unit * Empty_set) (unit * Empty_set)).

  (* Empty feedback makes every prefixed body Leibniz-equal to [body]. *)
  assert (Hbody : forall h : optionRel unit unit,
    @arr_comp optionRel OA _ _ _
      (@arr_first optionRel OA unit unit Empty_set h) body = body).
  {
    intro h.
    apply functional_extensionality.
    intros [u e]. destruct e.
  }
  pose proof (Htight unit unit unit Empty_set zero body) as Hzero.
  pose proof (Htight unit unit unit Empty_set raises body) as Hraises.
  rewrite (Hbody zero) in Hzero.
  rewrite (Hbody raises) in Hraises.

  (* A raised failure propagates without consulting the loop result. *)
  assert (Hfailure :
    @arr_comp optionRel OA unit unit unit raises
      (@arr_loop optionRel OA L unit unit Empty_set body) tt None).
  {
    cbn.
    exists None. split; [reflexivity |].
    exists (inr tt). split; [reflexivity |].
    exists (inr tt). split; reflexivity.
  }
  pose proof (proj2 (Hraises tt None) Hfailure) as Hloop.
  pose proof (proj1 (Hzero tt None) Hloop) as Habsurd.
  cbn in Habsurd.
  destruct Habsurd as [ob [Hfalse _]].
  exact Hfalse.
Qed.

(** In particular, the existing [optionRel] dictionaries admit no
    [ArrowLoop] satisfying [ArrowLoopLaws]. *)
Corollary optionRel_no_lawful_ArrowLoop :
  ~ exists L : @ArrowLoop optionRel OA,
      @ArrowLoopLaws optionRel OA L OE.
Proof.
  intros [L HL].
  apply (optionRel_no_left_tightening L).
  exact (@loop_left_tightening optionRel OA L OE HL).
Qed.
