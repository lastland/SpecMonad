(** * Generic state arrow transformer.

    [stateArrT S arr A B := arr (A * S) (B * S)] threads state
    through an arrow by transforming both input and output. *)

From Coq Require Import FunctionalExtensionality Morphisms.
From Incorrectness.Lib.Arrow Require Import Arrow.

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

(* ================================================================= *)
(** ** ArrowT instance                                                 *)
(* ================================================================= *)

#[global]
Instance ArrowT_stateArrT (S : Type) : ArrowT (stateArrT S) := {
  arrowT_lift := fun arr0 _ A B f => @arr_first arr0 _ A B S f
}.

(* ================================================================= *)
(** ** ArrowEq and ArrowLaws for [stateArrT]                          *)
(* ================================================================= *)

Section StateArrowTEqLaws.

  Variable S : Type.
  Context {arr : Type -> Type -> Type} `{HL : ArrowLaws arr}.

  Local Notation cassoc := (@comp_assoc arr Harr Heq HL).
  Local Notation pcomp  := (@pure_comp arr Harr Heq HL).
  Local Notation cprop  := (@comp_proper arr Harr Heq HL).
  Local Notation fnat   := (@first_natural arr Harr Heq HL).

  #[global]
  Instance ArrowEq_stateArrT : ArrowEq (stateArrT S arr) := {
    arrow_eq := fun A B => @arrow_eq arr _ (A * S) (B * S) ;
    arrow_eq_equiv := fun A B => @arrow_eq_equiv arr _ (A * S) (B * S)
  }.

  #[global]
  Instance ArrowLaws_stateArrT : ArrowLaws (stateArrT S arr).
  Proof.
    constructor; intros;
    unfold arr_id, arr_comp, arr_first, arr_pure, Arrow_stateArrT,
           arrow_eq, ArrowEq_stateArrT.
    - (* comp_id_l *)
      replace (fun p : A * S => let '(a, s0) := p in ((fun x : A => x) a, s0))
        with (fun p : A * S => p) by (extensionality p; destruct p; reflexivity).
      apply comp_id_l.
    - (* comp_id_r *)
      replace (fun p : B * S => let '(a, s0) := p in ((fun x : B => x) a, s0))
        with (fun p : B * S => p) by (extensionality p; destruct p; reflexivity).
      apply comp_id_r.
    - (* comp_assoc *)
      apply comp_assoc.
    - (* pure_comp *)
      apply (@Arrow.pure_comp_ext arr Harr Heq HL).
      intros [a s]. reflexivity.
    - (* first_pure *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        etransitivity.
        { apply comp_proper. { apply first_pure. } 1: reflexivity. }
        apply pure_comp. }
      apply (@Arrow.pure_comp_ext arr Harr Heq HL).
      intros [[a c] s]. reflexivity.
    - (* first_comp *)
      (* Goal: si >>> first(f>>>g) >>> so ≃ (si >>> first f >>> so) >>> (si >>> first g >>> so) *)
      symmetry.
      (* Right-associate RHS *)
      etransitivity. { apply comp_assoc. }
      etransitivity.
      { apply comp_proper. 1: reflexivity. apply comp_assoc. }
      (* si >>> first f >>> so >>> si >>> first g >>> so *)
      (* Cancel so >>> si *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        etransitivity. { symmetry. apply comp_assoc. }
        apply comp_proper. 2: reflexivity.
        transitivity (@arr_id arr Harr ((B * S) * D)%type). 2: reflexivity.
        apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[a s0] c]. reflexivity. }
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        apply comp_id_l. }
      (* si >>> first f >>> first g >>> so *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        symmetry. apply comp_assoc. }
      (* si >>> (first f >>> first g) >>> so *)
      apply comp_proper. 1: reflexivity.
      apply comp_proper. 2: reflexivity.
      symmetry. apply first_comp.
    - (* first_fst *)
      (* Goal: (si >>> first f >>> so) >>> pure fst_s ≃ pure fst_s >>> f *)
      (* Pre-prove: so >>> pure fst_s ≃ pure fst *)
      assert (Hso_fst : @arrow_eq arr _ ((B * S) * C) (B * S)
        (@arr_comp arr _ _ _ _
          (@arr_pure arr _ _ _ (@state_shuffle_out S B C))
          (@arr_pure arr _ _ _ (fun '(a, s0) => (fst a, s0))))
        (@arr_pure arr _ _ _ fst)).
      { apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[b s0] c]. reflexivity. }
      (* Pre-prove: si >>> pure fst ≃ pure fst_s *)
      assert (Hsi_fst : @arrow_eq arr _ ((A * C) * S) (A * S)
        (@arr_comp arr _ _ _ _
          (@arr_pure arr _ _ _ (@state_shuffle_in S A C))
          (@arr_pure arr _ _ _ fst))
        (@arr_pure arr _ _ _ (fun '(a, s0) => (fst a, s0)))).
      { apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[a0 c0] s0]. reflexivity. }
      (* Right-associate LHS *)
      etransitivity. { apply comp_assoc. }
      etransitivity.
      { apply comp_proper. 1: reflexivity. apply comp_assoc. }
      (* si >>> first f >>> (so >>> pure fst_s) *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        exact Hso_fst. }
      (* si >>> first f >>> pure fst *)
      etransitivity.
      { apply comp_proper. 1: reflexivity. apply first_fst. }
      (* si >>> (pure fst >>> f) *)
      etransitivity. { symmetry. apply comp_assoc. }
      apply comp_proper. 2: reflexivity.
      exact Hsi_fst.
    - (* first_assoc *)
      (* Goal: (si_D >>> first(F) >>> so_D) >>> assoc_s
               ≃ assoc_s >>> (si >>> first f >>> so)
         where F = si_C >>> first f >>> so_C *)
      (* Pre-prove: tail collapse *)
      assert (Htail : @arrow_eq arr _ (((B * S) * C) * D) ((B * (C * D)) * S)
        (arr_comp (arr_first (arr_pure (@state_shuffle_out S B C)))
          (arr_comp (arr_pure (@state_shuffle_out S (B * C) D))
            (arr_pure (fun '(a, s0) => (assoc_prod a, s0)))))
        (arr_comp (arr_pure assoc_prod)
          (arr_pure (@state_shuffle_out S B (C * D))))).
      { etransitivity.
        { apply comp_proper. 1: reflexivity. apply pure_comp. }
        etransitivity.
        { apply comp_proper. 2: reflexivity. apply first_pure. }
        etransitivity. { apply pure_comp. }
        symmetry.
        apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[[b s0] c] d]. reflexivity. }
      (* Pre-prove: head collapse *)
      assert (Hhead : @arrow_eq arr _ (((A * C) * D) * S) (((A * S) * C) * D)
        (arr_comp (arr_pure (@state_shuffle_in S (A * C) D))
          (arr_first (arr_pure (@state_shuffle_in S A C))))
        (arr_pure (fun '(((a, c), d), s) => (((a, s), c), d)))).
      { etransitivity.
        { apply comp_proper. 1: reflexivity. apply first_pure. }
        apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[[a0 c0] d0] s0]. reflexivity. }
      (* Pre-prove: head >>> assoc = rhs_head *)
      assert (Hhead_assoc : @arrow_eq arr _ (((A * C) * D) * S) ((A * S) * (C * D))
        (arr_comp
          (arr_pure (fun '(((a, c), d), s) => (((a, s), c), d)))
          (arr_pure assoc_prod))
        (arr_comp (arr_pure (fun '(a, s0) => (assoc_prod a, s0)))
          (arr_pure (@state_shuffle_in S A (C * D))))).
      { etransitivity. { apply pure_comp. }
        symmetry.
        apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[[a0 c0] d0] s0]. reflexivity. }
      (* Step 1: Right-associate LHS *)
      etransitivity. { apply comp_assoc. }
      etransitivity.
      { apply comp_proper. 1: reflexivity. apply comp_assoc. }
      (* si_D >>> first(F) >>> (so_D >>> assoc_s) *)
      (* Step 2: Expand first(F) = first(si_C) >>> first(first f) >>> first(so_C) *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 2: reflexivity.
        etransitivity. { apply first_comp. }
        apply comp_proper. 1: reflexivity.
        apply first_comp. }
      (* si_D >>> (first(si_C) >>> (first(first f) >>> first(so_C))) >>> (so_D >>> assoc_s) *)
      (* Step 3: Flatten to si_D >>> first(si_C) >>> first(first f) >>> (tail) *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        etransitivity. { apply comp_assoc. }
        apply comp_proper. 1: reflexivity.
        apply comp_assoc. }
      (* si_D >>> first(si_C) >>> first(first f) >>> (first(so_C) >>> so_D >>> assoc_s) *)
      (* Step 4: Apply Htail to collapse tail *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        exact Htail. }
      (* si_D >>> first(si_C) >>> first(first f) >>> (assoc >>> so) *)
      (* Step 5: Reassociate to apply first_assoc *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        symmetry. apply comp_assoc. }
      (* si_D >>> first(si_C) >>> (first(first f) >>> assoc) >>> so *)
      (* Step 6: Apply base first_assoc *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        apply comp_proper. 2: reflexivity.
        apply first_assoc. }
      (* si_D >>> first(si_C) >>> (assoc >>> first f) >>> so *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        apply comp_proper. 1: reflexivity.
        apply comp_assoc. }
      (* si_D >>> first(si_C) >>> assoc >>> first f >>> so *)
      (* Step 7: Left-associate head to collapse *)
      etransitivity.
      { apply comp_proper. 1: reflexivity.
        symmetry. apply comp_assoc. }
      (* si_D >>> ((first(si_C) >>> assoc) >>> (first f >>> so)) *)
      etransitivity. { symmetry. apply comp_assoc. }
      (* (si_D >>> (first(si_C) >>> assoc)) >>> (first f >>> so) *)
      etransitivity.
      { apply comp_proper. 2: reflexivity.
        symmetry. apply comp_assoc. }
      (* ((si_D >>> first(si_C)) >>> assoc) >>> (first f >>> so) *)
      etransitivity.
      { apply comp_proper. 2: reflexivity.
        apply comp_proper. 2: reflexivity.
        exact Hhead. }
      (* (pure Lfun >>> assoc) >>> (first f >>> so) *)
      etransitivity.
      { apply comp_proper. 2: reflexivity.
        exact Hhead_assoc. }
      (* (assoc_s >>> si) >>> (first f >>> so) *)
      (* Step 8: Match RHS *)
      apply comp_assoc.
    - (* comp_proper *)
      unfold Proper, respectful; intros.
      apply comp_proper; assumption.
    - (* first_proper *)
      unfold Proper, respectful; intros.
      apply comp_proper. { reflexivity. }
      apply comp_proper. 2: reflexivity.
      apply first_proper. assumption.
    - (* first_natural: the state shuffles commute with the pure map. *)
      assert (Htail : @arrow_eq arr _ ((B * S) * C) ((B * D) * S)
        (arr_comp (arr_pure (@state_shuffle_out S B C))
          (arr_pure (fun '(bc, s) => (let '(b, c) := bc in (b, g c), s))))
        (arr_comp (arr_pure (fun '(bs, c) => (bs, g c)))
          (arr_pure (@state_shuffle_out S B D)))).
      { etransitivity. { apply pcomp. }
        symmetry.
        apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[b s] c]. reflexivity. }
      assert (Hhead : @arrow_eq arr _ ((A * C) * S) ((A * S) * D)
        (arr_comp (arr_pure (@state_shuffle_in S A C))
          (arr_pure (fun '(as_, c) => (as_, g c))))
        (arr_comp (arr_pure (fun '(ac, s) => (let '(a, c) := ac in (a, g c), s)))
          (arr_pure (@state_shuffle_in S A D)))).
      { etransitivity. { apply pcomp. }
        symmetry.
        apply (@Arrow.pure_comp_ext arr Harr Heq HL).
        intros [[a c] s]. reflexivity. }
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. exact Htail. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply fnat. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity. exact Hhead. }
      apply cassoc.
    - (* pure_proper *)
      intros f g H. apply (@Arrow.pure_proper arr Harr Heq HL).
      intros [x s]. rewrite (H x). reflexivity.
  Qed.

End StateArrowTEqLaws.

(* ================================================================= *)
(** ** Helper functions for state/sum distribution                    *)
(* ================================================================= *)

Definition sum_distribute {A C S} (p : (A + C) * S) : (A * S) + (C * S) :=
  let '(ac, s) := p in match ac with inl a => inl (a, s) | inr c => inr (c, s) end.

Definition sum_undistribute {B C S} (x : (B * S) + (C * S)) : (B + C) * S :=
  match x with inl (b, s) => (inl b, s) | inr (c, s) => (inr c, s) end.

(* ================================================================= *)
(** ** ArrowChoice for [stateArrT]                                    *)
(* ================================================================= *)

Section StateArrowTChoice.
  Variable S : Type.
  Context {arr : Type -> Type -> Type} `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}.

  #[global]
  Instance ArrowChoice_stateArrT : ArrowChoice (stateArrT S arr) := {
    arr_left := fun A B C f =>
      @arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (sum_distribute (S:=S)))
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ _ f)
          (@arr_pure arr HA _ _ (sum_undistribute (S:=S))))
  }.

End StateArrowTChoice.

Arguments ArrowChoice_stateArrT {_} {_} {_} {_}.

(* ================================================================= *)
(** ** ArrowApply for [stateArrT]                                     *)
(* ================================================================= *)

Section StateArrowTApply.
  Variable S : Type.
  Context {arr : Type -> Type -> Type} `{HA : Arrow arr}
          `{HAA : @ArrowApply arr HA}.

  #[global]
  Instance ArrowApply_stateArrT : ArrowApply (stateArrT S arr) := {
    arr_app := fun A B =>
      @arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (fun '((f, a), s) => (f, (a, s))))
        (@arr_app arr HA HAA (A * S)%type (B * S)%type)
  }.

End StateArrowTApply.
