From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.StateArrowT Require Import Core.

(* ================================================================= *)
(** ** ArrowApplyLaws for [stateArrT]                                 *)
(* ================================================================= *)

Section StateArrowTApplyLaws.

  Variable S : Type.
  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HAAL : @ArrowApplyLaws arr HA HAA HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl   := (@comp_id_l arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation fpure  := (@first_pure arr HA HE HL).
  Local Notation fcomp  := (@first_comp arr HA HE HL).
  Local Notation fprop  := (@first_proper arr HA HE HL).
  Local Notation alaw   := (@app_law arr HA HAA HE HAAL).
  Local Notation aunit  := (@app_unit arr HA HAA HE HAAL).
  Local Notation apre  := (@app_precompose arr HA HAA HE HAAL).
  Local Notation apost := (@app_postcompose arr HA HAA HE HAAL).
  Local Notation aext  := (@app_ext arr HA HAA HE HAAL).

  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 50, left associativity).
  Local Notation pure := (@arr_pure arr HA _ _).
  Local Notation first := (@arr_first arr HA _ _ _).
  Local Notation app := (@arr_app arr HA HAA _ _).
  Local Notation eqA := (@arrow_eq arr HE _ _).
  Local Notation spure :=
    (@arr_pure (stateArrT S arr) (@Arrow_stateArrT S arr HA) _ _).
  Local Notation sfirst :=
    (@arr_first (stateArrT S arr) (@Arrow_stateArrT S arr HA) _ _ _).
  Local Notation ssecond :=
    (@arr_second (stateArrT S arr) (@Arrow_stateArrT S arr HA) _ _ _).
  Local Notation sapp :=
    (@arr_app (stateArrT S arr) (@Arrow_stateArrT S arr HA)
      (@ArrowApply_stateArrT S arr HA HAA) _ _).
  Local Notation sfpure :=
    (@first_pure (stateArrT S arr) (@Arrow_stateArrT S arr HA)
      (@ArrowEq_stateArrT S arr HE) (@ArrowLaws_stateArrT S arr HA HE HL)).

  (** Pure application follows from pairing and postcomposition.  The
      stored pure arrow is replaced using [app_ext], not Coq equality. *)
  Local Lemma app_pure {A B C} (f : A -> B -> C) :
    eqA (first (pure (fun a => pure (f a))) >>> app)
        (pure (fun '(a, b) => f a b)).
  Proof.
    set (pair := fun a : A => pure (fun b : B => (a, b))).
    set (eval := fun '(a, b) => f a b).
    assert (Hstored : forall a,
      eqA (pure (f a)) (pair a >>> pure eval)).
    { intro a. symmetry.
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
      intro b. reflexivity. }
    assert (Hinputs :
      eqA (first (pure (fun a => pure (f a))) >>> app)
          (first (pure (fun a => pair a >>> pure eval)) >>> app)).
    { etransitivity.
      { apply cprop. 2: reflexivity. apply fpure. }
      symmetry. etransitivity.
      { apply cprop. 2: reflexivity. apply fpure. }
      apply aext. intros [a b]. split.
      - symmetry. apply Hstored.
      - reflexivity. }
    etransitivity. { exact Hinputs. }
    transitivity ((first (pure pair) >>> app) >>> pure eval).
    - symmetry. etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. symmetry. apply apost. }
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity.
      etransitivity. { symmetry. apply fcomp. }
      apply fprop. apply pcomp.
    - etransitivity.
      { apply cprop. 2: reflexivity. apply aunit. }
      apply cidl.
  Qed.

  (** State application only reassociates the selected arrow, argument,
      and state before invoking base application. *)
  Local Lemma state_pure_app {X A B}
    (u : X -> stateArrT S arr A B * A) :
    eqA (spure u >>> sapp)
        (pure (fun '(x, s) => let '(f, a) := u x in (f, (a, s))) >>> app).
  Proof.
    cbn [arr_pure arr_app Arrow_stateArrT ArrowApply_stateArrT].
    etransitivity. { symmetry. apply cassoc. }
    apply cprop. 2: reflexivity.
    apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
    intros [x s]. destruct (u x). reflexivity.
  Qed.

  Local Lemma state_first_pure_app {A B C}
    (f : A -> stateArrT S arr B C) :
    eqA (sfirst (spure f) >>> sapp)
        (pure (@assoc_prod A B S) >>> (first (pure f) >>> app)).
  Proof.
    etransitivity.
    { apply cprop. 2: reflexivity. apply sfpure. }
    etransitivity. { apply state_pure_app. }
    symmetry. etransitivity.
    { apply cprop. 1: reflexivity.
      apply cprop. 2: reflexivity. apply fpure. }
    etransitivity. { symmetry. apply cassoc. }
    apply cprop. 2: reflexivity.
    apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
    intros [[a b] s]. reflexivity.
  Qed.

  (** Moving the state beside the argument commutes with [second]. *)
  Local Lemma state_second_assoc {A B C} (g : stateArrT S arr A B) :
    eqA (ssecond g >>> pure (@assoc_prod C B S))
        (pure (@assoc_prod C A S) >>> @arr_second arr HA _ _ C g).
  Proof.
    assert (Hhead :
      eqA (spure (@swap C A) >>> pure (@state_shuffle_in S A C))
          (pure (@assoc_prod C A S) >>> pure (@swap C (A * S)))).
    { cbn [arr_pure Arrow_stateArrT].
      etransitivity. { apply pcomp. }
      symmetry.
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
      intros [[c a] s]. reflexivity. }
    assert (Htail :
      eqA (pure (@state_shuffle_out S B C) >>>
            (spure (@swap B C) >>> pure (@assoc_prod C B S)))
          (pure (@swap (B * S) C))).
    { cbn [arr_pure Arrow_stateArrT].
      etransitivity.
      { apply cprop. 1: reflexivity. apply pcomp. }
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
      intros [[b s] c]. reflexivity. }
    change (eqA
      ((spure (@swap C A) >>>
          ((pure (@state_shuffle_in S A C) >>>
              (first g >>> pure (@state_shuffle_out S B C))) >>>
            spure (@swap B C))) >>> pure (@assoc_prod C B S))
      (pure (@assoc_prod C A S) >>>
        (pure (@swap C (A * S)) >>>
          (first g >>> pure (@swap (B * S) C))))).
    etransitivity. { apply cassoc. }
    etransitivity.
    { apply cprop. 1: reflexivity. apply cassoc. }
    etransitivity.
    { apply cprop. 1: reflexivity. apply cassoc. }
    etransitivity.
    { apply cprop. 1: reflexivity.
      apply cprop. 1: reflexivity. apply cassoc. }
    etransitivity.
    { apply cprop. 1: reflexivity.
      apply cprop. 1: reflexivity.
      apply cprop. 1: reflexivity. exact Htail. }
    etransitivity. { symmetry. apply cassoc. }
    etransitivity.
    { apply cprop. 2: reflexivity. exact Hhead. }
    apply cassoc.
  Qed.

  #[global]
  Instance ArrowApplyLaws_stateArrT : ArrowApplyLaws (stateArrT S arr).
  Proof.
    constructor.
    - (* app_law *)
      intros A B f.
      change (eqA (spure (fun a => (f, a)) >>> sapp) f).
      etransitivity. { apply state_pure_app. }
      transitivity (pure (fun p : A * S => (f, p)) >>> app).
      + apply cprop. 2: reflexivity.
        apply (@Arrow.arr_pure_ext arr HA HE). intros [a s]. reflexivity.
      + apply alaw.
    - (* app_unit *)
      intros A B.
      change (eqA
        (sfirst (spure (fun x : A => spure (fun y : B => (x, y)))) >>> sapp)
        (spure (fun p : A * B => p))).
      etransitivity. { apply state_first_pure_app. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply app_pure. }
      unfold arr_pure, Arrow_stateArrT.
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
      intros [[a b] s]. reflexivity.
    - (* app_precompose *)
      intros A B C g.
      change (eqA
        (sfirst (spure (fun f : stateArrT S arr B C => g >>> f)) >>> sapp)
        (ssecond g >>> sapp)).
      etransitivity. { apply state_first_pure_app. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply apre. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity.
        symmetry. apply state_second_assoc. }
      apply cassoc.
    - (* app_postcompose *)
      intros A B C h.
      change (eqA
        (sfirst (spure (fun f : stateArrT S arr A B => f >>> h)) >>> sapp)
        (sapp >>> h)).
      etransitivity. { apply state_first_pure_app. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply apost. }
      symmetry. apply cassoc.
    - (* app_ext *)
      intros X A B u v Huv.
      change (eqA (spure u >>> sapp) (spure v >>> sapp)).
      etransitivity. { apply state_pure_app. }
      symmetry. etransitivity. { apply state_pure_app. }
      apply aext. intros [x s].
      specialize (Huv x).
      destruct (u x) as [f a], (v x) as [g b].
      destruct Huv as [Hfg Hab]. cbn in Hfg, Hab |- *.
      change (a = b) in Hab.
      subst b. split.
      + symmetry. exact Hfg.
      + reflexivity.
  Qed.

End StateArrowTApplyLaws.
