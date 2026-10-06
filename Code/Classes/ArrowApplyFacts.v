(** * Generic consequences of arrow application coherence.

    These algebraic facts derive extensionality from the arrow and
    application laws, without assuming functional extensionality. *)

From Incorrectness.Classes Require Import Arrow.

Section StaticApplicationFacts.
  Context {arr : Type -> Type -> Type}
    `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
    `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}.

  (** Static application at a constant input needs only the equation for
      the fixed arrow, not a complete application-law dictionary. *)
  Lemma app_constant {X A B} (f : arr A B) (a : A) :
    @arrow_eq arr HE A B
      (arr_comp (arr_pure (fun a => (f, a))) arr_app) f ->
    @arrow_eq arr HE X B
      (arr_comp (arr_pure (fun _ : X => (f, a))) arr_app)
      (arr_comp (arr_pure (fun _ : X => a)) f).
  Proof.
    intro H. symmetry.
    etransitivity. { apply comp_proper. 1: reflexivity. symmetry. exact H. }
    etransitivity. { symmetry. apply comp_assoc. }
    apply comp_proper. 2: reflexivity.
    etransitivity. { apply pure_comp. } reflexivity.
  Qed.
End StaticApplicationFacts.

Section ArrowApplyFacts.
  Context {arr : Type -> Type -> Type}
    `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
    `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
    `{HAL : @ArrowApplyLaws arr HA HAA HE}.

  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 50, left associativity).
  Local Notation pure := (@arr_pure arr HA _ _).
  Local Notation app := (@arr_app arr HA HAA _ _).
  Local Notation eqA := (@arrow_eq arr HE _ _).
  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl := (@comp_id_l arr HA HE HL).
  Local Notation cidr := (@comp_id_r arr HA HE HL).
  Local Notation pcomp := (@pure_comp arr HA HE HL).
  Local Notation cprop := (@comp_proper arr HA HE HL).
  Local Notation fpure := (@first_pure arr HA HE HL).
  Local Notation aunit := (@app_unit arr HA HAA HE HAL).
  Local Notation apost := (@app_postcompose arr HA HAA HE HAL).
  Local Notation aext := (@app_ext arr HA HAA HE HAL).

  (** Postcomposition coherence after an arbitrary pure input map. *)
  Lemma app_postcompose_pure {X A B C}
    (u : X -> arr A B) (v : X -> A) (h : arr B C) :
    eqA (pure (fun x => (u x >>> h, v x)) >>> app)
        ((pure (fun x => (u x, v x)) >>> app) >>> h).
  Proof.
    symmetry.
    etransitivity. { apply cassoc. }
    etransitivity. { apply cprop. 1: reflexivity. symmetry. apply apost. }
    etransitivity. { symmetry. apply cassoc. }
    apply cprop. 2: reflexivity.
    etransitivity. { apply cprop. 1: reflexivity. apply fpure. }
    etransitivity. { apply pcomp. }
    reflexivity.
  Qed.

  (** Pairing coherence evaluates a dynamically selected constant arrow. *)
  Lemma app_constant_unit (A : Type) :
    eqA (pure (fun a : A => (pure (fun _ : unit => a), tt)) >>> app)
        (@arr_id arr HA A).
  Proof.
    assert (Hpair :
      eqA (pure (fun a : A => (pure (fun y : unit => (a, y)), tt)) >>> app)
          (pure (fun a : A => (a, tt)))).
    { symmetry.
      etransitivity. { symmetry. apply cidr. }
      etransitivity. { apply cprop. 1: reflexivity. symmetry. apply aunit. }
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity.
      etransitivity. { apply cprop. 1: reflexivity. apply fpure. }
      etransitivity. { apply pcomp. }
      reflexivity. }
    etransitivity.
    { apply (aext _ (fun a : A =>
        (pure (fun y : unit => (a, y)) >>> pure fst, tt))).
      intro a. split. 2: reflexivity. symmetry. apply pcomp. }
    etransitivity. { apply app_postcompose_pure. }
    etransitivity. { apply cprop. 2: reflexivity. exact Hpair. }
    etransitivity. { apply pcomp. }
    reflexivity.
  Qed.

  Lemma app_eta {A B} (f : arr A B) :
    eqA (pure (fun a : A => (pure (fun _ : unit => a) >>> f, tt)) >>> app) f.
  Proof.
    etransitivity. { apply app_postcompose_pure. }
    etransitivity. { apply cprop. 2: reflexivity. apply app_constant_unit. }
    apply cidl.
  Qed.

  (** Application coherence lets us prove an arrow equality by fixing
      each ordinary input.  No inhabitant of the input type is required. *)
  Lemma arrow_ext {A B} (f g : arr A B) :
    (forall a, eqA (pure (fun _ : unit => a) >>> f)
                   (pure (fun _ : unit => a) >>> g)) -> eqA f g.
  Proof.
    intro H.
    etransitivity. { symmetry. apply app_eta. }
    etransitivity.
    { apply (aext _ (fun a : A => (pure (fun _ : unit => a) >>> g, tt))).
      intro a. split. 2: reflexivity. apply H. }
    apply app_eta.
  Qed.

  (** Pure extensionality follows from application coherence as well;
      the derivation does not need functional extensionality as an axiom. *)
  Lemma pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) -> eqA (pure f) (pure g).
  Proof.
    intro H. apply arrow_ext. intro a.
    etransitivity. { apply pcomp. }
    symmetry. etransitivity. { apply pcomp. }
    cbn. rewrite H. reflexivity.
  Qed.
End ArrowApplyFacts.
