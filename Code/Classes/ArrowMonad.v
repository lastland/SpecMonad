(** * A lawful monad from higher-order arrow application.

    For every fixed input [I], [arr I] supports return and bind.  The
    arrow and application laws make these operations a monad up to the
    arrow's own equivalence relation. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowApplyFacts.

Section ArrowMonad.
  Variable arr : Type -> Type -> Type.
  Context `{HA : Arrow arr} `{HAA : ArrowApply arr}.
  Variable I : Type.

  Definition ret_arrow {A} (a : A) : arr I A :=
    arr_pure (fun _ => a).

  Definition bind_arrow {A B} (m : arr I A) (k : A -> arr I B) : arr I B :=
    arr_comp (arr_fanout m arr_id)
      (arr_comp (arr_pure (fun '(a, i) => (k a, i))) arr_app).

  #[global] Instance Monad_Arrow : Monad (arr I) := {
    ret := @ret_arrow;
    bind := @bind_arrow
  }.
End ArrowMonad.

(** The equality dictionary is explicit so that importing this module
    does not compete with concrete monads' chosen [Eq1] instances. *)
Definition Eq1_Arrow {arr : Type -> Type -> Type} (HE : ArrowEq arr)
  (I : Type) : Eq1 (arr I) :=
  fun A => @arrow_eq arr HE I A.

#[global] Instance Eq1Equivalence_Arrow
  {arr : Type -> Type -> Type} {HA : Arrow arr}
  {HAA : @ArrowApply arr HA} {HE : ArrowEq arr} (I : Type) :
  @Eq1Equivalence (arr I) (@Monad_Arrow arr HA HAA I)
    (@Eq1_Arrow arr HE I) :=
  fun A => @arrow_eq_equiv arr HE I A.

Section ArrowMonadLaws.
  Context {arr : Type -> Type -> Type}
    `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
    `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
    `{HAL : @ArrowApplyLaws arr HA HAA HE}.

  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 50, left associativity).
  Local Notation pure := (@arr_pure arr HA _ _).
  Local Notation first := (@arr_first arr HA _ _ _).
  Local Notation app := (@arr_app arr HA HAA _ _).
  Local Notation eqA := (@arrow_eq arr HE _ _).
  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidr := (@comp_id_r arr HA HE HL).
  Local Notation pcomp := (@pure_comp arr HA HE HL).
  Local Notation cprop := (@comp_proper arr HA HE HL).
  Local Notation fprop := (@first_proper arr HA HE HL).
  Local Notation fpure := (@first_pure arr HA HE HL).
  Local Notation aext := (@app_ext arr HA HAA HE HAL).
  Local Notation arrow_ext := (@ArrowApplyFacts.arrow_ext arr HA HAA HE HL HAL).

  Create HintDb arrow_monad_fanout.
  #[local] Hint Unfold arr_fanout arr_split : arrow_monad_fanout.

  Local Lemma second_id {A B} :
    eqA (@arr_second arr HA A A B (@arr_id arr HA A))
        (@arr_id arr HA (B * A)).
  Proof.
    unfold arr_second, arr_id.
    etransitivity.
    { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity. apply fpure. }
    etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
    apply (@pure_comp_ext arr HA HE HL
      (@ArrowApplyFacts.pure_proper arr HA HAA HE HL HAL)).
    intros [b a]. reflexivity.
  Qed.

  Local Lemma fanout_id {A B} (f : arr A B) :
    eqA (@arr_fanout arr HA _ _ _ f (@arr_id arr HA A))
        (pure (fun a => (a, a)) >>> first f).
  Proof.
    autounfold with arrow_monad_fanout.
    apply cprop. 1: reflexivity.
    etransitivity. { apply cprop. 1: reflexivity. apply second_id. }
    apply cidr.
  Qed.

  Local Lemma fanout_id_at {I A} (m : arr I A) (i : I) :
    eqA (pure (fun _ : unit => i) >>>
          @arr_fanout arr HA _ _ _ m (@arr_id arr HA I))
        ((pure (fun _ : unit => i) >>> m) >>> pure (fun a => (a, i))).
  Proof.
    assert (Hhead :
      eqA (pure (fun _ : unit => i) >>> pure (fun j => (j, j)))
          (pure (fun _ : unit => i) >>> pure (fun j => (j, i)))).
    { etransitivity. { apply pcomp. }
      symmetry. etransitivity. { apply pcomp. } reflexivity. }
    etransitivity. { apply cprop. 1: reflexivity. apply fanout_id. }
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. exact Hhead. }
    etransitivity. { apply cassoc. }
    (* A constant companion commutes with [first], by naturality and
       projection. This step preserves the fixed monad input. *)
    etransitivity.
    { apply cprop. 1: reflexivity.
      apply (@Arrow.first_constant arr HA HE HL
        (@ArrowApplyFacts.pure_proper arr HA HAA HE HL HAL)). }
    symmetry. apply cassoc.
  Qed.

  (** At a fixed input, bind is ordinary arrow composition followed by
      application of the selected continuation at that same input. *)
  Local Lemma bind_arrow_at {I A B} (m : arr I A)
    (k : A -> arr I B) (i : I) :
    eqA (pure (fun _ : unit => i) >>> @bind_arrow arr HA HAA I A B m k)
        ((pure (fun _ : unit => i) >>> m) >>>
          (pure (fun a => (k a, i)) >>> app)).
  Proof.
    unfold bind_arrow.
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. apply fanout_id_at. }
    etransitivity. { apply cassoc. }
    apply cprop. 1: reflexivity.
    etransitivity. { symmetry. apply cassoc. }
    apply cprop. 2: reflexivity.
    etransitivity. { apply pcomp. } reflexivity.
  Qed.

  (** Compatibility with the former unit-input development. *)
  Lemma bind_arrow_unit {A B} (m : arr unit A) (k : A -> arr unit B) :
    eqA (@bind_arrow arr HA HAA unit A B m k)
      (m >>> (pure (fun a => (k a, tt)) >>> app)).
  Proof.
    apply arrow_ext. intros [].
    etransitivity. { apply bind_arrow_at. }
    apply cassoc.
  Qed.

  Local Lemma app_at_constant {I A B} (k : A -> arr I B) (i : I) (a : A) :
    eqA (pure (fun _ : unit => a) >>>
          (pure (fun a => (k a, i)) >>> app))
        (pure (fun _ : unit => i) >>> k a).
  Proof.
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
    exact (@ArrowApplyFacts.app_constant arr HA HAA HE HL unit I B
      (k a) i (@app_law arr HA HAA HE HAL I B (k a))).
  Qed.

  Local Lemma app_at_ret {I A} (i : I) :
    eqA (pure (fun a : A => (@ret_arrow arr HA I A a, i)) >>> app)
        (@arr_id arr HA A).
  Proof.
    apply arrow_ext. intro a.
    etransitivity. { apply app_at_constant. }
    unfold ret_arrow.
    etransitivity. { apply pcomp. }
    symmetry. apply cidr.
  Qed.

  #[global] Instance MonadLawsE_Arrow (I : Type) :
    @MonadLawsE (arr I) (@Eq1_Arrow arr HE I) (@Monad_Arrow arr HA HAA I).
  Proof.
    constructor.
    - (* Left identity. *)
      intros A B k a.
      change (eqA (@bind_arrow arr HA HAA I A B (@ret_arrow arr HA I A a) k)
        (k a)).
      apply arrow_ext. intro i.
      etransitivity. { apply bind_arrow_at. }
      unfold ret_arrow.
      etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
      exact (app_at_constant k i a).
    - (* Right identity. *)
      intros A m.
      change (eqA (@bind_arrow arr HA HAA I A A m (@ret_arrow arr HA I A)) m).
      apply arrow_ext. intro i.
      etransitivity. { apply bind_arrow_at. }
      etransitivity. { apply cprop. 1: reflexivity. apply app_at_ret. }
      apply cidr.
    - (* Associativity.  Fixing the continuation's input exposes the
         same three-arrow composition on both sides. *)
      intros A B C m k l.
      change (eqA
        (@bind_arrow arr HA HAA I B C (@bind_arrow arr HA HAA I A B m k) l)
        (@bind_arrow arr HA HAA I A C m
          (fun a => @bind_arrow arr HA HAA I B C (k a) l))).
      apply arrow_ext. intro i.
      etransitivity. { apply bind_arrow_at. }
      etransitivity. { apply cprop. 2: reflexivity. apply bind_arrow_at. }
      etransitivity. { apply cassoc. }
      symmetry.
      etransitivity. { apply bind_arrow_at. }
      apply cprop. 1: reflexivity.
      apply arrow_ext. intro a.
      etransitivity. { apply app_at_constant. }
      etransitivity. { apply bind_arrow_at. }
      symmetry.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. apply app_at_constant.
    - (* Bind respects both the computation and pointwise continuation
         equivalence, including arrow values stored inside pure inputs. *)
      intros A B m n Hmn k l Hkl.
      change (eqA (@bind_arrow arr HA HAA I A B m k)
        (@bind_arrow arr HA HAA I A B n l)).
      unfold bind_arrow. apply cprop.
      + autounfold with arrow_monad_fanout.
        apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity.
        apply fprop. exact Hmn.
      + apply aext. intros [a i]. split.
        * apply Hkl.
        * reflexivity.
  Qed.
End ArrowMonadLaws.
