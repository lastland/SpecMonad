(** * Monad operations from higher-order arrow application.

    For a fixed input [I], [arr I] supports return and bind.  This module
    defines the operations and retains the generic monad laws at input
    [unit] from the four-field [ArrowApplyLaws] contract. *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Coq Require Import Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.

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

(** ** The arrow monad at input [unit] satisfies [MonadLawsE]

    At [I = unit] the fanout collapses: the input is [tt], so there is
    nothing to thread.  These are the generic unit-input laws previously
    defined in [SPostArr], now shared without a concrete-carrier dependency. *)

Section ArrowMonadLaws.
  Variable arr : Type -> Type -> Type.
  Context `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HAAL : @ArrowApplyLaws arr HA HAA HE}.

  Definition Eq1_Arrow : Eq1 (arr unit) := fun A => @arrow_eq arr HE unit A.

  Definition Eq1Equivalence_Arrow
    : @Eq1Equivalence (arr unit) (Monad_Arrow arr unit) Eq1_Arrow :=
    fun A => arrow_eq_equiv unit A.

  Local Lemma second_id {A C} :
    arrow_eq (@arr_second arr HA A A C arr_id) arr_id.
  Proof.
    unfold arr_second, arr_id.
    etransitivity.
    { apply comp_proper; [ reflexivity |].
      apply comp_proper; [ apply first_pure | reflexivity ]. }
    etransitivity; [ apply comp_proper; [ reflexivity | apply pure_comp ] |].
    etransitivity; [ apply pure_comp |].
    apply arr_pure_ext. intros [c a]. reflexivity.
  Qed.

  Local Lemma fanout_id {A B} (m : arr A B) :
    arrow_eq (arr_fanout m arr_id)
             (arr_comp (arr_pure (fun a : A => (a, a))) (arr_first m)).
  Proof.
    unfold arr_fanout, arr_split.
    apply comp_proper; [ reflexivity |].
    etransitivity; [ apply comp_proper; [ reflexivity | apply second_id ] |].
    apply comp_id_r.
  Qed.

  Lemma bind_arrow_unit {A B} (m : arr unit A) (k : A -> arr unit B) :
    arrow_eq (bind_arrow arr unit m k)
             (arr_comp m (arr_comp (arr_pure (fun a => (k a, tt))) arr_app)).
  Proof.
    unfold bind_arrow.
    etransitivity; [ apply comp_proper; [ apply fanout_id | reflexivity ] |].
    etransitivity; [ symmetry; apply comp_assoc |].
    symmetry.
    etransitivity; [ symmetry; apply comp_assoc |].
    symmetry.
    apply comp_proper; [| reflexivity ].
    etransitivity.
    { apply comp_proper; [ reflexivity |].
      apply (arr_pure_ext _ (fun p : A * unit => (k (fst p), tt))).
      intros [a []]. reflexivity. }
    etransitivity.
    { apply comp_proper; [ reflexivity |]. symmetry.
      apply (pure_comp (@fst A unit) (fun a => (k a, tt))). }
    etransitivity; [ symmetry; apply comp_assoc |].
    apply comp_proper; [| reflexivity ].
    etransitivity; [ apply comp_assoc |].
    etransitivity; [ apply comp_proper; [ reflexivity | apply first_fst ] |].
    etransitivity; [ symmetry; apply comp_assoc |].
    etransitivity; [ apply comp_proper; [ apply pure_comp | reflexivity ] |].
    etransitivity.
    { apply comp_proper; [| reflexivity ].
      apply (arr_pure_ext _ (fun x : unit => x)). intros []. reflexivity. }
    apply comp_id_l.
  Qed.

  Local Lemma ret_app_id {A} :
    arrow_eq (arr_comp (arr_pure (fun a : A => (ret_arrow arr unit a, tt))) arr_app)
             arr_id.
  Proof.
    unfold ret_arrow.
    etransitivity.
    { apply (app_ext_at
               (fun a : A => arr_pure (fun _ : unit => a))
               (fun a : A => arr_comp (arr_pure (fun v : unit => (a, v)))
                                      (arr_pure (@fst A unit)))
               (fun _ => tt)).
      intro a. symmetry.
      etransitivity; [ apply pure_comp |].
      apply arr_pure_ext. intros []. reflexivity. }
    etransitivity; [ apply app_post_at |].
    etransitivity.
    { apply comp_proper; [| reflexivity ].
      apply (app_pair_at (fun a : A => a) (fun _ : A => tt)). }
    etransitivity; [ apply pure_comp |].
    unfold arr_id. apply arr_pure_ext. intro a. reflexivity.
  Qed.

  Definition MonadLawsE_Arrow
    : @MonadLawsE (arr unit) Eq1_Arrow (Monad_Arrow arr unit).
  Proof.
    constructor; unfold eq1, Eq1_Arrow; cbn [ret bind Monad_Arrow].
    - intros A B k x.
      etransitivity; [ apply bind_arrow_unit |].
      unfold ret_arrow.
      etransitivity; [ symmetry; apply comp_assoc |].
      etransitivity; [ apply comp_proper; [ apply pure_comp | reflexivity ] |].
      etransitivity.
      { apply comp_proper; [| reflexivity ].
        apply (arr_pure_ext _ (fun u : unit => (k x, u))). intros []. reflexivity. }
      apply app_law.
    - intros A m.
      etransitivity; [ apply bind_arrow_unit |].
      etransitivity; [ apply comp_proper; [ reflexivity | apply ret_app_id ] |].
      apply comp_id_r.
    - intros A B C m f g.
      etransitivity; [ apply bind_arrow_unit |].
      etransitivity;
        [ apply comp_proper; [ apply bind_arrow_unit | reflexivity ] |].
      etransitivity; [ apply comp_assoc |].
      symmetry.
      etransitivity; [ apply bind_arrow_unit |].
      apply comp_proper; [ reflexivity |].
      etransitivity.
      { apply (@app_ext_at arr HA HAA HE HAAL A unit C
                 (fun a : A => bind_arrow arr unit (f a) g)
                 (fun a : A => arr_comp (f a)
                                 (arr_comp (arr_pure (fun b : B => (g b, tt))) arr_app))
                 (fun _ : A => tt)).
        intro a. apply bind_arrow_unit. }
      apply (@app_post_at arr HA HAA HE HL HAAL A unit B C f (fun _ : A => tt)
               (arr_comp (arr_pure (fun b : B => (g b, tt))) arr_app)).
    - intros A B m1 m2 Hm k1 k2 Hk.
      etransitivity; [ apply bind_arrow_unit |].
      symmetry.
      etransitivity; [ apply bind_arrow_unit |].
      symmetry.
      apply comp_proper; [ exact Hm |].
      apply app_ext_at. intro a. apply Hk.
  Qed.
End ArrowMonadLaws.

Arguments Eq1_Arrow {_} {_} {_}.
Arguments MonadLawsE_Arrow {_} {_} {_} {_} {_} {_}.
