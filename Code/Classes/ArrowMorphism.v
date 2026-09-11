(** * Arrow morphisms and their option/state lifts.

    An ordinary record packages preservation of pure arrows, composition,
    pairing, choice, and higher-order application.  Inverse maps preserve
    these operations, and the existing option and state transformers lift
    the morphisms.  All dictionaries are explicit. *)

From Coq Require Import FunctionalExtensionality RelationClasses.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.

(** ** An ordinary record for all five preservation equations

    The [morphism_app] field changes the type of the embedded arrow in
    the input.  Treating [app] as a nullary operation with unchanged
    input would omit this essential part of the equivalence. *)

Record ArrowMorphism {src dst : Type -> Type -> Type}
  (SA : Arrow src) (SC : @ArrowChoice src SA) (SX : @ArrowApply src SA)
  (DA : Arrow dst) (DC : @ArrowChoice dst DA) (DX : @ArrowApply dst DA)
  (map : forall A B, src A B -> dst A B) : Prop := {
  morphism_pure : forall A B (h : A -> B),
    map A B (@arr_pure src SA A B h) = @arr_pure dst DA A B h;
  morphism_comp : forall A B C (f : src A B) (g : src B C),
    map A C (@arr_comp src SA A B C f g) =
    @arr_comp dst DA A B C (map A B f) (map B C g);
  morphism_first : forall A B C (f : src A B),
    map (A * C)%type (B * C)%type (@arr_first src SA A B C f) =
    @arr_first dst DA A B C (map A B f);
  morphism_left : forall A B C (f : src A B),
    map (A + C)%type (B + C)%type (@arr_left src SA SC A B C f) =
    @arr_left dst DA DC A B C (map A B f);
  morphism_app : forall A B,
    map (src A B * A)%type B (@arr_app src SA SX A B) =
    @arr_comp dst DA _ _ _
      (@arr_pure dst DA _ _ (fun '(f, a) => (map A B f, a)))
      (@arr_app dst DA DX A B)
}.

Arguments morphism_pure {src dst SA SC SX DA DC DX map} _ {A B} _.
Arguments morphism_comp {src dst SA SC SX DA DC DX map} _ {A B C} _ _.
Arguments morphism_first {src dst SA SC SX DA DC DX map} _ {A B C} _.
Arguments morphism_left {src dst SA SC SX DA DC DX map} _ {A B C} _.
Arguments morphism_app {src dst SA SC SX DA DC DX map} _ {A B}.

(** The inverse and lifting results use Leibniz equality.  This
    dictionary is an ordinary definition, never a global instance. *)
Definition ArrowEq_leibniz (arr : Type -> Type -> Type) : ArrowEq arr :=
  {| arrow_eq := fun A B => @eq (arr A B);
     arrow_eq_equiv := fun A B => eq_equivalence |}.

Section InverseMorphism.
  Context {src dst : Type -> Type -> Type}
    {SA : Arrow src} {SC : @ArrowChoice src SA} {SX : @ArrowApply src SA}
    {DA : Arrow dst} {DC : @ArrowChoice dst DA} {DX : @ArrowApply dst DA}.
  Variables (to : forall A B, src A B -> dst A B)
    (back : forall A B, dst A B -> src A B).
  Hypothesis back_to : forall A B f, back A B (to A B f) = f.
  Hypothesis to_back : forall A B f, to A B (back A B f) = f.
  Variable M : ArrowMorphism SA SC SX DA DC DX to.
  Variable DL : @ArrowLaws dst DA (ArrowEq_leibniz dst).

  Lemma morphism_injective {A B} (f g : src A B) :
    to A B f = to A B g -> f = g.
  Proof.
    intro H. rewrite <- (back_to A B f), <- (back_to A B g). now rewrite H.
  Qed.

  Theorem inverse_morphism : ArrowMorphism DA DC DX SA SC SX back.
  Proof.
    constructor; intros.
    - apply morphism_injective. rewrite to_back, (morphism_pure M). reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_comp M), !to_back. reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_first M), to_back. reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_left M), to_back. reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_comp M), (morphism_pure M), (morphism_app M).
      pose proof (@comp_assoc dst DA (ArrowEq_leibniz dst) DL) as Hassoc.
      pose proof (@pure_comp dst DA (ArrowEq_leibniz dst) DL) as Hpure.
      cbn [arrow_eq ArrowEq_leibniz] in Hassoc, Hpure.
      rewrite <- Hassoc, Hpure.
      replace (fun x : dst A B * A =>
        let '(f, a) := (let '(g, a) := x in (back A B g, a)) in
        (to A B f, a)) with (fun x : dst A B * A => x).
      + symmetry. exact (@comp_id_l dst DA (ArrowEq_leibniz dst) DL _ _ _).
      + extensionality x. destruct x as [f a]. cbn. now rewrite to_back.
  Qed.
End InverseMorphism.

(** ** Lifting morphisms through the existing arrow transformers *)

Definition option_arrow_map {src dst : Type -> Type -> Type}
  (map : forall A B, src A B -> dst A B) :
  forall A B, optionArrT src A B -> optionArrT dst A B :=
  fun A B => map A (option B).

Definition state_arrow_map (S : Type) {src dst : Type -> Type -> Type}
  (map : forall A B, src A B -> dst A B) :
  forall A B, stateArrT S src A B -> stateArrT S dst A B :=
  fun A B => map (A * S)%type (B * S)%type.

Lemma option_arrow_map_roundtrip {src dst : Type -> Type -> Type}
  (to : forall A B, src A B -> dst A B)
  (back : forall A B, dst A B -> src A B)
  (H : forall A B f, back A B (to A B f) = f) A B f :
  option_arrow_map back A B (option_arrow_map to A B f) = f.
Proof. apply H. Qed.

Lemma state_arrow_map_roundtrip S {src dst : Type -> Type -> Type}
  (to : forall A B, src A B -> dst A B)
  (back : forall A B, dst A B -> src A B)
  (H : forall A B f, back A B (to A B f) = f) A B f :
  state_arrow_map S back A B (state_arrow_map S to A B f) = f.
Proof. apply H. Qed.

(** Pure precomposition at the option layer reduces to base
    precomposition.  This uses [left_inl], not carrier reindexing. *)
Section OptionPureComposition.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA}.
  Variable HL : @ArrowLaws arr HA (ArrowEq_leibniz arr).
  Variable HCL : @ArrowChoiceLaws arr HA HC (ArrowEq_leibniz arr).
  Local Notation pure := (@arr_pure arr HA).
  Local Notation comp := (@arr_comp arr HA).
  Local Notation OA := (@Arrow_optionArrT arr HA HC).

  Lemma option_pure_comp_eq {A B C} (h : A -> B) (f : optionArrT arr B C) :
    @arr_comp (optionArrT arr) OA A B C
      (@arr_pure (optionArrT arr) OA A B h) f = comp (pure h) f.
  Proof.
    exact (@optionArrT_comp_pure_l arr HA HC (ArrowEq_leibniz arr)
      HL HCL A B C h f).
  Qed.
End OptionPureComposition.

Create HintDb arrow_morphism_ops.
#[local] Hint Unfold option_arrow_map state_arrow_map
  arr_pure arr_comp arr_first arr_left arr_app
  Arrow_optionArrT ArrowChoice_optionArrT ArrowApply_optionArrT
  Arrow_stateArrT ArrowChoice_stateArrT ArrowApply_stateArrT : arrow_morphism_ops.

Section LiftMorphism.
  Context {src dst : Type -> Type -> Type}
    {SA : Arrow src} {SC : @ArrowChoice src SA} {SX : @ArrowApply src SA}
    {DA : Arrow dst} {DC : @ArrowChoice dst DA} {DX : @ArrowApply dst DA}.
  Variable map : forall A B, src A B -> dst A B.
  Variable M : ArrowMorphism SA SC SX DA DC DX map.
  Variable DL : @ArrowLaws dst DA (ArrowEq_leibniz dst).

  Local Notation SO := (@Arrow_optionArrT src SA SC).
  Local Notation DO := (@Arrow_optionArrT dst DA DC).

  Theorem option_arrow_morphism
    (DCL : @ArrowChoiceLaws dst DA DC (ArrowEq_leibniz dst)) :
    ArrowMorphism SO (@ArrowChoice_optionArrT src SA SC)
      (@ArrowApply_optionArrT src SA SC SX)
      DO (@ArrowChoice_optionArrT dst DA DC)
      (@ArrowApply_optionArrT dst DA DC DX) (option_arrow_map map).
  Proof.
    constructor; intros.
    - apply (morphism_pure M).
    - autounfold with arrow_morphism_ops.
      rewrite !(morphism_comp M), !(morphism_pure M), (morphism_left M).
      reflexivity.
    - autounfold with arrow_morphism_ops.
      rewrite (morphism_comp M), (morphism_first M), (morphism_pure M).
      reflexivity.
    - autounfold with arrow_morphism_ops.
      rewrite (morphism_comp M), (morphism_left M), (morphism_pure M).
      reflexivity.
    - rewrite (option_pure_comp_eq DL DCL).
      apply (morphism_app M).
  Qed.

  Theorem state_arrow_morphism (S : Type) :
    ArrowMorphism (@Arrow_stateArrT S src SA)
      (@ArrowChoice_stateArrT S src SA SC) (@ArrowApply_stateArrT S src SA SX)
      (@Arrow_stateArrT S dst DA)
      (@ArrowChoice_stateArrT S dst DA DC) (@ArrowApply_stateArrT S dst DA DX)
      (state_arrow_map S map).
  Proof.
    constructor; intros.
    - apply (morphism_pure M).
    - apply (morphism_comp M).
    - autounfold with arrow_morphism_ops.
      rewrite !(morphism_comp M), !(morphism_pure M), (morphism_first M).
      reflexivity.
    - autounfold with arrow_morphism_ops.
      rewrite !(morphism_comp M), !(morphism_pure M), (morphism_left M).
      reflexivity.
    - autounfold with arrow_morphism_ops.
      rewrite (morphism_comp M), (morphism_pure M), (morphism_app M).
      pose proof (@comp_assoc dst DA (ArrowEq_leibniz dst) DL) as Hassoc.
      pose proof (@pure_comp dst DA (ArrowEq_leibniz dst) DL) as Hpure.
      cbn [arrow_eq ArrowEq_leibniz] in Hassoc, Hpure.
      rewrite <- !Hassoc, !Hpure.
      f_equal. f_equal. extensionality x. destruct x as [[f a] s]. reflexivity.
  Qed.
End LiftMorphism.

Section LiftStateOptionMorphism.
  Context {src dst : Type -> Type -> Type}
    {SA : Arrow src} {SC : @ArrowChoice src SA} {SX : @ArrowApply src SA}
    {DA : Arrow dst} {DC : @ArrowChoice dst DA} {DX : @ArrowApply dst DA}.
  Variable map : forall A B, src A B -> dst A B.
  Variable M : ArrowMorphism SA SC SX DA DC DX map.
  Variable DL : @ArrowLaws dst DA (ArrowEq_leibniz dst).

  Local Notation SO := (@Arrow_optionArrT src SA SC).
  Local Notation DO := (@Arrow_optionArrT dst DA DC).

  Theorem state_option_arrow_morphism (S : Type)
    (DCL : @ArrowChoiceLaws dst DA DC (ArrowEq_leibniz dst)) :
    ArrowMorphism (@Arrow_stateArrT S (optionArrT src) SO)
      (@ArrowChoice_stateArrT S (optionArrT src) SO
        (@ArrowChoice_optionArrT src SA SC))
      (@ArrowApply_stateArrT S (optionArrT src) SO
        (@ArrowApply_optionArrT src SA SC SX))
      (@Arrow_stateArrT S (optionArrT dst) DO)
      (@ArrowChoice_stateArrT S (optionArrT dst) DO
        (@ArrowChoice_optionArrT dst DA DC))
      (@ArrowApply_stateArrT S (optionArrT dst) DO
        (@ArrowApply_optionArrT dst DA DC DX))
      (state_arrow_map S (option_arrow_map map)).
  Proof.
    exact (@state_arrow_morphism (optionArrT src) (optionArrT dst)
      SO (@ArrowChoice_optionArrT src SA SC) (@ArrowApply_optionArrT src SA SC SX)
      DO (@ArrowChoice_optionArrT dst DA DC) (@ArrowApply_optionArrT dst DA DC DX)
      (option_arrow_map map) (option_arrow_morphism map M DL DCL)
      (@ArrowLaws_optionArrT dst DA DC (ArrowEq_leibniz dst) DL DCL) S).
  Qed.
End LiftStateOptionMorphism.
