(** * Arrow morphisms and their option/state lifts.

    An ordinary record packages preservation of pure arrows, composition,
    pairing, choice, and higher-order application up to selected semantic
    equality, together with properness of the map. Inverse maps preserve
    these operations, and the existing option and state transformers lift
    the morphisms.  At each fixed input an arrow morphism is a monad morphism
    between the monads of the two arrows.  All dictionaries are explicit. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowApplyFacts OptionArrowT StateArrowT.
From Incorrectness.Classes Require Import ArrowMonad OrderedMonad.

(** ** An ordinary record for all five preservation equations

    [morphism_pure], [morphism_comp], and [morphism_first] follow the
    arrow-morphism equations in Atkey's Definition 4.4:
    [F(arr h) = arr h], [F(f >>> g) = F f >>> F g], and
    [F(first f) = first (F f)], where [F] is [map].
    Our fields use the selected destination [arrow_eq] instead of
    ordinary equality; [≈] below denotes that equivalence.

    This development extends Definition 4.4 with three requirements:
    - [morphism_proper] maps source-equivalent arrows to
      destination-equivalent arrows, so [map] respects the selected
      equivalences.
    - [morphism_left] preserves [ArrowChoice]'s [arr_left], so the map
      also preserves branching.
    - [morphism_app] preserves [ArrowApply] application, converting
      the embedded arrow in the input:
      [F(app_src) ≈ arr_dst (fun '(f, a) => (F f, a)) >>> app_dst].

    Source application consumes a source arrow; destination application
    consumes a destination arrow. The input conversion therefore maps
    the stored arrow with [F]. Treating [app] as a nullary operation
    with unchanged input would omit this essential conversion.

    Reference: Robert Atkey, "What is a Categorical Model of Arrows?",
    MSFP 2008; ENTCS 229 (2011), pp. 19-37, Definition 4.4.
    Author manuscript (p. 11): https://bentnib.org/arrows.pdf
    Published version: https://doi.org/10.1016/j.entcs.2011.02.014 *)

Record ArrowMorphism {src dst : Type -> Type -> Type}
  (SA : Arrow src) (SC : @ArrowChoice src SA) (SX : @ArrowApply src SA)
  (SE : ArrowEq src)
  (DA : Arrow dst) (DC : @ArrowChoice dst DA) (DX : @ArrowApply dst DA)
  (DE : ArrowEq dst)
  (map : forall A B, src A B -> dst A B) : Prop := {
  morphism_proper : forall A B,
    Proper (@arrow_eq src SE A B ==> @arrow_eq dst DE A B) (map A B);
  morphism_pure : forall A B (h : A -> B),
    @arrow_eq dst DE A B (map A B (@arr_pure src SA A B h)) (@arr_pure dst DA A B h);
  morphism_comp : forall A B C (f : src A B) (g : src B C),
    @arrow_eq dst DE A C (map A C (@arr_comp src SA A B C f g))
    (@arr_comp dst DA A B C (map A B f) (map B C g));
  morphism_first : forall A B C (f : src A B),
    @arrow_eq dst DE _ _ (map (A * C)%type (B * C)%type (@arr_first src SA A B C f))
    (@arr_first dst DA A B C (map A B f));
  morphism_left : forall A B C (f : src A B),
    @arrow_eq dst DE _ _ (map (A + C)%type (B + C)%type (@arr_left src SA SC A B C f))
    (@arr_left dst DA DC A B C (map A B f));
  morphism_app : forall A B,
    @arrow_eq dst DE _ _ (map (src A B * A)%type B (@arr_app src SA SX A B))
    (@arr_comp dst DA _ _ _
      (@arr_pure dst DA _ _ (fun '(f, a) => (map A B f, a)))
      (@arr_app dst DA DX A B))
}.

Arguments morphism_proper {src dst SA SC SX SE DA DC DX DE map} _ {A B} _ _ _.
Arguments morphism_pure {src dst SA SC SX SE DA DC DX DE map} _ {A B} _.
Arguments morphism_comp {src dst SA SC SX SE DA DC DX DE map} _ {A B C} _ _.
Arguments morphism_first {src dst SA SC SX SE DA DC DX DE map} _ {A B C} _.
Arguments morphism_left {src dst SA SC SX SE DA DC DX DE map} _ {A B C} _.
Arguments morphism_app {src dst SA SC SX SE DA DC DX DE map} _ {A B}.

(** An independent Leibniz dictionary, never a global instance. *)
Definition ArrowEq_leibniz (arr : Type -> Type -> Type) : ArrowEq arr :=
  {| arrow_eq := fun A B => @eq (arr A B);
     arrow_eq_equiv := fun A B => eq_equivalence |}.

Section InverseMorphism.
  Context {src dst : Type -> Type -> Type}
    {SA : Arrow src} {SC : @ArrowChoice src SA} {SX : @ArrowApply src SA}
    {SE : ArrowEq src}
    {DA : Arrow dst} {DC : @ArrowChoice dst DA} {DX : @ArrowApply dst DA}
    {DE : ArrowEq dst}.
  Variables (to : forall A B, src A B -> dst A B)
    (back : forall A B, dst A B -> src A B).
  Hypothesis back_proper : forall A B,
    Proper (@arrow_eq dst DE A B ==> @arrow_eq src SE A B) (back A B).
  Hypothesis back_to : forall A B f, @arrow_eq src SE A B (back A B (to A B f)) f.
  Hypothesis to_back : forall A B f, @arrow_eq dst DE A B (to A B (back A B f)) f.
  Variable M : ArrowMorphism SA SC SX SE DA DC DX DE to.
  Variable DL : @ArrowLaws dst DA DE.
  Variable DCL : @ArrowChoiceLaws dst DA DC DE.
  Variable DXL : @ArrowApplyLaws dst DA DX DE.
  Local Existing Instance DL.
  Local Instance inverse_left_proper A B C :
    Proper (@arrow_eq dst DE A B ==> @arrow_eq dst DE (A + C)%type (B + C)%type)
      (@arr_left dst DA DC A B C) := @left_proper dst DA DC DE DCL A B C.

  Lemma morphism_injective {A B} (f g : src A B) :
    @arrow_eq dst DE A B (to A B f) (to A B g) -> @arrow_eq src SE A B f g.
  Proof.
    intro H. transitivity (back A B (to A B f)).
    - symmetry. apply back_to.
    - transitivity (back A B (to A B g)).
      + apply back_proper. exact H.
      + apply back_to.
  Qed.

  Theorem inverse_morphism : ArrowMorphism DA DC DX DE SA SC SX SE back.
  Proof.
    constructor; intros.
    - apply back_proper.
    - apply morphism_injective. rewrite to_back, (morphism_pure M). reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_comp M), !to_back. reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_first M), to_back. reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_left M), to_back. reflexivity.
    - apply morphism_injective.
      rewrite to_back, (morphism_comp M), (morphism_pure M), (morphism_app M).
      pose proof (@comp_assoc dst DA DE DL) as Hassoc.
      pose proof (@pure_comp dst DA DE DL) as Hpure.
      rewrite <- Hassoc, Hpure.
      symmetry. etransitivity.
      + apply (@app_ext dst DA DX DE DXL _ A B _ (fun x => x)).
        intros [g a]. cbn.
        split; [apply to_back | reflexivity].
      + exact (@comp_id_l dst DA DE DL _ _ _).
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
  {SE : ArrowEq src}
  (to : forall A B, src A B -> dst A B)
  (back : forall A B, dst A B -> src A B)
  (H : forall A B f, @arrow_eq src SE A B (back A B (to A B f)) f) A B f :
  @arrow_eq (optionArrT src) (@ArrowEq_optionArrT src SE) A B
    (option_arrow_map back A B (option_arrow_map to A B f)) f.
Proof. apply H. Qed.

Lemma state_arrow_map_roundtrip S {src dst : Type -> Type -> Type}
  {SE : ArrowEq src}
  (to : forall A B, src A B -> dst A B)
  (back : forall A B, dst A B -> src A B)
  (H : forall A B f, @arrow_eq src SE A B (back A B (to A B f)) f) A B f :
  @arrow_eq (stateArrT S src) (@ArrowEq_stateArrT S src SE) A B
    (state_arrow_map S back A B (state_arrow_map S to A B f)) f.
Proof. apply H. Qed.

(** Pure precomposition at the option layer reduces to base
    precomposition.  This uses [left_inl], not carrier reindexing. *)
Section OptionPureComposition.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HE : ArrowEq arr}.
  Variable HL : @ArrowLaws arr HA HE.
  Variable HCL : @ArrowChoiceLaws arr HA HC HE.
  Local Notation pure := (@arr_pure arr HA).
  Local Notation comp := (@arr_comp arr HA).
  Local Notation OA := (@Arrow_optionArrT arr HA HC).

  Lemma option_pure_comp_eq {A B C} (h : A -> B) (f : optionArrT arr B C) :
    @arrow_eq arr HE A (option C)
      (@arr_comp (optionArrT arr) OA A B C
      (@arr_pure (optionArrT arr) OA A B h) f) (comp (pure h) f).
  Proof.
    exact (@optionArrT_comp_pure_l arr HA HC HE
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
    {SE : ArrowEq src}
    {DA : Arrow dst} {DC : @ArrowChoice dst DA} {DX : @ArrowApply dst DA}
    {DE : ArrowEq dst}.
  Variable map : forall A B, src A B -> dst A B.
  Variable M : ArrowMorphism SA SC SX SE DA DC DX DE map.
  Variable DL : @ArrowLaws dst DA DE.
  Local Existing Instance DL.

  Local Notation SO := (@Arrow_optionArrT src SA SC).
  Local Notation DO := (@Arrow_optionArrT dst DA DC).

  Theorem option_arrow_morphism
    (DCL : @ArrowChoiceLaws dst DA DC DE) :
    ArrowMorphism SO (@ArrowChoice_optionArrT src SA SC)
      (@ArrowApply_optionArrT src SA SC SX)
      (@ArrowEq_optionArrT src SE)
      DO (@ArrowChoice_optionArrT dst DA DC)
      (@ArrowApply_optionArrT dst DA DC DX) (@ArrowEq_optionArrT dst DE)
      (option_arrow_map map).
  Proof.
    assert (Hleft := @left_proper dst DA DC DE DCL).
    constructor; intros; cbn [arrow_eq ArrowEq_optionArrT].
    - exact (@morphism_proper _ _ _ _ _ _ _ _ _ _ _ M A (option B)).
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

  Theorem state_arrow_morphism (S : Type)
    (DXL : @ArrowApplyLaws dst DA DX DE) :
    ArrowMorphism (@Arrow_stateArrT S src SA)
      (@ArrowChoice_stateArrT S src SA SC) (@ArrowApply_stateArrT S src SA SX)
      (@ArrowEq_stateArrT S src SE)
      (@Arrow_stateArrT S dst DA)
      (@ArrowChoice_stateArrT S dst DA DC) (@ArrowApply_stateArrT S dst DA DX)
      (@ArrowEq_stateArrT S dst DE)
      (state_arrow_map S map).
  Proof.
    constructor; intros; cbn [arrow_eq ArrowEq_stateArrT].
    - exact (@morphism_proper _ _ _ _ _ _ _ _ _ _ _ M (A * S)%type (B * S)%type).
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
      pose proof (@comp_assoc dst DA DE DL) as Hassoc.
      pose proof (@pure_comp dst DA DE DL) as Hpure.
      rewrite <- !Hassoc, !Hpure.
      apply (@comp_proper dst DA DE DL); [|reflexivity].
      apply (@ArrowApplyFacts.pure_ext dst DA DX DE DL DXL).
      intros [[f a] s]. reflexivity.
  Qed.

  (** At a fixed input [I], each arrow gives a monad ([ArrowMonad.v]), and
      the morphism is a monad morphism between the two. *)
  Theorem arrow_morphism_monad (I : Type)
    (DXL : @ArrowApplyLaws dst DA DX DE) :
    @MonadMorphism (src I) (dst I)
      (@Monad_Arrow src SA SX I) (@Monad_Arrow dst DA DX I)
      (@Eq1_Arrow src SE I) (@Eq1_Arrow dst DE I)
      (fun A => map I A).
  Proof.
    constructor.
    - intros A x y H.
      exact (@morphism_proper _ _ _ _ _ _ _ _ _ _ _ M I A x y H).
    - intros A a. exact (morphism_pure M (fun _ : I => a)).
    - intros A B m k.
      change (@arrow_eq dst DE I B
                (map I B (@bind_arrow src SA SX I A B m k))
                (@bind_arrow dst DA DX I A B (map I A m)
                   (fun a => map I B (k a)))).
      unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id.
      rewrite !(morphism_comp M), !(morphism_first M), !(morphism_pure M),
        (morphism_app M).
      apply (@comp_proper dst DA DE DL); [ reflexivity |].
      etransitivity; [ symmetry; apply (@comp_assoc dst DA DE DL) |].
      etransitivity;
        [ apply (@comp_proper dst DA DE DL);
            [ apply (@pure_comp dst DA DE DL) | reflexivity ] |].
      apply (@app_ext dst DA DX DE DXL). intros [a i]. split; reflexivity.
  Qed.
End LiftMorphism.

Section LiftStateOptionMorphism.
  Context {src dst : Type -> Type -> Type}
    {SA : Arrow src} {SC : @ArrowChoice src SA} {SX : @ArrowApply src SA}
    {SE : ArrowEq src}
    {DA : Arrow dst} {DC : @ArrowChoice dst DA} {DX : @ArrowApply dst DA}
    {DE : ArrowEq dst}.
  Variable map : forall A B, src A B -> dst A B.
  Variable M : ArrowMorphism SA SC SX SE DA DC DX DE map.
  Variable DL : @ArrowLaws dst DA DE.

  Local Notation SO := (@Arrow_optionArrT src SA SC).
  Local Notation DO := (@Arrow_optionArrT dst DA DC).

  Theorem state_option_arrow_morphism (S : Type)
    (DCL : @ArrowChoiceLaws dst DA DC DE)
    (DXL : @ArrowApplyLaws dst DA DX DE) :
    ArrowMorphism (@Arrow_stateArrT S (optionArrT src) SO)
      (@ArrowChoice_stateArrT S (optionArrT src) SO
        (@ArrowChoice_optionArrT src SA SC))
      (@ArrowApply_stateArrT S (optionArrT src) SO
        (@ArrowApply_optionArrT src SA SC SX))
      (@ArrowEq_stateArrT S (optionArrT src) (@ArrowEq_optionArrT src SE))
      (@Arrow_stateArrT S (optionArrT dst) DO)
      (@ArrowChoice_stateArrT S (optionArrT dst) DO
        (@ArrowChoice_optionArrT dst DA DC))
      (@ArrowApply_stateArrT S (optionArrT dst) DO
        (@ArrowApply_optionArrT dst DA DC DX))
      (@ArrowEq_stateArrT S (optionArrT dst) (@ArrowEq_optionArrT dst DE))
      (state_arrow_map S (option_arrow_map map)).
  Proof.
    exact (@state_arrow_morphism (optionArrT src) (optionArrT dst)
      SO (@ArrowChoice_optionArrT src SA SC) (@ArrowApply_optionArrT src SA SC SX)
      (@ArrowEq_optionArrT src SE)
      DO (@ArrowChoice_optionArrT dst DA DC) (@ArrowApply_optionArrT dst DA DC DX)
      (@ArrowEq_optionArrT dst DE)
      (option_arrow_map map) (option_arrow_morphism map M DL DCL)
      (@ArrowLaws_optionArrT dst DA DC DE DL DCL) S
      (@ArrowApplyLaws_optionArrT dst DA DC DX DE DL DCL DXL)).
  Qed.
End LiftStateOptionMorphism.
