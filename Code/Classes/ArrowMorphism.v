(** * Arrow morphisms

    A morphism between two arrows is a family of maps between their hom-sets,
    the identity on types, that respects the source's [arrow_eq] and
    preserves [arr_pure], [arr_comp] and [arr_first] up to the target's.

    [arr_app]'s input carries an arrow of the source, so preserving it means
    converting that arrow before applying it:
    [F arr_app ≡ arr_pure (fun p => (F (fst p), snd p)) >>> arr_app].

    The derived operations ([arr_id], [arr_second], [arr_split],
    [arr_fanout]) are preserved as well.  That [Monad_Arrow] is preserved
    at every input is in [Taxonomy/Arrows/SPostArr.v], next to it. *)

From Coq Require Import Morphisms RelationClasses Setoid.
From Incorrectness.Classes Require Import Arrow.

Class ArrowMorphism (arr1 arr2 : Type -> Type -> Type)
  `{HA1 : Arrow arr1} `{HE1 : ArrowEq arr1}
  `{HA2 : Arrow arr2} `{HE2 : ArrowEq arr2}
  (F : forall A B, arr1 A B -> arr2 A B) := {
  morph_proper : forall A B,
    Proper (@arrow_eq arr1 HE1 A B ==> @arrow_eq arr2 HE2 A B) (F A B) ;
  morph_pure : forall {A B} (f : A -> B),
    arrow_eq (F A B (arr_pure f)) (arr_pure f) ;
  morph_comp : forall {A B C} (f : arr1 A B) (g : arr1 B C),
    arrow_eq (F A C (arr_comp f g)) (arr_comp (F A B f) (F B C g)) ;
  morph_first : forall {A B C} (f : arr1 A B),
    arrow_eq (F (A * C)%type (B * C)%type (arr_first f)) (arr_first (F A B f))
}.

Class ArrowApplyMorphism (arr1 arr2 : Type -> Type -> Type)
  `{HA1 : Arrow arr1} `{HAA1 : @ArrowApply arr1 HA1}
  `{HA2 : Arrow arr2} `{HAA2 : @ArrowApply arr2 HA2} `{HE2 : ArrowEq arr2}
  (F : forall A B, arr1 A B -> arr2 A B) := {
  morph_app : forall {A B},
    arrow_eq (F (arr1 A B * A)%type B arr_app)
             (arr_comp (arr_pure (fun p : arr1 A B * A => (F A B (fst p), snd p))) arr_app)
}.

Section ArrowMorphismDerived.

  Context {arr1 arr2 : Type -> Type -> Type}
          `{HA1 : Arrow arr1} `{HE1 : ArrowEq arr1}
          `{HA2 : Arrow arr2} `{HE2 : ArrowEq arr2} `{HL2 : @ArrowLaws arr2 HA2 HE2}
          (F : forall A B, arr1 A B -> arr2 A B)
          `{HF : @ArrowMorphism arr1 arr2 HA1 HE1 HA2 HE2 F}.

  Lemma morph_id {A} : arrow_eq (F A A arr_id) arr_id.
  Proof. apply morph_pure. Qed.

  Lemma morph_second {A B C} (f : arr1 A B) :
    arrow_eq (F (C * A)%type (C * B)%type (arr_second f)) (arr_second (F A B f)).
  Proof.
    unfold arr_second.
    etransitivity; [ apply morph_comp |].
    apply comp_proper; [ apply morph_pure |].
    etransitivity; [ apply morph_comp |].
    apply comp_proper; [ apply morph_first | apply morph_pure ].
  Qed.

  Lemma morph_split {A B C D} (f : arr1 A B) (g : arr1 C D) :
    arrow_eq (F (A * C)%type (B * D)%type (arr_split f g))
             (arr_split (F A B f) (F C D g)).
  Proof.
    unfold arr_split.
    etransitivity; [ apply morph_comp |].
    apply comp_proper; [ apply morph_first | apply morph_second ].
  Qed.

  Lemma morph_fanout {A B C} (f : arr1 A B) (g : arr1 A C) :
    arrow_eq (F A (B * C)%type (arr_fanout f g)) (arr_fanout (F A B f) (F A C g)).
  Proof.
    unfold arr_fanout.
    etransitivity; [ apply morph_comp |].
    apply comp_proper; [ apply morph_pure | apply morph_split ].
  Qed.

End ArrowMorphismDerived.
