(** * Lightweight Galois connection between binary type constructors.

    A Galois connection between two binary type constructors [F] and [G],
    parameterised over their (preorder) inclusion relations.  Both
    relations are bundled as class indices so that two different Galois
    connections can co-exist for the same pair of types under different
    orderings.  In [Taxonomy/Galois.v] this flexibility is used to state
    connections involving local subtypes ([MonotoneWP],
    [HealthyRelPrePost], [MonotoneSPost]) whose orders are lifted from
    the global refinement orders on the raw types. *)

From Coq Require Import Relation_Definitions RelationClasses Morphisms.

Class Galois
    (F G : Type -> Type -> Type)
    (le_F : forall A B, relation (F A B))
    (le_G : forall A B, relation (G A B)) :=
{
  galois_alpha : forall {A B}, G A B -> F A B ;
  galois_gamma : forall {A B}, F A B -> G A B ;
  galois_preorder_F :: forall A B, PreOrder (le_F A B) ;
  galois_preorder_G :: forall A B, PreOrder (le_G A B) ;
  galois_adjunction : forall {A B} (g : G A B) (f : F A B),
    le_F A B (galois_alpha g) f <-> le_G A B g (galois_gamma f)
}.

(* ================================================================= *)
(** ** Derived lemmas                                                 *)
(* ================================================================= *)

Section GaloisLemmas.
  Context {F G : Type -> Type -> Type}.
  Context {le_F : forall A B, relation (F A B)}.
  Context {le_G : forall A B, relation (G A B)}.
  Context `{Galois F G le_F le_G}.

  Lemma galois_alpha_gamma_deflation {A B} (f : F A B) :
    le_F A B (galois_alpha (galois_gamma f)) f.
  Proof. apply galois_adjunction. reflexivity. Qed.

  Lemma galois_gamma_alpha_inflation {A B} (g : G A B) :
    le_G A B g (galois_gamma (galois_alpha g)).
  Proof. apply galois_adjunction. reflexivity. Qed.

  Lemma galois_alpha_monotone {A B} (g1 g2 : G A B) :
    le_G A B g1 g2 ->
    le_F A B (galois_alpha g1) (galois_alpha g2).
  Proof.
    intros Hle. apply galois_adjunction.
    transitivity g2; [exact Hle | apply galois_gamma_alpha_inflation].
  Qed.

  Lemma galois_gamma_monotone {A B} (f1 f2 : F A B) :
    le_F A B f1 f2 ->
    le_G A B (galois_gamma f1) (galois_gamma f2).
  Proof.
    intros Hle. apply galois_adjunction.
    transitivity f1; [apply galois_alpha_gamma_deflation | exact Hle].
  Qed.

End GaloisLemmas.
