(** * Monotone PrePost operations and the relation-inclusion embedding.

    [PrePostArr.v] develops the arrow laws under the pointwise-iff
    equality; this file adds the order facts. Under the Hoare order
    [PrePost_le] (stronger pre, weaker post), the exact arrow
    operations are jointly monotone:

    - [arr_comp] in both factors;
    - [arr_first];
    - [arr_left];
    - the exact generic arrow-derived bind [bind_arrow] of
      [ArrowMonad.v] in both arguments.  The bind proof unfolds the
      generic construction directly; it depends neither on the compact
      test formulas nor on any module under [Tests/].

    Through the [(True, R)] embedding [rel_to_pp] of [GaloisArr.v],
    relation inclusion is exactly [PrePost_le]: [Rel_le R S] iff
    [PrePost_le (rel_to_pp R) (rel_to_pp S)].  A generic extraction
    lemma turns this into short corollaries for the four
    relation-inclusion orders of [SPRelationOrder.v] — on [DSPStExc],
    [ASLPStExc], [StDSP.DSPSt], and [StASLP.ASLPSt]: ordering two
    well-formed specifications by inclusion of their extracted
    relations is the same as comparing their embedded [(True, R)]
    images under [PrePost_le].

    Caveat.  This embedding orders relations, not judgments: as
    recorded in [SPRelationOrder.v], relation inclusion does not
    preserve DSP/ASLP judgments at arbitrary preconditions. *)

From Incorrectness.Classes Require Import Arrow ArrowMonad.
From Incorrectness.Taxonomy.Arrows Require Import Rel PrePostArr GaloisArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  DSPMonad ASLPMonad SPRelationOrder.

(* ================================================================= *)
(** ** Operation monotonicity under [PrePost_le]                      *)
(* ================================================================= *)

Lemma PrePost_le_refl {A B} (pq : PrePostArr A B) : PrePost_le pq pq.
Proof. split; intros; assumption. Qed.

(** Composition is jointly monotone: the Hoare conjunction on
    preconditions and the relational join on postconditions both
    transport the two factor inclusions. *)
Lemma arr_comp_PrePost_le {A B C}
  (f1 f2 : PrePostArr A B) (g1 g2 : PrePostArr B C) :
  PrePost_le f1 f2 -> PrePost_le g1 g2 ->
  PrePost_le (@arr_comp PrePostArr Arrow_PrePost A B C f1 g1)
             (@arr_comp PrePostArr Arrow_PrePost A B C f2 g2).
Proof.
  intros Hf Hg. split.
  - intros a [Hf2 Hg2]. split.
    + exact (proj1 Hf a Hf2).
    + intros b Hb. exact (proj1 Hg b (Hg2 b (proj2 Hf a b Hb))).
  - intros a c [b [H1 H2]]. exists b. split.
    + exact (proj2 Hf a b H1).
    + exact (proj2 Hg b c H2).
Qed.

(** [first] is monotone: it only forwards the source inclusion at the
    first projection and copies the second. *)
Lemma arr_first_PrePost_le {A B C} (f g : PrePostArr A B) :
  PrePost_le f g ->
  PrePost_le (@arr_first PrePostArr Arrow_PrePost A B C f)
             (@arr_first PrePostArr Arrow_PrePost A B C g).
Proof.
  intros H. split.
  - intros [a c]. exact (proj1 H a).
  - intros [a c] [b c'] [Hf Heq]. split.
    + exact (proj2 H a b Hf).
    + exact Heq.
Qed.

(** [left] is monotone: the injected summand transports the source
    inclusion and the right summand is the identity relation. *)
Lemma arr_left_PrePost_le {A B C} (f g : PrePostArr A B) :
  PrePost_le f g ->
  PrePost_le (@arr_left PrePostArr Arrow_PrePost ArrowChoice_PrePost A B C f)
             (@arr_left PrePostArr Arrow_PrePost ArrowChoice_PrePost A B C g).
Proof.
  intros H. split.
  - intros [a|c].
    + exact (proj1 H a).
    + intros _. exact I.
  - intros [a|c] [b|c'].
    + intros Hf. exact (proj2 H a b Hf).
    + intros [].
    + intros [].
    + intros Heq. exact Heq.
Qed.

(** The fanout-with-identity head of the generic bind is monotone
    because it is a pure diagonal followed by [first] and an unchanged
    [arr_second arr_id]. *)
Lemma arr_fanout_id_PrePost_le {I X} (m n : PrePostArr I X) :
  PrePost_le m n ->
  PrePost_le (@arr_fanout PrePostArr Arrow_PrePost I X I m
                 (@arr_id PrePostArr Arrow_PrePost I))
             (@arr_fanout PrePostArr Arrow_PrePost I X I n
                 (@arr_id PrePostArr Arrow_PrePost I)).
Proof.
  intros H. unfold arr_fanout, arr_split.
  apply arr_comp_PrePost_le.
  - apply PrePost_le_refl.
  - apply arr_comp_PrePost_le.
    + apply arr_first_PrePost_le, H.
    + apply PrePost_le_refl.
Qed.

(** The application tail of the generic bind, with the pure selector
    carrying [k] on the left and [l] on the right, is monotone when the
    continuations are.  This is the pointwise computation obtained by
    unfolding the exact composition; no compact bind formula is
    introduced. *)
Lemma arr_comp_pure_pick_app_PrePost_le {I X Y}
  (k l : X -> PrePostArr I Y) :
  (forall a, PrePost_le (k a) (l a)) ->
  PrePost_le (@arr_comp PrePostArr Arrow_PrePost (X * I)%type
                (PrePostArr I Y * I)%type Y
                (@arr_pure PrePostArr Arrow_PrePost (X * I)%type
                   (PrePostArr I Y * I)%type (fun '(a, i) => (k a, i)))
                (@arr_app PrePostArr Arrow_PrePost ArrowApply_PrePost I Y))
             (@arr_comp PrePostArr Arrow_PrePost (X * I)%type
                (PrePostArr I Y * I)%type Y
                (@arr_pure PrePostArr Arrow_PrePost (X * I)%type
                   (PrePostArr I Y * I)%type (fun '(a, i) => (l a, i)))
                (@arr_app PrePostArr Arrow_PrePost ArrowApply_PrePost I Y)).
Proof.
  intros Hk.
  split.
  - intros p Hpre. destruct p as [a i]. cbn in Hpre.
    split; [reflexivity |].
    intros q Hq. rewrite <- Hq.
    exact (proj1 (Hk a) i (proj2 Hpre (l a, i) eq_refl)).
  - intros p c Hpost. destruct p as [a i]. cbn in Hpost.
    destruct Hpost as [q [Hq Hpost]].
    exists (l a, i). split.
    + reflexivity.
    + rewrite <- Hq in Hpost.
      exact (proj2 (Hk a) i c Hpost).
Qed.

(** The exact generic arrow-derived bind is jointly monotone under
    [PrePost_le]: in the computation, only the [first] head and the
    pure continuation selector change between the two sides. *)
Lemma bind_arrow_PrePost_le {I X Y}
  (m n : PrePostArr I X) (k l : X -> PrePostArr I Y) :
  PrePost_le m n ->
  (forall a, PrePost_le (k a) (l a)) ->
  PrePost_le (@bind_arrow PrePostArr Arrow_PrePost ArrowApply_PrePost I X Y m k)
             (@bind_arrow PrePostArr Arrow_PrePost ArrowApply_PrePost I X Y n l).
Proof.
  intros Hm Hk. unfold bind_arrow.
  apply arr_comp_PrePost_le.
  - apply arr_fanout_id_PrePost_le, Hm.
  - exact (arr_comp_pure_pick_app_PrePost_le k l Hk).
Qed.

(* ================================================================= *)
(** ** Relation inclusion as [PrePost_le] after the [(True, R)] map   *)
(* ================================================================= *)

(** Relation inclusion is exactly the [PrePost_le] comparison of the
    images under [rel_to_pp]: with a trivially-true precondition the
    contravariant clause dissolves and only [R ⊆ S] remains. *)
Lemma rel_le_rel_to_pp {A B} (R S : Rel A B) :
  Rel_le R S <-> PrePost_le (rel_to_pp R) (rel_to_pp S).
Proof.
  split; intros H.
  - exact (proj2 (adjunction_Rel_PrePost R (rel_to_pp S)) H).
  - exact (proj1 (adjunction_Rel_PrePost R (rel_to_pp S)) H).
Qed.

(** Generic form: any order defined by inclusion of an extracted
    relation [rho] embeds into [PrePost_le] through [rel_to_pp]. *)
Lemma extracted_rel_incl_PrePost_le {X Y C} (rho : C -> Rel X Y)
  (m n : C) :
  (forall x y, rho m x y -> rho n x y) <->
  PrePost_le (rel_to_pp (rho m)) (rel_to_pp (rho n)).
Proof. exact (rel_le_rel_to_pp (rho m) (rho n)). Qed.

(** ** The four SP relation-inclusion orders of [SPRelationOrder.v]  *)

Corollary ordDSPStExcRel_rel_to_pp {S A} (m n : DSPStExc S A) :
  ordDSPStExcRel m n <->
  PrePost_le (rel_to_pp (dspStExcRel m)) (rel_to_pp (dspStExcRel n)).
Proof. exact (@extracted_rel_incl_PrePost_le S (option (A * S))
                (DSPStExc S A) dspStExcRel m n). Qed.

Corollary ordASLPStExcRel_rel_to_pp {S A} (m n : ASLPStExc S A) :
  ordASLPStExcRel m n <->
  PrePost_le (rel_to_pp (aslpStExcRel m)) (rel_to_pp (aslpStExcRel n)).
Proof. exact (@extracted_rel_incl_PrePost_le S (option (A * S))
                (ASLPStExc S A) aslpStExcRel m n). Qed.

Corollary ordDSPStRel_rel_to_pp {S A} (m n : StDSP.DSPSt S A) :
  ordDSPStRel m n <->
  PrePost_le (rel_to_pp (dspStRel m)) (rel_to_pp (dspStRel n)).
Proof. exact (@extracted_rel_incl_PrePost_le S (A * S)
                (StDSP.DSPSt S A) dspStRel m n). Qed.

Corollary ordASLPStRel_rel_to_pp {S A} (m n : StASLP.ASLPSt S A) :
  ordASLPStRel m n <->
  PrePost_le (rel_to_pp (aslpStRel m)) (rel_to_pp (aslpStRel n)).
Proof. exact (@extracted_rel_incl_PrePost_le S (A * S)
                (StASLP.ASLPSt S A) aslpStRel m n). Qed.
