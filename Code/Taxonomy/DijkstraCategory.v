(** * Generalizing the Dijkstra monad: specification *categories*.

    This file formalizes the intuition of the brief "Generalizing the
    Dijkstra Monad: from Specification Monads to Specification
    Categories".  The claim it makes precise is:

    >  A Dijkstra monad indexes computations by the *morphisms* of a
    >  [Pos]-enriched category of predicate transformers.  [return] is
    >  indexed by identities and [bind] by composition.  "Dijkstra
    >  Monads for All" is the special case where that category is
    >  *representable* — the Kleisli category of a specification monad.

    A **specification category** is defined here *from scratch* (it does
    not reuse the Hughes-style [Arrow] typeclasses of [Classes/Arrow.v]).
    It is a [Pos]-enriched category of predicate transformers, layered as:

    - [Category W]: the bare data — an identity morphism [cat_id] and a
      composition [cat_comp] on a hom-family [W A B];
    - [SpecCategory W]: on top of a [Category], a hom-setoid [cat_eq]
      (with the category laws holding up to it) and a refinement preorder
      [cat_le] that composition is monotone in and that [cat_eq] entails
      — the [Pos]-enrichment.

    The three axes the brief separates map to three independent pieces
    of structure:

    - *composability* = functoriality of [wp] (AK Thm 3.4 / Cartesian
      lifting): the hypotheses [wp_id], [wp_comp];
    - *order* (weakening / Hoare triples) = the fiber order [cat_le],
      used by [weakenD];
    - *representability* (specs as data) = the hom-family being the
      Kleisli arrows [A -> Wm B] of a monad [Wm]: the class
      [Representable], with [WPArr]/[PureWP] as the worked instance.

    Correspondence with DM4All, made precise below:

        specification monad  W        <->  specification category  W
        w : W A       (an element)    <->  w : W A B    (a morphism)
        ret^W                         <->  cat_id
        bind^W w1 w2                  <->  cat_comp w1 w2
        monadic laws of W             <->  category laws of W (id + assoc)

    The single substantive change (the brief's "de-familization") is
    that DM4All's second [bind] argument, a value-indexed family
    [(x : A) -> D B (w2 x)], becomes a single open computation indexed
    by one morphism [w2 : W B C]; [bind^D] becomes plain composition.
    In the representable case the family reappears (a Kleisli arrow
    [B -> Wm C] *is* such a family), recovering DM4All verbatim. *)

From Coq Require Import Morphisms RelationClasses ZArith Lia.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy Require Import Pred WP WPArr.

(* ================================================================= *)
(** ** 1. [Pos]-enriched specification category (from scratch)         *)
(* ================================================================= *)

(** The bare category: identity and composition on a hom-family.  No
    laws yet — this is the minimal data needed to say "morphisms" and
    is all that representability (section 4) refers to. *)
Class Category (W : Type -> Type -> Type) :=
{
  cat_id   : forall {A}, W A A ;
  cat_comp : forall {A B C}, W A B -> W B C -> W A C ;
}.

(** A [SpecCategory] enriches a [Category] with a hom-setoid [cat_eq]
    (up to which the category laws hold) and a refinement preorder
    [cat_le] (the [Pos]-enrichment): composition is monotone in it and
    the categorical equality entails it.

    Refinement convention: [cat_le w1 w2] reads "[w1] refines / is at
    least as strong as [w2]".  A Dijkstra element for [w] may be
    implemented by any computation whose [wp] refines [w]. *)
Class SpecCategory (W : Type -> Type -> Type) {CW : Category W} :=
{
  cat_eq : forall {A B}, W A B -> W A B -> Prop ;
  cat_le : forall {A B}, W A B -> W A B -> Prop ;

  cat_eq_equiv   :: forall A B, Equivalence (@cat_eq A B) ;
  cat_le_preorder :: forall A B, PreOrder (@cat_le A B) ;

  (** Category laws, up to the hom-setoid [cat_eq]. *)
  cat_comp_id_l : forall {A B} (f : W A B),
    cat_eq (cat_comp cat_id f) f ;
  cat_comp_id_r : forall {A B} (f : W A B),
    cat_eq (cat_comp f cat_id) f ;
  cat_comp_assoc : forall {A B C D} (f : W A B) (g : W B C) (h : W C D),
    cat_eq (cat_comp (cat_comp f g) h) (cat_comp f (cat_comp g h)) ;

  (** Composition respects the hom-setoid (congruence). *)
  cat_comp_proper :: forall A B C,
    Proper (cat_eq ==> cat_eq ==> cat_eq) (@cat_comp W CW A B C) ;

  (** The [Pos]-enrichment: composition is monotone in both arguments,
      and equality entails refinement (both ways, [cat_eq] being
      symmetric). *)
  cat_comp_mono : forall {A B C} (f f' : W A B) (g g' : W B C),
    cat_le f f' -> cat_le g g' -> cat_le (cat_comp f g) (cat_comp f' g') ;
  cat_eq_le : forall {A B} (f g : W A B), cat_eq f g -> cat_le f g ;
}.

(* ================================================================= *)
(** ** 2. The generalized Dijkstra monad over a spec category          *)
(* ================================================================= *)

(** Fix a computation monad [M] (with ExtLib/ITree monad laws up to
    [Eq1]) and a specification category [W], together with a *weakest
    precondition functor* [wp] mapping Kleisli arrows of [M] to
    morphisms of [W].

    The hypotheses [wp_id] and [wp_comp] say [wp] is a *strict* functor
    of categories: it sends identities to identities and composition to
    composition.  By AK Thm 3.4 this is equivalent to the underlying
    lifting being Cartesian, and it is exactly what licenses the typing
    of [bindD].  (A merely lax [wp] — inequalities in place of
    [cat_eq] — still yields a sound but non-functorial [D]; we take the
    Cartesian case.) *)

Section GeneralizedDijkstra.

  Context {M : Type -> Type}.
  Context {MM : Monad M} {EM : Eq1 M}.
  Context {EEM : @Eq1Equivalence M MM EM}.
  Context {MLM : @MonadLawsE M EM MM}.

  Context {W : Type -> Type -> Type}.
  Context {CW : Category W} {SC : @SpecCategory W CW}.

  (** The Kleisli category of the computation monad [M]. *)
  Definition kl (A B : Type) : Type := A -> M B.
  Definition kid {A} : kl A A := fun a => ret a.
  Definition kcomp {A B C} (f : kl A B) (g : kl B C) : kl A C :=
    fun a => bind (f a) g.
  Definition kl_eq {A B} (f g : kl A B) : Prop := forall a, eq1 (f a) (g a).

  Context (wp : forall A B, kl A B -> W A B).
  Arguments wp {A B} _.

  Hypothesis wp_id : forall A, cat_eq (wp (@kid A)) cat_id.
  Hypothesis wp_comp : forall A B C (f : kl A B) (g : kl B C),
    cat_eq (wp (kcomp f g)) (cat_comp (wp f) (wp g)).

  (** The generalized Dijkstra monad: computations refining a
      specification *morphism* [w] (target 4). *)
  Definition D (A B : Type) (w : W A B) : Type :=
    { c : kl A B | cat_le w (wp c) }.

  (** [ret^D] is indexed by the identity morphism [cat_id]. *)
  #[program] Definition retD {A} : D A A cat_id := kid.
  Next Obligation.
    apply cat_eq_le. symmetry. apply wp_id.
  Qed.

  (** [bind^D] is indexed by *composition* [cat_comp w1 w2].  Its
      second argument is a single open computation [D B C w2] indexed by
      one morphism — the de-familized bind. *)
  #[program] Definition bindD {A B C} {w1 : W A B} {w2 : W B C}
    (m : D A B w1) (f : D B C w2) : D A C (cat_comp w1 w2) :=
    kcomp (proj1_sig m) (proj1_sig f).
  Next Obligation.
    etransitivity.
    - apply cat_comp_mono; [ apply (proj2_sig m) | apply (proj2_sig f) ].
    - apply cat_eq_le. symmetry. apply wp_comp.
  Qed.

  (** Weakening: the fiber order lets us reindex a computation along a
      refinement.  This is the subtyping / consequence rule. *)
  #[program] Definition weakenD {A B} {w w' : W A B}
    (Hle : cat_le w w') (m : D A B w') : D A B w := proj1_sig m.
  Next Obligation.
    etransitivity; [ exact Hle | exact (proj2_sig m) ].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** The three monad laws (target 4)                             *)
  (* --------------------------------------------------------------- *)

  (** Two Dijkstra elements are compared on their *carriers* (both live
      in [kl A B]) up to the computation monad's equivalence [Eq1].
      Their indices may differ by [cat_eq] — see the index lemmas
      below.  This is the honest Coq rendering of "the laws hold up to
      the specification equations": the carrier component is [M]'s monad
      law, the index component is [W]'s category law. *)
  Definition D_eq {A B} {w w' : W A B} (m : D A B w) (n : D A B w') : Prop :=
    kl_eq (proj1_sig m) (proj1_sig n).

  (** Carrier equations: the three laws reduce to [M]'s [MonadLawsE]. *)

  Lemma D_left_id {A C} {w : W A C} (f : D A C w) :
    D_eq (bindD retD f) f.
  Proof. intro a. cbn. apply bind_ret_l. Qed.

  Lemma D_right_id {A B} {w : W A B} (m : D A B w) :
    D_eq (bindD m retD) m.
  Proof. intro a. cbn. apply bind_ret_r. Qed.

  Lemma D_assoc {A B C E}
    {w1 : W A B} {w2 : W B C} {w3 : W C E}
    (m : D A B w1) (f : D B C w2) (g : D C E w3) :
    D_eq (bindD (bindD m f) g) (bindD m (bindD f g)).
  Proof. intro a. cbn. apply bind_bind. Qed.

  (** Index equations: the same three laws, typed over [W]'s category
      laws.  These are literally the [SpecCategory] fields — DM4All's
      "monadic equations for W" become "identity + associativity of the
      category [W]". *)

  Lemma D_left_id_index {A C} (w : W A C) :
    cat_eq (cat_comp cat_id w) w.
  Proof. apply cat_comp_id_l. Qed.

  Lemma D_right_id_index {A B} (w : W A B) :
    cat_eq (cat_comp w cat_id) w.
  Proof. apply cat_comp_id_r. Qed.

  Lemma D_assoc_index {A B C E}
    (w1 : W A B) (w2 : W B C) (w3 : W C E) :
    cat_eq (cat_comp (cat_comp w1 w2) w3) (cat_comp w1 (cat_comp w2 w3)).
  Proof. apply cat_comp_assoc. Qed.

  (* --------------------------------------------------------------- *)
  (** *** The weakening (subtyping) laws                              *)
  (* --------------------------------------------------------------- *)

  (** [weakenD] never touches the underlying computation — the single
      fact behind DM4All's dm_law4, dm_law5 and dm_law6. *)
  Lemma D_weaken_carrier {A B} {w w' : W A B}
    (Hle : cat_le w w') (m : D A B w') :
    proj1_sig (weakenD Hle m) = proj1_sig m.
  Proof. reflexivity. Qed.

  (** dm_law4: weakening along [reflexivity] is the identity. *)
  Lemma D_weaken_refl {A B} {w : W A B} (m : D A B w) :
    D_eq (weakenD (reflexivity w) m) m.
  Proof. intro a. reflexivity. Qed.

  (** dm_law5: weakening composes along transitivity. *)
  Lemma D_weaken_trans {A B} {w1 w2 w3 : W A B}
    (H12 : cat_le w1 w2) (H23 : cat_le w2 w3) (m : D A B w3) :
    D_eq (weakenD (transitivity H12 H23) m)
         (weakenD H12 (weakenD H23 m)).
  Proof. intro a. reflexivity. Qed.

  (** dm_law6: weakening commutes with [bind].  [D] is a full
      [SpecCategory], so the composite index is weakened by the
      enrichment's own [cat_comp_mono] — unlike the [Dawlp] instance,
      whose raw [ProgWP] bind is not monotone, this needs no extra
      hypothesis. *)
  Lemma D_weaken_bind {A B C} {w1 w1' : W A B} {w2 w2' : W B C}
    (H1 : cat_le w1' w1) (H2 : cat_le w2' w2)
    (m : D A B w1) (f : D B C w2) :
    D_eq (weakenD (cat_comp_mono w1' w1 w2' w2 H1 H2) (bindD m f))
         (bindD (weakenD H1 m) (weakenD H2 f)).
  Proof. intro a. reflexivity. Qed.

End GeneralizedDijkstra.

(* ================================================================= *)
(** ** 3. An instance of a spec category: relations [Pred]             *)
(* ================================================================= *)

(** The relational / strongest-postcondition category [Pred A B =
    A -> B -> Prop]: identity is the equality relation, composition is
    relational composition, the hom-setoid is pointwise-iff [Pred_eq],
    the order is inclusion [Pred_le].  Relational composition is
    manifestly monotone under inclusion and respects iff, so [Pred] is a
    bona fide [Pos]-enriched spec category — defined here without any
    reference to arrows. *)

#[global]
Instance Category_Pred : Category Pred :=
{|
  cat_id   := fun A a b => a = b ;
  cat_comp := fun A B C f g a c => exists b, f a b /\ g b c ;
|}.

(** The category laws for [Pred], proved as standalone lemmas (they
    reference [cat_id]/[cat_comp] of [Category_Pred] and the relation
    orders [Pred_eq]/[Pred_le] directly). *)

Lemma Pred_comp_id_l {A B} (f : Pred A B) :
  Pred_eq (cat_comp cat_id f) f.
Proof.
  intros a c; cbn; split.
  - intros [b [Hb Hf]]; subst b; exact Hf.
  - intro Hf; exists a; split; [ reflexivity | exact Hf ].
Qed.

Lemma Pred_comp_id_r {A B} (f : Pred A B) :
  Pred_eq (cat_comp f cat_id) f.
Proof.
  intros a c; cbn; split.
  - intros [b [Hf Hb]]; subst b; exact Hf.
  - intro Hf; exists c; split; [ exact Hf | reflexivity ].
Qed.

Lemma Pred_comp_assoc {A B C E}
  (f : Pred A B) (g : Pred B C) (h : Pred C E) :
  Pred_eq (cat_comp (cat_comp f g) h) (cat_comp f (cat_comp g h)).
Proof.
  intros a e; cbn; split.
  - intros [c [[b [Hf Hg]] Hh]].
    exists b; split; [ exact Hf | exists c; split; [ exact Hg | exact Hh ] ].
  - intros [b [Hf [c [Hg Hh]]]].
    exists c; split; [ exists b; split; [ exact Hf | exact Hg ] | exact Hh ].
Qed.

Lemma Pred_comp_proper {A B C} :
  Proper (Pred_eq ==> Pred_eq ==> Pred_eq) (@cat_comp Pred _ A B C).
Proof.
  intros f f' Hf g g' Hg a c; cbn; split.
  - intros [b [H1 H2]]; exists b; split;
      [ apply (proj1 (Hf a b)); exact H1 | apply (proj1 (Hg b c)); exact H2 ].
  - intros [b [H1 H2]]; exists b; split;
      [ apply (proj2 (Hf a b)); exact H1 | apply (proj2 (Hg b c)); exact H2 ].
Qed.

Lemma Pred_comp_mono {A B C} (f f' : Pred A B) (g g' : Pred B C) :
  Pred_le f f' -> Pred_le g g' -> Pred_le (cat_comp f g) (cat_comp f' g').
Proof.
  intros Hf Hg a c H; cbn in H |- *. destruct H as [b [H1 H2]].
  exists b; split; [ apply Hf; exact H1 | apply Hg; exact H2 ].
Qed.

Lemma Pred_eq_le {A B} (f g : Pred A B) : Pred_eq f g -> Pred_le f g.
Proof. intros H a b Hf; exact (proj1 (H a b) Hf). Qed.

#[global]
Instance SpecCategory_Pred : SpecCategory Pred :=
{|
  cat_eq := @Pred_eq ;
  cat_le := @Pred_le ;
  cat_eq_equiv    := @Pred_eq_Equivalence ;
  cat_le_preorder := @Pred_le_PreOrder ;
  cat_comp_id_l   := @Pred_comp_id_l ;
  cat_comp_id_r   := @Pred_comp_id_r ;
  cat_comp_assoc  := @Pred_comp_assoc ;
  cat_comp_proper := @Pred_comp_proper ;
  cat_comp_mono   := @Pred_comp_mono ;
  cat_eq_le       := @Pred_eq_le ;
|}.

(* ================================================================= *)
(** ** 4. Representability: DM4All as the special case (target 5)      *)
(* ================================================================= *)

(** A spec category [W] is *representable* by a specification monad
    [Wm] when its hom-sets are the Kleisli arrows [A -> Wm B], with the
    categorical identity/composition given by [Wm]'s [ret]/[bind].
    Representability refers only to the bare [Category] data — this is
    exactly the content of "morphisms become elements, [cat_comp]
    becomes [bind^W], [cat_id] becomes [ret^W]", so a Dijkstra monad
    over a representable [W] *is* a DM4All Dijkstra monad over [Wm]. *)

Class Representable (W : Type -> Type -> Type) {CW : Category W}
      (Wm : Type -> Type) {MWm : Monad Wm} :=
{
  rep : forall {A B}, W A B -> (A -> Wm B) ;
  rep_id : forall A (a : A), rep (@cat_id W CW A) a = ret a ;
  rep_comp : forall A B C (f : W A B) (g : W B C) (a : A),
    rep (cat_comp f g) a = bind (rep f a) (fun b => rep g b) ;
}.

(** The worked instance: the DM4All pure specification monad
    [W_Pure = PureWP], whose Kleisli category is [WPArr] (defined in
    [Taxonomy/WPArr.v] as [WPArr A B := A -> PureWP B]).

    We give [WPArr] its category structure *directly*, as
    predicate-transformer composition — [cat_id a Q = Q a] and
    [cat_comp f g a Q = f a (fun b => g b Q)] — and then show it
    coincides with [PureWP]'s [ret]/[bind].  [rep] is the identity: a
    [WPArr] morphism already *is* a value-indexed family [A -> PureWP B]. *)

#[global]
Instance Category_WPArr : Category WPArr :=
{|
  cat_id   := fun A a Q => Q a ;
  cat_comp := fun A B C f g a Q => f a (fun b => g b Q) ;
|}.

#[global]
Instance Representable_WPArr : Representable WPArr PureWP :=
{|
  rep      := fun A B w => w ;
  rep_id   := fun A a => eq_refl ;
  rep_comp := fun A B C f g a => eq_refl ;
|}.

(** Made fully explicit: on [WPArr], the categorical identity is
    [PureWP]'s [ret] and categorical composition is [PureWP]'s Kleisli
    [bind].  Both hold by computation. *)

Corollary WPArr_id_recovers_ret {A} (a : A) :
  (@cat_id WPArr _ A) a = @ret PureWP _ _ a.
Proof. reflexivity. Qed.

Corollary WPArr_comp_recovers_bind {A B C}
  (f : WPArr A B) (g : WPArr B C) (a : A) :
  cat_comp f g a = bind (f a) g.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 5. Concrete regression test: state, single [Z] cell (target 7)  *)
(* ================================================================= *)

(** We verify the worked example of the brief: for the state monad over
    a single integer cell, [incr = bind get (fun x => put (x+1))] has
    weakest precondition [wp_incr post s0 = post ((), s0+1)], and the
    Hoare triple [{odd s0} incr {even (final)}] reduces to the tautology
    [odd s0 -> odd s0].

    The spec type used here is DM4All's [W_St]:

        StQ A = (A * Z -> Prop) -> (Z -> Prop)

    which is the representable state specification monad, isomorphic
    (by swapping the two curried arguments) to [stateT Z PureWP] — the
    recovery of [W_St] promised by section 4 above. *)

Section StateRegression.
  Local Open Scope Z_scope.

  Definition StQ (A : Type) : Type := (A * Z -> Prop) -> Z -> Prop.

  Definition ret_st {A} (a : A) : StQ A :=
    fun post s0 => post (a, s0).
  Definition bind_st {A B} (m : StQ A) (k : A -> StQ B) : StQ B :=
    fun post s0 => m (fun p => let '(x, s1) := p in k x post s1) s0.

  Definition wp_get : StQ Z :=
    fun post s0 => post (s0, s0).
  Definition wp_put (n : Z) : StQ unit :=
    fun post s0 => post (tt, n).

  Definition wp_incr : StQ unit :=
    bind_st wp_get (fun x => wp_put (x + 1)).

  (** The wp of [incr] computes to updating the cell by one. *)
  Lemma wp_incr_eval : forall post s0, wp_incr post s0 = post (tt, s0 + 1).
  Proof. reflexivity. Qed.

  (** Parity predicates and the arithmetic fact [even (s+1) <-> odd s]. *)
  Definition is_even (z : Z) : Prop := exists k, z = 2 * k.
  Definition is_odd  (z : Z) : Prop := exists k, z = 2 * k + 1.

  Lemma even_succ_iff_odd : forall z, is_even (z + 1) <-> is_odd z.
  Proof.
    intro z; split; intros [k Hk]; [ exists (k - 1) | exists (k + 1) ]; lia.
  Qed.

  (** A Hoare triple [{P} w {Q}] in the [StQ] spec: [P] entails the wp
      of [Q].  This is the DM4all refinement [P => wp(w, Q)]. *)
  Definition triple {A} (P : Z -> Prop) (w : StQ A) (Q : A * Z -> Prop) : Prop :=
    forall s0, P s0 -> w Q s0.

  (** {odd s0} incr {even (final state)} reduces to [odd s0 -> odd s0]. *)
  Lemma incr_triple_reduces :
    triple is_odd wp_incr (fun p => is_even (snd p))
    <-> (forall s0 : Z, is_odd s0 -> is_odd s0).
  Proof.
    unfold triple. split.
    - intros H s0 Hodd. specialize (H s0 Hodd). cbn in H.
      apply even_succ_iff_odd in H. exact H.
    - intros H s0 Hodd. specialize (H s0 Hodd). cbn.
      apply even_succ_iff_odd. exact H.
  Qed.

  (** ... and therefore the triple holds. *)
  Lemma incr_triple_holds :
    triple is_odd wp_incr (fun p => is_even (snd p)).
  Proof. apply incr_triple_reduces. auto. Qed.

End StateRegression.

(* ================================================================= *)
(** ** 6. On the non-example: sp-over-state (target 6)                 *)
(* ================================================================= *)

(** The motivating non-example is *strongest-postcondition transformers
    over state*: a specification structure that is a [Pos]-enriched
    category (each [sp(c, -)] is a term, composition is image-of-image)
    yet is **not** representable by a specification monad — witnessing
    the strict gap (weak "each spec is a term") ⊋ (strong "specs form a
    monad").

    We do not add a fresh formal counterexample here, because this
    project already contains the sharpest available formal obstruction
    of exactly this shape: the failure of the SPost <-> RelPrePost
    Galois connection in the *binary* setting, proved by counterexample
    in [Taxonomy/Galois.v] ("Obstruction" section,
    [gamma_uni_not_monotone] and the existential-variant remark).

    The obstruction there is the same variance mismatch the brief
    identifies: a strongest-postcondition transformer is the
    direct-image / opfibration direction ([Pred A B = A -> B -> Prop] is
    a *joint* relation over inputs and outputs), whereas closing the
    hom-family [A |-> {specs for A}] into a covariant specification
    monad [Wm] with [ret^Wm]/[bind^Wm] requires the *continuation*
    (backward, [wp]-style) direction.  Recovering the joint from the
    [B -> Prop] marginals that a covariant monad would expose is
    ill-posed without extra structure (independence), which is exactly
    why [gamma] fails to be monotone / the adjunction fails.

    Contrast with [SpecCategory_Pred] above: [Pred] *is* a spec
    category and, taken as [A -> SetM B], is even representable — the
    non-representability is specifically a *state* phenomenon (the [S]
    carrier threads through, and the covariant [W_St = StT (Cont_P)] is
    the [wp] direction, not the direct-image direction).  Formalizing
    the full state non-example is left as future work; the variance
    argument together with the existing binary Galois obstruction is
    the semi-formal justification the brief calls for. *)
