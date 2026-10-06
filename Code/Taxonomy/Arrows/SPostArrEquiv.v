(** * Equivalence of property-only and relational SP arrows.

    The conversions are the recovered relations [ASP_rel] / [DSLP_rel] and
    the relation constructors [relASP] / [relDSLP] from [SPostArr.v]; the
    arrow value on the relational side is the existing [Rel] carrier.  The
    round trips preserve each transformer reading exactly, and all five
    operations: pure, composition, first, choice ([left]), and application.
    Application preservation also converts the arrow stored in the input.

    The generic machinery imported from [Classes/ArrowMorphism.v] lifts
    these laws through the existing option and state transformers.  The
    [ArrowMorphism] API uses the selected equalities [Rel_eq] and pointwise
    transformer equivalence, including properness of both maps. *)

From Coq Require Import Morphisms.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Classes Require Export ArrowMorphism.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPostArr OptionLoop SPostArr.

Module PropertySP := SPostArr.
Module RelSP := RelSPostArr.

(** ** Transformer-preserving round trips *)

Theorem asp_from_to {A B} (f : PropertySP.PureASPostArr A B) :
  @arrow_eq _ PropertySP.ArrowEq_PureASPostArr A B
    (relASP (PropertySP.ASP_rel f)) f.
Proof. apply PropertySP.arrow_eq_relASP_ASP_rel. Qed.

Theorem asp_to_from {A B} (R : Rel A B) :
  Rel_eq (@PropertySP.ASP_rel A B (relASP R)) R.
Proof. intros a b. apply PropertySP.ASP_rel_relASP. Qed.

Theorem dslp_from_to {A B} (f : PropertySP.PureDSLPostArr A B) :
  @arrow_eq _ PropertySP.ArrowEq_PureDSLPostArr A B
    (relDSLP (PropertySP.DSLP_rel f)) f.
Proof. apply PropertySP.arrow_eq_relDSLP_DSLP_rel. Qed.

Theorem dslp_to_from {A B} (R : Rel A B) :
  Rel_eq (@PropertySP.DSLP_rel A B (relDSLP R)) R.
Proof. intros a b. apply PropertySP.DSLP_rel_relDSLP. Qed.

(** ** Transformer readings agree on both sides *)

Theorem asp_from_rel_reading {A B} (R : Rel A B) P b :
  PropertySP.getASP (relASP R) P b <-> RelSP.asp R P b.
Proof. apply PropertySP.getASP_relASP. Qed.

Theorem asp_to_rel_reading {A B} (f : PropertySP.PureASPostArr A B) P b :
  RelSP.asp (PropertySP.ASP_rel f) P b <-> PropertySP.getASP f P b.
Proof. rewrite PropertySP.ASP_normal_form. reflexivity. Qed.

Theorem dslp_from_rel_reading {A B} (R : Rel A B) P b :
  PropertySP.getDSLP (relDSLP R) P b <-> RelSP.dslp R P b.
Proof. apply PropertySP.getDSLP_relDSLP. Qed.

Theorem dslp_to_rel_reading {A B} (f : PropertySP.PureDSLPostArr A B) P b :
  RelSP.dslp (PropertySP.DSLP_rel f) P b <-> PropertySP.getDSLP f P b.
Proof. rewrite PropertySP.DSLP_normal_form. reflexivity. Qed.

(** ** Base operation preservation *)

Theorem asp_to_rel_pure {A B} (h : A -> B) :
  Rel_eq (@PropertySP.ASP_rel A B (PropertySP.arrASP h))
    (@arr_pure Rel Arrow_Rel A B h).
Proof. intros a b. apply PropertySP.ASP_rel_pure. Qed.

Theorem asp_to_rel_comp {A B C}
  (f : PropertySP.PureASPostArr A B) (g : PropertySP.PureASPostArr B C) :
  Rel_eq (@PropertySP.ASP_rel A C (PropertySP.compASP f g))
    (@arr_comp Rel Arrow_Rel A B C (PropertySP.ASP_rel f) (PropertySP.ASP_rel g)).
Proof. intros a c. apply PropertySP.ASP_rel_comp. Qed.

Theorem asp_to_rel_first {A B C} (f : PropertySP.PureASPostArr A B) :
  Rel_eq (@PropertySP.ASP_rel (A * C)%type (B * C)%type (PropertySP.firstASP f))
    (@arr_first Rel Arrow_Rel A B C (PropertySP.ASP_rel f)).
Proof.
  intros [a c] [b d]. apply PropertySP.ASP_rel_first.
Qed.

Theorem asp_to_rel_left {A B C} (f : PropertySP.PureASPostArr A B) :
  Rel_eq (@PropertySP.ASP_rel (A + C)%type (B + C)%type (PropertySP.leftASP f))
    (@arr_left Rel Arrow_Rel ArrowChoice_Rel A B C (PropertySP.ASP_rel f)).
Proof. intros x y. apply PropertySP.ASP_rel_left. Qed.

Theorem asp_to_rel_app {A B} :
  Rel_eq (@PropertySP.ASP_rel (PropertySP.PureASPostArr A B * A)%type B
    (@arr_app PropertySP.PureASPostArr PropertySP.Arrow_PureASPostArr
       PropertySP.ArrowApply_PureASPostArr A B))
  (@arr_comp Rel Arrow_Rel
    (PropertySP.PureASPostArr A B * A)%type
    (Rel A B * A)%type B
    (@arr_pure Rel Arrow_Rel
      (PropertySP.PureASPostArr A B * A)%type
      (Rel A B * A)%type
      (fun '(f, a) => (PropertySP.ASP_rel f, a)))
    (@arr_app Rel Arrow_Rel ArrowApply_Rel A B)).
Proof.
  intros [f a] b.
  rewrite PropertySP.ASP_rel_app. unfold Arrow_Rel; cbn.
  split.
  - intros H. exists (PropertySP.ASP_rel f, a).
    split; [reflexivity | exact H].
  - intros [y [Heq H]]. subst y. exact H.
Qed.

Theorem dslp_to_rel_pure {A B} (h : A -> B) :
  Rel_eq (@PropertySP.DSLP_rel A B (PropertySP.arrDSLP h))
    (@arr_pure Rel Arrow_Rel A B h).
Proof. intros a b. apply PropertySP.DSLP_rel_pure. Qed.

Theorem dslp_to_rel_comp {A B C}
  (f : PropertySP.PureDSLPostArr A B) (g : PropertySP.PureDSLPostArr B C) :
  Rel_eq (@PropertySP.DSLP_rel A C (PropertySP.compDSLP f g))
    (@arr_comp Rel Arrow_Rel A B C (PropertySP.DSLP_rel f) (PropertySP.DSLP_rel g)).
Proof. intros a c. apply PropertySP.DSLP_rel_comp. Qed.

Theorem dslp_to_rel_first {A B C} (f : PropertySP.PureDSLPostArr A B) :
  Rel_eq (@PropertySP.DSLP_rel (A * C)%type (B * C)%type (PropertySP.firstDSLP f))
    (@arr_first Rel Arrow_Rel A B C (PropertySP.DSLP_rel f)).
Proof.
  intros [a c] [b d]. apply PropertySP.DSLP_rel_first.
Qed.

Theorem dslp_to_rel_left {A B C} (f : PropertySP.PureDSLPostArr A B) :
  Rel_eq (@PropertySP.DSLP_rel (A + C)%type (B + C)%type (PropertySP.leftDSLP f))
    (@arr_left Rel Arrow_Rel ArrowChoice_Rel A B C (PropertySP.DSLP_rel f)).
Proof. intros x y. apply PropertySP.DSLP_rel_left. Qed.

Theorem dslp_to_rel_app {A B} :
  Rel_eq (@PropertySP.DSLP_rel (PropertySP.PureDSLPostArr A B * A)%type B
    (@arr_app PropertySP.PureDSLPostArr PropertySP.Arrow_PureDSLPostArr
       PropertySP.ArrowApply_PureDSLPostArr A B))
  (@arr_comp Rel Arrow_Rel
    (PropertySP.PureDSLPostArr A B * A)%type
    (Rel A B * A)%type B
    (@arr_pure Rel Arrow_Rel
      (PropertySP.PureDSLPostArr A B * A)%type
      (Rel A B * A)%type
      (fun '(f, a) => (PropertySP.DSLP_rel f, a)))
    (@arr_app Rel Arrow_Rel ArrowApply_Rel A B)).
Proof.
  intros [f a] b.
  rewrite PropertySP.DSLP_rel_app. unfold Arrow_Rel; cbn.
  split.
  - intros H. exists (PropertySP.DSLP_rel f, a).
    split; [reflexivity | exact H].
  - intros [y [Heq H]]. subst y. exact H.
Qed.

(** ** Base morphisms *)

Lemma asp_from_rel_proper A B :
  Proper (Rel_eq ==> @arrow_eq _ PropertySP.ArrowEq_PureASPostArr A B)
    (@relASP A B).
Proof.
  intros R T H. apply PropertySP.ASP_arrow_eq_rel. intros a b.
  rewrite !PropertySP.ASP_rel_relASP. apply H.
Qed.

Lemma dslp_from_rel_proper A B :
  Proper (Rel_eq ==> @arrow_eq _ PropertySP.ArrowEq_PureDSLPostArr A B)
    (@relDSLP A B).
Proof.
  intros R T H. apply PropertySP.DSLP_arrow_eq_rel. intros a b.
  rewrite !PropertySP.DSLP_rel_relDSLP. apply H.
Qed.

Theorem asp_to_rel_morphism :
  ArrowMorphism PropertySP.Arrow_PureASPostArr
    PropertySP.ArrowChoice_PureASPostArr PropertySP.ArrowApply_PureASPostArr
    PropertySP.ArrowEq_PureASPostArr
    Arrow_Rel ArrowChoice_Rel ArrowApply_Rel ArrowEq_Rel (@PropertySP.ASP_rel).
Proof.
  constructor.
  - intros A B f g H. exact (proj1 (PropertySP.ASP_arrow_eq_rel f g) H).
  - exact @asp_to_rel_pure.
  - exact @asp_to_rel_comp.
  - exact @asp_to_rel_first.
  - exact @asp_to_rel_left.
  - exact @asp_to_rel_app.
Qed.

Theorem asp_from_rel_morphism :
  ArrowMorphism Arrow_Rel ArrowChoice_Rel ArrowApply_Rel ArrowEq_Rel
    PropertySP.Arrow_PureASPostArr PropertySP.ArrowChoice_PureASPostArr
    PropertySP.ArrowApply_PureASPostArr PropertySP.ArrowEq_PureASPostArr (@relASP).
Proof.
  exact (inverse_morphism (@PropertySP.ASP_rel) (@relASP)
    asp_from_rel_proper (@asp_from_to) (@asp_to_from) asp_to_rel_morphism
    ArrowLaws_Rel ArrowChoiceLaws_Rel ArrowApplyLaws_Rel).
Qed.

Theorem dslp_to_rel_morphism :
  ArrowMorphism PropertySP.Arrow_PureDSLPostArr
    PropertySP.ArrowChoice_PureDSLPostArr PropertySP.ArrowApply_PureDSLPostArr
    PropertySP.ArrowEq_PureDSLPostArr
    Arrow_Rel ArrowChoice_Rel ArrowApply_Rel ArrowEq_Rel (@PropertySP.DSLP_rel).
Proof.
  constructor.
  - intros A B f g H. exact (proj1 (PropertySP.DSLP_arrow_eq_rel f g) H).
  - exact @dslp_to_rel_pure.
  - exact @dslp_to_rel_comp.
  - exact @dslp_to_rel_first.
  - exact @dslp_to_rel_left.
  - exact @dslp_to_rel_app.
Qed.

Theorem dslp_from_rel_morphism :
  ArrowMorphism Arrow_Rel ArrowChoice_Rel ArrowApply_Rel ArrowEq_Rel
    PropertySP.Arrow_PureDSLPostArr PropertySP.ArrowChoice_PureDSLPostArr
    PropertySP.ArrowApply_PureDSLPostArr PropertySP.ArrowEq_PureDSLPostArr (@relDSLP).
Proof.
  exact (inverse_morphism (@PropertySP.DSLP_rel) (@relDSLP)
    dslp_from_rel_proper (@dslp_from_to) (@dslp_to_from) dslp_to_rel_morphism
    ArrowLaws_Rel ArrowChoiceLaws_Rel ArrowApplyLaws_Rel).
Qed.

(** ** Public option and state-over-option equivalences

    Each [_morphism] theorem exposes all five laws through
    [morphism_pure], [morphism_comp], [morphism_first], [morphism_left],
    and [morphism_app], in either conversion direction.  State-only lifts
    are obtained directly with [state_arrow_map] and [state_arrow_morphism]. *)

Definition option_asp_to_rel {A B} (f : PropertySP.optionASPArr A B) :
  optionRel A B := option_arrow_map (@PropertySP.ASP_rel) A B f.
Definition option_asp_from_rel {A B} (f : optionRel A B) :
  PropertySP.optionASPArr A B := option_arrow_map (@relASP) A B f.
Definition option_dslp_to_rel {A B} (f : PropertySP.optionDSLPArr A B) :
  optionRel A B := option_arrow_map (@PropertySP.DSLP_rel) A B f.
Definition option_dslp_from_rel {A B} (f : optionRel A B) :
  PropertySP.optionDSLPArr A B := option_arrow_map (@relDSLP) A B f.

Definition state_option_asp_to_rel {S A B}
  (f : stateArrT S PropertySP.optionASPArr A B) :
  stateArrT S optionRel A B :=
  state_arrow_map S (@option_asp_to_rel) A B f.
Definition state_option_asp_from_rel {S A B}
  (f : stateArrT S optionRel A B) :
  stateArrT S PropertySP.optionASPArr A B :=
  state_arrow_map S (@option_asp_from_rel) A B f.
Definition state_option_dslp_to_rel {S A B}
  (f : stateArrT S PropertySP.optionDSLPArr A B) :
  stateArrT S optionRel A B :=
  state_arrow_map S (@option_dslp_to_rel) A B f.
Definition state_option_dslp_from_rel {S A B}
  (f : stateArrT S optionRel A B) :
  stateArrT S PropertySP.optionDSLPArr A B :=
  state_arrow_map S (@option_dslp_from_rel) A B f.

Theorem option_asp_from_to {A B} (f : PropertySP.optionASPArr A B) :
  @arrow_eq _ PropertySP.ArrowEq_optionASPArr A B
    (option_asp_from_rel (option_asp_to_rel f)) f.
Proof.
  exact (@option_arrow_map_roundtrip _ _ PropertySP.ArrowEq_PureASPostArr
    (@PropertySP.ASP_rel) (@relASP)
    (@asp_from_to) A B f).
Qed.

Theorem option_asp_to_from {A B} (f : optionRel A B) :
  Rel_eq (option_asp_to_rel (option_asp_from_rel f)) f.
Proof.
  exact (@option_arrow_map_roundtrip _ _ ArrowEq_Rel (@relASP) (@PropertySP.ASP_rel)
    (@asp_to_from) A B f).
Qed.

Theorem option_dslp_from_to {A B} (f : PropertySP.optionDSLPArr A B) :
  @arrow_eq _ PropertySP.ArrowEq_optionDSLPArr A B
    (option_dslp_from_rel (option_dslp_to_rel f)) f.
Proof.
  exact (@option_arrow_map_roundtrip _ _ PropertySP.ArrowEq_PureDSLPostArr
    (@PropertySP.DSLP_rel) (@relDSLP)
    (@dslp_from_to) A B f).
Qed.

Theorem option_dslp_to_from {A B} (f : optionRel A B) :
  Rel_eq (option_dslp_to_rel (option_dslp_from_rel f)) f.
Proof.
  exact (@option_arrow_map_roundtrip _ _ ArrowEq_Rel (@relDSLP) (@PropertySP.DSLP_rel)
    (@dslp_to_from) A B f).
Qed.

Theorem state_option_asp_from_to {S A B}
  (f : stateArrT S PropertySP.optionASPArr A B) :
  @arrow_eq _ (PropertySP.ArrowEq_stateOptASP S) A B
    (state_option_asp_from_rel (state_option_asp_to_rel f)) f.
Proof.
  exact (@state_arrow_map_roundtrip S _ _ PropertySP.ArrowEq_optionASPArr
    (@option_asp_to_rel) (@option_asp_from_rel)
    (@option_asp_from_to) A B f).
Qed.

Theorem state_option_asp_to_from {S A B}
  (f : stateArrT S optionRel A B) :
  Rel_eq (state_option_asp_to_rel (state_option_asp_from_rel f)) f.
Proof.
  exact (@state_arrow_map_roundtrip S _ _ (@ArrowEq_optionArrT Rel ArrowEq_Rel)
    (@option_asp_from_rel) (@option_asp_to_rel)
    (@option_asp_to_from) A B f).
Qed.

Theorem state_option_dslp_from_to {S A B}
  (f : stateArrT S PropertySP.optionDSLPArr A B) :
  @arrow_eq _ (PropertySP.ArrowEq_stateOptDSLP S) A B
    (state_option_dslp_from_rel (state_option_dslp_to_rel f)) f.
Proof.
  exact (@state_arrow_map_roundtrip S _ _ PropertySP.ArrowEq_optionDSLPArr
    (@option_dslp_to_rel) (@option_dslp_from_rel)
    (@option_dslp_from_to) A B f).
Qed.

Theorem state_option_dslp_to_from {S A B}
  (f : stateArrT S optionRel A B) :
  Rel_eq (state_option_dslp_to_rel (state_option_dslp_from_rel f)) f.
Proof.
  exact (@state_arrow_map_roundtrip S _ _ (@ArrowEq_optionArrT Rel ArrowEq_Rel)
    (@option_dslp_from_rel) (@option_dslp_to_rel)
    (@option_dslp_to_from) A B f).
Qed.

Local Notation ROA := (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel).
Local Notation ROAC := (@ArrowChoice_optionArrT Rel Arrow_Rel ArrowChoice_Rel).
Local Notation ROAA := (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel
  ArrowApply_Rel).
Local Notation ROE := (@ArrowEq_optionArrT Rel ArrowEq_Rel).
Local Notation RSE S := (@ArrowEq_stateArrT S optionRel ROE).

Theorem option_asp_to_rel_morphism :
  ArrowMorphism PropertySP.Arrow_optionASPArr PropertySP.ArrowChoice_optionASPArr
    PropertySP.ArrowApply_optionASPArr PropertySP.ArrowEq_optionASPArr
    ROA ROAC ROAA ROE (@option_asp_to_rel).
Proof.
  exact (option_arrow_morphism (@PropertySP.ASP_rel) asp_to_rel_morphism
    ArrowLaws_Rel ArrowChoiceLaws_Rel).
Qed.

Theorem option_asp_from_rel_morphism :
  ArrowMorphism ROA ROAC ROAA ROE PropertySP.Arrow_optionASPArr
    PropertySP.ArrowChoice_optionASPArr PropertySP.ArrowApply_optionASPArr
    PropertySP.ArrowEq_optionASPArr (@option_asp_from_rel).
Proof.
  exact (option_arrow_morphism (@relASP) asp_from_rel_morphism
    PropertySP.ArrowLaws_PureASPostArr
    PropertySP.ArrowChoiceLaws_PureASPostArr).
Qed.

Theorem option_dslp_to_rel_morphism :
  ArrowMorphism PropertySP.Arrow_optionDSLPArr PropertySP.ArrowChoice_optionDSLPArr
    PropertySP.ArrowApply_optionDSLPArr PropertySP.ArrowEq_optionDSLPArr
    ROA ROAC ROAA ROE (@option_dslp_to_rel).
Proof.
  exact (option_arrow_morphism (@PropertySP.DSLP_rel) dslp_to_rel_morphism
    ArrowLaws_Rel ArrowChoiceLaws_Rel).
Qed.

Theorem option_dslp_from_rel_morphism :
  ArrowMorphism ROA ROAC ROAA ROE PropertySP.Arrow_optionDSLPArr
    PropertySP.ArrowChoice_optionDSLPArr PropertySP.ArrowApply_optionDSLPArr
    PropertySP.ArrowEq_optionDSLPArr (@option_dslp_from_rel).
Proof.
  exact (option_arrow_morphism (@relDSLP) dslp_from_rel_morphism
    PropertySP.ArrowLaws_PureDSLPostArr
    PropertySP.ArrowChoiceLaws_PureDSLPostArr).
Qed.

Theorem state_option_asp_to_rel_morphism (S : Type) :
  ArrowMorphism (PropertySP.Arrow_stateOptASP S)
    (PropertySP.ArrowChoice_stateOptASP S) (PropertySP.ArrowApply_stateOptASP S)
    (PropertySP.ArrowEq_stateOptASP S)
    (@Arrow_stateArrT S optionRel ROA)
    (@ArrowChoice_stateArrT S optionRel ROA ROAC)
    (@ArrowApply_stateArrT S optionRel ROA ROAA)
    (RSE S) (@state_option_asp_to_rel S).
Proof.
  exact (state_option_arrow_morphism (@PropertySP.ASP_rel) asp_to_rel_morphism
    ArrowLaws_Rel S ArrowChoiceLaws_Rel ArrowApplyLaws_Rel).
Qed.

Theorem state_option_asp_from_rel_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S optionRel ROA)
    (@ArrowChoice_stateArrT S optionRel ROA ROAC)
    (@ArrowApply_stateArrT S optionRel ROA ROAA)
    (RSE S)
    (PropertySP.Arrow_stateOptASP S)
    (PropertySP.ArrowChoice_stateOptASP S) (PropertySP.ArrowApply_stateOptASP S)
    (PropertySP.ArrowEq_stateOptASP S) (@state_option_asp_from_rel S).
Proof.
  exact (state_option_arrow_morphism (@relASP) asp_from_rel_morphism
    PropertySP.ArrowLaws_PureASPostArr S
    PropertySP.ArrowChoiceLaws_PureASPostArr PropertySP.ArrowApplyLaws_PureASPostArr).
Qed.

Theorem state_option_dslp_to_rel_morphism (S : Type) :
  ArrowMorphism (PropertySP.Arrow_stateOptDSLP S)
    (PropertySP.ArrowChoice_stateOptDSLP S) (PropertySP.ArrowApply_stateOptDSLP S)
    (PropertySP.ArrowEq_stateOptDSLP S)
    (@Arrow_stateArrT S optionRel ROA)
    (@ArrowChoice_stateArrT S optionRel ROA ROAC)
    (@ArrowApply_stateArrT S optionRel ROA ROAA)
    (RSE S) (@state_option_dslp_to_rel S).
Proof.
  exact (state_option_arrow_morphism (@PropertySP.DSLP_rel) dslp_to_rel_morphism
    ArrowLaws_Rel S ArrowChoiceLaws_Rel ArrowApplyLaws_Rel).
Qed.

Theorem state_option_dslp_from_rel_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S optionRel ROA)
    (@ArrowChoice_stateArrT S optionRel ROA ROAC)
    (@ArrowApply_stateArrT S optionRel ROA ROAA)
    (RSE S)
    (PropertySP.Arrow_stateOptDSLP S)
    (PropertySP.ArrowChoice_stateOptDSLP S) (PropertySP.ArrowApply_stateOptDSLP S)
    (PropertySP.ArrowEq_stateOptDSLP S) (@state_option_dslp_from_rel S).
Proof.
  exact (state_option_arrow_morphism (@relDSLP) dslp_from_rel_morphism
    PropertySP.ArrowLaws_PureDSLPostArr S
    PropertySP.ArrowChoiceLaws_PureDSLPostArr PropertySP.ArrowApplyLaws_PureDSLPostArr).
Qed.

(** ** Transport of the option-loop obstruction

    Only composition, [first], and injectivity of the direct option lifts
    are needed.  The contradiction itself remains the theorem from
    [OptionLoop], including its empty-feedback witness. Projection laws
    use semantic equality. Source injectivity supplies exact substitution
    under an arbitrary loop, which has no congruence assumption. *)

Section OptionLoopTransport.
  Context {arr : Type -> Type -> Type} {HA : Arrow arr} {SE : ArrowEq arr}.
  Variable project : forall A B, arr A B -> optionRel A B.
  Variable embed : forall A B, optionRel A B -> arr A B.
  Hypothesis project_proper : forall A B,
    Proper (@arrow_eq arr SE A B ==> Rel_eq) (project A B).
  Hypothesis project_embed : forall A B f, Rel_eq (project A B (embed A B f)) f.
  Hypothesis project_injective : forall A B (f g : arr A B),
    Rel_eq (project A B f) (project A B g) -> f = g.
  Local Notation OPA := (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel).
  Hypothesis project_comp : forall A B C (f : arr A B) (g : arr B C),
    Rel_eq (project A C (@arr_comp arr HA A B C f g))
    (@arr_comp optionRel OPA A B C (project A B f) (project B C g)).
  Hypothesis project_first : forall A B C (f : arr A B),
    Rel_eq (project (A * C)%type (B * C)%type (@arr_first arr HA A B C f))
    (@arr_first optionRel OPA A B C (project A B f)).

  Local Definition OPL : @ArrowLaws optionRel OPA ROE :=
    @ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowEq_Rel
      ArrowLaws_Rel ArrowChoiceLaws_Rel.
  Local Existing Instance OPL.

  Local Theorem optionRel_no_left_tightening_transport (L : @ArrowLoop arr HA) :
    ~ (forall (A B C D : Type) (h : arr A B) (f : arr (B * D) (C * D)),
      @arrow_eq arr SE A C
        (@arr_loop arr HA L A C D
          (@arr_comp arr HA _ _ _ (@arr_first arr HA A B D h) f))
        (@arr_comp arr HA _ _ _ h (@arr_loop arr HA L B C D f))).
  Proof.
    intro Htight.
    pose (LP :=
      {| arr_loop := fun A B C f => project A B
        (@arr_loop arr HA L A B C (embed (A * C)%type (B * C)%type f)) |}
      : @ArrowLoop optionRel OPA).
    apply (OptionLoop.optionRel_no_left_tightening LP).
    intros A B C D h f.
    assert (HE : embed (A * D)%type (C * D)%type
      (@arr_comp optionRel OPA _ _ _ (@arr_first optionRel OPA A B D h) f) =
      @arr_comp arr HA _ _ _ (@arr_first arr HA A B D (embed A B h))
        (embed (B * D)%type (C * D)%type f)).
    { apply project_injective.
      transitivity (@arr_comp optionRel OPA _ _ _
        (@arr_first optionRel OPA A B D h) f).
      - apply project_embed.
      - symmetry. etransitivity; [apply project_comp |].
        apply (@comp_proper _ _ _ OPL).
        + etransitivity; [apply project_first |].
          apply (@first_proper _ _ _ OPL). apply project_embed.
        + apply project_embed. }
    change (Rel_eq
      (project A C (@arr_loop arr HA L A C D
        (embed (A * D)%type (C * D)%type
          (@arr_comp optionRel OPA _ _ _ (@arr_first optionRel OPA A B D h) f))))
      (@arr_comp optionRel OPA _ _ _ h
        (project B C (@arr_loop arr HA L B C D
          (embed (B * D)%type (C * D)%type f))))).
    rewrite HE.
    transitivity (project A C (@arr_comp arr HA _ _ _ (embed A B h)
      (@arr_loop arr HA L B C D (embed (B * D)%type (C * D)%type f)))).
    - apply project_proper. apply Htight.
    - etransitivity; [apply project_comp |].
      apply (@comp_proper _ _ _ OPL); [apply project_embed | reflexivity].
  Qed.
End OptionLoopTransport.

Theorem optionASP_no_left_tightening
  (L : @ArrowLoop PropertySP.optionASPArr PropertySP.Arrow_optionASPArr) :
  ~ (forall (A B C D : Type) (h : PropertySP.optionASPArr A B)
       (f : PropertySP.optionASPArr (B * D) (C * D)),
     @arrow_eq _ PropertySP.ArrowEq_optionASPArr A C
       (@arr_loop _ PropertySP.Arrow_optionASPArr L A C D
       (@arr_comp _ PropertySP.Arrow_optionASPArr _ _ _
         (@arr_first _ PropertySP.Arrow_optionASPArr A B D h) f))
       (@arr_comp _ PropertySP.Arrow_optionASPArr _ _ _ h
         (@arr_loop _ PropertySP.Arrow_optionASPArr L B C D f))).
Proof.
  apply (optionRel_no_left_tightening_transport
    (@option_asp_to_rel) (@option_asp_from_rel)).
  - intros A B f g H. exact (morphism_proper option_asp_to_rel_morphism f g H).
  - intros A B R. apply option_asp_to_from.
  - intros A B f g Heq. exact (PropertySP.ASP_rel_ext f g Heq).
  - intros A B C f g. exact (morphism_comp option_asp_to_rel_morphism f g).
  - intros A B C f. exact (morphism_first option_asp_to_rel_morphism f).
Qed.

Theorem optionDSLP_no_left_tightening
  (L : @ArrowLoop PropertySP.optionDSLPArr PropertySP.Arrow_optionDSLPArr) :
  ~ (forall (A B C D : Type) (h : PropertySP.optionDSLPArr A B)
       (f : PropertySP.optionDSLPArr (B * D) (C * D)),
     @arrow_eq _ PropertySP.ArrowEq_optionDSLPArr A C
       (@arr_loop _ PropertySP.Arrow_optionDSLPArr L A C D
       (@arr_comp _ PropertySP.Arrow_optionDSLPArr _ _ _
         (@arr_first _ PropertySP.Arrow_optionDSLPArr A B D h) f))
       (@arr_comp _ PropertySP.Arrow_optionDSLPArr _ _ _ h
         (@arr_loop _ PropertySP.Arrow_optionDSLPArr L B C D f))).
Proof.
  apply (optionRel_no_left_tightening_transport
    (@option_dslp_to_rel) (@option_dslp_from_rel)).
  - intros A B f g H. exact (morphism_proper option_dslp_to_rel_morphism f g H).
  - intros A B R. apply option_dslp_to_from.
  - intros A B f g Heq. exact (PropertySP.DSLP_rel_ext f g Heq).
  - intros A B C f g. exact (morphism_comp option_dslp_to_rel_morphism f g).
  - intros A B C f. exact (morphism_first option_dslp_to_rel_morphism f).
Qed.

Corollary optionASP_no_lawful_ArrowLoop :
  ~ exists L : @ArrowLoop PropertySP.optionASPArr PropertySP.Arrow_optionASPArr,
    @ArrowLoopLaws PropertySP.optionASPArr PropertySP.Arrow_optionASPArr L
      PropertySP.ArrowEq_optionASPArr.
Proof.
  intros [L HL]. apply (optionASP_no_left_tightening L).
  intros A B C D h f.
  exact (@loop_left_tightening _ _ L _ HL A B C D h f).
Qed.

Corollary optionDSLP_no_lawful_ArrowLoop :
  ~ exists L : @ArrowLoop PropertySP.optionDSLPArr PropertySP.Arrow_optionDSLPArr,
    @ArrowLoopLaws PropertySP.optionDSLPArr PropertySP.Arrow_optionDSLPArr L
      PropertySP.ArrowEq_optionDSLPArr.
Proof.
  intros [L HL]. apply (optionDSLP_no_left_tightening L).
  intros A B C D h f.
  exact (@loop_left_tightening _ _ L _ HL A B C D h f).
Qed.
