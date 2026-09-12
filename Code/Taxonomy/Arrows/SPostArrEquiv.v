(** * Equivalence of property-only and coupled SP arrows.

    The conversions preserve the predicate transformer exactly.  Their
    operation laws include higher-order application: the arrow stored in
    an application's input is converted along with the application.

    The generic machinery imported from [Classes/ArrowMorphism.v] lifts
    these laws through the existing option and state transformers. *)

From Coq Require Import FunctionalExtensionality PropExtensionality.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Classes Require Export ArrowMorphism.
From Incorrectness.Taxonomy.Arrows Require Import PredArr RelSPPairArr OptionLoop SPostArr.

Module PropertySP := SPostArr.
Module CoupledSP := RelSPPairArr.

Local Obligation Tactic := idtac.

(** ** Transformer-preserving conversions *)

#[program] Definition asp_to_coupled {A B}
  (f : PropertySP.PureASPostArr A B) : CoupledSP.PureRelASPPairArr A B :=
  CoupledSP.mkRelSPPair (PropertySP.getASP f)
    (CoupledSP.asp_inv (PropertySP.getASP f)).
Next Obligation.
  intros A B f P b. apply PropertySP.ASP_normal_form.
Qed.

#[program] Definition dslp_to_coupled {A B}
  (f : PropertySP.PureDSLPostArr A B) : CoupledSP.PureRelDSLPPairArr A B :=
  CoupledSP.mkRelSPPair (PropertySP.getDSLP f)
    (CoupledSP.dslp_inv (PropertySP.getDSLP f)).
Next Obligation.
  intros A B f P b. apply PropertySP.DSLP_normal_form.
Qed.

#[program] Definition asp_from_coupled {A B}
  (f : CoupledSP.PureRelASPPairArr A B) : PropertySP.PureASPostArr A B :=
  CoupledSP.spost f.
Next Obligation.
  intros A B f. split.
  - intros b H. apply (proj2_sig f) in H. destruct H as [a [H _]]. exact H.
  - intros I HI p b. split.
    + intro H. apply (proj2_sig f) in H. destruct H as [a [[i HP] HR]].
      exists i. apply (proj2_sig f). exists a. auto.
    + intros [i H]. apply (proj2_sig f) in H. destruct H as [a [HP HR]].
      apply (proj2_sig f). exists a. split; [exists i; exact HP | exact HR].
Qed.

#[program] Definition dslp_from_coupled {A B}
  (f : CoupledSP.PureRelDSLPPairArr A B) : PropertySP.PureDSLPostArr A B :=
  CoupledSP.spost f.
Next Obligation.
  intros A B f. split.
  - intro b. apply (proj2_sig f). intros a _. constructor.
  - intros I HI p b. split.
    + intros H i. apply (proj2_sig f) in H.
      apply (proj2_sig f). intros a HR. exact (H a HR i).
    + intro H. apply (proj2_sig f). intros a HR i.
      specialize (H i). apply (proj2_sig f) in H. exact (H a HR).
Qed.

Lemma asp_to_coupled_semantics {A B} (f : PropertySP.PureASPostArr A B) :
  CoupledSP.spost (proj1_sig (asp_to_coupled f)) = PropertySP.getASP f.
Proof. reflexivity. Qed.

Lemma asp_from_coupled_semantics {A B} (f : CoupledSP.PureRelASPPairArr A B) :
  PropertySP.getASP (asp_from_coupled f) = CoupledSP.spost (proj1_sig f).
Proof. reflexivity. Qed.

Lemma dslp_to_coupled_semantics {A B} (f : PropertySP.PureDSLPostArr A B) :
  CoupledSP.spost (proj1_sig (dslp_to_coupled f)) = PropertySP.getDSLP f.
Proof. reflexivity. Qed.

Lemma dslp_from_coupled_semantics {A B} (f : CoupledSP.PureRelDSLPPairArr A B) :
  PropertySP.getDSLP (dslp_from_coupled f) = CoupledSP.spost (proj1_sig f).
Proof. reflexivity. Qed.

Theorem asp_from_to {A B} (f : PropertySP.PureASPostArr A B) :
  asp_from_coupled (asp_to_coupled f) = f.
Proof. apply PropertySP.PureASPostArr_eq. intros P b. reflexivity. Qed.

Theorem asp_to_from {A B} (f : CoupledSP.PureRelASPPairArr A B) :
  asp_to_coupled (asp_from_coupled f) = f.
Proof. apply CoupledSP.PureRelASPPairArr_eq. intros P b. reflexivity. Qed.

Theorem dslp_from_to {A B} (f : PropertySP.PureDSLPostArr A B) :
  dslp_from_coupled (dslp_to_coupled f) = f.
Proof. apply PropertySP.PureDSLPostArr_eq. intros P b. reflexivity. Qed.

Theorem dslp_to_from {A B} (f : CoupledSP.PureRelDSLPPairArr A B) :
  dslp_to_coupled (dslp_from_coupled f) = f.
Proof. apply CoupledSP.PureRelDSLPPairArr_eq. intros P b. reflexivity. Qed.

(** ** Base operation preservation *)

Local Notation CA := CoupledSP.Arrow_PureRelASPPairArr.
Local Notation CD := CoupledSP.Arrow_PureRelDSLPPairArr.
Local Notation CAC := CoupledSP.ArrowChoice_PureRelASPPairArr.
Local Notation CDC := CoupledSP.ArrowChoice_PureRelDSLPPairArr.
Local Notation CAA := CoupledSP.ArrowApply_PureRelASPPairArr.
Local Notation CDA := CoupledSP.ArrowApply_PureRelDSLPPairArr.

Theorem asp_to_coupled_pure {A B} (h : A -> B) :
  asp_to_coupled (PropertySP.pureASP h) = @arr_pure _ CA A B h.
Proof. apply CoupledSP.PureRelASPPairArr_eq. intros P b. reflexivity. Qed.

Theorem asp_to_coupled_comp {A B C}
  (f : PropertySP.PureASPostArr A B) (g : PropertySP.PureASPostArr B C) :
  asp_to_coupled (PropertySP.compASP f g) =
  @arr_comp _ CA A B C (asp_to_coupled f) (asp_to_coupled g).
Proof. apply CoupledSP.PureRelASPPairArr_eq. intros P c. reflexivity. Qed.

Theorem asp_to_coupled_first {A B C} (f : PropertySP.PureASPostArr A B) :
  asp_to_coupled (@PropertySP.firstASP A B C f) =
  @arr_first _ CA A B C (asp_to_coupled f).
Proof. apply CoupledSP.PureRelASPPairArr_eq. intros P [b c]. reflexivity. Qed.

Theorem asp_to_coupled_left {A B C} (f : PropertySP.PureASPostArr A B) :
  asp_to_coupled (@PropertySP.leftASP A B C f) =
  @arr_left _ CA CAC A B C (asp_to_coupled f).
Proof. apply CoupledSP.PureRelASPPairArr_eq. intros P [b|c]; reflexivity. Qed.

Theorem asp_to_coupled_app {A B} :
  asp_to_coupled (@PropertySP.appASP A B) =
  @arr_comp _ CA _ _ _
    (@arr_pure _ CA _ _ (fun '(f, a) => (asp_to_coupled f, a)))
    (@arr_app _ CA CAA A B).
Proof.
  apply CoupledSP.PureRelASPPairArr_eq. intros P b. cbn. split.
  - intros [f H]. apply PropertySP.ASP_normal_form in H.
    destruct H as [a [HP HR]]. exists (asp_to_coupled f), a.
    split; [exists (f, a); auto | exact HR].
  - intros [g [a [[[f a0] [HP Heq]] HR]]].
    injection Heq as Hg Ha. subst g a0.
    exists f. apply PropertySP.ASP_normal_form. exists a. auto.
Qed.

Theorem dslp_to_coupled_pure {A B} (h : A -> B) :
  dslp_to_coupled (PropertySP.pureDSLP h) = @arr_pure _ CD A B h.
Proof. apply CoupledSP.PureRelDSLPPairArr_eq. intros P b. reflexivity. Qed.

Theorem dslp_to_coupled_comp {A B C}
  (f : PropertySP.PureDSLPostArr A B) (g : PropertySP.PureDSLPostArr B C) :
  dslp_to_coupled (PropertySP.compDSLP f g) =
  @arr_comp _ CD A B C (dslp_to_coupled f) (dslp_to_coupled g).
Proof. apply CoupledSP.PureRelDSLPPairArr_eq. intros P c. reflexivity. Qed.

Theorem dslp_to_coupled_first {A B C} (f : PropertySP.PureDSLPostArr A B) :
  dslp_to_coupled (@PropertySP.firstDSLP A B C f) =
  @arr_first _ CD A B C (dslp_to_coupled f).
Proof. apply CoupledSP.PureRelDSLPPairArr_eq. intros P [b c]. reflexivity. Qed.

Theorem dslp_to_coupled_left {A B C} (f : PropertySP.PureDSLPostArr A B) :
  dslp_to_coupled (@PropertySP.leftDSLP A B C f) =
  @arr_left _ CD CDC A B C (dslp_to_coupled f).
Proof. apply CoupledSP.PureRelDSLPPairArr_eq. intros P [b|c]; reflexivity. Qed.

Theorem dslp_to_coupled_app {A B} :
  dslp_to_coupled (@PropertySP.appDSLP A B) =
  @arr_comp _ CD _ _ _
    (@arr_pure _ CD _ _ (fun '(f, a) => (dslp_to_coupled f, a)))
    (@arr_app _ CD CDA A B).
Proof.
  apply CoupledSP.PureRelDSLPPairArr_eq. intros P b. cbn. split.
  - intros H g a HR [f a0] Heq. injection Heq as Hg Ha. subst g a0.
    apply (proj1 (PropertySP.DSLP_normal_form f _ b) (H f) a HR).
  - intros H f. apply PropertySP.DSLP_normal_form. intros a HR.
    exact (H (dslp_to_coupled f) a HR (f, a) eq_refl).
Qed.

Theorem asp_to_coupled_morphism :
  ArrowMorphism PropertySP.Arrow_PureASPostArr
    PropertySP.ArrowChoice_PureASPostArr PropertySP.ArrowApply_PureASPostArr
    CA CAC CAA (@asp_to_coupled).
Proof.
  constructor.
  - exact @asp_to_coupled_pure.
  - exact @asp_to_coupled_comp.
  - exact @asp_to_coupled_first.
  - exact @asp_to_coupled_left.
  - exact @asp_to_coupled_app.
Qed.

Theorem dslp_to_coupled_morphism :
  ArrowMorphism PropertySP.Arrow_PureDSLPostArr
    PropertySP.ArrowChoice_PureDSLPostArr PropertySP.ArrowApply_PureDSLPostArr
    CD CDC CDA (@dslp_to_coupled).
Proof.
  constructor.
  - exact @dslp_to_coupled_pure.
  - exact @dslp_to_coupled_comp.
  - exact @dslp_to_coupled_first.
  - exact @dslp_to_coupled_left.
  - exact @dslp_to_coupled_app.
Qed.

Theorem asp_from_coupled_morphism :
  ArrowMorphism CA CAC CAA PropertySP.Arrow_PureASPostArr
    PropertySP.ArrowChoice_PureASPostArr PropertySP.ArrowApply_PureASPostArr
    (@asp_from_coupled).
Proof.
  exact (inverse_morphism (@asp_to_coupled) (@asp_from_coupled)
    (@asp_from_to) (@asp_to_from) asp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelASPPairArr).
Qed.

Theorem dslp_from_coupled_morphism :
  ArrowMorphism CD CDC CDA PropertySP.Arrow_PureDSLPostArr
    PropertySP.ArrowChoice_PureDSLPostArr PropertySP.ArrowApply_PureDSLPostArr
    (@dslp_from_coupled).
Proof.
  exact (inverse_morphism (@dslp_to_coupled) (@dslp_from_coupled)
    (@dslp_from_to) (@dslp_to_from) dslp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelDSLPPairArr).
Qed.

(** ** Public option, state, and state-over-option equivalences

    Each [_morphism] theorem exposes all five laws through
    [morphism_pure], [morphism_comp], [morphism_first], [morphism_left],
    and [morphism_app], in either conversion direction. *)

Definition option_asp_to_coupled {A B} (f : PropertySP.optionASPArr A B) :
  CoupledSP.optionASPArr A B := option_arrow_map (@asp_to_coupled) A B f.
Definition option_asp_from_coupled {A B} (f : CoupledSP.optionASPArr A B) :
  PropertySP.optionASPArr A B := option_arrow_map (@asp_from_coupled) A B f.
Definition option_dslp_to_coupled {A B} (f : PropertySP.optionDSLPArr A B) :
  CoupledSP.optionDSLPArr A B := option_arrow_map (@dslp_to_coupled) A B f.
Definition option_dslp_from_coupled {A B} (f : CoupledSP.optionDSLPArr A B) :
  PropertySP.optionDSLPArr A B := option_arrow_map (@dslp_from_coupled) A B f.

Definition state_asp_to_coupled {S A B}
  (f : stateArrT S PropertySP.PureASPostArr A B) :
  stateArrT S CoupledSP.PureRelASPPairArr A B := state_arrow_map S (@asp_to_coupled) A B f.
Definition state_asp_from_coupled {S A B}
  (f : stateArrT S CoupledSP.PureRelASPPairArr A B) :
  stateArrT S PropertySP.PureASPostArr A B := state_arrow_map S (@asp_from_coupled) A B f.
Definition state_dslp_to_coupled {S A B}
  (f : stateArrT S PropertySP.PureDSLPostArr A B) :
  stateArrT S CoupledSP.PureRelDSLPPairArr A B := state_arrow_map S (@dslp_to_coupled) A B f.
Definition state_dslp_from_coupled {S A B}
  (f : stateArrT S CoupledSP.PureRelDSLPPairArr A B) :
  stateArrT S PropertySP.PureDSLPostArr A B := state_arrow_map S (@dslp_from_coupled) A B f.

Definition state_option_asp_to_coupled {S A B}
  (f : stateArrT S PropertySP.optionASPArr A B) :
  stateArrT S CoupledSP.optionASPArr A B :=
  state_arrow_map S (@option_asp_to_coupled) A B f.
Definition state_option_asp_from_coupled {S A B}
  (f : stateArrT S CoupledSP.optionASPArr A B) :
  stateArrT S PropertySP.optionASPArr A B :=
  state_arrow_map S (@option_asp_from_coupled) A B f.
Definition state_option_dslp_to_coupled {S A B}
  (f : stateArrT S PropertySP.optionDSLPArr A B) :
  stateArrT S CoupledSP.optionDSLPArr A B :=
  state_arrow_map S (@option_dslp_to_coupled) A B f.
Definition state_option_dslp_from_coupled {S A B}
  (f : stateArrT S CoupledSP.optionDSLPArr A B) :
  stateArrT S PropertySP.optionDSLPArr A B :=
  state_arrow_map S (@option_dslp_from_coupled) A B f.

Theorem option_asp_from_to {A B} (f : PropertySP.optionASPArr A B) :
  option_asp_from_coupled (option_asp_to_coupled f) = f.
Proof.
  exact (option_arrow_map_roundtrip (@asp_to_coupled) (@asp_from_coupled)
    (@asp_from_to) A B f).
Qed.

Theorem option_asp_to_from {A B} (f : CoupledSP.optionASPArr A B) :
  option_asp_to_coupled (option_asp_from_coupled f) = f.
Proof.
  exact (option_arrow_map_roundtrip (@asp_from_coupled) (@asp_to_coupled)
    (@asp_to_from) A B f).
Qed.

Theorem option_dslp_from_to {A B} (f : PropertySP.optionDSLPArr A B) :
  option_dslp_from_coupled (option_dslp_to_coupled f) = f.
Proof.
  exact (option_arrow_map_roundtrip (@dslp_to_coupled) (@dslp_from_coupled)
    (@dslp_from_to) A B f).
Qed.

Theorem option_dslp_to_from {A B} (f : CoupledSP.optionDSLPArr A B) :
  option_dslp_to_coupled (option_dslp_from_coupled f) = f.
Proof.
  exact (option_arrow_map_roundtrip (@dslp_from_coupled) (@dslp_to_coupled)
    (@dslp_to_from) A B f).
Qed.

Theorem state_asp_from_to {S A B} (f : stateArrT S PropertySP.PureASPostArr A B) :
  state_asp_from_coupled (state_asp_to_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@asp_to_coupled) (@asp_from_coupled)
    (@asp_from_to) A B f).
Qed.

Theorem state_asp_to_from {S A B} (f : stateArrT S CoupledSP.PureRelASPPairArr A B) :
  state_asp_to_coupled (state_asp_from_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@asp_from_coupled) (@asp_to_coupled)
    (@asp_to_from) A B f).
Qed.

Theorem state_dslp_from_to {S A B} (f : stateArrT S PropertySP.PureDSLPostArr A B) :
  state_dslp_from_coupled (state_dslp_to_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@dslp_to_coupled) (@dslp_from_coupled)
    (@dslp_from_to) A B f).
Qed.

Theorem state_dslp_to_from {S A B} (f : stateArrT S CoupledSP.PureRelDSLPPairArr A B) :
  state_dslp_to_coupled (state_dslp_from_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@dslp_from_coupled) (@dslp_to_coupled)
    (@dslp_to_from) A B f).
Qed.

Theorem state_option_asp_from_to {S A B}
  (f : stateArrT S PropertySP.optionASPArr A B) :
  state_option_asp_from_coupled (state_option_asp_to_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@option_asp_to_coupled) (@option_asp_from_coupled)
    (@option_asp_from_to) A B f).
Qed.

Theorem state_option_asp_to_from {S A B}
  (f : stateArrT S CoupledSP.optionASPArr A B) :
  state_option_asp_to_coupled (state_option_asp_from_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@option_asp_from_coupled) (@option_asp_to_coupled)
    (@option_asp_to_from) A B f).
Qed.

Theorem state_option_dslp_from_to {S A B}
  (f : stateArrT S PropertySP.optionDSLPArr A B) :
  state_option_dslp_from_coupled (state_option_dslp_to_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@option_dslp_to_coupled) (@option_dslp_from_coupled)
    (@option_dslp_from_to) A B f).
Qed.

Theorem state_option_dslp_to_from {S A B}
  (f : stateArrT S CoupledSP.optionDSLPArr A B) :
  state_option_dslp_to_coupled (state_option_dslp_from_coupled f) = f.
Proof.
  exact (state_arrow_map_roundtrip S (@option_dslp_from_coupled) (@option_dslp_to_coupled)
    (@option_dslp_to_from) A B f).
Qed.

Local Notation PA := PropertySP.Arrow_PureASPostArr.
Local Notation PAC := PropertySP.ArrowChoice_PureASPostArr.
Local Notation PAA := PropertySP.ArrowApply_PureASPostArr.
Local Notation PD := PropertySP.Arrow_PureDSLPostArr.
Local Notation PDC := PropertySP.ArrowChoice_PureDSLPostArr.
Local Notation PDA := PropertySP.ArrowApply_PureDSLPostArr.
Local Notation COA := (@Arrow_optionArrT CoupledSP.PureRelASPPairArr CA CAC).
Local Notation COAC := (@ArrowChoice_optionArrT CoupledSP.PureRelASPPairArr CA CAC).
Local Notation COAA := (@ArrowApply_optionArrT CoupledSP.PureRelASPPairArr CA CAC CAA).
Local Notation COD := (@Arrow_optionArrT CoupledSP.PureRelDSLPPairArr CD CDC).
Local Notation CODC := (@ArrowChoice_optionArrT CoupledSP.PureRelDSLPPairArr CD CDC).
Local Notation CODA := (@ArrowApply_optionArrT CoupledSP.PureRelDSLPPairArr CD CDC CDA).

Theorem option_asp_to_coupled_morphism :
  ArrowMorphism PropertySP.Arrow_optionASPArr PropertySP.ArrowChoice_optionASPArr
    PropertySP.ArrowApply_optionASPArr COA COAC COAA (@option_asp_to_coupled).
Proof.
  exact (option_arrow_morphism (@asp_to_coupled) asp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelASPPairArr CoupledSP.ArrowChoiceLaws_PureRelASPPairArr).
Qed.

Theorem option_asp_from_coupled_morphism :
  ArrowMorphism COA COAC COAA PropertySP.Arrow_optionASPArr
    PropertySP.ArrowChoice_optionASPArr PropertySP.ArrowApply_optionASPArr
    (@option_asp_from_coupled).
Proof.
  exact (option_arrow_morphism (@asp_from_coupled) asp_from_coupled_morphism
    PropertySP.ArrowLaws_PureASPostArr PropertySP.ArrowChoiceLaws_PureASPostArr).
Qed.

Theorem option_dslp_to_coupled_morphism :
  ArrowMorphism PropertySP.Arrow_optionDSLPArr PropertySP.ArrowChoice_optionDSLPArr
    PropertySP.ArrowApply_optionDSLPArr COD CODC CODA (@option_dslp_to_coupled).
Proof.
  exact (option_arrow_morphism (@dslp_to_coupled) dslp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelDSLPPairArr CoupledSP.ArrowChoiceLaws_PureRelDSLPPairArr).
Qed.

Theorem option_dslp_from_coupled_morphism :
  ArrowMorphism COD CODC CODA PropertySP.Arrow_optionDSLPArr
    PropertySP.ArrowChoice_optionDSLPArr PropertySP.ArrowApply_optionDSLPArr
    (@option_dslp_from_coupled).
Proof.
  exact (option_arrow_morphism (@dslp_from_coupled) dslp_from_coupled_morphism
    PropertySP.ArrowLaws_PureDSLPostArr PropertySP.ArrowChoiceLaws_PureDSLPostArr).
Qed.

Theorem state_asp_to_coupled_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S PropertySP.PureASPostArr PA)
    (@ArrowChoice_stateArrT S PropertySP.PureASPostArr PA PAC)
    (@ArrowApply_stateArrT S PropertySP.PureASPostArr PA PAA)
    (@Arrow_stateArrT S CoupledSP.PureRelASPPairArr CA)
    (@ArrowChoice_stateArrT S CoupledSP.PureRelASPPairArr CA CAC)
    (@ArrowApply_stateArrT S CoupledSP.PureRelASPPairArr CA CAA)
    (@state_asp_to_coupled S).
Proof.
  exact (state_arrow_morphism (@asp_to_coupled) asp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelASPPairArr S).
Qed.

Theorem state_asp_from_coupled_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S CoupledSP.PureRelASPPairArr CA)
    (@ArrowChoice_stateArrT S CoupledSP.PureRelASPPairArr CA CAC)
    (@ArrowApply_stateArrT S CoupledSP.PureRelASPPairArr CA CAA)
    (@Arrow_stateArrT S PropertySP.PureASPostArr PA)
    (@ArrowChoice_stateArrT S PropertySP.PureASPostArr PA PAC)
    (@ArrowApply_stateArrT S PropertySP.PureASPostArr PA PAA)
    (@state_asp_from_coupled S).
Proof.
  exact (state_arrow_morphism (@asp_from_coupled) asp_from_coupled_morphism
    PropertySP.ArrowLaws_PureASPostArr S).
Qed.

Theorem state_dslp_to_coupled_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S PropertySP.PureDSLPostArr PD)
    (@ArrowChoice_stateArrT S PropertySP.PureDSLPostArr PD PDC)
    (@ArrowApply_stateArrT S PropertySP.PureDSLPostArr PD PDA)
    (@Arrow_stateArrT S CoupledSP.PureRelDSLPPairArr CD)
    (@ArrowChoice_stateArrT S CoupledSP.PureRelDSLPPairArr CD CDC)
    (@ArrowApply_stateArrT S CoupledSP.PureRelDSLPPairArr CD CDA)
    (@state_dslp_to_coupled S).
Proof.
  exact (state_arrow_morphism (@dslp_to_coupled) dslp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelDSLPPairArr S).
Qed.

Theorem state_dslp_from_coupled_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S CoupledSP.PureRelDSLPPairArr CD)
    (@ArrowChoice_stateArrT S CoupledSP.PureRelDSLPPairArr CD CDC)
    (@ArrowApply_stateArrT S CoupledSP.PureRelDSLPPairArr CD CDA)
    (@Arrow_stateArrT S PropertySP.PureDSLPostArr PD)
    (@ArrowChoice_stateArrT S PropertySP.PureDSLPostArr PD PDC)
    (@ArrowApply_stateArrT S PropertySP.PureDSLPostArr PD PDA)
    (@state_dslp_from_coupled S).
Proof.
  exact (state_arrow_morphism (@dslp_from_coupled) dslp_from_coupled_morphism
    PropertySP.ArrowLaws_PureDSLPostArr S).
Qed.

Theorem state_option_asp_to_coupled_morphism (S : Type) :
  ArrowMorphism (PropertySP.Arrow_stateOptASP S)
    (PropertySP.ArrowChoice_stateOptASP S) (PropertySP.ArrowApply_stateOptASP S)
    (@Arrow_stateArrT S CoupledSP.optionASPArr COA)
    (@ArrowChoice_stateArrT S CoupledSP.optionASPArr COA COAC)
    (@ArrowApply_stateArrT S CoupledSP.optionASPArr COA COAA)
    (@state_option_asp_to_coupled S).
Proof.
  exact (state_option_arrow_morphism (@asp_to_coupled) asp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelASPPairArr S CoupledSP.ArrowChoiceLaws_PureRelASPPairArr).
Qed.

Theorem state_option_asp_from_coupled_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S CoupledSP.optionASPArr COA)
    (@ArrowChoice_stateArrT S CoupledSP.optionASPArr COA COAC)
    (@ArrowApply_stateArrT S CoupledSP.optionASPArr COA COAA)
    (PropertySP.Arrow_stateOptASP S)
    (PropertySP.ArrowChoice_stateOptASP S) (PropertySP.ArrowApply_stateOptASP S)
    (@state_option_asp_from_coupled S).
Proof.
  exact (state_option_arrow_morphism (@asp_from_coupled) asp_from_coupled_morphism
    PropertySP.ArrowLaws_PureASPostArr S PropertySP.ArrowChoiceLaws_PureASPostArr).
Qed.

Theorem state_option_dslp_to_coupled_morphism (S : Type) :
  ArrowMorphism (PropertySP.Arrow_stateOptDSLP S)
    (PropertySP.ArrowChoice_stateOptDSLP S) (PropertySP.ArrowApply_stateOptDSLP S)
    (@Arrow_stateArrT S CoupledSP.optionDSLPArr COD)
    (@ArrowChoice_stateArrT S CoupledSP.optionDSLPArr COD CODC)
    (@ArrowApply_stateArrT S CoupledSP.optionDSLPArr COD CODA)
    (@state_option_dslp_to_coupled S).
Proof.
  exact (state_option_arrow_morphism (@dslp_to_coupled) dslp_to_coupled_morphism
    CoupledSP.ArrowLaws_PureRelDSLPPairArr S CoupledSP.ArrowChoiceLaws_PureRelDSLPPairArr).
Qed.

Theorem state_option_dslp_from_coupled_morphism (S : Type) :
  ArrowMorphism (@Arrow_stateArrT S CoupledSP.optionDSLPArr COD)
    (@ArrowChoice_stateArrT S CoupledSP.optionDSLPArr COD CODC)
    (@ArrowApply_stateArrT S CoupledSP.optionDSLPArr COD CODA)
    (PropertySP.Arrow_stateOptDSLP S)
    (PropertySP.ArrowChoice_stateOptDSLP S) (PropertySP.ArrowApply_stateOptDSLP S)
    (@state_option_dslp_from_coupled S).
Proof.
  exact (state_option_arrow_morphism (@dslp_from_coupled) dslp_from_coupled_morphism
    PropertySP.ArrowLaws_PureDSLPostArr S PropertySP.ArrowChoiceLaws_PureDSLPostArr).
Qed.

(** ** Transport of the option-loop obstruction

    Only composition, [first], and an invertible relation projection
    are needed.  The contradiction itself remains the theorem from
    [OptionLoop], including its empty-feedback witness. *)

Section OptionLoopTransport.
  Context {arr : Type -> Type -> Type} {HA : Arrow arr}.
  Variable project : forall A B, arr A B -> optionPred A B.
  Variable embed : forall A B, optionPred A B -> arr A B.
  Hypothesis project_embed : forall A B f, project A B (embed A B f) = f.
  Hypothesis project_injective : forall A B (f g : arr A B),
    project A B f = project A B g -> f = g.
  Local Notation OPA := (@Arrow_optionArrT PredArr Arrow_Pred ArrowChoice_Pred).
  Hypothesis project_comp : forall A B C (f : arr A B) (g : arr B C),
    project A C (@arr_comp arr HA A B C f g) =
    @arr_comp optionPred OPA A B C (project A B f) (project B C g).
  Hypothesis project_first : forall A B C (f : arr A B),
    project (A * C)%type (B * C)%type (@arr_first arr HA A B C f) =
    @arr_first optionPred OPA A B C (project A B f).

  Theorem optionPred_no_left_tightening_transport (L : @ArrowLoop arr HA) :
    ~ (forall (A B C D : Type) (h : arr A B) (f : arr (B * D) (C * D)),
      @arr_loop arr HA L A C D
        (@arr_comp arr HA _ _ _ (@arr_first arr HA A B D h) f) =
      @arr_comp arr HA _ _ _ h (@arr_loop arr HA L B C D f)).
  Proof.
    intro Htight.
    pose (LP :=
      {| arr_loop := fun A B C f => project A B
        (@arr_loop arr HA L A B C (embed (A * C)%type (B * C)%type f)) |}
      : @ArrowLoop optionPred OPA).
    apply (OptionLoop.optionPred_no_left_tightening LP).
    intros A B C D h f.
    assert (HE : embed (A * D)%type (C * D)%type
      (@arr_comp optionPred OPA _ _ _ (@arr_first optionPred OPA A B D h) f) =
      @arr_comp arr HA _ _ _ (@arr_first arr HA A B D (embed A B h))
        (embed (B * D)%type (C * D)%type f)).
    { apply project_injective.
      rewrite project_embed, project_comp, project_first, !project_embed.
      reflexivity. }
    change (forall a c,
      project A C (@arr_loop arr HA L A C D
        (embed (A * D)%type (C * D)%type
          (@arr_comp optionPred OPA _ _ _ (@arr_first optionPred OPA A B D h) f))) a c
      <-> @arr_comp optionPred OPA _ _ _ h
        (project B C (@arr_loop arr HA L B C D
          (embed (B * D)%type (C * D)%type f))) a c).
    rewrite HE, Htight, project_comp, project_embed. intros a c. reflexivity.
  Qed.
End OptionLoopTransport.

Local Definition option_asp_project A B (f : PropertySP.optionASPArr A B) :
  optionPred A B := CoupledSP.rel (proj1_sig (option_asp_to_coupled f)).
Local Definition option_dslp_project A B (f : PropertySP.optionDSLPArr A B) :
  optionPred A B := CoupledSP.rel (proj1_sig (option_dslp_to_coupled f)).

Theorem optionASP_no_left_tightening
  (L : @ArrowLoop PropertySP.optionASPArr PropertySP.Arrow_optionASPArr) :
  ~ (forall (A B C D : Type) (h : PropertySP.optionASPArr A B)
       (f : PropertySP.optionASPArr (B * D) (C * D)),
    @arr_loop _ PropertySP.Arrow_optionASPArr L A C D
      (@arr_comp _ PropertySP.Arrow_optionASPArr _ _ _
        (@arr_first _ PropertySP.Arrow_optionASPArr A B D h) f) =
    @arr_comp _ PropertySP.Arrow_optionASPArr _ _ _ h
      (@arr_loop _ PropertySP.Arrow_optionASPArr L B C D f)).
Proof.
  apply (optionPred_no_left_tightening_transport option_asp_project
    (fun A B R => option_asp_from_coupled (CoupledSP.mkASP R))).
  - intros A B R. unfold option_asp_project. rewrite option_asp_to_from. reflexivity.
  - intros A B f g Heq. apply PropertySP.PureASPostArr_eq. intros P b.
    rewrite !PropertySP.ASP_normal_form.
    change ((exists a, P a /\ option_asp_project A B f a b) <->
      exists a, P a /\ option_asp_project A B g a b).
    now rewrite Heq.
  - intros A B C f g. unfold option_asp_project.
    rewrite (morphism_comp option_asp_to_coupled_morphism). reflexivity.
  - intros A B C f. unfold option_asp_project.
    rewrite (morphism_first option_asp_to_coupled_morphism).
    extensionality p. destruct p as [a c]. extensionality q.
    apply propositional_extensionality. cbn.
    split; intros [[ob d] H]; exists (ob, d); exact H.
Qed.

Theorem optionDSLP_no_left_tightening
  (L : @ArrowLoop PropertySP.optionDSLPArr PropertySP.Arrow_optionDSLPArr) :
  ~ (forall (A B C D : Type) (h : PropertySP.optionDSLPArr A B)
       (f : PropertySP.optionDSLPArr (B * D) (C * D)),
    @arr_loop _ PropertySP.Arrow_optionDSLPArr L A C D
      (@arr_comp _ PropertySP.Arrow_optionDSLPArr _ _ _
        (@arr_first _ PropertySP.Arrow_optionDSLPArr A B D h) f) =
    @arr_comp _ PropertySP.Arrow_optionDSLPArr _ _ _ h
      (@arr_loop _ PropertySP.Arrow_optionDSLPArr L B C D f)).
Proof.
  apply (optionPred_no_left_tightening_transport option_dslp_project
    (fun A B R => option_dslp_from_coupled (CoupledSP.mkDSLP R))).
  - intros A B R. unfold option_dslp_project. rewrite option_dslp_to_from. reflexivity.
  - intros A B f g Heq. apply PropertySP.PureDSLPostArr_eq. intros P b.
    rewrite !PropertySP.DSLP_normal_form.
    change ((forall a, option_dslp_project A B f a b -> P a) <->
      forall a, option_dslp_project A B g a b -> P a).
    now rewrite Heq.
  - intros A B C f g. unfold option_dslp_project.
    rewrite (morphism_comp option_dslp_to_coupled_morphism). reflexivity.
  - intros A B C f. unfold option_dslp_project.
    rewrite (morphism_first option_dslp_to_coupled_morphism).
    extensionality p. destruct p as [a c]. extensionality q.
    apply propositional_extensionality. cbn.
    split; intros [[ob d] H]; exists (ob, d); exact H.
Qed.

Corollary optionASP_no_lawful_ArrowLoop :
  ~ exists L : @ArrowLoop PropertySP.optionASPArr PropertySP.Arrow_optionASPArr,
    @ArrowLoopLaws PropertySP.optionASPArr PropertySP.Arrow_optionASPArr L
      PropertySP.ArrowEq_optionASPArr.
Proof.
  intros [L HL]. apply (optionASP_no_left_tightening L).
  exact (@loop_left_tightening _ _ L _ HL).
Qed.

Corollary optionDSLP_no_lawful_ArrowLoop :
  ~ exists L : @ArrowLoop PropertySP.optionDSLPArr PropertySP.Arrow_optionDSLPArr,
    @ArrowLoopLaws PropertySP.optionDSLPArr PropertySP.Arrow_optionDSLPArr L
      PropertySP.ArrowEq_optionDSLPArr.
Proof.
  intros [L HL]. apply (optionDSLP_no_left_tightening L).
  exact (@loop_left_tightening _ _ L _ HL).
Qed.
