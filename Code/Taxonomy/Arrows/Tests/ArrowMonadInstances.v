(** * Concrete instantiation checks for the arrow-derived monad.

    Named dictionaries specialize the generic construction.  Agreement
    lemmas check its compact relational formulas; [:= _] checks automatic
    resolution, and [..._reuses_arrow] verifies which dictionary it finds.
    No test helper is registered as an instance.  Non-unit inputs exercise
    the threading of the input through [arr I]. *)

From Coq Require Import Morphisms.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow ArrowMonad RelArrowCoherence.
From Incorrectness.Lib.Arrow Require Import OptionArrowT StateArrowT.
From Incorrectness.Relational Require Import
  Rel.
From Incorrectness.GaloisConnections Require Import
  PrePostArr RelPrePostArr.
From Incorrectness.SP Require Import
  SPostArr.
From Incorrectness.SP Require ASPMonad DSLPMonad.

Create HintDb sp_arrow_bind.
#[local] Hint Unfold bind_arrow arr_fanout arr_split arr_second arr_id
  : sp_arrow_bind.

(* ================================================================= *)
(** ** [Rel]                                                       *)
(* ================================================================= *)

(** Typeclass resolution uses [Monad_Arrow]; these are named aliases.
     The compact [retRel]/[bindRel] helpers are in [Rel.v]. *)

Definition Monad_Rel (A : Type) : Monad (Rel A) :=
  @Monad_Arrow Rel Arrow_Rel ArrowApply_Rel A.

Definition Eq1Equivalence_Rel (A : Type)
  : @Eq1Equivalence (Rel A) (Monad_Rel A) Eq1_Rel :=
  @Eq1Equivalence_Arrow Rel Arrow_Rel ArrowApply_Rel ArrowEq_Rel A.

Definition MonadLawsE_Rel (A : Type)
  : @MonadLawsE (Rel A) Eq1_Rel (Monad_Rel A) :=
  @MonadLawsE_Arrow Rel Arrow_Rel ArrowApply_Rel ArrowEq_Rel
    ArrowLaws_Rel ArrowApplyLaws_Rel A.

Lemma retRel_eq_ret_arrow {A B} (b : B) :
  @arrow_eq Rel ArrowEq_Rel A B
    (retRel b) (@ret_arrow Rel Arrow_Rel A B b).
Proof. intros a b'. reflexivity. Qed.

Lemma bindRel_eq_bind_arrow {A B C}
  (m : Rel A B) (k : B -> Rel A C) :
  @arrow_eq Rel ArrowEq_Rel A C
    (bindRel m k) (@bind_arrow Rel Arrow_Rel ArrowApply_Rel A B C m k).
Proof.
  autounfold with sp_arrow_bind.
  setoid_rewrite (@first_pure Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  repeat setoid_rewrite (@pure_comp Rel Arrow_Rel ArrowEq_Rel ArrowLaws_Rel).
  intros a c. cbn. unfold bindRel. split.
  - intros [b [Hm Hk]]. exists (b, a). split.
    + exists (a, a). split; [reflexivity|].
      exists (b, a). cbn [swap]. auto.
    + exists (k b, a). cbn. auto.
  - intros [p [[p0 [Hp0 [p1 [Hm Hp]]]] [p2 [Hp2 Hk]]]].
    subst p0. destruct p1 as [b a']. cbn [swap] in Hp. subst p.
    cbn in Hm, Hp2. destruct Hm as [Hm Ha]. subst a' p2.
    exists b. exact (conj Hm Hk).
Qed.

(* ================================================================= *)
(** ** [PrePostArr]                                                    *)
(* ================================================================= *)

Definition retPrePost {A B} (b : B) : PrePostArr A B :=
  (fun _ => True, fun _ b' => b = b').

Definition bindPrePost {A B C}
  (m : PrePostArr A B) (k : B -> PrePostArr A C) : PrePostArr A C :=
  ( fun a => fst m a /\ (forall b, snd m a b -> fst (k b) a)
  , fun a c => exists b, snd m a b /\ snd (k b) a c ).

Definition Monad_PrePost (A : Type) : Monad (PrePostArr A) :=
  @Monad_Arrow PrePostArr Arrow_PrePost ArrowApply_PrePost A.

Definition Eq1Equivalence_PrePost (A : Type)
  : @Eq1Equivalence (PrePostArr A) (Monad_PrePost A) Eq1_PrePost :=
  @Eq1Equivalence_Arrow PrePostArr Arrow_PrePost ArrowApply_PrePost
    ArrowEq_PrePost A.

Definition MonadLawsE_PrePost (A : Type)
  : @MonadLawsE (PrePostArr A) Eq1_PrePost (Monad_PrePost A) :=
  @MonadLawsE_Arrow PrePostArr Arrow_PrePost ArrowApply_PrePost ArrowEq_PrePost
    ArrowLaws_PrePost ArrowApplyLaws_PrePost A.

Lemma retPrePost_eq_ret_arrow {A B} (b : B) :
  @arrow_eq PrePostArr ArrowEq_PrePost A B
    (retPrePost b) (@ret_arrow PrePostArr Arrow_PrePost A B b).
Proof. split; reflexivity. Qed.

Lemma bindPrePost_eq_bind_arrow {A B C}
    (m : PrePostArr A B) (k : B -> PrePostArr A C) :
  @arrow_eq PrePostArr ArrowEq_PrePost A C
    (bindPrePost m k)
    (@bind_arrow PrePostArr Arrow_PrePost ArrowApply_PrePost A B C m k).
Proof.
  autounfold with sp_arrow_bind.
  setoid_rewrite (@first_pure PrePostArr Arrow_PrePost ArrowEq_PrePost
    ArrowLaws_PrePost).
  repeat setoid_rewrite (@pure_comp PrePostArr Arrow_PrePost ArrowEq_PrePost
    ArrowLaws_PrePost).
  split; cbn.
  - intros a. split.
    + intros [HP Hk]. split.
      * split; [exact I|]. intros p <-. cbn.
        split; [exact HP|]. intros _ _. exact I.
      * intros p [p0 [Hp0 [p1 [Hm Hp]]]].
        subst p0. destruct p1 as [b a']. cbn [swap] in Hp. subst p.
        cbn in Hm. destruct Hm as [Hm Ha]. subst a'.
        split; [exact I|]. intros p2 <-. exact (Hk b Hm).
    + intros [[_ HP] Hk]. split.
      * exact (proj1 (HP (a, a) eq_refl)).
      * intros b Hm.
        assert (Hpre : True /\ forall p : PrePostArr A C * A,
          (k b, a) = p -> fst (fst p) (snd p)).
        { apply (Hk (b, a)). exists (a, a). split; [reflexivity|].
          exists (b, a). cbn [swap]. auto. }
        exact (proj2 Hpre (k b, a) eq_refl).
  - intros a c. split.
    + intros [b [Hm Hk]]. exists (b, a). split.
      * exists (a, a). split; [reflexivity|].
        exists (b, a). cbn [swap]. auto.
      * exists (k b, a). cbn. auto.
    + intros [p [[p0 [Hp0 [p1 [Hm Hp]]]] [p2 [Hp2 Hk]]]].
      subst p0. destruct p1 as [b a']. cbn [swap] in Hp. subst p.
      cbn in Hm, Hp2. destruct Hm as [Hm Ha]. subst a' p2.
      exists b. exact (conj Hm Hk).
Qed.

(* ================================================================= *)
(** ** [RelPrePostArr]                                                 *)
(* ================================================================= *)

(** The compact [retRelPrePost]/[bindRelPrePost] helpers stay in
    [RelPrePostArr.v] because the projection characterization lemmas
    [project_wp_ret]/[project_wp_bind] are stated in terms of them. *)

Definition Monad_RelPrePost (A : Type) : Monad (RelPrePostArr A) :=
  @Monad_Arrow RelPrePostArr Arrow_RelPrePost ArrowApply_RelPrePost A.

Definition Eq1Equivalence_RelPrePost (A : Type)
  : @Eq1Equivalence (RelPrePostArr A) (Monad_RelPrePost A) Eq1_RelPrePost :=
  @Eq1Equivalence_Arrow RelPrePostArr Arrow_RelPrePost ArrowApply_RelPrePost
    ArrowEq_RelPrePost A.

Definition MonadLawsE_RelPrePost (A : Type)
  : @MonadLawsE (RelPrePostArr A) Eq1_RelPrePost (Monad_RelPrePost A) :=
  @MonadLawsE_Arrow RelPrePostArr Arrow_RelPrePost ArrowApply_RelPrePost
    ArrowEq_RelPrePost ArrowLaws_RelPrePost ArrowApplyLaws_RelPrePost A.

Lemma retRelPrePost_eq_ret_arrow {A B} (b : B) :
  @arrow_eq RelPrePostArr ArrowEq_RelPrePost A B
    (retRelPrePost b) (@ret_arrow RelPrePostArr Arrow_RelPrePost A B b).
Proof. intros a Q. reflexivity. Qed.

Lemma bindRelPrePost_eq_bind_arrow {A B C}
    (r : RelPrePostArr A B) (k : B -> RelPrePostArr A C) :
  @arrow_eq RelPrePostArr ArrowEq_RelPrePost A C
    (bindRelPrePost r k)
    (@bind_arrow RelPrePostArr Arrow_RelPrePost ArrowApply_RelPrePost
      A B C r k).
Proof.
  intros a Q. rewrite project_wp_bind.
  autounfold with sp_arrow_bind.
  rewrite !project_wp_arr_comp, project_wp_arr_pure.
  rewrite project_wp_arr_comp, project_wp_arr_first.
  cbn [fst snd]. apply project_wp_Proper. intros b.
  rewrite project_wp_arr_comp, project_wp_arr_pure.
  cbn [swap].
  rewrite project_wp_arr_comp, project_wp_arr_first, project_wp_arr_pure.
  cbn [fst snd].
  rewrite project_wp_arr_pure. cbn [swap].
  rewrite project_wp_arr_comp, project_wp_arr_pure, project_wp_arr_app.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** [progRelArr] and state-over-option Rel monad                   *)
(* ================================================================= *)

(** The relational specification monad [progRelArr S] specializes the
    input of [stateArrT S optionRel] to [unit]. Non-unit inputs
    exercise the threading of the input through [stateArrT S optionRel I]. *)

Definition Monad_progRelArr (S : Type) : Monad (progRelArr S) :=
  @Monad_Arrow (stateArrT S optionRel)
    (@Arrow_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel))
    (@ArrowApply_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
      (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel)) unit.

Definition MonadLawsE_progRelArr (S : Type)
  : @MonadLawsE (progRelArr S)
      (@Eq1_Arrow _ (@ArrowEq_stateArrT S optionRel
          (@ArrowEq_optionArrT _ ArrowEq_Rel)) unit)
      (Monad_progRelArr S) :=
  @MonadLawsE_Arrow (stateArrT S optionRel)
    (@Arrow_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel))
    (@ArrowApply_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
      (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel))
    (@ArrowEq_stateArrT S optionRel
      (@ArrowEq_optionArrT _ ArrowEq_Rel))
    (@ArrowLaws_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
      (@ArrowEq_optionArrT _ ArrowEq_Rel)
      (@ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel
        ArrowEq_Rel ArrowLaws_Rel ArrowChoiceLaws_Rel))
    (@ArrowApplyLaws_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
      (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel)
      (@ArrowEq_optionArrT _ ArrowEq_Rel)
      (@ArrowLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel
        ArrowEq_Rel ArrowLaws_Rel ArrowChoiceLaws_Rel)
      (@ArrowApplyLaws_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel
        ArrowEq_Rel ArrowLaws_Rel ArrowChoiceLaws_Rel ArrowApplyLaws_Rel))
    unit.

(** Compact return and bind agreement for [stateArrT S optionRel],
    exercising arbitrary (non-unit) input [I]. *)

Lemma state_option_rel_ret_eq {S I A} (a : A) (i : I) (s : S) r :
  @ret_arrow (stateArrT S optionRel)
    (@Arrow_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel))
    I A a (i, s) r <-> Some (a, s) = r.
Proof.
  apply (@rel_state_option_pure_fields Rel Arrow_Rel ArrowChoice_Rel
    (fun _ _ f => f)
    (fun _ _ _ _ _ => iff_refl _)
    S I A (fun _ => a) i s r).
Qed.

Lemma state_option_rel_bind_eq {S I A B}
    (m : stateArrT S optionRel I A) (k : A -> stateArrT S optionRel I B)
    (i : I) (s : S) r :
  @bind_arrow (stateArrT S optionRel)
    (@Arrow_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel))
    (@ArrowApply_stateArrT S optionRel
      (@Arrow_optionArrT Rel Arrow_Rel ArrowChoice_Rel)
      (@ArrowApply_optionArrT Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel))
    I A B m k (i, s) r <->
  exists om, m (i, s) om /\
    match om with
    | Some (a, t) => k a (i, t) r
    | None => r = None
    end.
Proof.
  apply (@rel_state_option_bind_fields Rel Arrow_Rel ArrowChoice_Rel ArrowApply_Rel
    (fun _ _ f => f)
    (fun _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ _ => iff_refl _)
    (fun _ _ _ _ _ => iff_refl _)
    S I A B m k i s r).
Qed.

(** Compact return and bind agreement for [progRelArr S] (specialized to [unit]). *)

Lemma progRelArr_ret_eq {S A} (a : A) (s : S) r :
  @ret _ (Monad_progRelArr S) A a (tt, s) r <-> Some (a, s) = r.
Proof. exact (state_option_rel_ret_eq a tt s r). Qed.

Lemma progRelArr_bind_eq {S A B} (m : progRelArr S A) (k : A -> progRelArr S B)
    (s : S) r :
  @bind _ (Monad_progRelArr S) A B m k (tt, s) r <->
  exists om, m (tt, s) om /\
    match om with
    | Some (a, t) => k a (tt, t) r
    | None => r = None
    end.
Proof. exact (state_option_rel_bind_eq m k tt s r). Qed.

(* ================================================================= *)
(** ** Resolution checks                                               *)
(* ================================================================= *)

(** These monads are inferred without naming the concrete aliases.  The
    equalities check both automatic resolution and the public alias bodies. *)
Definition inferred_rel_monad : Monad (Rel bool) := _.
Definition inferred_prepost_monad : Monad (PrePostArr bool) := _.
Definition inferred_relprepost_monad : Monad (RelPrePostArr bool) := _.

Example rel_reuses_arrow :
  inferred_rel_monad = @Monad_Rel bool /\
  @Monad_Rel bool = @Monad_Arrow Rel Arrow_Rel ArrowApply_Rel bool.
Proof. split; reflexivity. Qed.

Example prepost_reuses_arrow :
  inferred_prepost_monad = @Monad_PrePost bool /\
  @Monad_PrePost bool = @Monad_Arrow PrePostArr Arrow_PrePost ArrowApply_PrePost bool.
Proof. split; reflexivity. Qed.

Example relprepost_reuses_arrow :
  inferred_relprepost_monad = @Monad_RelPrePost bool /\
  @Monad_RelPrePost bool =
    @Monad_Arrow RelPrePostArr Arrow_RelPrePost ArrowApply_RelPrePost bool.
Proof. split; reflexivity. Qed.

(** Canonical concrete equalities must resolve the generic law instances. *)
Definition rel_canonical_laws :
  @MonadLawsE (Rel bool) (@Eq1_Rel bool) inferred_rel_monad := _.
Definition prepost_canonical_laws :
  @MonadLawsE (PrePostArr bool) (@Eq1_PrePost bool) inferred_prepost_monad := _.
Definition relprepost_canonical_laws :
  @MonadLawsE (RelPrePostArr bool) (@Eq1_RelPrePost bool)
    inferred_relprepost_monad := _.

Definition rel_canonical_equivalence :
  @Eq1Equivalence (Rel bool) inferred_rel_monad (@Eq1_Rel bool) := _.
Definition prepost_canonical_equivalence :
  @Eq1Equivalence (PrePostArr bool) inferred_prepost_monad (@Eq1_PrePost bool) := _.
Definition relprepost_canonical_equivalence :
  @Eq1Equivalence (RelPrePostArr bool) inferred_relprepost_monad
    (@Eq1_RelPrePost bool) := _.

(** Pointwise arrow equalities, rather than Leibniz equality. *)
Definition rel_monad_laws :
  @MonadLawsE (Rel bool)
    (@Eq1_Arrow _ ArrowEq_Rel bool)
    (@Monad_Arrow _ Arrow_Rel ArrowApply_Rel bool) := _.

Definition relprepost_monad_laws :
  @MonadLawsE (RelPrePostArr bool)
    (@Eq1_Arrow _ ArrowEq_RelPrePost bool)
    (@Monad_Arrow _ Arrow_RelPrePost ArrowApply_RelPrePost bool) := _.

(** Property-only angelic arrows: base, option, state, and state-over-option. *)
Definition property_asp_monad_laws :
  @MonadLawsE (SPostArr.PureASPostArr bool)
    (@Eq1_Arrow _ SPostArr.ArrowEq_PureASPostArr bool)
    (@Monad_Arrow _ SPostArr.Arrow_PureASPostArr
      SPostArr.ArrowApply_PureASPostArr bool) := _.

Definition property_option_asp_monad_laws :
  @MonadLawsE (SPostArr.optionASPArr bool)
    (@Eq1_Arrow _ SPostArr.ArrowEq_optionASPArr bool)
    (@Monad_Arrow _ SPostArr.Arrow_optionASPArr
      SPostArr.ArrowApply_optionASPArr bool) := _.

Definition property_state_asp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S SPostArr.PureASPostArr bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S _ SPostArr.ArrowEq_PureASPostArr) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _ SPostArr.Arrow_PureASPostArr)
      (@ArrowApply_stateArrT S _ SPostArr.Arrow_PureASPostArr
        SPostArr.ArrowApply_PureASPostArr) bool) := _.

Definition property_state_option_asp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S SPostArr.optionASPArr bool)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptASP S) bool)
    (@Monad_Arrow _ (SPostArr.Arrow_stateOptASP S)
      (SPostArr.ArrowApply_stateOptASP S) bool) := _.

(** Relational arrows: base, option, state, and state-over-option stacks.
    These exercise the shared [Rel] presentation with non-unit inputs. *)
Definition rel_option_monad_laws :
  @MonadLawsE (optionRel bool)
    (@Eq1_Arrow _ (@ArrowEq_optionArrT _ ArrowEq_Rel) bool)
    (@Monad_Arrow _ (@Arrow_optionArrT _ Arrow_Rel ArrowChoice_Rel)
      (@ArrowApply_optionArrT _ Arrow_Rel ArrowChoice_Rel ArrowApply_Rel) bool) := _.

Definition rel_state_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S Rel bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S _ ArrowEq_Rel) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _ Arrow_Rel)
      (@ArrowApply_stateArrT S _ Arrow_Rel ArrowApply_Rel) bool) := _.

Definition rel_state_option_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S optionRel bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S optionRel
        (@ArrowEq_optionArrT _ ArrowEq_Rel)) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _
        (@Arrow_optionArrT _ Arrow_Rel
          ArrowChoice_Rel))
      (@ArrowApply_stateArrT S _
        (@Arrow_optionArrT _ Arrow_Rel
          ArrowChoice_Rel)
        (@ArrowApply_optionArrT _ Arrow_Rel
          ArrowChoice_Rel
          ArrowApply_Rel)) bool) := _.

(** The monad dictionaries of [BaseSpecMonads/ASPMonad] and [DSLPMonad] at
    the state-over-option stacks are the generic arrow monads. Explicit
    generic dictionaries pin the exact instance at arbitrary state and avoid
    competing recursive option/state resolution paths. *)
Definition spostarr_asp_monad_laws (S : Type) :
  @MonadLawsE (SPostArr.ASPostArr S)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptASP S) unit)
    (ASPMonad.Monad_ASPStExc S) :=
  @MonadLawsE_Arrow (stateArrT S SPostArr.optionASPArr)
    (SPostArr.Arrow_stateOptASP S) (SPostArr.ArrowApply_stateOptASP S)
    (SPostArr.ArrowEq_stateOptASP S) (SPostArr.ArrowLaws_stateOptASP S)
    (SPostArr.ArrowApplyLaws_stateOptASP S) unit.

Definition spostarr_dslp_monad_laws (S : Type) :
  @MonadLawsE (SPostArr.DSLPostArr S)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptDSLP S) unit)
    (DSLPMonad.Monad_DSLPStExc S) :=
  @MonadLawsE_Arrow (stateArrT S SPostArr.optionDSLPArr)
    (SPostArr.Arrow_stateOptDSLP S) (SPostArr.ArrowApply_stateOptDSLP S)
    (SPostArr.ArrowEq_stateOptDSLP S) (SPostArr.ArrowLaws_stateOptDSLP S)
    (SPostArr.ArrowApplyLaws_stateOptDSLP S) unit.

(** Cross-API clients: these must typecheck by conversion, without a map
    between bundles or equality reflection. They also pin the dictionaries
    selected after importing the arrow and unary monad APIs. *)
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad.
From Incorrectness.SP Require Import SPostArrEquiv.

Module CanonicalSP.
  Definition asp_dictionary : Arrow ASPArr := _.
  Definition dslp_dictionary : Arrow DSLPArr := _.
  Definition asp_laws : ArrowLaws ASPArr := _.
  Definition dslp_laws : ArrowLaws DSLPArr := _.
  Definition dsp_laws : ArrowLaws DSPArr := _.
  Definition dsp_choice : ArrowChoiceLaws DSPArr := _.
  Definition dsp_apply : ArrowApplyLaws DSPArr := _.
  Definition aslp_laws : ArrowLaws ASLPArr := _.
  Definition aslp_choice : ArrowChoiceLaws ASLPArr := _.
  Definition aslp_apply : ArrowApplyLaws ASLPArr := _.

  Example asp_dictionary_identity : asp_dictionary = Arrow_PureASPostArr.
  Proof. reflexivity. Qed.
  Example dslp_dictionary_identity : dslp_dictionary = Arrow_PureDSLPostArr.
  Proof. reflexivity. Qed.
  Example asp_law_dictionary_identity : asp_laws = ArrowLaws_PureASPostArr.
  Proof. reflexivity. Qed.
  Example dslp_law_dictionary_identity : dslp_laws = ArrowLaws_PureDSLPostArr.
  Proof. reflexivity. Qed.
  Example asp_choice_dictionary_identity : ArrowChoice_ASPArr = ArrowChoice_PureASPostArr.
  Proof. reflexivity. Qed.
  Example dslp_choice_dictionary_identity : ArrowChoice_DSLPArr = ArrowChoice_PureDSLPostArr.
  Proof. reflexivity. Qed.
  Example asp_apply_dictionary_identity : ArrowApply_ASPArr = ArrowApply_PureASPostArr.
  Proof. reflexivity. Qed.
  Example dslp_apply_dictionary_identity : ArrowApply_DSLPArr = ArrowApply_PureDSLPostArr.
  Proof. reflexivity. Qed.
  Example asp_equality_dictionary_identity : ArrowEq_ASPArr = ArrowEq_PureASPostArr.
  Proof. reflexivity. Qed.
  Example dslp_equality_dictionary_identity : ArrowEq_DSLPArr = ArrowEq_PureDSLPostArr.
  Proof. reflexivity. Qed.

  (** A canonical arrow is fed to the compatibility application operator,
      and its result is consumed using the canonical equality and laws. *)
  Example asp_mixed_application {A B} (f : ASPArr A B) :
    ASPArr_eq (SPostArr.compASP (SPostArr.arrASP (fun a => (f, a))) SPostArr.appASP) f.
  Proof. exact (@app_law ASPArr Arrow_ASPArr ArrowApply_ASPArr ArrowEq_ASPArr ArrowApplyLaws_ASPArr A B f). Qed.
  Example dslp_mixed_application {A B} (f : DSLPArr A B) :
    DSLPArr_eq (SPostArr.compDSLP (SPostArr.arrDSLP (fun a => (f, a))) SPostArr.appDSLP) f.
  Proof. exact (@app_law DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr ArrowEq_DSLPArr ArrowApplyLaws_DSLPArr A B f). Qed.

  Definition asp_pure_client {A B} (m : ASP A) (k : A -> PureASPostArr unit B) :
    PureASPostArr unit B := bindASP m k.
  Definition dslp_pure_client {A B} (m : DSLP A) (k : A -> PureDSLPostArr unit B) :
    PureDSLPostArr unit B := bindDSLP m k.
  Definition asp_state_client {S A B} (m : ASPSt S A)
    (k : A -> stateArrT S PureASPostArr unit B) :
    stateArrT S PureASPostArr unit B := bindASPSt m k.
  Definition dslp_state_client {S A B} (m : DSLPSt S A)
    (k : A -> stateArrT S PureDSLPostArr unit B) :
    stateArrT S PureDSLPostArr unit B := bindDSLPSt m k.

  (** Both directions of the public type seam are exercised by binding a
      canonical computation to a compatibility continuation. *)
  Definition asp_mixed_bind {S A B} (m : ASPStExc S A)
    (k : A -> ASPostArr S B) : ASPostArr S B := bindASPStExc m k.
  Definition dslp_mixed_bind {S A B} (m : DSLPStExc S A)
    (k : A -> DSLPostArr S B) : DSLPostArr S B := bindDSLPStExc m k.
  Example asp_mixed_bind_identity {S A B} (m : ASPStExc S A) (k : A -> ASPostArr S B) :
    asp_mixed_bind m k = @bind _ (Monad_ASPStExc S) A B m k.
  Proof. reflexivity. Qed.
  Example dslp_mixed_bind_identity {S A B} (m : DSLPStExc S A) (k : A -> DSLPostArr S B) :
    dslp_mixed_bind m k = @bind _ (Monad_DSLPStExc S) A B m k.
  Proof. reflexivity. Qed.

  (** The canonical bind and runner, read through the compatibility
      relation [ASP_rel]. *)
  Lemma ASP_rel_bind {S A B} (m : ASPostArr S A) (k : A -> ASPostArr S B)
      (s : S) r :
    ASP_rel (@bind _ (Monad_ASPStExc S) A B m k) (tt, s) r <->
    exists om, ASP_rel m (tt, s) om /\
      match om with
      | Some (a, t) => ASP_rel (k a) (tt, t) r
      | None => r = None
      end.
  Proof.
    exact (@relE_bind PureASPostArr Arrow_PureASPostArr ArrowApply_PureASPostArr
      RelArrow_PureASPostArr RelArrowApply_PureASPostArr
      ArrowChoice_PureASPostArr RelArrowChoice_PureASPostArr
      S unit A B m k tt s r).
  Qed.

  Lemma getASPStExc_ASP_rel {S A} (w : ASPostArr S A) (pre : S -> Prop) r :
    getASPStExc w pre r <-> exists s, pre s /\ ASP_rel w (tt, s) r.
  Proof.
    unfold getASPStExc. rewrite (ASP_normal_form w (fun us => pre (snd us)) r).
    split.
    - intros [us [Hus Hw]]. destruct us as [[] s]. exists s.
      split; [exact Hus | exact Hw].
    - intros [s [Hs Hw]]. exists (tt, s). split; [exact Hs | exact Hw].
  Qed.

  (** Conversion still preserves semantics on canonical values, including
      state update followed by propagated failure. These are not just
      dictionary equations. *)
  Definition update : ASPStExc nat nat :=
    ofRelASPArr (fun p r => r = Some (snd p, S (snd p))).
  Definition fail (a : nat) : ASPostArr nat nat :=
    SPostArr.relASP (fun _ r => r = None).
  Example mixed_update_failure r :
    getASPStExc (asp_mixed_bind update fail) (eq 3) r <-> r = None.
  Proof.
    rewrite asp_mixed_bind_identity, getASPStExc_ASP_rel. split.
    - intros [s [_ H]]. rewrite ASP_rel_bind in H.
      destruct H as [om [Hm Hk]]. unfold update in Hm.
      rewrite (ASP_rel_relASP (fun p : unit * nat => fun r => r = Some (snd p, S (snd p)))) in Hm.
      cbn in Hm. subst om.
      unfold fail in Hk. rewrite ASP_rel_relASP in Hk. exact Hk.
    - intros ->. exists 3. split; [reflexivity |]. rewrite ASP_rel_bind.
      exists (Some (3, 4)). split.
      + unfold update. rewrite ASP_rel_relASP. reflexivity.
      + unfold fail. rewrite ASP_rel_relASP. reflexivity.
  Qed.
  Example canonical_asp_semantic_roundtrip {A B} (f : ASPArr A B) :
    ASPArr_eq (SPostArr.relASP (ASP_rel f)) f.
  Proof. apply asp_from_to. Qed.
  Example canonical_dslp_semantic_roundtrip {A B} (f : DSLPArr A B) :
    DSLPArr_eq (SPostArr.relDSLP (DSLP_rel f)) f.
  Proof. apply dslp_from_to. Qed.
End CanonicalSP.
