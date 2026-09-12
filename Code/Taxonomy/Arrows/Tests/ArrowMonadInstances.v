(** * Concrete instantiation checks for the arrow-derived monad.

    Named dictionaries specialize the generic construction.  Agreement
    lemmas check its compact relational formulas; [:= _] checks automatic
    resolution, and [..._reuses_arrow] verifies which dictionary it finds.
    No test helper is registered as an instance.  Non-unit inputs exercise
    the reader-like use of [arr I]. *)

From Coq Require Import Morphisms.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad.
From Incorrectness.Classes Require Import OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import
  PredArr PrePostArr RelPrePostArr RelSPPairArr SPostArr SPostArrMonad.

Create HintDb sp_arrow_bind.
#[local] Hint Unfold bind_arrow arr_fanout arr_split arr_second arr_id
  : sp_arrow_bind.

(* ================================================================= *)
(** ** [PredArr]                                                       *)
(* ================================================================= *)

(** Typeclass resolution uses [Monad_Arrow]; these are named aliases.
     The compact [retPred]/[bindPred] helpers stay in [PredArr.v]: the
     [OldSP] observations consume them. *)

Definition Monad_Pred (A : Type) : Monad (PredArr A) :=
  @Monad_Arrow PredArr Arrow_Pred ArrowApply_Pred A.

Definition Eq1Equivalence_Pred (A : Type)
  : @Eq1Equivalence (PredArr A) (Monad_Pred A) Eq1_Pred :=
  @Eq1Equivalence_Arrow PredArr Arrow_Pred ArrowApply_Pred ArrowEq_Pred A.

Definition MonadLawsE_Pred (A : Type)
  : @MonadLawsE (PredArr A) Eq1_Pred (Monad_Pred A) :=
  @MonadLawsE_Arrow PredArr Arrow_Pred ArrowApply_Pred ArrowEq_Pred
    ArrowLaws_Pred ArrowApplyLaws_Pred A.

Lemma retPred_eq_ret_arrow {A B} (b : B) :
  @arrow_eq PredArr ArrowEq_Pred A B
    (retPred b) (@ret_arrow PredArr Arrow_Pred A B b).
Proof. intros a b'. reflexivity. Qed.

Lemma bindPred_eq_bind_arrow {A B C}
  (m : PredArr A B) (k : B -> PredArr A C) :
  @arrow_eq PredArr ArrowEq_Pred A C
    (bindPred m k) (@bind_arrow PredArr Arrow_Pred ArrowApply_Pred A B C m k).
Proof.
  autounfold with sp_arrow_bind.
  setoid_rewrite (@first_pure PredArr Arrow_Pred ArrowEq_Pred ArrowLaws_Pred).
  repeat setoid_rewrite (@pure_comp PredArr Arrow_Pred ArrowEq_Pred ArrowLaws_Pred).
  intros a c. cbn. unfold bindPred. split.
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
(** ** Coupled [PureRelASPPairArr] / [PureRelDSLPPairArr]              *)
(* ================================================================= *)

(** Angelic. *)

Definition Monad_PureRelASPPairArr (I : Type)
  : Monad (PureRelASPPairArr I) :=
  @Monad_Arrow PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowApply_PureRelASPPairArr I.

Definition Eq1Equivalence_PureRelASPPairArr (I : Type)
  : @Eq1Equivalence (PureRelASPPairArr I) (Monad_PureRelASPPairArr I)
    (@Eq1_PureRelASPPairArr I) :=
  @Eq1Equivalence_Arrow PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowApply_PureRelASPPairArr ArrowEq_PureRelASPPairArr I.

(** Compact relational descriptions of return and bind. *)

Definition ret_ASP {I A} (a : A) : PureRelASPPairArr I A :=
  mkASP (fun _ a' => a = a').

(** For the angelic bind, we extract the underlying relation directly
    via [rel (proj1_sig ...)], mirroring the demonic bind. *)
Definition bind_ASP {I A B}
    (m : PureRelASPPairArr I A) (k : A -> PureRelASPPairArr I B)
    : PureRelASPPairArr I B :=
  mkASP (fun i c => exists b,
           rel (proj1_sig m) i b /\
           rel (proj1_sig (k b)) i c).

Lemma ret_ASP_eq_ret_arrow {I A} (a : A) :
  @arrow_eq PureRelASPPairArr ArrowEq_PureRelASPPairArr I A
    (ret_ASP a) (@ret_arrow PureRelASPPairArr Arrow_PureRelASPPairArr I A a).
Proof. apply RelSPPairArr.ASP_rel_ext; intros i b. reflexivity. Qed.

Lemma bind_ASP_eq_bind_arrow {I A B}
    (m : PureRelASPPairArr I A) (k : A -> PureRelASPPairArr I B) :
  @arrow_eq PureRelASPPairArr ArrowEq_PureRelASPPairArr I B
    (bind_ASP m k)
    (@bind_arrow PureRelASPPairArr Arrow_PureRelASPPairArr
      ArrowApply_PureRelASPPairArr I A B m k).
Proof.
  autounfold with sp_arrow_bind.
  rewrite (@first_pure PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowEq_PureRelASPPairArr ArrowLaws_PureRelASPPairArr).
  repeat rewrite (@pure_comp PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowEq_PureRelASPPairArr ArrowLaws_PureRelASPPairArr).
  apply RelSPPairArr.ASP_rel_ext; intros i c. cbn. split.
  - intros [b [Hm Hk]]. exists (b, i). split.
    + exists (i, i). split; [reflexivity |].
      exists (b, i). cbn [swap]. auto.
    + exists (k b, i). cbn. auto.
  - intros [p [[p0 [Hp0 [p1 [Hm Hp]]]] [p2 [Hp2 Hk]]]].
    subst p0. destruct p1 as [b i']. cbn [swap] in Hp. subst p.
    cbn in Hm, Hp2. destruct Hm as [Hm Hi]. subst i' p2.
    exists b. exact (conj Hm Hk).
Qed.

Definition MonadLawsE_PureRelASPPairArr (I : Type)
  : @MonadLawsE (PureRelASPPairArr I) (@Eq1_PureRelASPPairArr I)
    (Monad_PureRelASPPairArr I) :=
  @MonadLawsE_Arrow PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowApply_PureRelASPPairArr ArrowEq_PureRelASPPairArr
    ArrowLaws_PureRelASPPairArr ArrowApplyLaws_PureRelASPPairArr I.

(** Demonic. *)

Definition Monad_PureRelDSLPPairArr (I : Type)
  : Monad (PureRelDSLPPairArr I) :=
  @Monad_Arrow PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
    ArrowApply_PureRelDSLPPairArr I.

Definition Eq1Equivalence_PureRelDSLPPairArr (I : Type)
  : @Eq1Equivalence (PureRelDSLPPairArr I) (Monad_PureRelDSLPPairArr I)
    (@Eq1_PureRelDSLPPairArr I) :=
  @Eq1Equivalence_Arrow PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
    ArrowApply_PureRelDSLPPairArr ArrowEq_PureRelDSLPPairArr I.

Definition ret_DSLP {I A} (a : A) : PureRelDSLPPairArr I A :=
  mkDSLP (fun _ a' => a = a').

(** For the demonic bind, we extract the underlying relation directly
    via [rel (proj1_sig ...)], avoiding classical axioms. *)
Definition bind_DSLP {I A B}
    (m : PureRelDSLPPairArr I A) (k : A -> PureRelDSLPPairArr I B)
    : PureRelDSLPPairArr I B :=
  mkDSLP (fun i c => exists b,
            rel (proj1_sig m) i b /\
            rel (proj1_sig (k b)) i c).

Lemma ret_DSLP_eq_ret_arrow {I A} (a : A) :
  @arrow_eq PureRelDSLPPairArr ArrowEq_PureRelDSLPPairArr I A
    (ret_DSLP a) (@ret_arrow PureRelDSLPPairArr Arrow_PureRelDSLPPairArr I A a).
Proof. apply RelSPPairArr.DSLP_rel_ext; intros i b. reflexivity. Qed.

Lemma bind_DSLP_eq_bind_arrow {I A B}
    (m : PureRelDSLPPairArr I A) (k : A -> PureRelDSLPPairArr I B) :
  @arrow_eq PureRelDSLPPairArr ArrowEq_PureRelDSLPPairArr I B
    (bind_DSLP m k)
    (@bind_arrow PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
      ArrowApply_PureRelDSLPPairArr I A B m k).
Proof.
  autounfold with sp_arrow_bind.
  rewrite (@first_pure PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
    ArrowEq_PureRelDSLPPairArr ArrowLaws_PureRelDSLPPairArr).
  repeat rewrite (@pure_comp PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
    ArrowEq_PureRelDSLPPairArr ArrowLaws_PureRelDSLPPairArr).
  apply RelSPPairArr.DSLP_rel_ext; intros i c. cbn. split.
  - intros [b [Hm Hk]]. exists (b, i). split.
    + exists (i, i). split; [reflexivity |].
      exists (b, i). cbn [swap]. auto.
    + exists (k b, i). cbn. auto.
  - intros [p [[p0 [Hp0 [p1 [Hm Hp]]]] [p2 [Hp2 Hk]]]].
    subst p0. destruct p1 as [b i']. cbn [swap] in Hp. subst p.
    cbn in Hm, Hp2. destruct Hm as [Hm Hi]. subst i' p2.
    exists b. exact (conj Hm Hk).
Qed.

Lemma proj_mkDSLP {J B} (R : PredArr J B) pre b :
  spost (proj1_sig (mkDSLP R)) pre b <-> dslp R pre b.
Proof. reflexivity. Qed.

Definition MonadLawsE_PureRelDSLPPairArr (I : Type)
  : @MonadLawsE (PureRelDSLPPairArr I) (@Eq1_PureRelDSLPPairArr I)
    (Monad_PureRelDSLPPairArr I) :=
  @MonadLawsE_Arrow PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
    ArrowApply_PureRelDSLPPairArr ArrowEq_PureRelDSLPPairArr
    ArrowLaws_PureRelDSLPPairArr ArrowApplyLaws_PureRelDSLPPairArr I.

(* ================================================================= *)
(** ** Resolution checks                                               *)
(* ================================================================= *)

(** The concrete bundle must reuse the generic dictionary itself. *)
Example coupled_asp_reuses_arrow (I : Type) :
  @Monad_PureRelASPPairArr I =
  @Monad_Arrow PureRelASPPairArr Arrow_PureRelASPPairArr
    ArrowApply_PureRelASPPairArr I.
Proof. reflexivity. Qed.

(** These monads are inferred without naming the concrete aliases.  The
    equalities check both automatic resolution and the public alias bodies. *)
Definition inferred_pred_monad : Monad (PredArr bool) := _.
Definition inferred_prepost_monad : Monad (PrePostArr bool) := _.
Definition inferred_relprepost_monad : Monad (RelPrePostArr bool) := _.
Definition inferred_asp_monad : Monad (PureRelASPPairArr bool) := _.
Definition inferred_dslp_monad : Monad (PureRelDSLPPairArr bool) := _.

Example pred_reuses_arrow :
  inferred_pred_monad = @Monad_Pred bool /\
  @Monad_Pred bool = @Monad_Arrow PredArr Arrow_Pred ArrowApply_Pred bool.
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

Example asp_resolution_uses_arrow :
  inferred_asp_monad = @Monad_PureRelASPPairArr bool /\
  @Monad_PureRelASPPairArr bool =
    @Monad_Arrow PureRelASPPairArr Arrow_PureRelASPPairArr
      ArrowApply_PureRelASPPairArr bool.
Proof. split; reflexivity. Qed.

Example dslp_reuses_arrow :
  inferred_dslp_monad = @Monad_PureRelDSLPPairArr bool /\
  @Monad_PureRelDSLPPairArr bool =
    @Monad_Arrow PureRelDSLPPairArr Arrow_PureRelDSLPPairArr
      ArrowApply_PureRelDSLPPairArr bool.
Proof. split; reflexivity. Qed.

(** Canonical concrete equalities must resolve the generic law instances. *)
Definition pred_canonical_laws :
  @MonadLawsE (PredArr bool) (@Eq1_Pred bool) inferred_pred_monad := _.
Definition prepost_canonical_laws :
  @MonadLawsE (PrePostArr bool) (@Eq1_PrePost bool) inferred_prepost_monad := _.
Definition relprepost_canonical_laws :
  @MonadLawsE (RelPrePostArr bool) (@Eq1_RelPrePost bool)
    inferred_relprepost_monad := _.
Definition asp_canonical_laws :
  @MonadLawsE (PureRelASPPairArr bool)
    (@Eq1_PureRelASPPairArr bool) inferred_asp_monad := _.
Definition dslp_canonical_laws :
  @MonadLawsE (PureRelDSLPPairArr bool)
    (@Eq1_PureRelDSLPPairArr bool) inferred_dslp_monad := _.

Definition pred_canonical_equivalence :
  @Eq1Equivalence (PredArr bool) inferred_pred_monad (@Eq1_Pred bool) := _.
Definition prepost_canonical_equivalence :
  @Eq1Equivalence (PrePostArr bool) inferred_prepost_monad (@Eq1_PrePost bool) := _.
Definition relprepost_canonical_equivalence :
  @Eq1Equivalence (RelPrePostArr bool) inferred_relprepost_monad
    (@Eq1_RelPrePost bool) := _.
Definition asp_canonical_equivalence :
  @Eq1Equivalence (PureRelASPPairArr bool) inferred_asp_monad
    (@Eq1_PureRelASPPairArr bool) := _.
Definition dslp_canonical_equivalence :
  @Eq1Equivalence (PureRelDSLPPairArr bool) inferred_dslp_monad
    (@Eq1_PureRelDSLPPairArr bool) := _.

(** Pointwise arrow equalities, rather than Leibniz equality. *)
Definition pred_monad_laws :
  @MonadLawsE (PredArr bool)
    (@Eq1_Arrow _ ArrowEq_Pred bool)
    (@Monad_Arrow _ Arrow_Pred ArrowApply_Pred bool) := _.

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

(** Coupled demonic-liberal arrows exercise the other SP presentation. *)
Definition coupled_dslp_monad_laws :
  @MonadLawsE (PureRelDSLPPairArr bool)
    (@Eq1_Arrow _ ArrowEq_PureRelDSLPPairArr bool)
    (@Monad_Arrow _ Arrow_PureRelDSLPPairArr
      ArrowApply_PureRelDSLPPairArr bool) := _.

Definition coupled_option_dslp_monad_laws :
  @MonadLawsE (RelSPPairArr.optionDSLPArr bool)
    (@Eq1_Arrow _ (@ArrowEq_optionArrT _ ArrowEq_PureRelDSLPPairArr) bool)
    (@Monad_Arrow _ (@Arrow_optionArrT _ Arrow_PureRelDSLPPairArr
        ArrowChoice_PureRelDSLPPairArr)
      (@ArrowApply_optionArrT _ Arrow_PureRelDSLPPairArr
        ArrowChoice_PureRelDSLPPairArr
        ArrowApply_PureRelDSLPPairArr) bool) := _.

Definition coupled_state_dslp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S PureRelDSLPPairArr bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S _ ArrowEq_PureRelDSLPPairArr) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _ Arrow_PureRelDSLPPairArr)
      (@ArrowApply_stateArrT S _ Arrow_PureRelDSLPPairArr
        ArrowApply_PureRelDSLPPairArr) bool) := _.

(** The state-over-option stack is spelled with the generic transformer
    dictionaries applied to the coupled base: no per-stack instances
    are registered for this presentation. *)
Definition coupled_state_option_dslp_monad_laws (S : Type) :
  @MonadLawsE (stateArrT S RelSPPairArr.optionDSLPArr bool)
    (@Eq1_Arrow _ (@ArrowEq_stateArrT S RelSPPairArr.optionDSLPArr
        (@ArrowEq_optionArrT _ ArrowEq_PureRelDSLPPairArr)) bool)
    (@Monad_Arrow _ (@Arrow_stateArrT S _
        (@Arrow_optionArrT _ Arrow_PureRelDSLPPairArr
          ArrowChoice_PureRelDSLPPairArr))
      (@ArrowApply_stateArrT S _
        (@Arrow_optionArrT _ Arrow_PureRelDSLPPairArr
          ArrowChoice_PureRelDSLPPairArr)
        (@ArrowApply_optionArrT _ Arrow_PureRelDSLPPairArr
          ArrowChoice_PureRelDSLPPairArr
          ArrowApply_PureRelDSLPPairArr)) bool) := _.

(** The named monad dictionaries of [SPostArrMonad] alias the same
    property-only stacks.  Typeclass resolution does not see through the
    aliases, so the generic law instance is named explicitly, at
    arbitrary state. *)
Definition spostarr_asp_monad_laws (S : Type) :
  @MonadLawsE (SPostArr.ASPostArr S)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptASP S) unit)
    (Monad_ASPostArr S) :=
  @MonadLawsE_Arrow (stateArrT S SPostArr.optionASPArr)
    (SPostArr.Arrow_stateOptASP S) (SPostArr.ArrowApply_stateOptASP S)
    (SPostArr.ArrowEq_stateOptASP S) (SPostArr.ArrowLaws_stateOptASP S)
    (SPostArr.ArrowApplyLaws_stateOptASP S) unit.

Definition spostarr_dslp_monad_laws (S : Type) :
  @MonadLawsE (SPostArr.DSLPostArr S)
    (@Eq1_Arrow _ (SPostArr.ArrowEq_stateOptDSLP S) unit)
    (Monad_DSLPostArr S) :=
  @MonadLawsE_Arrow (stateArrT S SPostArr.optionDSLPArr)
    (SPostArr.Arrow_stateOptDSLP S) (SPostArr.ArrowApply_stateOptDSLP S)
    (SPostArr.ArrowEq_stateOptDSLP S) (SPostArr.ArrowLaws_stateOptDSLP S)
    (SPostArr.ArrowApplyLaws_stateOptDSLP S) unit.
