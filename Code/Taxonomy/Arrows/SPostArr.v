(** * Property-only strongest-postcondition arrows.

    Compatibility names reuse the canonical ASP/DSLP carriers and operations.
    The carriers contain only predicate transformers and healthiness proofs.
    Constructive normal forms support reasoning; no relation is stored. *)

From Coq Require Import FunctionalExtensionality PropExtensionality RelationClasses Morphisms.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Export ArrowMonad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT ArrowMorphism RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Taxonomy.Arrows Require Export PredicateTransformerProperties.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPArrowCore ASPArrowRel DSLPArrowCore DSLPArrowRel.

Definition PureASPostArr (A B : Type) : Type :=
  ASPArr A B.

Definition PureDSLPostArr (A B : Type) : Type :=
  DSLPArr A B.

Definition getASP {A B} (f : PureASPostArr A B) : (A -> Prop) -> B -> Prop :=
  proj1_sig f.

Definition getDSLP {A B} (f : PureDSLPostArr A B) : (A -> Prop) -> B -> Prop :=
  proj1_sig f.

Lemma ASP_strict {A B} (f : PureASPostArr A B) : StrictArr (getASP f).
Proof. exact (proj1 (proj2 (proj2_sig f))). Qed.

Lemma ASP_disjunctive {A B} (f : PureASPostArr A B) :
  DisjunctiveArr (getASP f).
Proof. exact (proj2 (proj2 (proj2_sig f))). Qed.

Lemma DSLP_terminating {A B} (f : PureDSLPostArr A B) :
  TerminatingArr (getDSLP f).
Proof. exact (proj1 (proj2 (proj2_sig f))). Qed.

Lemma DSLP_conjunctive {A B} (f : PureDSLPostArr A B) :
  ConjunctiveArr (getDSLP f).
Proof. exact (proj2 (proj2 (proj2_sig f))). Qed.

Lemma ASP_monotone {A B} (f : PureASPostArr A B) P Q b :
  (forall a, P a -> Q a) -> getASP f P b -> getASP f Q b.
Proof. exact (getASPArr_mono f P Q b). Qed.

Lemma DSLP_monotone {A B} (f : PureDSLPostArr A B) P Q b :
  (forall a, P a -> Q a) -> getDSLP f P b -> getDSLP f Q b.
Proof. exact (getDSLPArr_mono f P Q b). Qed.

Lemma ASP_full_join {A B} (f : PureASPostArr A B)
  (I : Type) (p : I -> A -> Prop) b :
  getASP f (fun a => exists i, p i a) b <-> exists i, getASP f (p i) b.
Proof.
  rewrite getASPArr_join. split.
  - intros [a [[i HP] Hr]]. exists i. apply getASPArr_join. exists a. auto.
  - intros [i H]. apply getASPArr_join in H. destruct H as [a [HP Hr]].
    exists a. split; [exists i; exact HP | exact Hr].
Qed.

Lemma DSLP_full_meet {A B} (f : PureDSLPostArr A B)
  (I : Type) (p : I -> A -> Prop) b :
  getDSLP f (fun a => forall i, p i a) b <-> forall i, getDSLP f (p i) b.
Proof.
  rewrite getDSLPArr_meet. split.
  - intros H i. apply getDSLPArr_meet. intros a Hr. exact (H a Hr i).
  - intros H a Hr i. exact (proj1 (getDSLPArr_meet f (p i) b) (H i) a Hr).
Qed.

(** Canonical representations reuse constructive singleton joins and
    accepted-predicate meets; no extensionality or excluded middle is needed. *)
Theorem ASP_normal_form {A B} (f : PureASPostArr A B) P b :
  getASP f P b <-> exists a, P a /\ getASP f (eq a) b.
Proof.
  rewrite (getASPArr_join f). split.
  - intros [a [HP H]]. exists a. split; [exact HP |].
    eapply getASPArr_ext; [|exact H]. intro x. split; symmetry; assumption.
  - intros [a [HP H]]. exists a. split; [exact HP |].
    eapply getASPArr_ext; [|exact H]. intro x. split; symmetry; assumption.
Qed.

Theorem DSLP_normal_form {A B} (f : PureDSLPostArr A B) P b :
  getDSLP f P b <-> forall a, (forall Q, getDSLP f Q b -> Q a) -> P a.
Proof.
  exact (getDSLPArr_meet f P b).
Qed.

Lemma PureASPostArr_eq {A B} (f g : PureASPostArr A B) :
  (forall P b, getASP f P b <-> getASP g P b) -> f = g.
Proof.
  destruct f as [f Hf], g as [g Hg]. cbn. intro H.
  assert (HE : f = g).
  { extensionality P. extensionality b. apply propositional_extensionality, H. }
  subst. f_equal. apply proof_irrelevance.
Qed.

Lemma PureDSLPostArr_eq {A B} (f g : PureDSLPostArr A B) :
  (forall P b, getDSLP f P b <-> getDSLP g P b) -> f = g.
Proof.
  destruct f as [f Hf], g as [g Hg]. cbn. intro H.
  assert (HE : f = g).
  { extensionality P. extensionality b. apply propositional_extensionality, H. }
  subst. f_equal. apply proof_irrelevance.
Qed.

(** ** Canonical operations under compatibility names *)

Local Obligation Tactic := idtac.

Definition arrASP := @ASPArrowCore.pureASP.
Definition compASP := @ASPArrowCore.compASP.
Definition firstASP := @ASPArrowCore.firstASP.
Definition leftASP := @ASPArrowCore.leftASP.
Definition appASP := @ASPArrowCore.appASP.
Definition arrDSLP := @DSLPArrowCore.pureDSLP.
Definition compDSLP := @DSLPArrowCore.compDSLP.
Definition firstDSLP := @DSLPArrowCore.firstDSLP.
Definition leftDSLP := @DSLPArrowCore.leftDSLP.
Definition appDSLP := @DSLPArrowCore.appDSLP.
Arguments arrASP {A B} _.
Arguments compASP {A B C} _ _.
Arguments firstASP {A B C} _.
Arguments leftASP {A B C} _.
Arguments appASP {A B}.
Arguments arrDSLP {A B} _.
Arguments compDSLP {A B C} _ _.
Arguments firstDSLP {A B C} _.
Arguments leftDSLP {A B C} _.
Arguments appDSLP {A B}.

Definition Arrow_PureASPostArr : Arrow PureASPostArr := Arrow_ASPArr.
Definition Arrow_PureDSLPostArr : Arrow PureDSLPostArr := Arrow_DSLPArr.
Definition ArrowChoice_PureASPostArr := ArrowChoice_ASPArr.
Definition ArrowChoice_PureDSLPostArr := ArrowChoice_DSLPArr.
Definition ArrowApply_PureASPostArr := ArrowApply_ASPArr.
Definition ArrowApply_PureDSLPostArr := ArrowApply_DSLPArr.

Definition arrow_eq_ASP {A B} (f g : PureASPostArr A B) : Prop :=
  forall P b, getASP f P b <-> getASP g P b.

Lemma arrow_eq_ASP_equiv A B : Equivalence (@arrow_eq_ASP A B).
Proof.
  constructor.
  - intros f P b. reflexivity.
  - intros f g H P b. symmetry. apply H.
  - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
Qed.

Definition ArrowEq_PureASPostArr : ArrowEq PureASPostArr := ArrowEq_ASPArr.

Definition arrow_eq_DSLP {A B} (f g : PureDSLPostArr A B) : Prop :=
  forall P b, getDSLP f P b <-> getDSLP g P b.

Lemma arrow_eq_DSLP_equiv A B : Equivalence (@arrow_eq_DSLP A B).
Proof.
  constructor.
  - intros f P b. reflexivity.
  - intros f g H P b. symmetry. apply H.
  - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
Qed.

Definition ArrowEq_PureDSLPostArr : ArrowEq PureDSLPostArr := ArrowEq_DSLPArr.

#[global] Instance Proper_getASP {A B} :
  Proper (arrow_eq ==> eq ==> eq ==> iff) (@getASP A B).
Proof.
  intros f g H P ? <- b ? <-. apply H.
Qed.

#[global] Instance Proper_getDSLP {A B} :
  Proper (arrow_eq ==> eq ==> eq ==> iff) (@getDSLP A B).
Proof.
  intros f g H P ? <- b ? <-. apply H.
Qed.

(** Public computational seams: lifting a function is its direct or
    universal image, and composition is transformer composition. *)
Lemma arrASP_spec {A B} (h : A -> B) P b :
  getASP (arrASP h) P b <-> exists a, P a /\ h a = b.
Proof. reflexivity. Qed.

Lemma arrDSLP_spec {A B} (h : A -> B) P b :
  getDSLP (arrDSLP h) P b <-> forall a, h a = b -> P a.
Proof. reflexivity. Qed.

Lemma compASP_spec {A B C} (f : PureASPostArr A B) (g : PureASPostArr B C) P c :
  getASP (compASP f g) P c <-> getASP g (getASP f P) c.
Proof. reflexivity. Qed.

Lemma compDSLP_spec {A B C} (f : PureDSLPostArr A B) (g : PureDSLPostArr B C) P c :
  getDSLP (compDSLP f g) P c <-> getDSLP g (getDSLP f P) c.
Proof. reflexivity. Qed.

Lemma firstASP_spec {A B C} (f : PureASPostArr A B) P b (c : C) :
  getASP (firstASP f) P (b, c) <-> getASP f (fun a => P (a, c)) b.
Proof. reflexivity. Qed.

Lemma firstDSLP_spec {A B C} (f : PureDSLPostArr A B) P b (c : C) :
  getDSLP (firstDSLP f) P (b, c) <-> getDSLP f (fun a => P (a, c)) b.
Proof. reflexivity. Qed.

Lemma leftASP_spec {A B C} (f : PureASPostArr A B) P (bc : B + C) :
  getASP (leftASP f) P bc <->
  match bc with inl b => getASP f (fun a => P (inl a)) b | inr c => P (inr c) end.
Proof. destruct bc; reflexivity. Qed.

Lemma leftDSLP_spec {A B C} (f : PureDSLPostArr A B) P (bc : B + C) :
  getDSLP (leftDSLP f) P bc <->
  match bc with inl b => getDSLP f (fun a => P (inl a)) b | inr c => P (inr c) end.
Proof. destruct bc; reflexivity. Qed.

Lemma appASP_spec {A B} (P : PureASPostArr A B * A -> Prop) b :
  getASP appASP P b <-> exists f, getASP f (fun a => P (f, a)) b.
Proof.
  change ((exists f a, P (f, a) /\ getASP f (fun x => x = a) b) <->
    exists f, getASP f (fun a => P (f, a)) b). split.
  - intros [f [a [HP H]]]. exists f. apply getASPArr_join. exists a. auto.
  - intros [f H]. apply getASPArr_join in H. destruct H as [a [HP H]].
    exists f, a. auto.
Qed.

Lemma appDSLP_spec {A B} (P : PureDSLPostArr A B * A -> Prop) b :
  getDSLP appDSLP P b <-> forall f, getDSLP f (fun a => P (f, a)) b.
Proof.
  change ((forall f a, dslpRelT (getDSLPArr f) a b -> P (f, a)) <->
    forall f, getDSLP f (fun a => P (f, a)) b). split.
  - intros H f. apply getDSLPArr_meet. intros a Hr. exact (H f a Hr).
  - intros H f a Hr. exact (proj1 (getDSLPArr_meet f _ b) (H f) a Hr).
Qed.

(** ** Recovered relations, constructors, and round trips

    These derived witnesses and relation constructors allow the property-only
    arrows to interface with relational descriptions, existential rewrite normal
    forms, and generic semantic coherence packages. *)

Definition ASP_rel {A B} (f : PureASPostArr A B) a b : Prop :=
  getASP f (eq a) b.

Definition DSLP_rel {A B} (f : PureDSLPostArr A B) a b : Prop :=
  forall Q, getDSLP f Q b -> Q a.

Definition relASP := @ofRelASPArr.
Definition relDSLP := @ofRelDSLPArr.
Arguments relASP {A B} _.
Arguments relDSLP {A B} _.

Lemma getASP_relASP {A B} (R : A -> B -> Prop) P b :
  getASP (relASP R) P b <-> exists a, P a /\ R a b.
Proof. reflexivity. Qed.

Lemma getDSLP_relDSLP {A B} (R : A -> B -> Prop) P b :
  getDSLP (relDSLP R) P b <-> forall a, R a b -> P a.
Proof. reflexivity. Qed.

Lemma ASP_rel_relASP {A B} (R : A -> B -> Prop) a b :
  ASP_rel (relASP R) a b <-> R a b.
Proof.
  unfold ASP_rel. rewrite getASP_relASP. split.
  - intros [a' [Heq HR]]. subst a'. exact HR.
  - intro HR. exists a. split; [reflexivity | exact HR].
Qed.

(** Any universal relational representation recovers its relation
    constructively: the forward direction chooses [Q := R (_, b)]. *)
Lemma DSLP_rel_of_representation {A B} (f : PureDSLPostArr A B)
  (R : A -> B -> Prop)
  (HR : forall Q b, getDSLP f Q b <-> forall a, R a b -> Q a) a b :
  DSLP_rel f a b <-> R a b.
Proof.
  unfold DSLP_rel. split.
  - intro H. apply (H (fun a' => R a' b)). apply HR. auto.
  - intros Hab Q HQ. exact (proj1 (HR Q b) HQ a Hab).
Qed.

Lemma DSLP_rel_relDSLP {A B} (R : A -> B -> Prop) a b :
  DSLP_rel (relDSLP R) a b <-> R a b.
Proof.
  apply (DSLP_rel_of_representation _ R).
  exact (getDSLP_relDSLP R).
Qed.

Lemma relASP_ASP_rel {A B} (f : PureASPostArr A B) :
  relASP (ASP_rel f) = f.
Proof.
  apply PureASPostArr_eq. intros P b.
  rewrite getASP_relASP. symmetry. apply ASP_normal_form.
Qed.

Lemma arrow_eq_relASP_ASP_rel {A B} (f : PureASPostArr A B) :
  arrow_eq (relASP (ASP_rel f)) f.
Proof.
  intros P b. rewrite getASP_relASP. symmetry. apply ASP_normal_form.
Qed.

Lemma relDSLP_DSLP_rel {A B} (f : PureDSLPostArr A B) :
  relDSLP (DSLP_rel f) = f.
Proof.
  apply PureDSLPostArr_eq. intros P b.
  rewrite getDSLP_relDSLP. symmetry. apply DSLP_normal_form.
Qed.

Lemma arrow_eq_relDSLP_DSLP_rel {A B} (f : PureDSLPostArr A B) :
  arrow_eq (relDSLP (DSLP_rel f)) f.
Proof.
  intros P b. rewrite getDSLP_relDSLP. symmetry. apply DSLP_normal_form.
Qed.

(** Existentially packaged normal forms are convenient for repeated rewriting
    without unfolding the canonical singleton/intersection predicates. *)
Lemma IsASP_rewrite {A B} (f : PureASPostArr A B) :
  exists R : A -> B -> Prop,
    forall P b, getASP f P b <-> exists a, P a /\ R a b.
Proof.
  exists (ASP_rel f). apply ASP_normal_form.
Qed.

Lemma IsDSLP_rewrite {A B} (f : PureDSLPostArr A B) :
  exists R : A -> B -> Prop,
    forall P b, getDSLP f P b <-> forall a, R a b -> P a.
Proof.
  exists (DSLP_rel f). apply DSLP_normal_form.
Qed.

Lemma ASP_arrow_eq_rel {A B} (f g : PureASPostArr A B) :
  arrow_eq f g <-> (forall a b, ASP_rel f a b <-> ASP_rel g a b).
Proof.
  split.
  - intros H a b. apply (H (eq a) b).
  - intros Hrel P b.
    rewrite (ASP_normal_form f), (ASP_normal_form g).
    split; intros [a [HP Hr]]; exists a; split; [exact HP | apply Hrel, Hr | exact HP | apply Hrel, Hr].
Qed.

Lemma DSLP_arrow_eq_rel {A B} (f g : PureDSLPostArr A B) :
  arrow_eq f g <-> (forall a b, DSLP_rel f a b <-> DSLP_rel g a b).
Proof.
  split.
  - intros H a b. unfold DSLP_rel.
    split; intros HQ Q Hq; apply HQ; [apply H | apply H]; exact Hq.
  - intros Hrel P b.
    rewrite (DSLP_normal_form f), (DSLP_normal_form g).
    split; intros H a Hr; apply H; apply Hrel; exact Hr.
Qed.

Lemma ASP_rel_ext {A B} (f g : PureASPostArr A B) :
  (forall a b, ASP_rel f a b <-> ASP_rel g a b) -> f = g.
Proof.
  intro Hrel. apply PureASPostArr_eq. intros Q b.
  rewrite (ASP_normal_form f), (ASP_normal_form g).
  split; intros [a [HQ Hr]]; exists a; split.
  - exact HQ.
  - apply Hrel. exact Hr.
  - exact HQ.
  - apply Hrel. exact Hr.
Qed.

Lemma DSLP_rel_ext {A B} (f g : PureDSLPostArr A B) :
  (forall a b, DSLP_rel f a b <-> DSLP_rel g a b) -> f = g.
Proof.
  intro Hrel. apply PureDSLPostArr_eq. intros Q b.
  rewrite (DSLP_normal_form f), (DSLP_normal_form g).
  split; intros H a Hr; apply H; apply Hrel; exact Hr.
Qed.

(** ** Demonic relation semantics

    Each direct transformer is put into a universal relational normal
    form, then [DSLP_rel_of_representation] recovers that relation. *)

Lemma DSLP_rel_pure {A B} (h : A -> B) a b :
  DSLP_rel (arrDSLP h) a b <-> @arr_pure Rel Arrow_Rel _ _ h a b.
Proof.
  apply (DSLP_rel_of_representation (arrDSLP h) (fun a b => h a = b)).
  intros Q b'. apply arrDSLP_spec.
Qed.

Lemma DSLP_rel_comp {A B C}
  (f : PureDSLPostArr A B) (g : PureDSLPostArr B C) a c :
  DSLP_rel (compDSLP f g) a c <->
  @arr_comp Rel Arrow_Rel _ _ _ (DSLP_rel f) (DSLP_rel g) a c.
Proof.
  apply (DSLP_rel_of_representation (compDSLP f g)
    (fun a c => exists b, DSLP_rel f a b /\ DSLP_rel g b c)).
  intros Q c'. rewrite compDSLP_spec, (DSLP_normal_form g).
  split.
  - intros H a' [b [Hf Hg]]. exact (Hf Q (H b Hg)).
  - intros H b Hg. apply DSLP_normal_form. intros a' Hf.
    apply H. exists b. split; assumption.
Qed.

Lemma DSLP_rel_first {A B C} (f : PureDSLPostArr A B) a (c : C) b d :
  DSLP_rel (firstDSLP f) (a, c) (b, d) <->
  @arr_first Rel Arrow_Rel _ _ _ (DSLP_rel f) (a, c) (b, d).
Proof.
  apply (DSLP_rel_of_representation (firstDSLP f)
    (fun '(a, c) '(b, d) => DSLP_rel f a b /\ c = d))
    with (a := (a, c)) (b := (b, d)).
  intros Q [b' d']. rewrite firstDSLP_spec, (DSLP_normal_form f).
  split.
  - intros H [a' c'] [Hf Heq]. cbn in Heq. subst c'. exact (H a' Hf).
  - intros H a' Hf. apply (H (a', d')). split; [exact Hf | reflexivity].
Qed.

Lemma DSLP_rel_left {A B C} (f : PureDSLPostArr A B)
  (x : A + C) (y : B + C) :
  DSLP_rel (leftDSLP f) x y <->
  @arr_left Rel Arrow_Rel ArrowChoice_Rel _ _ _ (DSLP_rel f) x y.
Proof.
  apply (DSLP_rel_of_representation (leftDSLP f)
    (fun x y => match x, y with
      | inl a, inl b => DSLP_rel f a b
      | inr c, inr d => c = d
      | _, _ => False
      end)) with (a := x) (b := y).
  intros Q [b|d]; rewrite leftDSLP_spec; cbn.
  - rewrite (DSLP_normal_form f). split.
    + intros H [a|c] Hr; [exact (H a Hr) | contradiction].
    + intros H a Hr. exact (H (inl a) Hr).
  - split.
    + intros HQ [a|c] Hr; [contradiction | subst c; exact HQ].
    + intro H. exact (H (inr d) eq_refl).
Qed.

Lemma DSLP_rel_app {A B} (f : PureDSLPostArr A B) a b :
  DSLP_rel appDSLP (f, a) b <-> DSLP_rel f a b.
Proof.
  apply (DSLP_rel_of_representation appDSLP
    (fun '(f, a) b => DSLP_rel f a b)) with (a := (f, a)) (b := b).
  intros Q b'. rewrite appDSLP_spec. split.
  - intros H [f' a'] Hr. exact (Hr (fun a => Q (f', a)) (H f')).
  - intros H f'. apply DSLP_normal_form. intros a' Hr.
    exact (H (f', a') Hr).
Qed.

(** ** Angelic relation semantics *)

Lemma ASP_rel_pure {A B} (h : A -> B) a b :
  ASP_rel (arrASP h) a b <-> @arr_pure Rel Arrow_Rel _ _ h a b.
Proof.
  unfold ASP_rel. rewrite arrASP_spec. split.
  - intros [a' [<- Hh]]. exact Hh.
  - intro Hh. exists a. split; [reflexivity | exact Hh].
Qed.

Lemma ASP_rel_comp {A B C}
  (f : PureASPostArr A B) (g : PureASPostArr B C) a c :
  ASP_rel (compASP f g) a c <->
  @arr_comp Rel Arrow_Rel _ _ _ (ASP_rel f) (ASP_rel g) a c.
Proof.
  unfold ASP_rel. rewrite compASP_spec, (ASP_normal_form g).
  reflexivity.
Qed.

Lemma ASP_rel_first {A B C} (f : PureASPostArr A B) a (c : C) b d :
  ASP_rel (firstASP f) (a, c) (b, d) <->
  @arr_first Rel Arrow_Rel _ _ _ (ASP_rel f) (a, c) (b, d).
Proof.
  unfold ASP_rel. rewrite firstASP_spec, (ASP_normal_form f).
  split.
  - intros [a' [Heq Hr]]. injection Heq as <- <-. split; [exact Hr | reflexivity].
  - intros [Hr ->]. exists a. split; [reflexivity | exact Hr].
Qed.

Lemma ASP_rel_left {A B C} (f : PureASPostArr A B)
  (x : A + C) (y : B + C) :
  ASP_rel (leftASP f) x y <->
  @arr_left Rel Arrow_Rel ArrowChoice_Rel _ _ _ (ASP_rel f) x y.
Proof.
  unfold ASP_rel. destruct x as [a|c], y as [b|d];
    rewrite leftASP_spec; cbn.
  - rewrite (ASP_normal_form f). split.
    + intros [a' [Heq Hr]]. injection Heq as <-. exact Hr.
    + intro Hr. exists a. split; [reflexivity | exact Hr].
  - split; [intro H; discriminate H | contradiction].
  - rewrite (ASP_normal_form f). split.
    + intros [a [Heq _]]. discriminate Heq.
    + contradiction.
  - split.
    + intro H. injection H as H. exact H.
    + intros ->. reflexivity.
Qed.

Lemma ASP_rel_app {A B} (f : PureASPostArr A B) a b :
  ASP_rel appASP (f, a) b <-> ASP_rel f a b.
Proof.
  unfold ASP_rel. rewrite appASP_spec. split.
  - intros [f' H]. rewrite (ASP_normal_form f') in H.
    destruct H as [a' [Heq Hr]]. injection Heq as <- <-. exact Hr.
  - intro Hr. exists f. rewrite (ASP_normal_form f).
    exists a. split; [reflexivity | exact Hr].
Qed.

(** ** Generic semantic instances and derived law packages *)

Definition RelArrow_PureASPostArr : RelArrow PureASPostArr := {|
  rel_reading := @ASP_rel;
  rel_pure := @ASP_rel_pure;
  rel_comp := @ASP_rel_comp;
  rel_first := @ASP_rel_first;
|}.

Definition RelArrowChoice_PureASPostArr :
  @RelArrowChoice PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr RelArrow_PureASPostArr :=
  @Build_RelArrowChoice PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr
    RelArrow_PureASPostArr (@ASP_rel_left).

Definition RelArrowApply_PureASPostArr :
  @RelArrowApply PureASPostArr Arrow_PureASPostArr ArrowApply_PureASPostArr RelArrow_PureASPostArr :=
  @Build_RelArrowApply PureASPostArr Arrow_PureASPostArr ArrowApply_PureASPostArr
    RelArrow_PureASPostArr (@ASP_rel_app).

Definition RelArrowEq_PureASPostArr :
  @RelArrowEq PureASPostArr Arrow_PureASPostArr ArrowEq_PureASPostArr RelArrow_PureASPostArr :=
  @Build_RelArrowEq PureASPostArr Arrow_PureASPostArr ArrowEq_PureASPostArr
    RelArrow_PureASPostArr (@ASP_arrow_eq_rel).

Definition ArrowLaws_PureASPostArr :
  ArrowLaws PureASPostArr := ArrowLaws_ASPArr.

Definition ArrowChoiceLaws_PureASPostArr :
  ArrowChoiceLaws PureASPostArr := ArrowChoiceLaws_ASPArr.

Definition ArrowApplyLaws_PureASPostArr :
  ArrowApplyLaws PureASPostArr := ArrowApplyLaws_ASPArr.

Definition RelArrow_PureDSLPostArr : RelArrow PureDSLPostArr := {|
  rel_reading := @DSLP_rel;
  rel_pure := @DSLP_rel_pure;
  rel_comp := @DSLP_rel_comp;
  rel_first := @DSLP_rel_first;
|}.

Definition RelArrowChoice_PureDSLPostArr :
  @RelArrowChoice PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr RelArrow_PureDSLPostArr :=
  @Build_RelArrowChoice PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    RelArrow_PureDSLPostArr (@DSLP_rel_left).

Definition RelArrowApply_PureDSLPostArr :
  @RelArrowApply PureDSLPostArr Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr RelArrow_PureDSLPostArr :=
  @Build_RelArrowApply PureDSLPostArr Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr
    RelArrow_PureDSLPostArr (@DSLP_rel_app).

Definition RelArrowEq_PureDSLPostArr :
  @RelArrowEq PureDSLPostArr Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr RelArrow_PureDSLPostArr :=
  @Build_RelArrowEq PureDSLPostArr Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr
    RelArrow_PureDSLPostArr (@DSLP_arrow_eq_rel).

Definition ArrowLaws_PureDSLPostArr :
  ArrowLaws PureDSLPostArr := ArrowLaws_DSLPArr.

Definition ArrowChoiceLaws_PureDSLPostArr :
  ArrowChoiceLaws PureDSLPostArr := ArrowChoiceLaws_DSLPArr.

Definition ArrowApplyLaws_PureDSLPostArr :
  ArrowApplyLaws PureDSLPostArr := ArrowApplyLaws_DSLPArr.

Lemma ArrowLaws_PureASPostArr_leibniz :
  @ArrowLaws PureASPostArr Arrow_PureASPostArr (ArrowEq_leibniz PureASPostArr).
Proof.
  exact (rel_arrow_laws_leibniz (fun A B f g H => @PureASPostArr_eq A B f g H) ArrowLaws_PureASPostArr).
Qed.

Lemma ArrowChoiceLaws_PureASPostArr_leibniz :
  @ArrowChoiceLaws PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr
    (ArrowEq_leibniz PureASPostArr).
Proof.
  exact (rel_arrow_choice_laws_leibniz (fun A B f g H => @PureASPostArr_eq A B f g H) ArrowChoiceLaws_PureASPostArr).
Qed.

Lemma ArrowLaws_PureDSLPostArr_leibniz :
  @ArrowLaws PureDSLPostArr Arrow_PureDSLPostArr (ArrowEq_leibniz PureDSLPostArr).
Proof.
  exact (rel_arrow_laws_leibniz (fun A B f g H => @PureDSLPostArr_eq A B f g H) ArrowLaws_PureDSLPostArr).
Qed.

Lemma ArrowChoiceLaws_PureDSLPostArr_leibniz :
  @ArrowChoiceLaws PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    (ArrowEq_leibniz PureDSLPostArr).
Proof.
  exact (rel_arrow_choice_laws_leibniz (fun A B f g H => @PureDSLPostArr_eq A B f g H) ArrowChoiceLaws_PureDSLPostArr).
Qed.

Definition ASP_rel_presentation :
  RelArrowCoherence.RelArrowPresentation PureASPostArr
    Arrow_PureASPostArr ArrowChoice_PureASPostArr
    ArrowApply_PureASPostArr := {|
  RelArrowCoherence.present_rel := @ASP_rel;
  RelArrowCoherence.present_ext := @ASP_rel_ext;
  RelArrowCoherence.present_pure := @ASP_rel_pure;
  RelArrowCoherence.present_comp := @ASP_rel_comp;
  RelArrowCoherence.present_first := @ASP_rel_first;
  RelArrowCoherence.present_left := @ASP_rel_left;
  RelArrowCoherence.present_app := @ASP_rel_app
|}.

Definition DSLP_rel_presentation :
  RelArrowCoherence.RelArrowPresentation PureDSLPostArr
    Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    ArrowApply_PureDSLPostArr := {|
  RelArrowCoherence.present_rel := @DSLP_rel;
  RelArrowCoherence.present_ext := @DSLP_rel_ext;
  RelArrowCoherence.present_pure := @DSLP_rel_pure;
  RelArrowCoherence.present_comp := @DSLP_rel_comp;
  RelArrowCoherence.present_first := @DSLP_rel_first;
  RelArrowCoherence.present_left := @DSLP_rel_left;
  RelArrowCoherence.present_app := @DSLP_rel_app
|}.

(** ** Option and state stacks

    Explicit dictionaries keep the two recursive transformer instances from
    competing during typeclass search.  All stack laws are generic lifts. *)

Definition optionASPArr := optionArrT PureASPostArr.
Definition optionDSLPArr := optionArrT PureDSLPostArr.

Definition ASPostArr (S B : Type) : Type := stateArrT S optionASPArr unit B.
Definition DSLPostArr (S B : Type) : Type := stateArrT S optionDSLPArr unit B.

Definition Arrow_optionASPArr : Arrow optionASPArr :=
  @Arrow_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr.
Definition ArrowEq_optionASPArr : ArrowEq optionASPArr :=
  @ArrowEq_optionArrT PureASPostArr ArrowEq_PureASPostArr.
Definition ArrowChoice_optionASPArr :
  @ArrowChoice optionASPArr Arrow_optionASPArr :=
  @ArrowChoice_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr.
Definition ArrowApply_optionASPArr :
  @ArrowApply optionASPArr Arrow_optionASPArr :=
  @ArrowApply_optionArrT PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr.
Definition ArrowLaws_optionASPArr :
  @ArrowLaws optionASPArr Arrow_optionASPArr ArrowEq_optionASPArr :=
  @ArrowLaws_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr
    ArrowEq_PureASPostArr ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr.
Definition ArrowChoiceLaws_optionASPArr :
  @ArrowChoiceLaws optionASPArr Arrow_optionASPArr
    ArrowChoice_optionASPArr ArrowEq_optionASPArr :=
  @ArrowChoiceLaws_optionArrT PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowEq_PureASPostArr
    ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr.
Definition ArrowApplyLaws_optionASPArr :
  @ArrowApplyLaws optionASPArr Arrow_optionASPArr
    ArrowApply_optionASPArr ArrowEq_optionASPArr :=
  @ArrowApplyLaws_optionArrT PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr ArrowEq_PureASPostArr
    ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr ArrowApplyLaws_PureASPostArr.

Definition Arrow_optionDSLPArr : Arrow optionDSLPArr :=
  @Arrow_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr.
Definition ArrowEq_optionDSLPArr : ArrowEq optionDSLPArr :=
  @ArrowEq_optionArrT PureDSLPostArr ArrowEq_PureDSLPostArr.
Definition ArrowChoice_optionDSLPArr :
  @ArrowChoice optionDSLPArr Arrow_optionDSLPArr :=
  @ArrowChoice_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr.
Definition ArrowApply_optionDSLPArr :
  @ArrowApply optionDSLPArr Arrow_optionDSLPArr :=
  @ArrowApply_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr.
Definition ArrowLaws_optionDSLPArr :
  @ArrowLaws optionDSLPArr Arrow_optionDSLPArr ArrowEq_optionDSLPArr :=
  @ArrowLaws_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    ArrowEq_PureDSLPostArr ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr.
Definition ArrowChoiceLaws_optionDSLPArr :
  @ArrowChoiceLaws optionDSLPArr Arrow_optionDSLPArr
    ArrowChoice_optionDSLPArr ArrowEq_optionDSLPArr :=
  @ArrowChoiceLaws_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowEq_PureDSLPostArr
    ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr.
Definition ArrowApplyLaws_optionDSLPArr :
  @ArrowApplyLaws optionDSLPArr Arrow_optionDSLPArr
    ArrowApply_optionDSLPArr ArrowEq_optionDSLPArr :=
  @ArrowApplyLaws_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr ArrowEq_PureDSLPostArr
    ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr.

Section StateOptionInstances.
  Variable S : Type.

  Definition Arrow_stateOptASP : Arrow (stateArrT S optionASPArr) :=
    @Arrow_stateArrT S optionASPArr Arrow_optionASPArr.
  Definition ArrowEq_stateOptASP : ArrowEq (stateArrT S optionASPArr) :=
    @ArrowEq_stateArrT S optionASPArr ArrowEq_optionASPArr.
  Definition ArrowChoice_stateOptASP :
    @ArrowChoice (stateArrT S optionASPArr) Arrow_stateOptASP :=
    @ArrowChoice_stateArrT S optionASPArr Arrow_optionASPArr ArrowChoice_optionASPArr.
  Definition ArrowApply_stateOptASP :
    @ArrowApply (stateArrT S optionASPArr) Arrow_stateOptASP :=
    @ArrowApply_stateArrT S optionASPArr Arrow_optionASPArr ArrowApply_optionASPArr.
  Definition ArrowLaws_stateOptASP :
    @ArrowLaws (stateArrT S optionASPArr) Arrow_stateOptASP ArrowEq_stateOptASP :=
    @ArrowLaws_stateArrT S optionASPArr Arrow_optionASPArr
      ArrowEq_optionASPArr ArrowLaws_optionASPArr.
  Definition ArrowChoiceLaws_stateOptASP :
    @ArrowChoiceLaws (stateArrT S optionASPArr) Arrow_stateOptASP
      ArrowChoice_stateOptASP ArrowEq_stateOptASP :=
    @ArrowChoiceLaws_stateArrT S optionASPArr Arrow_optionASPArr
      ArrowChoice_optionASPArr ArrowEq_optionASPArr
      ArrowLaws_optionASPArr ArrowChoiceLaws_optionASPArr.
  Definition ArrowApplyLaws_stateOptASP :
    @ArrowApplyLaws (stateArrT S optionASPArr) Arrow_stateOptASP
      ArrowApply_stateOptASP ArrowEq_stateOptASP :=
    @ArrowApplyLaws_stateArrT S optionASPArr Arrow_optionASPArr
      ArrowApply_optionASPArr ArrowEq_optionASPArr
      ArrowLaws_optionASPArr ArrowApplyLaws_optionASPArr.

  Definition Arrow_stateOptDSLP : Arrow (stateArrT S optionDSLPArr) :=
    @Arrow_stateArrT S optionDSLPArr Arrow_optionDSLPArr.
  Definition ArrowEq_stateOptDSLP : ArrowEq (stateArrT S optionDSLPArr) :=
    @ArrowEq_stateArrT S optionDSLPArr ArrowEq_optionDSLPArr.
  Definition ArrowChoice_stateOptDSLP :
    @ArrowChoice (stateArrT S optionDSLPArr) Arrow_stateOptDSLP :=
    @ArrowChoice_stateArrT S optionDSLPArr Arrow_optionDSLPArr ArrowChoice_optionDSLPArr.
  Definition ArrowApply_stateOptDSLP :
    @ArrowApply (stateArrT S optionDSLPArr) Arrow_stateOptDSLP :=
    @ArrowApply_stateArrT S optionDSLPArr Arrow_optionDSLPArr ArrowApply_optionDSLPArr.
  Definition ArrowLaws_stateOptDSLP :
    @ArrowLaws (stateArrT S optionDSLPArr) Arrow_stateOptDSLP ArrowEq_stateOptDSLP :=
    @ArrowLaws_stateArrT S optionDSLPArr Arrow_optionDSLPArr
      ArrowEq_optionDSLPArr ArrowLaws_optionDSLPArr.
  Definition ArrowChoiceLaws_stateOptDSLP :
    @ArrowChoiceLaws (stateArrT S optionDSLPArr) Arrow_stateOptDSLP
      ArrowChoice_stateOptDSLP ArrowEq_stateOptDSLP :=
    @ArrowChoiceLaws_stateArrT S optionDSLPArr Arrow_optionDSLPArr
      ArrowChoice_optionDSLPArr ArrowEq_optionDSLPArr
      ArrowLaws_optionDSLPArr ArrowChoiceLaws_optionDSLPArr.
  Definition ArrowApplyLaws_stateOptDSLP :
    @ArrowApplyLaws (stateArrT S optionDSLPArr) Arrow_stateOptDSLP
      ArrowApply_stateOptDSLP ArrowEq_stateOptDSLP :=
    @ArrowApplyLaws_stateArrT S optionDSLPArr Arrow_optionDSLPArr
      ArrowApply_optionDSLPArr ArrowEq_optionDSLPArr
      ArrowLaws_optionDSLPArr ArrowApplyLaws_optionDSLPArr.
End StateOptionInstances.

(** ** Stack semantics

    At the option layer, [None] propagates through composition.  The state
    layer uses exactly these equations on state-indexed inputs and outputs. *)

Lemma optionASP_pure_spec {A B} (h : A -> B) P r :
  getASP (@arr_pure optionASPArr Arrow_optionASPArr A B h) P r <->
  exists a, P a /\ Some (h a) = r.
Proof. reflexivity. Qed.

Lemma optionDSLP_pure_spec {A B} (h : A -> B) P r :
  getDSLP (@arr_pure optionDSLPArr Arrow_optionDSLPArr A B h) P r <->
  forall a, Some (h a) = r -> P a.
Proof. reflexivity. Qed.

Lemma optionASP_comp_spec {A B C}
  (f : optionASPArr A B) (g : optionASPArr B C) P r :
  getASP (@arr_comp optionASPArr Arrow_optionASPArr A B C f g) P r <->
  (getASP f P None /\ r = None) \/
  getASP g (fun b => getASP f P (Some b)) r.
Proof.
  cbn. unfold leftASPT. destruct (IsASP_rewrite g) as [R HR]. unfold getASP, getASPArr in *. split.
  - intros [[r0|[]] [H Heq]]; cbn in Heq; subst.
    + right. rewrite HR in H |- *. destruct H as [b [[ob [Hb Heq]] Hg]].
      destruct ob as [b0|]; cbn in Heq; [|discriminate].
      injection Heq as Heq. subst. exists b. auto.
    + left. split; [|reflexivity].
      destruct H as [[b|] [H Heq]]; [discriminate|exact H].
  - intros [[H ->]|H].
    + exists (inr tt). split; [exists None; auto | reflexivity].
    + exists (inl r). split; [|reflexivity].
      rewrite HR in H |- *. destruct H as [b [Hb Hg]].
      exists b. split; [exists (Some b); auto | exact Hg].
Qed.

Lemma optionDSLP_comp_spec {A B C}
  (f : optionDSLPArr A B) (g : optionDSLPArr B C) P r :
  getDSLP (@arr_comp optionDSLPArr Arrow_optionDSLPArr A B C f g) P r <->
  (r = None -> getDSLP f P None) /\
  getDSLP g (fun b => getDSLP f P (Some b)) r.
Proof.
  cbn. unfold leftDSLPT. destruct (IsDSLP_rewrite g) as [R HR]. unfold getDSLP, getDSLPArr in *. split.
  - intro H. split.
    + intro Heq. subst. exact (H (inr tt) eq_refl None eq_refl).
    + rewrite HR. intros b Hb.
      assert (Hg := H (inl r) eq_refl). cbn in Hg. rewrite HR in Hg.
      exact (Hg b Hb (Some b) eq_refl).
  - intros [Hnone Hg] [r0|[]] Heq; cbn in Heq; subst.
    + rewrite HR in Hg |- *. intros b Hb [b0|] Heq; cbn in Heq;
        [|discriminate].
      injection Heq as Heq. subst. exact (Hg b Hb).
    + intros [b|] Heq; [discriminate|apply Hnone; reflexivity].
Qed.

Lemma optionASP_app_spec {A B} (P : optionASPArr A B * A -> Prop) r :
  getASP (@arr_app optionASPArr Arrow_optionASPArr ArrowApply_optionASPArr A B) P r
  <-> exists f, getASP f (fun a => P (f, a)) r.
Proof. apply appASP_spec. Qed.

Lemma optionDSLP_app_spec {A B} (P : optionDSLPArr A B * A -> Prop) r :
  getDSLP (@arr_app optionDSLPArr Arrow_optionDSLPArr ArrowApply_optionDSLPArr A B) P r
  <-> forall f, getDSLP f (fun a => P (f, a)) r.
Proof. apply appDSLP_spec. Qed.

Lemma stateOptASP_pure_spec {S A B} (h : A -> B) P r :
  getASP (@arr_pure (stateArrT S optionASPArr) (Arrow_stateOptASP S) A B h) P r
  <-> exists a s, P (a, s) /\ Some (h a, s) = r.
Proof. cbn. sauto limit: 200. Qed.

Lemma stateOptDSLP_pure_spec {S A B} (h : A -> B) P r :
  getDSLP (@arr_pure (stateArrT S optionDSLPArr) (Arrow_stateOptDSLP S) A B h) P r
  <-> forall a s, Some (h a, s) = r -> P (a, s).
Proof. cbn. sauto limit: 200. Qed.

Lemma stateOptASP_comp_spec {S A B C}
  (f : stateArrT S optionASPArr A B) (g : stateArrT S optionASPArr B C) P r :
  getASP (@arr_comp (stateArrT S optionASPArr) (Arrow_stateOptASP S) A B C f g) P r
  <-> (getASP f P None /\ r = None) \/
      getASP g (fun bs => getASP f P (Some bs)) r.
Proof. apply optionASP_comp_spec. Qed.

Lemma stateOptDSLP_comp_spec {S A B C}
  (f : stateArrT S optionDSLPArr A B) (g : stateArrT S optionDSLPArr B C) P r :
  getDSLP (@arr_comp (stateArrT S optionDSLPArr) (Arrow_stateOptDSLP S) A B C f g) P r
  <-> (r = None -> getDSLP f P None) /\
      getDSLP g (fun bs => getDSLP f P (Some bs)) r.
Proof. apply optionDSLP_comp_spec. Qed.

Lemma stateOptASP_app_spec {S A B}
  (P : (stateArrT S optionASPArr A B * A) * S -> Prop) r :
  getASP (@arr_app (stateArrT S optionASPArr) (Arrow_stateOptASP S)
    (ArrowApply_stateOptASP S) A B) P r <->
  exists f : stateArrT S optionASPArr A B,
    getASP f (fun '(a, s) => P ((f, a), s)) r.
Proof.
  change (getASP (@arr_comp optionASPArr Arrow_optionASPArr _ _ _
    (@arr_pure optionASPArr Arrow_optionASPArr _ _
      (fun '((f, a), s) => (f, (a, s))))
    (@arr_app optionASPArr Arrow_optionASPArr ArrowApply_optionASPArr _ _)) P r <->
    exists f : stateArrT S optionASPArr A B,
      getASP f (fun '(a, s) => P ((f, a), s)) r).
  rewrite optionASP_comp_spec, optionASP_app_spec. cbn. split.
  - intros [[[p [_ Heq]] _]|[f H]]; [discriminate|].
    exists f. eapply ASP_monotone; [|exact H].
    intros [a s] [[[f0 a0] s0] [HP Heq]]. injection Heq as Hf Ha Hs. subst.
    exact HP.
  - intros [f H]. right. exists f. eapply ASP_monotone; [|exact H].
    intros [a s] HP. exists ((f, a), s). auto.
Qed.

Lemma stateOptDSLP_app_spec {S A B}
  (P : (stateArrT S optionDSLPArr A B * A) * S -> Prop) r :
  getDSLP (@arr_app (stateArrT S optionDSLPArr) (Arrow_stateOptDSLP S)
    (ArrowApply_stateOptDSLP S) A B) P r <->
  forall f : stateArrT S optionDSLPArr A B,
    getDSLP f (fun '(a, s) => P ((f, a), s)) r.
Proof.
  change (getDSLP (@arr_comp optionDSLPArr Arrow_optionDSLPArr _ _ _
    (@arr_pure optionDSLPArr Arrow_optionDSLPArr _ _
      (fun '((f, a), s) => (f, (a, s))))
    (@arr_app optionDSLPArr Arrow_optionDSLPArr ArrowApply_optionDSLPArr _ _)) P r <->
    forall f : stateArrT S optionDSLPArr A B,
      getDSLP f (fun '(a, s) => P ((f, a), s)) r).
  rewrite optionDSLP_comp_spec, optionDSLP_app_spec. cbn. split.
  - intros [_ H] f. eapply DSLP_monotone; [|exact (H f)].
    intros [a s] Ha. exact (Ha ((f, a), s) eq_refl).
  - intro H. split.
    + intros _ p Heq. discriminate.
    + intro f. eapply DSLP_monotone; [|exact (H f)].
      intros [a s] HP [[f0 a0] s0] Heq. injection Heq as Hf Ha Hs. subst.
      exact HP.
Qed.
