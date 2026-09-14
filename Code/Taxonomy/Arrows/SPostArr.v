(** * Property-only strongest-postcondition arrows.

    The carriers contain only predicate transformers and well-formedness proofs.
    All operations act directly on transformers.  Canonical normal forms are
    derived below for reasoning; no relation is stored in either carrier. *)

From Coq Require Import FunctionalExtensionality PropExtensionality RelationClasses Morphisms.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Export ArrowMonad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT ArrowMorphism RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import Rel.
From Incorrectness.Taxonomy.Arrows Require Export PredicateTransformerProperties.

Definition PureASPostArr (A B : Type) : Type :=
  { w : (A -> Prop) -> B -> Prop | StrictArr w /\ DisjunctiveArr w }.

Definition PureDSLPostArr (A B : Type) : Type :=
  { w : (A -> Prop) -> B -> Prop | TerminatingArr w /\ ConjunctiveArr w }.

Definition getASP {A B} (f : PureASPostArr A B) : (A -> Prop) -> B -> Prop :=
  proj1_sig f.

Definition getDSLP {A B} (f : PureDSLPostArr A B) : (A -> Prop) -> B -> Prop :=
  proj1_sig f.

Lemma ASP_strict {A B} (f : PureASPostArr A B) : StrictArr (getASP f).
Proof. exact (proj1 (proj2_sig f)). Qed.

Lemma ASP_disjunctive {A B} (f : PureASPostArr A B) :
  DisjunctiveArr (getASP f).
Proof. exact (proj2 (proj2_sig f)). Qed.

Lemma DSLP_terminating {A B} (f : PureDSLPostArr A B) :
  TerminatingArr (getDSLP f).
Proof. exact (proj1 (proj2_sig f)). Qed.

Lemma DSLP_conjunctive {A B} (f : PureDSLPostArr A B) :
  ConjunctiveArr (getDSLP f).
Proof. exact (proj2 (proj2_sig f)). Qed.

Lemma ASP_monotone {A B} (f : PureASPostArr A B) P Q b :
  (forall a, P a -> Q a) -> getASP f P b -> getASP f Q b.
Proof. apply disjunctiveArr_monotone, ASP_disjunctive. Qed.

Lemma DSLP_monotone {A B} (f : PureDSLPostArr A B) P Q b :
  (forall a, P a -> Q a) -> getDSLP f P b -> getDSLP f Q b.
Proof. apply conjunctiveArr_monotone, DSLP_conjunctive. Qed.

Lemma ASP_full_join {A B} (f : PureASPostArr A B)
  (I : Type) (p : I -> A -> Prop) b :
  getASP f (fun a => exists i, p i a) b <-> exists i, getASP f (p i) b.
Proof.
  apply strict_disjunctiveArr_full_join; [apply ASP_strict | apply ASP_disjunctive].
Qed.

Lemma DSLP_full_meet {A B} (f : PureDSLPostArr A B)
  (I : Type) (p : I -> A -> Prop) b :
  getDSLP f (fun a => forall i, p i a) b <-> forall i, getDSLP f (p i) b.
Proof.
  apply terminating_conjunctiveArr_full_meet;
    [apply DSLP_terminating | apply DSLP_conjunctive].
Qed.

(** Canonical representations follow from full joins/meets, including empty
    families.  Their proofs use extensionality, without excluded middle. *)
Theorem ASP_normal_form {A B} (f : PureASPostArr A B) P b :
  getASP f P b <-> exists a, P a /\ getASP f (eq a) b.
Proof.
  assert (HE : P = (fun a' => exists a : {a : A | P a}, proj1_sig a = a')).
  { extensionality a'. apply propositional_extensionality. split.
    - intro HP. exists (exist _ a' HP). reflexivity.
    - intros [[a HP] Heq]. cbn in Heq. subst. exact HP. }
  split.
  - intro H. rewrite HE in H. apply ASP_full_join in H.
    destruct H as [[a HP] H]. exists a. auto.
  - intros [a [HP H]]. rewrite HE. apply ASP_full_join.
    exists (exist _ a HP). exact H.
Qed.

Theorem DSLP_normal_form {A B} (f : PureDSLPostArr A B) P b :
  getDSLP f P b <-> forall a, (forall Q, getDSLP f Q b -> Q a) -> P a.
Proof.
  split.
  - intros H a Ha. exact (Ha P H).
  - intro H.
    assert (HM : getDSLP f
      (fun a => forall Q : {Q : A -> Prop | getDSLP f Q b}, proj1_sig Q a) b).
    { apply DSLP_full_meet. intros [Q HQ]. exact HQ. }
    eapply DSLP_monotone; [|exact HM].
    intros a Ha. apply H. intros Q HQ. exact (Ha (exist _ Q HQ)).
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

(** ** Direct operations and their well-formedness proofs *)

Local Obligation Tactic := idtac.

#[program] Definition arrASP {A B} (h : A -> B) : PureASPostArr A B :=
  fun P b => exists a, P a /\ h a = b.
Next Obligation.
  intros A B h. split.
  - intros b [a [H _]]. exact H.
  - intros I HI p b. split.
    + intros [a [[i H] Heq]]. exists i, a. auto.
    + intros [i [a [H Heq]]]. exists a. split; [exists i; exact H | exact Heq].
Qed.

#[program] Definition compASP {A B C}
  (f : PureASPostArr A B) (g : PureASPostArr B C) : PureASPostArr A C :=
  fun P c => getASP g (getASP f P) c.
Next Obligation.
  intros A B C f g. split.
  - intros c H. apply (ASP_strict g c).
    eapply ASP_monotone; [|exact H]. intros b Hb. exact (ASP_strict f b Hb).
  - intros I HI p c.
    assert (HE : getASP f (fun a => exists i, p i a) =
      (fun b => exists i, getASP f (p i) b)).
    { extensionality b. apply propositional_extensionality, ASP_disjunctive, HI. }
    rewrite HE. apply ASP_disjunctive, HI.
Qed.

#[program] Definition firstASP {A B C} (f : PureASPostArr A B) :
  PureASPostArr (A * C) (B * C) :=
  fun P '(b, c) => getASP f (fun a => P (a, c)) b.
Next Obligation.
  intros A B C f. split.
  - intros [b c]. apply ASP_strict.
  - intros I HI p [b c]. apply ASP_disjunctive, HI.
Qed.

#[program] Definition leftASP {A B C} (f : PureASPostArr A B) :
  PureASPostArr (A + C) (B + C) :=
  fun P bc => match bc with
    | inl b => getASP f (fun a => P (inl a)) b
    | inr c => P (inr c)
    end.
Next Obligation.
  intros A B C f. split.
  - intros [b|c]; [apply ASP_strict | tauto].
  - intros I HI p [b|c]; [apply ASP_disjunctive, HI | reflexivity].
Qed.

#[program] Definition appASP {A B} : PureASPostArr (PureASPostArr A B * A) B :=
  fun P b => exists f : PureASPostArr A B, getASP f (fun a => P (f, a)) b.
Next Obligation.
  intros A B. split.
  - intros b [f H]. exact (ASP_strict f b H).
  - intros I HI p b. split.
    + intros [f H]. apply (ASP_disjunctive f I HI) in H.
      destruct H as [i H]. exists i, f. exact H.
    + intros [i [f H]]. exists f. apply (ASP_disjunctive f I HI).
      exists i. exact H.
Qed.

#[program] Definition arrDSLP {A B} (h : A -> B) : PureDSLPostArr A B :=
  fun P b => forall a, h a = b -> P a.
Next Obligation.
  intros A B h. split.
  - intros b a Heq. constructor.
  - intros I HI p b. split.
    + intros H i a Heq. exact (H a Heq i).
    + intros H a Heq i. exact (H i a Heq).
Qed.

#[program] Definition compDSLP {A B C}
  (f : PureDSLPostArr A B) (g : PureDSLPostArr B C) : PureDSLPostArr A C :=
  fun P c => getDSLP g (getDSLP f P) c.
Next Obligation.
  intros A B C f g. split.
  - intro c. eapply DSLP_monotone; [|apply DSLP_terminating].
    intros b _. apply DSLP_terminating.
  - intros I HI p c.
    assert (HE : getDSLP f (fun a => forall i, p i a) =
      (fun b => forall i, getDSLP f (p i) b)).
    { extensionality b. apply propositional_extensionality, DSLP_conjunctive, HI. }
    rewrite HE. apply DSLP_conjunctive, HI.
Qed.

#[program] Definition firstDSLP {A B C} (f : PureDSLPostArr A B) :
  PureDSLPostArr (A * C) (B * C) :=
  fun P '(b, c) => getDSLP f (fun a => P (a, c)) b.
Next Obligation.
  intros A B C f. split.
  - intros [b c]. apply DSLP_terminating.
  - intros I HI p [b c]. apply DSLP_conjunctive, HI.
Qed.

#[program] Definition leftDSLP {A B C} (f : PureDSLPostArr A B) :
  PureDSLPostArr (A + C) (B + C) :=
  fun P bc => match bc with
    | inl b => getDSLP f (fun a => P (inl a)) b
    | inr c => P (inr c)
    end.
Next Obligation.
  intros A B C f. split.
  - intros [b|c]; [apply DSLP_terminating | constructor].
  - intros I HI p [b|c]; [apply DSLP_conjunctive, HI | reflexivity].
Qed.

#[program] Definition appDSLP {A B} :
  PureDSLPostArr (PureDSLPostArr A B * A) B :=
  fun P b => (forall f : PureDSLPostArr A B, getDSLP f (fun a => P (f, a)) b).
Next Obligation.
  intros A B. split.
  - intros b f. apply DSLP_terminating.
  - intros I HI p b. split.
    + intros H i f. exact (proj1 (DSLP_conjunctive f I HI _ b) (H f) i).
    + intros H f. apply (DSLP_conjunctive f I HI). intro i. exact (H i f).
Qed.

#[global] Instance Arrow_PureASPostArr : Arrow PureASPostArr := {
  arr_pure := @arrASP; arr_comp := @compASP; arr_first := @firstASP
}.

#[global] Instance Arrow_PureDSLPostArr : Arrow PureDSLPostArr := {
  arr_pure := @arrDSLP; arr_comp := @compDSLP; arr_first := @firstDSLP
}.

#[global] Instance ArrowChoice_PureASPostArr :
  @ArrowChoice PureASPostArr Arrow_PureASPostArr := { arr_left := @leftASP }.

#[global] Instance ArrowChoice_PureDSLPostArr :
  @ArrowChoice PureDSLPostArr Arrow_PureDSLPostArr := { arr_left := @leftDSLP }.

#[global] Instance ArrowApply_PureASPostArr :
  @ArrowApply PureASPostArr Arrow_PureASPostArr := { arr_app := @appASP }.

#[global] Instance ArrowApply_PureDSLPostArr :
  @ArrowApply PureDSLPostArr Arrow_PureDSLPostArr := { arr_app := @appDSLP }.

Definition arrow_eq_ASP {A B} (f g : PureASPostArr A B) : Prop :=
  forall P b, getASP f P b <-> getASP g P b.

Lemma arrow_eq_ASP_equiv A B : Equivalence (@arrow_eq_ASP A B).
Proof.
  constructor.
  - intros f P b. reflexivity.
  - intros f g H P b. symmetry. apply H.
  - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
Qed.

#[global] Instance ArrowEq_PureASPostArr : ArrowEq PureASPostArr := {
  arrow_eq := @arrow_eq_ASP;
  arrow_eq_equiv := arrow_eq_ASP_equiv
}.

Definition arrow_eq_DSLP {A B} (f g : PureDSLPostArr A B) : Prop :=
  forall P b, getDSLP f P b <-> getDSLP g P b.

Lemma arrow_eq_DSLP_equiv A B : Equivalence (@arrow_eq_DSLP A B).
Proof.
  constructor.
  - intros f P b. reflexivity.
  - intros f g H P b. symmetry. apply H.
  - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
Qed.

#[global] Instance ArrowEq_PureDSLPostArr : ArrowEq PureDSLPostArr := {
  arrow_eq := @arrow_eq_DSLP;
  arrow_eq_equiv := arrow_eq_DSLP_equiv
}.

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
Proof. reflexivity. Qed.

Lemma appDSLP_spec {A B} (P : PureDSLPostArr A B * A -> Prop) b :
  getDSLP appDSLP P b <-> forall f, getDSLP f (fun a => P (f, a)) b.
Proof. reflexivity. Qed.

(** ** Recovered relations, constructors, and round trips

    These derived witnesses and relation constructors allow the property-only
    arrows to interface with relational descriptions, existential rewrite normal
    forms, and generic semantic coherence packages. *)

Definition ASP_rel {A B} (f : PureASPostArr A B) a b : Prop :=
  getASP f (eq a) b.

Definition DSLP_rel {A B} (f : PureDSLPostArr A B) a b : Prop :=
  forall Q, getDSLP f Q b -> Q a.

#[program] Definition relASP {A B} (R : A -> B -> Prop) : PureASPostArr A B :=
  fun P b => exists a, P a /\ R a b.
Next Obligation.
  intros A B R. split.
  - intros b [a [HF _]]. exact HF.
  - intros I HI p b. split.
    + intros [a [[i H] HR]]. exists i, a. auto.
    + intros [i [a [H HR]]]. exists a. split; [exists i; exact H | exact HR].
Qed.

#[program] Definition relDSLP {A B} (R : A -> B -> Prop) : PureDSLPostArr A B :=
  fun P b => forall a, R a b -> P a.
Next Obligation.
  intros A B R. split.
  - intros b a _. exact I.
  - intros I HI p b. split.
    + intros H i a Heq. exact (H a Heq i).
    + intros H a Heq i. exact (H i a Heq).
Qed.

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

#[global] Instance RelArrow_PureASPostArr : RelArrow PureASPostArr := {
  rel_reading := @ASP_rel;
  rel_pure := @ASP_rel_pure;
  rel_comp := @ASP_rel_comp;
  rel_first := @ASP_rel_first;
}.

#[global] Instance RelArrowChoice_PureASPostArr :
  RelArrowChoice PureASPostArr := {
  rel_left := @ASP_rel_left;
}.

#[global] Instance RelArrowApply_PureASPostArr :
  RelArrowApply PureASPostArr := {
  rel_app := @ASP_rel_app;
}.

#[global] Instance RelArrowEq_PureASPostArr :
  RelArrowEq PureASPostArr := {|
  rel_arrow_eq := @ASP_arrow_eq_rel;
|}.

#[global] Instance ArrowLaws_PureASPostArr :
  ArrowLaws PureASPostArr := rel_arrow_laws.

#[global] Instance ArrowChoiceLaws_PureASPostArr :
  ArrowChoiceLaws PureASPostArr := rel_arrow_choice_laws.

#[global] Instance ArrowApplyLaws_PureASPostArr :
  ArrowApplyLaws PureASPostArr := rel_arrow_apply_laws.

#[global] Instance RelArrow_PureDSLPostArr : RelArrow PureDSLPostArr := {
  rel_reading := @DSLP_rel;
  rel_pure := @DSLP_rel_pure;
  rel_comp := @DSLP_rel_comp;
  rel_first := @DSLP_rel_first;
}.

#[global] Instance RelArrowChoice_PureDSLPostArr :
  RelArrowChoice PureDSLPostArr := {
  rel_left := @DSLP_rel_left;
}.

#[global] Instance RelArrowApply_PureDSLPostArr :
  RelArrowApply PureDSLPostArr := {
  rel_app := @DSLP_rel_app;
}.

#[global] Instance RelArrowEq_PureDSLPostArr :
  RelArrowEq PureDSLPostArr := {|
  rel_arrow_eq := @DSLP_arrow_eq_rel;
|}.

#[global] Instance ArrowLaws_PureDSLPostArr :
  ArrowLaws PureDSLPostArr := rel_arrow_laws.

#[global] Instance ArrowChoiceLaws_PureDSLPostArr :
  ArrowChoiceLaws PureDSLPostArr := rel_arrow_choice_laws.

#[global] Instance ArrowApplyLaws_PureDSLPostArr :
  ArrowApplyLaws PureDSLPostArr := rel_arrow_apply_laws.

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

#[global] Instance Arrow_optionASPArr : Arrow optionASPArr :=
  @Arrow_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr.
#[global] Instance ArrowEq_optionASPArr : ArrowEq optionASPArr :=
  @ArrowEq_optionArrT PureASPostArr ArrowEq_PureASPostArr.
#[global] Instance ArrowChoice_optionASPArr :
  @ArrowChoice optionASPArr Arrow_optionASPArr :=
  @ArrowChoice_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr.
#[global] Instance ArrowApply_optionASPArr :
  @ArrowApply optionASPArr Arrow_optionASPArr :=
  @ArrowApply_optionArrT PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr.
#[global] Instance ArrowLaws_optionASPArr :
  @ArrowLaws optionASPArr Arrow_optionASPArr ArrowEq_optionASPArr :=
  @ArrowLaws_optionArrT PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr
    ArrowEq_PureASPostArr ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr.
#[global] Instance ArrowChoiceLaws_optionASPArr :
  @ArrowChoiceLaws optionASPArr Arrow_optionASPArr
    ArrowChoice_optionASPArr ArrowEq_optionASPArr :=
  @ArrowChoiceLaws_optionArrT PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowEq_PureASPostArr
    ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr.
#[global] Instance ArrowApplyLaws_optionASPArr :
  @ArrowApplyLaws optionASPArr Arrow_optionASPArr
    ArrowApply_optionASPArr ArrowEq_optionASPArr :=
  @ArrowApplyLaws_optionArrT PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowApply_PureASPostArr ArrowEq_PureASPostArr
    ArrowLaws_PureASPostArr ArrowChoiceLaws_PureASPostArr ArrowApplyLaws_PureASPostArr.

#[global] Instance Arrow_optionDSLPArr : Arrow optionDSLPArr :=
  @Arrow_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr.
#[global] Instance ArrowEq_optionDSLPArr : ArrowEq optionDSLPArr :=
  @ArrowEq_optionArrT PureDSLPostArr ArrowEq_PureDSLPostArr.
#[global] Instance ArrowChoice_optionDSLPArr :
  @ArrowChoice optionDSLPArr Arrow_optionDSLPArr :=
  @ArrowChoice_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr.
#[global] Instance ArrowApply_optionDSLPArr :
  @ArrowApply optionDSLPArr Arrow_optionDSLPArr :=
  @ArrowApply_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr.
#[global] Instance ArrowLaws_optionDSLPArr :
  @ArrowLaws optionDSLPArr Arrow_optionDSLPArr ArrowEq_optionDSLPArr :=
  @ArrowLaws_optionArrT PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    ArrowEq_PureDSLPostArr ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr.
#[global] Instance ArrowChoiceLaws_optionDSLPArr :
  @ArrowChoiceLaws optionDSLPArr Arrow_optionDSLPArr
    ArrowChoice_optionDSLPArr ArrowEq_optionDSLPArr :=
  @ArrowChoiceLaws_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowEq_PureDSLPostArr
    ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr.
#[global] Instance ArrowApplyLaws_optionDSLPArr :
  @ArrowApplyLaws optionDSLPArr Arrow_optionDSLPArr
    ArrowApply_optionDSLPArr ArrowEq_optionDSLPArr :=
  @ArrowApplyLaws_optionArrT PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowApply_PureDSLPostArr ArrowEq_PureDSLPostArr
    ArrowLaws_PureDSLPostArr ArrowChoiceLaws_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr.

Section StateOptionInstances.
  Variable S : Type.

  #[global] Instance Arrow_stateOptASP : Arrow (stateArrT S optionASPArr) :=
    @Arrow_stateArrT S optionASPArr Arrow_optionASPArr.
  #[global] Instance ArrowEq_stateOptASP : ArrowEq (stateArrT S optionASPArr) :=
    @ArrowEq_stateArrT S optionASPArr ArrowEq_optionASPArr.
  #[global] Instance ArrowChoice_stateOptASP :
    @ArrowChoice (stateArrT S optionASPArr) Arrow_stateOptASP :=
    @ArrowChoice_stateArrT S optionASPArr Arrow_optionASPArr ArrowChoice_optionASPArr.
  #[global] Instance ArrowApply_stateOptASP :
    @ArrowApply (stateArrT S optionASPArr) Arrow_stateOptASP :=
    @ArrowApply_stateArrT S optionASPArr Arrow_optionASPArr ArrowApply_optionASPArr.
  #[global] Instance ArrowLaws_stateOptASP :
    @ArrowLaws (stateArrT S optionASPArr) Arrow_stateOptASP ArrowEq_stateOptASP :=
    @ArrowLaws_stateArrT S optionASPArr Arrow_optionASPArr
      ArrowEq_optionASPArr ArrowLaws_optionASPArr.
  #[global] Instance ArrowChoiceLaws_stateOptASP :
    @ArrowChoiceLaws (stateArrT S optionASPArr) Arrow_stateOptASP
      ArrowChoice_stateOptASP ArrowEq_stateOptASP :=
    @ArrowChoiceLaws_stateArrT S optionASPArr Arrow_optionASPArr
      ArrowChoice_optionASPArr ArrowEq_optionASPArr
      ArrowLaws_optionASPArr ArrowChoiceLaws_optionASPArr.
  #[global] Instance ArrowApplyLaws_stateOptASP :
    @ArrowApplyLaws (stateArrT S optionASPArr) Arrow_stateOptASP
      ArrowApply_stateOptASP ArrowEq_stateOptASP :=
    @ArrowApplyLaws_stateArrT S optionASPArr Arrow_optionASPArr
      ArrowApply_optionASPArr ArrowEq_optionASPArr
      ArrowLaws_optionASPArr ArrowApplyLaws_optionASPArr.

  #[global] Instance Arrow_stateOptDSLP : Arrow (stateArrT S optionDSLPArr) :=
    @Arrow_stateArrT S optionDSLPArr Arrow_optionDSLPArr.
  #[global] Instance ArrowEq_stateOptDSLP : ArrowEq (stateArrT S optionDSLPArr) :=
    @ArrowEq_stateArrT S optionDSLPArr ArrowEq_optionDSLPArr.
  #[global] Instance ArrowChoice_stateOptDSLP :
    @ArrowChoice (stateArrT S optionDSLPArr) Arrow_stateOptDSLP :=
    @ArrowChoice_stateArrT S optionDSLPArr Arrow_optionDSLPArr ArrowChoice_optionDSLPArr.
  #[global] Instance ArrowApply_stateOptDSLP :
    @ArrowApply (stateArrT S optionDSLPArr) Arrow_stateOptDSLP :=
    @ArrowApply_stateArrT S optionDSLPArr Arrow_optionDSLPArr ArrowApply_optionDSLPArr.
  #[global] Instance ArrowLaws_stateOptDSLP :
    @ArrowLaws (stateArrT S optionDSLPArr) Arrow_stateOptDSLP ArrowEq_stateOptDSLP :=
    @ArrowLaws_stateArrT S optionDSLPArr Arrow_optionDSLPArr
      ArrowEq_optionDSLPArr ArrowLaws_optionDSLPArr.
  #[global] Instance ArrowChoiceLaws_stateOptDSLP :
    @ArrowChoiceLaws (stateArrT S optionDSLPArr) Arrow_stateOptDSLP
      ArrowChoice_stateOptDSLP ArrowEq_stateOptDSLP :=
    @ArrowChoiceLaws_stateArrT S optionDSLPArr Arrow_optionDSLPArr
      ArrowChoice_optionDSLPArr ArrowEq_optionDSLPArr
      ArrowLaws_optionDSLPArr ArrowChoiceLaws_optionDSLPArr.
  #[global] Instance ArrowApplyLaws_stateOptDSLP :
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
  cbn. destruct (IsASP_rewrite g) as [R HR]. split.
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
  cbn. destruct (IsDSLP_rewrite g) as [R HR]. split.
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
Proof. reflexivity. Qed.

Lemma optionDSLP_app_spec {A B} (P : optionDSLPArr A B * A -> Prop) r :
  getDSLP (@arr_app optionDSLPArr Arrow_optionDSLPArr ArrowApply_optionDSLPArr A B) P r
  <-> forall f, getDSLP f (fun a => P (f, a)) r.
Proof. reflexivity. Qed.

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
