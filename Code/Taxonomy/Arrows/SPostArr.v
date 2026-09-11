(** * Property-only strongest-postcondition arrows.

    The carriers contain only predicate transformers and well-formedness proofs.
    All operations act directly on transformers.  Canonical normal forms are
    derived below for reasoning; no relation is stored in either carrier. *)

From Coq Require Import FunctionalExtensionality PropExtensionality.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Classes Require Export ArrowMonad.
From Incorrectness.Classes Require RelArrowCoherence.
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

(** Existentially packaged normal forms are convenient for repeated rewriting
    without unfolding the canonical singleton/intersection predicates. *)
Lemma IsASP_rewrite {A B} (f : PureASPostArr A B) :
  exists R : A -> B -> Prop,
    forall P b, getASP f P b <-> exists a, P a /\ R a b.
Proof.
  exists (fun a b => getASP f (eq a) b). apply ASP_normal_form.
Qed.

Lemma IsDSLP_rewrite {A B} (f : PureDSLPostArr A B) :
  exists R : A -> B -> Prop,
    forall P b, getDSLP f P b <-> forall a, R a b -> P a.
Proof.
  exists (fun a b => forall Q, getDSLP f Q b -> Q a). apply DSLP_normal_form.
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

#[program] Definition pureASP {A B} (h : A -> B) : PureASPostArr A B :=
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

#[program] Definition pureDSLP {A B} (h : A -> B) : PureDSLPostArr A B :=
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
  arr_pure := @pureASP; arr_comp := @compASP; arr_first := @firstASP
}.

#[global] Instance Arrow_PureDSLPostArr : Arrow PureDSLPostArr := {
  arr_pure := @pureDSLP; arr_comp := @compDSLP; arr_first := @firstDSLP
}.

#[global] Instance ArrowChoice_PureASPostArr :
  @ArrowChoice PureASPostArr Arrow_PureASPostArr := { arr_left := @leftASP }.

#[global] Instance ArrowChoice_PureDSLPostArr :
  @ArrowChoice PureDSLPostArr Arrow_PureDSLPostArr := { arr_left := @leftDSLP }.

#[global] Instance ArrowApply_PureASPostArr :
  @ArrowApply PureASPostArr Arrow_PureASPostArr := { arr_app := @appASP }.

#[global] Instance ArrowApply_PureDSLPostArr :
  @ArrowApply PureDSLPostArr Arrow_PureDSLPostArr := { arr_app := @appDSLP }.

#[global] Instance ArrowEq_PureASPostArr : ArrowEq PureASPostArr := {
  arrow_eq := fun A B => @eq (PureASPostArr A B)
}.

#[global] Instance ArrowEq_PureDSLPostArr : ArrowEq PureDSLPostArr := {
  arrow_eq := fun A B => @eq (PureDSLPostArr A B)
}.

(** Public computational seams: lifting a function is its direct or
    universal image, and composition is transformer composition. *)
Lemma pureASP_spec {A B} (h : A -> B) P b :
  getASP (pureASP h) P b <-> exists a, P a /\ h a = b.
Proof. reflexivity. Qed.

Lemma pureDSLP_spec {A B} (h : A -> B) P b :
  getDSLP (pureDSLP h) P b <-> forall a, h a = b -> P a.
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

(** ** Recovered relations and faithfulness

    These derived witnesses let the core law instances reuse relational
    application coherence without changing the property-only carriers. *)

Definition ASP_rel {A B} (f : PureASPostArr A B) a b : Prop :=
  getASP f (eq a) b.

Definition DSLP_rel {A B} (f : PureDSLPostArr A B) a b : Prop :=
  forall Q, getDSLP f Q b -> Q a.

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
  DSLP_rel (pureDSLP h) a b <-> h a = b.
Proof.
  apply (DSLP_rel_of_representation (pureDSLP h) (fun a b => h a = b)).
  intros Q b'. apply pureDSLP_spec.
Qed.

Lemma DSLP_rel_comp {A B C}
  (f : PureDSLPostArr A B) (g : PureDSLPostArr B C) a c :
  DSLP_rel (compDSLP f g) a c <->
  exists b, DSLP_rel f a b /\ DSLP_rel g b c.
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
  DSLP_rel (firstDSLP f) (a, c) (b, d) <-> DSLP_rel f a b /\ c = d.
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
  match x, y with
  | inl a, inl b => DSLP_rel f a b
  | inr c, inr d => c = d
  | _, _ => False
  end.
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
  ASP_rel (pureASP h) a b <-> h a = b.
Proof.
  unfold ASP_rel. rewrite pureASP_spec. split.
  - intros [a' [<- Hh]]. exact Hh.
  - intro Hh. exists a. split; [reflexivity | exact Hh].
Qed.

Lemma ASP_rel_comp {A B C}
  (f : PureASPostArr A B) (g : PureASPostArr B C) a c :
  ASP_rel (compASP f g) a c <->
  exists b, ASP_rel f a b /\ ASP_rel g b c.
Proof.
  unfold ASP_rel. rewrite compASP_spec, (ASP_normal_form g).
  reflexivity.
Qed.

Lemma ASP_rel_first {A B C} (f : PureASPostArr A B) a (c : C) b d :
  ASP_rel (firstASP f) (a, c) (b, d) <-> ASP_rel f a b /\ c = d.
Proof.
  unfold ASP_rel. rewrite firstASP_spec, (ASP_normal_form f).
  split.
  - intros [a' [Heq Hr]]. injection Heq as <- <-. split; [exact Hr | reflexivity].
  - intros [Hr ->]. exists a. split; [reflexivity | exact Hr].
Qed.

Lemma ASP_rel_left {A B C} (f : PureASPostArr A B)
  (x : A + C) (y : B + C) :
  ASP_rel (leftASP f) x y <->
  match x, y with
  | inl a, inl b => ASP_rel f a b
  | inr c, inr d => c = d
  | _, _ => False
  end.
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

(** ** Derived proof packages for the existing property-only carriers *)

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

(** ** Angelic arrow laws *)

Local Lemma id_pred {A} (P : A -> Prop) :
  (fun b => exists a, P a /\ a = b) = P.
Proof.
  extensionality b. apply propositional_extensionality. sauto limit: 200.
Qed.

#[global] Instance ArrowLaws_PureASPostArr :
  @ArrowLaws PureASPostArr Arrow_PureASPostArr ArrowEq_PureASPostArr.
Proof.
  constructor; intros.
  - apply PureASPostArr_eq; intros P b. cbn. rewrite id_pred. reflexivity.
  - apply PureASPostArr_eq; intros P b. cbn. sauto limit: 200.
  - apply PureASPostArr_eq; intros P d. cbn. reflexivity.
  - apply PureASPostArr_eq; intros P c. cbn. sauto limit: 200.
  - apply PureASPostArr_eq; intros P [b c]. cbn. sauto limit: 200.
  - apply PureASPostArr_eq; intros P [c d]. cbn. reflexivity.
  - (* [first_fst] uses the full join implicit in the normal form, even
       when the untouched component type is empty. *)
    apply PureASPostArr_eq; intros P b. cbn.
    destruct (IsASP_rewrite f) as [R HR]. split.
    + intros [[b0 c] [Hfc Heq]]. cbn in Heq. subst.
      rewrite HR in Hfc. destruct Hfc as [a [HP Ha]].
      rewrite HR. exists a. split; [exists (a, c); auto | exact Ha].
    + intro H. rewrite HR in H. destruct H as [a [[[a0 c] [HP Heq]] Ha]].
      cbn in Heq. subst. exists (b, c). split.
      * rewrite HR. exists a. auto.
      * reflexivity.
  - apply PureASPostArr_eq; intros P [b [c d]]. cbn.
    destruct (IsASP_rewrite f) as [R HR]. split.
    + intros [[[b0 c0] d0] [Hf Heq]].
      unfold assoc_prod in Heq. inversion Heq; subst.
      rewrite HR in Hf. destruct Hf as [a [HP Ha]].
      rewrite HR. exists a. split; [exists ((a, c), d); auto | exact Ha].
    + intro H. rewrite HR in H. destruct H as [a [[[[a0 c0] d0] [HP Heq]] Ha]].
      unfold assoc_prod in Heq. inversion Heq; subst.
      exists ((b, c), d). split; [rewrite HR; exists a; auto | reflexivity].
  - intros x y -> z w ->. reflexivity.
  - intros x y ->. reflexivity.
  - (* first_natural *)
    apply PureASPostArr_eq; intros P [b d]. cbn.
    destruct (IsASP_rewrite f) as [R HR]. split.
    + intros [[b0 c] [Hf Heq]]. injection Heq as Hb Hd. subst b0 d.
      rewrite HR in Hf |- *. destruct Hf as [a [HP Ha]].
      exists a. split; [exists (a, c); auto | exact Ha].
    + intro H. rewrite HR in H.
      destruct H as [a [[[a0 c] [HP Heq]] Ha]].
      injection Heq as Ha0 Hd. subst a0 d.
      exists (b, c). split; [rewrite HR; exists a; auto | reflexivity].
Qed.

#[global] Instance ArrowChoiceLaws_PureASPostArr :
  @ArrowChoiceLaws PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr ArrowEq_PureASPostArr.
Proof.
  constructor; intros.
  - apply PureASPostArr_eq; intros P [b|c]; cbn; unfold sum_bimap;
      sauto limit: 200.
  - apply PureASPostArr_eq; intros P [c|d]; cbn; reflexivity.
  - apply PureASPostArr_eq; intros P [b|c]; cbn.
    + destruct (IsASP_rewrite f) as [R HR]. split.
      * intros [b0 [Hf Heq]]. injection Heq as Heq. subst.
        rewrite HR in Hf. destruct Hf as [a [HP Ha]].
        rewrite HR. exists a. split; [exists a; auto | exact Ha].
      * intro H. rewrite HR in H. destruct H as [a [[a0 [HP Heq]] Ha]].
        injection Heq as Heq. subst.
        exists b. split; [rewrite HR; exists a; auto | reflexivity].
    + sauto limit: 200.
  - apply PureASPostArr_eq; intros P [b|[c|d]]; cbn.
    + destruct (IsASP_rewrite f) as [R HR]. split.
      * intros [x [Hf Heq]]. destruct x as [[b0|c0]|d0]; cbn in Heq;
          try discriminate.
        injection Heq as Heq. subst. cbn in Hf.
        rewrite HR in Hf. destruct Hf as [a [HP Ha]].
        rewrite HR. exists a. split; [exists (inl (inl a)); auto | exact Ha].
      * intro H. rewrite HR in H. destruct H as [a [[x [HP Heq]] Ha]].
        destruct x as [[a0|c0]|d0]; cbn in Heq; try discriminate.
        injection Heq as Heq. subst.
        exists (inl (inl b)). split; [cbn; rewrite HR; exists a; auto | reflexivity].
    + split.
      * intros [x [HP Heq]]. destruct x as [[b0|c0]|d0]; cbn in Heq;
          try discriminate.
        injection Heq as Heq. subst. exists (inl (inr c)). auto.
      * intros [x [HP Heq]]. destruct x as [[a0|c0]|d0]; cbn in Heq;
          try discriminate.
        injection Heq as Heq. subst. exists (inl (inr c)). auto.
    + split.
      * intros [x [HP Heq]]. destruct x as [[b0|c0]|d0]; cbn in Heq;
          try discriminate.
        injection Heq as Heq. subst. exists (inr d). auto.
      * intros [x [HP Heq]]. destruct x as [[a0|c0]|d0]; cbn in Heq;
          try discriminate.
        injection Heq as Heq. subst. exists (inr d). auto.
  - apply PureASPostArr_eq; intros P [b|c]; cbn.
    + destruct (IsASP_rewrite f) as [R HR]. rewrite HR.
      split; intros H; exfalso.
      * destruct H as [a [[c0 [_ H]] _]]. discriminate.
      * destruct H as [c0 [_ H]]. discriminate.
    + sauto limit: 200.
  - apply PureASPostArr_eq; intros P [b|d]; cbn; unfold sum_bimap.
    + destruct (IsASP_rewrite f) as [R HR]. split.
      * intros [[b0|c0] [Hf Heq]]; [|discriminate].
        injection Heq as Heq. subst. cbn in Hf.
        rewrite HR in Hf. destruct Hf as [a [HP Ha]].
        rewrite HR. exists a. split; [exists (inl a); auto | exact Ha].
      * intro H. rewrite HR in H. destruct H as [a [[x [HP Heq]] Ha]].
        destruct x as [a0|c0]; [injection Heq as Heq; subst | discriminate].
        exists (inl b). split; [cbn; rewrite HR; exists a; auto | reflexivity].
    + split.
      * intros [[b0|c0] [HP Heq]]; [discriminate|].
        injection Heq as Heq. subst. exists (inr c0). auto.
      * intros [[a0|c0] [HP Heq]]; [discriminate|].
        injection Heq as Heq. subst. exists (inr c0). auto.
  - apply PureASPostArr_eq; intros P [[b d]|[c d]]; cbn; unfold sum_prod_dist.
    + destruct (IsASP_rewrite f) as [R HR]. split.
      * intros [[[b0|c0] d0] [Hf Heq]]; [|discriminate].
        injection Heq as Hb Hd. subst. cbn in Hf.
        rewrite HR in Hf. destruct Hf as [a [HP Ha]].
        rewrite HR. exists a. split; [exists (inl a, d); auto | exact Ha].
      * intro H. rewrite HR in H. destruct H as [a [[[[a0|c0] d0] [HP Heq]] Ha]];
          cbn in Heq; [|discriminate].
        injection Heq as Ha0 Hd. subst.
        exists (inl b, d). split; [cbn; rewrite HR; exists a; auto | reflexivity].
    + split.
      * intros [[[b0|c0] d0] [HP Heq]]; [discriminate|].
        injection Heq as Hc Hd. subst. exists (inr c, d). auto.
      * intros [[[a0|c0] d0] [HP Heq]]; cbn in Heq; [discriminate|].
        injection Heq as Hc Hd. subst. exists (inr c, d). auto.
  - intros x y ->. reflexivity.
Qed.

(** ** Demonic arrow laws *)

Local Lemma id_pred_dslp {A} (P : A -> Prop) :
  (fun b => forall a, a = b -> P a) = P.
Proof.
  extensionality b. apply propositional_extensionality. sauto limit: 200.
Qed.

#[global] Instance ArrowLaws_PureDSLPostArr :
  @ArrowLaws PureDSLPostArr Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr.
Proof.
  constructor; intros.
  - apply PureDSLPostArr_eq; intros P b. cbn. rewrite id_pred_dslp. reflexivity.
  - apply PureDSLPostArr_eq; intros P b. cbn. sauto limit: 200.
  - apply PureDSLPostArr_eq; intros P d. cbn. reflexivity.
  - apply PureDSLPostArr_eq; intros P c. cbn. sauto limit: 200.
  - apply PureDSLPostArr_eq; intros P [b c]. cbn. sauto limit: 200.
  - apply PureDSLPostArr_eq; intros P [c d]. cbn. reflexivity.
  - (* The full meet in the normal form handles an empty component type. *)
    apply PureDSLPostArr_eq; intros P b. cbn.
    destruct (IsDSLP_rewrite f) as [R HR]. split.
    + intro H. rewrite HR. intros a Ha [a0 c] Heq. cbn in Heq. subst.
      assert (Hc := H (b, c) eq_refl). rewrite HR in Hc. exact (Hc a Ha).
    + intro H. rewrite HR in H. intros [b0 c] Heq. cbn in Heq. subst.
      rewrite HR. intros a Ha. exact (H a Ha (a, c) eq_refl).
  - apply PureDSLPostArr_eq; intros P [b [c d]]. cbn.
    destruct (IsDSLP_rewrite f) as [R HR]. split.
    + intro H. rewrite HR. intros a Ha [[a0 c0] d0] Heq.
      unfold assoc_prod in Heq. inversion Heq; subst.
      assert (Hcd := H ((b, c), d) eq_refl). rewrite HR in Hcd. exact (Hcd a Ha).
    + intro H. rewrite HR in H. intros [[b0 c0] d0] Heq.
      unfold assoc_prod in Heq. inversion Heq; subst.
      rewrite HR. intros a Ha. exact (H a Ha ((a, c), d) eq_refl).
  - intros x y -> z w ->. reflexivity.
  - intros x y ->. reflexivity.
  - (* first_natural *)
    apply PureDSLPostArr_eq; intros P [b d]. cbn.
    destruct (IsDSLP_rewrite f) as [R HR]. split.
    + intro H. rewrite HR. intros a Ha [a0 c] Heq.
      injection Heq as Ha0 Hd. subst a0 d.
      assert (Hc := H (b, c) eq_refl). rewrite HR in Hc. exact (Hc a Ha).
    + intro H. rewrite HR in H. intros [b0 c] Heq.
      injection Heq as Hb Hd. subst b0 d.
      rewrite HR. intros a Ha. exact (H a Ha (a, c) eq_refl).
Qed.

#[global] Instance ArrowChoiceLaws_PureDSLPostArr :
  @ArrowChoiceLaws PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr ArrowEq_PureDSLPostArr.
Proof.
  constructor; intros.
  - apply PureDSLPostArr_eq; intros P [b|c]; cbn; unfold sum_bimap;
      sauto limit: 200.
  - apply PureDSLPostArr_eq; intros P [c|d]; cbn; reflexivity.
  - apply PureDSLPostArr_eq; intros P [b|c]; cbn.
    + destruct (IsDSLP_rewrite f) as [R HR]. split.
      * intro H. rewrite HR. intros a Ha a0 Heq. injection Heq as Heq. subst.
        assert (Hf := H b eq_refl). rewrite HR in Hf. exact (Hf a Ha).
      * intro H. rewrite HR in H. intros b0 Heq. injection Heq as Heq. subst.
        rewrite HR. intros a Ha. exact (H a Ha a eq_refl).
    + split; intros _ ? H; discriminate H.
  - apply PureDSLPostArr_eq; intros P [b|[c|d]]; cbn.
    + destruct (IsDSLP_rewrite f) as [R HR]. split.
      * intro H. rewrite HR. intros a Ha [[a0|c0]|d0] Heq;
          cbn in Heq; try discriminate.
        injection Heq as Heq. subst.
        assert (Hf := H (inl (inl b)) eq_refl). cbn in Hf. rewrite HR in Hf.
        exact (Hf a Ha).
      * intro H. rewrite HR in H. intros [[b0|c0]|d0] Heq;
          cbn in Heq; try discriminate.
        injection Heq as Heq. subst. cbn. rewrite HR.
        intros a Ha. exact (H a Ha (inl (inl a)) eq_refl).
    + split.
      * intros H [[a0|c0]|d0] Heq; cbn in Heq; try discriminate.
        injection Heq as Heq. subst. exact (H (inl (inr c)) eq_refl).
      * intros H [[b0|c0]|d0] Heq; cbn in Heq; try discriminate.
        injection Heq as Heq. subst. exact (H (inl (inr c)) eq_refl).
    + split.
      * intros H [[a0|c0]|d0] Heq; cbn in Heq; try discriminate.
        injection Heq as Heq. subst. exact (H (inr d) eq_refl).
      * intros H [[b0|c0]|d0] Heq; cbn in Heq; try discriminate.
        injection Heq as Heq. subst. exact (H (inr d) eq_refl).
  - apply PureDSLPostArr_eq; intros P [b|c]; cbn.
    + destruct (IsDSLP_rewrite f) as [R HR]. split.
      * intros _ c0 H. discriminate.
      * intros _. rewrite HR. intros a _ c0 H. discriminate.
    + split; intros H c0 Heq; injection Heq as Heq; subst; exact (H c eq_refl).
  - apply PureDSLPostArr_eq; intros P [b|d]; cbn; unfold sum_bimap.
    + destruct (IsDSLP_rewrite f) as [R HR]. split.
      * intro H. rewrite HR. intros a Ha [a0|c0] Heq; [|discriminate].
        injection Heq as Heq. subst.
        specialize (H (inl b) eq_refl). cbn in H. rewrite HR in H. exact (H a Ha).
      * intro H. rewrite HR in H. intros [b0|c0] Heq; [|discriminate].
        injection Heq as Heq. subst. cbn. rewrite HR.
        intros a Ha. exact (H a Ha (inl a) eq_refl).
    + split.
      * intros H [a0|c0] Heq; [discriminate|].
        injection Heq as Heq. apply (H (inr c0)). f_equal. exact Heq.
      * intros H [b0|c0] Heq; [discriminate|].
        injection Heq as Heq. apply (H (inr c0)). f_equal. exact Heq.
  - apply PureDSLPostArr_eq; intros P [[b d]|[c d]]; cbn; unfold sum_prod_dist.
    + destruct (IsDSLP_rewrite f) as [R HR]. split.
      * intro H. rewrite HR. intros a Ha [[a0|c0] d0] Heq;
          cbn in Heq; [|discriminate].
        injection Heq as Ha0 Hd. subst.
        assert (Hf := H (inl b, d) eq_refl). cbn in Hf. rewrite HR in Hf.
        exact (Hf a Ha).
      * intro H. rewrite HR in H. intros [[b0|c0] d0] Heq;
          cbn in Heq; [|discriminate].
        injection Heq as Hb Hd. subst. cbn. rewrite HR.
        intros a Ha. exact (H a Ha (inl a, d) eq_refl).
    + split.
      * intros H [[a0|c0] d0] Heq; cbn in Heq; [discriminate|].
        injection Heq as Hc Hd. subst. exact (H (inr c, d) eq_refl).
      * intros H [[b0|c0] d0] Heq; cbn in Heq; [discriminate|].
        injection Heq as Hc Hd. subst. exact (H (inr c, d) eq_refl).
  - intros x y ->. reflexivity.
Qed.

(** ** Application laws *)

#[global] Instance ArrowApplyLaws_PureASPostArr :
  @ArrowApplyLaws PureASPostArr Arrow_PureASPostArr
    ArrowApply_PureASPostArr ArrowEq_PureASPostArr.
Proof.
  constructor.
  - intros A B f. apply PureASPostArr_eq; intros P b. cbn.
    split.
    + intros [f0 H]. destruct (IsASP_rewrite f0) as [R HR].
      rewrite HR in H. destruct H as [a [[a0 [HP Heq]] Ha]].
      injection Heq as Hf Heq. subst f0 a0.
      rewrite HR. exists a. auto.
    + intro H. exists f. eapply ASP_monotone; [|exact H].
      intros a HP. exists a. auto.
  - exact (RelArrowCoherence.rel_app_unit ASP_rel_presentation).
  - intros A B C g. exact (RelArrowCoherence.rel_app_precompose ASP_rel_presentation g).
  - intros A B C h. exact (RelArrowCoherence.rel_app_postcompose ASP_rel_presentation h).
  - intros X A B u v H.
    assert (Heq : u = v).
    { extensionality x. specialize (H x).
      destruct (u x) as [f a], (v x) as [g b].
      cbn in H. destruct H as [-> ->]. reflexivity. }
    subst v. reflexivity.
Qed.

#[global] Instance ArrowApplyLaws_PureDSLPostArr :
  @ArrowApplyLaws PureDSLPostArr Arrow_PureDSLPostArr
    ArrowApply_PureDSLPostArr ArrowEq_PureDSLPostArr.
Proof.
  constructor.
  - intros A B f. apply PureDSLPostArr_eq; intros P b. cbn.
    split.
    + intro H. eapply DSLP_monotone; [|exact (H f)].
      intros a Ha. exact (Ha a eq_refl).
    + intros H f0. destruct (IsDSLP_rewrite f0) as [R HR].
      rewrite HR. intros a Ha a0 Heq. injection Heq as Hf Heq. subst f0 a0.
      rewrite HR in H. exact (H a Ha).
  - exact (RelArrowCoherence.rel_app_unit DSLP_rel_presentation).
  - intros A B C g. exact (RelArrowCoherence.rel_app_precompose DSLP_rel_presentation g).
  - intros A B C h. exact (RelArrowCoherence.rel_app_postcompose DSLP_rel_presentation h).
  - intros X A B u v H.
    assert (Heq : u = v).
    { extensionality x. specialize (H x).
      destruct (u x) as [f a], (v x) as [g b].
      cbn in H. destruct H as [-> ->]. reflexivity. }
    subst v. reflexivity.
Qed.

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
