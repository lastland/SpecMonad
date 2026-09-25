(** * WP and SP side by side: AWP, DWLP, ASP and DSLP

    A relation determines four healthy predicate transformers.  Two run
    backwards, from a postcondition to the precondition that guarantees it
    (AWP, DWLP); two run forwards, from a precondition to the postcondition
    it guarantees (ASP, DSLP).  Each has a specification monad, and each
    observes the nondeterministic computation monad with divergence through
    its terminating outcomes.  This file puts the four next to each other,
    first without state and then with.

    Without state, for a relation [R : A -> Prop], a postcondition [k] and
    a precondition [p : Prop]:

      AWP   ret x    = λk. k x                    reading  λk. ∃a. R a ∧ k a
            bind w f = λk. w (λa. f a k)          order    R' ⊆ R
      DWLP  ret, bind as for AWP                  reading  λk. ∀a. R a → k a
                                                  order    R ⊆ R'
      ASP   ret x    = λp a. p ∧ x = a            reading  λp a. p ∧ R a
            bind w f = λp b. ∃a. w p a ∧ f a ⊤ b  order    R ⊆ R'
      DSLP  ret x    = λp a. x = a → p            reading  λp a. R a → p
            bind w f = λp b. ∀a. w p a ∨ f a ⊥ b  order    R' ⊆ R

    - The WP pair shares [WPure]'s [ret] and [bind]: AWP and DWLP are the
      sub-monads carved out by healthiness ([HealthyWP]).  The SP pair has
      its own operations, and they are De Morgan duals ([getASP_ret],
      [getASP_bind], [getDSLP_ret], [getDSLP_bind_dual]).
    - The readings pair up by adjunction, AWP with DSLP and ASP with DWLP
      ([awp_dslp_adjunction], [asp_dwlp_adjunction]), and adjoint partners
      order relations the same way ([rho*_order]).

    With state [S], for [R : S -> A * S -> Prop], [k : A * S -> Prop] and
    [pre : S -> Prop], the WP columns are the pure ones at each start
    state: [stateT] over the carved monads, readings [λs k. ∃r. R s r ∧ k r]
    and [λs k. ∀r. R s r → k r].  The SP columns quantify over the start
    states that reach an outcome:

      ASP   ret x    = λpre r. ∃s. pre s ∧ r = (x, s)
            bind w f = λpre r. ∃a s'. w pre (a, s') ∧ f a {s'} r
            reading  = λpre r. ∃s. pre s ∧ R s r
      DSLP  ret x    = λpre r. ∀s. r = (x, s) → pre s
            bind w f = λpre r. ∀a s'. w pre (a, s') ∨ f a (≠ s') r
            reading  = λpre r. ∀s. R s r → pre s

    The continuation of an SP [bind] is read at the intermediate state:
    exactly at it for ASP, anywhere but at it for DSLP.  Without state these
    are [⊤] and [⊥].  The orders and adjunctions are the pure ones, at each
    start state. *)

From Coq Require Import Morphisms RelationClasses Setoid Classical_Prop.
From ExtLib Require Import Monad OptionMonad StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  WPureMonad DSLPArrowRel ASPMonad DSLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require SpecificationMonads.

(* ================================================================= *)
(** ** Healthy WP transformers                                        *)
(* ================================================================= *)

(** Disjunctivity and conjunctivity quantify over nonempty families;
    strictness and termination supply the empty ones. *)

Definition wpStrict {A} (w : WPure A) : Prop := ~ getWPure w (fun _ => False).

Definition wpTerminating {A} (w : WPure A) : Prop := getWPure w (fun _ => True).

Definition wpDisjunctive {A} (w : WPure A) : Prop :=
  forall (I : Type) (i0 : I) (Q : I -> A -> Prop),
    getWPure w (fun a => exists i, Q i a) <-> exists i, getWPure w (Q i).

Definition wpConjunctive {A} (w : WPure A) : Prop :=
  forall (I : Type) (i0 : I) (Q : I -> A -> Prop),
    getWPure w (fun a => forall i, Q i a) <-> forall i, getWPure w (Q i).

Section HealthinessClosure.
  Context {A B : Type}.

  Lemma wpStrict_ret (a : A) : wpStrict (ret a).
  Proof. intro H. exact H. Qed.

  Lemma wpTerminating_ret (a : A) : wpTerminating (ret a).
  Proof. exact I. Qed.

  Lemma wpDisjunctive_ret (a : A) : wpDisjunctive (ret a).
  Proof. intros Ix i0 Q. cbn. reflexivity. Qed.

  Lemma wpConjunctive_ret (a : A) : wpConjunctive (ret a).
  Proof. intros Ix i0 Q. cbn. reflexivity. Qed.

  Variable w : WPure A.
  Variable f : A -> WPure B.

  Lemma wpStrict_bind :
    wpStrict w -> (forall a, wpStrict (f a)) -> wpStrict (bind w f).
  Proof.
    intros Hw Hf H. apply Hw. cbn in H.
    exact (getWPure_mono w _ _ (fun a Ha => Hf a Ha) H).
  Qed.

  Lemma wpTerminating_bind :
    wpTerminating w -> (forall a, wpTerminating (f a)) -> wpTerminating (bind w f).
  Proof. intros Hw Hf. cbn. exact (getWPure_mono w _ _ (fun a _ => Hf a) Hw). Qed.

  Lemma wpDisjunctive_bind :
    wpDisjunctive w -> (forall a, wpDisjunctive (f a)) -> wpDisjunctive (bind w f).
  Proof.
    intros Hw Hf Ix i0 Q. cbn. split.
    - intro H. apply (proj1 (Hw Ix i0 (fun i a => getWPure (f a) (Q i)))).
      refine (getWPure_mono w _ _ _ H).
      intros a Ha. exact (proj1 (Hf a Ix i0 Q) Ha).
    - intros [i H]. refine (getWPure_mono w _ _ _ H).
      intros a Ha. apply (proj2 (Hf a Ix i0 Q)). exists i. exact Ha.
  Qed.

  Lemma wpConjunctive_bind :
    wpConjunctive w -> (forall a, wpConjunctive (f a)) -> wpConjunctive (bind w f).
  Proof.
    intros Hw Hf Ix i0 Q. cbn. split.
    - intros H i. refine (getWPure_mono w _ _ _ H).
      intros a Ha. exact (proj1 (Hf a Ix i0 Q) Ha i).
    - intro H. refine (getWPure_mono w (fun a => forall i, getWPure (f a) (Q i)) _ _ _).
      + intros a Ha. exact (proj2 (Hf a Ix i0 Q) Ha).
      + exact (proj2 (Hw Ix i0 (fun i a => getWPure (f a) (Q i))) H).
  Qed.
End HealthinessClosure.

(** A healthiness condition closed under [ret] and [bind] carves a
    specification monad out of [WPure]: same operations, same [eq1], same
    order. *)
Section HealthyWP.
  Variable H : forall A, WPure A -> Prop.
  Hypothesis H_ret : forall A (a : A), H A (ret a).
  Hypothesis H_bind : forall A B (w : WPure A) (f : A -> WPure B),
      H A w -> (forall a, H B (f a)) -> H B (bind w f).

  Definition WH (A : Type) : Type := { w : WPure A | H A w }.

  Definition getWH {A} (w : WH A) : WPure A := proj1_sig w.

  Definition retWH {A} (a : A) : WH A := exist _ (ret a) (H_ret A a).

  Definition bindWH {A B} (w : WH A) (f : A -> WH B) : WH B :=
    exist _ (bind (getWH w) (fun a => getWH (f a)))
      (H_bind A B (getWH w) (fun a => getWH (f a)) (proj2_sig w) (fun a => proj2_sig (f a))).

  Definition Monad_WH : Monad WH := {| ret := @retWH ; bind := @bindWH |}.

  Definition Eq1_WH : Eq1 WH := fun A w v => eq1 (getWH w) (getWH v).

  Definition Eq1Equivalence_WH : @Eq1Equivalence WH Monad_WH Eq1_WH.
  Proof.
    intro A. destruct (Eq1Equivalence_WPure A) as [Hr Hs Ht]. constructor.
    - intro x. exact (Hr (getWH x)).
    - intros x y Hxy. exact (Hs _ _ Hxy).
    - intros x y z H1 H2. exact (Ht _ _ _ H1 H2).
  Qed.

  Definition MonadLawsE_WH : @MonadLawsE WH Eq1_WH Monad_WH.
  Proof.
    destruct MonadLawsE_WPure as [Lbrl Lbrr Lbb Lpb]. constructor.
    - intros A B f x. exact (Lbrl A B (fun a => getWH (f a)) x).
    - intros A x. exact (Lbrr A (getWH x)).
    - intros A B C x f g.
      exact (Lbb A B C (getWH x) (fun a => getWH (f a)) (fun b => getWH (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (getWH x) (getWH y) Hxy
               (fun a => getWH (f a)) (fun a => getWH (g a)) Hfg).
  Qed.

  Definition leWH {A} (w v : WH A) : Prop := WP_le (getWH w) (getWH v).

  Definition OrderedMonad_WH : @OrderedMonad WH Monad_WH Eq1_WH (@leWH).
  Proof.
    destruct SpecificationMonads.OrderedMonad_WPure as [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre A) as [Hr Ht]. constructor.
      + intro x. exact (Hr (getWH x)).
      + intros x y z H1 H2. exact (Ht _ _ _ H1 H2).
    - intros A x y Hxy. exact (Heq A _ _ Hxy).
    - intros A B m1 m2 Hm k1 k2 Hk.
      exact (Hbind A B _ _ Hm (fun a => getWH (k1 a)) (fun a => getWH (k2 a)) Hk).
  Qed.
End HealthyWP.

Arguments getWH {H A} w.
Arguments leWH {H A} w v.
Coercion getWH : WH >-> WPure.

Definition AWPH A (w : WPure A) : Prop := wpStrict w /\ wpDisjunctive w.
Definition DWLPH A (w : WPure A) : Prop := wpTerminating w /\ wpConjunctive w.

Lemma AWPH_ret A (a : A) : AWPH A (ret a).
Proof. split; [ apply wpStrict_ret | apply wpDisjunctive_ret ]. Qed.
Lemma DWLPH_ret A (a : A) : DWLPH A (ret a).
Proof. split; [ apply wpTerminating_ret | apply wpConjunctive_ret ]. Qed.

Lemma AWPH_bind A B (w : WPure A) (f : A -> WPure B) :
  AWPH A w -> (forall a, AWPH B (f a)) -> AWPH B (bind w f).
Proof.
  intros [Hs Hd] Hf. split.
  - apply wpStrict_bind; [ exact Hs | intro a; exact (proj1 (Hf a)) ].
  - apply wpDisjunctive_bind; [ exact Hd | intro a; exact (proj2 (Hf a)) ].
Qed.
Lemma DWLPH_bind A B (w : WPure A) (f : A -> WPure B) :
  DWLPH A w -> (forall a, DWLPH B (f a)) -> DWLPH B (bind w f).
Proof.
  intros [Ht Hc] Hf. split.
  - apply wpTerminating_bind; [ exact Ht | intro a; exact (proj1 (Hf a)) ].
  - apply wpConjunctive_bind; [ exact Hc | intro a; exact (proj2 (Hf a)) ].
Qed.

Notation AWP := (WH AWPH).
Notation DWLP := (WH DWLPH).

#[global] Instance Monad_AWP : Monad AWP := Monad_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance Monad_DWLP : Monad DWLP := Monad_WH DWLPH DWLPH_ret DWLPH_bind.

#[global] Instance Eq1_AWP : Eq1 AWP := Eq1_WH AWPH.
#[global] Instance Eq1_DWLP : Eq1 DWLP := Eq1_WH DWLPH.

#[global] Instance Eq1Equivalence_AWP : @Eq1Equivalence AWP Monad_AWP Eq1_AWP :=
  Eq1Equivalence_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance Eq1Equivalence_DWLP : @Eq1Equivalence DWLP Monad_DWLP Eq1_DWLP :=
  Eq1Equivalence_WH DWLPH DWLPH_ret DWLPH_bind.

#[global] Instance MonadLawsE_AWP : @MonadLawsE AWP Eq1_AWP Monad_AWP :=
  MonadLawsE_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance MonadLawsE_DWLP : @MonadLawsE DWLP Eq1_DWLP Monad_DWLP :=
  MonadLawsE_WH DWLPH DWLPH_ret DWLPH_bind.

(** Both are specification monads under [WPure]'s order.  ASP and DSLP
    are [OrderedMonad_ASP] and [OrderedMonad_DSLP]. *)
#[global] Instance OrderedMonad_AWP : OrderedMonad AWP (@leWH AWPH) :=
  OrderedMonad_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance OrderedMonad_DWLP : OrderedMonad DWLP (@leWH DWLPH) :=
  OrderedMonad_WH DWLPH DWLPH_ret DWLPH_bind.

(* ================================================================= *)
(** ** Without state                                                  *)
(* ================================================================= *)

(** *** [ret] and [bind] *)

Lemma getAWP_ret {A} (x : A) (k : A -> Prop) : getWPure (ret x : AWP A) k <-> k x.
Proof. reflexivity. Qed.

Lemma getAWP_bind {A B} (w : AWP A) (f : A -> AWP B) (k : B -> Prop) :
  getWPure (bind w f) k <-> getWPure w (fun a => getWPure (f a) k).
Proof. reflexivity. Qed.

Lemma getDWLP_ret {A} (x : A) (k : A -> Prop) : getWPure (ret x : DWLP A) k <-> k x.
Proof. reflexivity. Qed.

Lemma getDWLP_bind {A B} (w : DWLP A) (f : A -> DWLP B) (k : B -> Prop) :
  getWPure (bind w f) k <-> getWPure w (fun a => getWPure (f a) k).
Proof. reflexivity. Qed.

(** [getDSLP_bind] in transformer form: the De Morgan dual of [getASP_bind]. *)
Lemma getDSLP_bind_dual {A B} (w : DSLP A) (f : A -> DSLP B) p b :
  getDSLP (bind w f) p b <-> forall a, getDSLP w p a \/ getDSLP (f a) False b.
Proof.
  cbn [bind Monad_DSLP]. rewrite getDSLP_bind. split.
  - intros H a. destruct (classic (getDSLP (f a) False b)) as [Hf | Hf]; [ right; exact Hf |].
    left. apply H. apply NNPP. intro Hn. apply Hf. apply getDSLP_rel. intro Hr. exact (Hn Hr).
  - intros H a Hr. destruct (H a) as [Hw | Hf]; [ exact Hw |].
    exfalso. exact (proj1 (getDSLP_rel (f a) False b) Hf Hr).
Qed.

(** *** Readings of a relation *)

#[program] Definition wpAngelic {A} (R : A -> Prop) : WPure A :=
  fun k => exists a, R a /\ k a.
Next Obligation.
  intros p q Hpq [a [Ha Hp]]. exists a. split; [ exact Ha | exact (Hpq a Hp) ].
Qed.

#[program] Definition wpDemonic {A} (R : A -> Prop) : WPure A :=
  fun k => forall a, R a -> k a.
Next Obligation. intros p q Hpq H a Ha. exact (Hpq a (H a Ha)). Qed.

Lemma wpAngelic_AWPH {A} (R : A -> Prop) : AWPH A (wpAngelic R).
Proof.
  split.
  - intros [a [_ []]].
  - intros I i0 Q. cbn. split.
    + intros [a [Ha [i Hq]]]. exists i, a. split; assumption.
    + intros [i [a [Ha Hq]]]. exists a. split; [ exact Ha | exists i; exact Hq ].
Qed.

Lemma wpDemonic_DWLPH {A} (R : A -> Prop) : DWLPH A (wpDemonic R).
Proof.
  split.
  - intros a _. exact I.
  - intros I i0 Q. cbn. split.
    + intros H i a Ha. exact (H a Ha i).
    + intros H a Ha i. exact (H i a Ha).
Qed.

Definition rhoAWP {A} (R : A -> Prop) : AWP A := exist _ (wpAngelic R) (wpAngelic_AWPH R).
Definition rhoDWLP {A} (R : A -> Prop) : DWLP A := exist _ (wpDemonic R) (wpDemonic_DWLPH R).
Definition rhoASP {A} (R : A -> Prop) : ASP A := aspOfPred R.
Definition rhoDSLP {A} (R : A -> Prop) : DSLP A := dslpOfPred R.

(** *** Orders: adjoint partners agree *)

Theorem rhoAWP_order {A} (R R' : A -> Prop) :
  leWH (rhoAWP R) (rhoAWP R') <-> (forall a, R' a -> R a).
Proof.
  unfold leWH, WP_le. cbn. split.
  - intros H a Ha. destruct (H (fun x => x = a) (ex_intro _ a (conj Ha eq_refl)))
      as [x [Hx ->]]. exact Hx.
  - intros H Q [a [Ha HQ]]. exists a. split; [ exact (H a Ha) | exact HQ ].
Qed.

Theorem rhoDWLP_order {A} (R R' : A -> Prop) :
  leWH (rhoDWLP R) (rhoDWLP R') <-> (forall a, R a -> R' a).
Proof.
  unfold leWH, WP_le. cbn. split.
  - intros H a Ha. exact (H R' (fun x Hx => Hx) a Ha).
  - intros H Q HQ a Ha. exact (HQ a (H a Ha)).
Qed.

Theorem rhoASP_order {A} (R R' : A -> Prop) :
  ordASP (rhoASP R) (rhoASP R') <-> (forall a, R a -> R' a).
Proof.
  rewrite ordASP_get. unfold rhoASP. setoid_rewrite getASP_of. split.
  - intros H a Ha. exact (proj2 (H True a (conj I Ha))).
  - intros H p a [Hp Ha]. exact (conj Hp (H a Ha)).
Qed.

Theorem rhoDSLP_order {A} (R R' : A -> Prop) :
  ordDSLP (rhoDSLP R) (rhoDSLP R') <-> (forall a, R' a -> R a).
Proof.
  rewrite ordDSLP_get. unfold rhoDSLP. setoid_rewrite getDSLP_of. split.
  - intros H a Ha. exact (H (R a) a (fun Hr => Hr) Ha).
  - intros H p a Hp Ha. exact (Hp (H a Ha)).
Qed.

(** *** Adjunctions *)

Theorem asp_dwlp_adjunction {A} (R : A -> Prop) (p : Prop) (Q : A -> Prop) :
  (forall a, getASP (rhoASP R) p a -> Q a) <-> (p -> getWPure (rhoDWLP R) Q).
Proof.
  unfold rhoASP. setoid_rewrite getASP_of. cbn. split.
  - intros H Hp a Ha. exact (H a (conj Hp Ha)).
  - intros H a [Hp Ha]. exact (H Hp a Ha).
Qed.

Theorem awp_dslp_adjunction {A} (R : A -> Prop) (p : Prop) (Q : A -> Prop) :
  (getWPure (rhoAWP R) Q -> p) <-> (forall a, Q a -> getDSLP (rhoDSLP R) p a).
Proof.
  unfold rhoDSLP. setoid_rewrite getDSLP_of. cbn. split.
  - intros H a Hq Ha. exact (H (ex_intro _ a (conj Ha Hq))).
  - intros H [a [Ha Hq]]. exact (H a Hq Ha).
Qed.

(** *** Effect observations of [divnd]: the terminating outcomes, read *)

Definition obsAWP {A} (m : divnd A) : AWP A := rhoAWP (fun a => unOptionT m (Some a)).
Definition obsDWLP {A} (m : divnd A) : DWLP A := rhoDWLP (fun a => unOptionT m (Some a)).
Definition obsASP {A} (m : divnd A) : ASP A := rhoASP (fun a => unOptionT m (Some a)).
Definition obsDSLP {A} (m : divnd A) : DSLP A := rhoDSLP (fun a => unOptionT m (Some a)).

Theorem obsAWP_ret {A} (a : A) : eq1 (obsAWP (ret a)) (ret a).
Proof.
  intro k. split.
  - intros [b [E Hk]]. injection E as E. subst b. exact Hk.
  - intro Hk. exists a. split; [ reflexivity | exact Hk ].
Qed.

Theorem obsAWP_bind {A B} (m : divnd A) (k : A -> divnd B) :
  eq1 (obsAWP (bind m k)) (bind (obsAWP m) (fun a => obsAWP (k a))).
Proof.
  intro q. split.
  - intros [b [Hb Hq]]. apply (proj1 (outcomes_bind m k (Some b))) in Hb.
    destruct Hb as [[a|] [Ha Hk]]; [| discriminate Hk ].
    exists a. split; [ exact Ha | exists b; split; [ exact Hk | exact Hq ] ].
  - intros [a [Ha [b [Hk Hq]]]]. exists b. split; [| exact Hq ].
    apply (proj2 (outcomes_bind m k (Some b))). exists (Some a). split; [ exact Ha | exact Hk ].
Qed.

Theorem obsDWLP_ret {A} (a : A) : eq1 (obsDWLP (ret a)) (ret a).
Proof.
  intro k. split.
  - intro H. exact (H a eq_refl).
  - intros Hk b E. injection E as E. subst b. exact Hk.
Qed.

Theorem obsDWLP_bind {A B} (m : divnd A) (k : A -> divnd B) :
  eq1 (obsDWLP (bind m k)) (bind (obsDWLP m) (fun a => obsDWLP (k a))).
Proof.
  intro q. split.
  - intros H a Ha b Hk. apply H.
    apply (proj2 (outcomes_bind m k (Some b))). exists (Some a). split; [ exact Ha | exact Hk ].
  - intros H b Hb. apply (proj1 (outcomes_bind m k (Some b))) in Hb.
    destruct Hb as [[a|] [Ha Hk]]; [ exact (H a Ha b Hk) | discriminate Hk ].
Qed.

Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a)) (ret a).
Proof.
  apply eq1_ASP_get. intros p b. unfold obsASP, rhoASP. cbn [ret Monad_ASP].
  rewrite getASP_of, getASP_ret. split.
  - intros [Hp E]. injection E as E. split; [ exact Hp | symmetry; exact E ].
  - intros [Hp E]. subst b. split; [ exact Hp | reflexivity ].
Qed.

Theorem obsASP_bind {A B} (m : divnd A) (k : A -> divnd B) :
  eq1 (obsASP (bind m k)) (bind (obsASP m) (fun a => obsASP (k a))).
Proof.
  apply eq1_ASP_get. intros p b. unfold obsASP, rhoASP. cbn [bind Monad_ASP].
  rewrite getASP_bind, getASP_of. split.
  - intros [Hp Hb]. apply (proj1 (outcomes_bind m k (Some b))) in Hb.
    destruct Hb as [[a|] [Ha Hk]]; [| discriminate Hk ].
    exists a. split; apply getASP_of; split; [ exact Hp | exact Ha | exact I | exact Hk ].
  - intros [a [Hm Hk]]. apply getASP_of in Hm. apply getASP_of in Hk.
    destruct Hm as [Hp Ha]. destruct Hk as [_ Hk]. split; [ exact Hp |].
    apply (proj2 (outcomes_bind m k (Some b))). exists (Some a). split; [ exact Ha | exact Hk ].
Qed.

Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a)) (ret a).
Proof.
  apply eq1_DSLP_get. intros p b. unfold obsDSLP, rhoDSLP. cbn [ret Monad_DSLP].
  rewrite getDSLP_of, getDSLP_ret. split.
  - intros H E. apply H. subst b. reflexivity.
  - intros H E. apply H. injection E as E. symmetry. exact E.
Qed.

Theorem obsDSLP_bind {A B} (m : divnd A) (k : A -> divnd B) :
  eq1 (obsDSLP (bind m k)) (bind (obsDSLP m) (fun a => obsDSLP (k a))).
Proof.
  apply eq1_DSLP_get. intros p b. unfold obsDSLP, rhoDSLP. cbn [bind Monad_DSLP].
  rewrite getDSLP_bind, getDSLP_of. split.
  - intros H a Hk. apply getDSLP_of. intro Ha. apply H.
    apply (proj2 (outcomes_bind m k (Some b))). exists (Some a). split; [ exact Ha |].
    exact (proj1 (dslpRel_ofRel _ tt b) Hk).
  - intros H Hb. apply (proj1 (outcomes_bind m k (Some b))) in Hb.
    destruct Hb as [[a|] [Ha Hk]]; [| discriminate Hk ].
    exact (proj1 (getDSLP_of _ p a) (H a (proj2 (dslpRel_ofRel _ tt b) Hk)) Ha).
Qed.

(* ================================================================= *)
(** ** With state                                                     *)
(* ================================================================= *)

Section WithState.
  Variable S : Type.

  #[local] Existing Instance Monad_stateT.

  (** The WP carriers are [stateT S AWP] and [stateT S DWLP]; the SP
      carriers are [ASPSt S] and [DSLPSt S], specification monads by
      [OrderedMonad_ASPSt] and [OrderedMonad_DSLPSt]. *)

  Corollary OrderedMonad_AWPSt : OrderedMonad (stateT S AWP) (le_stateT (@leWH AWPH)).
  Proof. exact (OrderedMonad_stateT _ OrderedMonad_AWP). Qed.

  Corollary OrderedMonad_DWLPSt : OrderedMonad (stateT S DWLP) (le_stateT (@leWH DWLPH)).
  Proof. exact (OrderedMonad_stateT _ OrderedMonad_DWLP). Qed.

  (** *** [ret] and [bind] *)

  Lemma getAWPSt_ret {A} (x : A) (s : S) (k : A * S -> Prop) :
    getWPure (runStateT (ret x : stateT S AWP A) s) k <-> k (x, s).
  Proof. reflexivity. Qed.

  Lemma getAWPSt_bind {A B} (w : stateT S AWP A) (f : A -> stateT S AWP B) s k :
    getWPure (runStateT (bind w f : stateT S AWP B) s) k
    <-> getWPure (runStateT w s) (fun p => getWPure (runStateT (f (fst p)) (snd p)) k).
  Proof. cbn. split; apply getWPure_mono; intros [a s']; cbn; intro H; exact H. Qed.

  Lemma getDWLPSt_ret {A} (x : A) (s : S) (k : A * S -> Prop) :
    getWPure (runStateT (ret x : stateT S DWLP A) s) k <-> k (x, s).
  Proof. reflexivity. Qed.

  Lemma getDWLPSt_bind {A B} (w : stateT S DWLP A) (f : A -> stateT S DWLP B) s k :
    getWPure (runStateT (bind w f : stateT S DWLP B) s) k
    <-> getWPure (runStateT w s) (fun p => getWPure (runStateT (f (fst p)) (snd p)) k).
  Proof. cbn. split; apply getWPure_mono; intros [a s']; cbn; intro H; exact H. Qed.

  (** [getDSLPSt_bind] in transformer form: the continuation is read away
      from the intermediate state, dually to [getASPSt_bind]. *)
  Lemma getDSLPSt_bind_dual {A B} (w : DSLPSt S A) (f : A -> DSLPSt S B) pre r :
    getDSLPSt (bind w f) pre r
    <-> forall a s', getDSLPSt w pre (a, s') \/ getDSLPSt (f a) (fun t => t <> s') r.
  Proof.
    cbn [bind Monad_DSLPSt]. rewrite getDSLPSt_bind. split.
    - intros H a s'.
      destruct (classic (getDSLPSt (f a) (fun t => t <> s') r)) as [Hf | Hf];
        [ right; exact Hf | left; apply H ].
      apply NNPP. intro Hn. apply Hf. apply getDSLPSt_rel. intros t Ht E. subst t. exact (Hn Ht).
    - intros H a s' Hr. destruct (H a s') as [Hw | Hf]; [ exact Hw |].
      exfalso. exact (proj1 (getDSLPSt_rel S (f a) _ r) Hf s' Hr eq_refl).
  Qed.

  (** *** Readings of a relation *)

  Definition rhoAWPSt {A} (R : S -> A * S -> Prop) : stateT S AWP A :=
    @mkStateT S AWP A (fun s => rhoAWP (R s)).
  Definition rhoDWLPSt {A} (R : S -> A * S -> Prop) : stateT S DWLP A :=
    @mkStateT S DWLP A (fun s => rhoDWLP (R s)).
  Definition rhoASPSt {A} (R : S -> A * S -> Prop) : ASPSt S A := aspOfRelSt R.
  Definition rhoDSLPSt {A} (R : S -> A * S -> Prop) : DSLPSt S A := dslpOfRelSt R.

  (** *** Orders: the pure ones, at each start state *)

  Theorem rhoAWPSt_order {A} (R R' : S -> A * S -> Prop) :
    le_stateT (@leWH AWPH) A (rhoAWPSt R) (rhoAWPSt R') <-> (forall s r, R' s r -> R s r).
  Proof.
    split.
    - intros H s. exact (proj1 (rhoAWP_order (R s) (R' s)) (H s)).
    - intros H s. exact (proj2 (rhoAWP_order (R s) (R' s)) (H s)).
  Qed.

  Theorem rhoDWLPSt_order {A} (R R' : S -> A * S -> Prop) :
    le_stateT (@leWH DWLPH) A (rhoDWLPSt R) (rhoDWLPSt R') <-> (forall s r, R s r -> R' s r).
  Proof.
    split.
    - intros H s. exact (proj1 (rhoDWLP_order (R s) (R' s)) (H s)).
    - intros H s. exact (proj2 (rhoDWLP_order (R s) (R' s)) (H s)).
  Qed.

  Theorem rhoASPSt_order {A} (R R' : S -> A * S -> Prop) :
    ordASPSt (rhoASPSt R) (rhoASPSt R') <-> (forall s r, R s r -> R' s r).
  Proof.
    rewrite ordASPSt_get. unfold rhoASPSt. setoid_rewrite getASPSt_of. split.
    - intros H s r Hr.
      destruct (H (fun t => t = s) r (ex_intro _ s (conj eq_refl Hr))) as [t [Ht Ht']].
      subst t. exact Ht'.
    - intros H pre r [s [Hs Hr]]. exists s. split; [ exact Hs | exact (H s r Hr) ].
  Qed.

  Theorem rhoDSLPSt_order {A} (R R' : S -> A * S -> Prop) :
    ordDSLPSt (rhoDSLPSt R) (rhoDSLPSt R') <-> (forall s r, R' s r -> R s r).
  Proof.
    rewrite ordDSLPSt_get. unfold rhoDSLPSt. setoid_rewrite getDSLPSt_of. split.
    - intros H s r Hr'. exact (H (fun t => R t r) r (fun t Ht => Ht) s Hr').
    - intros H pre r Hpre s Hr'. exact (Hpre s (H s r Hr')).
  Qed.

  (** *** Adjunctions *)

  Theorem aspSt_dwlpSt_adjunction {A} (R : S -> A * S -> Prop) (P : S -> Prop) (Q : A * S -> Prop) :
    (forall r, getASPSt (rhoASPSt R) P r -> Q r)
    <-> (forall s, P s -> getWPure (runStateT (rhoDWLPSt R) s) Q).
  Proof.
    unfold rhoASPSt. setoid_rewrite getASPSt_of. cbn. split.
    - intros H s Hs r Hr. exact (H r (ex_intro _ s (conj Hs Hr))).
    - intros H r [s [Hs Hr]]. exact (H s Hs r Hr).
  Qed.

  Theorem awpSt_dslpSt_adjunction {A} (R : S -> A * S -> Prop) (P : S -> Prop) (Q : A * S -> Prop) :
    (forall s, getWPure (runStateT (rhoAWPSt R) s) Q -> P s)
    <-> (forall r, Q r -> getDSLPSt (rhoDSLPSt R) P r).
  Proof.
    unfold rhoDSLPSt. setoid_rewrite getDSLPSt_of. cbn. split.
    - intros H r Hq s Hr. exact (H s (ex_intro _ r (conj Hr Hq))).
    - intros H s [r [Hr Hq]]. exact (H r Hq s Hr).
  Qed.

  (** *** Effect observations of [stdivnd] *)

  Lemma stdivnd_bind_some {A B} (m : stdivnd S A) (k : A -> stdivnd S B) s r :
    unOptionT (runStateT (bind m k) s) (Some r)
    <-> exists a s', unOptionT (runStateT m s) (Some (a, s'))
                     /\ unOptionT (runStateT (k a) s') (Some r).
  Proof.
    cbn. split.
    - intros [[[a s']|] [Hm Hk]]; [ exists a, s'; split; [ exact Hm | exact Hk ] | discriminate Hk ].
    - intros [a [s' [Hm Hk]]]. exists (Some (a, s')). split; [ exact Hm | exact Hk ].
  Qed.

  Definition obsAWPSt {A} (m : stdivnd S A) : stateT S AWP A :=
    rhoAWPSt (fun s r => unOptionT (runStateT m s) (Some r)).
  Definition obsDWLPSt {A} (m : stdivnd S A) : stateT S DWLP A :=
    rhoDWLPSt (fun s r => unOptionT (runStateT m s) (Some r)).
  Definition obsASPSt {A} (m : stdivnd S A) : ASPSt S A :=
    rhoASPSt (fun s r => unOptionT (runStateT m s) (Some r)).
  Definition obsDSLPSt {A} (m : stdivnd S A) : DSLPSt S A :=
    rhoDSLPSt (fun s r => unOptionT (runStateT m s) (Some r)).

  Theorem obsAWPSt_ret {A} (a : A) : eq1 (obsAWPSt (ret a)) (ret a).
  Proof.
    intros s k. split.
    - intros [r [E Hk]]. injection E as E. subst r. exact Hk.
    - intro Hk. exists (a, s). split; [ reflexivity | exact Hk ].
  Qed.

  Theorem obsAWPSt_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    eq1 (obsAWPSt (bind m k)) (bind (obsAWPSt m) (fun a => obsAWPSt (k a))).
  Proof.
    intros s q. rewrite getAWPSt_bind. split.
    - intros [r [Hr Hq]]. apply (proj1 (stdivnd_bind_some m k s r)) in Hr.
      destruct Hr as [a [s' [Hm Hk]]].
      exists (a, s'). split; [ exact Hm | exists r; split; [ exact Hk | exact Hq ] ].
    - intros [[a s'] [Hm [r [Hk Hq]]]]. exists r. split; [| exact Hq ].
      apply (proj2 (stdivnd_bind_some m k s r)). exists a, s'. split; [ exact Hm | exact Hk ].
  Qed.

  Theorem obsDWLPSt_ret {A} (a : A) : eq1 (obsDWLPSt (ret a)) (ret a).
  Proof.
    intros s k. split.
    - intro H. exact (H (a, s) eq_refl).
    - intros Hk r E. injection E as E. subst r. exact Hk.
  Qed.

  Theorem obsDWLPSt_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    eq1 (obsDWLPSt (bind m k)) (bind (obsDWLPSt m) (fun a => obsDWLPSt (k a))).
  Proof.
    intros s q. rewrite getDWLPSt_bind. split.
    - intros H [a s'] Hm r Hk. apply H.
      apply (proj2 (stdivnd_bind_some m k s r)). exists a, s'. split; [ exact Hm | exact Hk ].
    - intros H r Hr. apply (proj1 (stdivnd_bind_some m k s r)) in Hr.
      destruct Hr as [a [s' [Hm Hk]]]. exact (H (a, s') Hm r Hk).
  Qed.

  Theorem obsASPSt_ret {A} (a : A) : eq1 (obsASPSt (ret a)) (ret a).
  Proof.
    apply eq1_ASPSt_get. intros pre r. unfold obsASPSt, rhoASPSt. cbn [ret Monad_ASPSt].
    rewrite getASPSt_of, getASPSt_ret. split.
    - intros [s [Hs E]]. exists s. split; [ exact Hs |]. injection E as E. exact E.
    - intros [s [Hs E]]. exists s. split; [ exact Hs |]. subst r. reflexivity.
  Qed.

  Theorem obsASPSt_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    eq1 (obsASPSt (bind m k)) (bind (obsASPSt m) (fun a => obsASPSt (k a))).
  Proof.
    apply eq1_ASPSt_get. intros pre r. unfold obsASPSt, rhoASPSt. cbn [bind Monad_ASPSt].
    rewrite getASPSt_bind, getASPSt_of. split.
    - intros [s [Hs Hr]]. apply (proj1 (stdivnd_bind_some m k s r)) in Hr.
      destruct Hr as [a [s' [Hm Hk]]]. exists a, s'. split.
      + apply getASPSt_of. exists s. split; [ exact Hs | exact Hm ].
      + apply getASPSt_of. exists s'. split; [ reflexivity | exact Hk ].
    - intros [a [s' [Hm Hk]]]. apply getASPSt_of in Hm. apply getASPSt_of in Hk.
      destruct Hm as [s [Hs Hm]]. destruct Hk as [t [Et Hk]]. subst t.
      exists s. split; [ exact Hs |]. apply (proj2 (stdivnd_bind_some m k s r)).
      exists a, s'. split; [ exact Hm | exact Hk ].
  Qed.

  Theorem obsDSLPSt_ret {A} (a : A) : eq1 (obsDSLPSt (ret a)) (ret a).
  Proof.
    apply eq1_DSLPSt_get. intros pre r. unfold obsDSLPSt, rhoDSLPSt. cbn [ret Monad_DSLPSt].
    rewrite getDSLPSt_of, getDSLPSt_ret. split.
    - intros H s E. apply H. subst r. reflexivity.
    - intros H s E. apply H. injection E as E. exact E.
  Qed.

  Theorem obsDSLPSt_bind {A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
    eq1 (obsDSLPSt (bind m k)) (bind (obsDSLPSt m) (fun a => obsDSLPSt (k a))).
  Proof.
    apply eq1_DSLPSt_get. intros pre r. unfold obsDSLPSt, rhoDSLPSt. cbn [bind Monad_DSLPSt].
    rewrite getDSLPSt_bind, getDSLPSt_of. split.
    - intros H a s' Hk. apply getDSLPSt_of. intros s Hm. apply H.
      apply (proj2 (stdivnd_bind_some m k s r)). exists a, s'. split; [ exact Hm |].
      exact (proj1 (dslpRelSt_of S _ s' r) Hk).
    - intros H s Hr. apply (proj1 (stdivnd_bind_some m k s r)) in Hr.
      destruct Hr as [a [s' [Hm Hk]]].
      exact (proj1 (getDSLPSt_of S _ pre (a, s')) (H a s' (proj2 (dslpRelSt_of S _ s' r) Hk)) s Hm).
  Qed.
End WithState.
