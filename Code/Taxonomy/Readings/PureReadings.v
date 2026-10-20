(** * Pure: the predicate-transformer monads as readings of [Rel]

    [Rel A = A -> Prop] ([PredM.Pred]) is the relation specification monad
    without state: [ret a] is the singleton, [bind R K] the union of the
    [K a] over [a ∈ R], and inclusion its order ([OrderedMonad_Pred]).

    [slice] maps [divnd] into it by keeping the terminating outcomes.  A
    READING maps it on into a predicate-transformer monad.  Every arrow here
    is a [MonadMorphism]:

      divnd   --slice-->  Rel  --rhoAWP-->   AWP    strict, disjunctive WPs
                               --rhoDWLP-->  DWLP   terminating, conjunctive WPs
                               --rhoASP-->   ASP    strict, disjunctive SPs
                               --rhoDSLP-->  DSLP   terminating, conjunctive SPs
                               --rhoDSP-->   DSP    strict, conjunctive SPs
                               --rhoASLP-->  ASLP   terminating, disjunctive SPs
      divndNE --obsDWP----------------->  DWP    strict, conjunctive WPs
      divndNE --obsAWLP---------------->  AWLP   terminating, disjunctive WPs

    The four WP targets are carved out of [WPure] by healthiness ([WH]).
    The four SP targets are the arrow monads of [BaseSpecMonads] at input
    [unit].

    What the readings show:

    - DWP and AWLP are not readings of [Rel] ([no_reading_Rel_DWP],
      [no_reading_Rel_AWLP]).  In [Rel] an empty branch disappears from a
      union, but DWP must count it as failure and AWLP as success.  Both
      read divergence, which [slice] forgets ([obs_not_via_slice]), so their
      relation monad is [divnd] itself.

    - Without state, DSP is ASP and ASLP is DSLP ([rhoDSP_is_rhoASP],
      [rhoASLP_is_rhoDSLP]).  With one start state, "some predecessor
      satisfies the precondition" and "every predecessor does" agree as soon
      as there is a predecessor.  So both are specification monads under
      their own orders ([OrderedMonad_DSP_reading],
      [OrderedMonad_ASLP_reading]); the stateful failure
      ([not_OrderedMonad_DSPSt]) needs a second start state.

    - Each reading induces an order on [Rel]: inclusion for ASP, DSP and
      DWLP, its reverse for DSLP, ASLP and AWP ([rho*_order]).  When the
      reading is onto its monad, a triple is carved out by an index exactly
      when its class of relations is a single inclusion ([carved_iso]).
      Hoare triples are ([hoare_carved_ASP], [hoare_carved_DWLP]), and so are
      incorrectness triples, whenever they are satisfiable at all
      ([incorrect_carved_iff]).  Angelic total correctness, "some outcome
      satisfies [Q]", is not ([angelic_not_carved_AWP]).

    - [WPure] contains elements outside the image of every WP reading, and
      those carve out every WP triple ([wp_sub_carved], [wp_sup_carved]).
      The SP monads have no such room: [aspRel] and [dslpRel] make ASP and
      DSLP isomorphic to [Rel]. *)

From Coq Require Import Morphisms RelationClasses Setoid.
From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OrderedMonad MonadMorphism.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  PredMonad WPureMonad BaseGaloisConnections SpecificationMonads.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPure ASPMonad DSLPMonad DSPMonad ASLPMonad.

(* ================================================================= *)
(** ** The relation monad                                            *)
(* ================================================================= *)

Notation Rel := PredM.Pred.

(** [SetM] unfolds to the same carrier with Leibniz [eq1], so [Rel]'s own
    instances are named explicitly wherever the equivalence matters. *)
Local Notation RelMM σ :=
  (@MonadMorphism PredM.Pred _ PredM.Monad_Pred _ PredM.Eq1_Pred _ σ).

Local Notation relIff R R' := (forall a, R a <-> R' a).

(* ================================================================= *)
(** ** [divnd] into [Rel]                                             *)
(* ================================================================= *)

(** The terminating slice: the outcomes that return. *)
Definition slice {A} (m : divnd A) : Rel A := fun a => unOptionT m (Some a).

Theorem slice_morphism :
  @MonadMorphism divnd PredM.Pred Monad__divnd PredM.Monad_Pred
    Eq1__divnd PredM.Eq1_Pred (@slice).
Proof.
  constructor.
  - intros A x y Hxy a. unfold slice.
    cbv [eq1 Eq1__divnd Eq1_optionT Eq1_SetM] in Hxy.
    rewrite Hxy. reflexivity.
  - intros A a b. unfold slice. cbn. split; intro H; congruence.
  - intros A B x k b. unfold slice. cbn [bind Monad__divnd].
    rewrite outcomes_bind. cbn. split.
    + intros [[a|] [Hx Hk]]; [ exists a; split; assumption | discriminate Hk ].
    + intros [a [Hx Hk]]. exists (Some a). split; assumption.
Qed.

(* ================================================================= *)
(** ** Healthy WP transformers                                       *)
(* ================================================================= *)

(** As for the SP carriers ([SPPredicateTransformers.v]), conjunctivity
    and disjunctivity quantify over NONEMPTY families; strictness and
    termination supply the empty ones. *)

Definition wpStrict {A} (w : WPure A) : Prop := ~ w (fun _ => False).

Definition wpTerminating {A} (w : WPure A) : Prop := w (fun _ => True).

Definition wpConjunctive {A} (w : WPure A) : Prop :=
  forall (I : Type) (i0 : I) (Q : I -> A -> Prop),
    w (fun a => forall i, Q i a) <-> forall i, w (Q i).

Definition wpDisjunctive {A} (w : WPure A) : Prop :=
  forall (I : Type) (i0 : I) (Q : I -> A -> Prop),
    w (fun a => exists i, Q i a) <-> exists i, w (Q i).

Section HealthinessClosure.
  Context {A B : Type}.

  Lemma wpStrict_ret (a : A) : wpStrict (ret a).
  Proof. intro H. exact H. Qed.

  Lemma wpTerminating_ret (a : A) : wpTerminating (ret a).
  Proof. exact I. Qed.

  Lemma wpConjunctive_ret (a : A) : wpConjunctive (ret a).
  Proof. intros Ix i0 Q. cbn. reflexivity. Qed.

  Lemma wpDisjunctive_ret (a : A) : wpDisjunctive (ret a).
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

  Lemma wpConjunctive_bind :
    wpConjunctive w -> (forall a, wpConjunctive (f a)) -> wpConjunctive (bind w f).
  Proof.
    intros Hw Hf Ix i0 Q. cbn. split.
    - intros H i. refine (getWPure_mono w _ _ _ H).
      intros a Ha. exact (proj1 (Hf a Ix i0 Q) Ha i).
    - intro H. refine (getWPure_mono w (fun a => forall i, f a (Q i)) _ _ _).
      + intros a Ha. exact (proj2 (Hf a Ix i0 Q) Ha).
      + exact (proj2 (Hw Ix i0 (fun i a => f a (Q i))) H).
  Qed.

  Lemma wpDisjunctive_bind :
    wpDisjunctive w -> (forall a, wpDisjunctive (f a)) -> wpDisjunctive (bind w f).
  Proof.
    intros Hw Hf Ix i0 Q. cbn. split.
    - intro H. apply (proj1 (Hw Ix i0 (fun i a => f a (Q i)))).
      refine (getWPure_mono w _ _ _ H).
      intros a Ha. exact (proj1 (Hf a Ix i0 Q) Ha).
    - intros [i H]. refine (getWPure_mono w _ _ _ H).
      intros a Ha. apply (proj2 (Hf a Ix i0 Q)). exists i. exact Ha.
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
    destruct OrderedMonad_WPure as [Hpre Heq Hbind]. constructor.
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

(** *** The four healthy WP monads *)

Definition AWPH A (w : WPure A) : Prop := wpStrict w /\ wpDisjunctive w.
Definition DWLPH A (w : WPure A) : Prop := wpTerminating w /\ wpConjunctive w.
Definition DWPH A (w : WPure A) : Prop := wpStrict w /\ wpConjunctive w.
Definition AWLPH A (w : WPure A) : Prop := wpTerminating w /\ wpDisjunctive w.

Lemma AWPH_ret A (a : A) : AWPH A (ret a).
Proof. split; [ apply wpStrict_ret | apply wpDisjunctive_ret ]. Qed.
Lemma DWLPH_ret A (a : A) : DWLPH A (ret a).
Proof. split; [ apply wpTerminating_ret | apply wpConjunctive_ret ]. Qed.
Lemma DWPH_ret A (a : A) : DWPH A (ret a).
Proof. split; [ apply wpStrict_ret | apply wpConjunctive_ret ]. Qed.
Lemma AWLPH_ret A (a : A) : AWLPH A (ret a).
Proof. split; [ apply wpTerminating_ret | apply wpDisjunctive_ret ]. Qed.

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
Lemma DWPH_bind A B (w : WPure A) (f : A -> WPure B) :
  DWPH A w -> (forall a, DWPH B (f a)) -> DWPH B (bind w f).
Proof.
  intros [Hs Hc] Hf. split.
  - apply wpStrict_bind; [ exact Hs | intro a; exact (proj1 (Hf a)) ].
  - apply wpConjunctive_bind; [ exact Hc | intro a; exact (proj2 (Hf a)) ].
Qed.
Lemma AWLPH_bind A B (w : WPure A) (f : A -> WPure B) :
  AWLPH A w -> (forall a, AWLPH B (f a)) -> AWLPH B (bind w f).
Proof.
  intros [Ht Hd] Hf. split.
  - apply wpTerminating_bind; [ exact Ht | intro a; exact (proj1 (Hf a)) ].
  - apply wpDisjunctive_bind; [ exact Hd | intro a; exact (proj2 (Hf a)) ].
Qed.

Notation AWP := (WH AWPH).
Notation DWLP := (WH DWLPH).
Notation DWP := (WH DWPH).
Notation AWLP := (WH AWLPH).

#[global] Instance Monad_AWP : Monad AWP := Monad_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance Monad_DWLP : Monad DWLP := Monad_WH DWLPH DWLPH_ret DWLPH_bind.
#[global] Instance Monad_DWP : Monad DWP := Monad_WH DWPH DWPH_ret DWPH_bind.
#[global] Instance Monad_AWLP : Monad AWLP := Monad_WH AWLPH AWLPH_ret AWLPH_bind.

#[global] Instance Eq1_AWP : Eq1 AWP := Eq1_WH AWPH.
#[global] Instance Eq1_DWLP : Eq1 DWLP := Eq1_WH DWLPH.
#[global] Instance Eq1_DWP : Eq1 DWP := Eq1_WH DWPH.
#[global] Instance Eq1_AWLP : Eq1 AWLP := Eq1_WH AWLPH.

#[global] Instance Eq1Equivalence_AWP : @Eq1Equivalence AWP Monad_AWP Eq1_AWP :=
  Eq1Equivalence_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance Eq1Equivalence_DWLP : @Eq1Equivalence DWLP Monad_DWLP Eq1_DWLP :=
  Eq1Equivalence_WH DWLPH DWLPH_ret DWLPH_bind.
#[global] Instance Eq1Equivalence_DWP : @Eq1Equivalence DWP Monad_DWP Eq1_DWP :=
  Eq1Equivalence_WH DWPH DWPH_ret DWPH_bind.
#[global] Instance Eq1Equivalence_AWLP : @Eq1Equivalence AWLP Monad_AWLP Eq1_AWLP :=
  Eq1Equivalence_WH AWLPH AWLPH_ret AWLPH_bind.

#[global] Instance MonadLawsE_AWP : @MonadLawsE AWP Eq1_AWP Monad_AWP :=
  MonadLawsE_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance MonadLawsE_DWLP : @MonadLawsE DWLP Eq1_DWLP Monad_DWLP :=
  MonadLawsE_WH DWLPH DWLPH_ret DWLPH_bind.
#[global] Instance MonadLawsE_DWP : @MonadLawsE DWP Eq1_DWP Monad_DWP :=
  MonadLawsE_WH DWPH DWPH_ret DWPH_bind.
#[global] Instance MonadLawsE_AWLP : @MonadLawsE AWLP Eq1_AWLP Monad_AWLP :=
  MonadLawsE_WH AWLPH AWLPH_ret AWLPH_bind.

(** All four are specification monads, under [WPure]'s order. *)
#[global] Instance OrderedMonad_AWP : OrderedMonad AWP (@leWH AWPH) :=
  OrderedMonad_WH AWPH AWPH_ret AWPH_bind.
#[global] Instance OrderedMonad_DWLP : OrderedMonad DWLP (@leWH DWLPH) :=
  OrderedMonad_WH DWLPH DWLPH_ret DWLPH_bind.
#[global] Instance OrderedMonad_DWP : OrderedMonad DWP (@leWH DWPH) :=
  OrderedMonad_WH DWPH DWPH_ret DWPH_bind.
#[global] Instance OrderedMonad_AWLP : OrderedMonad AWLP (@leWH AWLPH) :=
  OrderedMonad_WH AWLPH AWLPH_ret AWLPH_bind.

(* ================================================================= *)
(** ** [Rel] into AWP and DWLP                                        *)
(* ================================================================= *)

#[program] Definition wpAngelic {A} (R : Rel A) : WPure A :=
  fun Q => exists a, R a /\ Q a.
Next Obligation.
  intros p q Hpq [a [Ha Hp]]. exists a. split; [ exact Ha | exact (Hpq a Hp) ].
Qed.

#[program] Definition wpDemonic {A} (R : Rel A) : WPure A :=
  fun Q => forall a, R a -> Q a.
Next Obligation. intros p q Hpq H a Ha. exact (Hpq a (H a Ha)). Qed.

Lemma wpAngelic_AWPH {A} (R : Rel A) : AWPH A (wpAngelic R).
Proof.
  split.
  - intros [a [_ []]].
  - intros Ix i0 Q. cbn. split.
    + intros [a [Ha [i Hi]]]. exists i, a. split; assumption.
    + intros [i [a [Ha Hi]]]. exists a. split; [ exact Ha | exists i; exact Hi ].
Qed.

Definition rhoAWP {A} (R : Rel A) : AWP A := exist _ (wpAngelic R) (wpAngelic_AWPH R).

Lemma wpDemonic_DWLPH {A} (R : Rel A) : DWLPH A (wpDemonic R).
Proof.
  split.
  - intros a _. exact I.
  - intros Ix i0 Q. cbn. split.
    + intros H i a Ha. exact (H a Ha i).
    + intros H a Ha i. exact (H i a Ha).
Qed.

Definition rhoDWLP {A} (R : Rel A) : DWLP A := exist _ (wpDemonic R) (wpDemonic_DWLPH R).

Theorem rhoAWP_morphism : RelMM (@rhoAWP).
Proof.
  constructor.
  - intros A R R' HR Q. cbn. split; intros [a [Ha HQ]];
      exists a; (split; [ apply HR; exact Ha | exact HQ ]).
  - intros A a Q. cbn. split.
    + intros [x [Hx HQ]]. hnf in Hx. subst x. exact HQ.
    + intro HQ. exists a. split; [ reflexivity | exact HQ ].
  - intros A B R K Q. cbn. split.
    + intros [b [[a [Ha Hk]] HQ]]. exists a. split; [ exact Ha | exists b; split; assumption ].
    + intros [a [Ha [b [Hk HQ]]]]. exists b. split; [ exists a; split; assumption | exact HQ ].
Qed.

Theorem rhoDWLP_morphism : RelMM (@rhoDWLP).
Proof.
  constructor.
  - intros A R R' HR Q. cbn. split; intros H a Ha; apply H; apply HR; exact Ha.
  - intros A a Q. cbn. split.
    + intro H. exact (H a eq_refl).
    + intros HQ x Hx. hnf in Hx. subst x. exact HQ.
  - intros A B R K Q. cbn. split.
    + intros H a Ha b Hk. apply H. exists a. split; assumption.
    + intros H b [a [Ha Hk]]. exact (H a Ha b Hk).
Qed.

(** Both readings are onto: the healthy monad IS [Rel]. *)

Definition suppAWP {A} (w : AWP A) : Rel A := fun a => w (fun x => x = a).

Theorem rhoAWP_onto {A} (w : AWP A) : eq1 (rhoAWP (suppAWP w)) w.
Proof.
  intro Q. cbn. destruct (proj2_sig w) as [Hs Hd]. split.
  - intros [a [Ha HQ]]. refine (getWPure_mono w _ _ _ Ha).
    intros x Hx. subst x. exact HQ.
  - intro H.
    pose (F := fun (i : option {a : A | Q a}) (x : A) =>
                 match i with Some (exist _ a _) => x = a | None => False end).
    assert (Hj : getWH w (fun x => exists i, F i x)).
    { refine (getWPure_mono w Q _ _ H). intros x Hx. exists (Some (exist _ x Hx)). reflexivity. }
    destruct (proj1 (Hd _ None F) Hj) as [[[a Ha]|] Hi].
    + exists a. split; [ exact Hi | exact Ha ].
    + destruct (Hs Hi).
Qed.

Definition suppDWLP {A} (w : DWLP A) : Rel A := fun a => forall Q, w Q -> Q a.

Theorem rhoDWLP_onto {A} (w : DWLP A) : eq1 (rhoDWLP (suppDWLP w)) w.
Proof.
  intro Q. cbn. destruct (proj2_sig w) as [Ht Hc]. split.
  - intro H.
    pose (Idx := {Q' : A -> Prop | getWH w Q'}).
    assert (Hm : getWH w (fun a => forall i : Idx, proj1_sig i a)).
    { apply (proj2 (Hc Idx (exist _ (fun _ => True) Ht) (fun i => proj1_sig i))).
      intro i. exact (proj2_sig i). }
    refine (getWPure_mono w _ _ _ Hm).
    intros a Ha. apply H. intros Q' HQ'. exact (Ha (exist _ Q' HQ')).
  - intros HQ a Ha. exact (Ha Q HQ).
Qed.

(** The orders the two readings induce on [Rel].  [WP_le] ranks a
    transformer establishing more postconditions lower, so the angelic
    reading reverses inclusion and the demonic one keeps it. *)

Theorem rhoAWP_order {A} (R R' : Rel A) :
  leWH (rhoAWP R) (rhoAWP R') <-> (forall a, R' a -> R a).
Proof.
  unfold leWH, WP_le. cbn. split.
  - intros H a Ha. destruct (H (fun x => x = a) (ex_intro _ a (conj Ha eq_refl)))
      as [x [Hx ->]]. exact Hx.
  - intros H Q [a [Ha HQ]]. exists a. split; [ exact (H a Ha) | exact HQ ].
Qed.

Theorem rhoDWLP_order {A} (R R' : Rel A) :
  leWH (rhoDWLP R) (rhoDWLP R') <-> (forall a, R a -> R' a).
Proof.
  unfold leWH, WP_le. cbn. split.
  - intros H a Ha. exact (H R' (fun x Hx => Hx) a Ha).
  - intros H Q HQ a Ha. exact (HQ a (H a Ha)).
Qed.

(* ================================================================= *)
(** ** DWP and AWLP need divergence                                   *)
(* ================================================================= *)

(** Both are readings of [divnd]'s full outcome set.  On the nonempty
    fragment they land in their healthy monads. *)

Lemma wpDemonicTotal_mono {A} (m : divnd A) :
  wpure_mono (fun Q => forall o, unOptionT m o -> match o with Some a => Q a | None => False end).
Proof.
  intros p q Hpq H o Ho. specialize (H o Ho). destruct o; [ exact (Hpq _ H) | exact H ].
Qed.

Definition wpDemonicTotal {A} (m : divnd A) : WPure A := mkWPure _ (wpDemonicTotal_mono m).

#[program] Definition wpAngelicLiberal {A} (m : divnd A) : WPure A :=
  fun Q => (exists a, unOptionT m (Some a) /\ Q a) \/ unOptionT m None.
Next Obligation.
  intros p q Hpq [[a [Ha Hp]] | Hn];
    [ left; exists a; split; [ exact Ha | exact (Hpq a Hp) ] | right; exact Hn ].
Qed.

Lemma wpDemonicTotal_DWPH {A} (m : divndNE A) : DWPH A (wpDemonicTotal (getNE m)).
Proof.
  split.
  - intro H. destruct (getNE_nonEmpty m) as [o Ho].
    specialize (H o Ho). destruct o; exact H.
  - intros Ix i0 Q. cbn. split.
    + intros H i o Ho. specialize (H o Ho). destruct o; [ exact (H i) | exact H ].
    + intros H o Ho. destruct o as [a|].
      * intro i. exact (H i (Some a) Ho).
      * exact (H i0 None Ho).
Qed.

Definition obsDWP {A} (m : divndNE A) : DWP A :=
  exist _ (wpDemonicTotal (getNE m)) (wpDemonicTotal_DWPH m).

Lemma wpAngelicLiberal_AWLPH {A} (m : divndNE A) : AWLPH A (wpAngelicLiberal (getNE m)).
Proof.
  split.
  - destruct (getNE_nonEmpty m) as [[a|] Ho];
      [ left; exists a; split; [ exact Ho | exact I ] | right; exact Ho ].
  - intros Ix i0 Q. cbn. split.
    + intros [[a [Ha [i Hi]]] | Hn];
        [ exists i; left; exists a; split; assumption | exists i0; right; exact Hn ].
    + intros [i [[a [Ha Hi]] | Hn]];
        [ left; exists a; split; [ exact Ha | exists i; exact Hi ] | right; exact Hn ].
Qed.

Definition obsAWLP {A} (m : divndNE A) : AWLP A :=
  exist _ (wpAngelicLiberal (getNE m)) (wpAngelicLiberal_AWLPH m).

Theorem obsDWP_morphism : @MonadMorphism divndNE DWP _ _ _ _ (@obsDWP).
Proof.
  constructor.
  - intros A x y Hxy Q.
    cbv [eq1 Eq1__divndNE Eq1__divnd Eq1_optionT Eq1_SetM] in Hxy.
    transitivity (forall o, unOptionT (getNE x) o ->
                    match o with Some a => Q a | None => False end); [ split; intro Hc0; exact Hc0 |].
    transitivity (forall o, unOptionT (getNE y) o ->
                    match o with Some a => Q a | None => False end); [| split; intro Hc0; exact Hc0 ].
    rewrite Hxy. reflexivity.
  - intros A a Q. cbn. split.
    + intro H. exact (H (Some a) eq_refl).
    + intros HQ o Ho. subst o. exact HQ.
  - intros A B m k Q.
    transitivity (forall o, unOptionT (bindD (getNE m) (fun a => getNE (k a))) o ->
                    match o with Some b => Q b | None => False end);
      [ split; intro Hc0; exact Hc0 |].
    transitivity (forall o, unOptionT (getNE m) o ->
                    match o with
                    | Some a => forall o', unOptionT (getNE (k a)) o' ->
                                  match o' with Some b => Q b | None => False end
                    | None => False
                    end);
      [| split; intro Hc0; exact Hc0 ].
    split.
    + intros H o Ho. destruct o as [a|].
      * intros o' Ho'. apply H. apply outcomes_bind.
        exists (Some a). split; assumption.
      * apply (H None). apply outcomes_bind. exists None. split; [ exact Ho | reflexivity ].
    + intros H o Ho. apply outcomes_bind in Ho. destruct Ho as [[a|] [Hm Hk]].
      * exact (H (Some a) Hm o Hk).
      * subst o. exact (H None Hm).
Qed.

Theorem obsAWLP_morphism : @MonadMorphism divndNE AWLP _ _ _ _ (@obsAWLP).
Proof.
  constructor.
  - intros A x y Hxy Q.
    cbv [eq1 Eq1__divndNE Eq1__divnd Eq1_optionT Eq1_SetM] in Hxy.
    transitivity ((exists a, unOptionT (getNE x) (Some a) /\ Q a) \/ unOptionT (getNE x) None);
      [ split; intro Hc0; exact Hc0 |].
    transitivity ((exists a, unOptionT (getNE y) (Some a) /\ Q a) \/ unOptionT (getNE y) None);
      [| split; intro Hc0; exact Hc0 ].
    rewrite Hxy. reflexivity.
  - intros A a Q. cbn. split.
    + intros [[x [Hx HQ]] | Hn]; [ injection Hx as ->; exact HQ | discriminate Hn ].
    + intro HQ. left. exists a. split; [ reflexivity | exact HQ ].
  - intros A B m k Q.
    transitivity ((exists b, unOptionT (bindD (getNE m) (fun a => getNE (k a))) (Some b) /\ Q b)
                  \/ unOptionT (bindD (getNE m) (fun a => getNE (k a))) None);
      [ split; intro Hc0; exact Hc0 |].
    transitivity ((exists a, unOptionT (getNE m) (Some a) /\
                     ((exists b, unOptionT (getNE (k a)) (Some b) /\ Q b)
                      \/ unOptionT (getNE (k a)) None))
                  \/ unOptionT (getNE m) None);
      [| split; intro Hc0; exact Hc0 ].
    split.
    + intros [[b [Hb HQ]] | Hn].
      * apply outcomes_bind in Hb. destruct Hb as [[a|] [Hm Hk]]; [| discriminate Hk ].
        left. exists a. split; [ exact Hm | left; exists b; split; assumption ].
      * apply outcomes_bind in Hn. destruct Hn as [[a|] [Hm Hk]].
        -- left. exists a. split; [ exact Hm | right; exact Hk ].
        -- right. exact Hm.
    + intros [[a [Hm [[b [Hb HQ]] | Hn]]] | Hn].
      * left. exists b. split; [| exact HQ ]. apply outcomes_bind.
        exists (Some a). split; assumption.
      * right. apply outcomes_bind. exists (Some a). split; assumption.
      * right. apply outcomes_bind. exists None. split; [ exact Hn | reflexivity ].
Qed.

(** The slice forgets what they read: two programs with the same terminating
    outcomes, one of which may also diverge. *)
Example obs_not_via_slice :
  exists m1 m2 : divndNE unit,
    relIff (slice (getNE m1)) (slice (getNE m2))
    /\ ~ eq1 (obsDWP m1) (obsDWP m2) /\ ~ eq1 (obsAWLP m1) (obsAWLP m2).
Proof.
  exists (retNE tt), (orNE (retNE tt) divergeNE). split; [| split ].
  - intro u. unfold slice. cbn. split.
    + intro H. left. exact H.
    + intros [H | H]; [ exact H | discriminate H ].
  - intro H.
    assert (H1 : getWH (obsDWP (retNE tt)) (fun _ => True)).
    { cbn. intros o Ho. subst o. exact I. }
    pose proof (proj1 (H (fun _ => True)) H1) as H2. cbn in H2.
    exact (H2 None (or_intror eq_refl)).
  - intro H.
    assert (H1 : getWH (obsAWLP (orNE (retNE tt) divergeNE)) (fun _ => False)).
    { cbn. right. right. reflexivity. }
    pose proof (proj2 (H (fun _ => False)) H1) as H2. cbn in H2.
    destruct H2 as [[u [_ []]] | Hn]. discriminate Hn.
Qed.

(** And no reading of [Rel] can recover them.  The proof uses two
    relations.  The empty relation [z] must read the same after either of
    two continuations, which pins its value.  The full relation on [bool],
    followed by a continuation that is empty on one branch, must read as a
    single [ret].  DWP's strictness and conjunctivity then force the full
    relation's reading to establish [False]. *)
Theorem no_reading_Rel_DWP : ~ exists σ : (forall A, Rel A -> DWP A), RelMM σ.
Proof.
  intros [σ Hσ].
  pose (sem := fun A (R : Rel A) (Q : A -> Prop) => getWH (σ A R) Q).
  assert (Hmono : forall A (R : Rel A) (P Q : A -> Prop),
             (forall a, P a -> Q a) -> sem A R P -> sem A R Q).
  { intros A R P Q HPQ. exact (getWPure_mono _ P Q HPQ). }
  assert (Hret : forall A (a : A) Q, sem A (PredM.retPred a) Q <-> Q a).
  { intros A a Q. exact (mm_ret Hσ a Q). }
  assert (Hbind : forall A B (R : Rel A) (K : A -> Rel B) Q,
             sem B (PredM.bindPred R K) Q <-> sem A R (fun a => sem B (K a) Q)).
  { intros A B R K Q. exact (mm_bind Hσ R K Q). }
  assert (Hprop : forall A (R R' : Rel A), relIff R R' ->
             forall Q, sem A R Q <-> sem A R' Q).
  { intros A R R' HR Q. exact (mm_proper Hσ R R' HR Q). }
  assert (Hstrict : forall A (R : Rel A), ~ sem A R (fun _ => False)).
  { intros A R. exact (proj1 (proj2_sig (σ A R))). }
  assert (Hconj : forall A (R : Rel A), wpConjunctive (getWH (σ A R))).
  { intros A R. exact (proj2 (proj2_sig (σ A R))). }
  (* the empty relation reads the same after [ret true] and [ret false] *)
  assert (Hz : forall (b : bool) (Q : bool -> Prop),
             sem bool (PredM.bindPred (fun _ : unit => False) (fun _ => PredM.retPred b)) Q
             <-> sem unit (fun _ => False) (fun _ => Q b)).
  { intros b Q. rewrite Hbind.
    split; intro H; refine (Hmono _ _ _ _ _ H); intros u Hu;
      [ exact (proj1 (Hret _ b Q) Hu) | exact (proj2 (Hret _ b Q) Hu) ]. }
  assert (Hz01 : forall Q : bool -> Prop,
             sem unit (fun _ => False) (fun _ => Q true)
             <-> sem unit (fun _ => False) (fun _ => Q false)).
  { intro Q. rewrite <- (Hz true Q), <- (Hz false Q). apply Hprop.
    intro b'. split; intros [u [[] _]]. }
  (* so it establishes nothing *)
  assert (Hztop : ~ sem unit (fun _ => False) (fun _ => True)).
  { intro H. apply (Hstrict unit (fun _ => False)).
    refine (Hmono _ _ (fun _ => false = true) _ _ _); [ intros _ Hf; discriminate Hf |].
    apply (proj1 (Hz01 (fun b => b = true))).
    refine (Hmono _ _ _ _ _ H). intros _ _. reflexivity. }
  (* the full relation, continued by [K], is [ret tt] *)
  pose (full := fun _ : bool => True).
  assert (Hc : forall K : bool -> Rel unit,
             relIff (PredM.bindPred full K) (PredM.retPred tt) ->
             sem bool full (fun b => sem unit (K b) (fun _ => True))).
  { intros K HK. apply (proj1 (Hbind _ _ full K (fun _ => True))).
    apply (proj2 (Hprop _ _ _ HK (fun _ => True))).
    apply (proj2 (Hret _ tt (fun _ => True))). exact I. }
  assert (HK1 : relIff (PredM.bindPred full
                          (fun b => if b then PredM.retPred tt else (fun _ => False)))
                        (PredM.retPred tt)).
  { intro u. split.
    - intros [[|] [_ Hb]]; [ exact Hb | destruct Hb ].
    - intro Hu. exists true. split; [ exact I | exact Hu ]. }
  assert (HK2 : relIff (PredM.bindPred full
                          (fun b => if b then (fun _ => False) else PredM.retPred tt))
                        (PredM.retPred tt)).
  { intro u. split.
    - intros [[|] [_ Hb]]; [ destruct Hb | exact Hb ].
    - intro Hu. exists false. split; [ exact I | exact Hu ]. }
  assert (H1 : sem bool full (fun b => b = true)).
  { refine (Hmono _ _ _ _ _ (Hc _ HK1)).
    intros [|] Hb; [ reflexivity | exfalso; exact (Hztop Hb) ]. }
  assert (H2 : sem bool full (fun b => b = false)).
  { refine (Hmono _ _ _ _ _ (Hc _ HK2)).
    intros [|] Hb; [ exfalso; exact (Hztop Hb) | reflexivity ]. }
  (* conjunctivity combines the two, strictness refutes the result *)
  assert (H12 : sem bool full (fun b => forall i : bool, if i then b = true else b = false)).
  { apply (proj2 (Hconj bool full bool true (fun i b => if i then b = true else b = false))).
    intros [|]; [ exact H1 | exact H2 ]. }
  apply (Hstrict bool full). refine (Hmono _ _ _ _ _ H12).
  intros b Hb. pose proof (Hb true) as Ht. pose proof (Hb false) as Hf.
  cbn in Ht, Hf. rewrite Ht in Hf. discriminate Hf.
Qed.

Theorem no_reading_Rel_AWLP : ~ exists σ : (forall A, Rel A -> AWLP A), RelMM σ.
Proof.
  intros [σ Hσ].
  pose (sem := fun A (R : Rel A) (Q : A -> Prop) => getWH (σ A R) Q).
  assert (Hmono : forall A (R : Rel A) (P Q : A -> Prop),
             (forall a, P a -> Q a) -> sem A R P -> sem A R Q).
  { intros A R P Q HPQ. exact (getWPure_mono _ P Q HPQ). }
  assert (Hret : forall A (a : A) Q, sem A (PredM.retPred a) Q <-> Q a).
  { intros A a Q. exact (mm_ret Hσ a Q). }
  assert (Hbind : forall A B (R : Rel A) (K : A -> Rel B) Q,
             sem B (PredM.bindPred R K) Q <-> sem A R (fun a => sem B (K a) Q)).
  { intros A B R K Q. exact (mm_bind Hσ R K Q). }
  assert (Hprop : forall A (R R' : Rel A), relIff R R' ->
             forall Q, sem A R Q <-> sem A R' Q).
  { intros A R R' HR Q. exact (mm_proper Hσ R R' HR Q). }
  assert (Hterm : forall A (R : Rel A), sem A R (fun _ => True)).
  { intros A R. exact (proj1 (proj2_sig (σ A R))). }
  assert (Hdisj : forall A (R : Rel A), wpDisjunctive (getWH (σ A R))).
  { intros A R. exact (proj2 (proj2_sig (σ A R))). }
  assert (Hz : forall (b : bool) (Q : bool -> Prop),
             sem bool (PredM.bindPred (fun _ : unit => False) (fun _ => PredM.retPred b)) Q
             <-> sem unit (fun _ => False) (fun _ => Q b)).
  { intros b Q. rewrite Hbind.
    split; intro H; refine (Hmono _ _ _ _ _ H); intros u Hu;
      [ exact (proj1 (Hret _ b Q) Hu) | exact (proj2 (Hret _ b Q) Hu) ]. }
  assert (Hz01 : forall Q : bool -> Prop,
             sem unit (fun _ => False) (fun _ => Q true)
             <-> sem unit (fun _ => False) (fun _ => Q false)).
  { intro Q. rewrite <- (Hz true Q), <- (Hz false Q). apply Hprop.
    intro b'. split; intros [u [[] _]]. }
  (* the empty relation establishes everything *)
  assert (Hzbot : sem unit (fun _ => False) (fun _ => False)).
  { refine (Hmono _ _ (fun _ => false = true) _ _ _); [ intros _ Hf; discriminate Hf |].
    apply (proj1 (Hz01 (fun b => b = true))).
    refine (Hmono _ _ _ _ _ (Hterm unit (fun _ => False))). intros _ _. reflexivity. }
  pose (full := fun _ : bool => True).
  assert (Hc : forall K : bool -> Rel unit,
             relIff (PredM.bindPred full K) (PredM.retPred tt) ->
             ~ sem bool full (fun b => sem unit (K b) (fun _ => False))).
  { intros K HK H. apply (proj1 (Hret _ tt (fun _ => False))).
    apply (proj1 (Hprop _ _ _ HK (fun _ => False))).
    apply (proj2 (Hbind _ _ full K (fun _ => False))). exact H. }
  assert (HK1 : relIff (PredM.bindPred full
                          (fun b => if b then PredM.retPred tt else (fun _ => False)))
                        (PredM.retPred tt)).
  { intro u. split.
    - intros [[|] [_ Hb]]; [ exact Hb | destruct Hb ].
    - intro Hu. exists true. split; [ exact I | exact Hu ]. }
  assert (HK2 : relIff (PredM.bindPred full
                          (fun b => if b then (fun _ => False) else PredM.retPred tt))
                        (PredM.retPred tt)).
  { intro u. split.
    - intros [[|] [_ Hb]]; [ destruct Hb | exact Hb ].
    - intro Hu. exists false. split; [ exact I | exact Hu ]. }
  assert (N1 : ~ sem bool full (fun b => b = false)).
  { intro H. apply (Hc _ HK1). refine (Hmono _ _ _ _ _ H).
    intros [|] Hb; [ discriminate Hb | exact Hzbot ]. }
  assert (N2 : ~ sem bool full (fun b => b = true)).
  { intro H. apply (Hc _ HK2). refine (Hmono _ _ _ _ _ H).
    intros [|] Hb; [ exact Hzbot | discriminate Hb ]. }
  (* termination and disjunctivity pick one branch, which is refuted *)
  assert (Hex : sem bool full (fun b => exists i : bool, if i then b = true else b = false)).
  { refine (Hmono _ _ _ _ _ (Hterm bool full)). intros b _. exists b. destruct b; reflexivity. }
  destruct (proj1 (Hdisj bool full bool true (fun i b => if i then b = true else b = false)) Hex)
    as [[|] Hi].
  - exact (N2 Hi).
  - exact (N1 Hi).
Qed.

(* ================================================================= *)
(** ** [Rel] into the four SP monads                                  *)
(* ================================================================= *)

Definition rhoASP {A} (R : Rel A) : ASP A := aspOfPred R.
Definition rhoDSLP {A} (R : Rel A) : DSLP A := dslpOfPred R.
Definition rhoDSP {A} (R : Rel A) : DSP A := dspOfPred R.
Definition rhoASLP {A} (R : Rel A) : ASLP A := aslpOfPred R.

Theorem rhoASP_morphism : RelMM (@rhoASP).
Proof.
  constructor.
  - intros A R R' HR. apply eq1_ASP_get. intros p a. unfold rhoASP.
    rewrite !getASP_of. rewrite (HR a). reflexivity.
  - intros A a. apply eq1_ASP_get. intros p b. unfold rhoASP. cbn [ret Monad_ASP].
    rewrite getASP_of, getASP_ret.
    split; intros [Hp Hb]; (split; [ exact Hp | hnf in Hb |- *; symmetry; exact Hb ]).
  - intros A B R K. apply eq1_ASP_get. intros p b. unfold rhoASP. cbn [bind Monad_ASP].
    rewrite getASP_of, getASP_bind. setoid_rewrite getASP_of. cbn. split.
    + intros [Hp [a [Ha Hk]]]. exists a. split; [ split; assumption | split; [ exact I | exact Hk ] ].
    + intros [a [[Hp Ha] [_ Hk]]]. split; [ exact Hp | exists a; split; assumption ].
Qed.

Lemma dslpRel_of_pred {A} (Q : A -> Prop) (b : A) : dslpRel (dslpOfPred Q) tt b <-> Q b.
Proof. exact (dslpRel_ofRel (fun (_ : unit) => Q) tt b). Qed.

Theorem rhoDSLP_morphism : RelMM (@rhoDSLP).
Proof.
  constructor.
  - intros A R R' HR. apply eq1_DSLP_get. intros p a. unfold rhoDSLP.
    rewrite !getDSLP_of. rewrite (HR a). reflexivity.
  - intros A a. apply eq1_DSLP_get. intros p b. unfold rhoDSLP. cbn [ret Monad_DSLP].
    rewrite getDSLP_of, getDSLP_ret.
    split; intros H Hb; apply H; hnf in Hb |- *; symmetry; exact Hb.
  - intros A B R K. apply eq1_DSLP_get. intros p b. unfold rhoDSLP. cbn [bind Monad_DSLP].
    rewrite getDSLP_of, getDSLP_bind. setoid_rewrite dslpRel_of_pred.
    setoid_rewrite getDSLP_of. cbn. split.
    + intros H a Hk Ha. apply H. exists a. split; assumption.
    + intros H [a [Ha Hk]]. exact (H a Hk Ha).
Qed.

(** DSP and ASLP are read through their recovered relations. *)

Lemma eq1_DSP_rel {A} (w v : DSP A) :
  (forall y, dspRel w tt y <-> dspRel v tt y) -> eq1 w v.
Proof.
  intros H P y. rewrite (dspRel_spec w P y), (dspRel_spec v P y).
  apply dspOf_cong. intros [] y'. apply H.
Qed.

Lemma dspRel_of_pred {A} (Q : A -> Prop) (b : A) : dspRel (dspOfPred Q) tt b <-> Q b.
Proof. exact (dspRel_ofRelArr (fun (_ : unit) a => Q a) tt b). Qed.

Lemma dspRel_retDSP {A} (a : A) (b : A) : dspRel (ret a : DSP A) tt b <-> a = b.
Proof. exact (@rd_pure DSPArr _ _ _ (@dspRel) RelDenote_DSP unit A (fun _ => a) tt b). Qed.

Lemma dspRel_bindDSP {A B} (m : DSP A) (k : A -> DSP B) (b : B) :
  dspRel (bind m k) tt b <-> exists a, dspRel m tt a /\ dspRel (k a) tt b.
Proof. exact (rel_bind (arr := DSPArr) (rel := @dspRel) m k tt b). Qed.

Theorem rhoDSP_morphism : RelMM (@rhoDSP).
Proof.
  constructor.
  - intros A R R' HR. apply eq1_DSP_rel. intro y. unfold rhoDSP.
    rewrite !dspRel_of_pred. apply HR.
  - intros A a. apply eq1_DSP_rel. intro y. unfold rhoDSP.
    rewrite dspRel_of_pred, dspRel_retDSP. split; intro H; hnf in H |- *; symmetry; exact H.
  - intros A B R K. apply eq1_DSP_rel. intro y. unfold rhoDSP.
    rewrite dspRel_of_pred, dspRel_bindDSP. setoid_rewrite dspRel_of_pred. reflexivity.
Qed.

Lemma eq1_ASLP_rel {A} (w v : ASLP A) :
  (forall y, aslpRel w tt y <-> aslpRel v tt y) -> eq1 w v.
Proof.
  intros H P y. rewrite (aslpRel_spec w P y), (aslpRel_spec v P y).
  apply aslpOf_cong. intros [] y'. apply H.
Qed.

Lemma aslpRel_of_pred {A} (Q : A -> Prop) (b : A) : aslpRel (aslpOfPred Q) tt b <-> Q b.
Proof. exact (aslpRel_ofRelArr (fun (_ : unit) a => Q a) tt b). Qed.

Lemma aslpRel_retASLP {A} (a : A) (b : A) : aslpRel (ret a : ASLP A) tt b <-> a = b.
Proof. exact (@rd_pure ASLPArr _ _ _ (@aslpRel) RelDenote_ASLP unit A (fun _ => a) tt b). Qed.

Lemma aslpRel_bindASLP {A B} (m : ASLP A) (k : A -> ASLP B) (b : B) :
  aslpRel (bind m k) tt b <-> exists a, aslpRel m tt a /\ aslpRel (k a) tt b.
Proof. exact (rel_bind (arr := ASLPArr) (rel := @aslpRel) m k tt b). Qed.

Theorem rhoASLP_morphism : RelMM (@rhoASLP).
Proof.
  constructor.
  - intros A R R' HR. apply eq1_ASLP_rel. intro y. unfold rhoASLP.
    rewrite !aslpRel_of_pred. apply HR.
  - intros A a. apply eq1_ASLP_rel. intro y. unfold rhoASLP.
    rewrite aslpRel_of_pred, aslpRel_retASLP. split; intro H; hnf in H |- *; symmetry; exact H.
  - intros A B R K. apply eq1_ASLP_rel. intro y. unfold rhoASLP.
    rewrite aslpRel_of_pred, aslpRel_bindASLP. setoid_rewrite aslpRel_of_pred. reflexivity.
Qed.

(** Composed with [slice], each reading is an observation of [divnd]. *)

Corollary obsASP_morphism :
  @MonadMorphism divnd ASP Monad__divnd _ Eq1__divnd _ (fun A m => rhoASP (slice m)).
Proof.
  exact (@MonadMorphism_comp divnd PredM.Pred ASP _ _ _ Eq1__divnd PredM.Eq1_Pred _ _
           (@slice) (@rhoASP) slice_morphism rhoASP_morphism).
Qed.

Corollary obsAWP_morphism :
  @MonadMorphism divnd AWP Monad__divnd _ Eq1__divnd _ (fun A m => rhoAWP (slice m)).
Proof.
  exact (@MonadMorphism_comp divnd PredM.Pred AWP _ _ _ Eq1__divnd PredM.Eq1_Pred _ _
           (@slice) (@rhoAWP) slice_morphism rhoAWP_morphism).
Qed.

(* ================================================================= *)
(** ** Without state, DSP is ASP and ASLP is DSLP                     *)
(* ================================================================= *)

(** At input [unit] a DSP element reads its relation angelically and an
    ASLP element demonically: there is only one start state to quantify
    over. *)

Lemma getDSP_unit {A} (w : DSP A) (P : unit -> Prop) (y : A) :
  getDSP w P y <-> P tt /\ dspRel w tt y.
Proof.
  rewrite dspRel_spec. unfold dspOf, aspOf, dslpOf. split.
  - intros [[[] [HP HR]] _]. split; assumption.
  - intros [HP HR]. split; [ exists tt; split; assumption | intros [] _; exact HP ].
Qed.

Lemma getASLP_unit {A} (w : ASLP A) (P : unit -> Prop) (y : A) :
  getASLP w P y <-> (aslpRel w tt y -> P tt).
Proof.
  rewrite aslpRel_spec. unfold aslpOf, aspOf, dslpOf. split.
  - intros [[[] [HP _]] | H] HR; [ exact HP | exact (H tt HR) ].
  - intro H. right. intros [] HR. exact (H HR).
Qed.

Theorem rhoDSP_is_rhoASP {A} (R : Rel A) (p : Prop) (y : A) :
  getDSPPure (rhoDSP R) p y <-> getASP (rhoASP R) p y.
Proof.
  unfold getDSPPure, rhoASP. rewrite getDSP_unit, getASP_of.
  unfold rhoDSP. rewrite dspRel_of_pred. reflexivity.
Qed.

Theorem rhoASLP_is_rhoDSLP {A} (R : Rel A) (p : Prop) (y : A) :
  getASLPPure (rhoASLP R) p y <-> getDSLP (rhoDSLP R) p y.
Proof.
  unfold getASLPPure, rhoDSLP. rewrite getASLP_unit, getDSLP_of.
  unfold rhoASLP. rewrite aslpRel_of_pred. reflexivity.
Qed.

(** The reading's own order is therefore relational: inclusion for DSP,
    reverse inclusion for ASLP. *)

Theorem ordDSP_unit {A} (m n : DSP A) : ordDSP m n <-> ordDSPRel m n.
Proof.
  unfold ordDSP, ordDSPRel. split.
  - intros H [] b Hm.
    assert (Hn : getDSP n (fun _ => True) b).
    { apply H. apply (proj2 (getDSP_unit m (fun _ => True) b)). split; [ exact I | exact Hm ]. }
    exact (proj2 (proj1 (getDSP_unit n (fun _ => True) b) Hn)).
  - intros H P b Hm. destruct (proj1 (getDSP_unit m P b) Hm) as [HP Hr].
    apply (proj2 (getDSP_unit n P b)). split; [ exact HP | exact (H tt b Hr) ].
Qed.

Theorem ordASLP_unit {A} (m n : ASLP A) : ordASLP m n <-> ordASLPRel n m.
Proof.
  unfold ordASLP, ordASLPRel. split.
  - intros H [] b Hn.
    assert (Hm : getASLP m (fun _ => aslpRel m tt b) b).
    { apply (proj2 (getASLP_unit m (fun _ => aslpRel m tt b) b)). intro Hr. exact Hr. }
    exact (proj1 (getASLP_unit n (fun _ => aslpRel m tt b) b) (H _ b Hm) Hn).
  - intros H P b Hm. apply (proj2 (getASLP_unit n P b)). intro Hn.
    exact (proj1 (getASLP_unit m P b) Hm (H tt b Hn)).
Qed.

Theorem OrderedMonad_DSP_reading : OrderedMonad DSP (@ordDSP).
Proof.
  apply (OrderedMonad_iff (@ordDSPRel)); [| exact OrderedMonad_DSP ].
  intros A x y. symmetry. apply ordDSP_unit.
Qed.

Theorem OrderedMonad_ASLP_reading : OrderedMonad ASLP (@ordASLP).
Proof.
  apply (OrderedMonad_iff (fun A x y => ordASLPRel y x));
    [| exact (@OrderedMonad_flip ASLP _ _ Eq1Equivalence_ASLP (@ordASLPRel) OrderedMonad_ASLP) ].
  intros A x y. symmetry. apply ordASLP_unit.
Qed.

(* ================================================================= *)
(** ** The orders the SP readings induce on [Rel]                     *)
(* ================================================================= *)

Theorem rhoASP_order {A} (R R' : Rel A) :
  ordASP (rhoASP R) (rhoASP R') <-> (forall a, R a -> R' a).
Proof.
  rewrite ordASP_get. unfold rhoASP. setoid_rewrite getASP_of. split.
  - intros H a Ha. exact (proj2 (H True a (conj I Ha))).
  - intros H p a [Hp Ha]. exact (conj Hp (H a Ha)).
Qed.

Theorem rhoDSLP_order {A} (R R' : Rel A) :
  ordDSLP (rhoDSLP R) (rhoDSLP R') <-> (forall a, R' a -> R a).
Proof.
  rewrite ordDSLP_get. unfold rhoDSLP. setoid_rewrite getDSLP_of. split.
  - intros H a Ha'. exact (H (R a) a (fun h => h) Ha').
  - intros H p a Hp Ha'. exact (Hp (H a Ha')).
Qed.

Theorem rhoDSP_order {A} (R R' : Rel A) :
  ordDSP (rhoDSP R) (rhoDSP R') <-> (forall a, R a -> R' a).
Proof.
  rewrite ordDSP_unit. unfold ordDSPRel, rhoDSP. split.
  - intros H a Ha. apply (proj1 (dspRel_of_pred R' a)). apply H.
    exact (proj2 (dspRel_of_pred R a) Ha).
  - intros H [] a Ha. apply (proj2 (dspRel_of_pred R' a)). apply H.
    exact (proj1 (dspRel_of_pred R a) Ha).
Qed.

Theorem rhoASLP_order {A} (R R' : Rel A) :
  ordASLP (rhoASLP R) (rhoASLP R') <-> (forall a, R' a -> R a).
Proof.
  rewrite ordASLP_unit. unfold ordASLPRel, rhoASLP. split.
  - intros H a Ha. apply (proj1 (aslpRel_of_pred R a)). apply H.
    exact (proj2 (aslpRel_of_pred R' a) Ha).
  - intros H [] a Ha. apply (proj2 (aslpRel_of_pred R a)). apply H.
    exact (proj1 (aslpRel_of_pred R' a) Ha).
Qed.

(* ================================================================= *)
(** ** Which triples an index carves out                              *)
(* ================================================================= *)

(** [T] is carved out when some index [w] has [T x <-> ρ x <= w], so the
    Dijkstra monad at [w] contains exactly the computations the triple
    accepts.  The other direction is the same notion for the opposite
    order. *)
Definition carvedBy {X W : Type} (le : W -> W -> Prop) (ρ : X -> W) (T : X -> Prop) : Prop :=
  exists w, forall x, T x <-> le (ρ x) w.

(** For a reading onto its monad that reflects an order [sq] on its source,
    the carvable classes are exactly the principal down-sets of [sq]. *)
Theorem carved_iso {X W : Type} (le : W -> W -> Prop) (ρ : X -> W)
  (sq : X -> X -> Prop)
  (le_trans : forall u v w, le u v -> le v w -> le u w)
  (onto : forall w, exists x, le (ρ x) w /\ le w (ρ x))
  (emb : forall x y, le (ρ x) (ρ y) <-> sq x y) (T : X -> Prop) :
  carvedBy le ρ T <-> exists x0, forall x, T x <-> sq x x0.
Proof.
  split.
  - intros [w Hw]. destruct (onto w) as [x0 [H1 H2]]. exists x0. intro x.
    rewrite Hw, <- emb. split; intro H.
    + exact (le_trans _ _ _ H H2).
    + exact (le_trans _ _ _ H H1).
  - intros [x0 Hx0]. exists (ρ x0). intro x. rewrite Hx0, emb. reflexivity.
Qed.

Lemma getASP_rel {A} (w : ASP A) (p : Prop) (a : A) :
  getASP w p a <-> p /\ aspRel w tt a.
Proof.
  unfold getASP. rewrite get_aspRel.
  split; [ intros [[] [Hp Hr]]; split; assumption | intros [Hp Hr]; exists tt; split; assumption ].
Qed.

Lemma rhoASP_onto {A} (w : ASP A) :
  ordASP (rhoASP (fun a => aspRel w tt a)) w /\ ordASP w (rhoASP (fun a => aspRel w tt a)).
Proof.
  unfold rhoASP. rewrite !ordASP_get. setoid_rewrite getASP_of. setoid_rewrite getASP_rel.
  split; intros p a H; exact H.
Qed.

Corollary carved_ASP_iff {A} (T : Rel A -> Prop) :
  carvedBy ordASP rhoASP T <-> exists W0 : Rel A, forall R, T R <-> (forall a, R a -> W0 a).
Proof.
  apply (carved_iso ordASP rhoASP (fun R R' => forall a, R a -> R' a)).
  - intros u v w H1 H2. exact (PreOrder_Transitive u v w H1 H2).
  - intro w. exists (fun a => aspRel w tt a). exact (rhoASP_onto w).
  - intros R R'. apply rhoASP_order.
Qed.

Corollary carved_ASP_op_iff {A} (T : Rel A -> Prop) :
  carvedBy (fun x y => ordASP y x) rhoASP T
  <-> exists W0 : Rel A, forall R, T R <-> (forall a, W0 a -> R a).
Proof.
  apply (carved_iso (fun x y => ordASP y x) rhoASP (fun R R' => forall a, R' a -> R a)).
  - intros u v w H1 H2. exact (PreOrder_Transitive w v u H2 H1).
  - intro w. exists (fun a => aspRel w tt a).
    destruct (rhoASP_onto w) as [H1 H2]. split; assumption.
  - intros R R'. apply rhoASP_order.
Qed.

(** *** Three triples, as classes of relations *)

(** Hoare: every outcome satisfies [Q] (ASP [Over], DWLP [SubsetOf]). *)
Definition hoare {A} (p : Prop) (Q : A -> Prop) (R : Rel A) : Prop :=
  p -> forall a, R a -> Q a.

(** Incorrectness: every [Q]-outcome is reached (ASP [Under]). *)
Definition incorrect {A} (p : Prop) (Q : A -> Prop) (R : Rel A) : Prop :=
  forall a, Q a -> p /\ R a.

(** Angelic total correctness: some outcome satisfies [Q] (AWP [SubsetOf]). *)
Definition angelic {A} (p : Prop) (Q : A -> Prop) (R : Rel A) : Prop :=
  p -> exists a, R a /\ Q a.

Lemma hoare_is_ASP_Over {A} p Q (R : Rel A) :
  hoare p Q R <-> forall a, getASP (rhoASP R) p a -> Q a.
Proof.
  unfold rhoASP. setoid_rewrite getASP_of.
  split; [ intros H a [Hp Ha]; exact (H Hp a Ha) | intros H Hp a Ha; exact (H a (conj Hp Ha)) ].
Qed.

Lemma incorrect_is_ASP_Under {A} p Q (R : Rel A) :
  incorrect p Q R <-> forall a, Q a -> getASP (rhoASP R) p a.
Proof. unfold rhoASP. setoid_rewrite getASP_of. reflexivity. Qed.

Lemma angelic_is_AWP_Sub {A} p Q (R : Rel A) :
  angelic p Q R <-> (p -> rhoAWP R Q).
Proof. reflexivity. Qed.

(** Hoare triples are a single inclusion, [R ⊆ {a | p -> Q a}]. *)
Theorem hoare_carved_ASP {A} (p : Prop) (Q : A -> Prop) :
  carvedBy ordASP rhoASP (hoare p Q).
Proof.
  apply carved_ASP_iff. exists (fun a => p -> Q a). intro R. unfold hoare.
  split; [ intros H a Ha Hp; exact (H Hp a Ha) | intros H Hp a Ha; exact (H a Ha Hp) ].
Qed.

Theorem hoare_carved_DWLP {A} (p : Prop) (Q : A -> Prop) :
  carvedBy leWH rhoDWLP (hoare p Q).
Proof.
  exists (rhoDWLP (fun a => p -> Q a)). intro R. rewrite rhoDWLP_order. unfold hoare.
  split; [ intros H a Ha Hp; exact (H Hp a Ha) | intros H Hp a Ha; exact (H a Ha Hp) ].
Qed.

(** Incorrectness triples are [Q ⊆ R] once satisfiable, and an index for an
    unsatisfiable one would have to exclude the full relation, which lies
    above every index. *)
Theorem incorrect_carved_iff {A} (p : Prop) (Q : A -> Prop) :
  carvedBy (fun x y => ordASP y x) rhoASP (incorrect p Q) <-> (forall a, Q a -> p).
Proof.
  rewrite carved_ASP_op_iff. split.
  - intros [W0 HW] a Ha. exact (proj1 (proj2 (HW (fun _ => True)) (fun _ _ => I) a Ha)).
  - intro Hsat. exists Q. intro R. unfold incorrect. split.
    + intros H a Ha. exact (proj2 (H a Ha)).
    + intros H a Ha. exact (conj (Hsat a Ha) (H a Ha)).
Qed.

(** "Some outcome satisfies [Q]" is a union of inclusions, one per outcome
    in [Q], so with two outcomes in [Q] it is not carved out by AWP in either
    direction. *)
Theorem angelic_not_carved_AWP {A} (p : Prop) (Q : A -> Prop) (q1 q2 : A) :
  p -> Q q1 -> Q q2 -> q1 <> q2 ->
  ~ carvedBy leWH rhoAWP (angelic p Q)
  /\ ~ carvedBy (fun x y => leWH y x) rhoAWP (angelic p Q).
Proof.
  intros Hp Hq1 Hq2 Hne. split.
  - intros [w Hw].
    assert (H1 : leWH (rhoAWP (fun a => a = q1)) w).
    { apply Hw. intros _. exists q1. split; [ reflexivity | exact Hq1 ]. }
    assert (H2 : leWH (rhoAWP (fun a => a = q2)) w).
    { apply Hw. intros _. exists q2. split; [ reflexivity | exact Hq2 ]. }
    assert (H0 : leWH (rhoAWP (fun _ => False)) w).
    { intros Q' HQ'. exfalso.
      destruct (proj2 (rhoAWP_onto w Q') HQ') as [a [Ha _]].
      destruct (H1 (fun x => x = a) Ha) as [x1 [-> <-]].
      destruct (H2 (fun x => x = q1) Ha) as [x2 [-> Heq]].
      exact (Hne (eq_sym Heq)). }
    destruct (proj2 (Hw _) H0 Hp) as [a [[] _]].
  - intros [w Hw].
    assert (H0 : leWH w (rhoAWP (fun _ => False))) by (intros Q' [a [[] _]]).
    destruct (proj2 (Hw _) H0 Hp) as [a [[] _]].
Qed.

(** *** Room beyond the image *)

(** [WPure] holds every monotone transformer, not just the healthy ones.
    Two of them carve out the two WP triple shapes for ANY reading. *)

#[program] Definition wpSub {A} (p : Prop) (Q : A -> Prop) : WPure A :=
  fun Q' => p /\ forall a, Q a -> Q' a.
Next Obligation.
  intros k k' Hk [Hp HQ]. split; [ exact Hp | intros a Ha; exact (Hk a (HQ a Ha)) ].
Qed.

#[program] Definition wpSup {A} (p : Prop) (Q : A -> Prop) : WPure A :=
  fun Q' => (forall a, Q' a -> Q a) -> p.
Next Obligation. intros k k' Hk H HQ. apply H. intros a Ha. exact (HQ a (Hk a Ha)). Qed.

Theorem wp_sub_carved {X A} (ρ : X -> WPure A) (p : Prop) (Q : A -> Prop) :
  carvedBy WP_le ρ (fun x => p -> ρ x Q).
Proof.
  exists (wpSub p Q). intro x. split.
  - intros H k [Hp HQ]. exact (getWPure_mono (ρ x) Q k HQ (H Hp)).
  - intros H Hp. exact (H Q (conj Hp (fun a Ha => Ha))).
Qed.

Theorem wp_sup_carved {X A} (ρ : X -> WPure A) (p : Prop) (Q : A -> Prop) :
  carvedBy (fun w v => WP_le v w) ρ (fun x => ρ x Q -> p).
Proof.
  exists (wpSup p Q). intro x. split.
  - intros H k Hk HkQ. apply H. exact (getWPure_mono (ρ x) k Q HkQ Hk).
  - intros H HQ. exact (H Q HQ (fun a Ha => Ha)).
Qed.

(** In particular angelic total correctness IS carved out once the index may
    leave the AWP image: [wpSub] is not disjunctive. *)
Corollary angelic_carved_WPure {A} (p : Prop) (Q : A -> Prop) :
  carvedBy WP_le (fun R => getWH (rhoAWP R)) (angelic p Q).
Proof. exact (wp_sub_carved (fun R => getWH (rhoAWP R)) p Q). Qed.
