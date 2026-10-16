(** * Property-only strongest-postcondition arrows: ASP and DSLP.

    The canonical carriers contain predicate transformers and healthiness
    proofs, not stored relations. ASP/DSLP have constructive normal forms.
    Compatibility names and binary transformer stacks share these
    definitions.  The DSP and ASLP arrows, built from these two, are in
    [DSPASLPArr.v]. *)

From Coq Require Import FunctionalExtensionality PropExtensionality RelationClasses
  Morphisms Setoid Classical_Prop.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Arrow Require Export ArrowMonad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT
  ArrowMorphism RelArrowCoherence.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Export PredicateTransformerProperties.

(** ** Raw transformers and healthiness conditions
    Nonempty families define conjunctivity/disjunctivity; strictness and top
    preservation supply the respective empty cases. The raw carrier has no
    generic arrow structure: the four readings have different operations. *)

Definition SPArrT (A B : Type) : Type := (A -> Prop) -> B -> Prop.

Definition sp_monotone {A B} (f : SPArrT A B) : Prop :=
  forall (P Q : A -> Prop), (forall a, P a -> Q a) -> forall b, f P b -> f Q b.

Definition sp_strict := @StrictArr.

Definition sp_terminating := @TerminatingArr.

Definition sp_conjunctive := @ConjunctiveArr.

Definition sp_disjunctive := @DisjunctiveArr.

Arguments sp_strict {A B} _.
Arguments sp_terminating {A B} _.
Arguments sp_conjunctive {A B} _.
Arguments sp_disjunctive {A B} _.

(** ** Canonical ASP arrows: constructive singleton joins *)

Section ASPImplementation.

  (** *** Normal form: singleton joins *)

  Definition asp_join {A B} (f : SPArrT A B) : Prop :=
    forall P b, f P b <-> exists a, P a /\ f (fun x => x = a) b.

  Lemma asp_join_hom {A B} (f : SPArrT A B) :
    asp_join f -> sp_monotone f /\ sp_strict f /\ sp_disjunctive f.
  Proof.
    intro H. split; [|split].
    - intros P Q HPQ b Hf. apply H. apply H in Hf. destruct Hf as [a [Ha Hf]].
      exists a. split; [exact (HPQ a Ha) | exact Hf].
    - intros b Hf. destruct (proj1 (H _ b) Hf) as [a [[] _]].
    - intros I _ P b. rewrite (H _ b). split.
      + intros [a [[i Hi] Hf]]. exists i. apply (H _ b). exists a. split; assumption.
      + intros [i Hf]. apply (H _ b) in Hf. destruct Hf as [a [Hi Hf]].
        exists a. split; [exists i; exact Hi | exact Hf].
  Qed.

  Lemma asp_hom_join {A B} (f : SPArrT A B) :
    sp_monotone f /\ sp_strict f /\ sp_disjunctive f -> asp_join f.
  Proof.
    intros [Hm [Hs Hd]] P b. split.
    - intro Hf.
      pose (Q := fun (i : option { a : A | P a }) (x : A) =>
        match i with Some a => x = proj1_sig a | None => False end).
      assert (HQ : f (fun x => exists i, Q i x) b).
      { apply (Hm P); [|exact Hf]. intros x Hx. exists (Some (exist _ x Hx)). reflexivity. }
      apply (Hd _ (inhabits None) Q b) in HQ.
      destruct HQ as [[[a Ha] |] Hq];
        [exists a; split; [exact Ha | exact Hq] | destruct (Hs b Hq)].
    - intros [a [Ha Hf]]. apply (Hm (fun x => x = a)); [intros x ->; exact Ha | exact Hf].
  Qed.

  Theorem asp_join_iff {A B} (f : SPArrT A B) :
    asp_join f <-> sp_monotone f /\ sp_strict f /\ sp_disjunctive f.
  Proof. split; [apply asp_join_hom | apply asp_hom_join]. Qed.

  (** *** Carrier and accessors *)

  Definition ASPArr (A B : Type) : Type :=
    { f : SPArrT A B | sp_monotone f /\ sp_strict f /\ sp_disjunctive f }.

  Definition getASPArr {A B} (f : ASPArr A B) : (A -> Prop) -> B -> Prop := proj1_sig f.

  Coercion getASPArr : ASPArr >-> Funclass.

  Lemma getASPArr_join {A B} (f : ASPArr A B) P b :
    f P b <-> exists a, P a /\ f (fun x => x = a) b.
  Proof. exact (asp_hom_join _ (proj2_sig f) P b). Qed.

  Definition mkASPArr {A B} (f : SPArrT A B) (H : asp_join f) : ASPArr A B :=
    exist _ f (asp_join_hom f H).

  Lemma getASPArr_mono {A B} (f : ASPArr A B) (P Q : A -> Prop) b :
    (forall a, P a -> Q a) -> f P b -> f Q b.
  Proof.
    intro H. rewrite !(getASPArr_join f _ b).
    intros [a [Hp Hf]]. exists a. split; [apply H, Hp | exact Hf].
  Qed.

  Lemma getASPArr_ext {A B} (f : ASPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b -> f Q b.
  Proof. intro H. apply getASPArr_mono. intros; apply H; assumption. Qed.

  Lemma getASPArr_ext_iff {A B} (f : ASPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b <-> f Q b.
  Proof. split; now apply getASPArr_ext. Qed.

  (** *** Operations and arrow instances *)

  #[program] Definition ofRelASPArr {A B} (R : A -> B -> Prop) : ASPArr A B :=
    fun P b => exists a, P a /\ R a b.
  Next Obligation.
    apply asp_join_hom. intros P b. split.
    - intros [a [Hp HR]]. exists a. split; [exact Hp | exists a; auto].
    - intros [a [Hp [x [Hx HR]]]]. subst x. exists a. auto.
  Qed.

  #[program] Definition pureASP {A B} (h : A -> B) : ASPArr A B :=
    fun P b => exists a, P a /\ h a = b.
  Next Obligation.
    apply asp_join_hom. intros P b. split.
    - intros [a [Hp Hb]]. exists a. split; [exact Hp | exists a; auto].
    - intros [a [Hp [x [Hx Hb]]]]. subst. eauto.
  Qed.

  #[program] Definition compASP {A B C} (f : ASPArr A B) (g : ASPArr B C) : ASPArr A C :=
    fun P c => g (f P) c.
  Next Obligation.
    apply asp_join_hom. intros P c. rewrite getASPArr_join. split.
    - intros [b [Hf Hg]]. apply getASPArr_join in Hf. destruct Hf as [a [Hp Hf]].
      exists a. split; [exact Hp |]. apply getASPArr_join. exists b. exact (conj Hf Hg).
    - intros [a [Hp Hg]]. apply getASPArr_join in Hg. destruct Hg as [b [Hf Hg]].
      exists b. split; [|exact Hg]. apply getASPArr_join. exists a. exact (conj Hp Hf).
  Qed.

  #[program] Definition firstASP {A B C} (f : ASPArr A B) : ASPArr (A * C) (B * C) :=
    fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Next Obligation.
    apply asp_join_hom. intros P [b c]. cbn [fst snd]. rewrite getASPArr_join. split.
    - intros [a [Hp Hf]]. exists (a, c). split; [exact Hp |].
      apply (getASPArr_ext f (fun x => x = a)); [|exact Hf].
      intro x. split; [intros ->; reflexivity | intro H; injection H; auto].
    - intros [[a c'] [Hp Hf]]. apply getASPArr_join in Hf. destruct Hf as [x [Hx Hf]].
      injection Hx as Hx1 Hx2. subst. eauto.
  Qed.

  Definition leftASPT {A B C} (f : ASPArr A B) : SPArrT (A + C) (B + C) :=
    fun P y => match y with inl b => f (fun a => P (inl a)) b | inr c => P (inr c) end.

  #[program] Definition leftASP {A B C} (f : ASPArr A B) : ASPArr (A + C) (B + C) := leftASPT f.
  Next Obligation.
    apply asp_join_hom. intros P [b | c]; cbn.
    - rewrite getASPArr_join. split.
      + intros [a [Hp Hf]]. exists (inl a). split; [exact Hp |].
        apply (getASPArr_ext f (fun x => x = a)); [|exact Hf].
        intro x. split; [intros ->; reflexivity | intro H; injection H; auto].
      + intros [[a | c] [Hp Hf]].
        * apply getASPArr_join in Hf. destruct Hf as [x [Hx Hf]].
          injection Hx as Hx1. subst. eauto.
        * apply getASPArr_join in Hf. destruct Hf as [x [Hx _]]. discriminate Hx.
    - split; [intro Hp; exists (inr c); auto |].
      intros [[a | c'] [Hp Hc]]; [discriminate Hc | injection Hc as Hc; subst; exact Hp].
  Qed.

  #[program] Definition appASP {A B} : ASPArr (ASPArr A B * A) B :=
    fun P b => exists f a, P (f, a) /\ f (fun x => x = a) b.
  Next Obligation.
    apply asp_join_hom. intros P b. split.
    - intros [f [a [Hp Hf]]]. exists (f, a). split; [exact Hp |]. exists f, a. auto.
    - intros [[f a] [Hp [f' [a' [Heq Hf]]]]]. injection Heq as H1 H2. subst. eauto.
  Qed.

  #[global] Instance Arrow_ASPArr : Arrow ASPArr :=
    {| arr_pure := @pureASP; arr_comp := @compASP; arr_first := @firstASP |}.

  #[global] Instance ArrowChoice_ASPArr : ArrowChoice ASPArr := {| arr_left := @leftASP |}.

  #[global] Instance ArrowApply_ASPArr : ArrowApply ASPArr := {| arr_app := @appASP |}.

  (** *** Equality *)

  Definition ASPArr_eq {A B} (f g : ASPArr A B) : Prop := forall P b, f P b <-> g P b.

  #[global] Instance ASPArr_eq_Equivalence {A B} : Equivalence (@ASPArr_eq A B).
  Proof.
    constructor.
    - intros f P b. reflexivity.
    - intros f g H P b. symmetry. apply H.
    - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
  Qed.

  #[global] Instance ArrowEq_ASPArr : ArrowEq ASPArr := {| arrow_eq := @ASPArr_eq |}.

  (** Unfolding equations for the operations. *)
  Lemma getASPArr_pure {A B} (h : A -> B) :
    getASPArr (pureASP h) = fun P b => exists a, P a /\ h a = b.
  Proof. reflexivity. Qed.

  Lemma getASPArr_comp {A B C} (f : ASPArr A B) (g : ASPArr B C) :
    getASPArr (compASP f g) = fun P c => g (f P) c.
  Proof. reflexivity. Qed.

  Lemma getASPArr_first {A B C} (f : ASPArr A B) :
    getASPArr (@firstASP A B C f) = fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Proof. reflexivity. Qed.

  Lemma getASPArr_left {A B C} (f : ASPArr A B) : getASPArr (@leftASP A B C f) = leftASPT f.
  Proof. reflexivity. Qed.

  Lemma getASPArr_app {A B} :
    getASPArr (@appASP A B) = fun P b => exists f a, P (f, a) /\ f (fun x => x = a) b.
  Proof. reflexivity. Qed.

  (** *** Recovered relation
      The canonical probe orientation is [fun x => x = a]. *)

  Definition aspRel {A B} (f : ASPArr A B) (a : A) (b : B) : Prop := f (fun x => x = a) b.

  Lemma aspRel_pure {A B} (h : A -> B) a b : aspRel (arr_pure h) a b <-> h a = b.
  Proof. cbn. split; [intros [x [-> H]]; exact H | intro H; exists a; auto]. Qed.

  Lemma aspRel_comp {A B C} (f : ASPArr A B) (g : ASPArr B C) a c :
    aspRel (arr_comp f g) a c <-> exists b, aspRel f a b /\ aspRel g b c.
  Proof. exact (getASPArr_join g _ c). Qed.

  Lemma aspRel_first {A B C} (f : ASPArr A B) (p : A * C) (q : B * C) :
    aspRel (arr_first f) p q <-> aspRel f (fst p) (fst q) /\ snd p = snd q.
  Proof.
    destruct p as [a c], q as [b d]. unfold aspRel.
    change (f (fun x => (x, d) = (a, c)) b <-> f (fun x => x = a) b /\ c = d).
    rewrite getASPArr_join. split.
    - intros [x [H Hr]]. injection H as -> ->. auto.
    - intros [Hr ->]. exists a. auto.
  Qed.

  Lemma aspRel_left {A B C} (f : ASPArr A B) (x : A + C) (y : B + C) :
    aspRel (arr_left f) x y <->
    match x, y with inl a, inl b => aspRel f a b | inr c, inr d => c = d | _, _ => False end.
  Proof.
    unfold aspRel. destruct x as [a | c], y as [b | d]; cbn [arr_left ArrowChoice_ASPArr];
      rewrite getASPArr_left; unfold leftASPT; cbn.
    - apply getASPArr_ext_iff. intro z.
      split; [intro H; injection H; auto | intros ->; reflexivity].
    - split; [discriminate | contradiction].
    - rewrite getASPArr_join. split; [intros [z [H _]]; discriminate | contradiction].
    - split; [intro H; injection H; auto | intros ->; reflexivity].
  Qed.

  Lemma aspRel_app {A B} (p : ASPArr A B * A) b :
    aspRel arr_app p b <-> aspRel (fst p) (snd p) b.
  Proof.
    destruct p as [f a]. unfold aspRel. cbn [fst snd arr_app ArrowApply_ASPArr].
    rewrite getASPArr_app. split.
    - intros [g [x [H Hr]]]. injection H as <- <-. exact Hr.
    - intro H. exists f, a. auto.
  Qed.

  Lemma aspRel_eq {A B} (f g : ASPArr A B) :
    ASPArr_eq f g <-> (forall a b, aspRel f a b <-> aspRel g a b).
  Proof.
    split; [intros H a b; apply H |]. intros H P b.
    rewrite !getASPArr_join. split; intros [a [HP Hr]]; exists a; split;
      solve [exact HP | apply H, Hr].
  Qed.

  (** *** Semantic contracts and law packages *)

  #[global] Instance RelArrow_ASPArr : RelArrow ASPArr := {|
    rel_reading := @aspRel; rel_pure := @aspRel_pure; rel_comp := @aspRel_comp;
    rel_first := fun A B C f a c b d => aspRel_first f (a, c) (b, d)
  |}.

  #[global] Instance RelArrowChoice_ASPArr : RelArrowChoice ASPArr :=
    {| rel_left := @aspRel_left |}.

  #[global] Instance RelArrowApply_ASPArr : RelArrowApply ASPArr := {|
    rel_app := fun A B f a b => aspRel_app (f, a) b
  |}.

  #[global] Instance RelArrowEq_ASPArr : RelArrowEq ASPArr := {| rel_arrow_eq := @aspRel_eq |}.

  #[global] Instance ArrowLaws_ASPArr : ArrowLaws ASPArr :=
    @rel_arrow_laws ASPArr Arrow_ASPArr ArrowEq_ASPArr RelArrow_ASPArr RelArrowEq_ASPArr.

  #[global] Instance ArrowChoiceLaws_ASPArr : ArrowChoiceLaws ASPArr :=
    @rel_arrow_choice_laws ASPArr Arrow_ASPArr ArrowEq_ASPArr RelArrow_ASPArr
      RelArrowEq_ASPArr ArrowChoice_ASPArr RelArrowChoice_ASPArr.

  #[global] Instance ArrowApplyLaws_ASPArr : ArrowApplyLaws ASPArr :=
    @rel_arrow_apply_laws ASPArr Arrow_ASPArr ArrowEq_ASPArr RelArrow_ASPArr
      RelArrowEq_ASPArr ArrowApply_ASPArr RelArrowApply_ASPArr.

End ASPImplementation.

(** ** Canonical DSLP arrows: constructive accepted-predicate meets *)

Section DSLPImplementation.

  (** *** Normal form: accepted-predicate meets *)

  Definition dslpRelT {A B} (f : SPArrT A B) (a : A) (b : B) : Prop :=
    forall P, f P b -> P a.

  Definition dslp_meet {A B} (f : SPArrT A B) : Prop :=
    forall P b, f P b <-> forall a, dslpRelT f a b -> P a.

  Lemma dslp_meet_hom {A B} (f : SPArrT A B) :
    dslp_meet f -> sp_monotone f /\ sp_terminating f /\ sp_conjunctive f.
  Proof.
    intro H. split; [|split].
    - intros P Q HPQ b Hf. apply H. intros a Hr. exact (HPQ a (proj1 (H P b) Hf a Hr)).
    - intro b. apply (H _ b). intros a _. exact I.
    - intros I _ P b. rewrite (H _ b). split.
      + intros Hall i. apply (H _ b). intros a Hr. exact (Hall a Hr i).
      + intros Hall a Hr i. exact (proj1 (H _ b) (Hall i) a Hr).
  Qed.

  Lemma dslp_hom_meet {A B} (f : SPArrT A B) :
    sp_monotone f /\ sp_terminating f /\ sp_conjunctive f -> dslp_meet f.
  Proof.
    intros [Hm [Ht Hc]] P b. split.
    - intros Hf a Hr. exact (Hr P Hf).
    - intro H.
      apply (Hm (fun a => forall i : { Q : A -> Prop | f Q b }, proj1_sig i a)).
      + intros a Ha. apply H. intros Q HQ. exact (Ha (exist _ Q HQ)).
      + exact (proj2 (Hc _ (inhabits (exist (fun Q => f Q b) (fun _ => True) (Ht b)))
                       (fun i => proj1_sig i) b) (fun i => proj2_sig i)).
  Qed.

  Theorem dslp_meet_iff {A B} (f : SPArrT A B) :
    dslp_meet f <-> sp_monotone f /\ sp_terminating f /\ sp_conjunctive f.
  Proof. split; [apply dslp_meet_hom | apply dslp_hom_meet]. Qed.

  (** *** Carrier and accessors *)

  Definition DSLPArr (A B : Type) : Type :=
    { f : SPArrT A B | sp_monotone f /\ sp_terminating f /\ sp_conjunctive f }.

  Definition getDSLPArr {A B} (f : DSLPArr A B) : (A -> Prop) -> B -> Prop := proj1_sig f.

  Coercion getDSLPArr : DSLPArr >-> Funclass.

  Lemma getDSLPArr_meet {A B} (f : DSLPArr A B) P b :
    f P b <-> forall a, dslpRelT (getDSLPArr f) a b -> P a.
  Proof. exact (dslp_hom_meet _ (proj2_sig f) P b). Qed.

  Definition mkDSLPArr {A B} (f : SPArrT A B) (H : dslp_meet f) : DSLPArr A B :=
    exist _ f (dslp_meet_hom f H).

  Lemma getDSLPArr_ext_iff {A B} (f : DSLPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b <-> f Q b.
  Proof.
    intro H. rewrite !(getDSLPArr_meet f _ b).
    split; intros HP a Hr; solve [apply H, HP, Hr | apply H; apply HP, Hr].
  Qed.

  Lemma getDSLPArr_ext {A B} (f : DSLPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b -> f Q b.
  Proof. intro H. apply (getDSLPArr_ext_iff f P Q b H). Qed.

  Lemma getDSLPArr_mono {A B} (f : DSLPArr A B) (P Q : A -> Prop) b :
    (forall a, P a -> Q a) -> f P b -> f Q b.
  Proof. intro H. exact (proj1 (proj2_sig f) P Q H b). Qed.

  (** *** Operations and arrow instances *)

  #[program] Definition ofRelDSLPArr {A B} (R : A -> B -> Prop) : DSLPArr A B :=
    fun P b => forall a, R a b -> P a.
  Next Obligation.
    apply dslp_meet_hom. intros P b. split.
    - intros H a Hr. apply H. apply (Hr (fun x => R x b)). intros a' Hr'. exact Hr'.
    - intros H a Hr. apply H. intros Q HQ. exact (HQ a Hr).
  Qed.

  #[program] Definition pureDSLP {A B} (h : A -> B) : DSLPArr A B :=
    fun P b => forall a, h a = b -> P a.
  Next Obligation.
    apply dslp_meet_hom. intros P b. split.
    - intros H a Hr. apply H. apply (Hr (fun x => h x = b)). intros a' Hr'. exact Hr'.
    - intros H a Hr. apply H. intros Q HQ. exact (HQ a Hr).
  Qed.

  #[program] Definition compDSLP {A B C} (f : DSLPArr A B) (g : DSLPArr B C) : DSLPArr A C :=
    fun P c => g (f P) c.
  Next Obligation.
    apply dslp_meet_hom. intros P c. split.
    - intros H a Hr. exact (Hr P H).
    - intros H.
      apply (getDSLPArr_meet g (f P) c). intros b Hg.
      apply (getDSLPArr_meet f P b). intros a Hf.
      apply H. intros Q HQ.
      apply (proj1 (getDSLPArr_meet f Q b)); [|exact Hf].
      apply (proj1 (getDSLPArr_meet g (f Q) c)); [exact HQ | exact Hg].
  Qed.

  #[program] Definition firstDSLP {A B C} (f : DSLPArr A B) : DSLPArr (A * C) (B * C) :=
    fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Next Obligation.
    apply dslp_meet_hom. intros P [b c]. cbn [fst snd]. split.
    - intros H [a c'] Hr. exact (Hr P H).
    - intros H.
      apply (getDSLPArr_meet f (fun a => P (a, c)) b). intros a Hf.
      apply H. intros Q HQ. cbn [fst snd] in HQ.
      apply (proj1 (getDSLPArr_meet f (fun a0 => Q (a0, c)) b)); [exact HQ | exact Hf].
  Qed.

  Definition leftDSLPT {A B C} (f : DSLPArr A B) : SPArrT (A + C) (B + C) :=
    fun P y => match y with inl b => f (fun a => P (inl a)) b | inr c => P (inr c) end.

  #[program] Definition leftDSLP {A B C} (f : DSLPArr A B) :
    DSLPArr (A + C) (B + C) := leftDSLPT f.
  Next Obligation.
    apply dslp_meet_hom. intros P [b | c]; cbn.
    - split.
      + intros H [a | c'] Hr; exact (Hr P H).
      + intros H.
        apply (getDSLPArr_meet f (fun a => P (inl a)) b). intros a Hf.
        apply (H (inl a)). intros Q HQ. cbn in HQ.
        apply (proj1 (getDSLPArr_meet f (fun a0 => Q (inl a0)) b)); [exact HQ | exact Hf].
    - split.
      + intros H [a | c'] Hr; exact (Hr P H).
      + intro H. apply (H (inr c)). intros Q HQ. cbn in HQ. exact HQ.
  Qed.

  #[program] Definition appDSLP {A B} : DSLPArr (DSLPArr A B * A) B :=
    fun P b => forall f a, dslpRelT (getDSLPArr f) a b -> P (f, a).
  Next Obligation.
    apply dslp_meet_hom. intros P b. split.
    - intros H [f a] Hr. exact (Hr P H).
    - intros H f a Hr. apply H. intros Q HQ. exact (HQ f a Hr).
  Qed.

  #[global] Instance Arrow_DSLPArr : Arrow DSLPArr :=
    {| arr_pure := @pureDSLP; arr_comp := @compDSLP; arr_first := @firstDSLP |}.

  #[global] Instance ArrowChoice_DSLPArr : ArrowChoice DSLPArr := {| arr_left := @leftDSLP |}.

  #[global] Instance ArrowApply_DSLPArr : ArrowApply DSLPArr := {| arr_app := @appDSLP |}.

  (** *** Equality *)

  Definition DSLPArr_eq {A B} (f g : DSLPArr A B) : Prop := forall P b, f P b <-> g P b.

  #[global] Instance DSLPArr_eq_Equivalence {A B} : Equivalence (@DSLPArr_eq A B).
  Proof.
    constructor.
    - intros f P b. reflexivity.
    - intros f g H P b. symmetry. apply H.
    - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
  Qed.

  #[global] Instance ArrowEq_DSLPArr : ArrowEq DSLPArr := {| arrow_eq := @DSLPArr_eq |}.

  (** Unfolding equations for the operations. *)
  Lemma getDSLPArr_pure {A B} (h : A -> B) :
    getDSLPArr (pureDSLP h) = fun P b => forall a, h a = b -> P a.
  Proof. reflexivity. Qed.

  Lemma getDSLPArr_comp {A B C} (f : DSLPArr A B) (g : DSLPArr B C) :
    getDSLPArr (compDSLP f g) = fun P c => g (f P) c.
  Proof. reflexivity. Qed.

  Lemma getDSLPArr_first {A B C} (f : DSLPArr A B) :
    getDSLPArr (@firstDSLP A B C f) = fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Proof. reflexivity. Qed.

  Lemma getDSLPArr_left {A B C} (f : DSLPArr A B) : getDSLPArr (@leftDSLP A B C f) = leftDSLPT f.
  Proof. reflexivity. Qed.

  Lemma getDSLPArr_app {A B} :
    getDSLPArr (@appDSLP A B) = fun P b => forall f a, dslpRelT (getDSLPArr f) a b -> P (f, a).
  Proof. reflexivity. Qed.

End DSLPImplementation.

(** ** DSLP relation recovery and operation contracts *)

Section DSLPRelation.

  (** *** Recovered relation *)

  Definition dslpRel {A B} (f : DSLPArr A B) (a : A) (b : B) : Prop :=
    dslpRelT (getDSLPArr f) a b.

  Lemma get_dslpRel {A B} (f : DSLPArr A B) P b :
    f P b <-> forall a, dslpRel f a b -> P a.
  Proof. exact (getDSLPArr_meet f P b). Qed.

  (** Only this optional complement probe needs excluded middle. *)
  Lemma dslpRel_probe {A B} (f : DSLPArr A B) a b :
    dslpRel f a b <-> ~ f (fun x => x <> a) b.
  Proof.
    split.
    - intros Hr Hf. exact (Hr (fun x => x <> a) Hf eq_refl).
    - intros Hf P HP.
      destruct (classic (dslpRel f a b)) as [Hin | Hout].
      + exact (proj1 (get_dslpRel f P b) HP a Hin).
      + exfalso. apply Hf.
        apply (proj2 (get_dslpRel f (fun x => x <> a) b)).
        intros a' Hr' Heq. subst a'. exact (Hout Hr').
  Qed.

  Lemma dslpRel_ofRel {A B} (R : A -> B -> Prop) a b :
    dslpRel (ofRelDSLPArr R) a b <-> R a b.
  Proof.
    unfold dslpRel, dslpRelT, ofRelDSLPArr. cbn. split.
    - intro H. exact (H (fun x => R x b) (fun a' Hr => Hr)).
    - intros HR Q HQ. exact (HQ a HR).
  Qed.

  Lemma ofRel_dslpRel {A B} (f : DSLPArr A B) P b :
    ofRelDSLPArr (dslpRel f) P b <-> f P b.
  Proof. unfold dslpRel, dslpRelT, ofRelDSLPArr. cbn. split; apply getDSLPArr_meet. Qed.

  Lemma dslpRel_pure {A B} (h : A -> B) a b : dslpRel (arr_pure h) a b <-> h a = b.
  Proof.
    cbn. unfold dslpRel, dslpRelT. cbn. split.
    - intro H. exact (H (fun x => h x = b) (fun a' Hr => Hr)).
    - intros H Q HQ. exact (HQ a H).
  Qed.

  Lemma dslpRel_comp {A B C} (f : DSLPArr A B) (g : DSLPArr B C) a c :
    dslpRel (arr_comp f g) a c <-> exists b, dslpRel f a b /\ dslpRel g b c.
  Proof.
    split.
    - intro H.
      exact (H (fun x => exists b, dslpRel f x b /\ dslpRel g b c)
               (proj2 (get_dslpRel g _ c)
                  (fun b Hg => proj2 (get_dslpRel f _ b)
                                 (fun a' Hf => ex_intro _ b (conj Hf Hg))))).
    - intros [b [Hf Hg]] Q HQ. cbn in HQ.
      apply (proj1 (get_dslpRel f Q b)); [|exact Hf].
      apply (proj1 (get_dslpRel g (f Q) c)); [exact HQ | exact Hg].
  Qed.

  Lemma dslpRel_first {A B C} (f : DSLPArr A B) (p : A * C) (q : B * C) :
    dslpRel (arr_first f) p q <-> dslpRel f (fst p) (fst q) /\ snd p = snd q.
  Proof.
    destruct p as [a c], q as [b c']. cbn [fst snd]. split.
    - intro H. split.
      + intros Q HQ. exact (H (fun p => Q (fst p)) HQ).
      + exact (H (fun p => snd p = c')
                 (proj2 (get_dslpRel f (fun x => c' = c') b) (fun a' _ => eq_refl))).
    - intros [Hf Hc]. cbn in Hc. subst c'. intros Q HQ.
      apply (proj1 (get_dslpRel f (fun a0 => Q (a0, c)) b)); [exact HQ | exact Hf].
  Qed.

  Lemma dslpRel_left {A B C} (f : DSLPArr A B) (x : A + C) (y : B + C) :
    dslpRel (arr_left f) x y <->
    match x, y with inl a, inl b => dslpRel f a b | inr c, inr c' => c = c' | _, _ => False end.
  Proof.
    unfold dslpRel, dslpRelT. cbn [getDSLPArr arr_left ArrowChoice_DSLPArr].
    rewrite getDSLPArr_left. unfold leftDSLPT.
    destruct y as [b | c'].
    - destruct x as [a | c]; split.
      + intros H Q HQ.
        exact (H (fun z => match z with inl a0 => Q a0 | inr _ => True end) HQ).
      + intros Hr P HP. exact (proj1 (get_dslpRel f _ b) HP a Hr).
      + intro H.
        exact (H (fun z => match z with inl _ => True | inr _ => False end)
                 (proj2 (get_dslpRel f (fun _ => True) b) (fun _ _ => I))).
      + intros [].
    - destruct x as [a | c]; split.
      + intro H.
        exact (H (fun z => match z with inl _ => False | inr _ => True end) I).
      + intros [].
      + intro H. injection (H (fun z => z = inr c') eq_refl) as ->. reflexivity.
      + intros -> P HP. exact HP.
  Qed.

  Lemma dslpRel_app {A B} (p : DSLPArr A B * A) (b : B) :
    dslpRel arr_app p b <-> dslpRel (fst p) (snd p) b.
  Proof.
    destruct p as [f a]. cbn [fst snd]. split.
    - intro H. exact (H (fun q => dslpRel (fst q) (snd q) b) (fun f' a' Hr => Hr)).
    - intros Hr P HP. exact (HP f a Hr).
  Qed.

  Lemma dslpRel_eq {A B} (f g : DSLPArr A B) :
    DSLPArr_eq f g <-> (forall a b, dslpRel f a b <-> dslpRel g a b).
  Proof.
    split.
    - intros H a b. unfold dslpRel, dslpRelT. split; intros Hr P HP.
      + apply Hr, H, HP.
      + apply Hr, H, HP.
    - intros H P b. rewrite !get_dslpRel.
      split; intros HP a Hr; apply HP, H, Hr.
  Qed.

  Lemma dslpRel_incl {A B} (f g : DSLPArr A B) :
    (forall P b, f P b -> g P b) <-> (forall a b, dslpRel g a b -> dslpRel f a b).
  Proof.
    split.
    - intros H a b Hg P HP. exact (Hg P (H P b HP)).
    - intros H P b Hf. apply get_dslpRel. intros a Hg.
      exact (proj1 (get_dslpRel f P b) Hf a (H a b Hg)).
  Qed.

  (** *** Semantic contracts and law packages *)

  #[global] Instance RelArrow_DSLPArr : RelArrow DSLPArr := {|
    rel_reading := @dslpRel; rel_pure := @dslpRel_pure; rel_comp := @dslpRel_comp;
    rel_first := fun A B C f a c b d => dslpRel_first f (a, c) (b, d)
  |}.

  #[global] Instance RelArrowChoice_DSLPArr : RelArrowChoice DSLPArr :=
    {| rel_left := @dslpRel_left |}.

  #[global] Instance RelArrowApply_DSLPArr : RelArrowApply DSLPArr := {|
    rel_app := fun A B f a b => dslpRel_app (f, a) b
  |}.

  #[global] Instance RelArrowEq_DSLPArr : RelArrowEq DSLPArr := {| rel_arrow_eq := @dslpRel_eq |}.

  #[global] Instance ArrowLaws_DSLPArr : ArrowLaws DSLPArr :=
    @rel_arrow_laws DSLPArr Arrow_DSLPArr ArrowEq_DSLPArr RelArrow_DSLPArr RelArrowEq_DSLPArr.

  #[global] Instance ArrowChoiceLaws_DSLPArr : ArrowChoiceLaws DSLPArr :=
    @rel_arrow_choice_laws DSLPArr Arrow_DSLPArr ArrowEq_DSLPArr RelArrow_DSLPArr
      RelArrowEq_DSLPArr ArrowChoice_DSLPArr RelArrowChoice_DSLPArr.

  #[global] Instance ArrowApplyLaws_DSLPArr : ArrowApplyLaws DSLPArr :=
    @rel_arrow_apply_laws DSLPArr Arrow_DSLPArr ArrowEq_DSLPArr RelArrow_DSLPArr
      RelArrowEq_DSLPArr ArrowApply_DSLPArr RelArrowApply_DSLPArr.

End DSLPRelation.

(** ** Public ASP/DSLP compatibility interface
    Carrier and dictionary aliases are plain definitions, not competing global
    registrations. The public ASP probe retains its opposite equality direction. *)

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
  subst. f_equal. apply PropExtensionality.proof_irrelevance.
Qed.

Lemma PureDSLPostArr_eq {A B} (f g : PureDSLPostArr A B) :
  (forall P b, getDSLP f P b <-> getDSLP g P b) -> f = g.
Proof.
  destruct f as [f Hf], g as [g Hg]. cbn. intro H.
  assert (HE : f = g).
  { extensionality P. extensionality b. apply propositional_extensionality, H. }
  subst. f_equal. apply PropExtensionality.proof_irrelevance.
Qed.

(** ** Function-lifting aliases and canonical operation dictionaries *)

Local Obligation Tactic := idtac.

Definition arrASP := @pureASP.

Definition arrDSLP := @pureDSLP.

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
    split; intros [a [HP Hr]]; exists a; split;
      [exact HP | apply Hrel, Hr | exact HP | apply Hrel, Hr].
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
  intros Q [b | d]; rewrite leftDSLP_spec; cbn.
  - rewrite (DSLP_normal_form f). split.
    + intros H [a | c] Hr; [exact (H a Hr) | contradiction].
    + intros H a Hr. exact (H (inl a) Hr).
  - split.
    + intros HQ [a | c] Hr; [contradiction | subst c; exact HQ].
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
  unfold ASP_rel. destruct x as [a | c], y as [b | d];
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

(** ** Compatibility semantic dictionaries and derived law packages *)

Definition RelArrow_PureASPostArr : RelArrow PureASPostArr := {|
  rel_reading := @ASP_rel;
  rel_pure := @ASP_rel_pure;
  rel_comp := @ASP_rel_comp;
  rel_first := @ASP_rel_first;
|}.

Definition RelArrowChoice_PureASPostArr :
  @RelArrowChoice PureASPostArr Arrow_PureASPostArr
    ArrowChoice_PureASPostArr RelArrow_PureASPostArr :=
  @Build_RelArrowChoice PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr
    RelArrow_PureASPostArr (@ASP_rel_left).

Definition RelArrowApply_PureASPostArr :
  @RelArrowApply PureASPostArr Arrow_PureASPostArr
    ArrowApply_PureASPostArr RelArrow_PureASPostArr :=
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
  @RelArrowChoice PureDSLPostArr Arrow_PureDSLPostArr
    ArrowChoice_PureDSLPostArr RelArrow_PureDSLPostArr :=
  @Build_RelArrowChoice PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    RelArrow_PureDSLPostArr (@DSLP_rel_left).

Definition RelArrowApply_PureDSLPostArr :
  @RelArrowApply PureDSLPostArr Arrow_PureDSLPostArr
    ArrowApply_PureDSLPostArr RelArrow_PureDSLPostArr :=
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
  exact (rel_arrow_laws_leibniz (fun A B f g H => @PureASPostArr_eq A B f g H)
    ArrowLaws_PureASPostArr).
Qed.

Lemma ArrowChoiceLaws_PureASPostArr_leibniz :
  @ArrowChoiceLaws PureASPostArr Arrow_PureASPostArr ArrowChoice_PureASPostArr
    (ArrowEq_leibniz PureASPostArr).
Proof.
  exact (rel_arrow_choice_laws_leibniz (fun A B f g H => @PureASPostArr_eq A B f g H)
    ArrowChoiceLaws_PureASPostArr).
Qed.

Lemma ArrowLaws_PureDSLPostArr_leibniz :
  @ArrowLaws PureDSLPostArr Arrow_PureDSLPostArr (ArrowEq_leibniz PureDSLPostArr).
Proof.
  exact (rel_arrow_laws_leibniz (fun A B f g H => @PureDSLPostArr_eq A B f g H)
    ArrowLaws_PureDSLPostArr).
Qed.

Lemma ArrowChoiceLaws_PureDSLPostArr_leibniz :
  @ArrowChoiceLaws PureDSLPostArr Arrow_PureDSLPostArr ArrowChoice_PureDSLPostArr
    (ArrowEq_leibniz PureDSLPostArr).
Proof.
  exact (rel_arrow_choice_laws_leibniz (fun A B f g H => @PureDSLPostArr_eq A B f g H)
    ArrowChoiceLaws_PureDSLPostArr).
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

(** ASP option-layer dictionaries. *)
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

(** DSLP option-layer dictionaries. *)
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

(** State-over-option dictionaries. *)
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
  - intros [[r0 | []] [H Heq]]; cbn in Heq; subst.
    + right. rewrite HR in H |- *. destruct H as [b [[ob [Hb Heq]] Hg]].
      destruct ob as [b0 |]; cbn in Heq; [|discriminate].
      injection Heq as Heq. subst. exists b. auto.
    + left. split; [|reflexivity].
      destruct H as [[b |] [H Heq]]; [discriminate | exact H].
  - intros [[H ->] | H].
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
  cbn. unfold leftDSLPT. destruct (IsDSLP_rewrite g) as [R HR].
  unfold getDSLP, getDSLPArr in *. split.
  - intro H. split.
    + intro Heq. subst. exact (H (inr tt) eq_refl None eq_refl).
    + rewrite HR. intros b Hb.
      assert (Hg := H (inl r) eq_refl). cbn in Hg. rewrite HR in Hg.
      exact (Hg b Hb (Some b) eq_refl).
  - intros [Hnone Hg] [r0 | []] Heq; cbn in Heq; subst.
    + rewrite HR in Hg |- *. intros b Hb [b0 |] Heq; cbn in Heq; [|discriminate].
      injection Heq as Heq. subst. exact (Hg b Hb).
    + intros [b |] Heq; [discriminate | apply Hnone; reflexivity].
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
  - intros [[[p [_ Heq]] _] | [f H]]; [discriminate |].
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

(** ** Canonical ASP recovery and fixed-input bind wrappers *)

Section ASPRelationWrappers.

  Lemma get_aspRel {A B} (f : ASPArr A B) P b :
    f P b <-> exists a, P a /\ aspRel f a b.
  Proof. exact (getASPArr_join f P b). Qed.

  Lemma aspRel_ofRel {A B} (R : A -> B -> Prop) a b :
    aspRel (ofRelASPArr R) a b <-> R a b.
  Proof.
    unfold aspRel, ofRelASPArr. cbn. split.
    - intros [x [Hx HR]]. subst x. exact HR.
    - intro HR. exists a. auto.
  Qed.

  Lemma ofRel_aspRel {A B} (f : ASPArr A B) P b :
    ofRelASPArr (aspRel f) P b <-> f P b.
  Proof. unfold aspRel, ofRelASPArr. cbn. split; apply getASPArr_join. Qed.

  Lemma aspRel_incl {A B} (f g : ASPArr A B) :
    (forall P b, f P b -> g P b) <-> (forall a b, aspRel f a b -> aspRel g a b).
  Proof.
    split.
    - intros H a b. apply H.
    - intros H P b Hf. apply get_aspRel in Hf. destruct Hf as [a [Hp Hr]].
      apply get_aspRel. exists a. split; [exact Hp | apply H, Hr].
  Qed.

  Lemma aspRel_bind {I A B} (m : ASPArr I A) (k : A -> ASPArr I B) i b :
    aspRel (@bind_arrow ASPArr Arrow_ASPArr ArrowApply_ASPArr I A B m k) i b <->
    exists a, aspRel m i a /\ aspRel (k a) i b.
  Proof.
    exact (@rel_bind ASPArr Arrow_ASPArr ArrowApply_ASPArr
      RelArrow_ASPArr RelArrowApply_ASPArr I A B m k i b).
  Qed.

  Lemma aspRelS_ret (S : Type) {I A} (x : A) i s r :
    aspRel (@ret_arrow (stateArrT S ASPArr) _ I A x) (i, s) r <-> r = (x, s).
  Proof.
    unfold ret_arrow. cbn [arr_pure Arrow_stateArrT]. rewrite aspRel_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma aspRelS_bind (S : Type) {I A B} (m : stateArrT S ASPArr I A)
    (k : A -> stateArrT S ASPArr I B) i s r :
    aspRel (@bind_arrow (stateArrT S ASPArr) _ _ I A B m k) (i, s) r <->
    exists a s', aspRel m (i, s) (a, s') /\ aspRel (k a) (i, s') r.
  Proof.
    exact (@relS_bind ASPArr Arrow_ASPArr ArrowApply_ASPArr
      RelArrow_ASPArr RelArrowApply_ASPArr S I A B m k i s r).
  Qed.

  (** Option and state-over-option wrappers. *)
  Lemma aspRelO_comp {X Y Z} (f : optionArrT ASPArr X Y) (g : optionArrT ASPArr Y Z) x o :
    aspRel (@arr_comp (optionArrT ASPArr) _ X Y Z f g) x o <->
    exists o1, aspRel f x o1 /\ match o1 with Some y => aspRel g y o | None => o = None end.
  Proof.
    exact (@relO_comp ASPArr Arrow_ASPArr RelArrow_ASPArr
      ArrowChoice_ASPArr RelArrowChoice_ASPArr X Y Z f g x o).
  Qed.

  Lemma aspRelO_pure {X Y} (h : X -> Y) x o :
    aspRel (@arr_pure (optionArrT ASPArr) _ X Y h) x o <-> o = Some (h x).
  Proof. exact (@relO_pure ASPArr Arrow_ASPArr RelArrow_ASPArr ArrowChoice_ASPArr X Y h x o). Qed.

  Lemma aspRelO_first {X Y C} (f : optionArrT ASPArr X Y) x (c : C) o :
    aspRel (@arr_first (optionArrT ASPArr) _ X Y C f) (x, c) o <->
    exists o1, aspRel f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    exact (@relO_first ASPArr Arrow_ASPArr RelArrow_ASPArr
      ArrowChoice_ASPArr X Y C f x c o).
  Qed.

  Section ASPStateOptionWrappers.

    Variable S : Type.
    Local Notation T := (stateArrT S (optionArrT ASPArr)).

    Lemma aspRelE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
      aspRel (@arr_comp T _ X Y Z f g) p o <->
      exists o1, aspRel f p o1 /\ match o1 with Some q => aspRel g q o | None => o = None end.
    Proof.
      exact (@relE_comp ASPArr Arrow_ASPArr RelArrow_ASPArr
        ArrowChoice_ASPArr RelArrowChoice_ASPArr S X Y Z f g p o).
    Qed.

    Lemma aspRelE_pure {X Y} (h : X -> Y) x s o :
      aspRel (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
    Proof.
      exact (@relE_pure ASPArr Arrow_ASPArr RelArrow_ASPArr
        ArrowChoice_ASPArr S X Y h x s o).
    Qed.

    Lemma aspRelE_first {X Y C} (f : T X Y) x (c : C) s o :
      aspRel (@arr_first T _ X Y C f) ((x, c), s) o <->
      exists o1, aspRel f (x, s) o1 /\
        o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
    Proof.
      exact (@relE_first ASPArr Arrow_ASPArr RelArrow_ASPArr
        ArrowChoice_ASPArr RelArrowChoice_ASPArr S X Y C f x c s o).
    Qed.

    Lemma aspRelE_app {X Y} (f : T X Y) x s o :
      aspRel (@arr_app T _ _ X Y) ((f, x), s) o <-> aspRel f (x, s) o.
    Proof.
      exact (@relE_app ASPArr Arrow_ASPArr ArrowApply_ASPArr RelArrow_ASPArr RelArrowApply_ASPArr
        ArrowChoice_ASPArr RelArrowChoice_ASPArr S X Y f x s o).
    Qed.

    Lemma aspRelE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
      aspRel (@bind_arrow T _ _ I A B m k) (i, s) o <->
      exists o1, aspRel m (i, s) o1 /\
        match o1 with Some (a, s') => aspRel (k a) (i, s') o | None => o = None end.
    Proof.
      exact (@relE_bind ASPArr Arrow_ASPArr ArrowApply_ASPArr RelArrow_ASPArr RelArrowApply_ASPArr
        ArrowChoice_ASPArr RelArrowChoice_ASPArr S I A B m k i s o).
    Qed.

    Lemma aspRelE_ret {I A} (a : A) i s o :
      aspRel (@ret_arrow T _ I A a) (i, s) o <-> o = Some (a, s).
    Proof.
      exact (@relE_pure ASPArr Arrow_ASPArr RelArrow_ASPArr
        ArrowChoice_ASPArr S I A (fun _ => a) i s o).
    Qed.

  End ASPStateOptionWrappers.

End ASPRelationWrappers.

(** ** Canonical DSLP fixed-input bind wrappers *)

Section DSLPRelationWrappers.

  Lemma dslpRel_bind {I A B} (m : DSLPArr I A) (k : A -> DSLPArr I B) i b :
    dslpRel (@bind_arrow DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr I A B m k) i b <->
    exists a, dslpRel m i a /\ dslpRel (k a) i b.
  Proof.
    exact (@rel_bind DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr
      RelArrow_DSLPArr RelArrowApply_DSLPArr I A B m k i b).
  Qed.

  Lemma dslpRelS_ret (S : Type) {I A} (x : A) i s r :
    dslpRel (@ret_arrow (stateArrT S DSLPArr) _ I A x) (i, s) r <-> r = (x, s).
  Proof.
    unfold ret_arrow. cbn [arr_pure Arrow_stateArrT]. rewrite dslpRel_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma dslpRelS_bind (S : Type) {I A B} (m : stateArrT S DSLPArr I A)
    (k : A -> stateArrT S DSLPArr I B) i s r :
    dslpRel (@bind_arrow (stateArrT S DSLPArr) _ _ I A B m k) (i, s) r <->
    exists a s', dslpRel m (i, s) (a, s') /\ dslpRel (k a) (i, s') r.
  Proof.
    exact (@relS_bind DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr
      RelArrow_DSLPArr RelArrowApply_DSLPArr S I A B m k i s r).
  Qed.

  (** Option and state-over-option wrappers. *)
  Lemma dslpRelO_comp {X Y Z} (f : optionArrT DSLPArr X Y) (g : optionArrT DSLPArr Y Z) x o :
    dslpRel (@arr_comp (optionArrT DSLPArr) _ X Y Z f g) x o <->
    exists o1, dslpRel f x o1 /\ match o1 with Some y => dslpRel g y o | None => o = None end.
  Proof.
    exact (@relO_comp DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
      ArrowChoice_DSLPArr RelArrowChoice_DSLPArr X Y Z f g x o).
  Qed.

  Lemma dslpRelO_pure {X Y} (h : X -> Y) x o :
    dslpRel (@arr_pure (optionArrT DSLPArr) _ X Y h) x o <-> o = Some (h x).
  Proof.
    exact (@relO_pure DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
      ArrowChoice_DSLPArr X Y h x o).
  Qed.

  Lemma dslpRelO_first {X Y C} (f : optionArrT DSLPArr X Y) x (c : C) o :
    dslpRel (@arr_first (optionArrT DSLPArr) _ X Y C f) (x, c) o <->
    exists o1, dslpRel f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    exact (@relO_first DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
      ArrowChoice_DSLPArr X Y C f x c o).
  Qed.

  Section DSLPStateOptionWrappers.

    Variable S : Type.
    Local Notation T := (stateArrT S (optionArrT DSLPArr)).

    Lemma dslpRelE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
      dslpRel (@arr_comp T _ X Y Z f g) p o <->
      exists o1, dslpRel f p o1 /\ match o1 with Some q => dslpRel g q o | None => o = None end.
    Proof.
      exact (@relE_comp DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
        ArrowChoice_DSLPArr RelArrowChoice_DSLPArr S X Y Z f g p o).
    Qed.

    Lemma dslpRelE_pure {X Y} (h : X -> Y) x s o :
      dslpRel (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
    Proof.
      exact (@relE_pure DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
        ArrowChoice_DSLPArr S X Y h x s o).
    Qed.

    Lemma dslpRelE_first {X Y C} (f : T X Y) x (c : C) s o :
      dslpRel (@arr_first T _ X Y C f) ((x, c), s) o <->
      exists o1, dslpRel f (x, s) o1 /\
        o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
    Proof.
      exact (@relE_first DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
        ArrowChoice_DSLPArr RelArrowChoice_DSLPArr S X Y C f x c s o).
    Qed.

    Lemma dslpRelE_app {X Y} (f : T X Y) x s o :
      dslpRel (@arr_app T _ _ X Y) ((f, x), s) o <-> dslpRel f (x, s) o.
    Proof.
      exact (@relE_app DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr
        RelArrow_DSLPArr RelArrowApply_DSLPArr
        ArrowChoice_DSLPArr RelArrowChoice_DSLPArr S X Y f x s o).
    Qed.

    Lemma dslpRelE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
      dslpRel (@bind_arrow T _ _ I A B m k) (i, s) o <->
      exists o1, dslpRel m (i, s) o1 /\
        match o1 with Some (a, s') => dslpRel (k a) (i, s') o | None => o = None end.
    Proof.
      exact (@relE_bind DSLPArr Arrow_DSLPArr ArrowApply_DSLPArr
        RelArrow_DSLPArr RelArrowApply_DSLPArr
        ArrowChoice_DSLPArr RelArrowChoice_DSLPArr S I A B m k i s o).
    Qed.

    Lemma dslpRelE_ret {I A} (a : A) i s o :
      dslpRel (@ret_arrow T _ I A a) (i, s) o <-> o = Some (a, s).
    Proof.
      exact (@relE_pure DSLPArr Arrow_DSLPArr RelArrow_DSLPArr
        ArrowChoice_DSLPArr S I A (fun _ => a) i s o).
    Qed.

  End DSLPStateOptionWrappers.

End DSLPRelationWrappers.

(** ** Angelic-to-demonic binary conversion *)

Definition asp_to_dslp {A B} (w : PureASPostArr A B) : PureDSLPostArr A B :=
  relDSLP (ASP_rel w).

Lemma asp_to_dslp_spec {A B} (w : PureASPostArr A B) P b :
  getDSLP (asp_to_dslp w) P b <-> forall a, ASP_rel w a b -> P a.
Proof. exact (getDSLP_relDSLP (ASP_rel w) P b). Qed.

Lemma DSLP_rel_asp_to_dslp {A B} (w : PureASPostArr A B) a b :
  DSLP_rel (asp_to_dslp w) a b <-> ASP_rel w a b.
Proof. exact (DSLP_rel_relDSLP (ASP_rel w) a b). Qed.

