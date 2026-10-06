(** * Canonical angelic strongest-postcondition arrows.
    The carrier and operations are transformer-based. Singleton joins recover
    a relation constructively; the generic relational contracts supply laws. *)
From Coq Require Import Morphisms RelationClasses Setoid.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad RelArrowCoherence.
From Incorrectness.Taxonomy.Arrows Require Import SPArr.

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
    pose (Q := fun (i : option {a : A | P a}) (x : A) =>
      match i with Some a => x = proj1_sig a | None => False end).
    assert (HQ : f (fun x => exists i, Q i x) b).
    { apply (Hm P); [|exact Hf]. intros x Hx. exists (Some (exist _ x Hx)). reflexivity. }
    apply (Hd _ (inhabits None) Q b) in HQ.
    destruct HQ as [[[a Ha]|] Hq];
      [exists a; split; [exact Ha | exact Hq] | destruct (Hs b Hq)].
  - intros [a [Ha Hf]]. apply (Hm (fun x => x = a)); [intros x ->; exact Ha | exact Hf].
Qed.

Theorem asp_join_iff {A B} (f : SPArrT A B) :
  asp_join f <-> sp_monotone f /\ sp_strict f /\ sp_disjunctive f.
Proof. split; [apply asp_join_hom | apply asp_hom_join]. Qed.

Definition ASPArr (A B : Type) : Type :=
  {f : SPArrT A B | sp_monotone f /\ sp_strict f /\ sp_disjunctive f}.
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
  apply asp_join_hom. intros P [b|c]; cbn.
  - rewrite getASPArr_join. split.
    + intros [a [Hp Hf]]. exists (inl a). split; [exact Hp |].
      apply (getASPArr_ext f (fun x => x = a)); [|exact Hf].
      intro x. split; [intros ->; reflexivity | intro H; injection H; auto].
    + intros [[a|c] [Hp Hf]].
      * apply getASPArr_join in Hf. destruct Hf as [x [Hx Hf]]. injection Hx as Hx1. subst. eauto.
      * apply getASPArr_join in Hf. destruct Hf as [x [Hx _]]. discriminate Hx.
  - split; [intro Hp; exists (inr c); auto |].
    intros [[a|c'] [Hp Hc]]; [discriminate Hc | injection Hc as Hc; subst; exact Hp].
Qed.
#[program] Definition appASP {A B} : ASPArr (ASPArr A B * A) B :=
  fun P b => exists f a, P (f, a) /\ f (fun x => x = a) b.
Next Obligation.
  apply asp_join_hom. intros P b. split.
  - intros [f [a [Hp Hf]]]. exists (f, a). split; [exact Hp |]. exists f, a. auto.
  - intros [[f a] [Hp [f' [a' [Heq Hf]]]]]. injection Heq as H1 H2. subst. eauto.
Qed.

#[global] Instance Arrow_ASPArr : Arrow ASPArr :=
  {|arr_pure := @pureASP; arr_comp := @compASP; arr_first := @firstASP|}.
#[global] Instance ArrowChoice_ASPArr : ArrowChoice ASPArr := {|arr_left := @leftASP|}.
#[global] Instance ArrowApply_ASPArr : ArrowApply ASPArr := {|arr_app := @appASP|}.
Definition ASPArr_eq {A B} (f g : ASPArr A B) : Prop := forall P b, f P b <-> g P b.
#[global] Instance ASPArr_eq_Equivalence {A B} : Equivalence (@ASPArr_eq A B).
Proof.
  constructor.
  - intros f P b. reflexivity.
  - intros f g H P b. symmetry. apply H.
  - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
Qed.
#[global] Instance ArrowEq_ASPArr : ArrowEq ASPArr := {|arrow_eq := @ASPArr_eq|}.

Lemma get_pure {A B} (h : A -> B) :
  getASPArr (pureASP h) = fun P b => exists a, P a /\ h a = b.
Proof. reflexivity. Qed.
Lemma get_comp {A B C} (f : ASPArr A B) (g : ASPArr B C) :
  getASPArr (compASP f g) = fun P c => g (f P) c.
Proof. reflexivity. Qed.
Lemma get_first {A B C} (f : ASPArr A B) :
  getASPArr (@firstASP A B C f) = fun P bc => f (fun a => P (a, snd bc)) (fst bc).
Proof. reflexivity. Qed.
Lemma get_left {A B C} (f : ASPArr A B) : getASPArr (@leftASP A B C f) = leftASPT f.
Proof. reflexivity. Qed.
Lemma get_app {A B} :
  getASPArr (@appASP A B) = fun P b => exists f a, P (f, a) /\ f (fun x => x = a) b.
Proof. reflexivity. Qed.

(** Recovery lives here so Core's public laws do not depend on Rel clients. *)
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
  unfold aspRel. destruct x as [a|c], y as [b|d]; cbn [arr_left ArrowChoice_ASPArr];
    rewrite get_left; unfold leftASPT; cbn.
  - apply getASPArr_ext_iff. intro z. split; [intro H; injection H; auto | intros ->; reflexivity].
  - split; [discriminate | contradiction].
  - rewrite getASPArr_join. split; [intros [z [H _]]; discriminate | contradiction].
  - split; [intro H; injection H; auto | intros ->; reflexivity].
Qed.
Lemma aspRel_app {A B} (p : ASPArr A B * A) b :
  aspRel arr_app p b <-> aspRel (fst p) (snd p) b.
Proof.
  destruct p as [f a]. unfold aspRel. cbn [fst snd arr_app ArrowApply_ASPArr].
  rewrite get_app. split.
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
#[global] Instance RelArrow_ASPArr : RelArrow ASPArr := {|
  rel_reading := @aspRel; rel_pure := @aspRel_pure; rel_comp := @aspRel_comp;
  rel_first := fun A B C f a c b d => aspRel_first f (a, c) (b, d)
|}.
#[global] Instance RelArrowChoice_ASPArr : RelArrowChoice ASPArr := {|rel_left := @aspRel_left|}.
#[global] Instance RelArrowApply_ASPArr : RelArrowApply ASPArr := {|
  rel_app := fun A B f a b => aspRel_app (f, a) b
|}.
#[global] Instance RelArrowEq_ASPArr : RelArrowEq ASPArr := {|rel_arrow_eq := @aspRel_eq|}.
#[global] Instance ArrowLaws_ASPArr : ArrowLaws ASPArr :=
  @rel_arrow_laws ASPArr Arrow_ASPArr ArrowEq_ASPArr RelArrow_ASPArr RelArrowEq_ASPArr.
#[global] Instance ArrowChoiceLaws_ASPArr : ArrowChoiceLaws ASPArr :=
  @rel_arrow_choice_laws ASPArr Arrow_ASPArr ArrowEq_ASPArr RelArrow_ASPArr
    RelArrowEq_ASPArr ArrowChoice_ASPArr RelArrowChoice_ASPArr.
#[global] Instance ArrowApplyLaws_ASPArr : ArrowApplyLaws ASPArr :=
  @rel_arrow_apply_laws ASPArr Arrow_ASPArr ArrowEq_ASPArr RelArrow_ASPArr
    RelArrowEq_ASPArr ArrowApply_ASPArr RelArrowApply_ASPArr.
