(** * [ASPArr]: the arrow of angelic strongest-postcondition transformers.

      [ASPArr A B] = { f : SPArrT A B | f monotone, strict, disjunctive }

    The carrier refines [Arrows/SPArr.SPArrT] by homomorphism properties, as
    monotonicity refines [WPure]; [asp_join_iff] shows they are exactly join
    preservation, [f P b <-> exists a, P a /\ f {a} b], the form the proofs
    below use.  This file is the arrow and its laws only:
    [Arrow] / [ArrowChoice] / [ArrowApply] and the three law bundles.

    The RELATION an arrow denotes lives in [ASPArrowRel.v], and the
    specification monads built over it in [ASPMonad.v]. *)

From Coq Require Import Morphisms RelationClasses Setoid.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Taxonomy.Arrows Require Import SPArr.
(* ================================================================= *)
(** ** [ASPArr]                                                      *)
(* ================================================================= *)

Section ASPArr.

  Definition asp_join {A B} (f : SPArrT A B) : Prop :=
    forall P b, f P b <-> exists a, P a /\ f (fun x => x = a) b.

  Lemma asp_join_hom {A B} (f : SPArrT A B) :
    asp_join f -> sp_monotone f /\ sp_strict f /\ sp_disjunctive f.
  Proof.
    intro H. split; [| split ].
    - intros P Q HPQ b Hf. apply H. apply H in Hf. destruct Hf as [a [Ha Hf]].
      exists a. split; [ exact (HPQ a Ha) | exact Hf ].
    - intros b Hf. destruct (proj1 (H _ b) Hf) as [a [[] _]].
    - intros I _ P b. rewrite (H _ b). split.
      + intros [a [[i Hi] Hf]]. exists i. apply (H _ b). exists a. split; assumption.
      + intros [i Hf]. apply (H _ b) in Hf. destruct Hf as [a [Hi Hf]].
        exists a. split; [ exists i; exact Hi | exact Hf ].
  Qed.

  (** Backwards, [P] lies below the union of [False] and the singletons of
      its elements. *)
  Lemma asp_hom_join {A B} (f : SPArrT A B) :
    sp_monotone f /\ sp_strict f /\ sp_disjunctive f -> asp_join f.
  Proof.
    intros [Hm [Hs Hd]] P b. split.
    - intro Hf.
      pose (Q := fun (i : option { a : A | P a }) (x : A) =>
                   match i with Some a => x = proj1_sig a | None => False end).
      assert (HQ : f (fun x => exists i, Q i x) b).
      { apply (Hm P); [| exact Hf ]. intros x Hx. exists (Some (exist _ x Hx)). reflexivity. }
      apply (Hd _ (inhabits None) Q b) in HQ.
      destruct HQ as [[[a Ha] |] Hq]; [ exists a; split; [ exact Ha | exact Hq ] | destruct (Hs b Hq) ].
    - intros [a [Ha Hf]]. apply (Hm (fun x => x = a)); [ intros x ->; exact Ha | exact Hf ].
  Qed.

  Theorem asp_join_iff {A B} (f : SPArrT A B) :
    asp_join f <-> sp_monotone f /\ sp_strict f /\ sp_disjunctive f.
  Proof. split; [ apply asp_join_hom | apply asp_hom_join ]. Qed.

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
    intros [a [Hp Hf]]; exists a; split; solve [ apply H, Hp | exact Hf ].
  Qed.

  Lemma getASPArr_ext {A B} (f : ASPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b -> f Q b.
  Proof.
    intro H; apply getASPArr_mono; intros; apply H; assumption.
  Qed.

  Lemma getASPArr_ext_iff {A B} (f : ASPArr A B) (P Q : A -> Prop) b :
    (forall a, P a <-> Q a) -> f P b <-> f Q b.
  Proof.
    split; now apply getASPArr_ext.
  Qed.

  (** The arrow of a relation: its direct image. *)
  #[program] Definition ofRelASPArr {A B} (R : A -> B -> Prop) : ASPArr A B :=
    fun P b => exists a, P a /\ R a b.
  Next Obligation.
    apply asp_join_hom. intros P b. split.
    - intros [a [Hp HR]]. exists a. split; [ exact Hp | exists a; auto ].
    - intros [a [Hp [x [Hx HR]]]]. subst x. exists a. auto.
  Qed.

  (** pure, comp, first, left, app *)

  #[program] Definition pureASP {A B} (h : A -> B) : ASPArr A B :=
    fun P b => exists a, P a /\ h a = b.
  Next Obligation.
    apply asp_join_hom. intros P b. split.
    - intros [a [Hp Hb]]. exists a. split; [ exact Hp | exists a; auto ].
    - intros [a [Hp [x [Hx Hb]]]]. subst. eauto.
  Qed.

  #[program] Definition compASP {A B C} (f : ASPArr A B) (g : ASPArr B C) : ASPArr A C :=
    fun P c => g (f P) c.
  Next Obligation.
    apply asp_join_hom. intros P c. rewrite getASPArr_join. split.
    - intros [b [Hf Hg]]. apply getASPArr_join in Hf. destruct Hf as [a [Hp Hf]].
      exists a. split; [ exact Hp |].
      apply getASPArr_join. exists b. exact (conj Hf Hg).
    - intros [a [Hp Hg]]. apply getASPArr_join in Hg. destruct Hg as [b [Hf Hg]].
      exists b. split; [| exact Hg ].
      apply getASPArr_join. exists a. exact (conj Hp Hf).
  Qed.

  #[program] Definition firstASP {A B C} (f : ASPArr A B) : ASPArr (A * C) (B * C) :=
    fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Next Obligation.
    apply asp_join_hom. intros P [b c]. cbn [fst snd]. rewrite getASPArr_join. split.
    - intros [a [Hp Hf]]. exists (a, c). split; [ exact Hp |].
      apply (getASPArr_ext f (fun x => x = a)); [| exact Hf ].
      intro x. split; [ intros ->; reflexivity | intro H; injection H; auto ].
    - intros [[a c'] [Hp Hf]].
      apply getASPArr_join in Hf. destruct Hf as [x [Hx Hf]].
      injection Hx as Hx1 Hx2. subst. eauto.
  Qed.

  Definition leftASPT {A B C} (f : ASPArr A B) : SPArrT (A + C) (B + C) :=
    fun P y => match y with
               | inl b => f (fun a => P (inl a)) b
               | inr c => P (inr c)
               end.

  #[program] Definition leftASP {A B C} (f : ASPArr A B) : ASPArr (A + C) (B + C) :=
    leftASPT f.
  Next Obligation.
    apply asp_join_hom. intros P [b | c]; cbn.
    - rewrite getASPArr_join. split.
      + intros [a [Hp Hf]]. exists (inl a). split; [ exact Hp |].
        apply (getASPArr_ext f (fun x => x = a)); [| exact Hf ].
        intro x. split; [ intros ->; reflexivity | intro H; injection H; auto ].
      + intros [[a | c] [Hp Hf]].
        * apply getASPArr_join in Hf. destruct Hf as [x [Hx Hf]].
          injection Hx as Hx1. subst. eauto.
        * apply getASPArr_join in Hf. destruct Hf as [x [Hx _]]. discriminate Hx.
    - split.
      + intro Hp. exists (inr c). auto.
      + intros [[a | c'] [Hp Hc]]; [ discriminate Hc | injection Hc as Hc; subst; exact Hp ].
  Qed.

  #[program] Definition appASP {A B} : ASPArr (ASPArr A B * A) B :=
    fun P b => exists f a, P (f, a) /\ f (fun x => x = a) b.
  Next Obligation.
    apply asp_join_hom. intros P b. split.
    - intros [f [a [Hp Hf]]]. exists (f, a). split; [ exact Hp |]. exists f, a. auto.
    - intros [[f a] [Hp [f' [a' [Heq Hf]]]]]. injection Heq as H1 H2. subst. eauto.
  Qed.

  #[global] Instance Arrow_ASPArr : Arrow ASPArr :=
    {| arr_pure := @pureASP ; arr_comp := @compASP ; arr_first := @firstASP |}.

  #[global] Instance ArrowChoice_ASPArr : ArrowChoice ASPArr :=
    {| arr_left := @leftASP |}.

  #[global] Instance ArrowApply_ASPArr : ArrowApply ASPArr :=
    {| arr_app := @appASP |}.

  (** Pointwise logical equivalence of the underlying transformers. *)
  Definition ASPArr_eq {A B} (f g : ASPArr A B) : Prop :=
    forall P b, f P b <-> g P b.

  #[global] Instance ASPArr_eq_Equivalence {A B} : Equivalence (@ASPArr_eq A B).
  Proof.
    constructor.
    - intros f P b. reflexivity.
    - intros f g H P b. symmetry. apply H.
    - intros f g h H1 H2 P b. etransitivity; [ apply H1 | apply H2 ].
  Qed.

  #[global] Instance ArrowEq_ASPArr : ArrowEq ASPArr :=
    {| arrow_eq := @ASPArr_eq |}.

End ASPArr.

(* ================================================================= *)
(** ** Arrow laws                                                    *)
(* ================================================================= *)

(** Each operation, unfolded once. *)
Section Get.
  Lemma get_pure {A B} (h : A -> B) :
    getASPArr (pureASP h) = fun P b => exists a, P a /\ h a = b.
  Proof. reflexivity. Qed.
  Lemma get_comp {A B C} (f : ASPArr A B) (g : ASPArr B C) :
    getASPArr (compASP f g) = fun P c => g (f P) c.
  Proof. reflexivity. Qed.
  Lemma get_first {A B C} (f : ASPArr A B) :
    getASPArr (@firstASP A B C f) = fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Proof. reflexivity. Qed.
  Lemma get_left {A B C} (f : ASPArr A B) :
    getASPArr (@leftASP A B C f) = leftASPT f.
  Proof. reflexivity. Qed.
  Lemma get_app {A B} :
    getASPArr (@appASP A B) = fun P b => exists f a, P (f, a) /\ f (fun x => x = a) b.
  Proof. reflexivity. Qed.
End Get.

Local Ltac asp_simpl :=
  cbn [arrow_eq ArrowEq_ASPArr ASPArr_eq arr_id arr_second arr_comp arr_pure arr_first
       arr_left arr_app Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr];
  repeat rewrite ?get_comp, ?get_pure, ?get_first, ?get_left, ?get_app;
  unfold leftASPT; cbv beta.

Local Ltac asp_intro := cbn [arrow_eq ArrowEq_ASPArr]; unfold ASPArr_eq.

#[global] Instance ArrowLaws_ASPArr : ArrowLaws ASPArr.
Proof.
  constructor; intros; asp_intro.
  - intros P b. asp_simpl. apply getASPArr_ext_iff. intro a. split.
    + intros [x [Hx <-]]. exact Hx.
    + intro Ha. exists a. auto.
  - intros P b. asp_simpl. split.
    + intros [a [H <-]]. exact H.
    + intro H. exists b. auto.
  - intros P b. asp_simpl. reflexivity.
  - intros P b. asp_simpl. split.
    + intros [a [[a0 [Hp <-]] <-]]. exists a0. auto.
    + intros [a [Hp <-]]. exists (f a). split; [ exists a; auto | reflexivity ].
  - intros P [b c]. asp_simpl. cbn. split.
    + intros [a [Hp <-]]. exists (a, c). auto.
    + intros [[a c'] [Hp Heq]]. injection Heq as <- <-. exists a. auto.
  - intros P b. asp_simpl. reflexivity.
  - intros P b. asp_simpl. split.
    + intros [[b' d] [Hf <-]]. cbn in Hf. apply getASPArr_join in Hf.
      destruct Hf as [a [Hp Hf]]. apply getASPArr_join.
      exists a. split; [ exists (a, d); auto | exact Hf ].
    + intro H. apply getASPArr_join in H.
      destruct H as [a [[[a' d] [Hp Ha]] Hf]]. cbn in Ha. subst a'.
      exists (b, d). cbn. split; [| reflexivity ].
      apply getASPArr_join. exists a. auto.
  - intros P [b1 [c d]]. asp_simpl. cbn.
    transitivity (f (fun a => P ((a, c), d)) b1).
    + split.
      * intros [[[b' c'] d'] [Hf Heq]]. cbn in *. injection Heq as -> -> ->. exact Hf.
      * intro H. exists ((b1, c), d). auto.
    + apply getASPArr_ext_iff. intro a. split.
      * intro H. exists ((a, c), d). auto.
      * intros [[[a' c'] d'] [Hp Heq]]. cbn in Heq. injection Heq as -> -> ->. exact Hp.
  - intros f f' Hf g g' Hg P c. asp_simpl.
    transitivity (g (f' P) c); [ apply getASPArr_ext_iff; intro; apply Hf | apply Hg ].
  - intros f f' Hf P bc. asp_simpl. apply Hf.
  - (* first_natural *)
    intros P [b d]. asp_simpl. cbn. split.
    + intros [[b0 c] [Hf Heq]]. injection Heq as Hb Hd. subst b0 d.
      apply getASPArr_join in Hf. destruct Hf as [a [HP Hr]].
      apply getASPArr_join. exists a. split; [|exact Hr].
      exists (a, c). auto.
    + intro H. apply getASPArr_join in H.
      destruct H as [a [[[a0 c] [HP Heq]] Hr]].
      injection Heq as Ha Hd. subst a0 d.
      exists (b, c). split; [|reflexivity].
      apply getASPArr_join. exists a. auto.
Qed.

#[global] Instance ArrowChoiceLaws_ASPArr : ArrowChoiceLaws ASPArr.
Proof.
  constructor; intros; asp_intro.
  - (* left_pure *)
    intros P [b | c]; asp_simpl; split.
    + intros [a [Hp <-]]. exists (inl a). auto.
    + intros [[a | c] [Hp Heq]]; cbn in Heq; [ injection Heq as <- | discriminate Heq ].
      exists a. auto.
    + intro Hp. exists (inr c). auto.
    + intros [[a | c'] [Hp Heq]]; cbn in Heq; [ discriminate Heq | injection Heq as -> ].
      exact Hp.
  - (* left_comp *)
    intros P [b | c]; asp_simpl; reflexivity.
  - (* left_inl *)
    intros P [b | c]; asp_simpl; split.
    + intros [a [H Heq]]. injection Heq as ->.
      apply (getASPArr_ext f P). { intro x. split; [ intro Hx; exists x; auto | ].
        intros [x' [Hx Heq]]. injection Heq as ->. exact Hx. } exact H.
    + intro H. exists b. split; [| reflexivity ].
      refine (getASPArr_ext f _ P b _ H).
      intro x. split; [ intros [x' [Hx Heq]]; injection Heq as ->; exact Hx | ].
      intro Hx. exists x. auto.
    + intros [a [_ Heq]]. discriminate Heq.
    + intros [a [_ Heq]]. discriminate Heq.
  - (* left_assoc *)
    intros P [b | [c | d]]; asp_simpl; split.
    + intros [[[y | c] | d] [H Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. try rewrite get_left in H; try unfold leftASPT in H; cbn in H.
      refine (getASPArr_ext f _ _ b _ H).
      intro a. split; [ intro Ha; exists (inl (inl a)); auto |].
      intros [[[a' | c'] | d'] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exact Hp.
    + intro H. exists (inl (inl b)). split; [| reflexivity ].
      cbn; try rewrite get_left; try unfold leftASPT; cbn.
      refine (getASPArr_ext f _ _ b _ H).
      intro a. split; [| intro Ha; exists (inl (inl a)); auto ].
      intros [[[a' | c'] | d'] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exact Hp.
    + intros [[[y | c'] | d] [H Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. try rewrite get_left in H; try unfold leftASPT in H; cbn in H.
      exists (inl (inr c)). auto.
    + intros [[[a | c'] | d] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exists (inl (inr c)). split; [| reflexivity ].
      cbn; try rewrite get_left; try unfold leftASPT; cbn. exact Hp.
    + intros [[[y | c] | d'] [H Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exists (inr d). auto.
    + intros [[[a | c] | d'] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exists (inr d). auto.
  - (* left_inr *)
    intros P [b | c]; asp_simpl; split.
    + intro H. apply getASPArr_join in H.
      destruct H as [a [[a0 [_ Heq]] _]]. discriminate Heq.
    + intros [a [_ Heq]]. discriminate Heq.
    + intros [a [Hp Heq]]. injection Heq as ->. exists c. auto.
    + intros [a [Hp Heq]]. injection Heq as ->. exists c. auto.
  - (* left_natural *)
    intros P [b | d]; asp_simpl; split.
    + intros [[y | c] [H Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. refine (getASPArr_ext f _ _ b _ H).
      intro a. split; [ intro Ha; exists (inl a); auto |].
      intros [[a' | c] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exact Hp.
    + intro H. exists (inl b). split; [| reflexivity ].
      refine (getASPArr_ext f _ _ b _ H).
      intro a. split; [| intro Ha; exists (inl a); auto ].
      intros [[a' | c] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as ->. exact Hp.
    + intros [[y | c] [H Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as <-. exists (inr c). auto.
    + intros [[a | c] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as <-. exists (inr c). auto.
  - (* first_left_dist *)
    intros P [[b d] | [c d]]; asp_simpl; split.
    + intros [[[y | c] d'] [H Heq]]; cbn in *; try discriminate Heq.
      injection Heq as -> ->. refine (getASPArr_ext f _ _ b _ H).
      intro a. split; [ intro Ha; exists (inl a, d); auto |].
      intros [[[a' | c] d'] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as -> ->. exact Hp.
    + intro H. exists (inl b, d). split; [| reflexivity ]. cbn.
      refine (getASPArr_ext f _ _ b _ H).
      intro a. split; [| intro Ha; exists (inl a, d); auto ].
      intros [[[a' | c] d'] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as -> ->. exact Hp.
    + intros [[[y | c'] d'] [H Heq]]; cbn in *; try discriminate Heq.
      injection Heq as -> ->. exists (inr c, d). auto.
    + intros [[[a | c'] d'] [Hp Heq]]; cbn in Heq; try discriminate Heq.
      injection Heq as -> ->. exists (inr c, d). auto.
  - (* left_proper *)
    intros f f' Hf P [b | c]; cbn; [ apply Hf | reflexivity ].
Qed.

#[global] Instance ArrowApplyLaws_ASPArr : ArrowApplyLaws ASPArr.
Proof.
  constructor.
  - (* app_law *)
    intros A B f. asp_intro. intros P b. asp_simpl. split.
    + intros [f0 [a [[a0 [Hp Heq]] Hf]]]. injection Heq as <- <-.
      apply getASPArr_join. exists a0. auto.
    + intro H. apply getASPArr_join in H. destruct H as [a [Hp Hf]].
      exists f, a. split; [ exists a; auto | exact Hf ].
  - (* app_pair *)
    intros A B. asp_intro. intros P q. asp_simpl. split.
    + intros [f [y [[x [Hp Heq]] Hf]]]. cbn [fst snd] in Hp, Heq. subst f.
      rewrite get_pure in Hf. destruct Hf as [y' [Hy Hq]]. subst y'.
      exists (x, y). auto.
    + intros [[x y] [Hp Hq]]. subst q.
      exists (pureASP (fun y' : B => (x, y'))), y. cbn [fst snd].
      split; [ exists x; auto |]. rewrite get_pure. exists y. auto.
  - (* app_precompose *)
    intros A B C g. asp_intro. intros P c. asp_simpl.
    unfold arr_second, swap.
    cbn [arr_comp arr_pure arr_first Arrow_ASPArr].
    repeat rewrite ?get_comp, ?get_pure, ?get_first. cbv beta.
    cbn [fst snd]. split.
    + intros [k [a [[f [HP Hk]] Hcomp]]]. subst k.
      rewrite get_comp in Hcomp. apply getASPArr_join in Hcomp.
      destruct Hcomp as [b [Hg Hf]]. exists f, b. split; [|exact Hf].
      exists (b, f). cbn. split; [|reflexivity].
      eapply getASPArr_mono; [|exact Hg]. intros a' ->.
      exists (f, a). auto.
    + intros [f [b [[p [Hg Heq]] Hf]]]. destruct p as [b0 f0]. cbn in Heq, Hg.
      injection Heq as Hf0 Hb. subst f0 b0.
      apply getASPArr_join in Hg.
      destruct Hg as [a [[p [HP Heq]] Hg]]. destruct p as [f0 a0]. cbn in Heq.
      injection Heq as Ha Hf0. subst a0 f0.
      exists (compASP g f), a. split; [exists f; auto |].
      rewrite get_comp. apply getASPArr_join. exists b. auto.
  - (* app_postcompose *)
    intros A B C h. asp_intro. intros P c. asp_simpl. split.
    + intros [f [a [[f0 [Hp Heq]] Hf]]]. cbn [fst snd] in Hp, Heq. subst f.
      rewrite get_comp in Hf.
      apply getASPArr_join in Hf. destruct Hf as [b [Hf0 Hh]].
      apply getASPArr_join. exists b. split; [| exact Hh ].
      exists f0, a. auto.
    + intro H. apply getASPArr_join in H. destruct H as [b [[f [a [Hp Hf]]] Hh]].
      exists (compASP f h), a. cbn [fst snd].
      split; [ exists f; auto |].
      rewrite get_comp. apply getASPArr_join. exists b. auto.
  - (* app_ext *)
    intros X A B u v Huv. asp_intro. intros P b. asp_simpl. split.
    + intros [f [a [[x [Hp Heq]] Hf]]].
      specialize (Huv x). destruct (u x) as [fu au] eqn:Hu, (v x) as [fv av] eqn:Hv.
      cbn in Huv. destruct Huv as [Hfg Ha]. subst av.
      injection Heq as <- <-. exists fv, au.
      split; [exists x; auto | apply Hfg; exact Hf].
    + intros [f [a [[x [Hp Heq]] Hf]]].
      specialize (Huv x). destruct (u x) as [fu au] eqn:Hu, (v x) as [fv av] eqn:Hv.
      cbn in Huv. destruct Huv as [Hfg Ha]. subst av.
      injection Heq as <- <-. exists fu, au.
      split; [exists x; auto | apply Hfg; exact Hf].
Qed.
