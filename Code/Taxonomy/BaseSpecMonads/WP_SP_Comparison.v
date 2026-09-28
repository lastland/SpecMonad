(** * Stateful AWP and DWLP

    Both are carved out of [WSt S = stateT S WPure] by healthiness, stated at
    every start state:

      AWPSt  S A = { w : WSt S A | wpStrict w ∧ wpDisjunctive w }
      DWLPSt S A = { w : WSt S A | wpTerminating w ∧ wpConjunctive w }

    [WSt]'s [ret] is strict, terminating, disjunctive and conjunctive, and its
    [bind] preserves each property, so both carvings are closed under [ret]
    and [bind].  They keep [WSt]'s operations, [eq1] and order [ordWSt]:

      ret a    = λs k. k (a, s)
      bind w f = λs k. w s (λ(a, s'). f a s' k)
      w ⊑ v    = ∀s k. v s k → w s k

    Disjunctivity and conjunctivity quantify over nonempty families;
    strictness and termination supply the empty ones.

    The observations of [stdivnd] read its terminating outcomes, angelically
    and demonically:

      obsAWPSt  m = λs k. ∃r. m s ⇓ r ∧ k r
      obsDWLPSt m = λs k. ∀r. m s ⇓ r → k r

    where [m s ⇓ r] is [unOptionT (runStateT m s) (Some r)]. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad OptionMonad StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require SpecificationMonads.

(* ================================================================= *)
(** ** Healthiness of [WSt]                                           *)
(* ================================================================= *)

Definition wpStrict {S A} (w : WSt S A) : Prop :=
  forall s, ~ getWPure (runStateT w s) (fun _ => False).

Definition wpTerminating {S A} (w : WSt S A) : Prop :=
  forall s, getWPure (runStateT w s) (fun _ => True).

Definition wpDisjunctive {S A} (w : WSt S A) : Prop :=
  forall s (I : Type) (i0 : I) (Q : I -> A * S -> Prop),
    getWPure (runStateT w s) (fun r => exists i, Q i r)
    <-> exists i, getWPure (runStateT w s) (Q i).

Definition wpConjunctive {S A} (w : WSt S A) : Prop :=
  forall s (I : Type) (i0 : I) (Q : I -> A * S -> Prop),
    getWPure (runStateT w s) (fun r => forall i, Q i r)
    <-> forall i, getWPure (runStateT w s) (Q i).

(** *** [ret] has all four *)

Lemma wpStrict_ret {S A} (a : A) : wpStrict (ret a : WSt S A).
Proof. intros s H. exact H. Qed.

Lemma wpTerminating_ret {S A} (a : A) : wpTerminating (ret a : WSt S A).
Proof. intro s. exact I. Qed.

Lemma wpDisjunctive_ret {S A} (a : A) : wpDisjunctive (ret a : WSt S A).
Proof. intros s Ix i0 Q. cbn. reflexivity. Qed.

Lemma wpConjunctive_ret {S A} (a : A) : wpConjunctive (ret a : WSt S A).
Proof. intros s Ix i0 Q. cbn. reflexivity. Qed.

(** *** [bind] preserves each *)

Lemma wpStrict_bind {S A B} (w : WSt S A) (f : A -> WSt S B) :
  wpStrict w -> (forall a, wpStrict (f a)) -> wpStrict (bind w f).
Proof.
  intros Hw Hf s H. apply (Hw s). cbn in H. revert H. apply getWPure_mono.
  intros [a s'] H. exact (Hf a s' H).
Qed.

Lemma wpTerminating_bind {S A B} (w : WSt S A) (f : A -> WSt S B) :
  wpTerminating w -> (forall a, wpTerminating (f a)) -> wpTerminating (bind w f).
Proof.
  intros Hw Hf s. cbn. generalize (Hw s). apply getWPure_mono.
  intros [a s'] _. exact (Hf a s').
Qed.

Lemma wpDisjunctive_bind {S A B} (w : WSt S A) (f : A -> WSt S B) :
  wpDisjunctive w -> (forall a, wpDisjunctive (f a)) -> wpDisjunctive (bind w f).
Proof.
  intros Hw Hf s Ix i0 Q. cbn. split.
  - intro H. apply (proj1 (Hw s Ix i0 _)). revert H. apply getWPure_mono.
    intros [a s'] H. exact (proj1 (Hf a s' Ix i0 Q) H).
  - intros [i H]. revert H. apply getWPure_mono.
    intros [a s'] H. apply (proj2 (Hf a s' Ix i0 Q)). exists i. exact H.
Qed.

Lemma wpConjunctive_bind {S A B} (w : WSt S A) (f : A -> WSt S B) :
  wpConjunctive w -> (forall a, wpConjunctive (f a)) -> wpConjunctive (bind w f).
Proof.
  intros Hw Hf s Ix i0 Q. cbn. split.
  - intros H i. revert H. apply getWPure_mono.
    intros [a s'] H. exact (proj1 (Hf a s' Ix i0 Q) H i).
  - intro H. pose proof (proj2 (Hw s Ix i0 _) H) as H'. revert H'. apply getWPure_mono.
    intros [a s'] H'. exact (proj2 (Hf a s' Ix i0 Q) H').
Qed.

Section Stateful.
  Variable S : Type.

  (* ================================================================= *)
  (** ** Stateful AWP                                                   *)
  (* ================================================================= *)

  Definition AWPSt (A : Type) : Type := { w : WSt S A | wpStrict w /\ wpDisjunctive w }.

  #[program] Definition retAWPSt {A} (a : A) : AWPSt A := exist _ (ret a) _.
  Next Obligation. exact (conj (wpStrict_ret a) (wpDisjunctive_ret a)). Qed.

  #[program] Definition bindAWPSt {A B} (w : AWPSt A) (f : A -> AWPSt B) : AWPSt B :=
    exist _ (bind (proj1_sig w) (fun a => proj1_sig (f a))) _.
  Next Obligation.
    split.
    - apply wpStrict_bind; [ exact (proj1 (proj2_sig w)) | intro a; exact (proj1 (proj2_sig (f a))) ].
    - apply wpDisjunctive_bind; [ exact (proj2 (proj2_sig w)) | intro a; exact (proj2 (proj2_sig (f a))) ].
  Qed.

  Definition leAWPSt {A} (w v : AWPSt A) : Prop := ordWSt (proj1_sig w) (proj1_sig v).

  #[global] Instance Monad_AWPSt : Monad AWPSt := {| ret := @retAWPSt ; bind := @bindAWPSt |}.

  #[global] Instance Eq1_AWPSt : Eq1 AWPSt := fun A w v => eq1 (proj1_sig w) (proj1_sig v).

  #[global] Instance Eq1Equivalence_AWPSt : @Eq1Equivalence AWPSt _ Eq1_AWPSt.
  Proof.
    intro A. destruct (Eq1Equivalence__WSt S A) as [Hr Hs Ht]. constructor.
    - intro w. exact (Hr (proj1_sig w)).
    - intros w v H. exact (Hs _ _ H).
    - intros w v u H1 H2. exact (Ht _ _ _ H1 H2).
  Qed.

  #[global] Instance MonadLawsE_AWPSt : @MonadLawsE AWPSt Eq1_AWPSt Monad_AWPSt.
  Proof.
    destruct (MonadLawsE__WSt S) as [Lrl Lrr Lbb Lpb]. constructor.
    - intros A B f a. exact (Lrl A B (fun a => proj1_sig (f a)) a).
    - intros A w. exact (Lrr A (proj1_sig w)).
    - intros A B C w f g.
      exact (Lbb A B C (proj1_sig w) (fun a => proj1_sig (f a)) (fun b => proj1_sig (g b))).
    - intros A B w v Hwv f g Hfg.
      exact (Lpb A B (proj1_sig w) (proj1_sig v) Hwv
               (fun a => proj1_sig (f a)) (fun a => proj1_sig (g a)) Hfg).
  Qed.

  #[global] Instance OrderedMonad_AWPSt : OrderedMonad AWPSt (@leAWPSt).
  Proof.
    destruct (SpecificationMonads.OrderedMonad_WSt S) as [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre A) as [Hr Ht]. constructor.
      + intro w. exact (Hr (proj1_sig w)).
      + intros w v u H1 H2. exact (Ht _ _ _ H1 H2).
    - intros A w v H. exact (Heq A _ _ H).
    - intros A B w v Hwv f g Hfg.
      exact (Hbind A B _ _ Hwv (fun a => proj1_sig (f a)) (fun a => proj1_sig (g a)) Hfg).
  Qed.

  (* ================================================================= *)
  (** ** Stateful DWLP                                                  *)
  (* ================================================================= *)

  Definition DWLPSt (A : Type) : Type := { w : WSt S A | wpTerminating w /\ wpConjunctive w }.

  #[program] Definition retDWLPSt {A} (a : A) : DWLPSt A := exist _ (ret a) _.
  Next Obligation. exact (conj (wpTerminating_ret a) (wpConjunctive_ret a)). Qed.

  #[program] Definition bindDWLPSt {A B} (w : DWLPSt A) (f : A -> DWLPSt B) : DWLPSt B :=
    exist _ (bind (proj1_sig w) (fun a => proj1_sig (f a))) _.
  Next Obligation.
    split.
    - apply wpTerminating_bind; [ exact (proj1 (proj2_sig w)) | intro a; exact (proj1 (proj2_sig (f a))) ].
    - apply wpConjunctive_bind; [ exact (proj2 (proj2_sig w)) | intro a; exact (proj2 (proj2_sig (f a))) ].
  Qed.

  Definition leDWLPSt {A} (w v : DWLPSt A) : Prop := ordWSt (proj1_sig w) (proj1_sig v).

  #[global] Instance Monad_DWLPSt : Monad DWLPSt := {| ret := @retDWLPSt ; bind := @bindDWLPSt |}.

  #[global] Instance Eq1_DWLPSt : Eq1 DWLPSt := fun A w v => eq1 (proj1_sig w) (proj1_sig v).

  #[global] Instance Eq1Equivalence_DWLPSt : @Eq1Equivalence DWLPSt _ Eq1_DWLPSt.
  Proof.
    intro A. destruct (Eq1Equivalence__WSt S A) as [Hr Hs Ht]. constructor.
    - intro w. exact (Hr (proj1_sig w)).
    - intros w v H. exact (Hs _ _ H).
    - intros w v u H1 H2. exact (Ht _ _ _ H1 H2).
  Qed.

  #[global] Instance MonadLawsE_DWLPSt : @MonadLawsE DWLPSt Eq1_DWLPSt Monad_DWLPSt.
  Proof.
    destruct (MonadLawsE__WSt S) as [Lrl Lrr Lbb Lpb]. constructor.
    - intros A B f a. exact (Lrl A B (fun a => proj1_sig (f a)) a).
    - intros A w. exact (Lrr A (proj1_sig w)).
    - intros A B C w f g.
      exact (Lbb A B C (proj1_sig w) (fun a => proj1_sig (f a)) (fun b => proj1_sig (g b))).
    - intros A B w v Hwv f g Hfg.
      exact (Lpb A B (proj1_sig w) (proj1_sig v) Hwv
               (fun a => proj1_sig (f a)) (fun a => proj1_sig (g a)) Hfg).
  Qed.

  #[global] Instance OrderedMonad_DWLPSt : OrderedMonad DWLPSt (@leDWLPSt).
  Proof.
    destruct (SpecificationMonads.OrderedMonad_WSt S) as [Hpre Heq Hbind]. constructor.
    - intro A. destruct (Hpre A) as [Hr Ht]. constructor.
      + intro w. exact (Hr (proj1_sig w)).
      + intros w v u H1 H2. exact (Ht _ _ _ H1 H2).
    - intros A w v H. exact (Heq A _ _ H).
    - intros A B w v Hwv f g Hfg.
      exact (Hbind A B _ _ Hwv (fun a => proj1_sig (f a)) (fun a => proj1_sig (g a)) Hfg).
  Qed.

  (* ================================================================= *)
  (** ** Observations of [stdivnd]                                      *)
  (* ================================================================= *)

  #[program] Definition obsAWPSt {A} (m : stdivnd S A) : AWPSt A :=
    exist _ (mkStateT (fun s =>
               mkWPure (fun k => exists r, unOptionT (runStateT m s) (Some r) /\ k r) _)) _.
  Next Obligation. intros p q Hpq [r [Hr Hp]]. exists r. split; [ exact Hr | exact (Hpq r Hp) ]. Qed.
  Next Obligation.
    split.
    - intros s [r [_ []]].
    - intros s Ix i0 Q. cbn. split.
      + intros [r [Hr [i Hq]]]. exists i, r. split; assumption.
      + intros [i [r [Hr Hq]]]. exists r. split; [ exact Hr | exists i; exact Hq ].
  Qed.

  #[program] Definition obsDWLPSt {A} (m : stdivnd S A) : DWLPSt A :=
    exist _ (mkStateT (fun s =>
               mkWPure (fun k => forall r, unOptionT (runStateT m s) (Some r) -> k r) _)) _.
  Next Obligation. intros p q Hpq H r Hr. exact (Hpq r (H r Hr)). Qed.
  Next Obligation.
    split.
    - intros s r _. exact I.
    - intros s Ix i0 Q. cbn. split.
      + intros H i r Hr. exact (H r Hr i).
      + intros H r Hr i. exact (H i r Hr).
  Qed.

  Theorem obsAWPSt_ret {A} (a : A) : eq1 (obsAWPSt (ret a)) (ret a).
  Proof.
    intros s k. cbn. split.
    - intros [r [E Hk]]. injection E as E. subst r. exact Hk.
    - intro Hk. exists (a, s). split; [ reflexivity | exact Hk ].
  Qed.

  Theorem obsAWPSt_bind {A B} (m : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsAWPSt (bind m f)) (bind (obsAWPSt m) (fun a => obsAWPSt (f a))).
  Proof.
    intros s k. cbn. split.
    - intros [r [[[[a s']|] [Hm Hf]] Hk]]; [| discriminate Hf ].
      exists (a, s'). split; [ exact Hm | exists r; split; [ exact Hf | exact Hk ] ].
    - intros [[a s'] [Hm [r [Hf Hk]]]]. exists r. split; [| exact Hk ].
      exists (Some (a, s')). split; [ exact Hm | exact Hf ].
  Qed.

  Theorem obsDWLPSt_ret {A} (a : A) : eq1 (obsDWLPSt (ret a)) (ret a).
  Proof.
    intros s k. cbn. split.
    - intro H. exact (H (a, s) eq_refl).
    - intros Hk r E. injection E as E. subst r. exact Hk.
  Qed.

  Theorem obsDWLPSt_bind {A B} (m : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDWLPSt (bind m f)) (bind (obsDWLPSt m) (fun a => obsDWLPSt (f a))).
  Proof.
    intros s k. cbn. split.
    - intros H [a s'] Hm r Hf. apply H. exists (Some (a, s')). split; [ exact Hm | exact Hf ].
    - intros H r [[[a s']|] [Hm Hf]]; [ exact (H (a, s') Hm r Hf) | discriminate Hf ].
  Qed.
End Stateful.
