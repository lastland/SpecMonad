(** * The four WP readings land in their refined monads (paper, Sections 3.5 and 5)

    The readings [dwpPure], [dwlpPure], [awpPure], [awlpPure] of
    [Morphisms.v] target the unrestricted [WPure].  Each lands in the
    refined monad of its interpretation ([WP/WPVariants.v]):

      [dwpPure]   strict, conjunctive        [DWP]
      [dwlpPure]  terminating, conjunctive   [DWLP]
      [awpPure]   strict, disjunctive        [AWP]
      [awlpPure]  terminating, disjunctive   [AWLP]

    ([dwpPure_healthy] &c., without axioms).  Their corestrictions
    [dwpPure_DWP] &c. ([corestrict]) are the base morphisms θ^DWP &c.,
    monad morphisms [divndNE ~> DWP] &c. ([dwpPure_DWP_morphism] &c.).

    Conversely, classically, every element of a refined monad is the
    reading of a computation, up to [eq1] ([dwpPure_DWP_complete] &c.).
    The computation returns the results [a] the transformer cannot exclude
    ([~ w (<> a)], demonic) or can force ([w (= a)], angelic), and its
    divergence is read off [w] at [True] (demonic total) or [False]
    (angelic liberal). *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.WP Require Import WPure WPVariants.
From Incorrectness.Verification.DivNonDet Require Import Computation Morphisms.

(* ================================================================= *)
(** * Soundness: each reading has the properties of its class         *)
(* ================================================================= *)

(** Conjunctivity and disjunctivity, at either divergence value; at a
    divergence outcome they need the family to be non-empty. *)
Lemma demonic_conjunctive {A} (div : Prop) (d : divndNE A) :
  wpure_conjunctive (demonic div d).
Proof.
  intros I [i0] q. split.
  - intros H i [a|] Ho; [ exact (H (Some a) Ho i) | exact (H None Ho) ].
  - intros H [a|] Ho; [ intro i; exact (H i (Some a) Ho) | exact (H i0 None Ho) ].
Qed.

Lemma angelic_disjunctive {A} (div : Prop) (d : divndNE A) :
  wpure_disjunctive (angelic div d).
Proof.
  intros I [i0] q. split.
  - intros [[a|] [Ho H]].
    + destruct H as [i Hi]. exists i, (Some a). exact (conj Ho Hi).
    + exists i0, None. exact (conj Ho H).
  - intros [i [[a|] [Ho H]]].
    + exists (Some a). split; [ exact Ho | exists i; exact H ].
    + exists None. exact (conj Ho H).
Qed.

(** Strictness: a computation has an outcome, and at it the empty
    postcondition fails, as does [False] at divergence. *)
Lemma dwpPure_healthy {A} (d : divndNE A) : dwp_health A (getWPure (dwpPure d)).
Proof.
  split; [ exact (demonic_mono False d) |]. split; [| exact (demonic_conjunctive False d) ].
  intro H. destruct (getNE_nonEmpty d) as [[a|] Ho]; exact (H _ Ho).
Qed.

Lemma dwlpPure_healthy {A} (d : divndNE A) : dwlp_health A (getWPure (dwlpPure d)).
Proof.
  split; [ exact (demonic_mono True d) |]. split; [| exact (demonic_conjunctive True d) ].
  intros [a|] _; exact I.
Qed.

Lemma awpPure_healthy {A} (d : divndNE A) : awp_health A (getWPure (awpPure d)).
Proof.
  split; [ exact (angelic_mono False d) |]. split; [| exact (angelic_disjunctive False d) ].
  intros [[a|] [_ H]]; exact H.
Qed.

(** Termination of the angelic liberal reading needs an outcome. *)
Lemma awlpPure_healthy {A} (d : divndNE A) : awlp_health A (getWPure (awlpPure d)).
Proof.
  split; [ exact (angelic_mono True d) |]. split; [| exact (angelic_disjunctive True d) ].
  destruct (getNE_nonEmpty d) as [oa Ho].
  exists oa. split; [ exact Ho | destruct oa; exact I ].
Qed.

(* ================================================================= *)
(** * The readings as monad morphisms into the refined monads         *)
(* ================================================================= *)

(** A morphism into [WPure] whose values satisfy [h] corestricts to a
    morphism into [WPSub h], which has [WPure]'s [ret], [bind] and [eq1]. *)
Section Corestrict.
  Context (h : WPHealth) {M : Type -> Type} {MonadM : Monad M} {Eq1M : Eq1 M}
    (σ : forall A, M A -> WPure A) (Hh : forall A (m : M A), h A (getWPure (σ A m))).

  #[program] Definition corestrict {A} (m : M A) : WPSub h A := getWPure (σ A m).

  Lemma corestrict_morphism :
    @MonadMorphism M WPure MonadM Monad_WPure Eq1M Eq1_WPure σ ->
    @MonadMorphism M (WPSub h) MonadM (Monad_WPSub h) Eq1M (Eq1_WPSub h) (@corestrict).
  Proof. intros [Hp Hr Hb]. constructor; [ exact Hp | exact Hr | exact Hb ]. Qed.
End Corestrict.

Definition dwpPure_DWP {A} : divndNE A -> DWP A :=
  corestrict dwp_health (@dwpPure) (@dwpPure_healthy).
Definition dwlpPure_DWLP {A} : divndNE A -> DWLP A :=
  corestrict dwlp_health (@dwlpPure) (@dwlpPure_healthy).
Definition awpPure_AWP {A} : divndNE A -> AWP A :=
  corestrict awp_health (@awpPure) (@awpPure_healthy).
Definition awlpPure_AWLP {A} : divndNE A -> AWLP A :=
  corestrict awlp_health (@awlpPure) (@awlpPure_healthy).

Lemma dwpPure_DWP_morphism :
  @MonadMorphism divndNE DWP Monad__divndNE Monad_DWP Eq1__divndNE Eq1_DWP (@dwpPure_DWP).
Proof. exact (corestrict_morphism _ _ _ dwpPure_morphism). Qed.

Lemma dwlpPure_DWLP_morphism :
  @MonadMorphism divndNE DWLP Monad__divndNE Monad_DWLP Eq1__divndNE Eq1_DWLP (@dwlpPure_DWLP).
Proof. exact (corestrict_morphism _ _ _ dwlpPure_morphism). Qed.

Lemma awpPure_AWP_morphism :
  @MonadMorphism divndNE AWP Monad__divndNE Monad_AWP Eq1__divndNE Eq1_AWP (@awpPure_AWP).
Proof. exact (corestrict_morphism _ _ _ awpPure_morphism). Qed.

Lemma awlpPure_AWLP_morphism :
  @MonadMorphism divndNE AWLP Monad__divndNE Monad_AWLP Eq1__divndNE Eq1_AWLP (@awlpPure_AWLP).
Proof. exact (corestrict_morphism _ _ _ awlpPure_morphism). Qed.

(* ================================================================= *)
(** * Completeness: each element of a refined monad is a reading      *)
(* ================================================================= *)

(** Classically, a monotone conjunctive transformer is determined by its
    value at [True] and by the results it cannot exclude; a monotone
    disjunctive one by its value at [False] and by the results it can
    force. *)

Section Representation.
  Context {A : Type} (f : WPureT A) (Hm : wpure_mono f).

  Lemma conjunctive_repr (Hc : wpure_conjunctive f) (Q : A -> Prop) :
    f Q <-> f (fun _ => True) /\ (forall a, ~ f (fun x => x <> a) -> Q a).
  Proof.
    split.
    - intro H. split; [ exact (Hm Q _ (fun _ _ => I) H) |].
      intros a Hna. apply NNPP. intro HQ. apply Hna.
      refine (Hm Q _ _ H). intros x Hx Hxa. subst x. exact (HQ Hx).
    - intros [Htop H]. destruct (classic (exists a, ~ Q a)) as [[a0 Ha0] | Hall].
      + refine (Hm (fun x => forall i : { a | ~ Q a }, x <> proj1_sig i) Q _ _).
        * intros x Hx. apply NNPP. intro HQ. exact (Hx (exist _ x HQ) eq_refl).
        * apply (proj2 (Hc { a | ~ Q a } (inhabits (exist _ a0 Ha0))
                          (fun i x => x <> proj1_sig i))).
          intros [a Ha]. apply NNPP. intro Hn. exact (Ha (H a Hn)).
      + refine (Hm _ Q _ Htop). intros x _. apply NNPP. intro HQ.
        exact (Hall (ex_intro _ x HQ)).
  Qed.

  Lemma disjunctive_repr (Hd : wpure_disjunctive f) (Q : A -> Prop) :
    f Q <-> f (fun _ => False) \/ (exists a, f (fun x => x = a) /\ Q a).
  Proof.
    split.
    - intro H. destruct (classic (exists a, Q a)) as [[a0 Ha0] | Hnone].
      + right.
        assert (Hex : f (fun x => exists i : { a | Q a }, x = proj1_sig i)).
        { refine (Hm Q _ _ H). intros x Hx. exists (exist _ x Hx). reflexivity. }
        destruct (proj1 (Hd { a | Q a } (inhabits (exist _ a0 Ha0))
                           (fun i x => x = proj1_sig i)) Hex) as [[a Ha] Hf].
        exists a. exact (conj Hf Ha).
      + left. refine (Hm Q _ _ H). intros x Hx. exact (Hnone (ex_intro _ x Hx)).
    - intros [H | [a [H Ha]]].
      + refine (Hm _ Q _ H). intros x [].
      + refine (Hm _ Q _ H). intros x Hx. subst x. exact Ha.
  Qed.
End Representation.

(** The outcomes a transformer prescribes, with [div] for divergence. *)
Definition demonicOutcomes {A} (div : Prop) (f : WPureT A) : divnd A :=
  @mkOptionT SetM _ (fun oa => match oa with
                               | Some a => ~ f (fun x => x <> a)
                               | None => div
                               end).

Definition angelicOutcomes {A} (div : Prop) (f : WPureT A) : divnd A :=
  @mkOptionT SetM _ (fun oa => match oa with
                               | Some a => f (fun x => x = a)
                               | None => div
                               end).

(** ** DWP: divergence iff [w] fails at [True] *)

#[program] Definition dwpProgram {A} (w : DWP A) : divndNE A :=
  demonicOutcomes (~ w (fun _ => True)) w.
Next Obligation.
  destruct (proj2_sig w) as [Hm [Hs Hc]].
  destruct (classic (w (fun _ => True))) as [Htop | Hntop];
    [| exists None; exact Hntop ].
  apply NNPP. intro Hne. apply Hs.
  apply (proj2 (conjunctive_repr _ Hm Hc _)). split; [ exact Htop |].
  intros a Ha. exact (Hne (ex_intro _ (Some a) Ha)).
Qed.

Theorem dwpPure_DWP_complete {A} (w : DWP A) : eq1 (dwpPure_DWP (dwpProgram w)) w.
Proof.
  destruct (proj2_sig w) as [Hm [_ Hc]]. intro Q.
  change (demonic False (dwpProgram w) Q <-> getWPSub w Q).
  rewrite (conjunctive_repr _ Hm Hc Q). split.
  - intro H. split.
    + apply NNPP. intro Hntop. exact (H None Hntop).
    + intros a Ha. exact (H (Some a) Ha).
  - intros [Htop H] [a|] Ho; [ exact (H a Ho) | exact (Ho Htop) ].
Qed.

(** ** DWLP: divergence is invisible; every [w] may diverge *)

#[program] Definition dwlpProgram {A} (w : DWLP A) : divndNE A :=
  demonicOutcomes True w.
Next Obligation. exists None. exact I. Qed.

Theorem dwlpPure_DWLP_complete {A} (w : DWLP A) : eq1 (dwlpPure_DWLP (dwlpProgram w)) w.
Proof.
  destruct (proj2_sig w) as [Hm [Ht Hc]]. intro Q.
  change (demonic True (dwlpProgram w) Q <-> getWPSub w Q).
  rewrite (conjunctive_repr _ Hm Hc Q). split.
  - intro H. split; [ exact Ht |]. intros a Ha. exact (H (Some a) Ha).
  - intros [_ H] [a|] Ho; [ exact (H a Ho) | exact I ].
Qed.

(** ** AWP: divergence is invisible; every [w] may diverge *)

#[program] Definition awpProgram {A} (w : AWP A) : divndNE A :=
  angelicOutcomes True w.
Next Obligation. exists None. exact I. Qed.

Theorem awpPure_AWP_complete {A} (w : AWP A) : eq1 (awpPure_AWP (awpProgram w)) w.
Proof.
  destruct (proj2_sig w) as [Hm [Hs Hd]]. intro Q.
  change (angelic False (awpProgram w) Q <-> getWPSub w Q).
  rewrite (disjunctive_repr _ Hm Hd Q). split.
  - intros [[a|] [Ho H]]; [ right; exists a; exact (conj Ho H) | destruct H ].
  - intros [H | [a [Ho H]]]; [ destruct (Hs H) |].
    exists (Some a). exact (conj Ho H).
Qed.

(** ** AWLP: divergence iff [w] holds at [False] *)

#[program] Definition awlpProgram {A} (w : AWLP A) : divndNE A :=
  angelicOutcomes (w (fun _ => False)) w.
Next Obligation.
  destruct (proj2_sig w) as [Hm [Ht Hd]].
  destruct (proj1 (disjunctive_repr _ Hm Hd _) Ht) as [Hbot | [a [Ha _]]].
  - exists None. exact Hbot.
  - exists (Some a). exact Ha.
Qed.

Theorem awlpPure_AWLP_complete {A} (w : AWLP A) : eq1 (awlpPure_AWLP (awlpProgram w)) w.
Proof.
  destruct (proj2_sig w) as [Hm [_ Hd]]. intro Q.
  change (angelic True (awlpProgram w) Q <-> getWPSub w Q).
  rewrite (disjunctive_repr _ Hm Hd Q). split.
  - intros [[a|] [Ho H]]; [ right; exists a; exact (conj Ho H) | left; exact Ho ].
  - intros [H | [a [Ho H]]].
    + exists None. exact (conj H I).
    + exists (Some a). exact (conj Ho H).
Qed.
