(** * Monad law proofs for [PureSPost] and [ProgSPost].

    [PureSPost A] is a forward predicate transformer (strongest
    postcondition style), bundled with a monotonicity condition.

    [ProgSPost S = stateT S (optionT PureSPost)] then inherits
    [MonadLawsE] via the generic [optionT] and [stateT] instances
    from [ProgFacts]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality ProofIrrelevance
  Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness Require Import
  Taxonomy.SPost
  Taxonomy.ProgFacts.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [PureSPost]                        *)
(* ================================================================= *)

Section PureSPostFacts.

  (** Equality of [sig] values from equality of their first projections,
      using proof irrelevance. *)
  Lemma sig_eq {A} {P : A -> Prop} (x y : sig P) :
    proj1_sig x = proj1_sig y -> x = y.
  Proof.
    destruct x as [xv xp], y as [yv yp]; simpl.
    intro Heq; subst. f_equal.
    apply proof_irrelevance.
  Qed.

  (** Two [PureSPost] values are equal when their postcondition
      predicates are pointwise logically equivalent. *)
  Lemma PureSPost_eq {A} (m1 m2 : PureSPost A) :
    (forall pre a,
       proj1_sig (proj1_sig m1 pre) a <->
       proj1_sig (proj1_sig m2 pre) a) ->
    m1 = m2.
  Proof.
    intro Heq.
    apply sig_eq. extensionality pre.
    apply sig_eq. extensionality a.
    apply propositional_extensionality. apply Heq.
  Qed.

  #[global]
  Instance Eq1_PureSPost : Eq1 PureSPost :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_PureSPost
    : @Eq1Equivalence PureSPost _ Eq1_PureSPost.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_PureSPost
    : @MonadLawsE PureSPost Eq1_PureSPost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x.
      unfold eq1, Eq1_PureSPost.
      apply PureSPost_eq. intros pre b. cbn.
      split.
      + intros [a0 Hb].
        assert (Ha : a0 = x /\ pre)
          by exact (proj2_sig (proj1_sig (f a0) _) b Hb).
        destruct Ha as [-> Hpre].
        exact (proj2_sig (f x) _ pre (fun H => proj2 H) b Hb).
      + intros Hb. exists x.
        exact (proj2_sig (f x) pre _ (fun H => conj eq_refl H) b Hb).
    - (* bind_ret_r *)
      intros A m.
      unfold eq1, Eq1_PureSPost.
      apply PureSPost_eq. intros pre a. cbn.
      split.
      + intros [v [Heq Hv]]. subst. exact Hv.
      + intros Ha. exists a. exact (conj eq_refl Ha).
    - (* bind_bind *)
      intros A B C m f g.
      unfold eq1, Eq1_PureSPost.
      apply PureSPost_eq. intros pre c. cbn.
      split.
      + intros [b0 Hb].
        pose proof (proj2_sig (proj1_sig (g b0) _) c Hb) as [a0 Ha0].
        exists a0, b0.
        exact (proj2_sig (g b0) _ _ (fun _ => Ha0) c Hb).
      + intros [a0 [b0 Hb]]. exists b0.
        exact (proj2_sig (g b0) _ _ (fun h => ex_intro _ a0 h) c Hb).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg.
      unfold eq1, Eq1_PureSPost in *.
      subst.
      assert (f = g) as ->
        by (apply functional_extensionality; exact Hfg).
      reflexivity.
  Qed.

End PureSPostFacts.

(* ================================================================= *)
(** ** [MonadLawsE] for [ProgSPost S]                                 *)
(* ================================================================= *)

Section ProgSPostFacts.

  Variable S : Type.

  (** The instance chains through:
        [Eq1_PureSPost]  (Leibniz eq)
      → [Eq1_optionT]    (eq on unwrapped PureSPost)
      → [Eq1_stateT]     (pointwise eq)

      and similarly for [MonadLawsE]. *)

  Definition Eq1__ProgSPost : Eq1 (ProgSPost S) :=
    Eq1_stateT S (optionT PureSPost).

  Definition MonadLawsE__ProgSPost
    : @MonadLawsE (ProgSPost S) _ (Monad__ProgSPost S) :=
    MonadLawsE_stateT S (optionT PureSPost).

End ProgSPostFacts.
