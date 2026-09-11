(** * Generic ASP/DSLP observations from an outcome kernel.

    An OUTCOME KERNEL for a monad [M] over states [S] is a family
    [kern : M A -> S -> option (A * S) -> Prop] whose [ret] and [bind]
    clauses mirror the kernels of the computation monads (see
    [Taxonomy/ComputationMonads/StExcNonDet.v] for the shape).  This file
    turns any such kernel into the arrow-derived SP observations of
    [SPostArrMonad]: the observations [obsASP]/[obsDSLP] (the demonic one
    derived from the angelic one via [asp_to_dslp], no second semantic
    proof), their relational and evaluator readings, the strict
    [ret]/[bind] equalities, and the Over/Under triples with their
    raw-spec equivalents.  Downstream effect files only need to build an
    [OutcomeKernel]. *)

From ITree Require Import Basics.Monad.
From Coq Require Import Morphisms_Prop.
From Incorrectness.Taxonomy.Arrows Require Export SPostArrMonad.
Import MonadNotation.
Open Scope monad_scope.

(** ** The outcome kernel record *)

Record OutcomeKernel (S : Type) (M : Type -> Type) `{MM : Monad M} := {
  kern : forall {A}, M A -> S -> option (A * S) -> Prop;
  kern_ret : forall {A} (a : A) (s : S) (r : option (A * S)),
    kern (ret a) s r <-> r = Some (a, s);
  kern_bind : forall {A B} (m : M A) (k : A -> M B) (s : S) (r : option (B * S)),
    kern (m >>= k) s r <->
    exists oa, kern m s oa /\
      match oa with
      | Some (a, s') => kern (k a) s' r
      | None => r = None
      end
}.
Arguments kern {S M MM} K {A} m s r : rename.
Arguments kern_ret {S M MM} K {A} a s r : rename.
Arguments kern_bind {S M MM} K {A B} m k s r : rename.

(** ** The generic observation adapter *)

Section SPObs.
  Variable S : Type.
  Variable M : Type -> Type.
  Context {MM : Monad M}.
  Variable K : OutcomeKernel S M.

  Definition obsASP {A} (m : M A) : ASPostArr S A :=
    relASP (fun us r => kern K m (snd us) r).

  Definition obsDSLP {A} (m : M A) : DSLPostArr S A :=
    asp_to_dslp (obsASP m).

  Lemma ASP_rel_obsASP {A} (m : M A) us r :
    ASP_rel (obsASP m) us r <-> kern K m (snd us) r.
  Proof.
    rewrite (ASP_rel_relASP (fun us r => kern K m (snd us) r) us r).
    reflexivity.
  Qed.

  Lemma DSLP_rel_obsDSLP {A} (m : M A) us r :
    DSLP_rel (obsDSLP m) us r <-> kern K m (snd us) r.
  Proof.
    unfold obsDSLP. rewrite DSLP_rel_asp_to_dslp. apply ASP_rel_obsASP.
  Qed.

  Lemma runASP_obsASP {A} (m : M A) (pre : S -> Prop) r :
    runASP (obsASP m) pre r <-> exists s, pre s /\ kern K m s r.
  Proof.
    rewrite runASP_rel. setoid_rewrite ASP_rel_obsASP. reflexivity.
  Qed.

  Lemma runDSLP_obsDSLP {A} (m : M A) (pre : S -> Prop) r :
    runDSLP (obsDSLP m) pre r <-> forall s, kern K m s r -> pre s.
  Proof.
    rewrite runDSLP_rel. setoid_rewrite DSLP_rel_obsDSLP. reflexivity.
  Qed.

  (** ** Morphism laws *)

  Theorem obsASP_ret {A} (a : A) :
    obsASP (ret a) = @ret _ (Monad_ASPostArr S) A a.
  Proof.
    apply PureASPostArr_eq. intros Q r.
    assert (HL : getASP (obsASP (ret a)) Q r
      <-> exists s, Q (tt, s) /\ r = Some (a, s)).
    { unfold obsASP. rewrite getASP_relASP. split.
      - intros [us [HQ Hr]]. destruct us as [[] s]. exists s.
        split; [exact HQ | exact (proj1 (kern_ret K a s r) Hr)].
      - intros [s [HQ Hr]]. exists (tt, s).
        split; [exact HQ | exact (proj2 (kern_ret K a s r) Hr)]. }
    assert (HR : getASP (@ret _ (Monad_ASPostArr S) A a) Q r
      <-> exists s, Q (tt, s) /\ r = Some (a, s)).
    { rewrite (ASP_normal_form (@ret _ (Monad_ASPostArr S) A a) Q r).
      split.
      - intros [us [HQ Hr]]. destruct us as [[] s]. exists s.
        split; [exact HQ |].
        apply (proj1 (ASP_rel_ret a tt s r)) in Hr. symmetry; exact Hr.
      - intros [s [HQ Hr]]. exists (tt, s).
        split; [exact HQ |].
        apply (proj2 (ASP_rel_ret a tt s r)). symmetry; exact Hr. }
    rewrite HL, HR. reflexivity.
  Qed.

  Theorem obsASP_bind {A B} (m : M A) (k : A -> M B) :
    obsASP (m >>= k) =
    @bind _ (Monad_ASPostArr S) A B (obsASP m) (fun a => obsASP (k a)).
  Proof.
    apply PureASPostArr_eq. intros Q r.
    rewrite (ASP_normal_form (obsASP (m >>= k)) Q r).
    rewrite (ASP_normal_form (@bind _ (Monad_ASPostArr S) A B (obsASP m)
        (fun a => obsASP (k a))) Q r).
    split.
    - intros [us [HQ Hr]]. destruct us as [[] s].
      apply (proj1 (ASP_rel_obsASP (m >>= k) (tt, s) r)) in Hr.
      apply (proj1 (kern_bind K m k s r)) in Hr.
      destruct Hr as [oa [Hm Hk]].
      exists (tt, s). split; [exact HQ |].
      apply (proj2 (ASP_rel_bind (obsASP m) (fun a => obsASP (k a)) s r)).
      exists oa. split.
      + apply (proj2 (ASP_rel_obsASP m (tt, s) oa)). exact Hm.
      + destruct oa as [[a t]|].
        * apply (proj2 (ASP_rel_obsASP (k a) (tt, t) r)). exact Hk.
        * exact Hk.
    - intros [us [HQ Hb]]. destruct us as [[] s].
      apply (proj1 (ASP_rel_bind (obsASP m) (fun a => obsASP (k a)) s r)) in Hb.
      destruct Hb as [oa [Hm Hk]].
      exists (tt, s). split; [exact HQ |].
      apply (proj2 (ASP_rel_obsASP (m >>= k) (tt, s) r)).
      apply (proj2 (kern_bind K m k s r)).
      exists oa. split.
      + apply (proj1 (ASP_rel_obsASP m (tt, s) oa)). exact Hm.
      + destruct oa as [[a t]|].
        * apply (proj1 (ASP_rel_obsASP (k a) (tt, t) r)). exact Hk.
        * exact Hk.
  Qed.

  Theorem obsDSLP_ret {A} (a : A) :
    obsDSLP (ret a) = @ret _ (Monad_DSLPostArr S) A a.
  Proof.
    unfold obsDSLP. rewrite obsASP_ret. apply asp_to_dslp_ret.
  Qed.

  Theorem obsDSLP_bind {A B} (m : M A) (k : A -> M B) :
    obsDSLP (m >>= k) =
    @bind _ (Monad_DSLPostArr S) A B (obsDSLP m) (fun a => obsDSLP (k a)).
  Proof.
    unfold obsDSLP. rewrite obsASP_bind.
    rewrite <- (asp_to_dslp_bind (obsASP m) (fun a => obsASP (k a))).
    reflexivity.
  Qed.

  (** ** Triples *)

  Inductive approxKind := Under | Over.

  Definition pp2_over {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : (S -> Prop) -> option (A * S) -> Prop :=
    fun p r => (forall s, p s -> pre s) -> post r.

  Definition pp2_under {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : (S -> Prop) -> option (A * S) -> Prop :=
    fun p r => (forall s, pre s -> p s) /\ post r.

  Definition tripleASP {A} (m : M A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over => forall r, (exists s, pre s /\ kern K m s r) -> post r
    | Under => forall r, post r -> exists s, pre s /\ kern K m s r
    end.

  Definition tripleASPspec {A} (m : M A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over => forall p r, runASP (obsASP m) p r -> pp2_over pre post p r
    | Under => forall p r, pp2_under pre post p r -> runASP (obsASP m) p r
    end.

  Theorem tripleASPDefEq {A} (m : M A) kind pre post :
    tripleASP m kind pre post <-> tripleASPspec m kind pre post.
  Proof.
    unfold tripleASP, tripleASPspec, pp2_over, pp2_under.
    destruct kind; split.
    - intros H p r [Hsub Hpost].
      apply (proj2 (runASP_obsASP m p r)).
      destruct (H r Hpost) as [s [Hpre Hreach]].
      exists s. split; [exact (Hsub s Hpre) | exact Hreach].
    - intros H r Hpost.
      apply (proj1 (runASP_obsASP m pre r)).
      exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - intros H p r Hrun Hsub. rewrite runASP_obsASP in Hrun.
      destruct Hrun as [s [Hp Hreach]].
      apply (H r). exists s. split; [exact (Hsub s Hp) | exact Hreach].
    - intros H r [s [Hpre Hreach]].
      apply (H pre r).
      + apply (proj2 (runASP_obsASP m pre r)).
        exists s. split; [exact Hpre | exact Hreach].
      + exact (fun s Hs => Hs).
  Qed.

  Definition tripleDSL {A} (m : M A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over => forall r, (forall s, kern K m s r -> pre s) -> post r
    | Under => forall r, post r -> forall s, kern K m s r -> pre s
    end.

  Definition tripleDSLspec {A} (m : M A) (kind : approxKind)
      (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over => forall p r, runDSLP (obsDSLP m) p r -> pp2_over pre post p r
    | Under => forall p r, pp2_under pre post p r -> runDSLP (obsDSLP m) p r
    end.

  Theorem tripleDSLDefEq {A} (m : M A) kind pre post :
    tripleDSL m kind pre post <-> tripleDSLspec m kind pre post.
  Proof.
    unfold tripleDSL, tripleDSLspec, pp2_over, pp2_under.
    destruct kind; split.
    - intros H p r [Hsub Hpost].
      apply (proj2 (runDSLP_obsDSLP m p r)).
      intros s Hout. exact (Hsub s (H r Hpost s Hout)).
    - intros H r Hpost s Hout.
      apply (proj1 (runDSLP_obsDSLP m pre r));
        [exact (H pre r (conj (fun s Hs => Hs) Hpost)) | exact Hout].
    - intros H p r Hrun Hsub. apply (H r).
      intros s Hout.
      exact (Hsub s (proj1 (runDSLP_obsDSLP m p r) Hrun s Hout)).
    - intros H r Hout.
      apply (H pre r).
      + apply (proj2 (runDSLP_obsDSLP m pre r)).
        exact Hout.
      + exact (fun s Hs => Hs).
  Qed.

End SPObs.

(** ** Downstream-facing implicit arguments *)

Arguments obsASP {S M MM} K {A} m.
Arguments obsDSLP {S M MM} K {A} m.
Arguments ASP_rel_obsASP {S M MM} K {A} m us r.
Arguments DSLP_rel_obsDSLP {S M MM} K {A} m us r.
Arguments runASP_obsASP {S M MM} K {A} m pre r.
Arguments runDSLP_obsDSLP {S M MM} K {A} m pre r.
Arguments obsASP_ret {S M MM} K {A} a.
Arguments obsASP_bind {S M MM} K {A B} m k.
Arguments obsDSLP_ret {S M MM} K {A} a.
Arguments obsDSLP_bind {S M MM} K {A B} m k.
Arguments pp2_over {S A} pre post.
Arguments pp2_under {S A} pre post.
Arguments tripleASP {S M MM} K {A} m kind pre post.
Arguments tripleASPspec {S M MM} K {A} m kind pre post.
Arguments tripleASPDefEq {S M MM} K {A} m kind pre post.
Arguments tripleDSL {S M MM} K {A} m kind pre post.
Arguments tripleDSLspec {S M MM} K {A} m kind pre post.
Arguments tripleDSLDefEq {S M MM} K {A} m kind pre post.
