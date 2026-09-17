(** * Effect observations of [stdivndNE] into the four healthy WP monads

    Four monad morphisms, one per monad of [BaseSpecMonads/WPHealthyMonads.v]:

      [obsAWP]   : stdivndNE S -> stateT S AWP.W    angelic total
      [obsDWLP]  : stdivndNE S -> stateT S DWLP.W   demonic liberal
      [obsDWP]   : stdivndNE S -> stateT S DWP.W    demonic total
      [obsAWLP]  : stdivndNE S -> stateT S AWLP.W   angelic liberal

    Postconditions range over [A * S], so divergence is visible to the
    observation but not to the postcondition: the total observations reject a
    divergent outcome, the liberal ones accept it.

    The healthiness condition of each target is an obligation of the
    definition.  Non-emptiness of the outcome set is needed for exactly two of
    the eight components — [Strict] for [obsDWP] and [Terminating] for
    [obsAWLP] — which is why the source is [stdivndNE] rather than [stdivnd].

    Each observation has the same transformer as its counterpart in
    [WP/StDivNonDet_WSt.v] ([obsAWP_run] &c.); what is new here is the
    healthier carrier, and that each observation is a monad morphism into it. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  Healthiness WPureMonad WPHealthyMonads.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivNonDet_WSt.

Import MonadNotation.
Open Scope monad_scope.

Module HealthyObsWP.

Section HealthyObs.
  Variable S : Type.

  #[local] Existing Instance Monad_stateT.

  (* ---------------- the four observations ---------------- *)

  #[program] Definition obsAWP {A} (m : stdivndNE S A) : stateT S AWP.W A :=
    mkStateT (fun s =>
      (fun (post : A * S -> Prop) =>
         exists r, unOptionT (runStateT (getNE m) s) (Some r) /\ post r)).
  Next Obligation.
    intros p q Hpq [r [Ho Hp]]. exists r. exact (conj Ho (Hpq r Hp)).
  Qed.
  Next Obligation.
    split.
    - intros [r [_ []]].
    - intros K [k0] p. cbn. split.
      + intros [r [Ho [j Hj]]]. exists j, r. exact (conj Ho Hj).
      + intros [j [r [Ho Hj]]]. exists r. split; [ exact Ho | exists j; exact Hj ].
  Qed.

  #[program] Definition obsDWLP {A} (m : stdivndNE S A) : stateT S DWLP.W A :=
    mkStateT (fun s =>
      (fun (post : A * S -> Prop) =>
         forall oa, unOptionT (runStateT (getNE m) s) oa ->
           match oa with Some r => post r | None => True end)).
  Next Obligation.
    intros p q Hpq H oa Ho. specialize (H oa Ho).
    destruct oa as [r|]; [ exact (Hpq r H) | exact I ].
  Qed.
  Next Obligation.
    split.
    - intros [r|] _; exact I.
    - intros K [k0] p. cbn. split.
      + intros H j oa Ho. specialize (H oa Ho).
        destruct oa as [r|]; [ exact (H j) | exact I ].
      + intros H oa Ho. destruct oa as [r|]; [ intro j; exact (H j _ Ho) | exact I ].
  Qed.

  #[program] Definition obsDWP {A} (m : stdivndNE S A) : stateT S DWP.W A :=
    mkStateT (fun s =>
      (fun (post : A * S -> Prop) =>
         forall oa, unOptionT (runStateT (getNE m) s) oa ->
           match oa with Some r => post r | None => False end)).
  Next Obligation.
    intros p q Hpq H oa Ho. specialize (H oa Ho).
    destruct oa as [r|]; [ exact (Hpq r H) | exact H ].
  Qed.
  Next Obligation.
    split.
    - intro H. destruct (getNE_nonEmpty S m s) as [oa Ho].
      specialize (H oa Ho). destruct oa; exact H.
    - intros K [k0] p. cbn. split.
      + intros H j oa Ho. specialize (H oa Ho).
        destruct oa as [r|]; [ exact (H j) | destruct H ].
      + intros H oa Ho. destruct oa as [r|];
          [ intro j; exact (H j _ Ho) | exact (H k0 None Ho) ].
  Qed.

  #[program] Definition obsAWLP {A} (m : stdivndNE S A) : stateT S AWLP.W A :=
    mkStateT (fun s =>
      (fun (post : A * S -> Prop) =>
         (exists r, unOptionT (runStateT (getNE m) s) (Some r) /\ post r)
         \/ unOptionT (runStateT (getNE m) s) None)).
  Next Obligation.
    intros p q Hpq [[r [Ho Hp]] | Hd];
      [ left; exists r; exact (conj Ho (Hpq r Hp)) | right; exact Hd ].
  Qed.
  Next Obligation.
    split.
    - destruct (getNE_nonEmpty S m s) as [[r|] Ho];
        [ left; exists r; exact (conj Ho I) | right; exact Ho ].
    - intros K [k0] p. cbn. split.
      + intros [[r [Ho [j Hj]]] | Hd];
          [ exists j; left; exists r; exact (conj Ho Hj)
          | exists k0; right; exact Hd ].
      + intros [j [[r [Ho Hj]] | Hd]];
          [ left; exists r; split; [ exact Ho | exists j; exact Hj ]
          | right; exact Hd ].
  Qed.

  (* ---------------- each is a monad morphism ---------------- *)

  Theorem obsAWP_ret {A} (a : A) : eq1 (obsAWP (ret a : stdivndNE S A)) (ret a).
  Proof.
    intros s p. cbn. split.
    - intros [r [Hr Hp]]. assert (E : r = (a, s)) by congruence. subst r. exact Hp.
    - intro Hp. exists (a, s). split; [ reflexivity | exact Hp ].
  Qed.

  Theorem obsAWP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsAWP (x >>= f)) (obsAWP x >>= (fun a => obsAWP (f a))).
  Proof.
    intros s p. cbn. split.
    - intros [rb [[[[a s']|] [Hx Hk]] Hp]]; [| discriminate Hk ].
      exists (a, s'). split; [ exact Hx |]. exists rb. exact (conj Hk Hp).
    - intros [[a s'] [Hx [rb [Hk Hp]]]].
      exists rb. split; [| exact Hp ]. exists (Some (a, s')). exact (conj Hx Hk).
  Qed.

  Theorem obsDWLP_ret {A} (a : A) : eq1 (obsDWLP (ret a : stdivndNE S A)) (ret a).
  Proof.
    intros s p. cbn. split.
    - intro H. exact (H (Some (a, s)) eq_refl).
    - intros Hp oa Heq. assert (E : oa = Some (a, s)) by congruence. subst oa. exact Hp.
  Qed.

  Theorem obsDWLP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsDWLP (x >>= f)) (obsDWLP x >>= (fun a => obsDWLP (f a))).
  Proof.
    intros s p. cbn. split.
    - intros H [[a s']|] Hx; [| exact I ].
      intros ob Hk. exact (H ob (ex_intro _ (Some (a, s')) (conj Hx Hk))).
    - intros H ob [[[a s']|] [Hx Hk]].
      + exact (H (Some (a, s')) Hx ob Hk).
      + assert (E : ob = None) by congruence. subst ob. exact I.
  Qed.

  Theorem obsDWP_ret {A} (a : A) : eq1 (obsDWP (ret a : stdivndNE S A)) (ret a).
  Proof.
    intros s p. cbn. split.
    - intro H. exact (H (Some (a, s)) eq_refl).
    - intros Hp oa Heq. assert (E : oa = Some (a, s)) by congruence. subst oa. exact Hp.
  Qed.

  Theorem obsDWP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsDWP (x >>= f)) (obsDWP x >>= (fun a => obsDWP (f a))).
  Proof.
    intros s p. cbn. split.
    - intros H [[a s']|] Hx.
      + intros ob Hk. exact (H ob (ex_intro _ (Some (a, s')) (conj Hx Hk))).
      + exact (H None (ex_intro _ None (conj Hx eq_refl))).
    - intros H ob [[[a s']|] [Hx Hk]].
      + exact (H (Some (a, s')) Hx ob Hk).
      + destruct (H None Hx).
  Qed.

  Theorem obsAWLP_ret {A} (a : A) : eq1 (obsAWLP (ret a : stdivndNE S A)) (ret a).
  Proof.
    intros s p. cbn. split.
    - intros [[r [Hr Hp]] | Hd]; [| discriminate Hd ].
      assert (E : r = (a, s)) by congruence. subst r. exact Hp.
    - intro Hp. left. exists (a, s). split; [ reflexivity | exact Hp ].
  Qed.

  Theorem obsAWLP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsAWLP (x >>= f)) (obsAWLP x >>= (fun a => obsAWLP (f a))).
  Proof.
    intros s p. cbn. split.
    - intros [[rb [[[[a s']|] [Hx Hk]] Hp]] | [[[a s']|] [Hx Hk]]].
      + left. exists (a, s'). split; [ exact Hx |]. left. exists rb. exact (conj Hk Hp).
      + discriminate Hk.
      + left. exists (a, s'). split; [ exact Hx |]. right. exact Hk.
      + right. exact Hx.
    - intros [[[a s'] [Hx [[rb [Hk Hp]] | Hd]]] | Hd].
      + left. exists rb. split; [| exact Hp ]. exists (Some (a, s')). exact (conj Hx Hk).
      + right. exists (Some (a, s')). exact (conj Hx Hd).
      + right. exists None. exact (conj Hd eq_refl).
  Qed.

  (* ---------------- same transformers as [StDivNonDet_WSt.v] ---------------- *)

  Theorem obsAWP_run {A} (m : stdivndNE S A) s post :
    AWP.runW (runStateT (obsAWP m) s) post
    <-> runStateT (TermSliceObsWP.obsAWP m) s post.
  Proof. symmetry. exact (TermSliceObsWP.obsAWP_unfold m s post). Qed.

  Theorem obsDWLP_run {A} (m : stdivndNE S A) s post :
    DWLP.runW (runStateT (obsDWLP m) s) post
    <-> runStateT (TermSliceObsWP.obsDWLP m) s post.
  Proof.
    rewrite TermSliceObsWP.obsDWLP_unfold. cbn.
    split; intros H oa Ho; specialize (H oa Ho); destruct oa; exact H.
  Qed.

  Theorem obsDWP_run {A} (m : stdivndNE S A) s post :
    DWP.runW (runStateT (obsDWP m) s) post
    <-> runStateT (TermSliceObsWP.obsDWP m) s post.
  Proof.
    rewrite TermSliceObsWP.obsDWP_unfold. cbn.
    split; intros H oa Ho; specialize (H oa Ho); destruct oa; exact H.
  Qed.

  Theorem obsAWLP_run {A} (m : stdivndNE S A) s post :
    AWLP.runW (runStateT (obsAWLP m) s) post
    <-> runStateT (TermSliceObsWP.obsAWLP m) s post.
  Proof. symmetry. exact (TermSliceObsWP.obsAWLP_unfold m s post). Qed.

End HealthyObs.

Arguments obsAWP  {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsDWP  {_} {_}.
Arguments obsAWLP {_} {_}.

End HealthyObsWP.
