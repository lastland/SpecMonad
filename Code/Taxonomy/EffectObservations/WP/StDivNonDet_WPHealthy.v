(** * The [stdivnd] WP observations, valued in the four healthy monads

    [WP/StDivNonDet_WSt.v] defines [obsDWP] / [obsDWLP] / [obsAWP] / [obsAWLP]
    into [WSt S = stateT S WPure], whose only carrier condition is
    monotonicity.  This file refines them to land in the four monads of
    [BaseSpecMonads/WPHealthyMonads.v], which are cut out by the SAME four
    pairings as the SP monads.

    Two levels of sharing are in play.

    - **One observation, not four.**  All four factor as

        [obsGen q k m s post  =  Q oa in reach, ext k post oa]

      with [q] choosing the quantifier ([Dem] = [forall], [Ang] = [exists])
      and [k] choosing how the DIVERGENT outcome is scored ([Total] = [False],
      [Liberal] = [True]).  The two axes are independent, so there is one
      definition with two parameters rather than four definitions.
      [obsGen_DWP] … [obsGen_AWLP] identify it with the four originals.

    - **Four healthiness proofs, not eight.**  Each condition depends on only
      ONE of the two axes: the quantifier fixes conjunctive vs disjunctive, the
      scoring fixes strict vs terminating.  So [obsGen_conjunctive] is proved
      once for both [k], [obsGen_strict] once for both [q], and so on.

    Non-emptiness of the outcome set is needed for exactly two of the four
    laws — [Strict] at [Dem] and [Terminating] at [Ang] — which is what the
    [stdivndNE] carrier supplies. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  Healthiness WPureMonad WPHealthyMonads.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivNonDet_WSt.
Import TermSliceObsWP.

Module HealthyObsWP.

Section HealthyObs.
  Variable S : Type.

  (** The two axes. *)
  Inductive mode  := Ang | Dem.
  Inductive scope := Total | Liberal.

  Definition reach {A} (m : stdivndNE S A) (s : S) (oa : option (A * S)) : Prop :=
    unOptionT (runStateT (getNE m) s) oa.

  (** The liberal/total axis is a modification of the POSTCONDITION: it only
      says how the divergent outcome is scored. *)
  Definition ext {A} (k : scope) (post : A * S -> Prop) (oa : option (A * S)) : Prop :=
    match oa with
    | Some r => post r
    | None   => match k with Total => False | Liberal => True end
    end.

  Definition obsGen {A} (q : mode) (k : scope)
    (m : stdivndNE S A) (s : S) : PT (A * S) :=
    fun post =>
      match q with
      | Dem => forall oa, reach m s oa -> ext k post oa
      | Ang => exists oa, reach m s oa /\ ext k post oa
      end.

  (* ---------------- the four originals, recovered ---------------- *)

  Theorem obsGen_DWP {A} (m : stdivndNE S A) s post :
    obsGen Dem Total m s post <-> runStateT (obsDWP m) s post.
  Proof. symmetry. exact (obsDWP_unfold m s post). Qed.

  Theorem obsGen_DWLP {A} (m : stdivndNE S A) s post :
    obsGen Dem Liberal m s post <-> runStateT (obsDWLP m) s post.
  Proof. symmetry. exact (obsDWLP_unfold m s post). Qed.

  Theorem obsGen_AWP {A} (m : stdivndNE S A) s post :
    obsGen Ang Total m s post <-> runStateT (obsAWP m) s post.
  Proof.
    rewrite obsAWP_unfold. split.
    - intros [[r|] [Ho Hp]]; [ exists r; exact (conj Ho Hp) | destruct Hp ].
    - intros [r [Ho Hp]]. exists (Some r). exact (conj Ho Hp).
  Qed.

  Theorem obsGen_AWLP {A} (m : stdivndNE S A) s post :
    obsGen Ang Liberal m s post <-> runStateT (obsAWLP m) s post.
  Proof.
    rewrite obsAWLP_unfold. split.
    - intros [[r|] [Ho Hp]];
        [ left; exists r; exact (conj Ho Hp) | right; exact Ho ].
    - intros [[r [Ho Hp]] | Hd];
        [ exists (Some r); exact (conj Ho Hp) | exists None; exact (conj Hd I) ].
  Qed.

  (* ---------------- healthiness, once per axis ---------------- *)

  (** The QUANTIFIER decides conjunctive vs disjunctive — for either scoring. *)

  Theorem obsGen_conjunctive {A} (k : scope) (m : stdivndNE S A) s :
    Conjunctive (obsGen Dem k m s).
  Proof.
    intros K [k0] p. cbn. split.
    - intros H j oa Ho. specialize (H oa Ho).
      destruct oa as [r|]; [ exact (H j) | destruct k; [ destruct H | exact I ] ].
    - intros H oa Ho. destruct oa as [r|].
      + intro j. exact (H j (Some r) Ho).
      + destruct k; [ exact (H k0 None Ho) | exact I ].
  Qed.

  Theorem obsGen_disjunctive {A} (k : scope) (m : stdivndNE S A) s :
    Disjunctive (obsGen Ang k m s).
  Proof.
    intros K [k0] p. cbn. split.
    - intros [oa [Ho Hp]]. destruct oa as [r|].
      + destruct Hp as [j Hj]. exists j, (Some r). exact (conj Ho Hj).
      + destruct k; [ destruct Hp | exists k0, None; exact (conj Ho I) ].
    - intros [j [oa [Ho Hp]]]. exists oa. split; [ exact Ho |].
      destruct oa as [r|]; [ exists j; exact Hp | exact Hp ].
  Qed.

  (** The SCORING decides strict vs terminating — for either quantifier.
      Each needs non-emptiness in exactly one of the two cases. *)

  Theorem obsGen_strict {A} (q : mode) (m : stdivndNE S A) s :
    Strict (obsGen q Total m s).
  Proof.
    destruct q; cbn; intro H.
    - destruct H as [oa [Ho Hp]]. destruct oa as [r|]; exact Hp.
    - destruct (getNE_nonEmpty S m s) as [oa Ho].
      specialize (H oa Ho). destruct oa as [r|]; exact H.
  Qed.

  Theorem obsGen_terminating {A} (q : mode) (m : stdivndNE S A) s :
    Terminating (obsGen q Liberal m s).
  Proof.
    destruct q; cbn.
    - destruct (getNE_nonEmpty S m s) as [oa Ho].
      exists oa. split; [ exact Ho | destruct oa as [r|]; exact I ].
    - intros oa _. destruct oa as [r|]; exact I.
  Qed.

  (* ---------------- the four pairings, assembled ---------------- *)

  Theorem obsGen_AngelicTotal {A} (m : stdivndNE S A) s :
    AngelicTotal (obsGen Ang Total m s).
  Proof. exact (conj (obsGen_strict Ang m s) (obsGen_disjunctive Total m s)). Qed.

  Theorem obsGen_DemonicLiberal {A} (m : stdivndNE S A) s :
    DemonicLiberal (obsGen Dem Liberal m s).
  Proof. exact (conj (obsGen_terminating Dem m s) (obsGen_conjunctive Liberal m s)). Qed.

  Theorem obsGen_DemonicTotal {A} (m : stdivndNE S A) s :
    DemonicTotal (obsGen Dem Total m s).
  Proof. exact (conj (obsGen_strict Dem m s) (obsGen_conjunctive Total m s)). Qed.

  Theorem obsGen_AngelicLiberal {A} (m : stdivndNE S A) s :
    AngelicLiberal (obsGen Ang Liberal m s).
  Proof. exact (conj (obsGen_terminating Ang m s) (obsGen_disjunctive Liberal m s)). Qed.

  (* ---------------- monad-valued observations ---------------- *)

  (** Each is [obsGen] at its corner, packaged with the matching pairing.
      Monotonicity comes from the pairing, so nothing extra is proved. *)

  Definition obsAWPh {A} (m : stdivndNE S A) : stateT S AWP.W A :=
    mkStateT (fun s =>
      exist _ (mkWPure (obsGen Ang Total m s)
                 (AngelicTotal_mono _ (obsGen_AngelicTotal m s)))
              (obsGen_AngelicTotal m s)).

  Definition obsDWLPh {A} (m : stdivndNE S A) : stateT S DWLP.W A :=
    mkStateT (fun s =>
      exist _ (mkWPure (obsGen Dem Liberal m s)
                 (DemonicLiberal_mono _ (obsGen_DemonicLiberal m s)))
              (obsGen_DemonicLiberal m s)).

  Definition obsDWPh {A} (m : stdivndNE S A) : stateT S DWP.W A :=
    mkStateT (fun s =>
      exist _ (mkWPure (obsGen Dem Total m s)
                 (DemonicTotal_mono _ (obsGen_DemonicTotal m s)))
              (obsGen_DemonicTotal m s)).

  Definition obsAWLPh {A} (m : stdivndNE S A) : stateT S AWLP.W A :=
    mkStateT (fun s =>
      exist _ (mkWPure (obsGen Ang Liberal m s)
                 (AngelicLiberal_mono _ (obsGen_AngelicLiberal m s)))
              (obsGen_AngelicLiberal m s)).

  (** Each refines the corresponding observation of [StDivNonDet_WSt.v]:
      same transformer, stronger carrier. *)

  Theorem obsAWPh_run {A} (m : stdivndNE S A) s post :
    AWP.runW (runStateT (obsAWPh m) s) post <-> runStateT (obsAWP m) s post.
  Proof. exact (obsGen_AWP m s post). Qed.

  Theorem obsDWLPh_run {A} (m : stdivndNE S A) s post :
    DWLP.runW (runStateT (obsDWLPh m) s) post <-> runStateT (obsDWLP m) s post.
  Proof. exact (obsGen_DWLP m s post). Qed.

  Theorem obsDWPh_run {A} (m : stdivndNE S A) s post :
    DWP.runW (runStateT (obsDWPh m) s) post <-> runStateT (obsDWP m) s post.
  Proof. exact (obsGen_DWP m s post). Qed.

  Theorem obsAWLPh_run {A} (m : stdivndNE S A) s post :
    AWLP.runW (runStateT (obsAWLPh m) s) post <-> runStateT (obsAWLP m) s post.
  Proof. exact (obsGen_AWLP m s post). Qed.

End HealthyObs.

Arguments obsAWPh  {_} {_}.
Arguments obsDWLPh {_} {_}.
Arguments obsDWPh  {_} {_}.
Arguments obsAWLPh {_} {_}.

End HealthyObsWP.
