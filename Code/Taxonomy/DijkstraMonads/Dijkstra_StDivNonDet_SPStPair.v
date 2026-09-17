(** * Dijkstra monads of the paired SP observations of [stdivnd]

    [Ddsp] and [Daslp], DM4All's [Dtheta] over [obsDSPPair] / [obsASLPPair]
    from [EffectObservations/SP/StDivNonDet_SPStPair.v], in the [Under]
    direction.  The pair orders are preserved by [bind]
    ([StDSPPair.ordDSPPair_bind], [StASLPPair.ordASLPPair_bind]), which is
    what the single [DSPSt] / [ASLPSt] orders lack. *)

From Coq Require Import RelationClasses Morphisms.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad
  BaseGaloisConnections NewGaloisConnections DSPMonadPair ASLPMonadPair.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPSt StDivNonDet_SPStPair.

Import MonadNotation.
Open Scope monad_scope.

Import StTrans StASP StDSLP StDSP StASLP StSP.
Import TermSliceObs.

Section PairDijkstra.
  Variable S : Type.
  #[local] Obligation Tactic := (intros; cbn beta).


  Definition Ddsp {A} (w : StDSPPair.DSPPair S A) : Type :=
    { m : stdivnd S A | StDSPPair.ordDSPPair w (obsDSPPair m) }.

  #[program] Definition Ddsp_ret {A} (a : A) : Ddsp (StDSPPair.retDSPPair a) :=
    @ret (stdivnd S) _ A a.
  Next Obligation. apply (obsDSPPair_ret S). Qed.

  #[program] Definition Ddsp_bind {A B} {w : StDSPPair.DSPPair S A}
    {wf : A -> StDSPPair.DSPPair S B}
    (m : Ddsp w) (f : forall a, Ddsp (wf a)) : Ddsp (StDSPPair.bindDSPPair w wf) :=
    @bind (stdivnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply (obsDSPPair_bind S) ].
    apply StDSPPair.ordDSPPair_bind;
      [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition Ddsp_wkn {A} {w w' : StDSPPair.DSPPair S A}
    (Hle : StDSPPair.ordDSPPair w' w) (m : Ddsp w) : Ddsp w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition Ddsp_lift {A} (m : stdivnd S A) : Ddsp (obsDSPPair m) := m.
  Next Obligation. reflexivity. Qed.

  Definition Daslp {A} (w : StASLPPair.ASLPPair S A) : Type :=
    { m : stdivnd S A | StASLPPair.ordASLPPair w (obsASLPPair m) }.

  #[program] Definition Daslp_ret {A} (a : A) : Daslp (StASLPPair.retASLPPair a) :=
    @ret (stdivnd S) _ A a.
  Next Obligation. apply (obsASLPPair_ret S). Qed.

  #[program] Definition Daslp_bind {A B} {w : StASLPPair.ASLPPair S A}
    {wf : A -> StASLPPair.ASLPPair S B}
    (m : Daslp w) (f : forall a, Daslp (wf a))
    : Daslp (StASLPPair.bindASLPPair w wf) :=
    @bind (stdivnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply (obsASLPPair_bind S) ].
    apply StASLPPair.ordASLPPair_bind;
      [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition Daslp_wkn {A} {w w' : StASLPPair.ASLPPair S A}
    (Hle : StASLPPair.ordASLPPair w' w) (m : Daslp w) : Daslp w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition Daslp_lift {A} (m : stdivnd S A) : Daslp (obsASLPPair m) := m.
  Next Obligation. reflexivity. Qed.

End PairDijkstra.

Arguments Ddsp {_} {_}.
Arguments Daslp {_} {_}.

(* ================================================================= *)
(** ** The examples, as Dijkstra typings                             *)
(* ================================================================= *)

Definition incrD_Ddsp
  : Ddsp (StDSPPair.aspOfRel W_incr, pp2dslp_under pre0 post1) :=
  exist _ incrD (conj incrD_asp incrD_dslp).

Definition twoD_Daslp
  : Daslp (StASLPPair.aspOfRel W_incr, pp2dslp_under pre0 post9) :=
  exist _ twoD (conj twoD_asp twoD_dslp).
