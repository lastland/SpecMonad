(** * The four SP observations of [stdivnd] into the arrow SP monads.

    [StDivNonDet_SPSt.v] observes [stdivnd] into the [OldMonads/] carriers.
    This file observes the same computations into the arrow presentation of
    [BaseSpecMonads/] -- [ASPSt], [DSLPSt], [DSPSt], [ASLPSt] -- on the
    terminating slice [A * S]: each observation is one reading of the
    outcomes [m] reaches from each start state.  It is what the obstruction
    results ([ASPUnderObstructions.v], [DSPASLPObstructions.v]) and the
    graded and lax structures ([Dijkstra_StDivNonDet_ASPUnder.v],
    [Dijkstra_StDivNonDet_ASPUnderLax.v]) are stated against. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.

Import MonadNotation.
Open Scope monad_scope.

Section Observations.
  Variable S : Type.

  (** ** Outcomes of [ret] and [bind] on the terminating slice *)

  Lemma outcomes_ret {A} (a : A) (s : S) (r : A * S) :
    unOptionT (runStateT (ret a : stdivnd S A) s) (Some r) <-> r = (a, s).
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma outcomes_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) s (r : B * S) :
    unOptionT (runStateT (x >>= f) s) (Some r)
    <-> (exists a s', unOptionT (runStateT x s) (Some (a, s'))
                      /\ unOptionT (runStateT (f a) s') (Some r)).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. destruct oy as [[a s']|]; cbn in *.
      + exists a, s'. split; [ exact H1 | exact H2 ].
      + congruence.
    - intros [a [s' [H1 H2]]]. exists (Some (a, s')).
      split; [ exact H1 | exact H2 ].
  Qed.

  (** ** The four observations *)

  Definition obsASP {A} (m : stdivnd S A) : ASPSt S A :=
    aspOfRelSt (fun s r => unOptionT (runStateT m s) (Some r)).
  Definition obsDSLP {A} (m : stdivnd S A) : DSLPSt S A :=
    dslpOfRelSt (fun s r => unOptionT (runStateT m s) (Some r)).
  Definition obsDSP {A} (m : stdivnd S A) : DSPSt S A :=
    dspOfRelSt (fun s r => unOptionT (runStateT m s) (Some r)).
  Definition obsASLP {A} (m : stdivnd S A) : ASLPSt S A :=
    aslpOfRelSt (fun s r => unOptionT (runStateT m s) (Some r)).

  Lemma getProgASP_obsASP {A} (m : stdivnd S A) pre r :
    getASPSt (obsASP m) pre r
    <-> (exists s, pre s /\ unOptionT (runStateT m s) (Some r)).
  Proof. apply getASPSt_of. Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivnd S A) pre r :
    getDSLPSt (obsDSLP m) pre r
    <-> (forall s, unOptionT (runStateT m s) (Some r) -> pre s).
  Proof. apply getDSLPSt_of. Qed.

  Lemma getProgDSP_obsDSP {A} (m : stdivnd S A) pre r :
    getDSPSt (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) (Some r))
         /\ (forall s, unOptionT (runStateT m s) (Some r) -> pre s)).
  Proof. apply getDSPSt_of. Qed.

  Lemma getProgASLP_obsASLP {A} (m : stdivnd S A) pre r :
    getASLPSt (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) (Some r))
         \/ (forall s, unOptionT (runStateT m s) (Some r) -> pre s)).
  Proof. apply getASLPSt_of. Qed.

  (** ** The ASP observation is a monad morphism *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : stdivnd S A)) (ret a).
  Proof.
    apply eq1_ASPSt_get. intros pre r. cbn [ret Monad_ASPSt].
    rewrite getProgASP_obsASP, getASPSt_ret. split.
    - intros [s [Hp Hr]]. exists s.
      split; [ exact Hp | exact (proj1 (outcomes_ret a s r) Hr) ].
    - intros [s [Hp Heq]]. exists s.
      split; [ exact Hp | exact (proj2 (outcomes_ret a s r) Heq) ].
  Qed.

  Theorem obsASP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    apply eq1_ASPSt_get. intros pre r. cbn [bind Monad_ASPSt].
    rewrite getProgASP_obsASP, getASPSt_bind.
    setoid_rewrite getProgASP_obsASP. split.
    - intros [s [Hp Hrel]]. apply outcomes_bind in Hrel.
      destruct Hrel as [a [s' [Hx Hk]]].
      exists a, s'. split.
      + exists s. split; [ exact Hp | exact Hx ].
      + exists s'. split; [ reflexivity | exact Hk ].
    - intros [a [s' [[s [Hp Hx]] [s2 [Hs2 Hk]]]]]. subst s2.
      exists s. split; [ exact Hp |]. apply outcomes_bind.
      exists a, s'. split; [ exact Hx | exact Hk ].
  Qed.

End Observations.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.

(* ==================================================================== *)
(** * Triples                                                            *)
(* ==================================================================== *)

(** [Over] requires the observed postcondition to imply [post]; [Under]
    requires [post] to imply it. *)
Inductive approxKind := | Under | Over.

Definition tripleASP {S A}
  (prog : stdivnd S A) (kind : approxKind)
  (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
  match kind with
  | Over  => forall r, getASPSt (obsASP prog) pre r -> post r
  | Under => forall r, post r -> getASPSt (obsASP prog) pre r
  end.

Definition tripleDSLP {S A}
  (prog : stdivnd S A) (kind : approxKind)
  (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
  match kind with
  | Over  => forall r, getDSLPSt (obsDSLP prog) pre r -> post r
  | Under => forall r, post r -> getDSLPSt (obsDSLP prog) pre r
  end.

Definition tripleDSP {S A}
  (prog : stdivnd S A) (kind : approxKind)
  (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
  match kind with
  | Over  => forall r, getDSPSt (obsDSP prog) pre r -> post r
  | Under => forall r, post r -> getDSPSt (obsDSP prog) pre r
  end.

Definition tripleASLP {S A}
  (prog : stdivnd S A) (kind : approxKind)
  (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
  match kind with
  | Over  => forall r, getASLPSt (obsASLP prog) pre r -> post r
  | Under => forall r, post r -> getASLPSt (obsASLP prog) pre r
  end.
