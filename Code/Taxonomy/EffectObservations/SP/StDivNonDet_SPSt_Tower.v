(** * [StDivNonDet_SPSt], via the stacking route.

    The ALTERNATIVE to [StDivNonDet_SPSt_Rel.v].  That file supplies the
    denotation of [stdivnd] and its two laws by hand ([outcomes_ret],
    [outcomes_bind]) and gets the four observations from [SPRelDenote.v].
    Here the denotation is STACKED out of [SPRelTower.v]'s base and steps,
    so those two laws are not written at all.

    Both files are kept.  [obsASPt_is_obsASP] and [obsDSLPt_is_obsDSLP] at
    the end show the two routes land on the same observation, by
    [reflexivity] -- so this is a drop-in alternative, not a parallel
    construction.

    The stack is read bottom-up:

      [GRel_SetM]          the outcome set                 (hand, in SPRelTower)
      [GRel_divnd_slice]   + optionT, divergence SLICED    (hand, in SPRelTower)
      [GRel_stateT]        + stateT S                      (free)

    Keeping the divergence layer instead ([GRel_optionT]) is what gives the
    [option]-indexed observations of [StDivNonDet_SPStExc.v]; that fork is
    the SP counterpart of the WP side's [none : L]. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad SPRelTower.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPSt_Rel.

Import MonadNotation.
Open Scope monad_scope.

Section Tower.
  Variable S : Type.

  #[local] Existing Instance Monad_optionT.
  #[local] Existing Instance Monad_stateT.

  (* --- Step 1: stack the denotation.  No proof obligations. --- *)

  Definition GRel_stdivndT_raw
    : @GRel (stateT S (optionT SetM)) _ (unit * S)%type (fun A => (A * S)%type)
        (@OShape_stateT unit (fun A => A) OShape_Id S) :=
    @GRel_stateT unit (fun A => A) OShape_Id S (optionT SetM) _ GRel_divnd_slice.

  (* --- Step 2: land it on the carrier's own shape.  Two [exact]s, by
         conversion: the stacked [oeta]/[ostep] reduce to [OShape_St]'s. --- *)

  Definition GRel_stdivndT
    : @GRel (stateT S (optionT SetM)) _ S (fun A => (A * S)%type) (OShape_St S).
  Proof.
    refine {| grel A m s r := @grel _ _ _ _ _ GRel_stdivndT_raw A m (tt, s) r |}.
    - intros A a s r.
      exact (@grel_ret _ _ _ _ _ GRel_stdivndT_raw A a (tt, s) r).
    - intros A B x f s r.
      exact (@grel_bind _ _ _ _ _ GRel_stdivndT_raw A B x f (tt, s) r).
  Defined.

  (* --- Step 2b: land it on [stdivnd], which on this branch IS the stacked
         transformer, with its own [Monad] instance. --- *)

  Definition GRel_stdivnd
    : @GRel (stdivnd S) _ S (fun A => (A * S)%type) (OShape_St S).
  Proof.
    refine {| grel A m s r := @grel _ _ _ _ _ GRel_stdivndT A m s r |}.
    - intros A a s r.
      exact (@grel_ret _ _ _ _ _ GRel_stdivndT A a s r).
    - intros A B x f s r.
      exact (@grel_bind _ _ _ _ _ GRel_stdivndT A B x f s r).
  Defined.

  (* --- Step 3: the observations. --- *)

  Definition obsASPt {A} (m : stdivnd S A) : ASPSt S A :=
    @gobsASP _ _ S _ (OShape_St S) GRel_stdivnd (ASPSt S) _ _ (ASPCar_St S) A m.

  Definition obsDSLPt {A} (m : stdivnd S A) : DSLPSt S A :=
    @gobsDSLP _ _ S _ (OShape_St S) GRel_stdivnd (DSLPSt S) _ _ (DSLPCar_St S) A m.

  (* --- Step 4: the laws.  Citations. --- *)

  Theorem obsASPt_ret {A} (a : A) : eq1 (obsASPt (ret a)) (ret a).
  Proof.
    exact (@gobsASP_ret _ _ S _ (OShape_St S) GRel_stdivnd
             (ASPSt S) _ _ (ASPCar_St S) A a).
  Qed.

  Theorem obsASPt_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASPt (bind x f)) (bind (obsASPt x) (fun a => obsASPt (f a))).
  Proof.
    exact (@gobsASP_bind _ _ S _ (OShape_St S) GRel_stdivnd
             (ASPSt S) _ _ (ASPCar_St S) A B x f).
  Qed.

  Theorem obsDSLPt_ret {A} (a : A) : eq1 (obsDSLPt (ret a)) (ret a).
  Proof.
    exact (@gobsDSLP_ret _ _ S _ (OShape_St S) GRel_stdivnd
             (DSLPSt S) _ _ (DSLPCar_St S) A a).
  Qed.

  Theorem obsDSLPt_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSLPt (bind x f)) (bind (obsDSLPt x) (fun a => obsDSLPt (f a))).
  Proof.
    exact (@gobsDSLP_bind _ _ S _ (OShape_St S) GRel_stdivnd
             (DSLPSt S) _ _ (DSLPCar_St S) A B x f).
  Qed.

  (* --- The readings. --- *)

  Lemma obsASPt_get {A} (m : stdivnd S A) pre r :
    getASPSt (obsASPt m) pre r
    <-> (exists s, pre s /\ unOptionT (runStateT m s) (Some r)).
  Proof. apply getASPSt_of. Qed.

  Lemma obsDSLPt_get {A} (m : stdivnd S A) pre r :
    getDSLPSt (obsDSLPt m) pre r
    <-> (forall s, unOptionT (runStateT m s) (Some r) -> pre s).
  Proof. apply getDSLPSt_of. Qed.

  (* --- The two routes agree, on the nose. --- *)

  Theorem obsASPt_is_obsASP {A} (m : stdivnd S A) pre r :
    getASPSt (obsASPt m) pre r <-> getASPSt (obsASP m) pre r.
  Proof. reflexivity. Qed.

  Theorem obsDSLPt_is_obsDSLP {A} (m : stdivnd S A) pre r :
    getDSLPSt (obsDSLPt m) pre r <-> getDSLPSt (obsDSLP m) pre r.
  Proof. reflexivity. Qed.

End Tower.

Arguments obsASPt  {_} {_}.
Arguments obsDSLPt {_} {_}.
