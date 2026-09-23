(** * [DivNonDet_SPure], via the stacking route.

    The ALTERNATIVE to [DivNonDet_SPure_Rel.v], which supplies [prel] and
    its two laws by hand.  Here the denotation is [SPRelTower.v]'s base
    slice -- [GRel_divnd_slice], the [SetM] outcome set with the divergence
    layer projected away -- so there is nothing to stack and nothing to
    prove: this is the shortest client the tower admits.

    Keeping that layer instead ([GRel_optionT]) is what makes divergence
    speakable; projecting it is the choice recorded here.

    [obsASPp_is_obsASP] / [obsDSLPp_is_obsDSLP] show the two routes land on
    the same observation, by [reflexivity]. *)

From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad SPRelTower.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  DivNonDet_SPure_Rel.

Import MonadNotation.
Open Scope monad_scope.

(* --- Steps 1 and 2 are empty: the base slice already has this shape. --- *)

(* --- Step 3: the observations. --- *)

Definition obsASPp {A} (m : optionT SetM A) : ASP A :=
  @gobsASP _ _ unit (fun A => A) OShape_Id GRel_divnd_slice
    ASP _ _ ASPCar_Pure A m.

Definition obsDSLPp {A} (m : optionT SetM A) : DSLP A :=
  @gobsDSLP _ _ unit (fun A => A) OShape_Id GRel_divnd_slice
    DSLP _ _ DSLPCar_Pure A m.

(* --- Step 4: the laws.  Citations. --- *)

Theorem obsASPp_ret {A} (a : A) : eq1 (obsASPp (ret a)) (ret a).
Proof.
  exact (@gobsASP_ret _ _ unit (fun A => A) OShape_Id GRel_divnd_slice
           ASP _ _ ASPCar_Pure A a).
Qed.

Theorem obsASPp_bind {A B} (x : optionT SetM A) (f : A -> optionT SetM B) :
  eq1 (obsASPp (bind x f)) (bind (obsASPp x) (fun a => obsASPp (f a))).
Proof.
  exact (@gobsASP_bind _ _ unit (fun A => A) OShape_Id GRel_divnd_slice
           ASP _ _ ASPCar_Pure A B x f).
Qed.

Theorem obsDSLPp_ret {A} (a : A) : eq1 (obsDSLPp (ret a)) (ret a).
Proof.
  exact (@gobsDSLP_ret _ _ unit (fun A => A) OShape_Id GRel_divnd_slice
           DSLP _ _ DSLPCar_Pure A a).
Qed.

Theorem obsDSLPp_bind {A B} (x : optionT SetM A) (f : A -> optionT SetM B) :
  eq1 (obsDSLPp (bind x f)) (bind (obsDSLPp x) (fun a => obsDSLPp (f a))).
Proof.
  exact (@gobsDSLP_bind _ _ unit (fun A => A) OShape_Id GRel_divnd_slice
           DSLP _ _ DSLPCar_Pure A B x f).
Qed.

(* --- The readings: "some [p]-state reaches [a]" / "everything reaching
       [a] was a [p]-state", with divergence invisible. --- *)

Lemma obsASPp_get {A} (m : optionT SetM A) p a :
  getASP (obsASPp m) p a <-> (p /\ unOptionT m (Some a)).
Proof. exact (getASP_of (fun o => unOptionT m (Some o)) p a). Qed.

Lemma obsDSLPp_get {A} (m : optionT SetM A) p a :
  getDSLP (obsDSLPp m) p a <-> (unOptionT m (Some a) -> p).
Proof. exact (getDSLP_of (fun o => unOptionT m (Some o)) p a). Qed.

(* --- The two routes agree, on the nose. --- *)

Theorem obsASPp_is_obsASP {A} (m : optionT SetM A) p a :
  getASP (obsASPp m) p a <-> getASP (obsASP m) p a.
Proof. reflexivity. Qed.

Theorem obsDSLPp_is_obsDSLP {A} (m : optionT SetM A) p a :
  getDSLP (obsDSLPp m) p a <-> getDSLP (obsDSLP m) p a.
Proof. reflexivity. Qed.
