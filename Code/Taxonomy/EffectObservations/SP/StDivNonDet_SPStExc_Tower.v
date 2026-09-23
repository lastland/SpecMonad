(** * [StDivNonDet_SPStExc], via the stacking route.

    The exception-VISIBLE observation of [stateT S (optionT SetM)]: the
    divergence layer is KEPT ([GRel_optionT]) rather than sliced, so the
    outcome type is [option (A * S)] and "this program may diverge from a
    [pre]-state" is expressible.  Contrast [StDivNonDet_SPSt_Tower.v],
    where the same stack is sliced and divergence cannot be spoken about.

    Both the denotation and the carrier are derived:

      denotation   [GRel_SetM] -> [GRel_optionT] -> [GRel_stateT]
      carrier      [ASPCar_ofStack] at [aspRelE_ret] / [aspRelE_bind]

    so this client proves nothing.  Note that [ASPCar_StExcS] is a carrier
    that no hand-written instance in [SPRelTower.v] supplied -- it came out
    of [ASPCar_ofStack] for the cost of naming two lemmas that
    [ASPArrowRel.v] had already proved. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPArrowCore ASPArrowRel ASPMonad DSLPMonad
  DSPMonad ASLPMonad SPRelTower.

Import MonadNotation.
Open Scope monad_scope.

Section Tower.
  Variable S : Type.

  #[local] Existing Instance Monad_optionT.
  #[local] Existing Instance Monad_stateT.

  (* --- Step 1: stack, KEEPING the divergence layer.  No obligations. --- *)

  Definition GRel_keep
    : @GRel (stateT S (optionT SetM)) _ (unit * S)%type (fun A => option (A * S)%type)
        (@OShape_stateT unit (fun A => option A)
           (@OShape_optionT unit (fun A => A) OShape_Id) S) :=
    @GRel_stateT unit (fun A => option A)
      (@OShape_optionT unit (fun A => A) OShape_Id) S (optionT SetM) _
      (@GRel_optionT unit (fun A => A) OShape_Id SetM _ GRel_SetM).

  (* --- Steps 2 and 3: the carrier's index is already [unit * S], so there
         is no landing step; the observation is immediate. --- *)

  Definition obsASPx {A} (m : stateT S (optionT SetM) A) : ASPStExc S A :=
    @gobsASP _ _ (unit * S)%type (fun A => option (A * S)%type) _ GRel_keep
      (ASPStExc S) _ _ (ASPCar_StExcS S) A m.

  (* --- Step 4: the laws.  Citations. --- *)

  Theorem obsASPx_ret {A} (a : A) : eq1 (obsASPx (ret a)) (ret a).
  Proof.
    exact (@gobsASP_ret _ _ (unit * S)%type (fun A => option (A * S)%type) _
             GRel_keep (ASPStExc S) _ _ (ASPCar_StExcS S) A a).
  Qed.

  Theorem obsASPx_bind {A B} (x : stateT S (optionT SetM) A)
    (f : A -> stateT S (optionT SetM) B) :
    eq1 (obsASPx (bind x f)) (bind (obsASPx x) (fun a => obsASPx (f a))).
  Proof.
    exact (@gobsASP_bind _ _ (unit * S)%type (fun A => option (A * S)%type) _
             GRel_keep (ASPStExc S) _ _ (ASPCar_StExcS S) A B x f).
  Qed.

  (** The reading.  [o] ranges over [option (A * S)], so [o = None] says
      "some [P]-state may diverge" -- unspeakable on the sliced route. *)
  Lemma obsASPx_get {A} (m : stateT S (optionT SetM) A) P o :
    getASPArr (obsASPx m) P o
    <-> (exists p, P p /\ unOptionT (runStateT m (snd p)) o).
  Proof.
    exact (@aget_of _ _ _ _ _ _ (ASPCar_StExcS S) A
             (fun p w => unOptionT (runStateT m (snd p)) w) P o).
  Qed.

End Tower.
