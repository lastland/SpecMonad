From ExtLib Require Import
  Monad MonadState
  StateMonad OptionMonad.
From Incorrectness.Taxonomy Require Import NonDetProg.

(** * Nondeterministic, possibly divergent stateful computations

    Same carrier as [ndprog]: [stateT S (optionT SetM)], whose payload is
    [S -> option (A * S) -> Prop] — a SET of outcomes for each initial state.
    What differs is the reading of the distinguished outcome [None]:

      - in [ndprog] it is a raised EXCEPTION ([MonadExc__ndprog]);
      - here it is DIVERGENCE.

    Nothing in the type distinguishes the two; what fixes the meaning is which
    operations are offered.  So this module deliberately provides NO [MonadExc]
    instance — [catch] would be "recover from divergence", which is not an
    observable operation — and instead provides [divergeD], the everywhere-
    divergent program.

    [None] is absorbing under [bind] (see [outcomes_bind] in
    [NonDetObservationNew]), which is exactly the propagation rule divergence
    needs, so the monad structure is unchanged. *)

Section NonDetDivProg.

  Variable S : Type.

  Definition nddprog A := stateT S (optionT SetM) A.

  #[local] Existing Instance Monad_stateT.

  Definition retD {A} (a : A) : nddprog A :=
    @ret (stateT _ _) _ _ a.

  Definition bindD {A B} (m : nddprog A) (k : A -> nddprog B) : nddprog B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__nddprog : Monad nddprog :=
    {| ret := fun _ => @retD _ ;
       bind := fun _ _ => @bindD _ _ |}.

  Definition getD : nddprog S :=
    @get _ (stateT _ _) _.

  Definition putD (s : S) : nddprog unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__nddprog : MonadState S nddprog :=
    {| get := getD ;
       put := putD |}.

  (** The everywhere-divergent program: from every state its only outcome is
      the divergence token. *)
  Definition divergeD {A} : nddprog A :=
    mkStateT (fun _ => @mkOptionT SetM _ (fun oa => oa = None)).

  (** Nondeterministic choice: union of outcome sets. *)
  Definition orD {A} (m1 m2 : nddprog A) : nddprog A :=
    mkStateT (fun s =>
      @mkOptionT SetM _ (fun oa =>
        unOptionT (runStateT m1 s) oa \/
        unOptionT (runStateT m2 s) oa)).

  (** [m] may diverge from [s]. *)
  Definition mayDiverge {A} (m : nddprog A) (s : S) : Prop :=
    unOptionT (runStateT m s) None.

End NonDetDivProg.

Arguments nddprog _ _.
Arguments divergeD {_} {_}.
Arguments orD {_} {_}.
Arguments mayDiverge {_} {_}.
