From Coq Require Import List.
From ExtLib Require Import
  Monad MonadTrans MonadState MonadExc
  StateMonad OptionMonad List.
From Hammer Require Import Tactics.

Section PureSPost.

  Definition PureSPost A :=
    forall (pre : Prop), {p : A -> Prop | forall a, p a -> pre}.

  #[local]
  #[program] Definition retSP {A} (a : A) : PureSPost A :=
    fun pre => exist _ (fun v => v = a /\ pre) _.

  #[local]
  #[program] Definition bindSP {A B}
    (m : PureSPost A) (k : A -> PureSPost B) : PureSPost B :=
    fun pre => exist _ (fun b =>
      exists a, proj1_sig (k a (proj1_sig (m pre) a)) b) _.
  Next Obligation. sfirstorder. Qed.

  #[global]
    Instance Monad_PureSPost : Monad PureSPost :=
    {| ret := fun _ => retSP ;
       bind := fun _ _ => bindSP |}.

End PureSPost.

Section ProgSPost.

  Variable S : Type.

  Definition ProgSPost := stateT S (optionT PureSPost).

  (* Copy-pasted from [WP.v]. *)
  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : ProgSPost A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B}
    (m : ProgSPost A) (k : A -> ProgSPost B) : ProgSPost B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__ProgSPost : Monad ProgSPost :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : ProgSPost S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : ProgSPost unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__ProgSPost : MonadState S ProgSPost :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : ProgSPost A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A}
    (m : ProgSPost A) (c : unit -> ProgSPost A) : ProgSPost A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__ProgSPost : MonadExc unit ProgSPost :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

End ProgSPost.
