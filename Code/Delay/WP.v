From ExtLib Require Import
  Monad MonadTrans MonadLaws
  StateMonad OptionMonad
  MonadState MonadExc.
From ITree Require Import ITree Eq Props.Infinite.
From ITree.Extra.Dijkstra Require Import DelaySpecMonad.
From Hammer Require Import Tactics.

#[local] Open Scope itree_scope.

Section Prog.

  Variable S : Type.

  (** A program is stateful, can have exceptions, and is nondeterministic. *)
  Definition prog A := stateT S (optionT Delay) A -> Prop.

  Definition eutt_SOD {A} (a b: stateT S (optionT Delay) A) : Prop :=
    match a, b with
    | mkStateT f, mkStateT g =>
        forall s, match f s, g s with
             | mkOptionT x, mkOptionT y =>
                 eutt eq x y
             end
    end.

  (* In ExtLib, [stateT] is not a global [Monad] instance. *)
  #[local] Existing Instance Monad_stateT.

  Definition ret_prog {A} (a : A) : prog A :=
    fun p => eutt_SOD p (ret a). 
    
  Definition bind_prog {A B} (m : prog A) (k : A -> prog B) : prog B :=
    fun b => exists a, m (ret a) /\ k a b.

  #[global]
  Instance Monad__prog : Monad prog :=
    {| ret := fun A => @ret_prog A ;
       bind := fun A B => @bind_prog A B
    |}.

  Definition get_prog : prog S :=
    fun p => eutt_SOD p get.

  Definition put_prog (s : S) : prog unit :=
    fun p => eutt_SOD p (put s).

  #[global]
  Instance MonadState__prog : MonadState S prog :=
    {| get := get_prog ;
       put := put_prog
    |}.

  (* In ExtLib, [optionT] is not a global [MonadExc] instance. *)
  #[local] Existing Instance OptionTError.
  
  Definition raise_prog {A} : unit -> prog A :=
    fun _ p => eutt_SOD p (lift (raise tt)).

  Definition catch_prog {A} (m : prog A) (k : unit -> prog A) : prog A :=
    fun p => m p \/ (m (lift (raise tt)) /\ k tt p).

  #[global]
  Instance MonadExc__prog : MonadExc unit prog :=
    {| raise := fun A => @raise_prog A ;
       catch := fun A => @catch_prog A
    |}.

  Definition pick : prog bool :=
    fun p => eutt_SOD p (ret true) \/ eutt_SOD p (ret false).

End Prog.

(** This is from the Dijkstra monad forever paper. However, later we choose to
    do something different. *)
Section Spec.

  Variable S : Type.

  Definition progSpec A := stateT S (optionT DelaySpec) A.

  #[local] Hint Unfold progSpec : prog.

  (* In ExtLib, [stateT] is not a global [Monad] instance. *)
  #[local] Existing Instance Monad_stateT.
  
  Definition ret_progSpec {A} (a : A) : progSpec A :=
    @ret (stateT S (optionT DelaySpec)) _ _ a.

  (** This essentially uses the [bind] of [DelaySpec]. Its definition is here:
      https://github.com/DeepSpec/InteractionTrees/blob/master/extra/Dijkstra/DelaySpecMonad.v#L77-L79
      This definition specifies the behavior of terminating programs AND
      non-terminating program. This is different from either weakest
      precondition transformer (always false when diverges) or weakest
      liberal precondition transformer (always true when diverges). *)
  Definition bind_progSpec {A B} (m : progSpec A) (k : A -> progSpec B) : progSpec B :=
    @bind (stateT S (optionT DelaySpec)) _ _ _ m k.

  #[global]
  Instance Monad__progSpec : Monad progSpec :=
    {| ret := fun A => @ret_progSpec A ;
       bind := fun A B => @bind_progSpec A B 
    |}.

End Spec.

Section WPProgSpec.

  #[local] Open Scope delayspec_scope.

  Definition DelayAWP := DelaySpec.

  #[program] Definition _bind_awp {A B : Type} (w : DelaySpec A) (f : A -> DelaySpec B)
    : DelaySpecInput B -> Prop :=
    fun p => w ∋ (fun t => (exists a, Ret a ≈ t /\ p ∈ f a)).
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    intros t1 t2 Heutt. split; intros; basic_solve.
    - exists a. split; auto. rewrite H. auto.
    - exists a. rewrite Heutt. auto.
  Qed.

  #[program] Definition bind_awp {A B : Type} (w : DelayAWP A) (f : A -> DelayAWP B) :
    DelayAWP B :=
    _bind_awp w f.
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    red. red in H0. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
    simpl. intros. basic_solve.
    exists a. split; auto. dest_dep f a. eapply Hfa; eauto.
  Qed.
    
  Definition DelayDWP := DelaySpec.

  #[program] Definition _bind_dwp {A B : Type} (w : DelaySpec A) (f : A -> DelaySpec B)
    : DelaySpecInput B -> Prop :=
    fun p => w ∋ (fun t => (forall a, Ret a ≈ t -> p ∈ f a)).
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    intros t1 t2 Heutt. split; intros; basic_solve.
    - apply H. rewrite Heutt. assumption. 
    - apply H. rewrite <- Heutt. assumption.
  Qed.

  #[program] Definition bind_dwp {A B : Type} (w : DelayDWP A) (f : A -> DelayDWP B) :
    DelayDWP B :=
    _bind_dwp w f.
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    red. red in H0. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
    simpl. intros. basic_solve.
    dest_dep f a. eapply Hfa; eauto. fcrush. 
  Qed.

  Definition DelayAWLP := DelaySpec.

  #[program] Definition _bind_awlp {A B : Type} (w : DelaySpec A) (f : A -> DelaySpec B)
    : DelaySpecInput B -> Prop :=
    fun p => w ∋ (fun t => (exists a, Ret a ≈ t /\ p ∈ f a) \/ any_infinite t).
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    intros t1 t2 Heutt. split; intros; basic_solve.
    - left. exists a. split; auto. rewrite H. auto.
    - right. rewrite <- Heutt. assumption.
    - left. exists a. rewrite Heutt. auto.
    - right. rewrite Heutt. assumption.
  Qed.

  #[program] Definition bind_awlp {A B : Type} (w : DelayAWLP A) (f : A -> DelayAWLP B) :
    DelayAWLP B :=
    _bind_awlp w f.
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    red. red in H0. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
    simpl. intros. basic_solve.
    - left. exists a. split; auto. dest_dep f a. eapply Hfa; eauto.
    - right. assumption.
  Qed.
    
  Definition DelayDWLP := DelaySpec.

  #[program] Definition _bind_dwlp {A B : Type} (w : DelaySpec A) (f : A -> DelaySpec B)
    : DelaySpecInput B -> Prop :=
    fun p => w ∋ (fun t => (forall a, Ret a ≈ t -> p ∈ f a) \/ any_infinite t).
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    intros t1 t2 Heutt. split; intros; basic_solve.
    - left. intros. apply H. rewrite Heutt. assumption.
    - right. rewrite <- Heutt. assumption.
    - left. intros. apply H. rewrite <- Heutt. assumption.
    - right. rewrite Heutt. assumption.
  Qed.

  #[program] Definition bind_dwlp {A B : Type} (w : DelayDWLP A) (f : A -> DelayDWLP B) :
    DelayDWLP B :=
    _bind_dwlp w f.
  Next Obligation.
    (* Adapted from Dijkstra monad forever proof. *)
    red. red in H0. destruct w as [w Hw]. simpl in *. eapply Hw; try apply H0.
    simpl. intros. basic_solve.
    - left. intros. dest_dep f a. eapply Hfa; eauto. fcrush.
    - right. assumption.
  Qed.

End WPProgSpec.
