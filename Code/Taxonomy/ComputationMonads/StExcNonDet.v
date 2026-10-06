From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.

Section SetM.

  Definition SetM A := A -> Prop.

  #[global]
    Instance Monad_SetM : Monad SetM :=
    {| ret := fun _ a => fun x => x = a ;
       bind := fun _ _ m k => fun b => exists a, m a /\ k a b |}.

End SetM.

Section StExcNonDet.

  Variable S : Type.

  Definition stexcnd A := stateT S (optionT SetM) A.

  #[local] Existing Instance Monad_stateT.

  Definition retP {A} (a : A) : stexcnd A :=
    @ret (stateT _ _) _ _ a.

  Definition bindP {A B} (m : stexcnd A) (k : A -> stexcnd B) : stexcnd B :=
    @bind (stateT _ _) _ _ _ m k.

  #[global]
    Instance Monad__stexcnd : Monad stexcnd :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Definition getP : stexcnd S :=
    @get _ (stateT _ _) _.

  Definition putP (s : S) : stexcnd unit :=
    @put _ (stateT _ _) _ s.

  #[global]
    Instance MonadState__stexcnd : MonadState S stexcnd :=
    {| get := getP ;
       put := putP |}.

  #[local] Existing Instance OptionTError.

  Definition raiseP {A} (_ : unit) : stexcnd A :=
    @raise _ (stateT _ _) _ _ tt.

  Definition catchP {A} (m : stexcnd A) (c : unit -> stexcnd A) : stexcnd A :=
    @catch _ (stateT _ _) _ _ m c.

  #[global]
    Instance MonadExc__stexcnd : MonadExc unit stexcnd :=
    {| raise := fun _ => raiseP ;
       catch := fun _ => catchP |}.

  Definition orP {A} (m1 m2 : stexcnd A) : stexcnd A :=
    mkStateT (fun s =>
      @mkOptionT SetM _ (fun oa =>
        unOptionT (runStateT m1 s) oa \/
        unOptionT (runStateT m2 s) oa)).

End StExcNonDet.

(* ================================================================= *)
(** * Raw outcome laws for [stateT S (optionT SetM)]                  *)
(* ================================================================= *)

(** Both [stexcnd] (this file) and [stdivnd] ([StDivNonDet.v]) use these
    raw dictionaries.  The effect-specific [retP]/[bindP] and [retD]/
    [bindD] convert to the operations named here, while the observations
    give [None] its exception or divergence reading.  All laws are
    pointwise iff statements about outcome sets; they are constructive
    and axiom-free. *)

Section RawOutcomes.

  Variable S : Type.

  Lemma outcomes_ret {A} (a : A) (s : S) (r : option (A * S)) :
    unOptionT (runStateT
      (@ret (stateT S (optionT SetM))
         (@Monad_stateT S (optionT SetM) (@Monad_optionT SetM Monad_SetM))
         A a) s) r <-> r = Some (a, s).
  Proof. split; intro H; exact H. Qed.

  (** [bind] with the absorbing outcome [None] — exactly the propagation
      rule both exception and divergence need. *)
  Lemma outcomes_bind {A B} (m : stateT S (optionT SetM) A)
      (k : A -> stateT S (optionT SetM) B) (s : S) (r : option (B * S)) :
    unOptionT (runStateT
      (@bind (stateT S (optionT SetM))
         (@Monad_stateT S (optionT SetM) (@Monad_optionT SetM Monad_SetM))
         A B m k) s) r <->
    exists oa, unOptionT (runStateT m s) oa /\
      match oa with
      | Some (a, s') => unOptionT (runStateT (k a) s') r
      | None => r = None
      end.
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. exists oy. split; [ exact H1 |].
      destruct oy as [[a s0]|]; cbn in *; [ exact H2 | congruence ].
    - intros [oy [H1 H2]]. exists oy. split; [ exact H1 |].
      destruct oy as [[a s0]|]; cbn in *; [ exact H2 | congruence ].
  Qed.

  (** The operations of [stexcnd] on the same raw shape: full outcome
      sets, not just a returning slice. *)

  Lemma outcomes_get (s : S) (r : option (S * S)) :
    unOptionT (runStateT (getP S) s) r <-> r = Some (s, s).
  Proof. split; intro H; exact H. Qed.

  Lemma outcomes_put (s0 s : S) (r : option (unit * S)) :
    unOptionT (runStateT (putP S s0) s) r <-> r = Some (tt, s0).
  Proof. split; intro H; exact H. Qed.

  (** [raiseP]'s only outcome is the exception token [None]. *)
  Lemma outcomes_raise {A} (s : S) (r : option (A * S)) :
    unOptionT (runStateT (raiseP S tt) s) r <-> r = None.
  Proof.
    cbn. split.
    - intros [aM [Ha Hr]]. subst aM. exact Hr.
    - intro Hr. exists None. split; [ reflexivity | exact Hr ].
  Qed.

End RawOutcomes.

(** ** Checked semantic examples: blocking versus the absorbing [None]

    An empty outcome set is BLOCKING — no bind outcome can be built from
    it — while a raised prefix survives even an empty continuation,
    because [bind] absorbs [None] without running the continuation. *)

Local Definition emptyP {S A} : stexcnd S A :=
  mkStateT (fun _ => @mkOptionT SetM _ (fun _ => False)).

(** An empty prefix blocks: the bind has no outcome either. *)
Local Example empty_prefix_blocks {S A B} (k : A -> stexcnd S B) (s : S)
    (r : option (B * S)) :
  ~ unOptionT (runStateT (bindP S emptyP k) s) r.
Proof.
  intro Hout.
  destruct (proj1 (outcomes_bind S emptyP k s r) Hout) as [oa [Hoa _]].
  exact Hoa.
Qed.

(** A raised prefix survives an empty continuation: the exception token
    is an outcome of the bind even though the continuation blocks. *)
Local Example raise_survives_empty {S A B} (s : S) :
  unOptionT (runStateT
    (bindP S (raiseP S tt : stexcnd S A) (fun _ => (emptyP : stexcnd S B))) s)
    None.
Proof.
  apply (outcomes_bind S).
  exists None. split.
  - apply (outcomes_raise S). reflexivity.
  - reflexivity.
Qed.

(* ================================================================= *)
(** * Facts and laws (merged from NonDetProgFacts.v)                          *)
(* ================================================================= *)

(** * Monad law proofs for [SetM] and [stexcnd].

    [SetM A = A -> Prop] is the powerset/nondeterminism monad.
    Monad laws hold up to Leibniz equality via propositional and
    functional extensionality.

    [stexcnd S = stateT S (optionT SetM)] then inherits
    [MonadLawsE] via the generic [optionT] and [stateT] instances
    from [Prog]. *)

From Coq Require Import FunctionalExtensionality PropExtensionality.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

(* ================================================================= *)
(** ** [Eq1] and [MonadLawsE] for [SetM]                             *)
(* ================================================================= *)

Section SetM.

  #[global]
  Instance Eq1_SetM : Eq1 SetM :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_SetM
    : @Eq1Equivalence SetM _ Eq1_SetM.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_SetM
    : @MonadLawsE SetM Eq1_SetM _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro c.
      apply propositional_extensionality. sauto.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_SetM in *. subst.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split; intros [a [Ha Hk]]; exists a; split; try exact Ha;
        [rewrite <- (Hfg a) | rewrite (Hfg a)]; exact Hk.
  Qed.

End SetM.

(* ================================================================= *)
(** ** [MonadLawsE] for [stexcnd S]                                    *)
(* ================================================================= *)

Section StExcNonDet.

  Variable S : Type.

  Definition Eq1__stexcnd : Eq1 (stexcnd S) :=
    Eq1_stateT S (optionT SetM).

  Definition MonadLawsE__stexcnd
    : @MonadLawsE (stexcnd S) _ (Monad__stexcnd S) :=
    MonadLawsE_stateT S (optionT SetM).

End StExcNonDet.
