From ExtLib Require Import Monad OptionMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.

(** * Nondeterministic computations with explicit exceptions and
    divergence, without state

    [divexcnd A = optionT (optionT SetM) A], whose payload is
    [option (option A) -> Prop] — a set of full outcomes with three
    outcome kinds:

    - [Some (Some a)] : successful return with result [a]
    - [Some None]     : raises an exception
    - [None]          : diverges

    The [optionT] directly over [SetM] contributes the raw outer option
    (divergence); the surrounding transformer contributes the raw inner
    option (exception).  Unlike a single-option model, this stack can
    distinguish exceptional and divergent branches of the same computation.

    This is the state-free base of [stdivexcnd] in [StDivExcNonDet.v].
    An empty outcome set represents blocking, not either failure token. *)

Section DivExcNonDet.

  Definition divexcnd A := optionT (optionT SetM) A.

  Definition retP {A} (a : A) : divexcnd A :=
    @ret (optionT (optionT SetM)) _ _ a.

  (** Only [Some (Some a)] calls [k a].  An exception or divergence
      propagates unchanged, even when [k] would have no outcomes. *)
  Definition bindP {A B} (m : divexcnd A) (k : A -> divexcnd B) : divexcnd B :=
    @bind (optionT (optionT SetM)) _ _ _ m k.

  #[global]
    Instance Monad__divexcnd : Monad divexcnd :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  (** The full outcome set of [m]: [outcomes m o] says that [o] is a
      possible full outcome of [m]. *)
  Definition outcomes {A} (m : divexcnd A) : option (option A) -> Prop :=
    unOptionT (unOptionT m).

  (** The inner raw [None] records an exception; its enclosing [Some]
      distinguishes it from divergence. *)
  Definition raiseP {A} : divexcnd A :=
    @mkOptionT (optionT SetM) A
      (@mkOptionT SetM (option A) (fun o => o = Some None)).

  (** Divergence has a singleton outcome set, containing [None].
      It is not represented by the absence of outcomes. *)
  Definition spinP {A} : divexcnd A :=
    @mkOptionT (optionT SetM) A
      (@mkOptionT SetM (option A) (fun o => o = None)).

  (** Nondeterministic choice is raw union, not ExtLib's left-biased
      [Plus_optionT].  At this stack's exception layer, option choice keeps
      a successful left result, tries the right branch on [Some None], and
      propagates [None].  For example, [orP raiseP spinP] retains both
      failure tokens; left-biased fallback would retain only divergence. *)
  Definition orP {A} (m1 m2 : divexcnd A) : divexcnd A :=
    @mkOptionT (optionT SetM) A
      (@mkOptionT SetM (option A)
         (fun o => outcomes m1 o \/ outcomes m2 o)).

End DivExcNonDet.

(* ================================================================= *)
(** ** Raw outcome laws                                                *)
(* ================================================================= *)

(** Clients should reuse these pointwise equivalences rather than unfold
    the transformer stack.  They describe full outcomes, including both
    failure tokens, and need no extensionality. *)

(** This local definition supplies the blocking continuations used below:
    it has no return, exception, or divergence outcome. *)
Local Definition blockP {A} : divexcnd A :=
  @mkOptionT (optionT SetM) A
    (@mkOptionT SetM (option A) (fun _ => False)).

Section OutcomeLaws.

  Lemma outcomes_ret {A} (a : A) (o : option (option A)) :
    outcomes (retP a) o <-> o = Some (Some a).
  Proof. cbn. split; intro H; congruence. Qed.

  (** A bind needs an intermediate outcome.  An empty prefix therefore
      blocks, but either failure token survives an empty continuation:
      neither failure case asks for an outcome of [k]. *)
  Lemma outcomes_bind {A B} (m : divexcnd A) (k : A -> divexcnd B)
      (o : option (option B)) :
    outcomes (bindP m k) o <->
    (exists oa, outcomes m oa /\
       match oa with
       | Some (Some a) => outcomes (k a) o
       | Some None => o = Some None
       | None => o = None
       end).
  Proof.
    cbn. split; intros [oa [H1 H2]]; exists oa; split; try exact H1;
      destruct oa as [[a|]|]; exact H2.
  Qed.

  Lemma outcomes_raise {A} (o : option (option A)) :
    outcomes (raiseP : divexcnd A) o <-> o = Some None.
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma outcomes_spin {A} (o : option (option A)) :
    outcomes (spinP : divexcnd A) o <-> o = None.
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma outcomes_orP {A} (m1 m2 : divexcnd A) (o : option (option A)) :
    outcomes (orP m1 m2) o <-> outcomes m1 o \/ outcomes m2 o.
  Proof. cbn. split; [ intro H; destruct H as [H|H]; [ left | right ]; exact H
                    | intros [H|H]; [ left | right ]; exact H ]. Qed.

  (** ** Checked examples

      A returning prefix runs its continuation.  The failure examples
      contrast this with bypassing even a blocking continuation. *)

  Example success_continuation (o : option (option nat)) :
    outcomes (bindP (retP 0 : divexcnd nat) (fun n => retP (S n))) o
    <-> o = Some (Some 1).
  Proof.
    rewrite outcomes_bind. split.
    - intros [oa [Hm Hk]]. cbn in Hm. subst oa.
      exact (proj1 (outcomes_ret 1 o) Hk).
    - intro Ho. exists (Some (Some 0)). split.
      + apply outcomes_ret. reflexivity.
      + exact (proj2 (outcomes_ret 1 o) Ho).
  Qed.

  (** The exception token survives an empty continuation. *)
  Example raise_survives_empty (o : option (option nat)) :
    outcomes (bindP (raiseP : divexcnd unit) (fun _ => blockP (A := nat))) o
    <-> o = Some None.
  Proof.
    rewrite outcomes_bind. split.
    - intros [oa [Hr H]]. cbn in Hr. subst oa. exact H.
    - intro Ho. exists (Some None). split.
      + apply outcomes_raise. reflexivity.
      + exact Ho.
  Qed.

  (** ...and so does the divergence token. *)
  Example spin_survives_empty (o : option (option nat)) :
    outcomes (bindP (spinP : divexcnd unit) (fun _ => blockP (A := nat))) o
    <-> o = None.
  Proof.
    rewrite outcomes_bind. split.
    - intros [oa [Hs H]]. cbn in Hs. subst oa. exact H.
    - intro Ho. exists None. split.
      + apply outcomes_spin. reflexivity.
      + exact Ho.
  Qed.

  (** A single choice can return [0], raise, or diverge.  The successful
      left branch does not suppress either failure in the right branch. *)
  Definition mixed : divexcnd nat := orP (retP 0) (orP raiseP spinP).

  Example mixed_outcomes (o : option (option nat)) :
    outcomes mixed o <-> o = Some (Some 0) \/ o = Some None \/ o = None.
  Proof.
    unfold mixed.
    rewrite outcomes_orP, outcomes_orP, outcomes_ret,
      outcomes_raise, outcomes_spin.
    tauto.
  Qed.

End OutcomeLaws.

(* ================================================================= *)
(** * Facts and laws                                                  *)
(* ================================================================= *)

(** The generic [optionT] instances in [TransformerLaws.v] lift the
    [SetM] laws from [StExcNonDet.v] through both layers. *)

From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

Section DivExcNonDetLaws.

  (** The instance chain:
         [Eq1_SetM]
      → [Eq1_optionT]  (for [optionT SetM])
      → [Eq1_optionT]  (for [divexcnd])

      and similarly for [Eq1Equivalence] and [MonadLawsE]. *)

  Definition Eq1__divexcnd : Eq1 divexcnd :=
    Eq1_optionT (optionT SetM).

  Definition Eq1Equivalence__divexcnd
    : @Eq1Equivalence divexcnd _ Eq1__divexcnd :=
    Eq1Equivalence_optionT (optionT SetM).

  Definition MonadLawsE__divexcnd
    : @MonadLawsE divexcnd _ Monad__divexcnd :=
    MonadLawsE_optionT (optionT SetM).

End DivExcNonDetLaws.
