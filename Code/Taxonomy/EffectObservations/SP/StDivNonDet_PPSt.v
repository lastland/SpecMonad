(** * A pre/post observation of [stdivnd]: total correctness AND strongest post.

    Every other SP observation in this development lands in a ONE-SLOT
    carrier -- [ASPSt], [DSLPSt], [DSPSt], [ASLPSt] are each a single
    predicate transformer capturing a single reading.  This one lands in
    [PrePostArr] with the state threaded ([stateArrT S PrePostArr] at input
    [unit], written out as [PPSt]), and so carries TWO readings at once.

    The two slots take different readings because they COMPOSE differently:

      pre  : [ppre m s /\ forall a s', ppost m s (a,s') -> ppre (k a) s']
      post : [exists a s', ppost m s (a,s') /\ ppost (k a) s' r]

    The pre slot is demonic (a guarantee must cover every branch), the post
    slot angelic (one path suffices).  So the pre slot admits a DEMONIC
    reading -- total correctness -- and the post an ANGELIC one -- ASP
    reachability:

      [obsPPm m = (mustT m, reachability-relation-of-m)]

    [obsPPm_bind]'s pre half is exactly the decomposition of divergence

      [div (bind m k) s  <->  div m s \/ exists a s', rel m s (a,s') /\ div (k a) s']

    negated, which is [bindPPSt]'s precondition verbatim; its post half is
    [outcomes_bind].  Both constructively.

    Getting the pre slot right took two false starts, recorded in
    [ASPUnderObstructions.v]: the trivial precondition satisfies the laws
    but carries no information, and [dom] ("can terminate", angelic) FAILS
    them -- see [obsPPdom_bind_fails].

    This does not index the ASP [Under] triple; the post slot is still
    compared pointwise in [s].  See [Dijkstra_StDivNonDet_ASPUnder.v]. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPStExc.

Import FullOutcomeObs.
Import MonadNotation.
Open Scope monad_scope.

Definition PPSt (S A : Type) : Type :=
  ((S -> Prop) * (S -> A * S -> Prop))%type.
Definition ppre  {S A} (m : PPSt S A) : S -> Prop := fst m.
Definition ppost {S A} (m : PPSt S A) : S -> A * S -> Prop := snd m.

Definition retPPSt {S A} (a : A) : PPSt S A :=
  (fun _ => True, fun s r => r = (a, s)).
Definition bindPPSt {S A B} (m : PPSt S A) (k : A -> PPSt S B) : PPSt S B :=
  ( fun s => ppre m s /\ (forall a s', ppost m s (a, s') -> ppre (k a) s')
  , fun s r => exists a s', ppost m s (a, s') /\ ppost (k a) s' r ).
Definition PPSt_eq {S A} (m n : PPSt S A) : Prop :=
  (forall s, ppre m s <-> ppre n s) /\ (forall s r, ppost m s r <-> ppost n s r).

(** The pre slot composes DEMONICALLY, so what belongs there is a demonic
    reading.  Total correctness: no divergent outcome from [s]. *)
Definition mustT {S A} (m : stdivnd S A) : S -> Prop :=
  fun s => ~ unOptionT (runStateT m s) None.

Definition obsPPm {S A} (m : stdivnd S A) : PPSt S A :=
  (mustT m, fun s r => unOptionT (runStateT m s) (Some r)).

Theorem obsPPm_ret {S A} (a : A) : PPSt_eq (obsPPm (ret a : stdivnd S A)) (retPPSt a).
Proof.
  split.
  - intro s. cbn. unfold mustT. split.
    + intros _. exact I.
    + intros _ Hdiv. apply (outcomes_ret S) in Hdiv. discriminate Hdiv.
  - intros s r. cbn. split.
    + intro H. apply (outcomes_ret S) in H. injection H as ->. reflexivity.
    + intro H. apply (outcomes_ret S). rewrite H. reflexivity.
Qed.

Theorem obsPPm_bind {S A B} (m : stdivnd S A) (k : A -> stdivnd S B) :
  PPSt_eq (obsPPm (bind m k)) (bindPPSt (obsPPm m) (fun a => obsPPm (k a))).
Proof.
  split.
  - intro s. cbn. unfold mustT. split.
    + intro Hnd. split.
      * intro Hm. apply Hnd. apply (outcomes_bind S).
        exists None. split; [ exact Hm | reflexivity ].
      * intros a s' Hr Hk. apply Hnd. apply (outcomes_bind S).
        exists (Some (a, s')). split; [ exact Hr | exact Hk ].
    + intros [Hm Hall] Hdiv. apply (outcomes_bind S) in Hdiv.
      destruct Hdiv as [oy [Hy Hrest]]. destruct oy as [[a s']|].
      * exact (Hall a s' Hy Hrest).
      * exact (Hm Hy).
  - intros s r. cbn. split.
    + intro H. apply (outcomes_bind S) in H. destruct H as [oy [Hy Hrest]].
      destruct oy as [[a s']|]; [| discriminate Hrest ].
      exists a, s'. split; [ exact Hy | exact Hrest ].
    + intros [a [s' [Hy Hk]]]. apply (outcomes_bind S).
      exists (Some (a, s')). split; [ exact Hy | exact Hk ].
Qed.
