(** * Shared raw-outcome normalization for [stateT S (optionT SetM)].

    Both [stexcnd] and [stdivnd] use these dictionaries.  The effect-specific
    [retP]/[bindP] and [retD]/[bindD] convert to these operations, while the
    observations give [None] its exception or divergence interpretation. *)

From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.

Section RawStOptOutcomes.
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
End RawStOptOutcomes.
