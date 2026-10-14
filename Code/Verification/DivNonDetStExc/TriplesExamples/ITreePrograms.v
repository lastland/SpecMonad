(** * [progA] as an ITree program

    [progA] of [ProgA.v], written with ExtLib's [get] and [put] over ITrees
    and ITree's nondeterministic choice [Or].  From any start state its tree
    is a choice between ending in state [42] and ending in state [43]
    ([progA_IT_tree]), so it has the outcomes of [progA] ([progA_IT_out]).
    A triple of the program is a triple of its denotation. *)

From Coq Require Import Lia.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad MonadTrans.
From ITree Require Import ITree Eq.
From ITree Require Events.Nondeterminism.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Computation.
From Incorrectness.Verification.DivNonDetStExc Require Import Morphisms.
From Incorrectness.Verification.DivNonDetStExc Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

Definition progA_IT : stateT nat (optionT (itree Nondeterminism.nondetE)) unit :=
  put 42 ;;
  s <- get ;;
  b <- lift (lift (ITree.trigger Nondeterminism.Or)) ;;
  if b : bool then put s else put (s + 1).

Lemma progA_IT_tree (s : nat) :
  eutt eq (unOptionT (runStateT progA_IT s))
    (ITree.bind (ITree.trigger Nondeterminism.Or)
       (fun b : bool => Ret (Some (tt, if b then 42 else 43)))).
Proof.
  cbn. rewrite Eqit.bind_ret_l. cbn [unOptionT runStateT].
  rewrite Eqit.bind_ret_l. cbn [unOptionT runStateT].
  rewrite !Eqit.bind_bind. apply eutt_eq_bind. intro b.
  rewrite !Eqit.bind_ret_l. cbn [unOptionT runStateT].
  destruct b; reflexivity.
Qed.

Lemma progA_IT_out (s : nat) (o : option (option (unit * nat))) :
  outStExc (@denoteStExc _ _ nat unit progA_IT) s o
  <-> o = Some (Some (tt, 42)) \/ o = Some (Some (tt, 43)).
Proof.
  rewrite outStExc_denoteStExc.
  rewrite (eq1_outcomes _ _ (mm_proper denote_morphism _ _ (progA_IT_tree s)) o).
  rewrite denote_bind. unfold ITree.trigger. split.
  - intros [[b|] [Hb Ho]].
    + apply denote_ret in Ho. destruct b; [ left | right ]; exact Ho.
    + apply denote_vis in Hb. destruct Hb as [x Hx]. apply denote_ret in Hx. discriminate.
  - intros [-> | ->]; [ exists (Some true) | exists (Some false) ];
      (split; [ apply denote_vis; eexists; apply denote_ret; reflexivity
              | apply denote_ret; reflexivity ]).
Qed.

(** Every run of [progA_IT] terminates with a state of at least [42]. *)
Theorem progA_IT_dwp_under :
  triple (@dwpStExc nat ∘ₘₘ @denoteStExc _ _ nat) progA_IT Under
    (fun _ => True)
    (fun r => match r with Some (_, s) => s >= 42 | None => False end).
Proof.
  intros s _. apply (proj2 (dwpStExc_read _ s _)). intros o Ho.
  apply progA_IT_out in Ho. destruct Ho as [-> | ->]; cbn; lia.
Qed.

(** The state [42] is reached: an incorrectness triple. *)
Theorem progA_IT_asp_under :
  triple (@aspStExc nat ∘ₘₘ @denoteStExc _ _ nat) progA_IT Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  intros r ->. apply (proj2 (aspStExc_read _ (fun _ : nat => True) _)).
  exists 0. split; [ exact I | apply progA_IT_out; left; reflexivity ].
Qed.
