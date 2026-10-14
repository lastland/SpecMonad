(** * Programs as interaction trees

    Programs written with the ITree library's definitions, over its
    nondeterministic choice [nondetE] ([Nondeterminism.or], [ITree.spin]),
    and verified through [denote]:

      [oneOrTwoIT]      a choice between returning [1] and [2];
      [ITree.spin]      the silent loop: DWLP accepts it, DWP rejects it. *)

From ExtLib Require Import Monad OptionMonad.
From ITree Require Import ITree.
From ITree Require Events.Nondeterminism.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDet Require Import Morphisms.
From Incorrectness.Verification.DivNonDet Require Import Triples.

(* ================================================================= *)
(** * A choice                                                        *)
(* ================================================================= *)

Definition oneOrTwoIT : itree Nondeterminism.nondetE nat := Nondeterminism.or (Ret 1) (Ret 2).

Lemma oneOrTwoIT_out (o : option nat) :
  unOptionT (getNE (denote oneOrTwoIT)) o <-> o = Some 1 \/ o = Some 2.
Proof. unfold oneOrTwoIT. rewrite denote_or, !denote_ret. reflexivity. Qed.

(** Every run returns [1] or [2]. *)
Theorem oneOrTwoIT_dwp_under :
  triple (@dwpPure ∘ₘₘ @denote _ _) oneOrTwoIT Under (fun _ => True) (fun a => a = 1 \/ a = 2).
Proof.
  intros [] _. apply (proj2 (dwpPure_read _ _)). intros o Ho.
  apply oneOrTwoIT_out in Ho. destruct Ho as [-> | ->]; [ left | right ]; reflexivity.
Qed.

(** The result [1] is reached: an incorrectness triple. *)
Theorem oneOrTwoIT_asp_under :
  triple (@aspPure ∘ₘₘ @denote _ _) oneOrTwoIT Under (fun _ => True) (fun a => a = 1).
Proof.
  intros a ->. apply (proj2 (aspPure_read _ _ _)).
  split; [ exact I | apply oneOrTwoIT_out; left; reflexivity ].
Qed.

(* ================================================================= *)
(** * The silent loop                                                 *)
(* ================================================================= *)

Theorem spin_not_dwp (P : unit -> Prop) (Q : unit -> Prop) :
  P tt -> ~ triple (@dwpPure ∘ₘₘ @denote _ _) (ITree.spin : itree Nondeterminism.nondetE unit) Under P Q.
Proof.
  intros Hp H.
  exact (proj1 (dwpPure_read _ _) (H tt Hp) None (proj2 (denote_spin None) eq_refl)).
Qed.

Theorem spin_dwlp (P : unit -> Prop) (Q : unit -> Prop) :
  triple (@dwlpPure ∘ₘₘ @denote _ _) (ITree.spin : itree Nondeterminism.nondetE unit) Under P Q.
Proof.
  intros [] _. apply (proj2 (dwlpPure_read _ _)).
  intros o Ho. apply denote_spin in Ho. subst o. exact I.
Qed.
