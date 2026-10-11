(** * Programs typed in the Dijkstra monads

    The programs are those of [Triples/Examples.v], with state and
    exceptions.

    - One typed program for each of the eight WP Dijkstra monads, for ASP
      [Over] and for DSLP [Under].  Each is the triple proved in
      [Triples/Examples.v], read as a typing.

    - ASP [Under] and DSLP [Over], where triple and typing differ.  A typing
      at [aspUnder] says every start state in the precondition reaches every
      result in the postcondition, which is more than the triple says:
      [progA_Dasp_op] is such a typing.  And a triple need not be a typing:
      [progloom_harder] satisfies the ASP [Under] triple for the raise from
      a positive balance, since an even balance raises, but an odd one does
      not, so it is not typed at [aspUnder]
      ([progloom_harder_not_Dasp_op]).  The DSLP [Over] examples are the
      same two at the complements.

    - Without state the ASP [Under] triple is a typing:
      [oneOrTwo_Dasp_op]. *)

From Coq Require Import Lia PeanoNat Classical_Prop.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Computation Require Import
  DivNonDetNE.
From Incorrectness.Relational Require Import Rel.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.WP Require Import
  WPureMonad.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad.
From Incorrectness.Triples Require Import Triple MonadMorphisms Examples.
From Incorrectness.Dijkstra Require Import DijkstraMonad.

(* ================================================================= *)
(** * WP: the eight Dijkstra monads                                   *)
(* ================================================================= *)

Definition progA_Ddwp :
  Ddwp (wpUnderStExc (fun _ : nat => True)
          (fun r : option (unit * nat) =>
             match r with Some (_, s) => s >= 42 | None => False end)) :=
  exist _ progA
    (proj1 (triple_under_wpStExc (@dwpStExc nat) progA _ _) progA_dwp_under).

Definition progRet_Ddwp_op : Ddwp_op (wpOverStExc preEq0 postEq0) :=
  exist _ progRet
    (proj1 (triple_over_wpStExc (@dwpStExc nat) progRet _ _) progRet_dwp_over).

Definition progB_Ddwlp :
  Ddwlp (wpUnderStExc (fun _ : nat => True)
           (fun r : option (unit * nat) =>
              match r with Some (_, s) => s = 42 | None => False end)) :=
  exist _ progB
    (proj1 (triple_under_wpStExc (@dwlpStExc nat) progB _ _) progB_dwlp_under).

Definition progRet_Ddwlp_op : Ddwlp_op (wpOverStExc preEq0 postEq0) :=
  exist _ progRet
    (proj1 (triple_over_wpStExc (@dwlpStExc nat) progRet _ _)
       progRet_dwlp_over).

Definition progA_Dawp :
  Dawp (wpUnderStExc (fun _ : nat => True)
          (fun r : option (unit * nat) => r = Some (tt, 42))) :=
  exist _ progA
    (proj1 (triple_under_wpStExc (@awpStExc nat) progA _ _) progA_awp_under).

Definition progA_Dawp_op :
  Dawp_op (wpOverStExc (fun _ : nat => False)
             (fun r : option (unit * nat) => r = Some (tt, 100))) :=
  exist _ progA
    (proj1 (triple_over_wpStExc (@awpStExc nat) progA _ _) progA_awp_over).

Definition progB_Dawlp :
  Dawlp (wpUnderStExc (fun _ : nat => True)
           (fun _ : option (unit * nat) => False)) :=
  exist _ progB
    (proj1 (triple_under_wpStExc (@awlpStExc nat) progB _ _) progB_awlp_under).

Definition progRet_Dawlp_op : Dawlp_op (wpOverStExc preEq0 postEq0) :=
  exist _ progRet
    (proj1 (triple_over_wpStExc (@awlpStExc nat) progRet _ _)
       progRet_awlp_over).

(** The operations type a program built by [ret] and [bind] at the index
    built the same way. *)
Definition ret_Ddwp : @Ddwp nat unit (ret tt) :=
  DM_ret (@dwpStExc nat) (@ordWStExc nat) tt.

Definition put_get_Dawp :
  @Dawp nat nat (bind (awpStExc (put 42)) (fun _ => awpStExc get)) :=
  DM_bind (@awpStExc nat) (@ordWStExc nat)
    (DM_lift (@awpStExc nat) (@ordWStExc nat) (put 42))
    (fun _ => DM_lift (@awpStExc nat) (@ordWStExc nat) get).

(* ================================================================= *)
(** * SP: ASP [Over] and DSLP [Under]                                 *)
(* ================================================================= *)

Definition progA_Dasp :
  Dasp (aspOver (fun _ : unit * nat => True)
          (fun r : option (unit * nat) =>
             match r with Some (_, s') => s' >= 42 | None => False end)) :=
  exist _ progA
    (proj1 (triple_over_aspStExc (@aspStExc nat) progA _ _) progA_asp_over).

Definition progEx_Ddslp_op :
  Ddslp_op (dslpUnder (fun us : unit * nat => preEq0 (snd us))
              (fun r : option (unit * nat) => r = Some (tt, 1))) :=
  exist _ progEx
    (proj1 (triple_under_dslpStExc (@dslpStExc nat) progEx _ _)
       progEx_dslp_under).

(* ================================================================= *)
(** * ASP [Under]                                                     *)
(* ================================================================= *)

(** Typed, and saying more than the triple [progA_asp_under]: every start
    state reaches [(tt, 42)]. *)
Lemma progA_asp_under_typing :
  ordASPStExc
    (aspUnder (fun _ : unit * nat => True)
       (fun r : option (unit * nat) => r = Some (tt, 42)))
    (aspStExc progA).
Proof.
  refine (proj2 (le_aspUnder _ _
                   (fun us r => outStExc progA (snd us) (Some r))) _).
  intros [[] s] r _ Hr. subst r.
  apply (proj2 (progA_out s _)). left. reflexivity.
Qed.

Definition progA_Dasp_op :
  Dasp_op (aspUnder (fun _ : unit * nat => True)
             (fun r : option (unit * nat) => r = Some (tt, 42))) :=
  exist _ progA progA_asp_under_typing.

(** A triple that is not a typing.  [progloom_harder_asp_under]
    ([Triples/Examples.v]) is the triple: the raise is reached from some
    positive balance.  It is not reached from every positive balance. *)
Theorem progloom_harder_not_Dasp_op :
  ~ ordASPStExc
      (aspUnder (fun us : unit * nat => snd us > 0)
         (fun r : option (unit * nat) => r = None))
      (aspStExc progloom_harder).
Proof.
  intro H.
  pose proof (proj1 (le_aspUnder (fun us : unit * nat => snd us > 0)
                       (fun r : option (unit * nat) => r = None)
                       (fun us r => outStExc progloom_harder (snd us) (Some r)))
                H (tt, 1) None (le_n 1) eq_refl) as Hr.
  destruct (proj1 (progloom_harder_out 1 _) Hr) as [n Hn].
  cbn in Hn. discriminate Hn.
Qed.

(* ================================================================= *)
(** * DSLP [Over]                                                     *)
(* ================================================================= *)

(** Typed, and saying more than the triple [progA_dslp_over]: every start
    state other than [0] reaches [(tt, 42)]. *)
Lemma progA_dslp_over_typing :
  ordDSLPStExc (dslpStExc progA)
    (dslpOver (fun us : unit * nat => preEq0 (snd us))
       (fun r : option (unit * nat) => r <> Some (tt, 42))).
Proof.
  refine (proj2 (dslpOver_le _ _
                   (fun us r => outStExc progA (snd us) (Some r))) _).
  intros [[] s] r _ HQ. apply NNPP in HQ. subst r.
  apply (proj2 (progA_out s _)). left. reflexivity.
Qed.

Definition progA_Ddslp :
  Ddslp (dslpOver (fun us : unit * nat => preEq0 (snd us))
           (fun r : option (unit * nat) => r <> Some (tt, 42))) :=
  exist _ progA progA_dslp_over_typing.

(** A triple that is not a typing: every result all of whose start states
    have balance [0] is a normal return, because the raise is reached from
    the balance [2]. *)
Theorem progloom_harder_dslp_over :
  triple (@dslpStExc nat) progloom_harder Over
    (fun balance => balance = 0) (fun r => r <> None).
Proof.
  intros r Hd E. subst r.
  assert (H2 : outStExc progloom_harder 2 (Some None)).
  { apply (proj2 (progloom_harder_out 2 _)). exists 0. reflexivity. }
  pose proof (Hd (tt, 2) H2) as E2. cbn in E2. discriminate E2.
Qed.

(** But the raise is not reached from every balance other than [0]. *)
Theorem progloom_harder_not_Ddslp :
  ~ ordDSLPStExc (dslpStExc progloom_harder)
      (dslpOver (fun us : unit * nat => snd us = 0)
         (fun r : option (unit * nat) => r <> None)).
Proof.
  intro H.
  pose proof (proj1 (dslpOver_le (fun us : unit * nat => snd us = 0)
                       (fun r : option (unit * nat) => r <> None)
                       (fun us r => outStExc progloom_harder (snd us) (Some r)))
                H (tt, 1) None) as Hr.
  assert (Hr' : outStExc progloom_harder 1 (Some None)).
  { apply Hr.
    - intro E. cbn in E. discriminate E.
    - intro Hn. exact (Hn eq_refl). }
  destruct (proj1 (progloom_harder_out 1 _) Hr') as [n Hn].
  cbn in Hn. discriminate Hn.
Qed.

(* ================================================================= *)
(** * Without state                                                   *)
(* ================================================================= *)

(** A computation with no state that returns [1] or [2]. *)
Definition oneOrTwo : divndNE nat := orNE (retNE 1) (retNE 2).

Theorem oneOrTwo_asp_under :
  triple (@aspPure) oneOrTwo Under (fun _ => True) (fun a => a = 1).
Proof.
  intros a Ha. subst a. exists tt. split; [ exact I |].
  cbn. left. reflexivity.
Qed.

(** The triple is a typing: there is one start point. *)
Definition oneOrTwo_Dasp_op :
  DMop (@aspPure) (@ordASP)
    (aspUnder (fun _ : unit => True) (fun a : nat => a = 1)) :=
  exist _ oneOrTwo
    (proj1 (triple_under_aspPure (@aspPure) oneOrTwo _ _ I)
       oneOrTwo_asp_under).
