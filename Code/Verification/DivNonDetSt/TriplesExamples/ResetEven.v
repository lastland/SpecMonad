(** * Reset an even state, maybe (paper, Section 5)

    The program [m], written in [stdivndNE nat]: from an even state it
    either resets the state to [0] or keeps it, from an odd state it keeps
    it.  It never diverges ([m_out]).  The file computes its AWP and ASP
    images ([awp_m], [asp_m]) and, for [p := s > 0], [q := s' = 0] and
    [p' := s > 0 /\ s even], shows that the Lisbon triple [[p] m [q]] fails
    ([lisbon_p_q_fails]) while the incorrectness triple holds
    ([incorr_p_q]); with [p'] both hold.  The AWP specification [wspec]
    types [m] in the Dijkstra monad of [awpSt] ([m_DM]) and is the
    embedding of the pair [(p', q)], so typing against it is the Lisbon
    triple ([le_wspec_iff_lisbon]).

    [ordWSt (θ m) w] says that [w post s] implies [θ m post s]. *)

From Coq Require Import Arith Lia.
From ExtLib Require Import Monad MonadState StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad TransformerLaws.
From Incorrectness.WP Require Import WPure.
From Incorrectness.SP Require Import ASPMonad.
From Incorrectness.Verification.Generic Require Import Triple DijkstraMonad.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Triples.
From Incorrectness.Verification.DivNonDetSt Require Import Typings.
From Incorrectness.Verification.DivNonDetSt Require Import DijkstraMonads.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** * The program                                                     *)
(* ================================================================= *)

(** [m s = {(tt, 0), (tt, s)}] if [s] is even, [{(tt, s)}] otherwise. *)
Definition m : stdivndNE nat unit :=
  s <- get ;;
  if Nat.even s then orSt (put 0) (ret tt) else ret tt.

Lemma m_out (s : nat) (o : option (unit * nat)) :
  outSt m s o <-> o = Some (tt, s) \/ (Nat.Even s /\ o = Some (tt, 0)).
Proof.
  unfold m. rewrite outSt_bind. split.
  - intros [o1 [H1 H2]]. apply (proj1 (outSt_get s o1)) in H1. subst o1.
    destruct (Nat.even s) eqn:E.
    + apply outSt_or in H2. destruct H2 as [H2 | H2].
      * apply outSt_put in H2. right. split; [ apply Nat.even_spec, E | exact H2 ].
      * apply outSt_ret in H2. left. exact H2.
    + apply outSt_ret in H2. left. exact H2.
  - intro H. exists (Some (s, s)). split; [ apply outSt_get; reflexivity |].
    destruct H as [-> | [He ->]].
    + destruct (Nat.even s); [ apply outSt_or; right |]; apply outSt_ret; reflexivity.
    + apply Nat.even_spec in He. rewrite He.
      apply outSt_or. left. apply outSt_put. reflexivity.
Qed.

Lemma m_out_some (s : nat) (r : unit * nat) :
  outSt m s (Some r) <-> snd r = s \/ (Nat.Even s /\ snd r = 0).
Proof.
  destruct r as [[] s']. rewrite m_out. cbn.
  split; (intros [H | [He H]]; [ left | right; split; [ exact He |] ]);
    congruence.
Qed.

(* ================================================================= *)
(** * Its AWP and ASP images                                          *)
(* ================================================================= *)

Theorem awp_m (post : unit * nat -> Prop) (s : nat) :
  getWPure (runStateT (awpSt m) s) post
  <-> post (tt, s) \/ (Nat.Even s /\ post (tt, 0)).
Proof.
  rewrite awpSt_read. split.
  - intros [o [Ho Hp]]. apply m_out in Ho.
    destruct Ho as [-> | [He ->]]; [ left | right ]; auto.
  - intros [Hp | [He Hp]]; [ exists (Some (tt, s)) | exists (Some (tt, 0)) ];
      (split; [ apply m_out; auto | exact Hp ]).
Qed.

Theorem asp_m (pre : nat -> Prop) (r : unit * nat) :
  getASPSt (aspSt m) pre r
  <-> pre (snd r) \/ (snd r = 0 /\ exists s, Nat.Even s /\ pre s).
Proof.
  unfold getASPSt. rewrite aspSt_read. split.
  - intros [s [Hp Hr]]. apply m_out_some in Hr.
    destruct Hr as [E | [He E]].
    + left. rewrite E. exact Hp.
    + right. split; [ exact E |]. exists s. auto.
  - intros [Hp | [E [s [He Hp]]]].
    + exists (snd r). split; [ exact Hp | apply m_out_some; left; reflexivity ].
    + exists s. split; [ exact Hp | apply m_out_some; right; auto ].
Qed.

(* ================================================================= *)
(** * Triples                                                         *)
(* ================================================================= *)

Definition p  (s : nat) : Prop := s > 0.
Definition p' (s : nat) : Prop := s > 0 /\ Nat.Even s.
Definition q  (r : unit * nat) : Prop := snd r = 0.

Lemma even_0 : Nat.Even 0.
Proof. exists 0. reflexivity. Qed.

Theorem awp_m_q (s : nat) :
  getWPure (runStateT (awpSt m) s) q <-> Nat.Even s.
Proof.
  rewrite awp_m. unfold q. cbn. split.
  - intros [-> | [He _]]; [ exact even_0 | exact He ].
  - intro He. right. auto.
Qed.

Theorem asp_m_p (r : unit * nat) : getASPSt (aspSt m) p r <-> True.
Proof.
  rewrite asp_m. unfold p. split; [ intros _; exact I | intros _ ].
  destruct (snd r) as [| n] eqn:E.
  - right. split; [ reflexivity |]. exists 2. split; [ exists 1; reflexivity | lia ].
  - left. lia.
Qed.

Theorem asp_m_p' (r : unit * nat) : getASPSt (aspSt m) p' r <-> Nat.Even (snd r).
Proof.
  rewrite asp_m. unfold p'. split.
  - intros [[_ He] | [-> _]]; [ exact He | exact even_0 ].
  - intro He. destruct (snd r) as [| n] eqn:E.
    + right. split; [ reflexivity |]. exists 2.
      assert (H2 : Nat.Even 2) by (exists 1; reflexivity).
      split; [ exact H2 | split; [ lia | exact H2 ] ].
    + left. split; [ lia | exact He ].
Qed.

(** The start state [1] satisfies [p] but cannot reach [q]. *)
Theorem lisbon_p_q_fails : ~ LisbonLogic p m q.
Proof.
  intro H. assert (He : p 1) by (unfold p; lia).
  apply H, awp_m_q, Nat.even_spec in He. discriminate He.
Qed.

Theorem incorr_p_q : IncorrLogic p m q.
Proof. intros r _. apply asp_m_p. exact I. Qed.

(** With [p'], both hold. *)
Theorem lisbon_p'_q : LisbonLogic p' m q.
Proof. intros s [_ He]. apply awp_m_q. exact He. Qed.

Theorem incorr_p'_q : IncorrLogic p' m q.
Proof. intros r Hq. apply asp_m_p'. rewrite Hq. exact even_0. Qed.

(* ================================================================= *)
(** * A predicate-transformer specification                           *)
(* ================================================================= *)

#[program] Definition wspec : WSt nat unit :=
  mkStateT (fun s =>
    mkWPure (fun post => s > 0 /\ Nat.Even s /\ post (tt, 0)) _).
Next Obligation. intros k1 k2 Hk [H1 [H2 H3]]. auto. Qed.

(** By the reset branch: [wspec] only accepts even start states. *)
Theorem awp_m_le_wspec : ordWSt (awpSt m) wspec.
Proof. intros s post [_ [He Hp]]. apply awp_m. right. auto. Qed.

(** [m] in the Dijkstra monad of [awpSt], at index [wspec]. *)
Definition m_DM : DM (@awpSt nat) (@ordWSt nat) wspec :=
  exist _ m awp_m_le_wspec.

Theorem wspec_pp2wp : @eq1 (WSt nat) (Eq1__WSt nat) unit wspec (wpUnderSt p' q).
Proof.
  intros s post. cbn. unfold p', q. split.
  - intros [H1 [H2 H3]]. split; [ auto |]. intros [[] s'] E. cbn in E. subst s'.
    exact H3.
  - intros [[H1 H2] H3]. split; [ exact H1 | split; [ exact H2 |] ].
    apply H3. reflexivity.
Qed.

(** So typing against [wspec] is the Lisbon triple for [(p', q)]. *)
Theorem le_wspec_iff_lisbon (m0 : stdivndNE nat unit) :
  ordWSt (awpSt m0) wspec <-> LisbonLogic p' m0 q.
Proof.
  rewrite (triple_under_wpSt (@awpSt nat) m0 p' q).
  split; intros H s k Hk; apply (H s k), (wspec_pp2wp s k); exact Hk.
Qed.
