(** * Sequencing DSP and ASLP triples: counterexamples (paper, Section 5)

    Over-approximate DSP triples and under-approximate ASLP triples do not
    compose, with the side condition in either direction
    ([dspSt_over_seq_counterexample], [aslpSt_under_seq_counterexample]).
    The two computations are those of the paper's sequencing figure, on the
    states [1]-[4], with a sink state [0] for the other start states:

      [m1]   1 ↦ 2,  every other state ↦ 0
      [f1]   2 ↦ 4,  3 ↦ 4,  every other state ↦ 0

    Both are deterministic and total, so the failure does not come from
    divergence or nondeterminism.  The first computation never produces
    state [3], which the intermediate assertions cannot say.

    The last two sections show that the under-approximate ASP rule of
    [TripleRules.v] needs its side condition in the stated direction, the
    opposite of the WP rule's ([side_aspSt_under]), and an inhabited
    returned type ([inhabited_aspSt_under]). *)

From Coq Require Import Arith Bool.
From ExtLib Require Import Monad MonadState StateMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Triples.
From Incorrectness.Verification.DivNonDetSt Require Import TripleRules.

(* ================================================================= *)
(** * The two computations                                            *)
(* ================================================================= *)

(** Replace the state by a function of it. *)
Definition setSt (g : nat -> nat) : stdivndNE nat unit :=
  bind get (fun s => put (g s)).

Lemma outSt_setSt (g : nat -> nat) (s : nat) (o : option (unit * nat)) :
  outSt (setSt g) s o <-> o = Some (tt, g s).
Proof.
  unfold setSt. rewrite outSt_bind. split.
  - intros [o1 [H1 H2]]. apply (proj1 (outSt_get s o1)) in H1. subst o1.
    exact (proj1 (outSt_put (g s) s o) H2).
  - intro H. exists (Some (s, s)).
    split; [ exact (proj2 (outSt_get s _) eq_refl) |].
    exact (proj2 (outSt_put (g s) s o) H).
Qed.

Definition g1 (s : nat) : nat := if s =? 1 then 2 else 0.
Definition g2 (s : nat) : nat := if (s =? 2) || (s =? 3) then 4 else 0.

(** The first computation, and the continuation. *)
Definition m1 : stdivndNE nat unit := setSt g1.
Definition f1 (_ : unit) : stdivndNE nat unit := setSt g2.

Lemma outSt_m1 (s : nat) (r : unit * nat) :
  outSt m1 s (Some r) <-> r = (tt, g1 s).
Proof.
  etransitivity; [ exact (outSt_setSt g1 s (Some r)) |].
  split; intro H; [ injection H; auto | subst r; reflexivity ].
Qed.

Lemma outSt_f1 (a : unit) (s : nat) (r : unit * nat) :
  outSt (f1 a) s (Some r) <-> r = (tt, g2 s).
Proof.
  etransitivity; [ exact (outSt_setSt g2 s (Some r)) |].
  split; intro H; [ injection H; auto | subst r; reflexivity ].
Qed.

Lemma outSt_m1f1 (s : nat) (r : unit * nat) :
  outSt (bind m1 f1) s (Some r) <-> r = (tt, g2 (g1 s)).
Proof.
  rewrite outSt_bind_Some. split.
  - intros [a [s' [H1 H2]]]. apply outSt_m1 in H1. apply outSt_f1 in H2.
    injection H1 as _ H1. subst s'. exact H2.
  - intro H. exists tt, (g1 s). split.
    + apply outSt_m1. reflexivity.
    + apply outSt_f1. exact H.
Qed.

(** Through the sequence, state [4] is reached from [1] only. *)
Lemma g2g1_4 (s : nat) : g2 (g1 s) = 4 <-> s = 1.
Proof.
  unfold g1. destruct (Nat.eqb_spec s 1); cbn; split; intro H;
    solve [ auto | discriminate H | contradiction ].
Qed.

(** The readings used below. *)
Lemma dspSt_over_iff {A} (m : stdivndNE nat A) (P : nat -> Prop)
  (Q : A * nat -> Prop) :
  triple (@dspSt nat) m Over P Q
  <-> forall r, (exists s, P s /\ outSt m s (Some r))
               /\ (forall s, outSt m s (Some r) -> P s) -> Q r.
Proof.
  split; intros H r Hr; apply H.
  - exact (proj2 (dspSt_read m P r) Hr).
  - exact (proj1 (dspSt_read m P r) Hr).
Qed.

Lemma aslpSt_under_iff {A} (m : stdivndNE nat A) (P : nat -> Prop)
  (Q : A * nat -> Prop) :
  triple (@aslpSt nat) m Under P Q
  <-> forall r, Q r -> (exists s, P s /\ outSt m s (Some r))
                     \/ (forall s, outSt m s (Some r) -> P s).
Proof.
  split; intros H r Hr.
  - exact (proj1 (aslpSt_read m P r) (H r Hr)).
  - exact (proj2 (aslpSt_read m P r) (H r Hr)).
Qed.

(* ================================================================= *)
(** * (a) Over-approximate DSP triples do not compose                 *)
(* ================================================================= *)

(** [p = {1}], [q0 = pa = {2}], [q = ∅].  From [pa], [f1] proves only the
    empty postcondition, since state [4] is also reached from [3], outside
    [pa].  In the sequence, [4] is reached only from [1], inside [p]. *)
Section DSPCounterexample.
  Let p : nat -> Prop := fun s => s = 1.
  Let q0 : unit * nat -> Prop := fun r => snd r = 2.
  Let pa : unit -> nat -> Prop := fun _ s => s = 2.
  Let q : unit * nat -> Prop := fun _ => False.

  Theorem dspSt_over_seq_counterexample :
    triple (@dspSt nat) m1 Over p q0
    /\ (forall a, triple (@dspSt nat) (f1 a) Over (pa a) q)
    /\ (forall a s, q0 (a, s) <-> pa a s)
    /\ ~ triple (@dspSt nat) (bind m1 f1) Over p q.
  Proof.
    split; [| split; [| split ] ].
    - apply dspSt_over_iff. intros r [[s [Hs Hr]] _]. unfold p in Hs.
      apply outSt_m1 in Hr. subst s r. reflexivity.
    - intro a. apply dspSt_over_iff. intros r [[s [Hs Hr]] Hall]. unfold pa in Hs.
      apply outSt_f1 in Hr. subst s r.
      discriminate (Hall 3 (proj2 (outSt_f1 a 3 _) eq_refl)).
    - reflexivity.
    - intro H. apply (proj1 (dspSt_over_iff _ p q) H (tt, 4)). split.
      + exists 1. split; [ reflexivity |]. apply outSt_m1f1. reflexivity.
      + intros s Hs. apply outSt_m1f1 in Hs. injection Hs as Hs.
        exact (proj1 (g2g1_4 s) (eq_sym Hs)).
  Qed.
End DSPCounterexample.

(* ================================================================= *)
(** * (b) Under-approximate ASLP triples do not compose               *)
(* ================================================================= *)

(** The complements of the assertions of (a): [p = ¬{1}], [q0 = pa = ¬{2}],
    [q] everything.  State [4] is reached by [f1] from [3], inside [pa], but
    in the sequence only from [1], outside [p]. *)
Section ASLPCounterexample.
  Let p : nat -> Prop := fun s => s <> 1.
  Let q0 : unit * nat -> Prop := fun r => snd r <> 2.
  Let pa : unit -> nat -> Prop := fun _ s => s <> 2.
  Let q : unit * nat -> Prop := fun _ => True.

  Theorem aslpSt_under_seq_counterexample :
    triple (@aslpSt nat) m1 Under p q0
    /\ (forall a, triple (@aslpSt nat) (f1 a) Under (pa a) q)
    /\ (forall a s, q0 (a, s) <-> pa a s)
    /\ ~ triple (@aslpSt nat) (bind m1 f1) Under p q.
  Proof.
    split; [| split; [| split ] ].
    - apply aslpSt_under_iff. intros r Hr. right. intros s Hs ->.
      apply outSt_m1 in Hs. subst r. exact (Hr eq_refl).
    - intro a. apply aslpSt_under_iff. intros [u s'] _.
      destruct (Nat.eq_dec s' 4) as [-> | Hne].
      + left. exists 3. split; [ discriminate |].
        apply outSt_f1. destruct u. reflexivity.
      + right. intros s Hs ->. apply outSt_f1 in Hs. injection Hs as _ Hs.
        exact (Hne Hs).
    - reflexivity.
    - intro H. destruct (proj1 (aslpSt_under_iff _ p q) H (tt, 4) I)
        as [[s [Hs Hr]] | Hall].
      + apply outSt_m1f1 in Hr. injection Hr as Hr.
        exact (Hs (proj1 (g2g1_4 s) (eq_sym Hr))).
      + exact (Hall 1 (proj2 (outSt_m1f1 1 _) eq_refl) eq_refl).
  Qed.
End ASLPCounterexample.

(* ================================================================= *)
(** * The direction of the side condition                             *)
(* ================================================================= *)

(** With the WP rule's side condition [Q0 (a, s) -> Pa a s], the
    under-approximate ASP rule fails.  Both computations are [skip]. *)
Definition skipSt : stdivndNE nat unit := ret tt.

Lemma outSt_skip2 (s : nat) (r : unit * nat) :
  outSt (bind skipSt (fun _ => skipSt)) s (Some r) <-> r = (tt, s).
Proof.
  rewrite outSt_bind_Some. split.
  - intros [a [s' [H1 H2]]].
    apply outSt_ret in H1, H2.
    injection H1 as _ ->. injection H2 as ->. reflexivity.
  - intros ->. exists tt, s. split; apply outSt_ret; reflexivity.
Qed.

Section SideUnder.
  Let p : nat -> Prop := fun s => s = 1.
  Let q0 : unit * nat -> Prop := fun r => snd r = 1.
  Let pa : unit -> nat -> Prop := fun _ _ => True.
  Let q : unit * nat -> Prop := fun r => snd r = 2.

  Theorem side_aspSt_under :
    triple (@aspSt nat) skipSt Under p q0
    /\ (forall a, triple (@aspSt nat) skipSt Under (pa a) q)
    /\ (forall a s, q0 (a, s) -> pa a s)
    /\ ~ triple (@aspSt nat) (bind skipSt (fun _ => skipSt)) Under p q.
  Proof.
    split; [| split; [| split ] ].
    - intros [[] s] Hs. exists (tt, s). split; [ exact Hs | reflexivity ].
    - intros a [[] s] _. exists (tt, s). split; [ exact I | reflexivity ].
    - intros; exact I.
    - intro H. destruct (proj1 (aspSt_read _ p (tt, 2)) (H (tt, 2) eq_refl))
        as [s [Hs Hr]].
      apply outSt_skip2 in Hr. injection Hr as <-. discriminate Hs.
  Qed.
End SideUnder.

(* ================================================================= *)
(** * An inhabited returned type                                      *)
(* ================================================================= *)

(** With an empty returned type the premise on the continuation is
    vacuous, and the under-approximate ASP rule fails.  The first
    computation diverges. *)
Section Inhabited.
  Let m0 : stdivndNE unit Empty_set := divergeSt.
  Let f0 (e : Empty_set) : stdivndNE unit unit := match e with end.

  Let p : unit -> Prop := fun _ => True.
  Let q0 : Empty_set * unit -> Prop := fun _ => False.
  Let pa : Empty_set -> unit -> Prop := fun _ _ => True.

  Theorem inhabited_aspSt_under :
    triple (@aspSt unit) m0 Under p q0
    /\ (forall a, triple (@aspSt unit) (f0 a) Under (pa a) (fun _ => True))
    /\ (forall a s, pa a s -> q0 (a, s))
    /\ ~ triple (@aspSt unit) (bind m0 f0) Under p (fun _ => True).
  Proof.
    split; [| split; [| split ] ].
    - intros [[] _].
    - intros [].
    - intros [].
    - intro H. destruct (proj1 (aspSt_read _ p (tt, tt)) (H (tt, tt) I))
        as [s [_ Hr]].
      apply outSt_bind_Some in Hr. destruct Hr as [[] _].
  Qed.
End Inhabited.
