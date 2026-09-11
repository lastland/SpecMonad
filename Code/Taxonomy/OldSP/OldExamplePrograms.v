(** * Old-style example programs and triples

    The example theorems stated over the earlier [tripleSP] / [obsASP]
    presentation of [OldSPObservations.v].  Split out of
    [Taxonomy/ExamplePrograms.v], which retains the [tripleASP] / [tripleDSP]
    and WP versions — the two families used the same theorem names, so they
    could not live in one file. *)

From ExtLib Require Import MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.Arrows Require Import RelSPPairArr.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.
From Incorrectness.Taxonomy.OldSP Require Import OldSPObservations.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** O'Hearn's Example 3.1, ported to [stdivexcnd] / [tripleSP obsASP] *)
(* ================================================================= *)

(** A port of [ST/PredArr.v]'s [OHearnExample] module.  The original
    operates on the pure state monad [state S A := S -> A * S] with a
    bespoke [Incorrect] predicate (reachability of a final state from
    some initial state).  Here we use [stdivexcnd S A] (deterministic in
    this example) and [tripleSP obsASP _ Under].

    Program (O'Hearn, "Incorrectness Logic", Example 3.1): swap [z]
    with [42] when [x] is even and [y] is odd; otherwise leave the
    state alone. *)


(* ================================================================= *)
(** ** SP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

(** All reachable converging results have state >= 42. *)
Theorem progA_all :
  tripleSP obsASP progA Over
    (fun _ => True)
    (fun r =>
      match r with
      | Some (_, s') => s' >= 42
      | None => False
      end).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r [sigma [_ Hrel]].
  destruct r as [[[] s'] |]; cbn in Hrel; sauto.
Qed.

(** State 42 is reachable. *)
Theorem progA_42 :
  tripleSP obsASP progA Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r ->. exists 0. split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** State 43 is also reachable. *)
Theorem progA_43 :
  tripleSP obsASP progA Under
    (fun _ => True)
    (fun r => r = Some (tt, 43)).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r ->. exists 0. split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(* ================================================================= *)
(** ** Examples: nondeterminism + divergence                          *)
(* ================================================================= *)

(** State 42 is reachable (via the converging branch). *)
Theorem progB_42 :
  tripleSP obsASP progB Under
    (fun _ => True)
    (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r ->. exists 0. split; [exact I | unfold obsRel; cbn; sauto].
Qed.

(** Failure ([None]) is NOT reachable: the divergent branch does not
    contribute an exception, and divergence is the absence of reaching
    any final state. *)
Theorem progB_not_None :
  tripleSP obsASP progB Over
    (fun _ => True)
    (fun r => r <> None).
Proof.
  unfold tripleSP, obsASP, asp.
  intros r [sigma [_ Hrel]] ->. cbn in Hrel. sauto.
Qed.


(** The SP-Inc triple holds: state [0] reaches the only post-result. *)
Theorem progRet_asp_inc :
  tripleSP obsASP progRet Under preEq0 postEq0.
Proof.
  unfold tripleSP, obsASP, preEq0, postEq0.
  unfold asp, obsRel.
  intros r ->. exists 0. split; [reflexivity | cbn; reflexivity].
Qed.

(** The stronger DSP-Inc triple also holds: the unique reacher of
    [Some (tt, 0)] is the state [0] itself, which satisfies [preEq0]. *)
Theorem progRet_dsp_inc :
  tripleSP obsDSP progRet Under preEq0 postEq0.
Proof.
  unfold tripleSP, preEq0, postEq0.
  intros r ->. apply obsDSP_char. split.
  - exists 0. cbn. reflexivity.
  - intros s Hrel. cbn in Hrel. inversion Hrel. reflexivity.
Qed.

Definition P0 : nat -> Prop := fun s => s = 0.

(** -- Class 1: exclusively reachable from P — all four include it -- *)

#[program] Theorem progEx_asp_1 :
  (obsASP progEx) P0 (Some (tt, 1)).
Proof.
  unfold obsASP, P0. unfold asp.
  exists 0. split; [reflexivity|].
  unfold obsRel. cbn.
  sauto.
Qed.

#[program] Theorem progEx_dslp_1 :
  (obsDSLP progEx) P0 (Some (tt, 1)).
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intros s Hrel. unfold obsRel in Hrel. cbn in Hrel.
  f_equal. f_equal. sauto lq: on.
Qed.

Theorem progEx_dsp_1 :
  obsDSP progEx P0 (Some (tt, 1)).
Proof.
  split; [exact progEx_asp_1 | exact progEx_dslp_1].
Qed.

Theorem progEx_aslp_1 :
  obsASLP progEx P0 (Some (tt, 1)).
Proof. left. exact progEx_asp_1. Qed.

(** -- Class 2: reachable from P and ¬P — asp and aslp include,
       dsp and dslp exclude -- *)

#[program] Theorem progEx_asp_42 :
  (obsASP progEx) P0 (Some (tt, 42)).
Proof.
  unfold obsASP, P0. unfold asp.
  exists 0. split; [reflexivity|].
  unfold obsRel. cbn. sauto.
Qed.

#[program] Theorem progEx_dslp_not_42 :
  ~ (obsDSLP progEx) P0 (Some (tt, 42)).
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intro H. specialize (H 1).
  assert (Hreach : obsRel progEx 1 (Some (tt, 42))).
  { unfold obsRel. cbn. sauto. }
  specialize (H Hreach). simpl in H. discriminate.
Qed.

Theorem progEx_dsp_not_42 :
  ~ obsDSP progEx P0 (Some (tt, 42)).
Proof.
  intros [_ H]. exact (progEx_dslp_not_42 H).
Qed.

Theorem progEx_aslp_42 :
  obsASLP progEx P0 (Some (tt, 42)).
Proof. left. exact progEx_asp_42. Qed.

(** -- Class 3: unreachable — dslp and aslp include,
       asp and dsp exclude -- *)

#[program] Theorem progEx_asp_not_None :
  ~ (obsASP progEx) P0 None.
Proof.
  unfold obsASP, P0. unfold asp.
  intros [s [HP Hrel]].
  unfold obsRel in Hrel. cbn in Hrel. sauto.
Qed.

#[program] Theorem progEx_dslp_None :
  (obsDSLP progEx) P0 None.
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intros s Hrel.
  (** None (exception) is unreachable — the ∀ is vacuously true. *)
  unfold obsRel in Hrel. cbn in Hrel. sauto.
Qed.

Theorem progEx_dsp_not_None :
  ~ obsDSP progEx P0 None.
Proof.
  intros [H _]. exact (progEx_asp_not_None H).
Qed.

Theorem progEx_aslp_None :
  obsASLP progEx P0 None.
Proof. right. exact progEx_dslp_None. Qed.

(** -- Class 4: exclusively reachable from ¬P — none include -- *)

#[program] Theorem progEx_asp_not_99 :
  ~ (obsASP progEx) P0 (Some (tt, 99)).
Proof.
  unfold obsASP, P0. unfold asp.
  intros [s [HP Hrel]]. subst.
  unfold obsRel in Hrel. cbn in Hrel. sauto lq: on.
Qed.

#[program] Theorem progEx_dslp_not_99 :
  ~ (obsDSLP progEx) P0 (Some (tt, 99)).
Proof.
  unfold obsDSLP, P0. unfold dslp.
  intro H. specialize (H 98).
  assert (Hreach : obsRel progEx 98 (Some (tt, 99))).
  { unfold obsRel. cbn. sauto. }
  specialize (H Hreach). simpl in H. discriminate.
Qed.

Theorem progEx_dsp_not_99 :
  ~ obsDSP progEx P0 (Some (tt, 99)).
Proof. intros [H _]. exact (progEx_asp_not_99 H). Qed.

Theorem progEx_aslp_not_99 :
  ~ obsASLP progEx P0 (Some (tt, 99)).
Proof.
  intros [H | H]; [exact (progEx_asp_not_99 H) |
                    exact (progEx_dslp_not_99 H)].
Qed.

Module OHearnExample.
  
  (** First incorrectness triple (paper-style): from any state whose
      [z] component is [11], there is a final state in which [z = 42],
      [x] is even, and [y] is odd.  Note the SP-Incorrect reading: the
      triple asserts only that *some* such reachable result exists,
      not that every initial state reaches one. *)
  Theorem example_incorrect_1 :
    tripleSP obsASP example_state Under
      (fun '(x, _, z) => z = 11)
      (fun r =>
         match r with
         | Some (tt, (x, y, z)) =>
             z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
         | _ => False
         end).
  Proof.
    unfold tripleSP, obsASP.
    unfold asp, obsRel.
    intros [[[] [[x y] z]]|] H; [|contradiction].
    destruct H as [-> [Hx Hy]].
    exists (x, y, 11). split; [reflexivity|].
    cbn. eexists. split; [reflexivity|].
    cbn. rewrite Hx, Hy. reflexivity.
  Qed.

  (** Weaker incorrectness triple (vacuous precondition): from *some*
      initial state, the program reaches a final state with [z = 42].
      The original proof in [ST/PredArr.v] also leaves [x], [y], [z]
      unconstrained and exhibits any state with [x] even and [y]
      odd as the witness. *)
  Theorem example_incorrect_2 :
    tripleSP obsASP example_state Under
      (fun _ => True)
      (fun r =>
         match r with
         | Some (tt, (_, _, z)) => z = 42
         | _ => False
         end).
  Proof.
    unfold tripleSP, obsASP.
    unfold asp, obsRel.
    intros [[[] [[x y] z]]|] H; [|contradiction].
    cbn in H. subst z.
    (* Use the final state itself, [(x, y, 42)], as the initial witness:
       both branches preserve [x, y] and either keep [z = 42] (identity)
       or set it to [42] (put). *)
    exists (x, y, 42). split; [exact I|].
    cbn. eexists. split; [reflexivity|].
    cbn. destruct (Nat.even x); destruct (negb (Nat.even y)); reflexivity.
  Qed.

  (** Unprovable triple (paper-noted): from any state with [z = 11],
      the program reaches a final state with [z = 42].  This is
      [example_3_1_incorrect_unprovable] in [ST/PredArr.v]; we mirror
      its failure here.

      Refutation: pick [r = Some (tt, (1, 0, 42))] — it satisfies the
      postcondition (because the post only mentions [z = 42]), but no
      initial state with [z = 11] reaches it.  Indeed the program only
      modifies the state when [x] is even and [y] is odd, and even
      then it preserves the first two components; so reaching
      [(1, 0, 42)] would require starting from [(1, 0, 42)], whose
      [z]-component is [42], not [11]. *)
  Theorem example_incorrect_unprovable :
    ~ tripleSP obsASP example_state Under
        (fun '(_, _, z) => z = 11)
        (fun r =>
           match r with
           | Some (tt, (_, _, z)) => z = 42
           | _ => False
           end).
  Proof.
    intro H.
    specialize (H (Some (tt, (1, 0, 42))) eq_refl).
    destruct H as [[[x y] z] [Hpre Hrel]].
    cbn in Hpre. subst z.
    cbn in Hrel.
    destruct Hrel as [a [Ha Hrel]].
    subst a. cbn in Hrel.
    destruct (Nat.even x) eqn:Hx; destruct (negb (Nat.even y)) eqn:Hy;
      cbn in Hrel; inversion Hrel; subst; try discriminate Hx.
  Qed.

End OHearnExample.


Theorem progB_ASP_42 :
  tripleSP obsASP progB Over
    (fun _ => True)
    (fun r : option (unit * nat) =>
       match r with
       | Some (_, s) => s = 42
       | None => False
       end).
Proof.
  unfold tripleSP, obsASP.
  unfold asp, obsRel.
  intros r [sigma [_ Hrel]].
  destruct r as [[[] s']|]; cbn in Hrel; sauto.
Qed.
(* ================================================================= *)
(** ** Worked examples in the transported ([tripleSPm]) triple         *)
(* ================================================================= *)

(** Worked examples in the new triple. *)
Example m_progA_under_42 :
  tripleSPm spASP obsSP progA Under (fun _ => True) (fun r => r = Some (tt, 42)).
Proof. to_pointwise_sp. exact progA_42. Qed.

Example m_progB_over_42 :
  tripleSPm spASP obsSP progB Over (fun _ => True)
    (fun r : option (unit * nat) =>
       match r with Some (_, s) => s = 42 | None => False end).
Proof. to_pointwise_sp. exact progB_ASP_42. Qed.
