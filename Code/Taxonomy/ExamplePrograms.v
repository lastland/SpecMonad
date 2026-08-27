From Coq Require Import Lia Classical_Prop PeanoNat.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.OldSP Require Import OldSPObservations.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg ProgFacts WP Pred PredFacts SPost WPred WPNonDetItObservations SPSpecMonads SPNonDetItObservations.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.


(* ================================================================= *)
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  tripleWP obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

Theorem progA_DWP_all_spec :
  tripleWPspec obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  (* [tripleWPspec _ Under] is the spec-as-WP-element form
     [(pre s /\ post <= p) -> wp p s]; derive it from the direct form
     [progA_DWP_all] by monotonicity of [obsDWP] in its postcondition. *)
  unfold tripleWPspec, ordProgWP, pp2wp_subset.
  intros s p Hp. cbn [runStateT unOptionT] in Hp. destruct Hp as [_ Hsub].
  pose proof progA_DWP_all as Hall. unfold tripleWP in Hall. specialize (Hall s I).
  unfold obsDWP in Hall |- *. cbn [runStateT unOptionT] in Hall |- *.
  destruct (runStateT progA s) as [[outcomes]].
  intros oa Hoa. specialize (Hall oa Hoa).
  destruct oa as [r|]; [exact (Hsub r Hall) | exact Hall].
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 : 
  not (
    tripleWP obsDWP progA
      (fun _ => True)
      SubsetOf
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 42
        | None => False
        end)).
Proof.
  intro contra.
  unfold tripleWP in contra. specialize (contra 0 I). cbn in contra.
  specialize (contra (Some (Some (tt, 43)))). sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

Theorem progA_AWP_43 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 43
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 43)). split; sauto.
Qed.

(** AWP, over-approximate ([Over]) reading: [awp(post) ⊆ pre], the
    "necessary precondition" of partial incorrectness — every state from
    which [progA] can *angelically* reach an outcome in [post] must lie in
    [pre].  [progA] overwrites the state with [put 42] and then yields [42]
    or [43], so no run reaches state [100]; hence [awp(reach 100)] is empty
    and even the empty precondition [fun _ => False] is a valid (necessary)
    precondition.  (Contrast: for a *reachable* post like [reach 43],
    [awp] would be all of [nat], forcing [pre] to be [True].) *)
Theorem progA_AWP_100_over :
  tripleWP obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  unfold tripleWP. intros s H. cbn in H.
  destruct H as [r [Hr Heq]]. subst r. cbn in Hr. sauto.
Qed.

Theorem progA_AWP_100_over_spec :
  tripleWPspec obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  (* [tripleWPspec _ Over] is [forall s p, awp p s -> ((p <= post) -> pre s)].
     An angelic witness [r] of [awp p s] satisfies [p], hence [p <= post]
     forces [r = Some (tt, 100)] — unreachable for [progA]. *)
  unfold tripleWPspec, ordProgWP, pp2wp_superset.
  intros s p Hp Hsub. cbn in Hp.
  destruct Hp as [r [Hr Hpr]]. specialize (Hsub r Hpr).
  subst r. cbn in Hr. sauto.
Qed.
  
(* ================================================================= *)
(** ** WP examples: nondeterminism + divergence                       *)
(* ================================================================= *)

Example progB_DWP := obsDWP progB.
Example progB_DWLP := obsDWLP progB.
Example progB_AWP := obsAWP progB.

(** DWP is unprovable: the divergent branch forces [False]. *)
Theorem progB_DWP_unprovable :
  not (
    tripleWP obsDWP progB
      (fun _ => True)
      SubsetOf
      (fun r : option (unit * nat) =>
          match r with
          | Some (_, s) => s = 42
          | None => False
          end)).
Proof.
  intro contra.
  unfold tripleWP in contra. specialize (contra 0 I). cbn in contra.
  specialize (contra None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored. *)
Theorem progB_DWLP_42 :
  tripleWP obsDWLP progB
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  tripleWP obsAWP progB
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

(** "There are divergent branches": divergence (the outermost [None]
    outcome) is *not* a result, so it is invisible to the SP observations
    ([obsRel] only sees the terminating [Some r] slice — cf.
    [progB_not_None]).  It is carried only by the *liberal* WP
    observations: [obsAWLP m s post = (exists terminating r, post r) \/
    (divergence reachable)].  Taking [post := fun _ => False] empties the
    terminating disjunct, so the triple says exactly "from every state,
    SOME branch diverges" (angelic), witnessed here by the [spinP] branch.

    This is the same shape as the (false) [progloom_correct] attempt —
    [progloom] never diverges, [progB] does.  Using [obsDWLP] instead
    would read "ALL branches diverge", which is false for [progB] (the
    [put s] branch converges). *)
Theorem progB_has_divergent_branch :
  tripleWP obsAWLP progB (fun _ => True) SubsetOf (fun _ => False).
Proof.
  intros s _. cbn.
  right.
  exists (Some (Some (tt, 42))). split; [reflexivity|].
  cbn. exists (Some (Some (42, 42))). split; [reflexivity|].
  cbn. right. reflexivity.
Qed.


(** The DWP-Inc triple now holds: [dwp(postEq0)(s)] forces [s = 0]. *)
Theorem progRet_dwp_inc :
  tripleWP obsDWP progRet preEq0 SupersetOf postEq0.
Proof.
  intros s Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(** Likewise DWLP-Inc holds (the divergence branch is vacuous, since
    [progRet] never diverges). *)
Theorem progRet_dwlp_inc :
  tripleWP obsDWLP progRet preEq0 SupersetOf postEq0.
Proof.
  intros s Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(* ================================================================= *)
(** ** Angelic vs. demonic nondeterminism under exceptions            *)
(* ================================================================= *)

(** A withdrawal session that nondeterministically [pick]s an [amount]
    and either throws (when the amount exceeds the balance) or debits the
    balance.  [balance] is the state.

      def withdrawSessionAngelic' returns (u : Unit)
        require balance > 0
        ensures False do
        let mut amount <- pick Nat
        if amount > balance then throw "Insufficient funds"
        else balance := balance - amount
        return

    The exception payload is [unit] (the message is dropped), and [pick
    Nat] is the unbounded-choice combinator [pickP] from [NonDetItProg.v].

    "Angelic, [ensures False]": from any positive balance *some* execution
    reaches an acceptable outcome.  A normal return is forbidden
    ([ensures False]); the only acceptable outcome is the exceptional one
    ([None]), so the triple states that the angelic scheduler can always
    drive the session to the [throw].  This is [tripleWP obsAWP _ Under]
    with a postcondition that is [True] on the exception and [False] on
    every normal return.  The [obsDWP] (demonic) reading of the same spec
    is invalid: the demon may pick a small amount and return normally. *)

Module WithdrawExample.

  Definition progloom : nditprog nat unit :=
    amount  <- pickP ;;
    balance <- get ;;
    if Nat.ltb balance amount then raise tt else put (balance - amount).

  (** Angelic spec: pick [amount = S balance > balance] to force the
      [raise], so the exceptional outcome [Some None] is reachable. *)
  Theorem progloom_triple :
    tripleWP obsAWP progloom
      (fun balance => balance > 0)
      SubsetOf
      (fun r => match r with Some (tt, _) => False | None => True end).
    Proof.
      intros s Hpos. cbn.
      exists None. split; [| exact I].
      exists (Some (Some (S s, s))). split.
      - exists (S s). reflexivity.
      - cbn. exists (Some (Some (s, s))). split.
        + reflexivity.
        + rewrite Nat.leb_refl. cbn.
      exists (Some None). split; [reflexivity|]. cbn. reflexivity.
    Qed.

  (** Traditional incorrectness reading: under-approximation of [asp],
      with the *same* postcondition as [progloom_triple] (on [option
      (unit * nat)], [match … Some (tt,_) => False | None => True] is
      exactly [r = None]).

      [tripleSP obsASP _ Under] is [post ⊆ asp(pre)] (∀ asserted output,
      ∃ input): "the throw is reachable from *some* [balance > 0]" —
      O'Hearn-style bug *presence*.  [progloom_triple] is the angelic-total
      WP reading [pre ⊆ awp(post)] (∀ input, ∃ output): "the throw is
      reachable from *every* [balance > 0]" — angelic *coverage*.  Same
      program, same postcondition; only the triple and the quantifier
      order over inputs/outputs differ. *)
  Theorem progloom_triple_asp :
    OldSPObservations.tripleSP OldSPObservations.obsASP progloom OldSPObservations.Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
  Proof.
    intros r Hr. destruct r as [[[] n]|]; [ exfalso; exact Hr | ].
    unfold obsASP, asp.
    exists 1. split.
    - exact (ltac:(lia) : 1 > 0).
    - unfold obsRel. cbn.
      exists (Some (Some (2, 1))). split.
      + exists 2. reflexivity.
      + cbn. exists (Some (Some (1, 1))). split.
        * reflexivity.
        * cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
  Qed.

  Definition progloom_harder : nditprog nat unit :=
    amount  <- pickP ;;
    balance <- get ;;
    if Nat.even balance then raise tt else put (balance - amount).

  (** WP coverage FAILS: the throw is reached iff [balance] is even (the
      picked [amount] is irrelevant), so from an odd [balance] (e.g. [1])
      every branch returns normally and the exception is unreachable —
      [awp(post)] is empty there, breaking [pre ⊆ awp(post)]. *)
  Theorem progloom_triple_harder :
    ~ (tripleWP obsAWP progloom_harder
      (fun balance => balance > 0)
      SubsetOf
      (fun r => match r with Some (tt, _) => False | None => True end)).
  Proof.
    intro H. specialize (H 1 (ltac:(lia) : 1 > 0)). cbn in H.
    destruct H as [r [Hreach Hpost]]. destruct r as [[[] n]|].
    - exact Hpost.
    - destruct Hreach as [a [[amt Ha] Hcont]]. subst a. cbn in Hcont.
      destruct Hcont as [a2 [Ha2 Hcont2]]. subst a2. cbn in Hcont2.
      discriminate Hcont2.
  Qed.

  (** SP incorrectness HOLDS: the throw is still reachable from *some*
      [balance > 0] — pick an even one (e.g. [2]).  Same program and
      postcondition as [progloom_triple_harder]; only the quantifier
      order over inputs differs (∃ input here vs ∀ input there). *)
  Theorem progloom_triple_asp_harder :
    OldSPObservations.tripleSP OldSPObservations.obsASP progloom_harder OldSPObservations.Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
  Proof.
    intros r Hr. destruct r as [[[] n]|]; [ exfalso; exact Hr | ].
    unfold obsASP, asp.
    exists 2. split.
    - exact (ltac:(lia) : 2 > 0).
    - unfold obsRel. cbn.
      exists (Some (Some (0, 2))). split.
      + exists 0. reflexivity.
      + cbn. exists (Some (Some (2, 2))). split.
        * reflexivity.
        * cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
  Qed.
End WithdrawExample.

Section ASPExamples.
  Theorem progA_all :
    tripleASP progA Over
      (fun _ => True)
      (fun r =>
         match r with
         | Some (_, s') => s' >= 42
         | None => False
         end).
  Proof.
    unfold tripleASP. intros r [sigma [_ Hrel]].
    destruct r as [[[] s'] |]; cbn in Hrel; sauto.
  Qed.

  Theorem progA_42 :
    tripleASP progA Under
      (fun _ => True)
      (fun r => r = Some (tt, 42)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split.
    - exact I.
    - cbn. sauto.
  Qed.

  Theorem progA_43 :
    tripleASP progA Under
      (fun _ => True)
      (fun r => r = Some (tt, 43)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split.
    - exact I.
    - cbn. sauto.
  Qed.

  Theorem progB_42 :
    tripleASP progB Under
      (fun _ => True)
      (fun r => r = Some (tt, 42)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split; [exact I | sauto].
  Qed.

  Theorem progB_not_None :
    tripleASP progB Over
      (fun _ => True)
      (fun r => r <> None).
  Proof.
    unfold tripleASP. intros r [sigma [_ Hrel]] ->. cbn in Hrel. sauto.
  Qed.

    Theorem progEx_under :
    tripleASP progEx Under
      (fun _ => True)
      (fun r => r = Some (tt, 1)).
  Proof.
    intros r ->. exists 0. split; [exact I | cbn; sauto].
  Qed.

End ASPExamples.

Theorem example_incorrect_1 :
    tripleASP example_state Under
      (fun '(x, _, z) => z = 11)
      (fun r =>
         match r with
         | Some (tt, (x, y, z)) =>
             z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
         | _ => False
         end).
Proof.
  unfold tripleASP.
  intros [[[] [[x y] z]]|] H; [| contradiction].
  destruct H as [-> [Hx Hy]].
  exists (x, y, 11). split; [reflexivity |].
  cbn. eexists. split; [reflexivity |].
  cbn. rewrite Hx, Hy. reflexivity.
Qed.

Theorem example_incorrect_2 :
  tripleASP example_state Under
    (fun _ => True)
    (fun r =>
       match r with
       | Some (tt, (_, _, z)) => z = 42
         | _ => False
       end).
Proof.
  unfold tripleASP.
  intros [[[] [[x y] z]]|] H; [| contradiction].
  cbn in H. subst z.
  (* the final state itself is a witness: both branches preserve [x], [y]
       and either set [z := 42] or leave it at [42] *)
  exists (x, y, 42). split; [exact I |].
  cbn. eexists. split; [reflexivity |].
  cbn. destruct (Nat.even x); destruct (negb (Nat.even y)); reflexivity.
Qed.

Theorem example_incorrect_unprovable :
  ~ tripleASP example_state Under
    (fun '(_, _, z) => z = 11)
    (fun r =>
           match r with
           | Some (tt, (_, _, z)) => z = 42
           | _ => False
           end).
Proof.
  (* [Some (tt, (1, 0, 42))] satisfies the postcondition but is reachable
     only from itself — and its [z] is [42], not [11] *)
    intro H.
    specialize (H (Some (tt, (1, 0, 42))) eq_refl).
    destruct H as [[[x y] z] [Hpre Hrel]].
    cbn in Hpre. subst z.
    cbn in Hrel. destruct Hrel as [a [Ha Hrel]]. subst a. cbn in Hrel.
    destruct (Nat.even x) eqn:Hx; destruct (negb (Nat.even y)) eqn:Hy;
      cbn in Hrel; inversion Hrel; subst; try discriminate Hx.
Qed.

Theorem progRet_asp_inc :
  tripleASP progRet Under preEq0 postEq0.
Proof.
  intros r Hpost. unfold postEq0 in Hpost. subst r.
  exists 0. split; [reflexivity | cbn; sauto].
Qed.

Theorem progRet_dsp_inc :
  tripleDSP progRet Under preEq0 postEq0.
Proof.
  intros r Hpost. split; [ exact (progRet_asp_inc r Hpost) |].
  unfold postEq0 in Hpost. subst r.
  intros s Hr. cbn in Hr. unfold preEq0. sauto.
Qed.

