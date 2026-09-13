(** * Observation functions for [stexcnd].

    SP observation: maps [stexcnd S A] to [ASPostArr S A] via
    set membership in the outcome set.

    WP observations: [obsDWP] (demonic, all outcomes) and
    [obsAWP] (angelic, some outcome) map into [WStExc S A]. *)

From Coq Require Import Lia.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.
From Incorrectness.Taxonomy.Arrows Require Import Rel RelSPPairArr.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

Section NDObservationWP.

  Variable S : Type.

  (** Demonic WP: ALL outcomes satisfy the postcondition. *)
  Lemma obsDWP_mono {A} (m : stexcnd S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT outcomes => forall oa, outcomes oa -> post oa
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [outcomes].
    intros oa Ho. exact (Hpq oa (H oa Ho)).
  Qed.

  Definition obsDWP {A} (m : stexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsDWP_mono m s))).

  (** Angelic WP: SOME outcome satisfies the postcondition. *)
  Lemma obsAWP_mono {A} (m : stexcnd S A) (s : S) :
    wpure_mono (fun post => match runStateT m s with
                            | mkOptionT outcomes => exists oa, outcomes oa /\ post oa
                            end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [outcomes].
    destruct H as [oa [Ho Hp]]. exists oa. split; [ exact Ho | exact (Hpq oa Hp) ].
  Qed.

  Definition obsAWP {A} (m : stexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsAWP_mono m s))).

  (** No WLP because no divergence. In this case, they are not even definable.
  *)

End NDObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsAWP {_} {_}.

(* ================================================================= *)
(** ** SP observations                                                *)
(* ================================================================= *)


Section NDObservationSP.

  Variable S : Type.

  (** Reachability relation for [stexcnd]: initial state [s0] reaches
      outcome [r] iff [r] is in the outcome set. *)
  Definition obsRel {A} (m : stexcnd S A)
    : Rel S (option (A * S)) :=
    fun s0 r => unOptionT (runStateT m s0) r.

  (** The four SP transformers are readings of the reachability relation
      [obsRel] (no [ASPostArr]/[RelSPPair]): [asp]/[dslp]/[spDSP]/[spASLP]
      from [RelSPPairArr.v]. *)
  Definition obsASP {A} (m : stexcnd S A)
    : (S -> Prop) -> option (A * S) -> Prop := asp (obsRel m).
  Definition obsDSLP {A} (m : stexcnd S A)
    : (S -> Prop) -> option (A * S) -> Prop := dslp (obsRel m).
  Definition obsDSP {A} (m : stexcnd S A)
    : (S -> Prop) -> option (A * S) -> Prop := fun pre r => asp (obsRel m) pre r /\ dslp (obsRel m) pre r.
  Definition obsASLP {A} (m : stexcnd S A)
    : (S -> Prop) -> option (A * S) -> Prop := fun pre r => asp (obsRel m) pre r \/ dslp (obsRel m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  Theorem obsDSP_sub_obsASP {A} (m : stexcnd S A) pre r :
    obsDSP m pre r -> obsASP m pre r.
  Proof. intros [H _]. exact H. Qed.

  Theorem obsDSP_sub_obsDSLP {A} (m : stexcnd S A) pre r :
    obsDSP m pre r -> obsDSLP m pre r.
  Proof. intros [_ H]. exact H. Qed.

  Theorem obsASP_sub_obsASLP {A} (m : stexcnd S A) pre r :
    obsASP m pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem obsDSLP_sub_obsASLP {A} (m : stexcnd S A) pre r :
    obsDSLP m pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : stexcnd S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP. symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : stexcnd S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP. symmetry. apply aslp_asp_dslp.
  Qed.

End NDObservationSP.

Arguments obsRel {_} {_}.
Arguments obsASP {_} {_}.
Arguments obsASLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsDSLP {_} {_}.


Example progA : stexcnd nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

(* ================================================================= *)
(** ** WP examples                                                    *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

Theorem progA_DWP_all :
  forall s, unOptionT (runStateT progA_DWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s >= 42
            | None => False
            end).
Proof.
  intros. cbn. intros []; sauto.
Qed.

Theorem progA_DWP_not42 :
  not (forall s, unOptionT (runStateT progA_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 (Some (tt, 43))).
  cbn in contra.
  assert (H: 43 = 42 -> False) by lia. apply H.
  apply contra. exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. right. reflexivity.
Qed.

Theorem progA_DWP_not43 :
  not (forall s, unOptionT (runStateT progA_DWP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 43
                 | None => False
                 end)).
Proof.
  intro contra. cbn in contra.
  specialize (contra 0 (Some (tt, 42))).
  cbn in contra.
  assert (H: 42 = 43 -> False) by lia. apply H.
  apply contra. exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. left. reflexivity.
Qed.

Theorem progA_AWP_all :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s >= 42
            | None => False
            end).
Proof.
  intros. cbn. exists (Some (tt, 42)). split; [| lia].
  exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. left. reflexivity.
Qed.

Theorem progA_AWP_42 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 42
            | None => False
            end).
Proof.
  intros. cbn. exists (Some (tt, 42)). split; [| lia].
  exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. left. reflexivity.
Qed.

Theorem progA_AWP_43 :
  forall s, unOptionT (runStateT progA_AWP s)
         (fun r : option (unit * nat) =>
            match r with
            | Some (_, s) => s = 43
            | None => False
            end).
Proof.
  intros. cbn. exists (Some (tt, 43)). split; [| lia].
  exists (Some (tt, 42)). split; [reflexivity| ].
  cbn. exists (Some (42, 42)). split; [reflexivity| ].
  cbn. right. reflexivity.
Qed.

(* ================================================================= *)
(** ** SP examples                                                    *)
(* ================================================================= *)

(** All reachable results from precondition [True] have state >= 42. *)
#[program] Theorem progA_all :
  forall (s : nat) r,
    (obsASP progA) (fun _ => True) r ->
    match r with
    | Some (_, s') => s' >= 42
    | None => False
    end.
Proof.
  intros s [[[] s']|] H; cbn in H; sauto.
Qed.

(** State 42 is reachable. *)
#[program] Theorem progA_42 :
  (obsASP progA) (fun _ => True) (Some (tt, 42)).
Proof.
  intros. cbn. unfold asp.
  exists 42. split; [reflexivity|].
  eapply ex_intro. split; [reflexivity|]. cbn.
  eapply ex_intro. split; [reflexivity|]. cbn.
  left. reflexivity.
Qed.

(** State 43 is also reachable. *)
#[program] Theorem progA_43 :
  (obsASP progA) (fun _ => True) (Some (tt, 43)).
Proof.
  intros. cbn. unfold asp.
  exists 42. split; [reflexivity|].
  eapply ex_intro. split; [reflexivity|]. cbn.
  eapply ex_intro. split; [reflexivity|]. cbn.
  right. reflexivity.
Qed.
