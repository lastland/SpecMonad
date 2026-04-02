(** * Four SP variants: asp, dslp, dsp, aslp.

    Following "A Taxonomy of Hoare-Like Logics" (Verscht & Kaminski,
    POPL 2025), we define four strongest postcondition transformers
    for [prog], [ndprog], and [nditprog].  All four use the same
    reachability relation but differ in quantifier structure over
    the inverse image:

    - [asp](b)(τ)  = ⋁_{σ ∈ ⟦p⟧⁻¹(τ)} b(σ)   (angelic, total)
    - [dslp](b)(τ) = ⋀_{σ ∈ ⟦p⟧⁻¹(τ)} b(σ)   (demonic, liberal)
    - [dsp]  = asp ∩ dslp                       (demonic, total)
    - [aslp] = asp ∪ dslp                       (angelic, liberal)

    Angelic vs demonic: ∃ vs ∀ over initial states reaching τ
    (confluence).  Liberal vs total: whether unreachable final
    states are included.

    The key arrow types are:
    - [ASPostArr]  (via [asp], existential) for [asp]
    - [DSLPostArr] (via [dslp], universal)  for [dslp]

    [dsp] and [aslp] are pointwise ∧ and ∨ of these two. *)

From Coq Require Import
  Lia Program.Tactics Classical_Prop
  FunctionalExtensionality PropExtensionality.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.

From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import
  Prog NonDetProg NonDetItProg SPostArr.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** * Characterization of dsp and aslp (paper §3.2.4)                 *)
(* ================================================================= *)

(** The paper's Definition 3.5 defines [dsp] via a reachability guard:

      dsp(b)(τ) = ∀σ∈⟦p⟧⁻¹(τ). b(σ)   if ⟦p⟧⁻¹(τ) ≠ ∅
                  false                  otherwise

    which equals [(∃a. R a b) ∧ (∀a. R a b → pre a)].

    Definition 3.6 defines [aslp] similarly:

      aslp(b)(τ) = ∃σ∈⟦p⟧⁻¹(τ). b(σ)  if ⟦p⟧⁻¹(τ) ≠ ∅
                   true                  otherwise

    which equals [(∃a. pre a ∧ R a b) ∨ ¬(∃a. R a b)].

    We prove these equal [asp ∧ dslp] and [asp ∨ dslp] respectively. *)

Section SPCharacterizations.

  Variables A B : Type.
  Variable R : SPArr A B.

  Theorem dsp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, R a b) /\ forall a, R a b -> pre a) <->
    (asp R pre b /\ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [[a0 HRa0] Hall].
      split; [exists a0; auto | exact Hall].
    - intros [[a0 [Hpre HRa0]] Hall].
      split; [exists a0; exact HRa0 | exact Hall].
  Qed.

  Theorem aslp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, pre a /\ R a b) \/ ~ exists a, R a b) <->
    (asp R pre b \/ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [Hsp | Hunreach].
      + left. exact Hsp.
      + right. intros a HRab. exfalso. apply Hunreach. exists a. exact HRab.
    - intros [Hsp | Hdp].
      + left. exact Hsp.
      + destruct (classic (exists a, R a b)) as [[a0 HRa0] | Hunreach].
        * left. exists a0. split; [exact (Hdp a0 HRa0) | exact HRa0].
        * right. exact Hunreach.
  Qed.

End SPCharacterizations.

(* ================================================================= *)
(** * SP variants for [nditprog]                                      *)
(* ================================================================= *)

Section NDItSP.

  Variable S : Type.

  (** The observation relation: reachability of terminating outcomes.
      Divergence is NOT a reachable final state — it is the absence
      of reaching any final state (dual to how divergence in WP is
      the absence of termination). *)
  Definition ndit_obsRel {A} (m : nditprog S A)
    : SPArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      match r with
      | Some (a, s') =>
          unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
      | None =>
          unOptionT (unOptionT (runStateT m s)) (Some None)
      end.

  (** Angelic strongest postcondition (total).
      [asp(b)(r) = ∃s. b(s) ∧ reachable(s, r)]
      Final states reachable from [b]. *)
  Definition ndit_asp {A} (m : nditprog S A) : ASPostArr S A :=
    mkASP (ndit_obsRel m).

  (** Demonic strongest liberal postcondition.
      [dslp(b)(r) = ∀s. reachable(s, r) → b(s)]
      Final states exclusively reachable from [b], or unreachable. *)
  Definition ndit_dslp {A} (m : nditprog S A) : DSLPostArr S A :=
    mkDSLP (ndit_obsRel m).

  (** Demonic strongest postcondition (total).
      [dsp = asp ∩ dslp]
      Final states exclusively reachable from [b]. *)
  #[program] Definition ndit_dsp {A} (m : nditprog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (ndit_asp m) pre r /\ sp_pt (ndit_dslp m) pre r.

  (** Angelic strongest liberal postcondition.
      [aslp = asp ∪ dslp]
      Final states reachable from [b], or unreachable. *)
  #[program] Definition ndit_aslp {A} (m : nditprog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (ndit_asp m) pre r \/ sp_pt (ndit_dslp m) pre r.

  (* -------------------------------------------------------------- *)
  (** ** Theorem 3.7: Square inclusions                              *)
  (* -------------------------------------------------------------- *)

  #[program] Theorem ndit_dsp_sub_asp {A} (m : nditprog S A) pre r :
    ndit_dsp m pre r -> sp_pt (ndit_asp m) pre r.
  Proof. intros [H _]. exact H. Qed.

  #[program] Theorem ndit_dsp_sub_dslp {A} (m : nditprog S A) pre r :
    ndit_dsp m pre r -> sp_pt (ndit_dslp m) pre r.
  Proof. intros [_ H]. exact H. Qed.

  #[program] Theorem ndit_asp_sub_aslp {A} (m : nditprog S A) pre r :
    sp_pt (ndit_asp m) pre r -> ndit_aslp m pre r.
  Proof. intro H. left. exact H. Qed.

  #[program] Theorem ndit_dslp_sub_aslp {A} (m : nditprog S A) pre r :
    sp_pt (ndit_dslp m) pre r -> ndit_aslp m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** ** Characterization: dsp = asp ∩ dslp, aslp = asp ∪ dslp       *)
  (* -------------------------------------------------------------- *)

  (** Paper §3.2.4: [dsp] matches Definition 3.5. *)
  Corollary ndit_dsp_char {A} (m : nditprog S A) pre r :
    ndit_dsp m pre r <->
    (exists sigma, ndit_obsRel m sigma r) /\
    (forall sigma, ndit_obsRel m sigma r -> pre sigma).
  Proof.
    unfold ndit_dsp, ndit_asp, ndit_dslp; simpl.
    symmetry. apply dsp_asp_dslp.
  Qed.

  (** Paper §3.2.4: [aslp] matches Definition 3.6. *)
  Corollary ndit_aslp_char {A} (m : nditprog S A) pre r :
    ndit_aslp m pre r <->
    (exists sigma, pre sigma /\ ndit_obsRel m sigma r) \/
    ~ (exists sigma, ndit_obsRel m sigma r).
  Proof.
    unfold ndit_aslp, ndit_asp, ndit_dslp; simpl.
    symmetry. apply aslp_asp_dslp.
  Qed.

  (* -------------------------------------------------------------- *)
  (** ** Theorem 3.8: Contrapositive transformers                     *)
  (* -------------------------------------------------------------- *)

  #[program] Theorem ndit_asp_contrapositive {A} (m : nditprog S A) pre r :
    sp_pt (ndit_asp m) pre r <->
    ~ sp_pt (ndit_dslp m) (fun x => ~ pre x) r.
  Proof.
    unfold ndit_asp, ndit_dslp; simpl.
    unfold asp, dslp. split.
    - intros [a [Hpre Hrel]] Hall.
      exact (Hall a Hrel Hpre).
    - intro Hnn.
      apply NNPP. intro Habs.
      apply Hnn. intros a Hrel Hpre.
      apply Habs. exists a. exact (conj Hpre Hrel).
  Qed.

  Theorem ndit_dsp_contrapositive {A} (m : nditprog S A) pre r :
    ndit_dsp m pre r <->
    ~ ndit_aslp m (fun x => ~ pre x) r.
  Proof.
    unfold ndit_dsp, ndit_aslp, ndit_asp, ndit_dslp.
    simpl. unfold asp, dslp.
    split.
    - intros [[a [Hpre Hrel]] Hall] [Hasp | Hdslp].
      + destruct Hasp as [a' [Hnpre Hrel']].
        exact (Hnpre (Hall a' Hrel')).
      + exact (Hdslp a Hrel Hpre).
    - intro Hnaslp.
      assert (Hnasp : ~ exists a, ~ pre a /\ ndit_obsRel m a r)
        by (intro; apply Hnaslp; left; assumption).
      assert (Hndslp : ~ forall a, ndit_obsRel m a r -> ~ pre a)
        by (intro; apply Hnaslp; right; assumption).
      split.
      + apply NNPP. intro Habs. apply Hndslp.
        intros a Hrel Hpre. apply Habs.
        exists a. exact (conj Hpre Hrel).
      + intros a Hrel. apply NNPP. intro Hn.
        apply Hnasp. exists a. exact (conj Hn Hrel).
  Qed.

End NDItSP.

Arguments ndit_obsRel {_} {_}.
Arguments ndit_asp {_} {_}.
Arguments ndit_dslp {_} {_}.
Arguments ndit_dsp {_} {_}.
Arguments ndit_aslp {_} {_}.

(* ================================================================= *)
(** * SP variants for [ndprog]                                        *)
(* ================================================================= *)

Section NDSP.

  Variable S : Type.

  (** For [ndprog], outcomes are [option (A * S)] directly. *)
  Definition nd_obsRel {A} (m : ndprog S A)
    : SPArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      unOptionT (runStateT m s) r.

  Definition nd_asp {A} (m : ndprog S A) : ASPostArr S A :=
    mkASP (nd_obsRel m).

  Definition nd_dslp {A} (m : ndprog S A) : DSLPostArr S A :=
    mkDSLP (nd_obsRel m).

  #[program] Definition nd_dsp {A} (m : ndprog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (nd_asp m) pre r /\ sp_pt (nd_dslp m) pre r.

  #[program] Definition nd_aslp {A} (m : ndprog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (nd_asp m) pre r \/ sp_pt (nd_dslp m) pre r.

  (** Diamond inclusions — same proofs as nditprog. *)
  #[program] Theorem nd_dsp_sub_asp {A} (m : ndprog S A) pre r :
    nd_dsp m pre r -> sp_pt (nd_asp m) pre r.
  Proof. intros [H _]. exact H. Qed.

  #[program] Theorem nd_dsp_sub_dslp {A} (m : ndprog S A) pre r :
    nd_dsp m pre r -> sp_pt (nd_dslp m) pre r.
  Proof. intros [_ H]. exact H. Qed.

  #[program] Theorem nd_asp_sub_aslp {A} (m : ndprog S A) pre r :
    sp_pt (nd_asp m) pre r -> nd_aslp m pre r.
  Proof. intro H. left. exact H. Qed.

  #[program] Theorem nd_dslp_sub_aslp {A} (m : ndprog S A) pre r :
    sp_pt (nd_dslp m) pre r -> nd_aslp m pre r.
  Proof. intro H. right. exact H. Qed.

  Corollary nd_dsp_char {A} (m : ndprog S A) pre r :
    nd_dsp m pre r <->
    (exists sigma, nd_obsRel m sigma r) /\
    (forall sigma, nd_obsRel m sigma r -> pre sigma).
  Proof.
    unfold nd_dsp, nd_asp, nd_dslp; simpl.
    symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary nd_aslp_char {A} (m : ndprog S A) pre r :
    nd_aslp m pre r <->
    (exists sigma, pre sigma /\ nd_obsRel m sigma r) \/
    ~ (exists sigma, nd_obsRel m sigma r).
  Proof.
    unfold nd_aslp, nd_asp, nd_dslp; simpl.
    symmetry. apply aslp_asp_dslp.
  Qed.

End NDSP.

Arguments nd_obsRel {_} {_}.
Arguments nd_asp {_} {_}.
Arguments nd_dslp {_} {_}.
Arguments nd_dsp {_} {_}.
Arguments nd_aslp {_} {_}.

(* ================================================================= *)
(** * SP variants for [prog]                                          *)
(* ================================================================= *)

From ITree Require Import ITree Eq Props.Infinite.

Section DetSP.

  Variable S : Type.

  (** For [prog], convergence is [eutt eq]. *)
  Definition det_obsRel {A} (m : prog S A)
    : SPArr (unit * S) (option (A * S)) :=
    fun '(tt, s) r =>
      eutt eq (unOptionT (runStateT m s)) (ret r).

  Definition det_asp {A} (m : prog S A) : ASPostArr S A :=
    mkASP (det_obsRel m).

  Definition det_dslp {A} (m : prog S A) : DSLPostArr S A :=
    mkDSLP (det_obsRel m).

  #[program] Definition det_dsp {A} (m : prog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (det_asp m) pre r /\ sp_pt (det_dslp m) pre r.

  #[program] Definition det_aslp {A} (m : prog S A)
    (pre : unit * S -> Prop) (r : option (A * S)) : Prop :=
    sp_pt (det_asp m) pre r \/ sp_pt (det_dslp m) pre r.

  #[program] Theorem det_dsp_sub_asp {A} (m : prog S A) pre r :
    det_dsp m pre r -> sp_pt (det_asp m) pre r.
  Proof. intros [H _]. exact H. Qed.

  #[program] Theorem det_dsp_sub_dslp {A} (m : prog S A) pre r :
    det_dsp m pre r -> sp_pt (det_dslp m) pre r.
  Proof. intros [_ H]. exact H. Qed.

  #[program] Theorem det_asp_sub_aslp {A} (m : prog S A) pre r :
    sp_pt (det_asp m) pre r -> det_aslp m pre r.
  Proof. intro H. left. exact H. Qed.

  #[program] Theorem det_dslp_sub_aslp {A} (m : prog S A) pre r :
    sp_pt (det_dslp m) pre r -> det_aslp m pre r.
  Proof. intro H. right. exact H. Qed.

  Corollary det_dsp_char {A} (m : prog S A) pre r :
    det_dsp m pre r <->
    (exists sigma, det_obsRel m sigma r) /\
    (forall sigma, det_obsRel m sigma r -> pre sigma).
  Proof.
    unfold det_dsp, det_asp, det_dslp; simpl.
    symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary det_aslp_char {A} (m : prog S A) pre r :
    det_aslp m pre r <->
    (exists sigma, pre sigma /\ det_obsRel m sigma r) \/
    ~ (exists sigma, det_obsRel m sigma r).
  Proof.
    unfold det_aslp, det_asp, det_dslp; simpl.
    symmetry. apply aslp_asp_dslp.
  Qed.

End DetSP.

Arguments det_obsRel {_} {_}.
Arguments det_asp {_} {_}.
Arguments det_dslp {_} {_}.
Arguments det_dsp {_} {_}.
Arguments det_aslp {_} {_}.

(* ================================================================= *)
(** * Examples: [nditprog] showing all four reachability classes      *)
(* ================================================================= *)

(** Program: [s <- get; orP (put (s + 1)) (put 42)]
    From state s, outcomes are: {(tt, s+1), (tt, 42)}.
    - [Some (tt, 1)] is exclusively reachable from s=0 (class 1)
    - [Some (tt, 42)] is reachable from all states (class 2)
    - [None] (exception) is unreachable (class 3)
    - [Some (tt, 99)] is exclusively reachable from s=98 (class 4) *)

Example progEx : nditprog nat unit :=
  s <- get ;;
  orP _ (put (s + 1)) (put 42).

Definition P0 : unit * nat -> Prop := fun '(tt, s) => s = 0.

(** -- Class 1: exclusively reachable from P — all four include it -- *)

#[program] Theorem progEx_asp_1 :
  sp_pt (ndit_asp progEx) P0 (Some (tt, 1)).
Proof.
  unfold ndit_asp, P0. simpl proj1_sig. unfold asp.
  exists (tt, 0). split; [reflexivity|].
  unfold ndit_obsRel. cbn.
  sauto.
Qed.

#[program] Theorem progEx_dslp_1 :
  sp_pt (ndit_dslp progEx) P0 (Some (tt, 1)).
Proof.
  unfold ndit_dslp, P0. simpl proj1_sig. unfold dslp.
  intros [[] s] Hrel. unfold ndit_obsRel in Hrel. cbn in Hrel.
  f_equal. f_equal. sauto lq: on.
Qed.

Theorem progEx_dsp_1 :
  ndit_dsp progEx P0 (Some (tt, 1)).
Proof.
  split; [exact progEx_asp_1 | exact progEx_dslp_1].
Qed.

Theorem progEx_aslp_1 :
  ndit_aslp progEx P0 (Some (tt, 1)).
Proof. left. exact progEx_asp_1. Qed.

(** -- Class 2: reachable from P and ¬P — asp and aslp include,
       dsp and dslp exclude -- *)

#[program] Theorem progEx_asp_42 :
  sp_pt (ndit_asp progEx) P0 (Some (tt, 42)).
Proof.
  unfold ndit_asp, P0. simpl proj1_sig. unfold asp.
  exists (tt, 0). split; [reflexivity|].
  unfold ndit_obsRel. cbn. sauto.
Qed.

#[program] Theorem progEx_dslp_not_42 :
  ~ sp_pt (ndit_dslp progEx) P0 (Some (tt, 42)).
Proof.
  unfold ndit_dslp, P0. simpl proj1_sig. unfold dslp.
  intro H. specialize (H (tt, 1)).
  assert (Hreach : ndit_obsRel progEx (tt, 1) (Some (tt, 42))).
  { unfold ndit_obsRel. cbn. sauto. }
  specialize (H Hreach). simpl in H. discriminate.
Qed.

Theorem progEx_dsp_not_42 :
  ~ ndit_dsp progEx P0 (Some (tt, 42)).
Proof.
  intros [_ H]. exact (progEx_dslp_not_42 H).
Qed.

Theorem progEx_aslp_42 :
  ndit_aslp progEx P0 (Some (tt, 42)).
Proof. left. exact progEx_asp_42. Qed.

(** -- Class 3: unreachable — dslp and aslp include,
       asp and dsp exclude -- *)

#[program] Theorem progEx_asp_not_None :
  ~ sp_pt (ndit_asp progEx) P0 None.
Proof.
  unfold ndit_asp, P0. simpl proj1_sig. unfold asp.
  intros [[[] s] [HP Hrel]].
  unfold ndit_obsRel in Hrel. cbn in Hrel. sauto.
Qed.

#[program] Theorem progEx_dslp_None :
  sp_pt (ndit_dslp progEx) P0 None.
Proof.
  unfold ndit_dslp, P0. simpl proj1_sig. unfold dslp.
  intros [[] s] Hrel.
  (** None (exception) is unreachable — the ∀ is vacuously true. *)
  unfold ndit_obsRel in Hrel. cbn in Hrel. sauto.
Qed.

Theorem progEx_dsp_not_None :
  ~ ndit_dsp progEx P0 None.
Proof.
  intros [H _]. exact (progEx_asp_not_None H).
Qed.

Theorem progEx_aslp_None :
  ndit_aslp progEx P0 None.
Proof. right. exact progEx_dslp_None. Qed.

(** -- Class 4: exclusively reachable from ¬P — none include -- *)

#[program] Theorem progEx_asp_not_99 :
  ~ sp_pt (ndit_asp progEx) P0 (Some (tt, 99)).
Proof.
  unfold ndit_asp, P0. simpl proj1_sig. unfold asp.
  intros [[[] s] [HP Hrel]]. subst.
  unfold ndit_obsRel in Hrel. cbn in Hrel. sauto lq: on.
Qed.

#[program] Theorem progEx_dslp_not_99 :
  ~ sp_pt (ndit_dslp progEx) P0 (Some (tt, 99)).
Proof.
  unfold ndit_dslp, P0. simpl proj1_sig. unfold dslp.
  intro H. specialize (H (tt, 98)).
  assert (Hreach : ndit_obsRel progEx (tt, 98) (Some (tt, 99))).
  { unfold ndit_obsRel. cbn. sauto. }
  specialize (H Hreach). simpl in H. discriminate.
Qed.

Theorem progEx_dsp_not_99 :
  ~ ndit_dsp progEx P0 (Some (tt, 99)).
Proof. intros [H _]. exact (progEx_asp_not_99 H). Qed.

Theorem progEx_aslp_not_99 :
  ~ ndit_aslp progEx P0 (Some (tt, 99)).
Proof.
  intros [H | H]; [exact (progEx_asp_not_99 H) |
                    exact (progEx_dslp_not_99 H)].
Qed.
