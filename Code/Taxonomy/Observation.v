(** * Observation functions for [prog].

    Maps [prog S A] (deterministic computation via ITree) to specification
    types.

    WP observations: [obsAWP] and [obsDWP] (total) and [obsAWLP] and [obsDWLP]
    (partial, tolerates divergence) map into [ProgWP S A]. Because [prog S A] is
    deterministic, we show [obsWPCollapse] and [obsWLPCollapse] theorems that
    state [obsAWP] is equivalent to [obsDWP], [obsAWLP] is equivalent to
    [obsDWLP].

    SP observation: [obsASP] and [obsDSLP], then [obsDSP] and [obsASLP] can be
    defined based on the former two. Even though [prog S A] is deterministic, it
    is not necessarily reversible, so we cannot collapse any of the [sp]s. *)

From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy Require Import Prog WP SPost.
From Paco Require Import paco.
From Hammer Require Import Tactics.
From ITree Require Import ITree Eq Props.Infinite.
From ITree.Extra Require Import Dijkstra.PureITreeBasics.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

(** There is no nondeterminism in [prog], so [awp] and [dwp] are the same. We
    only define [wp] here. *)

Section ObservationWP.

  Variable S : Type.

  Definition obsAWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                        | mkOptionT o => exists r, eutt eq o (ret r) /\ post r
                        end)).

  Definition obsAWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (exists r, eutt eq o (ret r) /\ post r) \/
                                           any_infinite o
                        end)).

  Definition obsDWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (forall r, eutt eq o (ret r) -> post r) /\
                                           ~ any_infinite o
                        end)).

  Definition obsDWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o =>
                             (forall r, eutt eq o (ret r) -> post r) : Prop
                         end)).

  Theorem obsWPCollapse :
    forall {A} (m : prog S A) post s0,
      unOptionT (runStateT (obsAWP m) s0) post <->
        unOptionT (runStateT (obsDWP m) s0) post.
  Proof.
    intros. cbn. destruct (runStateT m s0) as [o] eqn:Hs. split.
    - intros [r [He Hp]]. split.
      + intros r' He'. rewrite He' in He. apply eutt_inv_Ret in He. subst. exact Hp.
      + intro Hinf. rewrite He in Hinf. exact (ret_not_div Hinf).
    - intros [Hall Hninf].
      destruct (eutt_reta_or_div o) as [[a Ha] | Hinf]; [| contradiction].
      symmetry in Ha. exists a. auto.
  Qed.

  Theorem obsWLPCollapse :
    forall {A} (m : prog S A) post s0,
      unOptionT (runStateT (obsAWLP m) s0) post <->
        unOptionT (runStateT (obsDWLP m) s0) post.
  Proof.
    intros. cbn. destruct (runStateT m s0) as [o] eqn:Hs. split.
    - intros [[r [He Hp]] | Hinf].
      + intros r' He'. rewrite He' in He. apply eutt_inv_Ret in He. subst. exact Hp.
      + intros r' He'. exfalso. rewrite He' in Hinf. exact (ret_not_div Hinf).
    - intros Hall.
      destruct (eutt_reta_or_div o) as [[a Ha] | Hinf].
      + left. symmetry in Ha. exists a. auto.
      + right. exact Hinf.
  Qed.
  
End ObservationWP.

Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.
Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.

(* ================================================================= *)
(** ** SP observations                                                *)
(* ================================================================= *)

Section ObservationSP.

  Variable S : Type.

  (** [sp]s do not collapse under nondeterminism. They only collapse when
      programs are reversible.

      TODO: Question: Is there a type that we can use to represent reversible
      definitions? *)

  (** Reachability relation for a deterministic [prog]: an initial state
      [(tt, s)] reaches outcome [r] iff the computation converges to [ret r]. *)
  Definition obsRel {A} (m : prog S A)
    : Pred (unit * S) (option (A * S)) :=
    fun '(tt, s) r => eutt eq (unOptionT (runStateT m s)) (ret r).

  Definition obsASP {A} (m : prog S A) : ASPostArr S A :=
    mkASP (obsRel m).

  Definition obsDSLP {A} (m : prog S A) : DSLPostArr S A :=
    mkDSLP (obsRel m).

  #[program] Definition obsASLP {A} (m : prog S A) :
    (unit * S -> Prop) -> (option (A * S) -> Prop) :=
    fun pre r => sp_pt (obsASP m) pre r \/ sp_pt (obsDSLP m) pre r.

  #[program] Definition obsDSP {A} (m : prog S A) :
    (unit * S -> Prop) -> (option (A * S) -> Prop) :=
    fun pre r => sp_pt (obsASP m) pre r /\ sp_pt (obsDSLP m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  #[program] Theorem obsDSP_sub_obsASP {A} (m : prog S A) pre r :
    obsDSP m pre r -> sp_pt (obsASP m) pre r.
  Proof. intros [H _]. exact H. Qed.

  #[program] Theorem obsDSP_sub_obsDSLP {A} (m : prog S A) pre r :
    obsDSP m pre r -> sp_pt (obsDSLP m) pre r.
  Proof. intros [_ H]. exact H. Qed.

  #[program] Theorem obsASP_sub_obsASLP {A} (m : prog S A) pre r :
    sp_pt (obsASP m) pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  #[program] Theorem obsDSLP_sub_obsASLP {A} (m : prog S A) pre r :
    sp_pt (obsDSLP m) pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : prog S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP, obsASP, obsDSLP; simpl.
    symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : prog S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP, obsASP, obsDSLP; simpl.
    symmetry. apply aslp_asp_dslp.
  Qed.

End ObservationSP.

Arguments obsRel {_} {_}.
Arguments obsASP {_} {_}.
Arguments obsASLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsDSLP {_} {_}.
