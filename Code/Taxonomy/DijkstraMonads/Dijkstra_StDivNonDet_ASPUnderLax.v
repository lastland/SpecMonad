(** * ASP-[Under] over MONOTONE transformers: a lax Dijkstra structure.

    [ASPUnderObstructions.no_ordered_asp_under_index_bnd] shows the ASP
    [Under] triple is a fibre of NO order on the ASP monad for which [bind]
    is monotone in its continuation, whatever [bind] is, as long as the
    observation is a monad morphism.  Its proof uses one fact about the
    CARRIER: every specification is the observation of some program
    ([obsASP_progOfASP]), because ASP is join-preserving transformers, which
    are relations.  This file drops exactly that, and records what it buys
    and what it costs.

    THE CARRIER.  [Tr S A] is every transformer [(S -> Prop) -> A * S -> Prop];
    the carrier is the monotone ([TrMono]) and strict ([TrStrict]) ones, with
    ASP's forward [bindT] and pointwise order [ordT].

    WHAT WORKS.
      [obsT_ret] / [obsT_bind]      the observation is a monad morphism
      [bindT_mono] / [bindT_strict] the carrier is closed under [bindT]
      [bindT_ord]                   [bindT] is monotone in BOTH arguments
      [under_is_fibre]              the [Under] triple IS the fibre at
                                    [pp2under] -- the index names [pre],
                                    which no join-preserving transformer can
      [pp2under_seq]                the [bindT] of two such indices weakens to
                                    the composite triple's index
      [lax_under_bind]              hence Dijkstra-style [bind] for the triple
      [bindT_ret_r]                 right unit, strictly
      [bindT_ret_l]                 left unit, given strictness
                                    ([bindT_ret_l_needs_strict] shows why)

    WHAT FAILS.  Associativity holds in ONE direction only:
      [bindT_assoc_le]    right-nested <= left-nested, for monotone [h]
      [bindT_not_assoc]   the converse fails, with every piece in the carrier
    so the carrier is a LAX ordered monad, and the Dijkstra structure's
    associativity law holds only up to one weakening.

    WHY IT MUST FAIL.  [assoc_forces_join]: a monotone continuation that
    associates strictly after arbitrary relational stages preserves every
    join ([assoc_forces_strict]: including the empty one).  Such transformers
    are ASP's.  So a strict monad under forward [bind] is back inside the
    ASP carrier, where [no_ordered_asp_under_index_bnd] applies: there is no
    carrier between ASP and the lax one that is both a strict monad and
    names [pre]. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Coq Require Import Classical_Prop.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPSt_Arrow.

Import MonadNotation.
Open Scope monad_scope.

#[local] Existing Instance Monad_optionT.
#[local] Existing Instance Monad_stateT.

(* ================================================================= *)
(** ** The carrier                                                    *)
(* ================================================================= *)

Definition Tr (S A : Type) : Type := (S -> Prop) -> A * S -> Prop.

Definition TrMono {S A} (w : Tr S A) : Prop :=
  forall (p q : S -> Prop) r, (forall s, p s -> q s) -> w p r -> w q r.

Definition TrStrict {S A} (w : Tr S A) : Prop :=
  forall r, ~ w (fun _ => False) r.

Definition retT {S A} (a : A) : Tr S A :=
  fun pre r => exists s, pre s /\ r = (a, s).

Definition bindT {S A B} (w : Tr S A) (k : A -> Tr S B) : Tr S B :=
  fun pre r => exists a, k a (fun s0 => w pre (a, s0)) r.

Definition ordT {S A} (w v : Tr S A) : Prop := forall pre r, w pre r -> v pre r.
Definition eqT {S A} (w v : Tr S A) : Prop := forall pre r, w pre r <-> v pre r.

Lemma retT_mono {S A} (a : A) : TrMono (S:=S) (retT a).
Proof. intros p q r H [s [Hp ->]]. exists s. split; [ exact (H s Hp) | reflexivity ]. Qed.

Lemma retT_strict {S A} (a : A) : TrStrict (S:=S) (retT a).
Proof. intros r [s [[] _]]. Qed.

Lemma bindT_mono {S A B} (w : Tr S A) (k : A -> Tr S B) :
  TrMono w -> (forall a, TrMono (k a)) -> TrMono (bindT w k).
Proof.
  intros Hw Hk p q r H [a Ha]. exists a.
  exact (Hk a _ _ r (fun s0 Hs0 => Hw p q (a, s0) H Hs0) Ha).
Qed.

Lemma bindT_strict {S A B} (w : Tr S A) (k : A -> Tr S B) :
  TrStrict w -> (forall a, TrMono (k a)) -> (forall a, TrStrict (k a)) ->
  TrStrict (bindT w k).
Proof.
  intros Hw Hkm Hks r [a Ha]. apply (Hks a r).
  exact (Hkm a _ _ r (fun s0 Hs0 => Hw (a, s0) Hs0) Ha).
Qed.

(** Monotone in BOTH arguments: the first sits in the precondition slot of
    the (monotone) second. *)
Lemma bindT_ord {S A B} (w w' : Tr S A) (k k' : A -> Tr S B) :
  (forall a, TrMono (k' a)) -> ordT w w' -> (forall a, ordT (k a) (k' a)) ->
  ordT (bindT w k) (bindT w' k').
Proof.
  intros Hk' Hw Hkk pre r [a Ha]. exists a.
  apply (Hk' a (fun s0 => w pre (a, s0)) (fun s0 => w' pre (a, s0)) r).
  - intros s0 Hs0. exact (Hw _ _ Hs0).
  - exact (Hkk a _ _ Ha).
Qed.

(* ================================================================= *)
(** ** The unit laws                                                  *)
(* ================================================================= *)

Lemma bindT_ret_r {S A} (w : Tr S A) : eqT (bindT w retT) w.
Proof.
  intros pre r. split.
  - intros [a [s [Hw ->]]]. exact Hw.
  - intro H. destruct r as [a s]. exists a, s. split; [ exact H | reflexivity ].
Qed.

Lemma bindT_ret_l {S A B} (a : A) (k : A -> Tr S B) :
  (forall a', TrMono (k a')) -> (forall a', TrStrict (k a')) ->
  eqT (bindT (retT a) k) (k a).
Proof.
  intros Hm Hs pre r. split.
  - intros [a' H]. destruct (classic (a' = a)) as [-> | Hne].
    + refine (Hm a _ pre r _ H).
      intros s0 [s [Hp Heq]]. injection Heq as Hs0. subst. exact Hp.
    + exfalso. apply (Hs a' r). refine (Hm a' _ _ r _ H).
      intros s0 [s [_ Heq]]. injection Heq as Ha _. exact (Hne Ha).
  - intro H. exists a. apply (Hm a pre _ r); [| exact H ].
    intros s0 Hp. exists s0. split; [ exact Hp | reflexivity ].
Qed.

(** Without strictness the left unit fails: a continuation that holds at
    the empty precondition fires for values [ret] never produces. *)
Definition cex_kS : bool -> Tr nat unit :=
  fun a' p r => if a' then exists s, p s else True.

Lemma cex_kS_mono : forall a', TrMono (cex_kS a').
Proof.
  intros [] p q r H; cbn; [ intros [s Hs]; exists s; exact (H s Hs) | auto ].
Qed.

Theorem bindT_ret_l_needs_strict : ~ eqT (bindT (retT true) cex_kS) (cex_kS true).
Proof.
  intro H.
  destruct (proj1 (H (fun _ => False) (tt, 0))
              (ex_intro _ false I : bindT (retT true) cex_kS (fun _ => False) (tt, 0)))
    as [s []].
Qed.

(* ================================================================= *)
(** ** Associativity: one direction only                              *)
(* ================================================================= *)

(** The two bracketings differ only in where [exists a] sits: inside the
    precondition passed to [h b] (left-nested) or outside [h b]
    (right-nested).  Monotonicity of [h b] moves it inward. *)
Lemma bindT_assoc_le {S A B C} (w : Tr S A) (k : A -> Tr S B) (h : B -> Tr S C) :
  (forall b, TrMono (h b)) ->
  ordT (bindT w (fun a => bindT (k a) h)) (bindT (bindT w k) h).
Proof.
  intros Hh pre r [a [b Hb]]. exists b.
  apply (Hh b (fun s1 => k a (fun s0 => w pre (a, s0)) (b, s1))); [| exact Hb ].
  intros s1 Hs1. exists a. exact Hs1.
Qed.

(** Moving it outward fails.  [cex_w] offers both booleans from the
    current state, [cex_k] sends [true] to state 1 and [false] to state 2,
    and [cex_h] needs BOTH 1 and 2 in its precondition.  Left-nested, [h]
    sees the union [{1,2}]; right-nested, it sees [{1}] or [{2}]. *)
Definition cex_w : Tr nat bool := fun pre r => pre (snd r).
Definition cex_k : bool -> Tr nat unit :=
  fun a pre r => (exists s, pre s) /\ r = (tt, if a then 1 else 2).
Definition cex_h : unit -> Tr nat unit :=
  fun _ p r => p 1 /\ p 2 /\ r = (tt, 0).

Lemma cex_w_carrier : TrMono cex_w /\ TrStrict cex_w.
Proof. split; [ intros p q r H Hp; exact (H _ Hp) | intros r Hr; exact Hr ]. Qed.

Lemma cex_k_carrier : forall a, TrMono (cex_k a) /\ TrStrict (cex_k a).
Proof.
  intro a. split.
  - intros p q r H [[s Hs] Hr]. split; [ exists s; exact (H s Hs) | exact Hr ].
  - intros r [[s []] _].
Qed.

Lemma cex_h_carrier : forall b, TrMono (cex_h b) /\ TrStrict (cex_h b).
Proof.
  intro b. split.
  - intros p q r H [H1 [H2 Hr]].
    split; [ exact (H 1 H1) | split; [ exact (H 2 H2) | exact Hr ] ].
  - intros r [[] _].
Qed.

Theorem bindT_not_assoc :
  bindT (bindT cex_w cex_k) cex_h (fun _ => True) (tt, 0)
  /\ ~ bindT cex_w (fun a => bindT (cex_k a) cex_h) (fun _ => True) (tt, 0).
Proof.
  split.
  - exists tt. split; [| split; [| reflexivity ] ].
    + exists true. split; [ exists 0; exact I | reflexivity ].
    + exists false. split; [ exists 0; exact I | reflexivity ].
  - intros [a [b [H1 [H2 _]]]].
    destruct a; cbn in *; [ destruct H2 as [_ E] | destruct H1 as [_ E] ]; congruence.
Qed.

(** Strict associativity against ARBITRARY relational first stages forces a
    monotone continuation to preserve every join. *)
Theorem assoc_forces_join {S C} (s_inh : S) (h : Tr S C) (Hh : TrMono h)
  (Hassoc : forall (A : Type) (w : Tr S A) (k : A -> Tr S unit) pre r,
      bindT (bindT w k) (fun _ => h) pre r ->
      bindT w (fun a => bindT (k a) (fun _ => h)) pre r)
  (Ix : Type) (p : Ix -> S -> Prop) (r : C * S) :
  h (fun s => exists i, p i s) r -> exists i, h (p i) r.
Proof.
  intro H.
  (* stage 1 offers every [i] from the current state; stage [i] then
     lands anywhere in [p i] *)
  set (w := (fun pre (x : Ix * S) => pre (snd x)) : Tr S Ix).
  set (k := (fun i pre (x : unit * S) => (exists s0, pre s0) /\ p i (snd x))
            : Ix -> Tr S unit).
  destruct (Hassoc Ix w k (fun _ => True) r) as [i [u Hu]].
  - exists tt. apply (Hh (fun s => exists i, p i s)); [| exact H ].
    intros s [i Hi]. exists i. split; [ exists s_inh; exact I | exact Hi ].
  - exists i. exact (Hh _ _ r (fun s1 Hs1 => proj2 Hs1) Hu).
Qed.

Corollary assoc_forces_strict {S C} (s_inh : S) (h : Tr S C) (Hh : TrMono h)
  (Hassoc : forall (A : Type) (w : Tr S A) (k : A -> Tr S unit) pre r,
      bindT (bindT w k) (fun _ => h) pre r ->
      bindT w (fun a => bindT (k a) (fun _ => h)) pre r) :
  TrStrict h.
Proof.
  intros r H.
  destruct (assoc_forces_join s_inh h Hh Hassoc Empty_set (fun i _ => match i with end) r
              (Hh _ _ r (fun s (Hs : False) => match Hs with end) H)) as [[] _].
Qed.

(* ================================================================= *)
(** ** The observation, and the [Under] triple as a fibre             *)
(* ================================================================= *)

Definition obsT {S A} (m : stdivnd S A) : Tr S A :=
  fun pre r => exists s, pre s /\ unOptionT (runStateT m s) (Some r).

(** It is ASP's reading, so it lands in the join-preserving part. *)
Lemma obsT_is_obsASP {S A} (m : stdivnd S A) pre r :
  obsT m pre r <-> getASPSt (obsASP m) pre r.
Proof. exact (iff_sym (getProgASP_obsASP _ m pre r)). Qed.

Lemma obsT_mono {S A} (m : stdivnd S A) : TrMono (obsT m).
Proof. intros p q r H [s [Hp Hr]]. exists s. split; [ exact (H s Hp) | exact Hr ]. Qed.

Lemma obsT_ret {S A} (a : A) : eqT (obsT (ret a : stdivnd S A)) (retT a).
Proof.
  intros pre r. split.
  - intros [s [Hp Hr]]. apply (outcomes_ret S) in Hr. exists s. split; [ exact Hp | exact Hr ].
  - intros [s [Hp ->]]. exists s. split; [ exact Hp | apply (outcomes_ret S); reflexivity ].
Qed.

Lemma obsT_bind {S A B} (m : stdivnd S A) (f : A -> stdivnd S B) :
  eqT (obsT (bind m f)) (bindT (obsT m) (fun a => obsT (f a))).
Proof.
  intros pre r. split.
  - intros [s [Hp Hr]]. apply (outcomes_bind S) in Hr. destruct Hr as [a [s' [Hm Hf]]].
    exists a, s'. split; [ exists s; split; [ exact Hp | exact Hm ] | exact Hf ].
  - intros [a [s' [[s [Hp Hm]] Hf]]]. exists s. split; [ exact Hp |].
    apply (outcomes_bind S). exists a, s'. split; [ exact Hm | exact Hf ].
Qed.

(** The index: a transformer that NAMES the precondition.  It is monotone,
    strict when [P] is inhabited, and not join-preserving. *)
Definition pp2under {S A} (P : S -> Prop) (Q : A * S -> Prop) : Tr S A :=
  fun p r => (forall s, P s -> p s) /\ Q r.

Lemma pp2under_mono {S A} (P : S -> Prop) (Q : A * S -> Prop) : TrMono (pp2under P Q).
Proof. intros p q r H [Hsub HQ]. split; [ intros s Hs; exact (H s (Hsub s Hs)) | exact HQ ]. Qed.

Lemma pp2under_strict {S A} (P : S -> Prop) (Q : A * S -> Prop) :
  (exists s, P s) -> TrStrict (pp2under P Q).
Proof. intros [s0 Hs0] r [Hsub _]. exact (Hsub s0 Hs0). Qed.

Theorem under_is_fibre {S A} (m : stdivnd S A) (P : S -> Prop) (Q : A * S -> Prop) :
  ordT (pp2under P Q) (obsT m) <-> tripleASP m Under P Q.
Proof.
  split.
  - intros H r HQ. apply getProgASP_obsASP. exact (H P r (conj (fun s Hs => Hs) HQ)).
  - intros H p r [Hsub HQ].
    destruct (proj1 (getProgASP_obsASP _ _ _ _) (H r HQ)) as [s [HP Hr]].
    exists s. split; [ exact (Hsub s HP) | exact Hr ].
Qed.

(** Sequencing at the level of indices. *)
Lemma pp2under_seq {S A B} (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
  ordT (pp2under P (fun r => exists a, R a r))
       (bindT (pp2under P Q) (fun a => pp2under (fun s => Q (a, s)) (R a))).
Proof.
  intros p r [Hsub [a HR]]. exists a.
  split; [ intros s HQ; split; [ exact Hsub | exact HQ ] | exact HR ].
Qed.

(** The Dijkstra [bind] step for the incorrectness triple: membership of
    the parts gives membership of the composite, through the morphism law,
    monotone [bindT], and one weakening. *)
Theorem lax_under_bind {S A B} (m : stdivnd S A) (k : A -> stdivnd S B)
  (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
  ordT (pp2under P Q) (obsT m) ->
  (forall a, ordT (pp2under (fun s => Q (a, s)) (R a)) (obsT (k a))) ->
  ordT (pp2under P (fun r => exists a, R a r)) (obsT (bind m k)).
Proof.
  intros Hm Hk pre r H.
  apply (proj2 (obsT_bind m k pre r)).
  exact (bindT_ord (pp2under P Q) (obsT m)
           (fun a => pp2under (fun s => Q (a, s)) (R a)) (fun a => obsT (k a))
           (fun a => obsT_mono (k a)) Hm Hk pre r (pp2under_seq P Q R pre r H)).
Qed.
