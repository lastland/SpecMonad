(** * Why ASP-[Under] has no ordered-monad Dijkstra presentation.

    [no_asp_under_index] ([Dijkstra_StDivExcNonDet_SPStExc.v]) shows the ASP
    [Under] triple has no index in the GLOBAL order.  The natural response
    is to look for a different order, a different precondition, a different
    representation, or a weaker carrier.  This file records that all four
    routes are closed, so the search is not repeated.

    ORDERS.  Every order that is a congruence for [bind] collapses to
    relation inclusion, and inclusion cannot index [Under]:

      [ordASPSt_under_is_ordASPSt]   the forall-post variant IS the global order
      [singleton_order_is_global]    agreement at all singletons IS the global order
      [aspArr_le_rel]                the arrow-natural order IS relation inclusion
      [asp_of_rel_id]                transformers and relations are the SAME object

    Consequently composition is monotone ([arr_comp_mono], [arr_first_mono])
    -- the arrow structure was never the problem.

    PRECONDITIONS.  Every order that fixes a precondition fails [bind]:

      [ordASPStAt_bind_not_mono]              at the triple's own [pre]
      [ordASPSt_top_bind_not_mono]            at [pre = True]
      [ordASPSt_at_singleton_bind_not_mono]   at a fixed singleton
      [ordASPSt_ex_is_top]                    [exists s0, s = s0] IS [True]

    In each case two continuations agree at the fixed precondition and
    differ at the states [bind] actually evaluates them from.

    CARRIERS.  [AdditiveSP] ([OldSPObservations.v]) is join-preservation in
    closed form, and its own note records that additivity is EQUIVALENT to
    the [bind] law.  [AdditiveSP_strict] then forces strictness at [False],
    which excludes [pp2_under] -- the only target shape that can name [pre].

    PREPOST.  A carrier whose precondition is first class ([PPSt], see
    [StDivNonDet_PPSt.v]) does escape join-preservation, but introduces a
    new obstruction: [obsPPdom_bind_fails] shows the precondition slot
    composes DEMONICALLY while ASP is angelic, forcing the trivial
    precondition and collapsing the order back to relation inclusion.

    ANY ORDER.  The four groups above are candidates; the theorem at the
    end of this file closes the question for every order at once.
    [no_ordered_asp_under_index]: for ANY preorder on [ASPSt nat unit]
    that contains [eq1] and makes [bind] monotone in its CONTINUATION alone,
    no index has the [Under] class of a fixed triple as its up-set.
    [no_ordered_asp_under_index_D] is the down-set direction, and
    [no_asp_under_index_any_order] the corollary for every [OrderedMonad].
    The proof uses one context: jump to a fixed state [s], then continue.
    Monotonicity carries membership through that context, but the [Under]
    triple does not survive it -- a program reaching the outcome from some
    state stops doing so once its start state is forced to [s].

    What DOES work is dropping the ordered-monad presentation entirely --
    see [Dijkstra_StDivNonDet_ASPUnder.v]. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Coq Require Import RelationClasses.
From Incorrectness.Classes Require Import Arrow OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPArrowCore ASPArrowRel ASPMonad DSLPMonad
  DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPSt_Arrow StDivNonDet_PPSt.

Import MonadNotation.
Open Scope monad_scope.

#[local] Existing Instance Monad_optionT.
#[local] Existing Instance Monad_stateT.

(** A program with prescribed terminating outcomes, always admitting
    divergence so the nonempty-outcomes condition is free. *)
Definition progOfSt {S A} (R : S -> A * S -> Prop) : stdivnd S A :=
  mkStateT (fun s => @mkOptionT SetM _
    (fun oa => match oa with Some r => R s r | None => True end)).

Lemma progOfSt_outcomes {S A} (R : S -> A * S -> Prop) s r :
  unOptionT (runStateT (progOfSt R) s) (Some r) <-> R s r.
Proof. cbn. split; intro H; exact H. Qed.


(* ================= ORDERS ================= *)

Section Proposed.
  Variable S : Type.

  Definition ordASPSt_under {A} (m n : ASPSt S A) : Prop :=
    forall (pre : S -> Prop) (post : A * S -> Prop) r,
      (post r -> getASPSt m pre r) -> (post r -> getASPSt n pre r).

  (** It is the GLOBAL order, verbatim. *)
  Lemma ordASPSt_under_iff {A} (m n : ASPSt S A) :
    ordASPSt_under m n <-> (forall pre r, getASPSt m pre r -> getASPSt n pre r).
  Proof.
    split.
    - intros H pre r Hm.
      exact (H pre (fun _ => True) r (fun _ => Hm) I).
    - intros H pre post r Hk Hp. exact (H pre r (Hk Hp)).
  Qed.

  Lemma ordASPSt_under_is_ordASPSt {A} (m n : ASPSt S A) :
    ordASPSt_under m n <-> ordASPSt m n.
  Proof.
    rewrite ordASPSt_under_iff. symmetry. apply ordASPSt_get.
  Qed.

End Proposed.

Section Contextual.
  Variable S : Type.

  (** Agreement at every SINGLETON precondition already IS the global order.
      This is what makes every composition-closed order collapse: a context
      can always supply a computation landing in exactly one state. *)
  Lemma singleton_order_is_global {A} (m n : ASPSt S A) :
    (forall s0 r, getASPSt m (fun s => s = s0) r -> getASPSt n (fun s => s = s0) r)
    <-> (forall pre r, getASPSt m pre r -> getASPSt n pre r).
  Proof.
    split.
    - intros H pre r Hm.
      apply (getASPSt_singleton _ n pre r).
      destruct (proj1 (getASPSt_singleton _ m pre r) Hm) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (H s0 r Hs) ].
    - intros H s0 r Hm. exact (H _ r Hm).
  Qed.
End Contextual.


Lemma asp_of_rel_id {A B} (f : ASPArr A B) P b :
  getASPArr (ofRelASPArr (aspRel f)) P b <-> getASPArr f P b.
Proof.
  split.
  - intro H.
    destruct (proj1 (get_aspRel (ofRelASPArr (aspRel f)) P b) H) as [a [HP Hr]].
    apply (proj1 (aspRel_ofRel (aspRel f) a b)) in Hr.
    exact (proj2 (get_aspRel f P b) (ex_intro _ a (conj HP Hr))).
  - intro H.
    destruct (proj1 (get_aspRel f P b) H) as [a [HP Hr]].
    apply (proj2 (get_aspRel (ofRelASPArr (aspRel f)) P b)).
    exists a. split; [ exact HP | exact (proj2 (aspRel_ofRel (aspRel f) a b) Hr) ].
Qed.

(** The pointwise (global) order on arrows. *)
Definition aspArr_le {A B} (f g : ASPArr A B) : Prop :=
  forall P b, getASPArr f P b -> getASPArr g P b.

(** It IS relation inclusion -- the arrow version of [singleton_order_is_global]. *)
Lemma aspArr_le_rel {A B} (f g : ASPArr A B) :
  aspArr_le f g <-> (forall a b, aspRel f a b -> aspRel g a b).
Proof.
  split.
  - intros H a b Hr. exact (H _ b Hr).
  - intros H P b Hf.
    apply get_aspRel. apply get_aspRel in Hf.
    destruct Hf as [a [HP Hr]]. exists a. split; [ exact HP | exact (H a b Hr) ].
Qed.

(** Composition is monotone in BOTH arguments. *)
Theorem arr_comp_mono {A B C} (f f' : ASPArr A B) (g g' : ASPArr B C) :
  aspArr_le f f' -> aspArr_le g g' ->
  aspArr_le (arr_comp f g) (arr_comp f' g').
Proof.
  intros Hf Hg. apply aspArr_le_rel. intros a c Hr.
  apply aspRel_comp in Hr. destruct Hr as [b [Hfb Hgc]].
  apply aspRel_comp. exists b. split.
  - exact (proj1 (aspArr_le_rel f f') Hf a b Hfb).
  - exact (proj1 (aspArr_le_rel g g') Hg b c Hgc).
Qed.

(** [first] too, so the whole arrow structure is monotone. *)
Theorem arr_first_mono {A B C} (f f' : ASPArr A B) :
  aspArr_le f f' -> aspArr_le (@arr_first ASPArr _ A B C f) (arr_first f').
Proof.
  intro Hf. apply aspArr_le_rel. intros p q Hr.
  apply aspRel_first in Hr. destruct Hr as [Hfst Hsnd].
  apply aspRel_first. split; [ exact (proj1 (aspArr_le_rel f f') Hf _ _ Hfst) | exact Hsnd ].
Qed.

(** [fun s => exists s0, s = s0] is [True]: the witness is [s] itself. *)
Lemma pre_ex_triv (s : nat) : (exists s0 : nat, s = s0) <-> True.
Proof. split; [ intros _; exact I | intros _; exists s; reflexivity ]. Qed.

(** So the reading at it is the reading at [True], verbatim. *)
Lemma getASPSt_ex_triv {A} (w : ASPSt nat A) r :
  getASPSt w (fun s => exists s0 : nat, s = s0) r
  <-> getASPSt w (fun _ => True) r.
Proof.
  unfold getASPSt. apply getASPArr_ext_iff.
  intros [[] s]. cbn. apply pre_ex_triv.
Qed.

(** ... and therefore so is the order. *)
Definition ordASPSt_ex {A} (m n : ASPSt nat A) : Prop :=
  forall r, getASPSt m (fun s => exists s0 : nat, s = s0) r
            -> getASPSt n (fun s => exists s0 : nat, s = s0) r.

Definition ordASPSt_top {A} (m n : ASPSt nat A) : Prop :=
  forall r, getASPSt m (fun _ => True) r -> getASPSt n (fun _ => True) r.

Lemma ordASPSt_ex_is_top {A} (m n : ASPSt nat A) :
  ordASPSt_ex m n <-> ordASPSt_top m n.
Proof.
  unfold ordASPSt_ex, ordASPSt_top. split; intros H r Hm.
  - apply getASPSt_ex_triv. apply H. apply getASPSt_ex_triv. exact Hm.
  - apply getASPSt_ex_triv. apply H. apply getASPSt_ex_triv. exact Hm.
Qed.

(* ============ PRECONDITIONS ============ *)

Lemma bind_get {A B} (x : stdivnd nat A) (f : A -> stdivnd nat B) pre r :
  getASPSt (bind (obsASP x) (fun a => obsASP (f a))) pre r
  <-> getASPSt (obsASP (bind x f)) pre r.
Proof.
  symmetry.
  exact (proj1 (eq1_ASPSt_get _ (obsASP (bind x f))
                  (bind (obsASP x) (fun a => obsASP (f a))))
           (obsASP_bind _ x f) pre r).
Qed.

(** [mU] runs only from state 0 and leaves the state at 0. *)
Definition mU : stdivnd nat unit :=
  progOfSt (fun s r => s = 0 /\ r = (tt, 0)).
(** Two continuations supported at DIFFERENT states, both reaching [(tt,9)]. *)
Definition kA : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => s = 0 /\ r = (tt, 9)).
Definition kB : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => s = 1 /\ r = (tt, 9)).


Theorem ordASPStAt_bind_not_mono :
  ~ (forall A B (pre : nat -> Prop) (m : ASPSt nat A) (k k' : A -> ASPSt nat B),
        (forall a, ordASPStAt pre (k a) (k' a)) ->
        ordASPStAt pre (bind m k) (bind m k')).
Proof.
  intro Hmono.
  (* (1) at [pre = True] the two continuations agree *)
  assert (Hk : forall a, ordASPStAt (fun _ : nat => True)
                           (obsASP (kA a)) (obsASP (kB a))).
  { intros a r Hr. apply getProgASP_obsASP in Hr. destruct Hr as [s [_ Hr]].
    apply progOfSt_outcomes in Hr. destruct Hr as [_ ->].
    apply getProgASP_obsASP. exists 1. split; [ exact I |].
    apply progOfSt_outcomes. split; reflexivity. }
  specialize (Hmono unit unit (fun _ => True) (obsASP mU)
                (fun a => obsASP (kA a)) (fun a => obsASP (kB a)) Hk (tt, 9)).
  (* (2) the left composite reaches [(tt,9)] *)
  assert (Hin : getASPSt (bind (obsASP mU) (fun a => obsASP (kA a)))
                  (fun _ => True) (tt, 9)).
  { apply bind_get. apply getProgASP_obsASP. exists 0. split; [ exact I |].
    apply (outcomes_bind nat). exists tt, 0. split.
    - apply progOfSt_outcomes. split; reflexivity.
    - apply progOfSt_outcomes. split; reflexivity. }
  specialize (Hmono Hin).
  (* (3) the right composite cannot: [mU] only ever produces state 0 *)
  apply bind_get in Hmono. apply getProgASP_obsASP in Hmono.
  destruct Hmono as [s [_ Hr]]. apply (outcomes_bind nat) in Hr.
  destruct Hr as [a [s' [Hx Hk2]]].
  apply progOfSt_outcomes in Hx. destruct Hx as [_ Heq].
  injection Heq as Heq2. subst s'.
  apply progOfSt_outcomes in Hk2. destruct Hk2 as [Hn _]. discriminate Hn.
Qed.

(** The two continuations are related by the pinned order ... *)
Lemma kA_le_kB : forall a, ordASPSt_top (obsASP (kA a)) (obsASP (kB a)).
Proof.
  intros a r Hr. apply getProgASP_obsASP in Hr. destruct Hr as [s [_ Hr]].
  apply progOfSt_outcomes in Hr. destruct Hr as [_ ->].
  apply getProgASP_obsASP. exists 1. split; [ exact I |].
  apply progOfSt_outcomes. split; reflexivity.
Qed.

(** ... but NOT by the global one: at [pre = {0}] only [kA] fires. *)
Lemma kA_not_le_kB_globally :
  ~ ordASPSt (obsASP (kA tt)) (obsASP (kB tt)).
Proof.
  intro H.
  assert (Hin : getASPSt (obsASP (kA tt)) (fun s => s = 0) (tt, 9)).
  { apply getProgASP_obsASP. exists 0. split; [ reflexivity |].
    apply progOfSt_outcomes. split; reflexivity. }
  pose proof (proj1 (ordASPSt_get _ _ _) H (fun s => s = 0) (tt, 9) Hin) as Hout.
  apply getProgASP_obsASP in Hout. destruct Hout as [s [Hs Hr]].
  apply progOfSt_outcomes in Hr. destruct Hr as [Hn _].
  subst s. discriminate Hn.
Qed.
Theorem ordASPSt_top_bind_not_mono :
  ~ (forall A B (m : ASPSt nat A) (k k' : A -> ASPSt nat B),
       (forall a, ordASPSt_top (k a) (k' a)) ->
       ordASPSt_top (bind m k) (bind m k')).
Proof.
  intro Hmono.
  specialize (Hmono unit unit (obsASP mU)
                (fun a => obsASP (kA a)) (fun a => obsASP (kB a)) kA_le_kB (tt, 9)).
  assert (Hin : getASPSt (bind (obsASP mU) (fun a => obsASP (kA a)))
                  (fun _ => True) (tt, 9)).
  { apply bind_get. apply getProgASP_obsASP. exists 0. split; [ exact I |].
    apply (outcomes_bind nat). exists tt, 0. split.
    - apply progOfSt_outcomes. split; reflexivity.
    - apply progOfSt_outcomes. split; reflexivity. }
  specialize (Hmono Hin).
  apply bind_get in Hmono. apply getProgASP_obsASP in Hmono.
  destruct Hmono as [s [_ Hr]]. apply (outcomes_bind nat) in Hr.
  destruct Hr as [a [s' [Hx Hk2]]].
  apply progOfSt_outcomes in Hx. destruct Hx as [_ Heq].
  injection Heq as Heq2. subst s'.
  apply progOfSt_outcomes in Hk2. destruct Hk2 as [Hn _]. discriminate Hn.
Qed.

(** The proposed order: [At] pinned to a fixed SINGLETON [{s0}]. *)
Definition ordASPSt_at {A} (s0 : nat) (m n : ASPSt nat A) : Prop :=
  forall r, getASPSt m (fun s => s = s0) r -> getASPSt n (fun s => s = s0) r.

(** [mS] moves the state 0 |-> 5.  The two continuations fire at 5 and at 7:
    BOTH are vacuous at the fixed singleton {0}, so they are trivially
    related there -- yet they compose differently after [mS]. *)
Definition mS : stdivnd nat unit :=
  progOfSt (fun s r => s = 0 /\ r = (tt, 5)).
Definition cA : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => s = 5 /\ r = (tt, 9)).
Definition cB : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => s = 7 /\ r = (tt, 9)).

Lemma cA_le_cB : forall a, ordASPSt_at 0 (obsASP (cA a)) (obsASP (cB a)).
Proof.
  intros a r Hr. apply getProgASP_obsASP in Hr. destruct Hr as [s [Hs Hr]].
  apply progOfSt_outcomes in Hr. destruct Hr as [H5 _]. subst s. discriminate H5.
Qed.

Theorem ordASPSt_at_singleton_bind_not_mono :
  ~ (forall A B (s0 : nat) (m : ASPSt nat A) (k k' : A -> ASPSt nat B),
       (forall a, ordASPSt_at s0 (k a) (k' a)) ->
       ordASPSt_at s0 (bind m k) (bind m k')).
Proof.
  intro Hmono.
  specialize (Hmono unit unit 0 (obsASP mS)
                (fun a => obsASP (cA a)) (fun a => obsASP (cB a)) cA_le_cB (tt, 9)).
  assert (Hin : getASPSt (bind (obsASP mS) (fun a => obsASP (cA a)))
                  (fun s => s = 0) (tt, 9)).
  { apply bind_get. apply getProgASP_obsASP. exists 0. split; [ reflexivity |].
    apply (outcomes_bind nat). exists tt, 5. split.
    - apply progOfSt_outcomes. split; reflexivity.
    - apply progOfSt_outcomes. split; reflexivity. }
  specialize (Hmono Hin).
  apply bind_get in Hmono. apply getProgASP_obsASP in Hmono.
  destruct Hmono as [s [Hs Hr]]. apply (outcomes_bind nat) in Hr.
  destruct Hr as [a [s' [Hx Hk2]]].
  apply progOfSt_outcomes in Hx. destruct Hx as [_ Heq].
  injection Heq as Heq2. subst s'.
  apply progOfSt_outcomes in Hk2. destruct Hk2 as [Hn _]. discriminate Hn.
Qed.

(* ============== PREPOST ================ *)
(* the carrier and its [bind] are [StDivNonDet_PPSt.v]'s *)

(** Can the observation carry a NON-trivial precondition?  The natural
    candidate is the domain: the states from which the program terminates. *)
Definition dom {S A} (m : stdivnd S A) : S -> Prop :=
  fun s => exists r, unOptionT (runStateT m s) (Some r).

Definition obsPPdom {S A} (m : stdivnd S A) : PPSt S A :=
  (dom m, fun s r => unOptionT (runStateT m s) (Some r)).

(** [mD] branches from 0 to either 1 or 2; [kD] terminates only from 1. *)
Definition mD : stdivnd nat unit :=
  progOfSt (fun s r => s = 0 /\ (r = (tt, 1) \/ r = (tt, 2))).
Definition kD : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => s = 1 /\ r = (tt, 9)).

(** The morphism law FAILS on the precondition component: [bindPPSt]
    composes preconditions DEMONICALLY (every intermediate state must be
    in the continuation's domain) while the ASP reading is ANGELIC (one
    completing path suffices). *)
Theorem obsPPdom_bind_fails :
  ppre (obsPPdom (bind mD kD)) 0
  /\ ~ ppre (bindPPSt (obsPPdom mD) (fun a => obsPPdom (kD a))) 0.
Proof.
  split.
  - exists (tt, 9). apply (outcomes_bind nat). exists tt, 1. split.
    + apply progOfSt_outcomes. split; [ reflexivity | left; reflexivity ].
    + apply progOfSt_outcomes. split; reflexivity.
  - intros [_ Hall].
    assert (H2 : unOptionT (runStateT mD 0) (Some (tt, 2))).
    { apply progOfSt_outcomes. split; [ reflexivity | right; reflexivity ]. }
    destruct (Hall tt 2 H2) as [r Hr].
    apply progOfSt_outcomes in Hr. destruct Hr as [Hn _]. discriminate Hn.
Qed.


(* ============== ANY ORDER ================ *)

(** Every element of [ASPSt nat unit] is the observation of a program. *)
Definition progOfASP (w : ASPSt nat unit) : stdivnd nat unit :=
  progOfSt (fun s r => aspRel w (tt, s) r).

Lemma obsASP_progOfASP (w : ASPSt nat unit) : eq1 (obsASP (progOfASP w)) w.
Proof.
  apply (proj2 (eq1_ASPSt_get _ _ _)). intros pre r. split; intro H.
  - apply getProgASP_obsASP in H. destruct H as [s [Hp Hr]].
    apply progOfSt_outcomes in Hr.
    unfold getASPSt. apply get_aspRel. exists (tt, s). split; [ exact Hp | exact Hr ].
  - unfold getASPSt in H. apply get_aspRel in H. destruct H as [[[] s] [Hp Hr]].
    apply getProgASP_obsASP. exists s. split; [ exact Hp |].
    apply progOfSt_outcomes. exact Hr.
Qed.

Lemma eq1_ASPSt_sym {A} (x y : ASPSt nat A) : eq1 x y -> eq1 y x.
Proof.
  intro H. apply (proj2 (eq1_ASPSt_get _ _ _)). intros pre r.
  symmetry. exact (proj1 (eq1_ASPSt_get _ _ _) H pre r).
Qed.

(** The triple: [(tt, 0)] is reachable from some state. *)
Definition UnderAt0 (prog : stdivnd nat unit) : Prop :=
  tripleASP prog Under (fun _ => True) (fun r => r = (tt, 0)).

(** [jumpTo s] ignores its start state and lands in [s]. *)
Definition jumpTo (s : nat) : stdivnd nat unit :=
  progOfSt (fun _ r => r = (tt, s)).

(** Stated for ANY [bnd] that makes [obsASP] a monad morphism, so no
    redefinition of [bind] escapes it; [no_ordered_asp_under_index] is the
    instance at ASP's own [bind]. *)
Theorem no_ordered_asp_under_index_bnd
  (bnd : ASPSt nat unit -> (unit -> ASPSt nat unit) -> ASPSt nat unit)
  (Hmorph : forall (x : stdivnd nat unit) (f : unit -> stdivnd nat unit),
      eq1 (obsASP (bind x f)) (bnd (obsASP x) (fun a => obsASP (f a))))
  (ord : ASPSt nat unit -> ASPSt nat unit -> Prop)
  (ord_trans : forall x y z, ord x y -> ord y z -> ord x z)
  (ord_eq1 : forall x y, eq1 x y -> ord x y)
  (ord_bind : forall (m : ASPSt nat unit) (k k' : unit -> ASPSt nat unit),
      (forall a, ord (k a) (k' a)) -> ord (bnd m k) (bnd m k')) :
  ~ exists w : ASPSt nat unit,
      forall prog : stdivnd nat unit, ord w (obsASP prog) <-> UnderAt0 prog.
Proof.
  intros [w Hfib].
  (* (1) [w]'s own program is in the class, so it reaches [(tt, 0)] from some [s] *)
  pose proof (obsASP_progOfASP w) as Emw.
  assert (Hin : UnderAt0 (progOfASP w)).
  { apply Hfib. apply ord_eq1. apply eq1_ASPSt_sym. exact Emw. }
  destruct (proj1 (getProgASP_obsASP _ _ _ _) (Hin (tt, 0) eq_refl)) as [s [_ Hs]].
  (* (2) a program reaching [(tt, 0)] only from [S s] is also in the class *)
  set (y := progOfSt (fun t r => t = S s /\ r = (tt, 0)) : stdivnd nat unit).
  assert (Hy : ord w (obsASP y)).
  { apply Hfib. intros r ->. apply getProgASP_obsASP. exists (S s).
    split; [ exact I |]. apply progOfSt_outcomes. split; reflexivity. }
  (* (3) jumping to [s] first keeps [w]'s program in the class ... *)
  assert (H1 : ord w (obsASP (bind (jumpTo s) (fun _ => progOfASP w)))).
  { apply Hfib. intros r ->. apply getProgASP_obsASP. exists 0. split; [ exact I |].
    apply (outcomes_bind nat). exists tt, s. split; [| exact Hs ].
    apply progOfSt_outcomes. reflexivity. }
  (* (4) ... so monotonicity in the continuation puts [jumpTo s ;; y] in it too *)
  assert (Hchain : ord w (obsASP (bind (jumpTo s) (fun _ => y)))).
  { apply (ord_trans _ _ _ H1).
    apply (ord_trans _ _ _ (ord_eq1 _ _ (Hmorph (jumpTo s) (fun _ => progOfASP w)))).
    apply (ord_trans _ _ _ (ord_bind (obsASP (jumpTo s)) _ _ (fun _ => ord_eq1 _ _ Emw))).
    apply (ord_trans _ _ _ (ord_bind (obsASP (jumpTo s)) (fun _ => w) _ (fun _ => Hy))).
    apply ord_eq1. apply eq1_ASPSt_sym. exact (Hmorph (jumpTo s) (fun _ => y)). }
  (* (5) but it reaches nothing: after the jump the state is [s], not [S s] *)
  destruct (proj1 (getProgASP_obsASP _ _ _ _) (proj1 (Hfib _) Hchain (tt, 0) eq_refl))
    as [s0 [_ Hr]].
  apply (outcomes_bind nat) in Hr. destruct Hr as [a [s' [Hj Hk]]].
  apply progOfSt_outcomes in Hj. apply progOfSt_outcomes in Hk. destruct Hk as [Hk _].
  injection Hj as _ Hs'. rewrite Hs' in Hk. exact (n_Sn s Hk).
Qed.

Theorem no_ordered_asp_under_index
  (ord : ASPSt nat unit -> ASPSt nat unit -> Prop)
  (ord_trans : forall x y z, ord x y -> ord y z -> ord x z)
  (ord_eq1 : forall x y, eq1 x y -> ord x y)
  (ord_bind : forall (m : ASPSt nat unit) (k k' : unit -> ASPSt nat unit),
      (forall a, ord (k a) (k' a)) -> ord (bind m k) (bind m k')) :
  ~ exists w : ASPSt nat unit,
      forall prog : stdivnd nat unit, ord w (obsASP prog) <-> UnderAt0 prog.
Proof.
  exact (no_ordered_asp_under_index_bnd (fun m k => bind m k)
           (fun x f => obsASP_bind _ x f) ord ord_trans ord_eq1 ord_bind).
Qed.

(** The down-set direction [obs m <= w] is the same theorem for the
    opposite order. *)
Corollary no_ordered_asp_under_index_D
  (ord : ASPSt nat unit -> ASPSt nat unit -> Prop)
  (ord_trans : forall x y z, ord x y -> ord y z -> ord x z)
  (ord_eq1 : forall x y, eq1 x y -> ord x y)
  (ord_bind : forall (m : ASPSt nat unit) (k k' : unit -> ASPSt nat unit),
      (forall a, ord (k a) (k' a)) -> ord (bind m k) (bind m k')) :
  ~ exists w : ASPSt nat unit,
      forall prog : stdivnd nat unit, ord (obsASP prog) w <-> UnderAt0 prog.
Proof.
  apply (no_ordered_asp_under_index (fun x y => ord y x)).
  - intros x y z H1 H2. exact (ord_trans _ _ _ H2 H1).
  - intros x y H. apply ord_eq1. apply eq1_ASPSt_sym. exact H.
  - intros m k k' Hk. exact (ord_bind m k' k Hk).
Qed.

(** In particular, no specification-monad order on [ASPSt nat] works. *)
Corollary no_asp_under_index_any_order
  (le : forall A, ASPSt nat A -> ASPSt nat A -> Prop)
  (OM : OrderedMonad (ASPSt nat) le) :
  (~ exists w, forall prog, le unit w (obsASP prog) <-> UnderAt0 prog)
  /\ (~ exists w, forall prog, le unit (obsASP prog) w <-> UnderAt0 prog).
Proof.
  pose proof (@om_preorder _ _ _ le OM unit) as HP.
  assert (Ht : forall x y z, le unit x y -> le unit y z -> le unit x z).
  { intros x y z H1 H2. exact (@PreOrder_Transitive _ _ HP x y z H1 H2). }
  assert (Hb : forall (m : ASPSt nat unit) (k k' : unit -> ASPSt nat unit),
             (forall a, le unit (k a) (k' a)) -> le unit (bind m k) (bind m k')).
  { intros m k k' Hk.
    exact (@om_bind _ _ _ le OM unit unit m m (@PreOrder_Reflexive _ _ HP m) k k' Hk). }
  split.
  - exact (no_ordered_asp_under_index (le unit) Ht (@om_eq1 _ _ _ le OM unit) Hb).
  - exact (no_ordered_asp_under_index_D (le unit) Ht (@om_eq1 _ _ _ le OM unit) Hb).
Qed.
