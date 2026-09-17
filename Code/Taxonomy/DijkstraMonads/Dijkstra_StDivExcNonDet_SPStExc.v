(** * Dijkstra monads of the SP observations of [stdivexcnd]

    DM4All's [Dtheta] construction over the four observations of
    [EffectObservations/SP/StDivExcNonDet_SPStExc.v]: the two Dijkstra monads
    that exist (ASP, DSLP), the proof that DSP and ASLP admit none, triples as
    Dijkstra typings, and the worked examples of that file. *)

From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import BaseGaloisConnections NewGaloisConnections.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.

From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivExcNonDet_SPStExc.
From Incorrectness.Taxonomy.DijkstraMonads Require Import Dijkstra_StDivExcNonDet_WStExc.

(* ================================================================= *)
(** ** The Dijkstra monad of an effect observation                   *)
(* ================================================================= *)

(** DM4All's [Dtheta] (SPropMonadicStructures.v, section [OfMorphism]):
    for a monad morphism [theta : M ~> W] into an ORDERED specification
    monad,

        D A w := { m : M A | theta m <= w }

    with [ret] indexed by [ret^W], [bind] by [bind^W], and weakening
    along the refinement order.  Unlike the WP side, where all four
    observations land in the same [WStExc], the four SP observations land
    in four DIFFERENT monads, so the construction is parameterised by the
    spec monad [W] together with its order -- which is closer to DM4All's
    [OrderedMonad] than the WP-side version is.

    The hypotheses are exactly DM4All's: a preorder, a [bind] monotone in
    both arguments ([Pos]-enrichment), and the two monad morphism laws
    (available here as [obs*_ret] / [obs*_bind], already stated as [eq1]
    equations).  [DMop] is the opposite indexing, which is what the
    [Under] (incorrectness) triples need. *)

Section DijkstraOfSPObservation.

  Variable S : Type.
  Variable W : Type -> Type.
  Context {MW : Monad W} {EW : Eq1 W} {EEW : @Eq1Equivalence W MW EW}.

  Variable ordW : forall A, W A -> W A -> Prop.
  Arguments ordW {A} _ _.

  Hypothesis ordW_pre : forall A, PreOrder (@ordW A).
  Hypothesis ordW_eq1 : forall A (w w' : W A), eq1 w w' -> ordW w w'.
  Hypothesis ordW_bind : forall A B (m m' : W A) (k k' : A -> W B),
    ordW m m' -> (forall a, ordW (k a) (k' a)) -> ordW (bind m k) (bind m' k').

  Variable obs : forall A, stdivexcnd S A -> W A.
  Arguments obs {A} _.

  Hypothesis obs_ret : forall A (a : A), eq1 (obs (ret a)) (ret a).
  Hypothesis obs_bind : forall A B (x : stdivexcnd S A) (f : A -> stdivexcnd S B),
    eq1 (obs (x >>= f)) (bind (obs x) (fun a => obs (f a))).

  #[local] Existing Instance ordW_pre.
  #[local] Obligation Tactic := (intros; cbn beta).

  Definition DM {A} (w : W A) : Type := { m : stdivexcnd S A | ordW (obs m) w }.

  #[program] Definition DM_ret {A} (a : A) : DM (ret a) := @ret (stdivexcnd S) _ A a.
  Next Obligation. apply ordW_eq1. apply obs_ret. Qed.

  #[program] Definition DM_bind {A B} {w : W A} {wf : A -> W B}
    (m : DM w) (f : forall a, DM (wf a)) : DM (bind w wf) :=
    @bind (stdivexcnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [ apply ordW_eq1; apply obs_bind |].
    apply ordW_bind; [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition DM_wkn {A} {w w' : W A} (Hle : ordW w w') (m : DM w) : DM w' :=
    proj1_sig m.
  Next Obligation. etransitivity; [ exact (proj2_sig m) | exact Hle ]. Qed.

  #[program] Definition DM_lift {A} (m : stdivexcnd S A) : DM (obs m) := m.
  Next Obligation. reflexivity. Qed.

  Definition DMop {A} (w : W A) : Type := { m : stdivexcnd S A | ordW w (obs m) }.

  #[program] Definition DMop_ret {A} (a : A) : DMop (ret a) := @ret (stdivexcnd S) _ A a.
  Next Obligation. apply ordW_eq1. symmetry. apply obs_ret. Qed.

  #[program] Definition DMop_bind {A B} {w : W A} {wf : A -> W B}
    (m : DMop w) (f : forall a, DMop (wf a)) : DMop (bind w wf) :=
    @bind (stdivexcnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply ordW_eq1; symmetry; apply obs_bind ].
    apply ordW_bind; [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition DMop_wkn {A} {w w' : W A} (Hle : ordW w' w) (m : DMop w) : DMop w' :=
    proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition DMop_lift {A} (m : stdivexcnd S A) : DMop (obs m) := m.
  Next Obligation. reflexivity. Qed.

End DijkstraOfSPObservation.


(** The [Pos]-enrichment for the two observations that have it.  In both
    binds the FIRST argument sits in the PRECONDITION slot of the second,
    so monotonicity there is [aspMono] / [dslpMono]. *)
Section SPEnrichment.

  Variable S : Type.

  #[global] Instance ordASPStExc_PreOrder {A} : PreOrder (@ordASPStExc S A).
  Proof.
    constructor.
    - intros w pre r H. exact H.
    - intros w1 w2 w3 H1 H2 pre r H. exact (H2 pre r (H1 pre r H)).
  Qed.

  #[global] Instance ordDSLPStExc_PreOrder {A} : PreOrder (@ordDSLPStExc S A).
  Proof.
    constructor.
    - intros w pre r H. exact H.
    - intros w1 w2 w3 H1 H2 pre r H. exact (H2 pre r (H1 pre r H)).
  Qed.

  Lemma ordASPStExc_eq1 {A} (w w' : ASPStExc S A) :
    eq1 w w' -> ordASPStExc w w'.
  Proof. intros H pre r Hp. apply (H pre r). exact Hp. Qed.

  Lemma ordDSLPStExc_eq1 {A} (w w' : DSLPStExc S A) :
    eq1 w w' -> ordDSLPStExc w w'.
  Proof. intros H pre r Hp. apply (H pre r). exact Hp. Qed.

  (** The Pos-enrichment on the ASP side: [bind] is monotone in both
      arguments.  The first argument sits in the PRECONDITION slot of the
      second, so monotonicity there is [aspMono]. *)
  Lemma ordASPStExc_bind {A B} (m m' : ASPStExc S A) (k k' : A -> ASPStExc S B) :
    ordASPStExc m m' -> (forall a, ordASPStExc (k a) (k' a)) ->
    ordASPStExc (bind m k) (bind m' k').
  Proof.
    intros Hm Hk pre r H. cbn in H |- *.
    destruct H as [[a Ha] | [Hr Hn]].
    - left. exists a.
      apply (aspMono S (k' a) (fun s0 => getASPStExc m pre (Some (a, s0)))
                             (fun s0 => getASPStExc m' pre (Some (a, s0))) r).
      + intros s0 Hs0. exact (Hm pre (Some (a, s0)) Hs0).
      + exact (Hk a _ r Ha).
    - right. split; [ exact Hr | exact (Hm pre None Hn) ].
  Qed.

  Lemma ordDSLPStExc_bind {A B} (m m' : DSLPStExc S A) (k k' : A -> DSLPStExc S B) :
    ordDSLPStExc m m' -> (forall a, ordDSLPStExc (k a) (k' a)) ->
    ordDSLPStExc (bind m k) (bind m' k').
  Proof.
    intros Hm Hk pre r [H1 H2]. cbn in H1, H2 |- *. split.
    - intro a.
      apply (dslpMono S (k' a) (fun s0 => getDSLPStExc m pre (Some (a, s0)))
                              (fun s0 => getDSLPStExc m' pre (Some (a, s0))) r).
      + intros s0 Hs0. exact (Hm pre (Some (a, s0)) Hs0).
      + exact (Hk a _ r (H1 a)).
    - intro Hr. exact (Hm pre None (H2 Hr)).
  Qed.

End SPEnrichment.

(* ================================================================= *)
(** ** The two Dijkstra monads that exist                            *)
(* ================================================================= *)

Definition Dasp {S A} (w : ASPStExc S A) : Type :=
  DM S (ASPStExc S) (@ordASPStExc S) (@obsASP S) w.
Definition Dasp_op {S A} (w : ASPStExc S A) : Type :=
  DMop S (ASPStExc S) (@ordASPStExc S) (@obsASP S) w.

Definition Dasp_ret {S A} (a : A) : Dasp (ret a) :=
  DM_ret S (ASPStExc S) (@ordASPStExc S) (@ordASPStExc_eq1 S)
       (@obsASP S) (@obsASP_ret S) a.
Definition Dasp_bind {S A B} {w : ASPStExc S A} {wf : A -> ASPStExc S B}
  (m : Dasp w) (f : forall a, Dasp (wf a)) : Dasp (bind w wf) :=
  DM_bind S (ASPStExc S) (@ordASPStExc S) (@ordASPStExc_PreOrder S)
        (@ordASPStExc_eq1 S) (@ordASPStExc_bind S) (@obsASP S) (@obsASP_bind S) m f.
Definition Dasp_wkn {S A} {w w' : ASPStExc S A} (H : ordASPStExc w w') (m : Dasp w) : Dasp w' :=
  DM_wkn S (ASPStExc S) (@ordASPStExc S) (@ordASPStExc_PreOrder S) (@obsASP S) H m.
Definition Dasp_lift {S A} (m : stdivexcnd S A) : Dasp (obsASP m) :=
  DM_lift S (ASPStExc S) (@ordASPStExc S) (@ordASPStExc_PreOrder S) (@obsASP S) m.

Definition Ddslp {S A} (w : DSLPStExc S A) : Type :=
  DM S (DSLPStExc S) (@ordDSLPStExc S) (@obsDSLP S) w.
Definition Ddslp_op {S A} (w : DSLPStExc S A) : Type :=
  DMop S (DSLPStExc S) (@ordDSLPStExc S) (@obsDSLP S) w.

Definition Ddslp_ret {S A} (a : A) : Ddslp (ret a) :=
  DM_ret S (DSLPStExc S) (@ordDSLPStExc S) (@ordDSLPStExc_eq1 S)
       (@obsDSLP S) (@obsDSLP_ret S) a.
Definition Ddslp_bind {S A B} {w : DSLPStExc S A} {wf : A -> DSLPStExc S B}
  (m : Ddslp w) (f : forall a, Ddslp (wf a)) : Ddslp (bind w wf) :=
  DM_bind S (DSLPStExc S) (@ordDSLPStExc S) (@ordDSLPStExc_PreOrder S)
        (@ordDSLPStExc_eq1 S) (@ordDSLPStExc_bind S) (@obsDSLP S) (@obsDSLP_bind S) m f.
Definition Ddslp_wkn {S A} {w w' : DSLPStExc S A} (H : ordDSLPStExc w w') (m : Ddslp w) : Ddslp w' :=
  DM_wkn S (DSLPStExc S) (@ordDSLPStExc S) (@ordDSLPStExc_PreOrder S) (@obsDSLP S) H m.
Definition Ddslp_lift {S A} (m : stdivexcnd S A) : Ddslp (obsDSLP m) :=
  DM_lift S (DSLPStExc S) (@ordDSLPStExc S) (@ordDSLPStExc_PreOrder S) (@obsDSLP S) m.

(* ================================================================= *)
(** ** No Dijkstra monad over [DSPStExc] or [ASLPStExc]              *)
(* ================================================================= *)

(** [obsDSP] and [obsASLP] ARE monad morphisms — the [_ret] / [_bind]
    laws above — and their targets ARE monads.  What fails is the
    [Pos]-enrichment: [bindDSPStExc] and [bindASLPStExc] recover the
    underlying relation by PROBING their arguments ([dsp_recov],
    [aslp_recov]), so each argument occurs negatively and [bind] is not
    monotone in the refinement order.  Since [bind^D] is typed at
    [bind^W] of the indices, that is exactly the step that cannot be
    taken.  Both counterexamples are realised by actual programs, so
    they are obstructions in the Dijkstra monad and not just in the
    abstract order. *)
Section NoGo.

  (** A program with a prescribed terminating-outcome relation and no
      divergence: [stdivexcnd] is exactly a set of outcomes per state, so
      every relation is realised by a program. *)
  Definition progOf {S A} (R : S -> option (A * S) -> Prop) : stdivexcnd S A :=
    mkStateT (fun s => @mkOptionT (optionT SetM) _ (@mkOptionT SetM _
      (fun oa => match oa with Some r => R s r | None => False end))).

  Lemma progOf_outcomes {S A} (R : S -> option (A * S) -> Prop) s r :
    unOptionT (unOptionT (runStateT (progOf R) s)) (Some r) <-> R s r.
  Proof. cbn. split; intro H; exact H. Qed.

  (** [x] reaches [Some (tt,1)] from [0] only. *)
  Definition xR : nat -> option (unit * nat) -> Prop :=
    fun s r => s = 0 /\ r = Some (tt, 1).
  (** [x'] does that too, and additionally reaches [Some (tt,7)] from [5].
      That extra outcome is invisible to the DSP order, because the DSP
      order constrains [x'] only at outcomes [x] can already reach. *)
  Definition xR' : nat -> option (unit * nat) -> Prop :=
    fun s r => (s = 0 /\ r = Some (tt, 1)) \/ (s = 5 /\ r = Some (tt, 7)).
  (** [k] merges states [1] and [7] onto the same outcome. *)
  Definition kR : nat -> option (unit * nat) -> Prop :=
    fun s r => (s = 1 \/ s = 7) /\ r = Some (tt, 9).

  Definition xP  : stdivexcnd nat unit := progOf xR.
  Definition xP' : stdivexcnd nat unit := progOf xR'.
  Definition kP  : unit -> stdivexcnd nat unit := fun _ => progOf kR.

  Lemma dsp_x_le_x' : ordDSPStExc (obsDSP xP) (obsDSP xP').
  Proof.
    intros pre r H. apply getProgDSP_obsDSP in H. destruct H as [[s [Hp Hr]] Hall].
    unfold xP, progOf in Hr. cbn in Hr. unfold xR in Hr. destruct Hr as [-> ->].
    apply getProgDSP_obsDSP. split.
    - exists 0. split; [ exact Hp |]. cbn. unfold xR'. left. split; reflexivity.
    - intros s' Hs'. cbn in Hs'. unfold xR' in Hs'.
      destruct Hs' as [[-> _] | [_ Heq]]; [| discriminate Heq ].
      apply Hall. cbn. unfold xR. split; reflexivity.
  Qed.

  Lemma dsp_bind_not_le :
    ~ ordDSPStExc (obsDSP (xP >>= kP)) (obsDSP (xP' >>= kP)).
  Proof.
    intro Hc.
    specialize (Hc (fun s => s = 0) (Some (tt, 9))).
    assert (Hpre : getDSPStExc (obsDSP (xP >>= kP)) (fun s => s = 0) (Some (tt, 9))).
    { apply getProgDSP_obsDSP. split.
      - exists 0. split; [ reflexivity |].
        apply (outcomes_bind nat). exists (Some (Some (tt, 1))). split.
        + cbn. unfold xR. split; reflexivity.
        + cbn. unfold kR. split; [ left; reflexivity | reflexivity ].
      - intros s Hs. apply (outcomes_bind nat) in Hs.
        destruct Hs as [oy [Hx Hk]]. destruct oy as [[[[] s']|]|].
        + cbn in Hx. unfold xR in Hx. exact (proj1 Hx).
        + cbn in Hx. unfold xR in Hx. destruct Hx as [_ Heq]. discriminate Heq.
        + cbn in Hx. destruct Hx. }
    specialize (Hc Hpre). apply getProgDSP_obsDSP in Hc.
    destruct Hc as [_ Hall]. specialize (Hall 5).
    assert (H5 : unOptionT (unOptionT (runStateT (xP' >>= kP) 5)) (Some (Some (tt, 9)))).
    { apply (outcomes_bind nat). exists (Some (Some (tt, 7))). split.
      - cbn. unfold xR'. right. split; reflexivity.
      - cbn. unfold kR. split; [ right; reflexivity | reflexivity ]. }
    specialize (Hall H5). discriminate Hall.
  Qed.

End NoGo.

Section NoGo2.

  #[global] Instance ordDSPStExc_PreOrder {S A} : PreOrder (@ordDSPStExc S A).
  Proof.
    constructor.
    - intros w pre r H. exact H.
    - intros w1 w2 w3 H1 H2 pre r H. exact (H2 pre r (H1 pre r H)).
  Qed.

  #[global] Instance ordASLPStExc_PreOrder {S A} : PreOrder (@ordASLPStExc S A).
  Proof.
    constructor.
    - intros w pre r H. exact H.
    - intros w1 w2 w3 H1 H2 pre r H. exact (H2 pre r (H1 pre r H)).
  Qed.

  Lemma ordDSPStExc_eq1 {S A} (w w' : DSPStExc S A) : eq1 w w' -> ordDSPStExc w w'.
  Proof. intros H pre r Hp. apply (H pre r). exact Hp. Qed.

  Lemma ordASLPStExc_eq1 {S A} (w w' : ASLPStExc S A) : eq1 w w' -> ordASLPStExc w w'.
  Proof. intros H pre r Hp. apply (H pre r). exact Hp. Qed.

  (** The obstruction, stated on the Dijkstra side: [xP] meets the spec
      [obsDSP xP'] and [kP a] meets [obsDSP (kP a)], but the bind of the
      carriers does NOT meet the bind of the specs. *)
  Theorem dsp_bindD_untypeable :
    ordDSPStExc (obsDSP xP) (obsDSP xP') /\
    ~ ordDSPStExc (obsDSP (xP >>= kP))
        (bind (obsDSP xP') (fun a => obsDSP (kP a))).
  Proof.
    split; [ exact dsp_x_le_x' |].
    intro Hc. apply dsp_bind_not_le.
    etransitivity; [ exact Hc |].
    apply ordDSPStExc_eq1. symmetry. apply obsDSP_bind.
  Qed.

  (** Consequently [bind] is not monotone in the DSP order, so [DSPStExc]
      is not a Pos-enriched ("ordered") monad and DM4All's [Dtheta] does
      not apply to it. *)
  Theorem ordDSPStExc_bind_not_mono :
    ~ (forall A B (m m' : DSPStExc nat A) (k k' : A -> DSPStExc nat B),
          ordDSPStExc m m' -> (forall a, ordDSPStExc (k a) (k' a)) ->
          ordDSPStExc (bind m k) (bind m' k')).
  Proof.
    intro Hmono. apply dsp_bind_not_le.
    etransitivity; [ apply ordDSPStExc_eq1; apply obsDSP_bind |].
    etransitivity; [| apply ordDSPStExc_eq1; symmetry; apply obsDSP_bind ].
    apply Hmono; [ exact dsp_x_le_x' | intro a; reflexivity ].
  Qed.

End NoGo2.

Section NoGoASLP.

  (** The dual counterexample.  [yP] reaches [Some (tt,1)] from [0] and
      [Some (tt,3)] from [3]; [yP'] drops the first outcome entirely (an
      unreachable outcome is TOP for [obsASLP], so this is allowed by the
      order) and adds [7] to the second.  [kP2] merges [1] and [3]. *)
  Definition yR : nat -> option (unit * nat) -> Prop :=
    fun s r => (s = 0 /\ r = Some (tt, 1)) \/ (s = 3 /\ r = Some (tt, 3)).
  Definition yR' : nat -> option (unit * nat) -> Prop :=
    fun s r => (s = 3 \/ s = 7) /\ r = Some (tt, 3).
  Definition kR2 : nat -> option (unit * nat) -> Prop :=
    fun s r => (s = 1 \/ s = 3) /\ r = Some (tt, 9).

  Definition yP  : stdivexcnd nat unit := progOf yR.
  Definition yP' : stdivexcnd nat unit := progOf yR'.
  Definition kP2 : unit -> stdivexcnd nat unit := fun _ => progOf kR2.

  Lemma aslp_y_le_y' : ordASLPStExc (obsASLP yP) (obsASLP yP').
  Proof.
    intros pre r H. apply getProgASLP_obsASLP in H. apply getProgASLP_obsASLP.
    destruct (classic (r = Some (tt, 3))) as [-> | Hne].
    - assert (Hpre3 : pre 3).
      { destruct H as [[s [Hp Hr]] | Hall].
        - cbn in Hr. unfold yR in Hr.
          destruct Hr as [[_ Heq] | [-> _]]; [ discriminate Heq | exact Hp ].
        - apply Hall. cbn. unfold yR. right. split; reflexivity. }
      left. exists 3. split; [ exact Hpre3 |].
      cbn. unfold yR'. split; [ left; reflexivity | reflexivity ].
    - right. intros s Hs. cbn in Hs. unfold yR' in Hs.
      destruct Hs as [_ Heq]. destruct (Hne Heq).
  Qed.

  Lemma aslp_bind_not_le :
    ~ ordASLPStExc (obsASLP (yP >>= kP2)) (obsASLP (yP' >>= kP2)).
  Proof.
    intro Hc. specialize (Hc (fun s => s = 0) (Some (tt, 9))).
    assert (Hpre : getASLPStExc (obsASLP (yP >>= kP2)) (fun s => s = 0) (Some (tt, 9))).
    { apply getProgASLP_obsASLP. left. exists 0. split; [ reflexivity |].
      apply (outcomes_bind nat). exists (Some (Some (tt, 1))). split.
      - cbn. unfold yR. left. split; reflexivity.
      - cbn. unfold kR2. split; [ left; reflexivity | reflexivity ]. }
    specialize (Hc Hpre). apply getProgASLP_obsASLP in Hc.
    assert (H7 : unOptionT (unOptionT (runStateT (yP' >>= kP2) 7)) (Some (Some (tt, 9)))).
    { apply (outcomes_bind nat). exists (Some (Some (tt, 3))). split.
      - cbn. unfold yR'. split; [ right; reflexivity | reflexivity ].
      - cbn. unfold kR2. split; [ right; reflexivity | reflexivity ]. }
    destruct Hc as [[s [Hs Hreach]] | Hall].
    - cbn in Hs. subst s. apply (outcomes_bind nat) in Hreach.
      destruct Hreach as [oy [Hy Hk]]. destruct oy as [[[[] n]|]|].
      + cbn in Hy. unfold yR' in Hy. destruct Hy as [Hn _]. sauto limit: 200.
      + cbn in Hy. unfold yR' in Hy. destruct Hy as [_ Heq]. discriminate Heq.
      + cbn in Hy. destruct Hy.
    - specialize (Hall 7 H7). discriminate Hall.
  Qed.

  Theorem aslp_bindD_untypeable :
    ordASLPStExc (obsASLP yP) (obsASLP yP') /\
    ~ ordASLPStExc (obsASLP (yP >>= kP2))
        (bind (obsASLP yP') (fun a => obsASLP (kP2 a))).
  Proof.
    split; [ exact aslp_y_le_y' |].
    intro Hc. apply aslp_bind_not_le.
    etransitivity; [ exact Hc |].
    apply ordASLPStExc_eq1. symmetry. apply obsASLP_bind.
  Qed.

  Theorem ordASLPStExc_bind_not_mono :
    ~ (forall A B (m m' : ASLPStExc nat A) (k k' : A -> ASLPStExc nat B),
          ordASLPStExc m m' -> (forall a, ordASLPStExc (k a) (k' a)) ->
          ordASLPStExc (bind m k) (bind m' k')).
  Proof.
    intro Hmono. apply aslp_bind_not_le.
    etransitivity; [ apply ordASLPStExc_eq1; apply obsASLP_bind |].
    etransitivity; [| apply ordASLPStExc_eq1; symmetry; apply obsASLP_bind ].
    apply Hmono; [ exact aslp_y_le_y' | intro a; reflexivity ].
  Qed.

End NoGoASLP.

(** Neither failure is an artifact of how [bind] is WRITTEN.  Both
    [dsp_bind_not_le] and [aslp_bind_not_le] mention no [bind] at all --
    they are statements about the observation and the order alone -- so
    any operation that makes the observation a monad morphism inherits
    them.  In particular, defining [bindDSPStExc] directly instead of as
    a conjunction of an ASP-bind and a DSLP-bind changes nothing. *)

Theorem no_monotone_dsp_bind
  (bnd : forall A B, DSPStExc nat A -> (A -> DSPStExc nat B) -> DSPStExc nat B)
  (Hmorph : forall A B (x : stdivexcnd nat A) (f : A -> stdivexcnd nat B),
      eq1 (obsDSP (x >>= f)) (bnd A B (obsDSP x) (fun a => obsDSP (f a)))) :
  ~ (forall A B (m m' : DSPStExc nat A) (k : A -> DSPStExc nat B),
        ordDSPStExc m m' -> ordDSPStExc (bnd A B m k) (bnd A B m' k)).
Proof.
  intro Hmono. apply dsp_bind_not_le.
  etransitivity; [ apply ordDSPStExc_eq1; apply (Hmorph _ _ xP kP) |].
  etransitivity; [| apply ordDSPStExc_eq1; symmetry; apply (Hmorph _ _ xP' kP) ].
  apply Hmono. exact dsp_x_le_x'.
Qed.

Theorem no_monotone_aslp_bind
  (bnd : forall A B, ASLPStExc nat A -> (A -> ASLPStExc nat B) -> ASLPStExc nat B)
  (Hmorph : forall A B (x : stdivexcnd nat A) (f : A -> stdivexcnd nat B),
      eq1 (obsASLP (x >>= f)) (bnd A B (obsASLP x) (fun a => obsASLP (f a)))) :
  ~ (forall A B (m m' : ASLPStExc nat A) (k : A -> ASLPStExc nat B),
        ordASLPStExc m m' -> ordASLPStExc (bnd A B m k) (bnd A B m' k)).
Proof.
  intro Hmono. apply aslp_bind_not_le.
  etransitivity; [ apply ordASLPStExc_eq1; apply (Hmorph _ _ yP kP2) |].
  etransitivity; [| apply ordASLPStExc_eq1; symmetry; apply (Hmorph _ _ yP' kP2) ].
  apply Hmono. exact aslp_y_le_y'.
Qed.

(** The probing is not forced by the DSP shape either.  The reachable
    set of [r] is the INTERSECTION of the preconditions the transformer
    accepts, so it can be recovered positively -- and, unlike
    [dsp_recov], constructively: no [NNPP], no co-singleton, no negation.
    A direct [bind] is then "recover both relations, compose, take the
    DSP of the composite".  What it cannot avoid is the VARIANCE: the
    recovered relation shrinks as [w] grows, because [w] occurs in the
    antecedent. *)
Section DSPDirectRecovery.
  Variable S : Type.

  Definition dspShape {A} (R : S -> option (A * S) -> Prop) : @SPStExc S A :=
    fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s).

  Definition relOf {A} (w : @SPStExc S A) : S -> option (A * S) -> Prop :=
    fun s r => w (fun _ => True) r /\ (forall q, w q r -> q s).

  Lemma relOf_dspShape {A} (R : S -> option (A * S) -> Prop) s r :
    relOf (dspShape R) s r <-> R s r.
  Proof.
    unfold relOf, dspShape. split.
    - intros [[[s0 [_ Hs0]] _] Hall].
      apply (Hall (fun t => R t r)).
      split; [ exists s0; split; exact Hs0 | intros t Ht; exact Ht ].
    - intro Hr. split.
      + split; [ exists s; split; [ exact I | exact Hr ] | intros t _; exact I ].
      + intros q [_ Hsub]. exact (Hsub s Hr).
  Qed.

End DSPDirectRecovery.

(* ================================================================= *)
(** ** Triples as Dijkstra typings                                   *)
(* ================================================================= *)

(** Of the four (observation, direction) pairs, exactly the two that
    [NewGaloisConnections.v] calls "relation inclusions" — ASP/[Over] and
    DSLP/[Under] — are Dijkstra typings in the GLOBAL order, and those
    two are exact.  The other two are characterised only in the
    [At]-order, which is not an order on a spec MONAD: see
    [Dasp_op_under_iff] for what the global order asks instead. *)
Section SPTripleBridges.

  Variable S : Type.

  (** ASP / [Over]: an exact Dijkstra typing (no side condition). *)
  #[program] Definition ofTripleASPOver {A} (prog : stdivexcnd S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop)
    (H : tripleASP prog Over pre post) : Dasp (pp2asp_over pre post) := prog.
  Next Obligation. cbn beta. exact (proj1 (gen_asp_over S (obsASP prog) pre post) H). Qed.

  Lemma toTripleASPOver {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (d : Dasp (pp2asp_over pre post)) :
    tripleASP (proj1_sig d) Over pre post.
  Proof. exact (proj2 (gen_asp_over S (obsASP (proj1_sig d)) pre post) (proj2_sig d)). Qed.

  (** DSLP / [Under]: likewise exact. *)
  #[program] Definition ofTripleDSLPUnder {A} (prog : stdivexcnd S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop)
    (H : tripleDSLP prog Under pre post) : Ddslp_op (pp2dslp_under pre post) := prog.
  Next Obligation. cbn beta. exact (proj1 (gen_dslp_under S (obsDSLP prog) pre post) H). Qed.

  Lemma toTripleDSLPUnder {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (d : Ddslp_op (pp2dslp_under pre post)) :
    tripleDSLP (proj1_sig d) Under pre post.
  Proof. exact (proj2 (gen_dslp_under S (obsDSLP (proj1_sig d)) pre post) (proj2_sig d)). Qed.

  (** ASP / [Under] is the odd one out.  Membership of [Dasp_op] at
      [pp2asp_under] is strictly STRONGER than the triple: the global order
      quantifies over all preconditions, and that forces EVERY [pre]-state
      to reach EVERY [post]-outcome, where the triple asks only that SOME
      [pre]-state does. *)
  Lemma Dasp_op_under_iff {A} (prog : stdivexcnd S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    ordASPStExc (pp2asp_under pre post) (obsASP prog) <->
    (forall s r, pre s -> post r -> unOptionT (unOptionT (runStateT prog s)) (Some r)).
  Proof.
    split.
    - intros H s r Hpre Hpost.
      destruct (H (fun t => t = s) r
                  (ex_intro _ s (conj eq_refl (conj Hpre Hpost)))) as [s' [-> Hr]].
      exact Hr.
    - intros H p r [s [Hp [Hpre Hpost]]].
      exists s. split; [ exact Hp | exact (H s r Hpre Hpost) ].
  Qed.

  (** Whatever the index [w] is, membership of [DMop] is a RELATION
      INCLUSION: [SingletonProg] makes [w] the ASP of its own singleton
      values, so the global order can only ever compare those values,
      state by state, with the reachability relation of the program. *)
  Lemma Dasp_op_relational {A} (w : ASPStExc S A) (prog : stdivexcnd S A) :
    ordASPStExc w (obsASP prog) <->
    (forall s r, getASPStExc w (fun t => t = s) r ->
                 unOptionT (unOptionT (runStateT prog s)) (Some r)).
  Proof.
    split.
    - intros H s r Hw.
      destruct (H (fun t => t = s) r Hw) as [s' [-> Hr]]. exact Hr.
    - intros Hrel p r Hw.
      destruct (proj1 (getProg_singleton S w p r) Hw) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (Hrel s0 r Hs) ].
  Qed.

  Lemma toTripleASPUnder {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hne : exists s, pre s) (d : Dasp_op (pp2asp_under pre post)) :
    tripleASP (proj1_sig d) Under pre post.
  Proof.
    intros r Hpost. apply (proj2_sig d pre r).
    apply tASPunder_at; [ exact Hne | exact Hpost ].
  Qed.

End SPTripleBridges.

(** The three programs that show the [Under] triple is not an inclusion:
    [r0] is reached from [0] by one, from [1] by the other, and by
    neither in the third. *)
Definition aspU1 : stdivexcnd nat unit :=
  progOf (fun s (r : option (unit * nat)) => s = 0 /\ r = Some (tt, 0)).
Definition aspU2 : stdivexcnd nat unit :=
  progOf (fun s (r : option (unit * nat)) => s = 1 /\ r = Some (tt, 0)).
Definition aspU0 : stdivexcnd nat unit :=
  progOf (fun (_ : nat) (_ : option (unit * nat)) => False).

(** The obstruction, in full: NO index whatsoever represents an ASP
    [Under] triple.  Membership is always a relation inclusion
    [R_w <= reach prog] ([Dasp_op_relational]), and the class of
    programs cut out by a fixed inclusion is closed under INTERSECTION
    of reachability relations.  The [Under] triple is not: [aspU1] and
    [aspU2] both satisfy it, their intersection [aspU0] does not.  So no
    [w] can have the triple as its fibre -- which is a statement about
    the ASP ORDER, not about the Dijkstra construction, and it is why
    [NewGaloisConnections.v] characterises this direction only in the
    [At]-order. *)
Theorem no_asp_under_index :
  ~ exists w : ASPStExc nat unit,
      forall prog : stdivexcnd nat unit,
        ordASPStExc w (obsASP prog) <->
        tripleASP prog Under (fun _ => True)
          (fun r : option (unit * nat) => r = Some (tt, 0)).
Proof.
  intros [w Hiff].
  assert (H1 : ordASPStExc w (obsASP aspU1)).
  { apply Hiff. intros r ->. exists 0. split; [ exact I |].
    apply progOf_outcomes. split; reflexivity. }
  assert (H2 : ordASPStExc w (obsASP aspU2)).
  { apply Hiff. intros r ->. exists 1. split; [ exact I |].
    apply progOf_outcomes. split; reflexivity. }
  pose proof (proj1 (Dasp_op_relational nat w aspU1) H1) as R1.
  pose proof (proj1 (Dasp_op_relational nat w aspU2) H2) as R2.
  assert (H0 : ordASPStExc w (obsASP aspU0)).
  { apply (Dasp_op_relational nat). intros s r Hw.
    pose proof (proj1 (progOf_outcomes _ s r) (R1 s r Hw)) as [E1 _].
    pose proof (proj1 (progOf_outcomes _ s r) (R2 s r Hw)) as [E2 _].
    subst s. discriminate E2. }
  destruct (proj1 (Hiff aspU0) H0 (Some (tt, 0)) eq_refl) as [s [_ Hr]].
  exact (proj1 (progOf_outcomes _ s (Some (tt, 0))) Hr).
Qed.

(** Could a DIFFERENT order on [ASPStExc] repair this?  The fibre of an
    index is a principal up-set, so the question is whether the [Under]
    fibre can be made principal.  It can -- by comparing only the IMAGES
    of the fixed precondition, which is the [At]-order that
    [gen_asp_under] already uses.  But that order is not a
    [Pos]-enrichment: [bind] re-binds the precondition slot to the
    INTERMEDIATE states ([bindASPStExc] feeds [m pre (Some (a, s0))] to
    [k a]), so two continuations with the same image from [pre] can still
    disagree once they are run at the states [m] actually produced. *)
Definition aspK0 : unit -> stdivexcnd nat unit :=
  fun _ => progOf (fun s (r : option (unit * nat)) => s = 0 /\ r = Some (tt, 9)).
Definition aspK1 : unit -> stdivexcnd nat unit :=
  fun _ => progOf (fun s (r : option (unit * nat)) => s = 1 /\ r = Some (tt, 9)).

Theorem ordASPStExcAt_bind_not_mono :
  ~ (forall A B (pre : nat -> Prop) (m : ASPStExc nat A) (k k' : A -> ASPStExc nat B),
        (forall a, ordASPStExcAt pre (k a) (k' a)) ->
        ordASPStExcAt pre (bind m k) (bind m k')).
Proof.
  intro Hmono.
  assert (Hk : forall a, ordASPStExcAt (fun _ : nat => True)
                           (obsASP (aspK0 a)) (obsASP (aspK1 a))).
  { intros a r [s [_ Hr]]. apply progOf_outcomes in Hr. destruct Hr as [_ ->].
    exists 1. split; [ exact I |]. apply progOf_outcomes. split; reflexivity. }
  specialize (Hmono unit unit (fun _ => True) (obsASP aspU1)
                (fun a => obsASP (aspK0 a)) (fun a => obsASP (aspK1 a)) Hk
                (Some (tt, 9))).
  assert (Hin : getASPStExc (bind (obsASP aspU1) (fun a => obsASP (aspK0 a)))
                  (fun _ => True) (Some (tt, 9))).
  { apply (obsASP_bind nat aspU1 aspK0). exists 0. split; [ exact I |].
    apply (outcomes_bind nat). exists (Some (Some (tt, 0))). split.
    - apply progOf_outcomes. split; reflexivity.
    - apply progOf_outcomes. split; reflexivity. }
  specialize (Hmono Hin).
  apply (obsASP_bind nat aspU1 aspK1) in Hmono.
  destruct Hmono as [s [_ Hr]]. apply (outcomes_bind nat) in Hr.
  destruct Hr as [oy [Hx Hk2]]. destruct oy as [[[[] n]|]|].
  - apply progOf_outcomes in Hx. destruct Hx as [_ Heq].
    injection Heq as Heq2. subst n.
    apply progOf_outcomes in Hk2. destruct Hk2 as [Hn _]. discriminate Hn.
  - apply progOf_outcomes in Hx. destruct Hx as [_ Heq]. discriminate Heq.
  - cbn in Hx. exact Hx.
Qed.

(** What DOES characterise the triple is [tripleASPDefEq] above: the
    index [pp2_under pre post] in the UNRESTRICTED [SPStExc], under the
    same pointwise order [ordSPStExc].  So the missing ingredient is not
    an order but a carrier -- [pp2_under] is not [SingletonProg], which
    is exactly how it can name [pre] ("[pre <= p]") instead of being
    determined by its singleton values. *)

(* ================================================================= *)
(** ** [DSP] / [ASLP]: everything except [bind]                      *)
(* ================================================================= *)

(** [DM] itself, and [ret]/[wkn]/[lift], need only the preorder and the
    morphism laws, so they exist for all four observations.  [bind] is
    the single piece that needs the enrichment, and by
    [ordDSPStExc_bind_not_mono] / [ordASLPStExc_bind_not_mono] these two
    do not have it. *)
(** DSP / ASLP: everything except [bind] *)

Definition Ddsp {S A} (w : DSPStExc S A) : Type :=
  DM S (DSPStExc S) (@ordDSPStExc S) (@obsDSP S) w.
Definition Ddsp_op {S A} (w : DSPStExc S A) : Type :=
  DMop S (DSPStExc S) (@ordDSPStExc S) (@obsDSP S) w.
Definition Daslp {S A} (w : ASLPStExc S A) : Type :=
  DM S (ASLPStExc S) (@ordASLPStExc S) (@obsASLP S) w.
Definition Daslp_op {S A} (w : ASLPStExc S A) : Type :=
  DMop S (ASLPStExc S) (@ordASLPStExc S) (@obsASLP S) w.

Definition Ddsp_ret {S A} (a : A) : Ddsp (ret a) :=
  DM_ret S (DSPStExc S) (@ordDSPStExc S) (@ordDSPStExc_eq1 S) (@obsDSP S) (@obsDSP_ret S) a.
Definition Ddsp_wkn {S A} {w w' : DSPStExc S A} (H : ordDSPStExc w w') (m : Ddsp w) : Ddsp w' :=
  DM_wkn S (DSPStExc S) (@ordDSPStExc S) (@ordDSPStExc_PreOrder S) (@obsDSP S) H m.
Definition Ddsp_lift {S A} (m : stdivexcnd S A) : Ddsp (obsDSP m) :=
  DM_lift S (DSPStExc S) (@ordDSPStExc S) (@ordDSPStExc_PreOrder S) (@obsDSP S) m.
Definition Ddsp_op_wkn {S A} {w w' : DSPStExc S A} (H : ordDSPStExc w' w) (m : Ddsp_op w)
  : Ddsp_op w' :=
  DMop_wkn S (DSPStExc S) (@ordDSPStExc S) (@ordDSPStExc_PreOrder S) (@obsDSP S) H m.

Definition Daslp_ret {S A} (a : A) : Daslp (ret a) :=
  DM_ret S (ASLPStExc S) (@ordASLPStExc S) (@ordASLPStExc_eq1 S) (@obsASLP S) (@obsASLP_ret S) a.
Definition Daslp_wkn {S A} {w w' : ASLPStExc S A} (H : ordASLPStExc w w') (m : Daslp w) : Daslp w' :=
  DM_wkn S (ASLPStExc S) (@ordASLPStExc S) (@ordASLPStExc_PreOrder S) (@obsASLP S) H m.
Definition Daslp_lift {S A} (m : stdivexcnd S A) : Daslp (obsASLP m) :=
  DM_lift S (ASLPStExc S) (@ordASLPStExc S) (@ordASLPStExc_PreOrder S) (@obsASLP S) m.

(* ================================================================= *)
(** ** The examples, as Dijkstra typings                             *)
(* ================================================================= *)

(** The examples, as Dijkstra typings *)

Definition postGe42SP : option (unit * nat) -> Prop :=
  fun r => match r with Some (_, s') => s' >= 42 | None => False end.

(** ASP / [Over] — exact typings. *)
Definition progA_all_D : Dasp (pp2asp_over (fun _ : nat => True) postGe42SP) :=
  ofTripleASPOver nat progA _ _ progA_all.

Definition progB_not_None_D :
  Dasp (pp2asp_over (fun _ : nat => True) (fun r : option (unit * nat) => r <> None)) :=
  ofTripleASPOver nat progB _ _ progB_not_None.

(** ASP / [Under] — typeable exactly when EVERY [pre]-state reaches EVERY
    [post]-outcome, which for these three holds because [progA] / [progB]
    overwrite the state and [pre] is [True]. *)
#[program] Definition progA_42_Dop :
  Dasp_op (pp2asp_under (fun _ : nat => True)
             (fun r : option (unit * nat) => r = Some (tt, 42))) := progA.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r _ ->. cbn. sauto limit: 200.
Qed.

#[program] Definition progA_43_Dop :
  Dasp_op (pp2asp_under (fun _ : nat => True)
             (fun r : option (unit * nat) => r = Some (tt, 43))) := progA.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r _ ->. cbn. sauto limit: 200.
Qed.

#[program] Definition progB_42_Dop :
  Dasp_op (pp2asp_under (fun _ : nat => True)
             (fun r : option (unit * nat) => r = Some (tt, 42))) := progB.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r _ ->. cbn. sauto limit: 200.
Qed.

#[program] Definition progRet_asp_Dop : Dasp_op (pp2asp_under preEq0 postEq0) := progRet.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r Hpre Hpost.
  unfold preEq0 in Hpre. unfold postEq0 in Hpost. subst s r. cbn. reflexivity.
Qed.

(** ...and NOT typeable when only SOME [pre]-state reaches the outcome —
    which is the normal situation for incorrectness triples.  Both triples
    below hold; neither is a Dijkstra typing. *)
Theorem progEx_under_not_Dasp_op :
  forall d : Dasp_op (pp2asp_under (fun _ : nat => True)
                        (fun r : option (unit * nat) => r = Some (tt, 1))),
    proj1_sig d <> progEx.
Proof.
  intros d Heq.
  pose proof (proj1 (Dasp_op_under_iff nat (proj1_sig d) _ _) (proj2_sig d)) as H.
  rewrite Heq in H. specialize (H 5 (Some (tt, 1)) I eq_refl). cbn in H.
  sauto limit: 200.
Qed.

Theorem example_incorrect_1_not_Dasp_op :
  forall d : Dasp_op (pp2asp_under (fun '(_, _, z) => z = 11)
    (fun r : option (unit * (nat * nat * nat)) =>
       match r with
       | Some (tt, (x, y, z)) =>
           z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
       | _ => False
       end)),
    proj1_sig d <> example_state.
Proof.
  intros d Heq.
  pose proof (proj1 (Dasp_op_under_iff _ (proj1_sig d) _ _) (proj2_sig d)) as H.
  rewrite Heq in H.
  specialize (H (0, 1, 11) (Some (tt, (2, 3, 42))) eq_refl
                (conj eq_refl (conj eq_refl eq_refl))).
  cbn in H. sauto limit: 200.
Qed.

(** DSLP / [Under] — exact typings, from the [progEx] point facts. *)
(** The same [progEx] outcome IS typeable once [pre] is the singleton
    [P0]: then "some [pre]-state reaches it" and "every [pre]-state
    reaches it" coincide.  Contrast [progEx_under_not_Dasp_op], which is
    the identical postcondition at [pre = True]. *)
#[program] Definition progEx_asp_1_Dop :
  Dasp_op (pp2asp_under P0 (fun r : option (unit * nat) => r = Some (tt, 1))) := progEx.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r Hpre ->.
  unfold P0 in Hpre. subst s. cbn. sauto limit: 200.
Qed.

Theorem example_incorrect_2_not_Dasp_op :
  forall d : Dasp_op (pp2asp_under (fun _ : nat * nat * nat => True)
    (fun r : option (unit * (nat * nat * nat)) =>
       match r with Some (tt, (_, _, z)) => z = 42 | _ => False end)),
    proj1_sig d <> example_state.
Proof.
  intros d Heq.
  pose proof (proj1 (Dasp_op_under_iff _ (proj1_sig d) _ _) (proj2_sig d)) as H.
  rewrite Heq in H.
  specialize (H (1, 0, 0) (Some (tt, (0, 1, 42))) I eq_refl).
  cbn in H. sauto limit: 200.
Qed.

Theorem progEx_dslp_under : tripleDSLP progEx Under P0
  (fun r : option (unit * nat) => r = Some (tt, 1)).
Proof. intros r ->. exact progEx_dslp_1. Qed.

Definition progEx_dslp_D :
  Ddslp_op (pp2dslp_under P0 (fun r : option (unit * nat) => r = Some (tt, 1))) :=
  ofTripleDSLPUnder nat progEx _ _ progEx_dslp_under.

Theorem progEx_dslp_None_under : tripleDSLP progEx Under P0
  (fun r : option (unit * nat) => r = None).
Proof. intros r ->. exact progEx_dslp_None. Qed.

Definition progEx_dslp_None_D :
  Ddslp_op (pp2dslp_under P0 (fun r : option (unit * nat) => r = None)) :=
  ofTripleDSLPUnder nat progEx _ _ progEx_dslp_None_under.

(** DSP / [Under] — the index exists and [progRet] meets it; only [bind]
    is missing from this structure. *)
#[program] Definition pp2dsp_under {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : DSPStExc S A :=
  fun p r => (exists s, p s /\ (pre s /\ post r)) /\ (forall s, (pre s /\ post r) -> p s).
Next Obligation. exact (dsp_shape_wf S (fun s r => pre s /\ post r)). Qed.

Lemma toTripleDSPUnder {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  (Hne : exists s, pre s) (d : Ddsp_op (pp2dsp_under pre post)) :
  tripleDSP (proj1_sig d) Under pre post.
Proof.
  intros r Hpost. apply (proj2_sig d pre r). split.
  - destruct Hne as [s Hs]. exists s. split; [ exact Hs | split; [ exact Hs | exact Hpost ] ].
  - intros s [Hs _]. exact Hs.
Qed.

#[program] Definition progRet_dsp_Dop : Ddsp_op (pp2dsp_under preEq0 postEq0) := progRet.
Next Obligation.
  cbn beta. intros p r [[s [Hp [Hpre Hpost]]] Hall].
  unfold preEq0 in Hpre. unfold postEq0 in Hpost. subst s r.
  apply getProgDSP_obsDSP. split.
  - exists 0. split; [ exact Hp | cbn; reflexivity ].
  - intros s Hs. cbn in Hs. injection Hs as <-. exact Hp.
Qed.

(* ================================================================= *)
(** ** Nondeterministic choice at the spec level                     *)
(* ================================================================= *)

Section SPLattice.
  Variable S : Type.

  #[program] Definition joinASPStExc {A} (w1 w2 : ASPStExc S A) : ASPStExc S A :=
    fun pre r => getASPStExc w1 pre r \/ getASPStExc w2 pre r.
  Next Obligation.
    intros pre r.
    pose proof (proj2_sig w1 pre r) as H1. pose proof (proj2_sig w2 pre r) as H2.
    split.
    - intros [H|H].
      + destruct (proj1 H1 H) as [s0 [Hp Hs]]. exists s0. split; [exact Hp | left; exact Hs].
      + destruct (proj1 H2 H) as [s0 [Hp Hs]]. exists s0. split; [exact Hp | right; exact Hs].
    - intros [s0 [Hp [H|H]]].
      + left. apply H1. exists s0. split; [exact Hp | exact H].
      + right. apply H2. exists s0. split; [exact Hp | exact H].
  Qed.

  #[program] Definition meetDSLPStExc {A} (w1 w2 : DSLPStExc S A) : DSLPStExc S A :=
    fun pre r => getDSLPStExc w1 pre r /\ getDSLPStExc w2 pre r.
  Next Obligation.
    intros pre r.
    pose proof (proj2_sig w1 pre r) as H1. pose proof (proj2_sig w2 pre r) as H2.
    split.
    - intros [Ha Hb] s0 Hn. split;
        [ exact (proj1 H1 Ha s0 Hn) | exact (proj1 H2 Hb s0 Hn) ].
    - intro Hall. split;
        [ apply H1; intros s0 Hn; exact (proj1 (Hall s0 Hn))
        | apply H2; intros s0 Hn; exact (proj2 (Hall s0 Hn)) ].
  Qed.

  Lemma joinASPStExc_mono {A} (w1 w1' w2 w2' : ASPStExc S A) :
    ordASPStExc w1 w1' -> ordASPStExc w2 w2' ->
    ordASPStExc (joinASPStExc w1 w2) (joinASPStExc w1' w2').
  Proof.
    intros H1 H2 pre r [H|H]; [ left; exact (H1 pre r H) | right; exact (H2 pre r H) ].
  Qed.

  Lemma meetDSLPStExc_mono {A} (w1 w1' w2 w2' : DSLPStExc S A) :
    ordDSLPStExc w1 w1' -> ordDSLPStExc w2 w2' ->
    ordDSLPStExc (meetDSLPStExc w1 w2) (meetDSLPStExc w1' w2').
  Proof.
    intros H1 H2 pre r [Ha Hb]. split; [ exact (H1 pre r Ha) | exact (H2 pre r Hb) ].
  Qed.

  (** [orP] is a JOIN for the angelic (ASP) observation and a MEET for the
      demonic (DSLP) one. *)
  Lemma obsASP_or {A} (m1 m2 : stdivexcnd S A) :
    eq1 (obsASP (orP _ m1 m2)) (joinASPStExc (obsASP m1) (obsASP m2)).
  Proof.
    intros pre r. cbn. split.
    - intros [s [Hp [H|H]]]; [ left | right ]; exists s; split; assumption.
    - intros [[s [Hp H]] | [s [Hp H]]]; exists s; split;
        solve [ exact Hp | left; exact H | right; exact H ].
  Qed.

  Lemma obsDSLP_or {A} (m1 m2 : stdivexcnd S A) :
    eq1 (obsDSLP (orP _ m1 m2)) (meetDSLPStExc (obsDSLP m1) (obsDSLP m2)).
  Proof.
    intros pre r. cbn. split.
    - intro H. split; intros s Hs; apply H; [ left | right ]; exact Hs.
    - intros [H1 H2] s [Hs|Hs]; [ exact (H1 s Hs) | exact (H2 s Hs) ].
  Qed.
End SPLattice.

(** [orP] is not reachable from [ret]/[bind], so it gets its own rule,
    parametric in the binary spec combinator the observation turns it
    into: a JOIN for the angelic [obsASP], a MEET for the demonic
    [obsDSLP]. *)
Section DijkstraChoiceSP.
  Variable S : Type.
  Variable W : Type -> Type.
  Context {MW : Monad W} {EW : Eq1 W}.
  Variable ordW : forall A, W A -> W A -> Prop.
  Arguments ordW {A} _ _.
  Variable obs : forall A, stdivexcnd S A -> W A.
  Arguments obs {A} _.
  Variable comb : forall A, W A -> W A -> W A.
  Arguments comb {A} _ _.

  Hypothesis ordW_pre : forall A, PreOrder (@ordW A).
  Hypothesis ordW_eq1 : forall A (w w' : W A), eq1 w w' -> ordW w w'.
  Hypothesis comb_mono : forall A (w1 w1' w2 w2' : W A),
    ordW w1 w1' -> ordW w2 w2' -> ordW (comb w1 w2) (comb w1' w2').
  Hypothesis obs_or : forall A (m1 m2 : stdivexcnd S A),
    eq1 (obs (orP _ m1 m2)) (comb (obs m1) (obs m2)).

  #[local] Existing Instance ordW_pre.
  #[local] Obligation Tactic := (intros; cbn beta).

  #[program] Definition DM_or {A} {w1 w2 : W A}
    (m1 : DM S W (@ordW) (@obs) w1) (m2 : DM S W (@ordW) (@obs) w2)
    : DM S W (@ordW) (@obs) (comb w1 w2) :=
    orP _ (proj1_sig m1) (proj1_sig m2).
  Next Obligation.
    etransitivity; [ apply ordW_eq1; apply obs_or |].
    apply comb_mono; [ exact (proj2_sig m1) | exact (proj2_sig m2) ].
  Qed.

End DijkstraChoiceSP.

Definition Dasp_or {S A} {w1 w2 : ASPStExc S A} (m1 : Dasp w1) (m2 : Dasp w2)
  : Dasp (joinASPStExc S w1 w2) :=
  DM_or S (ASPStExc S) (@ordASPStExc S) (@obsASP S) (@joinASPStExc S)
      (@ordASPStExc_PreOrder S) (@ordASPStExc_eq1 S) (@joinASPStExc_mono S) (@obsASP_or S) m1 m2.

Definition Ddslp_or {S A} {w1 w2 : DSLPStExc S A} (m1 : Ddslp w1) (m2 : Ddslp w2)
  : Ddslp (meetDSLPStExc S w1 w2) :=
  DM_or S (DSLPStExc S) (@ordDSLPStExc S) (@obsDSLP S) (@meetDSLPStExc S)
      (@ordDSLPStExc_PreOrder S) (@ordDSLPStExc_eq1 S) (@meetDSLPStExc_mono S) (@obsDSLP_or S) m1 m2.

Definition progA_asp_compositional : Dasp _ :=
  Dasp_bind (Dasp_lift (put 42)) (fun _ =>
  Dasp_bind (Dasp_lift get)      (fun s : nat =>
  Dasp_or   (Dasp_lift (put s)) (Dasp_lift (put (s + 1))))).

Lemma progA_asp_compositional_carrier : proj1_sig progA_asp_compositional = progA.
Proof. reflexivity. Qed.

Lemma progA_asp_compositional_le :
  ordASPStExc (bind (obsASP (put 42)) (fun _ : unit =>
                bind (obsASP get) (fun s : nat =>
                  joinASPStExc nat (obsASP (put s)) (obsASP (put (s + 1))))))
              (pp2asp_over (fun _ : nat => True) postGe42SP).
Proof.
  intros p r H. cbn in H |- *. sauto limit: 300.
Qed.

Definition progA_all_compositional : Dasp (pp2asp_over (fun _ : nat => True) postGe42SP) :=
  Dasp_wkn progA_asp_compositional_le progA_asp_compositional.

Lemma progA_all_compositional_carrier : proj1_sig progA_all_compositional = progA.
Proof. reflexivity. Qed.
