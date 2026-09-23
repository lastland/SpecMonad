(** * Why DSP and ASLP have no Dijkstra presentation -- on any route.

    [Dijkstra_StDivExcNonDet_SPStExc.v] shows DSP and ASLP admit no
    ordered-monad Dijkstra monad under their own refinement order:
    [no_monotone_dsp_bind] / [no_monotone_aslp_bind] refute the
    [Pos]-enrichment for EVERY [bind] that makes the observation a monad
    morphism.  Two escape routes remain, and this file closes both.

    THE RELATIONAL ORDER.  [DSPMonad.v] / [ASLPMonad.v] prove DSP and ASLP
    ARE ordered monads under inclusion of the denoted relation
    ([ordDSPStRel], [OrderedMonad_DSPSt]).  So the DM4All construction goes
    through for that order -- and yields nothing: [DdspRel_membership] shows
    the fibre of an index [w] in that Dijkstra monad is the fibre, in the
    ASP Dijkstra monad, of the ASP index [aspOfDSP w] denoting the same
    relation, program for program ([DdspRel_to_DaspSt] /
    [DaspSt_to_DdspRel] are mutually inverse on carriers).  Its typings
    are relation inclusions, i.e. ASP/[Over] statements, never DSP
    triples.  ASLP is the same ([DaslpRel_membership]).

    THE GRADED ROUTE.  [Dijkstra_StDivNonDet_ASPUnder.v] types the
    ASP/[Under] triple with the precondition in the INDEX instead of the
    order, so [bind] needs no enrichment -- only that the triple family be
    CLOSED UNDER SEQUENCING with the continuation typed at the first
    stage's postcondition.  This file records, for all eight
    (reading, direction) pairs, whether that closure holds.  The composite
    postcondition follows the reading's [bind]: existential in the
    intermediate value for the angelic readings, universal for the demonic
    ones, their conjunction for DSP and their disjunction for ASLP.

      ASP  / Over   closed   [tripleASP_over_seq]
      ASP  / Under  closed   [tripleASP_under_seq]    (= [bindDU])
      DSLP / Over   closed   [tripleDSLP_over_seq]
      DSLP / Under  closed   [tripleDSLP_under_seq]
      DSP  / Under  closed   [tripleDSP_under_seq]
      ASLP / Over   closed   [tripleASLP_over_seq]
      DSP  / Over   NOT      [tripleDSP_over_not_seq]
      ASLP / Under  NOT      [tripleASLP_under_not_seq]

    The two failures are stated with the EMPTY continuation postcondition,
    so no choice of composite postcondition can repair them: both
    component triples hold and the composite reaches an outcome.  They are
    also the two genuinely new triples.  The other two DSP/ASLP triples
    are conjunctions of an ASP and a DSLP triple at the same [pre] and
    [post] ([tripleDSP_under_split], [tripleASLP_over_split]), which is
    why they are closed -- and why they add nothing.

    WHY.  A DSP/[Over] triple at [pre] says: every outcome reached ONLY
    from [pre]-states is in [post].  Typing a continuation at the first
    stage's postcondition [Q] loses which intermediate states are
    reachable at all; a state outside [Q] that the first stage never
    produces makes the continuation's own DSP/[Over] triple vacuous, yet
    the composite still reaches the outcome through the states the first
    stage does produce.  The reading is two-sided in the relation (it
    bounds [R^-1(r)] from above AND requires it nonempty), and a bound
    from both sides does not survive composition unless the intermediate
    assertion is exact.  ASLP/[Under] is the dual. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPArrowCore ASPArrowRel ASPMonad DSLPMonad
  DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.DijkstraMonads Require Import ASPUnderObstructions.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPSt_Arrow.

Import MonadNotation.
Open Scope monad_scope.

#[local] Existing Instance Monad_optionT.
#[local] Existing Instance Monad_stateT.

(* ================================================================= *)
(** ** The relational order: a Dijkstra monad, but ASP's              *)
(* ================================================================= *)

Section RelationalRoute.
  Variable S : Type.

  (** DM4All's [D] at the relational order, and at ASP's order. *)
  Definition DdspRel {A} (w : DSPSt S A) : Type :=
    { m : stdivnd S A | ordDSPStRel (obsDSP m) w }.
  Definition DaslpRel {A} (w : ASLPSt S A) : Type :=
    { m : stdivnd S A | ordASLPStRel (obsASLP m) w }.
  Definition DaspSt {A} (w : ASPSt S A) : Type :=
    { m : stdivnd S A | ordASPSt (obsASP m) w }.

  (** The ASP index denoting the same relation as a DSP / ASLP index. *)
  Definition aspOfDSP {A} (w : DSPSt S A) : ASPSt S A :=
    aspOfRelSt (fun s r => dspRel w (tt, s) r).
  Definition aspOfASLP {A} (w : ASLPSt S A) : ASPSt S A :=
    aspOfRelSt (fun s r => aslpRel w (tt, s) r).

  (** Membership is the SAME condition: the DSP index contributes only
      the relation it denotes. *)
  Lemma DdspRel_membership {A} (m : stdivnd S A) (w : DSPSt S A) :
    ordDSPStRel (obsDSP m) w <-> ordASPSt (obsASP m) (aspOfDSP w).
  Proof.
    rewrite ordASPSt_get. unfold ordDSPStRel, aspOfDSP. split.
    - intros H pre r Hm.
      destruct (proj1 (getProgASP_obsASP _ _ _ _) Hm) as [s [Hp Hr]].
      apply (proj2 (getASPSt_of _ _ _ _)). exists s. split; [ exact Hp |].
      apply H. unfold obsDSP. apply (proj2 (dspRelSt_of _ _ _)). exact Hr.
    - intros H [[] s] r Hd. unfold obsDSP in Hd.
      pose proof (proj1 (dspRelSt_of _ _ _) Hd) as Hr.
      assert (Hin : getASPSt (obsASP m) (fun t => t = s) r).
      { apply (proj2 (getProgASP_obsASP _ _ _ _)). exists s. split; [ reflexivity | exact Hr ]. }
      destruct (proj1 (getASPSt_of _ _ _ _) (H _ _ Hin)) as [t [Ht Hw]].
      subst t. exact Hw.
  Qed.

  Lemma DaslpRel_membership {A} (m : stdivnd S A) (w : ASLPSt S A) :
    ordASLPStRel (obsASLP m) w <-> ordASPSt (obsASP m) (aspOfASLP w).
  Proof.
    rewrite ordASPSt_get. unfold ordASLPStRel, aspOfASLP. split.
    - intros H pre r Hm.
      destruct (proj1 (getProgASP_obsASP _ _ _ _) Hm) as [s [Hp Hr]].
      apply (proj2 (getASPSt_of _ _ _ _)). exists s. split; [ exact Hp |].
      apply H. unfold obsASLP. apply (proj2 (aslpRelSt_of _ _ _)). exact Hr.
    - intros H [[] s] r Hd. unfold obsASLP in Hd.
      pose proof (proj1 (aslpRelSt_of _ _ _) Hd) as Hr.
      assert (Hin : getASPSt (obsASP m) (fun t => t = s) r).
      { apply (proj2 (getProgASP_obsASP _ _ _ _)). exists s. split; [ reflexivity | exact Hr ]. }
      destruct (proj1 (getASPSt_of _ _ _ _) (H _ _ Hin)) as [t [Ht Hw]].
      subst t. exact Hw.
  Qed.

  Definition DdspRel_to_DaspSt {A} {w : DSPSt S A} (d : DdspRel w)
    : DaspSt (aspOfDSP w) :=
    exist _ (proj1_sig d) (proj1 (DdspRel_membership _ w) (proj2_sig d)).

  Definition DaspSt_to_DdspRel {A} {w : DSPSt S A} (d : DaspSt (aspOfDSP w))
    : DdspRel w :=
    exist _ (proj1_sig d) (proj2 (DdspRel_membership _ w) (proj2_sig d)).

  Lemma DdspRel_DaspSt_carrier {A} {w : DSPSt S A} (d : DdspRel w) :
    proj1_sig (DdspRel_to_DaspSt d) = proj1_sig d.
  Proof. reflexivity. Qed.

  Lemma DaspSt_DdspRel_carrier {A} {w : DSPSt S A} (d : DaspSt (aspOfDSP w)) :
    proj1_sig (DaspSt_to_DdspRel d) = proj1_sig d.
  Proof. reflexivity. Qed.

End RelationalRoute.

(* ================================================================= *)
(** ** The graded route: closure of the triples under sequencing      *)
(* ================================================================= *)

Section Sequencing.
  Variable S : Type.

  (* ---- the six that are closed ---- *)

  Theorem tripleASP_over_seq {A B} (m : stdivnd S A) (k : A -> stdivnd S B)
    (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
    tripleASP m Over P Q ->
    (forall a, tripleASP (k a) Over (fun s => Q (a, s)) (R a)) ->
    tripleASP (m >>= k) Over P (fun r => exists a, R a r).
  Proof.
    unfold tripleASP. intros Hm Hk r Hobs.
    apply getProgASP_obsASP in Hobs. destruct Hobs as [s [HP Hr]].
    apply (outcomes_bind S) in Hr. destruct Hr as [a [s' [Hm' Hk']]].
    exists a. apply (Hk a). apply getProgASP_obsASP. exists s'. split; [| exact Hk' ].
    apply Hm. apply getProgASP_obsASP. exists s. split; [ exact HP | exact Hm' ].
  Qed.

  Theorem tripleASP_under_seq {A B} (m : stdivnd S A) (k : A -> stdivnd S B)
    (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
    tripleASP m Under P Q ->
    (forall a, tripleASP (k a) Under (fun s => Q (a, s)) (R a)) ->
    tripleASP (m >>= k) Under P (fun r => exists a, R a r).
  Proof.
    unfold tripleASP. intros Hm Hk r [a HR].
    destruct (proj1 (getProgASP_obsASP S (k a) _ r) (Hk a r HR)) as [s' [HQ Hk']].
    destruct (proj1 (getProgASP_obsASP S m P (a, s')) (Hm (a, s') HQ)) as [s [HP Hm']].
    apply getProgASP_obsASP. exists s. split; [ exact HP |].
    apply (outcomes_bind S). exists a, s'. split; [ exact Hm' | exact Hk' ].
  Qed.

  Theorem tripleDSLP_over_seq {A B} (m : stdivnd S A) (k : A -> stdivnd S B)
    (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
    tripleDSLP m Over P Q ->
    (forall a, tripleDSLP (k a) Over (fun s => Q (a, s)) (R a)) ->
    tripleDSLP (m >>= k) Over P (fun r => forall a, R a r).
  Proof.
    unfold tripleDSLP. intros Hm Hk r Hobs a.
    pose proof (proj1 (getProgDSLP_obsDSLP _ _ _ _) Hobs) as Hobs'. clear Hobs.
    rename Hobs' into Hobs.
    apply (Hk a). apply getProgDSLP_obsDSLP. intros s' Hk'.
    apply Hm. apply getProgDSLP_obsDSLP. intros s Hm'.
    apply Hobs. apply (outcomes_bind S). exists a, s'. split; [ exact Hm' | exact Hk' ].
  Qed.

  Theorem tripleDSLP_under_seq {A B} (m : stdivnd S A) (k : A -> stdivnd S B)
    (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
    tripleDSLP m Under P Q ->
    (forall a, tripleDSLP (k a) Under (fun s => Q (a, s)) (R a)) ->
    tripleDSLP (m >>= k) Under P (fun r => forall a, R a r).
  Proof.
    unfold tripleDSLP. intros Hm Hk r HR.
    apply getProgDSLP_obsDSLP. intros s Hr.
    apply (outcomes_bind S) in Hr. destruct Hr as [a [s' [Hm' Hk']]].
    assert (HQ : Q (a, s')).
    { exact (proj1 (getProgDSLP_obsDSLP S (k a) (fun t => Q (a, t)) r)
               (Hk a r (HR a)) s' Hk'). }
    exact (proj1 (getProgDSLP_obsDSLP S m P (a, s')) (Hm (a, s') HQ) s Hm').
  Qed.

  Theorem tripleDSP_under_seq {A B} (m : stdivnd S A) (k : A -> stdivnd S B)
    (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
    tripleDSP m Under P Q ->
    (forall a, tripleDSP (k a) Under (fun s => Q (a, s)) (R a)) ->
    tripleDSP (m >>= k) Under P (fun r => (exists a, R a r) /\ (forall a, R a r)).
  Proof.
    unfold tripleDSP. intros Hm Hk r [[a0 HR0] HRall].
    apply getProgDSP_obsDSP. split.
    - destruct (proj1 (getProgDSP_obsDSP S (k a0) _ r) (Hk a0 r HR0))
        as [[s' [HQ Hk']] _].
      destruct (proj1 (getProgDSP_obsDSP S m P (a0, s')) (Hm (a0, s') HQ))
        as [[s [HP Hm']] _].
      exists s. split; [ exact HP |].
      apply (outcomes_bind S). exists a0, s'. split; [ exact Hm' | exact Hk' ].
    - intros s Hr. apply (outcomes_bind S) in Hr. destruct Hr as [a [s' [Hm' Hk']]].
      destruct (proj1 (getProgDSP_obsDSP S (k a) _ r) (Hk a r (HRall a))) as [_ Hk_all].
      destruct (proj1 (getProgDSP_obsDSP S m P (a, s')) (Hm (a, s') (Hk_all s' Hk')))
        as [_ Hm_all].
      exact (Hm_all s Hm').
  Qed.

  Theorem tripleASLP_over_seq {A B} (m : stdivnd S A) (k : A -> stdivnd S B)
    (P : S -> Prop) (Q : A * S -> Prop) (R : A -> B * S -> Prop) :
    tripleASLP m Over P Q ->
    (forall a, tripleASLP (k a) Over (fun s => Q (a, s)) (R a)) ->
    tripleASLP (m >>= k) Over P (fun r => (exists a, R a r) \/ (forall a, R a r)).
  Proof.
    unfold tripleASLP. intros Hm Hk r Hobs.
    apply getProgASLP_obsASLP in Hobs. destruct Hobs as [[s [HP Hr]] | Hall].
    - apply (outcomes_bind S) in Hr. destruct Hr as [a [s' [Hm' Hk']]].
      left. exists a. apply (Hk a). apply getProgASLP_obsASLP. left.
      exists s'. split; [| exact Hk' ].
      apply Hm. apply getProgASLP_obsASLP. left. exists s. split; [ exact HP | exact Hm' ].
    - right. intro a. apply (Hk a). apply getProgASLP_obsASLP. right. intros s' Hk'.
      apply Hm. apply getProgASLP_obsASLP. right. intros s Hm'.
      apply Hall. apply (outcomes_bind S). exists a, s'. split; [ exact Hm' | exact Hk' ].
  Qed.

  (* ---- the two closed DSP/ASLP triples are conjunctions ---- *)

  Theorem tripleDSP_under_split {A} (m : stdivnd S A) (P : S -> Prop) (Q : A * S -> Prop) :
    tripleDSP m Under P Q <-> (tripleASP m Under P Q /\ tripleDSLP m Under P Q).
  Proof.
    unfold tripleDSP, tripleASP, tripleDSLP. split.
    - intro H. split; intros r HQ;
        destruct (proj1 (getProgDSP_obsDSP S m P r) (H r HQ)) as [Hasp Hdslp].
      + apply getProgASP_obsASP. exact Hasp.
      + apply getProgDSLP_obsDSLP. exact Hdslp.
    - intros [Ha Hd] r HQ. apply getProgDSP_obsDSP. split.
      + apply getProgASP_obsASP. exact (Ha r HQ).
      + apply getProgDSLP_obsDSLP. exact (Hd r HQ).
  Qed.

  Theorem tripleASLP_over_split {A} (m : stdivnd S A) (P : S -> Prop) (Q : A * S -> Prop) :
    tripleASLP m Over P Q <-> (tripleASP m Over P Q /\ tripleDSLP m Over P Q).
  Proof.
    unfold tripleASLP, tripleASP, tripleDSLP. split.
    - intro H. split; intros r Hobs; apply (H r); apply getProgASLP_obsASLP.
      + left. apply getProgASP_obsASP. exact Hobs.
      + right. apply getProgDSLP_obsDSLP. exact Hobs.
    - intros [Ha Hd] r Hobs.
      destruct (proj1 (getProgASLP_obsASLP S m P r) Hobs) as [Hasp | Hdslp].
      + apply (Ha r). apply getProgASP_obsASP. exact Hasp.
      + apply (Hd r). apply getProgDSLP_obsDSLP. exact Hdslp.
  Qed.

End Sequencing.

(* ---- the two that are not ---- *)

(** DSP / [Over].  [mDO] reaches [(tt,0)] from [0] alone.  [kDO] reaches
    [(tt,9)] from [0] and from [1].  At [pre = {0}] and [Q = {(tt,0)}] the
    first triple holds; the continuation is typed at [{0}], where its DSP
    reading of [(tt,9)] FAILS (state [1] also reaches it), so its triple
    holds vacuously with the empty postcondition.  The composite reaches
    [(tt,9)] from [0] alone, so its DSP reading at [{0}] holds and the
    empty postcondition is refuted. *)
Definition mDO : stdivnd nat unit :=
  progOfSt (fun s r => s = 0 /\ r = (tt, 0)).
Definition kDO : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => (s = 0 \/ s = 1) /\ r = (tt, 9)).

Theorem tripleDSP_over_not_seq :
  tripleDSP mDO Over (fun s => s = 0) (fun r => r = (tt, 0))
  /\ (forall a, tripleDSP (kDO a) Over (fun s => (a, s) = (tt, 0)) (fun _ => False))
  /\ ~ tripleDSP (mDO >>= kDO) Over (fun s => s = 0) (fun _ => False).
Proof.
  unfold tripleDSP. split; [| split ].
  - intros r H. apply getProgDSP_obsDSP in H. destruct H as [[s [_ Hr]] _].
    apply progOfSt_outcomes in Hr. destruct Hr as [_ ->]. reflexivity.
  - intros a r H. apply getProgDSP_obsDSP in H. destruct H as [[s [_ Hr]] Hall].
    apply progOfSt_outcomes in Hr. destruct Hr as [_ ->].
    assert (H1 : (a, 1) = (tt, 0)).
    { apply Hall. apply progOfSt_outcomes. split; [ right; reflexivity | reflexivity ]. }
    injection H1 as _ H1. discriminate H1.
  - intro H. apply (H (tt, 9)). apply getProgDSP_obsDSP. split.
    + exists 0. split; [ reflexivity |].
      apply (outcomes_bind nat). exists tt, 0. split; apply progOfSt_outcomes.
      * split; reflexivity.
      * split; [ left; reflexivity | reflexivity ].
    + intros s Hr. apply (outcomes_bind nat) in Hr. destruct Hr as [a [s' [Hm _]]].
      apply progOfSt_outcomes in Hm. destruct Hm as [-> _]. reflexivity.
Qed.

(** ASLP / [Under], the dual.  [mAU] reaches [(tt,7)] from [5] alone;
    [kAU] reaches [(tt,9)] from [7] and from [1].  At [pre = {0}] the
    postcondition [{(tt,1)}] names an outcome [mAU] never reaches, which
    the ASLP reading accepts for free; the continuation is typed at [{1}],
    from which it does reach [(tt,9)].  But the composite reaches [(tt,9)]
    from [5] alone -- neither from a [pre]-state nor from nowhere. *)
Definition mAU : stdivnd nat unit :=
  progOfSt (fun s r => s = 5 /\ r = (tt, 7)).
Definition kAU : unit -> stdivnd nat unit :=
  fun _ => progOfSt (fun s r => (s = 7 \/ s = 1) /\ r = (tt, 9)).

Theorem tripleASLP_under_not_seq :
  tripleASLP mAU Under (fun s => s = 0) (fun r => r = (tt, 1))
  /\ (forall a, tripleASLP (kAU a) Under (fun s => (a, s) = (tt, 1)) (fun r => r = (tt, 9)))
  /\ ~ tripleASLP (mAU >>= kAU) Under (fun s => s = 0) (fun r => r = (tt, 9)).
Proof.
  unfold tripleASLP. split; [| split ].
  - intros r ->. apply getProgASLP_obsASLP. right. intros s Hr.
    apply progOfSt_outcomes in Hr. destruct Hr as [_ Hr]. discriminate Hr.
  - intros a r ->. apply getProgASLP_obsASLP. left. exists 1.
    split; [ destruct a; reflexivity |].
    apply progOfSt_outcomes. split; [ right; reflexivity | reflexivity ].
  - intro H. specialize (H (tt, 9) eq_refl).
    apply getProgASLP_obsASLP in H. destruct H as [[s [Hs Hr]] | Hall].
    + apply (outcomes_bind nat) in Hr. destruct Hr as [a [s' [Hm _]]].
      apply progOfSt_outcomes in Hm. destruct Hm as [H5 _].
      rewrite Hs in H5. discriminate H5.
    + assert (H5 : 5 = 0).
      { apply Hall. apply (outcomes_bind nat). exists tt, 7. split; apply progOfSt_outcomes.
        - split; reflexivity.
        - split; [ left; reflexivity | reflexivity ]. }
      discriminate H5.
Qed.
