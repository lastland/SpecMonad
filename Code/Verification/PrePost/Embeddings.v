(** * Pre/post pairs as specifications of computations

    Which triples are typings in the pre/post monad [PPM.PrePost]
    ([GaloisConnections/PrePostMonad.v]), at which index, under which order
    and observation; and, for the other triples, why there is no index.

    - The twisted order [PP_le_tw] guards the postcondition clause of
      Hoare's order [PP_le] by the larger precondition.  It is [WP_le]
      pulled back along [pp2wp_under] ([PP_le_tw_pp2wp]), it is [PP_le] once
      the larger postcondition is divided by its precondition
      ([PP_le_tw_divide]), and [bind] is monotone for it
      ([OrderedMonad_PP_tw]).
    - The observations.  [prepost1] records nothing in the precondition,
      [prepost2] termination; both are monad morphisms.  The two other
      candidates, [False] and divergence, fail the [ret] law
      ([prepostFalse_not_morphism], [prepostDiv_not_morphism]).
    - Base setting.  Eight triples are typings, three of them at the bare
      pair [(P tt, Q)] ([dwlp_under_pp] to [dslp_over_pp]).  Lisbon logic
      and angelic partial correctness are not, at any index, under either
      order or observation, in either direction ([awp_under_no_pp_index],
      [awlp_under_no_pp_index]).  No specification order on [PPM.PrePost]
      makes the bare pair exact for incorrectness logic
      ([asp_under_no_bare_pair_order]).
    - With state, [PrePostSt S = stateT S PPM.PrePost], ordered start state
      by start state.  The six correctness typings lift ([dwlpSt_under_pp]
      to [awlpSt_over_pp]).  Incorrectness logic is not a typing for any
      order and any observation taken start state by start state
      ([aspSt_under_no_pp_index]): such typings are closed under gluing by
      start state ([glue_prog_le], [glue_le_prog]), and incorrectness logic
      is not.
    - Witnessed preconditions, as in the earlier [PurePre]: with state the
      state-threaded [bind] can return a precondition with no witness
      ([bind_loses_witness]), and if the postcondition forgets the start
      state no [ret] is a right unit ([no_right_unit_forgetful]). *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad TransformerLaws.
From Incorrectness.WP Require Import WPure.
From Incorrectness.SP Require Import ASPMonad DSLPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import
  Computation Morphisms Triples.
From Incorrectness.Verification.DivNonDetSt Require Import
  Computation Morphisms Triples Typings.
From Incorrectness.GaloisConnections Require Import
  PrePostMonad BaseGaloisConnections.

(* ================================================================= *)
(** * The twisted order                                               *)
(* ================================================================= *)

(** Hoare's order [PP_le], with the postcondition clause needed only
    where the larger precondition holds. *)
Definition PP_le_tw {A} (m1 m2 : PPM.PrePost A) : Prop :=
  (PPM.pre m2 -> PPM.pre m1)
  /\ (forall a, PPM.pre m2 -> PPM.post m1 a -> PPM.post m2 a).

#[global] Instance PP_le_tw_PreOrder {A} : PreOrder (@PP_le_tw A).
Proof.
  constructor; unfold PP_le_tw.
  - intro x. split; intros; assumption.
  - intros x y z [Hp1 Hq1] [Hp2 Hq2]. split.
    + intro Hz. exact (Hp1 (Hp2 Hz)).
    + intros a Hz Hx. exact (Hq2 a Hz (Hq1 a (Hp2 Hz) Hx)).
Qed.

Theorem OrderedMonad_PP_tw : OrderedMonad PPM.PrePost (@PP_le_tw).
Proof.
  constructor.
  - intro A. exact PP_le_tw_PreOrder.
  - intros A x y [Hp Hq].
    split; [ exact (proj2 Hp) | intros a _; exact (proj1 (Hq a)) ].
  - intros A B m1 m2 [Hmp Hmq] k1 k2 Hk.
    unfold PP_le_tw; cbn; unfold PPM.bindPP, PPM.pre, PPM.post; cbn. split.
    + intros [H1 H2]. split; [ exact (Hmp H1) |].
      intros a Ha. exact (proj1 (Hk a) (H2 a (Hmq a H1 Ha))).
    + intros b [H1 H2] [a [Ha Hb]]. exists a.
      split; [ exact (Hmq a H1 Ha) |].
      exact (proj2 (Hk a) b (H2 a (Hmq a H1 Ha)) Hb).
Qed.

(** The order of [WPure] pulled back along the demonic embedding of a pair. *)
Theorem PP_le_tw_pp2wp {A} (x y : PPM.PrePost A) :
  PP_le_tw x y <-> WP_le (pp2wp_under x) (pp2wp_under y).
Proof.
  unfold PP_le_tw, WP_le, pp2wp_under, PPM.pre, PPM.post; cbn. split.
  - intros [Hp Hq] k [Hy Hk]. split; [ exact (Hp Hy) |].
    intros a Ha. exact (Hk a (Hq a Hy Ha)).
  - intro H. split.
    + intro Hy. exact (proj1 (H (snd y) (conj Hy (fun a Ha => Ha)))).
    + intros a Hy Ha. exact (proj2 (H (snd y) (conj Hy (fun a Ha => Ha))) a Ha).
Qed.

(** Hoare's order, after dividing the larger postcondition by its
    precondition. *)
Lemma PP_le_tw_divide {A} (x : PPM.PrePost A) (p : Prop) (q : A -> Prop) :
  PP_le_tw x (p, q) <-> PP_le x (p, fun a => p -> q a).
Proof.
  unfold PP_le_tw, PP_le, PPM.pre, PPM.post; cbn.
  split; intros [H1 H2]; split; try exact H1.
  - intros a Ha Hp. exact (H2 a Hp Ha).
  - intros a Hp Ha. exact (H2 a Ha Hp).
Qed.

(* ================================================================= *)
(** * Observations into [PPM.PrePost]                                 *)
(* ================================================================= *)

(** The postcondition is the set of terminating results.  The precondition
    is the only place left to record divergence. *)
Definition prepost1 {A} (d : divndNE A) : PPM.PrePost A :=
  (True, fun a => unOptionT (getNE d) (Some a)).

Definition prepost2 {A} (d : divndNE A) : PPM.PrePost A :=
  (~ mayDivergeNE d, fun a => unOptionT (getNE d) (Some a)).

Lemma out_ret {A} (a b : A) :
  unOptionT (getNE (ret a : divndNE A)) (Some b) <-> b = a.
Proof.
  cbn. split; [ intro H; injection H as ->; reflexivity | intros ->; reflexivity ].
Qed.

Lemma out_bind_some {A B} (x : divndNE A) (k : A -> divndNE B) (b : B) :
  unOptionT (getNE (bind x k)) (Some b)
  <-> exists a, unOptionT (getNE x) (Some a) /\ unOptionT (getNE (k a)) (Some b).
Proof.
  etransitivity; [ exact (outcomes_bind (getNE x) (fun a => getNE (k a)) (Some b)) |].
  split.
  - intros [[a|] [Ha Hb]]; [ exists a; exact (conj Ha Hb) | discriminate Hb ].
  - intros [a [Ha Hb]]. exists (Some a). exact (conj Ha Hb).
Qed.

Lemma mayDivergeNE_bind {A B} (x : divndNE A) (k : A -> divndNE B) :
  mayDivergeNE (bind x k)
  <-> mayDivergeNE x
      \/ exists a, unOptionT (getNE x) (Some a) /\ mayDivergeNE (k a).
Proof.
  etransitivity; [ exact (outcomes_bind (getNE x) (fun a => getNE (k a)) None) |].
  split.
  - intros [[a|] [Ha Hb]]; [ right; exists a; exact (conj Ha Hb) | left; exact Ha ].
  - intros [H | [a [Ha Hb]]].
    + exists None. split; [ exact H | reflexivity ].
    + exists (Some a). exact (conj Ha Hb).
Qed.

Lemma not_mayDiverge_ret {A} (a : A) : ~ mayDivergeNE (ret a : divndNE A).
Proof. intro H. cbn in H. discriminate H. Qed.

Theorem prepost1_morphism :
  @MonadMorphism divndNE PPM.PrePost Monad__divndNE PPM.Monad_PrePost
    Eq1__divndNE PPM.Eq1_PrePost (@prepost1).
Proof.
  constructor.
  - intros A x y Hxy. split; [ reflexivity |].
    intro a. exact (eq1_outcomes x y Hxy (Some a)).
  - intros A a. split; [ reflexivity |]. intro b. exact (out_ret a b).
  - intros A B x k. split.
    + split; [ intros _; split; [ exact I | intros a _; exact I ] | intros _; exact I ].
    + intro b. exact (out_bind_some x k b).
Qed.

Theorem prepost2_morphism :
  @MonadMorphism divndNE PPM.PrePost Monad__divndNE PPM.Monad_PrePost
    Eq1__divndNE PPM.Eq1_PrePost (@prepost2).
Proof.
  constructor.
  - intros A x y Hxy. split.
    + pose proof (eq1_outcomes x y Hxy None) as Hn.
      split; intros H Hd; apply H; [ exact (proj2 Hn Hd) | exact (proj1 Hn Hd) ].
    + intro a. exact (eq1_outcomes x y Hxy (Some a)).
  - intros A a. split.
    + split; [ intros _; exact I | intros _; exact (not_mayDiverge_ret a) ].
    + intro b. exact (out_ret a b).
  - intros A B x k. split.
    + pose proof (mayDivergeNE_bind x k) as Hd. split.
      * intro H. split.
        -- intro Hx. apply H, Hd. left. exact Hx.
        -- intros a Ha Hka. apply H, Hd. right. exists a. exact (conj Ha Hka).
      * intros [Hx Hk] H. destruct (proj1 Hd H) as [H' | [a [Ha Hka]]].
        -- exact (Hx H').
        -- exact (Hk a Ha Hka).
    + intro b. exact (out_bind_some x k b).
Qed.

(** The other two candidates for the precondition fail the [ret] law:
    [ret] neither has precondition [False] nor diverges. *)
Definition prepostFalse {A} (d : divndNE A) : PPM.PrePost A :=
  (False, fun a => unOptionT (getNE d) (Some a)).

Definition prepostDiv {A} (d : divndNE A) : PPM.PrePost A :=
  (mayDivergeNE d, fun a => unOptionT (getNE d) (Some a)).

Theorem prepostFalse_not_morphism :
  ~ @MonadMorphism divndNE PPM.PrePost Monad__divndNE PPM.Monad_PrePost
      Eq1__divndNE PPM.Eq1_PrePost (@prepostFalse).
Proof. intro H. destruct (mm_ret H tt) as [Hp _]. exact (proj2 Hp I). Qed.

Theorem prepostDiv_not_morphism :
  ~ @MonadMorphism divndNE PPM.PrePost Monad__divndNE PPM.Monad_PrePost
      Eq1__divndNE PPM.Eq1_PrePost (@prepostDiv).
Proof.
  intro H. destruct (mm_ret H tt) as [Hp _].
  exact (not_mayDiverge_ret tt (proj2 Hp I)).
Qed.

(* ================================================================= *)
(** * The base setting: the eight typings                             *)
(* ================================================================= *)

(** The indices of incorrectness logic and of its contrapositive.  The
    precondition [p \/ q = ∅] rejects every computation when [p] fails and
    [q] is inhabited, as the triple does. *)
Definition asp2pp {A} (p : Prop) (q : A -> Prop) : PPM.PrePost A :=
  (p \/ forall a, ~ q a, fun a => p /\ q a).

Definition dslp2pp {A} (p : Prop) (q : A -> Prop) : PPM.PrePost A :=
  (~ p \/ forall a, q a, fun a => ~ p /\ ~ q a).

Section BaseEmbeddings.
  Context {A : Type} (d : divndNE A) (P : unit -> Prop) (Q : A -> Prop).

  (** Partial and total correctness, at the bare pair. *)
  Theorem dwlp_under_pp :
    triple (@dwlpPure) d Under P Q <-> PP_le_tw (prepost1 d) (P tt, Q).
  Proof.
    split.
    - intro H. split; [ intros _; exact I |].
      intros a Hp Ha. exact (proj1 (dwlpPure_read d Q) (H tt Hp) (Some a) Ha).
    - intros [_ H] [] Hp. apply (proj2 (dwlpPure_read d Q)).
      intros [a|] Ho; [ exact (H a Hp Ho) | exact I ].
  Qed.

  Theorem asp_over_pp :
    triple (@aspPure) d Over P Q <-> PP_le_tw (prepost1 d) (P tt, Q).
  Proof.
    split.
    - intro H. split; [ intros _; exact I |].
      intros a Hp Ha. exact (H a (proj2 (aspPure_read d P a) (conj Hp Ha))).
    - intros [_ H] a Ha. destruct (proj1 (aspPure_read d P a) Ha) as [Hp Ho].
      exact (H a Hp Ho).
  Qed.

  Theorem dwp_under_pp :
    triple (@dwpPure) d Under P Q <-> PP_le_tw (prepost2 d) (P tt, Q).
  Proof.
    split.
    - intro H. split.
      + intros Hp Hdiv. exact (proj1 (dwpPure_read d Q) (H tt Hp) None Hdiv).
      + intros a Hp Ha. exact (proj1 (dwpPure_read d Q) (H tt Hp) (Some a) Ha).
    - intros [Hpre H] [] Hp. apply (proj2 (dwpPure_read d Q)).
      intros [a|] Ho; [ exact (H a Hp Ho) | exact (Hpre Hp Ho) ].
  Qed.

  (** Their contrapositives, at the complemented pair. *)
  Theorem awp_over_pp :
    triple (@awpPure) d Over P Q <-> PP_le_tw (prepost1 d) (~ P tt, fun a => ~ Q a).
  Proof.
    split.
    - intro H. split; [ intros _; exact I |].
      intros a Hnp Ha Hq. apply Hnp, (H tt). apply (proj2 (awpPure_read d Q)).
      exists (Some a). exact (conj Ha Hq).
    - intros [_ H] [] Hw. apply NNPP. intro Hnp.
      destruct (proj1 (awpPure_read d Q) Hw) as [[a|] [Ho Hq]];
        [ exact (H a Hnp Ho Hq) | exact Hq ].
  Qed.

  Theorem dslp_under_pp :
    triple (@dslpPure) d Under P Q <-> PP_le_tw (prepost1 d) (~ P tt, fun a => ~ Q a).
  Proof.
    split.
    - intro H. split; [ intros _; exact I |].
      intros a Hnp Ha Hq. exact (Hnp (proj1 (dslpPure_read d P a) (H a Hq) Ha)).
    - intros [_ H] a Hq. apply (proj2 (dslpPure_read d P a)). intro Ha.
      apply NNPP. intro Hnp. exact (H a Hnp Ha Hq).
  Qed.

  Theorem awlp_over_pp :
    triple (@awlpPure) d Over P Q <-> PP_le_tw (prepost2 d) (~ P tt, fun a => ~ Q a).
  Proof.
    split.
    - intro H. split.
      + intros Hnp Hdiv. apply Hnp, (H tt). apply (proj2 (awlpPure_read d Q)).
        exists None. exact (conj Hdiv I).
      + intros a Hnp Ha Hq. apply Hnp, (H tt). apply (proj2 (awlpPure_read d Q)).
        exists (Some a). exact (conj Ha Hq).
    - intros [Hpre H] [] Hw. apply NNPP. intro Hnp.
      destruct (proj1 (awlpPure_read d Q) Hw) as [[a|] [Ho Hq]].
      + exact (H a Hnp Ho Hq).
      + exact (Hpre Hnp Ho).
  Qed.

  (** Incorrectness logic and its contrapositive, with the index below the
      computation. *)
  Theorem asp_under_pp :
    triple (@aspPure) d Under P Q <-> PP_le_tw (asp2pp (P tt) Q) (prepost1 d).
  Proof.
    split.
    - intro H. split.
      + intros _. destruct (classic (exists a, Q a)) as [[a Hq] | Hnone].
        * left. exact (proj1 (proj1 (aspPure_read d P a) (H a Hq))).
        * right. intros a Hq. exact (Hnone (ex_intro _ a Hq)).
      + intros a _ [Hp Hq]. exact (proj2 (proj1 (aspPure_read d P a) (H a Hq))).
    - intros [Hpre H] a Hq. apply (proj2 (aspPure_read d P a)).
      destruct (Hpre I) as [Hp | Hnone]; [| destruct (Hnone a Hq) ].
      exact (conj Hp (H a I (conj Hp Hq))).
  Qed.

  Theorem dslp_over_pp :
    triple (@dslpPure) d Over P Q <-> PP_le_tw (dslp2pp (P tt) Q) (prepost1 d).
  Proof.
    split.
    - intro H. split.
      + intros _. destruct (classic (P tt)) as [Hp | Hnp]; [ right | left; exact Hnp ].
        intro a. apply H. apply (proj2 (dslpPure_read d P a)). intros _. exact Hp.
      + intros a _ [Hnp Hnq]. apply NNPP. intro Hno. apply Hnq, H.
        apply (proj2 (dslpPure_read d P a)). intro Ho. destruct (Hno Ho).
    - intros [Hpre H] a Hd. pose proof (proj1 (dslpPure_read d P a) Hd) as Hd'.
      destruct (Hpre I) as [Hnp | Hall]; [| exact (Hall a) ].
      apply NNPP. intro Hnq. exact (Hnp (Hd' (H a I (conj Hnp Hnq)))).
  Qed.
End BaseEmbeddings.

(* ================================================================= *)
(** * The base setting: Lisbon logic has no index                     *)
(* ================================================================= *)

(** Four computations: [1], [2], [3], and a choice of [1] or [3].  None
    diverges, so [prepost1] and [prepost2] agree on them. *)
Definition retOne : divndNE nat := ret 1.
Definition retTwo : divndNE nat := ret 2.
Definition retThree : divndNE nat := ret 3.
Definition oneOrThree : divndNE nat := orNE (ret 1) (ret 3).

Definition target12 (a : nat) : Prop := a = 1 \/ a = 2.

(** With the computation below the index, the typed computations are
    closed downwards; with the index below, it is below the meet of what it
    types. *)
Lemma no_index_prog_le (le : relation (PPM.PrePost nat))
  (θ : divndNE nat -> PPM.PrePost nat) (T : divndNE nat -> Prop) :
  T oneOrThree -> ~ T retThree ->
  Transitive le -> le (θ retThree) (θ oneOrThree) ->
  ~ exists w, forall m, T m <-> le (θ m) w.
Proof.
  intros HT13 HT3 Htr Hle [w Hw]. apply HT3, Hw.
  exact (Htr _ _ _ Hle (proj1 (Hw oneOrThree) HT13)).
Qed.

Lemma no_index_le_prog (le : relation (PPM.PrePost nat))
  (θ : divndNE nat -> PPM.PrePost nat) (T : divndNE nat -> Prop) :
  T retOne -> T retTwo -> ~ T retThree ->
  (forall w, le w (θ retOne) -> le w (θ retTwo) -> le w (θ retThree)) ->
  ~ exists w, forall m, T m <-> le w (θ m).
Proof.
  intros HT1 HT2 HT3 Hmeet [w Hw]. apply HT3, Hw.
  exact (Hmeet w (proj1 (Hw retOne) HT1) (proj1 (Hw retTwo) HT2)).
Qed.

Lemma out_one_two (a : nat) :
  unOptionT (getNE retOne) (Some a) -> unOptionT (getNE retTwo) (Some a) -> False.
Proof. cbn. intros H1 H2. rewrite H1 in H2. discriminate H2. Qed.

Lemma pp_orders_trans (le : relation (PPM.PrePost nat)) :
  (le = PP_le \/ le = PP_le_tw) -> Transitive le.
Proof. intros [-> | ->]; typeclasses eauto. Qed.

Lemma pp_three_le_oneOrThree (le : relation (PPM.PrePost nat))
  (θ : divndNE nat -> PPM.PrePost nat) :
  (le = PP_le \/ le = PP_le_tw) -> (θ = prepost1 \/ θ = prepost2) ->
  le (θ retThree) (θ oneOrThree).
Proof.
  intros [-> | ->] [-> | ->]; split.
  - intros _. exact I.
  - intros a Ha. right. exact Ha.
  - intros _. exact (not_mayDiverge_ret 3).
  - intros a Ha. right. exact Ha.
  - intros _. exact I.
  - intros a _ Ha. right. exact Ha.
  - intros _. exact (not_mayDiverge_ret 3).
  - intros a _ Ha. right. exact Ha.
Qed.

Lemma pp_meet (le : relation (PPM.PrePost nat))
  (θ : divndNE nat -> PPM.PrePost nat) :
  (le = PP_le \/ le = PP_le_tw) -> (θ = prepost1 \/ θ = prepost2) ->
  forall w, le w (θ retOne) -> le w (θ retTwo) -> le w (θ retThree).
Proof.
  intros [-> | ->] [-> | ->] w [H1p H1q] [_ H2q]; split.
  - exact H1p.
  - intros a Ha. destruct (out_one_two a (H1q a Ha) (H2q a Ha)).
  - intros _. exact (H1p (not_mayDiverge_ret 1)).
  - intros a Ha. destruct (out_one_two a (H1q a Ha) (H2q a Ha)).
  - exact H1p.
  - intros a _ Ha. destruct (out_one_two a (H1q a I Ha) (H2q a I Ha)).
  - intros _. exact (H1p (not_mayDiverge_ret 1)).
  - intros a _ Ha.
    destruct (out_one_two a (H1q a (not_mayDiverge_ret 1) Ha)
                (H2q a (not_mayDiverge_ret 2) Ha)).
Qed.

Theorem awp_under_no_pp_index (le : relation (PPM.PrePost nat))
  (θ : divndNE nat -> PPM.PrePost nat) :
  (le = PP_le \/ le = PP_le_tw) -> (θ = prepost1 \/ θ = prepost2) ->
  ~ (exists w, forall m,
       triple (@awpPure) m Under (fun _ => True) target12 <-> le (θ m) w)
  /\ ~ (exists w, forall m,
       triple (@awpPure) m Under (fun _ => True) target12 <-> le w (θ m)).
Proof.
  intros Hle Hθ.
  assert (Hyes : forall m a, unOptionT (getNE m) (Some a) -> target12 a ->
            triple (@awpPure) m Under (fun _ => True) target12).
  { intros m a Ha Hq [] _. apply (proj2 (awpPure_read m target12)).
    exists (Some a). exact (conj Ha Hq). }
  assert (Hno : ~ triple (@awpPure) retThree Under (fun _ => True) target12).
  { intro H. destruct (proj1 (awpPure_read retThree target12) (H tt I))
      as [[a|] [Ho Hq]].
    - cbn in Ho. injection Ho as ->. destruct Hq as [E | E]; discriminate E.
    - exact Hq. }
  split.
  - apply (no_index_prog_le le θ
             (fun m => triple (@awpPure) m Under (fun _ => True) target12)).
    + exact (Hyes oneOrThree 1 (or_introl eq_refl) (or_introl eq_refl)).
    + exact Hno.
    + exact (pp_orders_trans le Hle).
    + exact (pp_three_le_oneOrThree le θ Hle Hθ).
  - apply (no_index_le_prog le θ
             (fun m => triple (@awpPure) m Under (fun _ => True) target12)).
    + exact (Hyes retOne 1 eq_refl (or_introl eq_refl)).
    + exact (Hyes retTwo 2 eq_refl (or_intror eq_refl)).
    + exact Hno.
    + exact (pp_meet le θ Hle Hθ).
Qed.

Theorem awlp_under_no_pp_index (le : relation (PPM.PrePost nat))
  (θ : divndNE nat -> PPM.PrePost nat) :
  (le = PP_le \/ le = PP_le_tw) -> (θ = prepost1 \/ θ = prepost2) ->
  ~ (exists w, forall m,
       triple (@awlpPure) m Under (fun _ => True) target12 <-> le (θ m) w)
  /\ ~ (exists w, forall m,
       triple (@awlpPure) m Under (fun _ => True) target12 <-> le w (θ m)).
Proof.
  intros Hle Hθ.
  assert (Hyes : forall m a, unOptionT (getNE m) (Some a) -> target12 a ->
            triple (@awlpPure) m Under (fun _ => True) target12).
  { intros m a Ha Hq [] _. apply (proj2 (awlpPure_read m target12)).
    exists (Some a). exact (conj Ha Hq). }
  assert (Hno : ~ triple (@awlpPure) retThree Under (fun _ => True) target12).
  { intro H. destruct (proj1 (awlpPure_read retThree target12) (H tt I))
      as [[a|] [Ho Hq]].
    - cbn in Ho. injection Ho as ->. destruct Hq as [E | E]; discriminate E.
    - cbn in Ho. discriminate Ho. }
  split.
  - apply (no_index_prog_le le θ
             (fun m => triple (@awlpPure) m Under (fun _ => True) target12)).
    + exact (Hyes oneOrThree 1 (or_introl eq_refl) (or_introl eq_refl)).
    + exact Hno.
    + exact (pp_orders_trans le Hle).
    + exact (pp_three_le_oneOrThree le θ Hle Hθ).
  - apply (no_index_le_prog le θ
             (fun m => triple (@awlpPure) m Under (fun _ => True) target12)).
    + exact (Hyes retOne 1 eq_refl (or_introl eq_refl)).
    + exact (Hyes retTwo 2 eq_refl (or_intror eq_refl)).
    + exact Hno.
    + exact (pp_meet le θ Hle Hθ).
Qed.

(* ================================================================= *)
(** * The base setting: no order fits incorrectness logic             *)
(* ================================================================= *)

(** A choice of [0] or [1], continued by a branch that needs [False] and
    returns nothing, or by one that returns [0].  Incorrectness logic sees
    no difference between [(False, ∅)] and [(True, ∅)] — neither returns
    anything — but the demonic [bind] does. *)
Definition il_m : divndNE nat := orNE (ret 0) (ret 1).

Definition il_k (a : nat) : PPM.PrePost nat :=
  match a with
  | O => (False, fun _ => False)
  | S _ => (True, fun b => b = 0)
  end.

Definition il_k' (a : nat) : PPM.PrePost nat :=
  match a with
  | O => prepost1 (divergeNE : divndNE nat)
  | S _ => prepost1 (ret 0 : divndNE nat)
  end.

Theorem asp_under_no_bare_pair_order (le : forall A, relation (PPM.PrePost A)) :
  OrderedMonad PPM.PrePost le ->
  ~ (forall A (d : divndNE A) (P : unit -> Prop) (Q : A -> Prop),
       triple (@aspPure) d Under P Q <-> le A (P tt, Q) (prepost1 d)).
Proof.
  intros [Hpre Heq Hbind] Hex.
  destruct (Hpre nat) as [Hrefl Htrans].
  assert (Hk : forall a, le nat (il_k a) (il_k' a)).
  { intros [|n].
    - apply (proj1 (Hex nat divergeNE (fun _ => False) (fun _ => False))).
      intros a [].
    - apply (proj1 (Hex nat (ret 0) (fun _ => True) (fun b => b = 0))).
      intros a ->. apply (proj2 (aspPure_read _ _ _)). split; [ exact I | reflexivity ]. }
  pose proof (Hbind nat nat (prepost1 il_m) (prepost1 il_m) (Hrefl _) il_k il_k' Hk)
    as Hb.
  assert (H1 : le nat (False, fun c : nat => c = 0) (bind (prepost1 il_m) il_k)).
  { apply Heq. split.
    - split; [ intros [] | intros [_ H]; exact (H 0 (or_introl eq_refl)) ].
    - intro c. split.
      + intros ->. exists 1. split; [ right; reflexivity | reflexivity ].
      + intros [[|n] [_ Hc]]; [ destruct Hc | exact Hc ]. }
  assert (H2 : le nat (bind (prepost1 il_m) il_k') (prepost1 (ret 0 : divndNE nat))).
  { apply Heq. split.
    - split; [ intros _; exact I | intros _; split; [ exact I | intros [|n] _; exact I ] ].
    - intro c. split.
      + intros [[|n] [_ Hc]]; [ cbn in Hc; discriminate Hc | exact Hc ].
      + intro Hc. exists 1. split; [ right; reflexivity | exact Hc ]. }
  pose proof (Htrans _ _ _ H1 (Htrans _ _ _ Hb H2)) as H.
  pose proof (proj2 (Hex nat (ret 0) (fun _ => False) (fun c => c = 0)) H) as Hil.
  destruct (proj1 (aspPure_read _ _ _) (Hil 0 eq_refl)) as [[] _].
Qed.

(* ================================================================= *)
(** * With state                                                      *)
(* ================================================================= *)

Section Stateful.
  Variable S : Type.

  (** [(S -> Prop) * (S -> A * S -> Prop)], up to currying: a precondition
      on the start state and a relation from it to the outcomes. *)
  Definition PrePostSt : Type -> Type := stateT S PPM.PrePost.

  #[global] Instance Monad__PrePostSt : Monad PrePostSt :=
    @Monad_stateT S PPM.PrePost PPM.Monad_PrePost.

  Definition Eq1__PrePostSt : Eq1 PrePostSt :=
    @Eq1_stateT S PPM.PrePost PPM.Eq1_PrePost.

  Definition MonadLawsE__PrePostSt
    : @MonadLawsE PrePostSt Eq1__PrePostSt Monad__PrePostSt :=
    MonadLawsE_stateT S PPM.PrePost.

  (** The twisted order, start state by start state. *)
  Definition PPSt_le_tw : forall A, relation (PrePostSt A) :=
    le_stateT (@PP_le_tw).

  Theorem OrderedMonad_PPSt_tw :
    @OrderedMonad PrePostSt Monad__PrePostSt Eq1__PrePostSt PPSt_le_tw.
  Proof. exact (OrderedMonad_stateT (@PP_le_tw) OrderedMonad_PP_tw). Qed.

  Definition prepost1St : forall A, stdivndNE S A -> PrePostSt A :=
    stateT_map S (@prepost1).

  Definition prepost2St : forall A, stdivndNE S A -> PrePostSt A :=
    stateT_map S (@prepost2).

  Theorem prepost1St_morphism :
    @MonadMorphism (stdivndNE S) PrePostSt (Monad__stdivndNE S) Monad__PrePostSt
      (Eq1__stdivndNE S) Eq1__PrePostSt prepost1St.
  Proof. exact (MonadMorphism_stateT S (@prepost1) prepost1_morphism). Qed.

  Theorem prepost2St_morphism :
    @MonadMorphism (stdivndNE S) PrePostSt (Monad__stdivndNE S) Monad__PrePostSt
      (Eq1__stdivndNE S) Eq1__PrePostSt prepost2St.
  Proof. exact (MonadMorphism_stateT S (@prepost2) prepost2_morphism). Qed.

  (** The bare pair, at every start state. *)
  Definition ppSt {A} (P : S -> Prop) (Q : A * S -> Prop) : PrePostSt A :=
    mkStateT (fun s => (P s, Q)).

  (** ** The six correctness typings *)

  Section Embeddings.
    Context {A : Type} (m : stdivndNE S A) (P : S -> Prop) (Q : A * S -> Prop).

    Theorem dwlpSt_under_pp :
      triple (@dwlpSt S) m Under P Q <-> PPSt_le_tw A (prepost1St A m) (ppSt P Q).
    Proof.
      split.
      - intros H s. apply (proj1 (dwlp_under_pp (runStateT m s) (fun _ => P s) Q)).
        exact (proj1 (triple_dwlpSt m Under P Q) H s).
      - intro H. apply (proj2 (triple_dwlpSt m Under P Q)). intro s.
        exact (proj2 (dwlp_under_pp (runStateT m s) (fun _ => P s) Q) (H s)).
    Qed.

    Theorem aspSt_over_pp :
      triple (@aspSt S) m Over P Q <-> PPSt_le_tw A (prepost1St A m) (ppSt P Q).
    Proof.
      split.
      - intros H s. split; [ intros _; exact I |].
        intros r Hp Hr. apply H. apply (proj2 (aspSt_read m P r)).
        exists s. exact (conj Hp Hr).
      - intros H r Hr. destruct (proj1 (aspSt_read m P r) Hr) as [s [Hp Ho]].
        exact (proj2 (H s) r Hp Ho).
    Qed.

    Theorem dwpSt_under_pp :
      triple (@dwpSt S) m Under P Q <-> PPSt_le_tw A (prepost2St A m) (ppSt P Q).
    Proof.
      split.
      - intros H s. apply (proj1 (dwp_under_pp (runStateT m s) (fun _ => P s) Q)).
        exact (proj1 (triple_dwpSt m Under P Q) H s).
      - intro H. apply (proj2 (triple_dwpSt m Under P Q)). intro s.
        exact (proj2 (dwp_under_pp (runStateT m s) (fun _ => P s) Q) (H s)).
    Qed.

    Theorem awpSt_over_pp :
      triple (@awpSt S) m Over P Q
      <-> PPSt_le_tw A (prepost1St A m) (ppSt (fun s => ~ P s) (fun r => ~ Q r)).
    Proof.
      split.
      - intros H s. apply (proj1 (awp_over_pp (runStateT m s) (fun _ => P s) Q)).
        exact (proj1 (triple_awpSt m Over P Q) H s).
      - intro H. apply (proj2 (triple_awpSt m Over P Q)). intro s.
        exact (proj2 (awp_over_pp (runStateT m s) (fun _ => P s) Q) (H s)).
    Qed.

    Theorem dslpSt_under_pp :
      triple (@dslpSt S) m Under P Q
      <-> PPSt_le_tw A (prepost1St A m) (ppSt (fun s => ~ P s) (fun r => ~ Q r)).
    Proof.
      split.
      - intros H s. split; [ intros _; exact I |].
        intros r Hnp Hr Hq. exact (Hnp (proj1 (dslpSt_read m P r) (H r Hq) s Hr)).
      - intros H r Hq. apply (proj2 (dslpSt_read m P r)). intros s Hr.
        apply NNPP. intro Hnp. exact (proj2 (H s) r Hnp Hr Hq).
    Qed.

    Theorem awlpSt_over_pp :
      triple (@awlpSt S) m Over P Q
      <-> PPSt_le_tw A (prepost2St A m) (ppSt (fun s => ~ P s) (fun r => ~ Q r)).
    Proof.
      split.
      - intros H s. apply (proj1 (awlp_over_pp (runStateT m s) (fun _ => P s) Q)).
        exact (proj1 (triple_awlpSt m Over P Q) H s).
      - intro H. apply (proj2 (triple_awlpSt m Over P Q)). intro s.
        exact (proj2 (awlp_over_pp (runStateT m s) (fun _ => P s) Q) (H s)).
    Qed.
  End Embeddings.

  (** ** Incorrectness logic has no index *)

  (** From start state [s], behave like [Y s]. *)
  Definition glue {A} (Y : S -> stdivndNE S A) : stdivndNE S A :=
    mkStateT (fun s => runStateT (Y s) s).

  (** An order taken start state by start state, against an observation
      taken start state by start state, sees each start state separately;
      so every class it types is closed under gluing.  Neither needs to be
      an order, nor a monad morphism. *)
  Section Gluing.
    Variable le0 : forall A, relation (PPM.PrePost A).
    Variable θ0 : forall A, divndNE A -> PPM.PrePost A.

    Lemma glue_prog_le {A} (w : PrePostSt A) (Y : S -> stdivndNE S A) :
      (forall t, le_stateT le0 A (stateT_map S θ0 A (Y t)) w) ->
      le_stateT le0 A (stateT_map S θ0 A (glue Y)) w.
    Proof. intros H s. exact (H s s). Qed.

    Lemma glue_le_prog {A} (w : PrePostSt A) (Y : S -> stdivndNE S A) :
      (forall t, le_stateT le0 A w (stateT_map S θ0 A (Y t))) ->
      le_stateT le0 A w (stateT_map S θ0 A (glue Y)).
    Proof. intros H s. exact (H s s). Qed.
  End Gluing.

  Section IncorrectnessLogic.
    Context {A : Type} (s1 s2 : S) (Hne : s1 <> s2) (r0 : A * S).

    (** Reach [r0] from the precondition state that is not [s]. *)
    Definition avoiding (s : S) : stdivndNE S A :=
      progOf (fun t r => r = r0 /\ (t = s1 \/ t = s2) /\ t <> s).

    Lemma avoiding_IL (s : S) :
      triple (@aspSt S) (avoiding s) Under (fun t => t = s1 \/ t = s2) (fun r => r = r0).
    Proof.
      intros r ->. apply (proj2 (aspSt_read (avoiding s) (fun t => t = s1 \/ t = s2) r0)).
      destruct (classic (s = s1)) as [-> | Hs].
      - exists s2. split; [ right; reflexivity |].
        split; [ reflexivity | split; [ right; reflexivity | intro E; exact (Hne (eq_sym E)) ] ].
      - exists s1. split; [ left; reflexivity |].
        split; [ reflexivity | split; [ left; reflexivity | intro E; exact (Hs (eq_sym E)) ] ].
    Qed.

    Lemma glue_avoiding_not_IL :
      ~ triple (@aspSt S) (glue avoiding) Under (fun t => t = s1 \/ t = s2) (fun r => r = r0).
    Proof.
      intro H.
      destruct (proj1 (aspSt_read (glue avoiding) (fun t => t = s1 \/ t = s2) r0)
                  (H r0 eq_refl)) as [t [_ Ht]].
      destruct Ht as [_ [_ Hneq]]. exact (Hneq eq_refl).
    Qed.

    Theorem aspSt_under_no_pp_index
      (le0 : forall A, relation (PPM.PrePost A))
      (θ0 : forall A, divndNE A -> PPM.PrePost A) :
      ~ (exists w : PrePostSt A, forall m,
            triple (@aspSt S) m Under (fun t => t = s1 \/ t = s2) (fun r => r = r0)
            <-> le_stateT le0 A (stateT_map S θ0 A m) w)
      /\ ~ (exists w : PrePostSt A, forall m,
            triple (@aspSt S) m Under (fun t => t = s1 \/ t = s2) (fun r => r = r0)
            <-> le_stateT le0 A w (stateT_map S θ0 A m)).
    Proof.
      split; intros [w Hw]; apply glue_avoiding_not_IL, Hw.
      - apply glue_prog_le. intro t. apply Hw, avoiding_IL.
      - apply glue_le_prog. intro t. apply Hw, avoiding_IL.
    Qed.
  End IncorrectnessLogic.
End Stateful.

(* ================================================================= *)
(** * Witnessed preconditions with state                              *)
(* ================================================================= *)

(** The earlier development restricted preconditions to inhabited ones,
    with a witness, so that [(False, ∅)] is not a specification. *)
Section WitnessedPreconditions.
  Variable S : Type.

  Definition PurePre : Type := { sp : S * (S -> Prop) | snd sp (fst sp) }.

  (** A witness is a start state: without one, there is no precondition,
      so no [ret]. *)
  Lemma PurePre_needs_a_state : PurePre -> S.
  Proof. intros [[s _] _]. exact s. Qed.

  Context {X : Type} (s1 s2 : S) (Hne : s1 <> s2) (x0 : X).

  (** With the start state kept in the postcondition, the state-threaded
      [bind] of two specifications whose preconditions hold at [s1] can
      have a precondition that holds nowhere. *)
  Theorem bind_loses_witness :
    exists (m : PrePostSt S X) (k : X -> PrePostSt S X),
      PPM.pre (runStateT m s1)
      /\ (forall x, PPM.pre (runStateT (k x) s1))
      /\ forall s, ~ PPM.pre (runStateT (bind m k) s).
  Proof.
    exists (mkStateT (fun s => (s = s1, fun r => r = (x0, s2)))).
    exists (fun x => mkStateT (fun s => (s = s1, fun r => r = (x, s)))).
    split; [ reflexivity | split; [ intros x; reflexivity |] ].
    intros s [_ H]. exact (Hne (eq_sym (H (x0, s2) eq_refl))).
  Qed.

  (** With the start state dropped from the postcondition, as in the
      earlier [PurePost], the state-threaded [bind] has no right unit. *)
  Definition PPForget (Y : Type) : Type := ((S -> Prop) * (Y * S -> Prop))%type.

  Definition bindForget {Y Z} (m : PPForget Y) (k : Y -> PPForget Z) : PPForget Z :=
    ( fun s => fst m s /\ (forall y s', snd m (y, s') -> fst (k y) s'),
      fun r => exists y s', snd m (y, s') /\ snd (k y) r ).

  Theorem no_right_unit_forgetful :
    ~ exists ret : X -> PPForget X,
        forall (m : PPForget X) (r : X * S), snd (bindForget m ret) r <-> snd m r.
  Proof.
    intros [ret Hret].
    assert (H2 : snd (ret x0) (x0, s2)).
    { destruct (proj2 (Hret (fun _ => True, fun r => r = (x0, s2)) (x0, s2)) eq_refl)
        as [y [s' [E Hy]]].
      cbn in E. injection E as -> ->. exact Hy. }
    assert (E : (x0, s2) = (x0, s1)).
    { apply (proj1 (Hret (fun _ => True, fun r => r = (x0, s1)) (x0, s2))).
      exists x0, s1. split; [ reflexivity | exact H2 ]. }
    injection E as E. exact (Hne (eq_sym E)).
  Qed.
End WitnessedPreconditions.
