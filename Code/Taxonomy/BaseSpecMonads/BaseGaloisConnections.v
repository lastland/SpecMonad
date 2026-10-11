(** * The DM4all adjunctions, between the five specification monads

    The orders are DM4all's, each defined in its monad's file with the proof
    that it makes the monad a specification monad:

      [Pred_le]  pointwise implication
      [PP_le]    strengthen the precondition, weaken the postcondition
      [SP_le]    pointwise implication in [(pre, result)]
      [WP_le]    reverse implication: a weaker precondition demand is lower
      [MR_le]    reverse implication on validator verdicts

    The six adjunctions below use those orders (schematically):

      [pred_pp_adjunction]      [pred2pp post <= pp     <->  post <= pp2pred pp]
      [wp_pp_under_adjunction]  [pp <= wp2pp_under w    <->  pp2wp_under pp <= w]
      [wp_pp_over_adjunction]   [wp2pp_over w <= pp     <->  w <= pp2wp_over pp]
      [wp_mr_adjunction]        [w <= mr2wp r           <->  wp2mr w <= r]
      [sp_pp_adjunction]        [sp2pp sp <= pp         <->  sp <= pp2sp pp]
      [sp_mr_adjunction]        [sp2mr sp <= mr         <->  sp <= mr2sp mr]

    [wp_pp_over_adjunction] is the only classical one. *)

From Coq Require Import RelationClasses Classical_Prop.
From Incorrectness.Relational Require Import
  PredMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  PrePostMonad.
From Incorrectness.SP Require Import
  SPostMonad.
From Incorrectness.WP Require Import
  WPureMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  RelPrePostMonad.

Import PredM SPM RPPM.
(* [PPM] is deliberately NOT imported: it binds [pre] and [post], which
   would capture the binders of the SP embeddings below. Use [PPM.pre] etc. *)

(* ================================================================= *)
(** ** 1.  [Pred] -| [PrePost]                                       *)
(* ================================================================= *)

(** [α] equips a predicate with the trivial precondition; [γ] forgets the
    precondition.  Under the Hoare order [True] is the top of the pre
    component, so the pre check dissolves. *)

Definition pred2pp {A} (post : PredM.Pred A) : PPM.PrePost A := (True, post).
Definition pp2pred {A} (pp : PPM.PrePost A) : PredM.Pred A := PPM.post pp.

Theorem pred_pp_adjunction {A} (post : PredM.Pred A) (pp : PPM.PrePost A) :
  PP_le (pred2pp post) pp <-> Pred_le post (pp2pred pp).
Proof.
  unfold PP_le, Pred_le, pred2pp, pp2pred, PPM.pre, PPM.post; cbn. split.
  - intros [_ H]. exact H.
  - intro H. split; [ intros _; exact I | exact H ].
Qed.

(* ================================================================= *)
(** ** 2.  [PrePost] -| [MonoWP]                                     *)
(* ================================================================= *)

(** [wp2pp_under w] reads off [w] at [True] and the intersection of every
    postcondition [w] accepts; [pp2wp_under pp] is the demonic
    transformer of a Hoare pair. *)

Definition wp2pp_under {A} (w : WPure A) : PPM.PrePost A :=
  ( getWPure w (fun _ => True)
    , fun x => forall p, getWPure w p -> p x ).

#[program] Definition pp2wp_under {A} (pp : PPM.PrePost A) : WPure A :=
  fun post => PPM.pre pp /\ (forall x, PPM.post pp x -> post x).
Next Obligation.
  intros k1 k2 Hk [Hpre Hpost]. split; [ exact Hpre |].
  intros x Hx. exact (Hk x (Hpost x Hx)).
Qed.

Theorem wp_pp_under_adjunction {A} (pp : PPM.PrePost A) (w : WPure A) :
  PP_le pp (wp2pp_under w) <-> WP_le (pp2wp_under pp) w.
Proof.
  unfold PP_le, WP_le, wp2pp_under, pp2wp_under, PPM.pre, PPM.post,
         getWPure, getWPure; cbn.
  split.
  - intros [Hpre Hpost] k Hw. split.
    + apply Hpre. exact (getWPure_mono w k (fun _ => True) (fun _ _ => I) Hw).
    + intros x Hx. exact (Hpost x Hx k Hw).
  - intro H. split.
    + intro Hw. exact (proj1 (H (fun _ => True) Hw)).
    + intros x Hx p Hw. exact (proj2 (H p Hw) x Hx).
Qed.

(** The second adjunction between the same two monads, with [MonoWP] on the
    left.  [wp2pp_over w] demands that [w] accept every postcondition, and
    collects the results of the postconditions [w] rejects;
    [pp2wp_over pp] holds of a postcondition when covering [pp]'s
    postcondition entails [pp]'s precondition. *)

Definition wp2pp_over {A} (w : WPure A) : PPM.PrePost A :=
  ( forall p, getWPure w p
    , fun x => exists p, ~ (getWPure w p) /\ p x ).

#[program] Definition pp2wp_over {A} (pp : PPM.PrePost A) : WPure A :=
  fun post => (forall x, post x -> PPM.post pp x) -> PPM.pre pp.
Next Obligation.
  intros k1 k2 Hk H Hsub. apply H. intros x Hx. exact (Hsub x (Hk x Hx)).
Qed.

Theorem wp_pp_over_adjunction {A} (pp : PPM.PrePost A) (w : WPure A) :
  PP_le (wp2pp_over w) pp <-> WP_le w (pp2wp_over pp).
Proof.
  unfold PP_le, WP_le, wp2pp_over, pp2wp_over, PPM.pre, PPM.post,
    getWPure, getWPure; cbn.
  split.
  - intros [H1 H2] q Hq.
    destruct (classic (proj1_sig w q)) as [Hy | Hn]; [ exact Hy |].
    exact (H1 (Hq (fun a Ha => H2 a (ex_intro _ q (conj Hn Ha)))) q).
  - intro H. split.
    + intros Hpre q. exact (H q (fun _ => Hpre)).
    + intros a [q [Hnq Hqa]].
      assert (Hn : ~ ((forall x, q x -> PPM.post pp x) -> PPM.pre pp))
        by (intro Hc; exact (Hnq (H q Hc))).
      exact (proj1 (imply_to_and _ _ Hn) a Hqa).
Qed.

(* ================================================================= *)
(** ** 3.  [MonoWP] -| [RelPrePost]                                  *)
(* ================================================================= *)

(** [wp2mr w] validates [(pre, post)] when [pre] entails [w]'s demand for
    [post]; [mr2wp r] asks for SOME precondition that [r] validates against
    the postcondition, and that holds. *)

Definition assumingP (p : Prop) {A} (k : A -> Prop) (a : A) : RPPM.Assuming p :=
  exist _ (p -> k a) (conj (fun H _ => H) (fun H hp => H hp hp)).

Definition wp2mrT {A} (w : WPure A) : RPPM.RPPT A :=
  fun p post =>
    exist _ (p -> getWPure w (fun a => RPPM.ab (post a)))
            (conj (fun H _ => H) (fun H hp => H hp hp)).

Lemma wp2mr_mono {A} (w : WPure A) : RPPM.rpp_mono (wp2mrT w).
Proof.
  intros p1 p2 post1 post2 Hpre Hpost H hp1. cbn in *.
  apply (getWPure_mono w (fun a => RPPM.ab (post2 a))
                          (fun a => RPPM.ab (post1 a)) Hpost).
  exact (H (Hpre hp1)).
Qed.

Definition wp2mr {A} (w : WPure A) : RPPM.RelPrePost A :=
  exist _ (wp2mrT w) (wp2mr_mono w).

Definition mr2wpT {A} (r : RPPM.RelPrePost A) : (A -> Prop) -> Prop :=
  fun k => exists p, RPPM.ab (RPPM.runRPP r p (assumingP p k)) /\ p.

Lemma mr2wp_mono {A} (r : RPPM.RelPrePost A) :
  wpure_mono (mr2wpT r).
Proof.
  intros k1 k2 Hk [p [Hr Hp]]. exists p. split; [| exact Hp ].
  apply (RPPM.runRPP_mono r p p (assumingP p k2) (assumingP p k1)
           (fun h => h)); [| exact Hr ].
  intros x Hx hp. exact (Hk x (Hx hp)).
Qed.

Definition mr2wp {A} (r : RPPM.RelPrePost A) : WPure A :=
  exist _ (mr2wpT r) (mr2wp_mono r).

Theorem wp_mr_adjunction {A} (w : WPure A) (r : RPPM.RelPrePost A) :
  WP_le w (mr2wp r) <-> MR_le (wp2mr w) r.
Proof.
  unfold WP_le, MR_le, mr2wp, mr2wpT, wp2mr, wp2mrT,
         getWPure, getWPure, RPPM.ab, RPPM.runRPP; cbn.
  split.
  - intros H p post Hr hp.
    apply (H (fun a => proj1_sig (post a))).
    exists p. split; [| exact hp ].
    apply (RPPM.runRPP_mono r p p
             (assumingP p (fun a => proj1_sig (post a))) post (fun h => h));
      [| exact Hr ].
    intros x Hx _. exact Hx.
  - intros H k [p [Hr Hp]].
    apply (getWPure_mono w (fun a => p -> k a) k (fun x hx => hx Hp)).
    exact (H p (assumingP p k) Hr Hp).

Qed.

(* ================================================================= *)
(** ** 4.  [SPost] -| [PrePost]                                      *)
(* ================================================================= *)

(** The SP/PrePost adjunction uses an impredicative intersection.

    [sp2pp sp] reads off the postcondition [sp] establishes from EVERY true
    precondition, and the precondition witnessing that this is achievable.

    [pp2sp0 pp] has the reading [p /\ (PPM.pre pp -> PPM.post pp a)].
    The actual right adjoint [pp2sp] uses [pp2spBase], which intersects all
    [SPost] values above [fun p a => p /\ PPM.post pp a].  Its underlying
    proposition therefore depends only on [pp]'s postcondition.
    [pp2sp01] places this right adjoint below [pp2sp0]. *)

Definition pp2sp0T {A} (pp : PPM.PrePost A) : SPM.SPostT A :=
  fun p a =>
    SPM.mkOver (p /\ (PPM.pre pp -> PPM.post pp a)) (fun H => proj1 H).

Lemma pp2sp0_mono {A} (pp : PPM.PrePost A) : SPM.sp_mono (pp2sp0T pp).
Proof.
  intros p1 p2 a Hpre [Hp Hpost]. cbn in *.
  split; [ exact (Hpre Hp) | exact Hpost ].
Qed.

Definition pp2sp0 {A} (pp : PPM.PrePost A) : SPM.SPost A :=
  exist _ (pp2sp0T pp) (pp2sp0_mono pp).

Definition sp2pp {A} (sp : SPM.SPost A) : PPM.PrePost A :=
  let post := fun a => forall p : Prop, p -> SPM.app sp p a in
  ( exists p : Prop, (forall a, post a -> SPM.app sp p a) /\ p
  , post ).

(** Intersect all [SPost] values above [fun q x => q /\ PPM.post pp x]. *)
Definition pp2spBase {A} (pp : PPM.PrePost A) (p : Prop) (a : A) : Prop :=
  forall sp : SPM.SPost A,
    (forall x q, q /\ PPM.post pp x -> SPM.app sp q x) -> SPM.app sp p a.

Lemma pp2sp_over {A} (pp : PPM.PrePost A) (p : Prop) (a : A) :
  pp2spBase pp p a -> p.
Proof.
  intro H.
  exact (proj1 (H (pp2sp0 pp)
                  (fun x q Hq => conj (proj1 Hq) (fun _ => proj2 Hq)))).
Qed.

Definition pp2spT {A} (pp : PPM.PrePost A) : SPM.SPostT A :=
  fun p a => SPM.mkOver (pp2spBase pp p a) (pp2sp_over pp p a).

Lemma pp2sp_mono {A} (pp : PPM.PrePost A) : SPM.sp_mono (pp2spT pp).
Proof.
  intros p1 p2 a Hpre H sp Hsp. cbn in *.
  exact (SPM.app_mono sp p1 p2 a Hpre (H sp Hsp)).
Qed.

Definition pp2sp {A} (pp : PPM.PrePost A) : SPM.SPost A :=
  exist _ (pp2spT pp) (pp2sp_mono pp).

Lemma pp2sp01 {A} (pp : PPM.PrePost A) : SP_le (pp2sp pp) (pp2sp0 pp).
Proof.
  intros p a H.
  exact (H (pp2sp0 pp) (fun x q Hq => conj (proj1 Hq) (fun _ => proj2 Hq))).
Qed.

Theorem sp_pp_adjunction {A} (sp : SPM.SPost A) (pp : PPM.PrePost A) :
  PP_le (sp2pp sp) pp <-> SP_le sp (pp2sp pp).
Proof.
  unfold PP_le, SP_le, sp2pp, pp2sp, pp2spT, PPM.pre, PPM.post,
         SPM.app; cbn.
  split.
  - intros [_ Hq] p a Ha sp' Hsp'.
    apply (Hsp' a p). split.
    + exact (SPM.app_over sp p a Ha).
    + apply Hq. intros q Hqh.
      exact (SPM.app_mono sp p q a (fun _ => Hqh) Ha).
  - intro H. split.
    + intros _. exists True. split; [| exact I ].
      intros a Hpost. exact (Hpost True I).
    + intros a Hpost.
      pose proof (H True a (Hpost True I)
                    (pp2sp0 (True, PPM.post pp))
                    (fun x q Hq => conj (proj1 Hq) (fun _ => proj2 Hq))) as H0.
      exact (proj2 H0 I).
Qed.

(* ================================================================= *)
(** ** 5.  [SPost] -| [RelPrePost]                                   *)
(* ================================================================= *)

(** [sp2mr sp] validates [(pre, post)] when everything [sp] can establish
    from [pre] satisfies [post]; [mr2sp mr] is [pre] together with what every
    postcondition [mr] validates must say. *)

Definition sp2mrT {A} (sp : SPM.SPost A) : RPPM.RPPT A :=
  fun p post =>
    exist _ (forall a, SPM.app sp p a -> RPPM.ab (post a))
            (conj (fun H _ => H)
                  (fun H a Ha => H (SPM.app_over sp p a Ha) a Ha)).

Lemma sp2mr_mono {A} (sp : SPM.SPost A) : RPPM.rpp_mono (sp2mrT sp).
Proof.
  intros p1 p2 post1 post2 Hpre Hpost H a Ha. cbn in *.
  exact (Hpost a (H a (SPM.app_mono sp p1 p2 a Hpre Ha))).
Qed.

Definition sp2mr {A} (sp : SPM.SPost A) : RPPM.RelPrePost A :=
  exist _ (sp2mrT sp) (sp2mr_mono sp).

Definition mr2spT {A} (mr : RPPM.RelPrePost A) : SPM.SPostT A :=
  fun p a =>
    SPM.mkOver (p /\ forall post, RPPM.ab (RPPM.runRPP mr p post)
                                  -> RPPM.ab (post a))
               (fun H => proj1 H).

Lemma mr2sp_mono {A} (mr : RPPM.RelPrePost A) : SPM.sp_mono (mr2spT mr).
Proof.
  intros p1 p2 a Hpre [Hp Hall]. cbn in *. split; [ exact (Hpre Hp) |].
  intros post Hr.
  apply (Hall (fun x => exist _ (RPPM.ab (post x))
                          (conj (fun H _ => H)
                                (fun H => H Hp)))).
  apply (RPPM.runRPP_mono mr p1 p2 _ post Hpre); [| exact Hr ].
  intros x Hx. exact Hx.
Qed.

Definition mr2sp {A} (mr : RPPM.RelPrePost A) : SPM.SPost A :=
  exist _ (mr2spT mr) (mr2sp_mono mr).

Theorem sp_mr_adjunction {A} (sp : SPM.SPost A) (mr : RPPM.RelPrePost A) :
  MR_le (sp2mr sp) mr <-> SP_le sp (mr2sp mr).
Proof.
  unfold MR_le, SP_le, sp2mr, sp2mrT, mr2sp, mr2spT,
         SPM.app, RPPM.ab, RPPM.runRPP; cbn.
  split.
  - intros H p a Ha. split; [ exact (SPM.app_over sp p a Ha) |].
    intros post Hr. exact (H p post Hr a Ha).
  - intros H p post Hr a Ha.
    exact (proj2 (H p a Ha) post Hr).
Qed.

(* ================================================================= *)
(** ** Unit and counit                                               *)
(* ================================================================= *)

(** Each adjunction gives the two round trips, by instantiating it at
    reflexivity.  [sp_pp] is DM4all's [pp2sp_sp2pp_loop] /
    [sp2pp_pp2sp_loop]. *)

Corollary pred_pp_unit {A} (post : PredM.Pred A) :
  Pred_le post (pp2pred (pred2pp post)).
Proof. exact (proj1 (pred_pp_adjunction post (pred2pp post)) (reflexivity _)). Qed.

Corollary pred_pp_counit {A} (pp : PPM.PrePost A) :
  PP_le (pred2pp (pp2pred pp)) pp.
Proof. exact (proj2 (pred_pp_adjunction (pp2pred pp) pp) (reflexivity _)). Qed.

Corollary wp_pp_under_unit {A} (pp : PPM.PrePost A) :
  PP_le pp (wp2pp_under (pp2wp_under pp)).
Proof. exact (proj2 (wp_pp_under_adjunction pp (pp2wp_under pp)) (reflexivity _)). Qed.

Corollary wp_pp_under_counit {A} (w : WPure A) :
  WP_le (pp2wp_under (wp2pp_under w)) w.
Proof. exact (proj1 (wp_pp_under_adjunction (wp2pp_under w) w) (reflexivity _)). Qed.

Corollary wp_mr_unit {A} (w : WPure A) : WP_le w (mr2wp (wp2mr w)).
Proof. exact (proj2 (wp_mr_adjunction w (wp2mr w)) (reflexivity _)). Qed.

Corollary wp_mr_counit {A} (r : RPPM.RelPrePost A) : MR_le (wp2mr (mr2wp r)) r.
Proof. exact (proj1 (wp_mr_adjunction (mr2wp r) r) (reflexivity _)). Qed.

Corollary pp2sp_sp2pp_loop {A} (sp : SPM.SPost A) :
  SP_le sp (pp2sp (sp2pp sp)).
Proof. exact (proj1 (sp_pp_adjunction sp (sp2pp sp)) (reflexivity _)). Qed.

Corollary sp2pp_pp2sp_loop {A} (pp : PPM.PrePost A) :
  PP_le (sp2pp (pp2sp pp)) pp.
Proof. exact (proj2 (sp_pp_adjunction (pp2sp pp) pp) (reflexivity _)). Qed.

Corollary sp_mr_unit {A} (sp : SPM.SPost A) : SP_le sp (mr2sp (sp2mr sp)).
Proof. exact (proj1 (sp_mr_adjunction sp (sp2mr sp)) (reflexivity _)). Qed.

Corollary sp_mr_counit {A} (mr : RPPM.RelPrePost A) : MR_le (sp2mr (mr2sp mr)) mr.
Proof. exact (proj2 (sp_mr_adjunction (mr2sp mr) mr) (reflexivity _)). Qed.
