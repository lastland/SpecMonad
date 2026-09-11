From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import NewGaloisConnections.

Import MonadNotation.
Open Scope monad_scope.

(** * SP observations of [stdivnd] over a plain stateful outcome

    [stdivnd S A] has outcome set [option (A * S) -> Prop], with [None] read as
    divergence.  [SPSimplerSpecMonads] indexes its transformers by [A * S], so the
    observations here read the TERMINATING SLICE

      [unOptionT (runStateT m s) (Some r)]     with [r : A * S]

    — the normal returns only, with divergence projected away.  This is exactly
    the move [NonDetItObservationNew] makes for [stdivexcnd], one layer down.

    Contrast with [NonDetObservationNew], which observes the SAME computation
    monad into the [option (A * S)]-indexed spec monads and therefore keeps
    [None] visible: there [getASPSt (obsASP m) pre None] asserts "some
    [pre]-state may diverge".  Here divergence cannot be spoken about at all;
    the transformers constrain only the terminating behaviour.

    Because the slice drops the one exceptional outcome, the composite relation
    of a [bind] has a single case, and the observation proofs are correspondingly
    shorter than their [option]-indexed counterparts. *)

Import StTrans StASP StDSLP StDSP StASLP StSP.

Module TermSliceObs.

Section StObservations.
  Variable S : Type.

  (** The terminating slice of a bind: one case, since the divergent branch
      cannot produce a [Some] outcome. *)
  Lemma outcomes_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) s (r : B * S) :
    unOptionT (runStateT (x >>= f) s) (Some r)
    <-> (exists a s', unOptionT (runStateT x s) (Some (a, s'))
                      /\ unOptionT (runStateT (f a) s') (Some r)).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. destruct oy as [[a s']|]; cbn in *.
      + exists a, s'. split; [ exact H1 | exact H2 ].
      + congruence.
    - intros [a [s' [H1 H2]]]. exists (Some (a, s')).
      split; [ exact H1 | exact H2 ].
  Qed.

  Lemma outcomes_ret {A} (a : A) (s : S) (r : A * S) :
    unOptionT (runStateT (ret a : stdivnd S A) s) (Some r) <-> r = (a, s).
  Proof. cbn. split; intro H; congruence. Qed.

  (** [divergeD] has no terminating outcome at all. *)
  Lemma outcomes_diverge {A} (s : S) (r : A * S) :
    ~ unOptionT (runStateT (divergeD : stdivnd S A) s) (Some r).
  Proof. cbn. intro H. congruence. Qed.

  (* ---- the two observations ---- *)

  (** Outcome space is the TERMINATING SLICE [A * S]: there is no [r] denoting
      divergence, so these observations cannot constrain it. *)
  #[program] Definition obsASP {A} (m : stdivnd S A) : StASP.ASPSt S A :=
    fun pre (r : A * S) => exists s, pre s /\ unOptionT (runStateT m s) (Some r).
  Next Obligation.
    intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hr ].
    - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hr ].
  Qed.

  #[program] Definition obsDSLP {A} (m : stdivnd S A) : StDSLP.DSLPSt S A :=
    fun pre (r : A * S) => forall s, unOptionT (runStateT m s) (Some r) -> pre s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => unOptionT (runStateT m s) (Some r))).
  Qed.

  Lemma getProgASP_obsASP {A} (m : stdivnd S A) pre r :
    getASPSt (obsASP m) pre r
    <-> (exists s, pre s /\ unOptionT (runStateT m s) (Some r)).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivnd S A) pre r :
    getDSLPSt (obsDSLP m) pre r
    <-> (forall s, unOptionT (runStateT m s) (Some r) -> pre s).
  Proof. split; intro H; exact H. Qed.

  (** The slice is blind to divergence: [divergeD] observes as the empty
      angelic postcondition and the trivial demonic one. *)
  Lemma obsASP_divergeD {A} (pre : S -> Prop) (r : A * S) :
    ~ getASPSt (obsASP divergeD) pre r.
  Proof. intros [s [_ Hr]]. exact (outcomes_diverge s r Hr). Qed.

  Lemma obsDSLP_divergeD {A} (pre : S -> Prop) (r : A * S) :
    getDSLPSt (obsDSLP divergeD) pre r.
  Proof. intros s Hr. destruct (outcomes_diverge s r Hr). Qed.

  (* ---- each observation is a monad morphism ---- *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ASPSt. intros pre r. split.
    - intros [s [Hp Hr]]. exists s.
      split; [ exact Hp | exact (proj1 (outcomes_ret a s r) Hr) ].
    - intros [s [Hp Heq]]. exists s.
      split; [ exact Hp | exact (proj2 (outcomes_ret a s r) Heq) ].
  Qed.

  Theorem obsASP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    unfold eq1, Eq1__ASPSt. intros pre r. split.
    - intros [s [Hp Hrel]]. apply outcomes_bind in Hrel.
      destruct Hrel as [a [s' [Hx Hk]]].
      exists a. exists s'. split; [| exact Hk ].
      exists s. split; [ exact Hp | exact Hx ].
    - intros [a [s' [[s [Hp Hx]] Hf]]].
      exists s. split; [ exact Hp |]. apply outcomes_bind.
      exists a, s'. split; [ exact Hx | exact Hf ].
  Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__DSLPSt. intros pre r. split.
    - intros H s0 Heq. exact (H s0 (proj2 (outcomes_ret a s0 r) Heq)).
    - intros H s Hr. exact (H s (proj1 (outcomes_ret a s r) Hr)).
  Qed.

  Theorem obsDSLP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    unfold eq1, Eq1__DSLPSt. intros pre r. split.
    - intros H a s' Hf s Hx. apply H. apply outcomes_bind.
      exists a, s'. split; [ exact Hx | exact Hf ].
    - intros H s Hrel. apply outcomes_bind in Hrel.
      destruct Hrel as [a [s' [Hx Hk]]]. exact (H a s' Hk s Hx).
  Qed.

  (* ---- the demonic and angelic-liberal observations ---- *)

  #[program] Definition obsDSP {A} (m : stdivnd S A) : StDSP.DSPSt S A :=
    fun pre (r : A * S) => (obsASP m pre r) /\ (obsDSLP m pre r).
  Next Obligation.
    exact (dsp_shape_wf S (fun s r => unOptionT (runStateT m s) (Some r))).
  Qed.

  #[program] Definition obsASLP {A} (m : stdivnd S A) : StASLP.ASLPSt S A :=
    fun pre (r : A * S) => (obsASP m pre r) \/ (obsDSLP m pre r).
  Next Obligation.
    exact (aslp_shape_wf S (fun s r => unOptionT (runStateT m s) (Some r))).
  Qed.

  Lemma getProgDSP_obsDSP {A} (m : stdivnd S A) pre r :
    getDSPSt (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) (Some r))
         /\ (forall s, unOptionT (runStateT m s) (Some r) -> pre s)).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgASLP_obsASLP {A} (m : stdivnd S A) pre r :
    getASLPSt (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) (Some r))
         \/ (forall s, unOptionT (runStateT m s) (Some r) -> pre s)).
  Proof. split; intro H; exact H. Qed.

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__DSPSt. intros pre r.
    apply (dsp_cong S
             (fun s r0 => unOptionT (runStateT (ret a : stdivnd S A) s) (Some r0))
             (fun s r0 => r0 = (a, s))).
    intros s r0. exact (outcomes_ret a s r0).
  Qed.

  Theorem obsDSP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    unfold eq1, Eq1__DSPSt. intros pre r.
    assert (Hx : forall s y,
               (getDSPSt (obsDSP x) (fun _ => True) y
                /\ ~ getDSPSt (obsDSP x) (fun t => t <> s) y)
               <-> unOptionT (runStateT x s) (Some y)).
    { intros s y.
      exact (dsp_recov S (fun s1 r1 => unOptionT (runStateT x s1) (Some r1)) s y). }
    assert (Hf : forall a s y,
               (getDSPSt (obsDSP (f a)) (fun _ => True) y
                /\ ~ getDSPSt (obsDSP (f a)) (fun t => t <> s) y)
               <-> unOptionT (runStateT (f a) s) (Some y)).
    { intros a s y.
      exact (dsp_recov S (fun s1 r1 => unOptionT (runStateT (f a) s1) (Some r1)) s y). }
    refine (iff_trans
              (dsp_cong S
                 (fun s r0 => unOptionT (runStateT (x >>= f) s) (Some r0))
                 (fun s r0 =>
                    exists a smid,
                      (getDSPSt (obsDSP x) (fun _ => True) (a, smid)
                       /\ ~ getDSPSt (obsDSP x) (fun t => t <> s) (a, smid))
                      /\ (getDSPSt (obsDSP (f a)) (fun _ => True) r0
                          /\ ~ getDSPSt (obsDSP (f a)) (fun t => t <> smid) r0))
                 _ pre r)
              (iff_sym (bindDSPProg_dsp S (obsDSP x) (fun a => obsDSP (f a)) pre r))).
    intros s r0. split.
    - intro H. apply outcomes_bind in H. destruct H as [a [s' [Hxx Hk]]].
      exists a, s'. split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
    - intros [a [s' [Hm Hk]]]. apply Hx in Hm. apply Hf in Hk.
      apply outcomes_bind. exists a, s'. split; [ exact Hm | exact Hk ].
  Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ASLPSt. intros pre r.
    apply (aslp_cong S
             (fun s r0 => unOptionT (runStateT (ret a : stdivnd S A) s) (Some r0))
             (fun s r0 => r0 = (a, s))).
    intros s r0. exact (outcomes_ret a s r0).
  Qed.

  Theorem obsASLP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof.
    unfold eq1, Eq1__ASLPSt. intros pre r.
    assert (Hx : forall s y,
               (~ getASLPSt (obsASLP x) (fun _ => False) y
                /\ getASLPSt (obsASLP x) (fun t => t = s) y)
               <-> unOptionT (runStateT x s) (Some y)).
    { intros s y.
      exact (aslp_recov S (fun s1 r1 => unOptionT (runStateT x s1) (Some r1)) s y). }
    assert (Hf : forall a s y,
               (~ getASLPSt (obsASLP (f a)) (fun _ => False) y
                /\ getASLPSt (obsASLP (f a)) (fun t => t = s) y)
               <-> unOptionT (runStateT (f a) s) (Some y)).
    { intros a s y.
      exact (aslp_recov S (fun s1 r1 => unOptionT (runStateT (f a) s1) (Some r1)) s y). }
    refine (iff_trans
              (aslp_cong S
                 (fun s r0 => unOptionT (runStateT (x >>= f) s) (Some r0))
                 (fun s r0 =>
                    exists a smid,
                      (~ getASLPSt (obsASLP x) (fun _ => False) (a, smid)
                       /\ getASLPSt (obsASLP x) (fun t => t = s) (a, smid))
                      /\ (~ getASLPSt (obsASLP (f a)) (fun _ => False) r0
                          /\ getASLPSt (obsASLP (f a)) (fun t => t = smid) r0))
                 _ pre r)
              (iff_sym (bindASLPProg_aslp S (obsASLP x) (fun a => obsASLP (f a)) pre r))).
    intros s r0. split.
    - intro H. apply outcomes_bind in H. destruct H as [a [s' [Hxx Hk]]].
      exists a, s'. split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
    - intros [a [s' [Hm Hk]]]. apply Hx in Hm. apply Hf in Hk.
      apply outcomes_bind. exists a, s'. split; [ exact Hm | exact Hk ].
  Qed.

End StObservations.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.

(* ==================================================================== *)
(** * Triples                                                            *)
(* ==================================================================== *)

Inductive approxKind := | Under | Over.

Definition ordSPSt {S A} (m1 m2 : @SPSt S A) : Prop :=
  forall pre r, m1 pre r -> m2 pre r.

Definition pp2_over {S A} (pre : S -> Prop) (post : (A * S) -> Prop)
  : @SPSt S A :=
  fun p r => (forall s, p s -> pre s) -> post r.

Definition pp2_under {S A} (pre : S -> Prop) (post : (A * S) -> Prop)
  : @SPSt S A :=
  fun p r => (forall s, pre s -> p s) /\ post r.

Section StTriples.

  Definition tripleASP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getASPSt (obsASP prog) pre r -> post r
    | Under => forall r, post r -> getASPSt (obsASP prog) pre r
    end.

  Definition tripleDSLP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getDSLPSt (obsDSLP prog) pre r -> post r
    | Under => forall r, post r -> getDSLPSt (obsDSLP prog) pre r
    end.

  Definition tripleDSP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getDSPSt (obsDSP prog) pre r -> post r
    | Under => forall r, post r -> getDSPSt (obsDSP prog) pre r
    end.

  Definition tripleASLP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getASLPSt (obsASLP prog) pre r -> post r
    | Under => forall r, post r -> getASLPSt (obsASLP prog) pre r
    end.

  (** Two of the four (observation, direction) pairs have an IN-MONAD
      comparison target: ASP/[Over] against [pp2asp_over] and DSLP/[Under]
      against [pp2dslp_under], both exact and with no side condition
      ([gen_asp_over], [gen_dslp_under]).  Those two are stated inside the
      specification monad, in its own order.

      The other two have no such target.  [tASPunder] and [tDSLPover]
      characterise their triples only in the [At]-order and only under a
      (co-)nonemptiness hypothesis, because [SingletonProg] makes every ASP
      false at the empty precondition and [MSingletonProg] makes every DSLP
      true at the full one.  So those comparisons are made in the ambient
      [SPSt], where [pp2_under] / [pp2_over] live and no healthiness is
      demanded of the target. *)

  Definition tripleASPspec {S A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordASPSt (obsASP prog) (pp2asp_over pre post)
    | Under => ordSPSt (pp2_under pre post) (getASPSt (obsASP prog))
    end.

  Definition tripleDSLPspec {S A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordSPSt (getDSLPSt (obsDSLP prog)) (pp2_over pre post)
    | Under => ordDSLPSt (pp2dslp_under pre post) (obsDSLP prog)
    end.

  Theorem tripleASPDefEq {S A} (prog : stdivnd S A) kind pre post :
    tripleASP prog kind pre post <-> tripleASPspec prog kind pre post.
  Proof.
    destruct kind.
    - (* [Under]: the ambient comparison, as no in-monad target exists *)
      unfold tripleASP, tripleASPspec, ordSPSt, pp2_under. split.
      + intros H p r [Hsub Hpost]. destruct (H r Hpost) as [s [Hpre Hreach]].
        exists s. split; [ exact (Hsub s Hpre) | exact Hreach ].
      + intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* [Over]: in-monad, and exact *)
      exact (gen_asp_over S (obsASP prog) pre post).
  Qed.

  Theorem tripleDSLPDefEq {S A} (prog : stdivnd S A) kind pre post :
    tripleDSLP prog kind pre post <-> tripleDSLPspec prog kind pre post.
  Proof.
    destruct kind.
    - (* [Under]: in-monad, and exact *)
      exact (gen_dslp_under S (obsDSLP prog) pre post).
    - (* [Over]: the ambient comparison *)
      unfold tripleDSLP, tripleDSLPspec, ordSPSt, pp2_over. split.
      + intros H p r Hdslp Hsub. apply (H r).
        intros s Hout. exact (Hsub s (Hdslp s Hout)).
      + intros H r Hdslp. exact (H pre r Hdslp (fun s Hs => Hs)).
  Qed.

  (** A [divergeD]-only program satisfies every [Over] triple and only the
      trivial [Under] ones — the slice sees nothing. *)
  Theorem tripleASP_divergeD_over {S A} pre (post : (A * S) -> Prop) :
    tripleASP divergeD Over pre post.
  Proof. intros r Hc. destruct (obsASP_divergeD S pre r Hc). Qed.

  Theorem tripleDSLP_divergeD_over {S A} pre (post : (A * S) -> Prop) :
    tripleDSLP divergeD Over pre post -> forall r, post r.
  Proof. intros H r. exact (H r (obsDSLP_divergeD S pre r)). Qed.

End StTriples.

Arguments tripleASP {_} {_}.
Arguments tripleDSLP {_} {_}.
Arguments tripleDSP {_} {_}.
Arguments tripleASLP {_} {_}.

End TermSliceObs.
