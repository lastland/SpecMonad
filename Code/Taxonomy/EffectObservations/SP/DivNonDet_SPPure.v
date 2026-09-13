From ExtLib Require Import OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

(** * SP observations of [divnd] into the pure spec monads

    [divnd A] has outcome set [option A -> Prop], with [None] read as
    divergence.  These observations retain only its terminating slice:

      [unOptionT m (Some a)]

    The targets are well-formed subsets of [SPPure A = Prop -> A -> Prop].
    Unlike [StDivNonDet_SPSt.v], there is no initial-state witness: the ASP
    reading is [pre /\ unOptionT m (Some a)], and the DSLP reading is
    [unOptionT m (Some a) -> pre].  Thus [divergeD] has a false ASP reading
    and a true DSLP reading at every precondition and result.

    The file defines all four observations and proves their return/bind laws.
    [obsDSP_is_obsASP] and [obsASLP_is_obsDSLP] show that their conjunction
    and disjunction collapse to ASP and DSLP, respectively.  The pure carrier
    equivalences are in [BaseSpecMonads/DSPMonad.v] and
    [BaseSpecMonads/ASLPMonad.v].  [PureObs] qualifies these names to
    distinguish them from the stateful observations. *)

Module PureObs.

Section PureObservations.

  (** The terminating slice of a bind: one case, since the divergent branch
      cannot produce a [Some] outcome. *)
  Lemma outcomes_bind {A B} (x : divnd A) (f : A -> divnd B) (r : B) :
    unOptionT (x >>= f) (Some r)
    <-> (exists a, unOptionT x (Some a) /\ unOptionT (f a) (Some r)).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. destruct oy as [a|]; cbn in *.
      + exists a. split; [ exact H1 | exact H2 ].
      + congruence.
    - intros [a [H1 H2]]. exists (Some a). split; [ exact H1 | exact H2 ].
  Qed.

  Lemma outcomes_ret {A} (a : A) (r : A) :
    unOptionT (ret a : divnd A) (Some r) <-> r = a.
  Proof. cbn. split; intro H; congruence. Qed.

  (** [divergeD] has no terminating outcome at all. *)
  Lemma outcomes_diverge {A} (r : A) :
    ~ unOptionT (divergeD : divnd A) (Some r).
  Proof. cbn. intro H. congruence. Qed.

  (* ---- the two observations ---- *)

  (** Outcome space is the TERMINATING SLICE [A]: there is no [r] denoting
      divergence, so these observations cannot constrain it. *)
  #[program] Definition obsASP {A} (m : divnd A) : ASPSP A :=
    fun p a => p /\ unOptionT m (Some a).
  Next Obligation. intros p a. tauto. Qed.

  #[program] Definition obsDSLP {A} (m : divnd A) : DSLPSP A :=
    fun p a => unOptionT m (Some a) -> p.
  Next Obligation.
    intros p a. split.
    - intro H. destruct (classic p) as [Hp | Hnp]; [ left; exact Hp |].
      right. intro HU. exact (Hnp (H HU)).
    - intros [Hp | Hn] HU; [ exact Hp | destruct (Hn HU) ].
  Qed.

  Lemma getASP_obsASP {A} (m : divnd A) p a :
    getASP (obsASP m) p a <-> (p /\ unOptionT m (Some a)).
  Proof. split; intro H; exact H. Qed.

  Lemma getDSLP_obsDSLP {A} (m : divnd A) p a :
    getDSLP (obsDSLP m) p a <-> (unOptionT m (Some a) -> p).
  Proof. split; intro H; exact H. Qed.

  (** The slice is blind to divergence. *)
  Lemma obsASP_divergeD {A} (p : Prop) (a : A) :
    ~ getASP (obsASP divergeD) p a.
  Proof. intros [_ Hr]. exact (outcomes_diverge a Hr). Qed.

  Lemma obsDSLP_divergeD {A} (p : Prop) (a : A) :
    getDSLP (obsDSLP divergeD) p a.
  Proof. intro Hr. destruct (outcomes_diverge a Hr). Qed.

  (* ---- each observation is a monad morphism ---- *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : divnd A)) (ret a).
  Proof.
    unfold eq1, Eq1_ASPSP. intros p b. split.
    - intros [Hp Hr]. split; [ exact Hp | exact (proj1 (outcomes_ret a b) Hr) ].
    - intros [Hp Heq]. split; [ exact Hp | exact (proj2 (outcomes_ret a b) Heq) ].
  Qed.

  Theorem obsASP_bind {A B} (x : divnd A) (f : A -> divnd B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    unfold eq1, Eq1_ASPSP. intros p b. split.
    - intros [Hp Hrel]. apply outcomes_bind in Hrel.
      destruct Hrel as [a [Hx Hk]].
      exists a. split; [ split; [ exact Hp | exact Hx ] | exact Hk ].
    - intros [a [[Hp Hx] Hk]].
      split; [ exact Hp |]. apply outcomes_bind.
      exists a. split; [ exact Hx | exact Hk ].
  Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : divnd A)) (ret a).
  Proof.
    unfold eq1, Eq1_DSLPSP. intros p b. split.
    - intros H Heq. exact (H (proj2 (outcomes_ret a b) Heq)).
    - intros H Hr. exact (H (proj1 (outcomes_ret a b) Hr)).
  Qed.

  Theorem obsDSLP_bind {A B} (x : divnd A) (f : A -> divnd B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    unfold eq1, Eq1_DSLPSP. intros p b. split.
    - intros H a Hk Hx. apply H. apply outcomes_bind.
      exists a. split; [ exact Hx | exact Hk ].
    - intros H Hrel. apply outcomes_bind in Hrel.
      destruct Hrel as [a [Hx Hk]]. exact (H a Hk Hx).
  Qed.


  (* ---- the demonic and angelic-liberal observations ---- *)

  (** As in the stateful files, DSP is the conjunction of the ASP and DSLP
      readings and ASLP their disjunction.  Here both collapse: see
      [obsDSP_is_obsASP] / [obsASLP_is_obsDSLP] below. *)

  #[program] Definition obsDSP {A} (m : divnd A) : DSPSP A :=
    fun p a => (obsASP m p a) /\ (obsDSLP m p a).
  Next Obligation.
    apply strict_conj_iff_singleton. intros p a. cbn. tauto.
  Qed.

  #[program] Definition obsASLP {A} (m : divnd A) : ASLPSP A :=
    fun p a => (obsASP m p a) \/ (obsDSLP m p a).
  Next Obligation.
    apply term_disj_iff_msingleton. intros p a. cbn.
    destruct (classic p) as [Hp | Hnp]; [ tauto |].
    destruct (classic (unOptionT m (Some a))) as [HU | HnU]; tauto.
  Qed.

  Lemma getDSP_obsDSP {A} (m : divnd A) p a :
    getDSP (obsDSP m) p a <-> (getASP (obsASP m) p a /\ getDSLP (obsDSLP m) p a).
  Proof. split; intro H; exact H. Qed.

  Lemma getASLP_obsASLP {A} (m : divnd A) p a :
    getASLP (obsASLP m) p a <-> (getASP (obsASP m) p a \/ getDSLP (obsDSLP m) p a).
  Proof. split; intro H; exact H. Qed.

  (** ** The collapse, at the level of observations

      With no state there is a single "input", so [R⁻¹(a) ⊆ pre] and
      [R⁻¹(a) ∩ pre ≠ ∅] say the same thing whenever [R⁻¹(a)] is inhabited.
      The conjunction therefore falls back on the angelic reading and the
      disjunction on the demonic-liberal one. *)

  Theorem obsDSP_is_obsASP {A} (m : divnd A) p a :
    getDSP (obsDSP m) p a <-> getASP (obsASP m) p a.
  Proof. cbn. tauto. Qed.

  Theorem obsASLP_is_obsDSLP {A} (m : divnd A) p a :
    getASLP (obsASLP m) p a <-> getDSLP (obsDSLP m) p a.
  Proof. cbn. tauto. Qed.

  Lemma obsDSP_divergeD {A} (p : Prop) (a : A) :
    ~ getDSP (obsDSP divergeD) p a.
  Proof. intro H. exact (obsASP_divergeD p a (proj1 (obsDSP_is_obsASP _ p a) H)). Qed.

  Lemma obsASLP_divergeD {A} (p : Prop) (a : A) :
    getASLP (obsASLP divergeD) p a.
  Proof. apply obsASLP_is_obsDSLP. exact (obsDSLP_divergeD p a). Qed.

  (* ---- both are monad morphisms, via the collapse ---- *)

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : divnd A)) (ret a).
  Proof.
    unfold eq1, Eq1_DSPSP. intros p b.
    rewrite (obsDSP_is_obsASP _ p b). exact (obsASP_ret a p b).
  Qed.

  Theorem obsDSP_bind {A B} (x : divnd A) (f : A -> divnd B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    unfold eq1, Eq1_DSPSP. intros p b.
    rewrite (obsDSP_is_obsASP _ p b). rewrite (obsASP_bind x f p b).
    split.
    - intros [a [Hm Hk]]. exists a. cbn in *. tauto.
    - intros [a [Hm Hk]]. exists a. cbn in *. tauto.
  Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : divnd A)) (ret a).
  Proof.
    unfold eq1, Eq1_ASLPSP. intros p b.
    rewrite (obsASLP_is_obsDSLP _ p b). exact (obsDSLP_ret a p b).
  Qed.

  Theorem obsASLP_bind {A B} (x : divnd A) (f : A -> divnd B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof.
    unfold eq1, Eq1_ASLPSP. intros p b.
    rewrite (obsASLP_is_obsDSLP _ p b). rewrite (obsDSLP_bind x f p b).
    split; intros H a; specialize (H a); cbn in *; tauto.
  Qed.
End PureObservations.

Arguments obsASP {_}.
Arguments obsDSLP {_}.
Arguments obsDSP {_}.
Arguments obsASLP {_}.

(* ==================================================================== *)
(** * Triples                                                            *)
(* ==================================================================== *)

Inductive approxKind := | Under | Over.

Definition ordSPPure {A} (m1 m2 : SPPure A) : Prop :=
  forall p a, m1 p a -> m2 p a.

Definition pp2_over {A} (pre : Prop) (post : A -> Prop) : SPPure A :=
  fun p a => (p -> pre) -> post a.

Definition pp2_under {A} (pre : Prop) (post : A -> Prop) : SPPure A :=
  fun p a => (pre -> p) /\ post a.

Section PureTriples.

  Definition tripleASP {A}
    (prog : divnd A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall a, getASP (obsASP prog) pre a -> post a
    | Under => forall a, post a -> getASP (obsASP prog) pre a
    end.

  Definition tripleDSLP {A}
    (prog : divnd A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall a, getDSLP (obsDSLP prog) pre a -> post a
    | Under => forall a, post a -> getDSLP (obsDSLP prog) pre a
    end.

  Definition tripleASPspec {A} (prog : divnd A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => ordSPPure (getASP (obsASP prog)) (pp2_over pre post)
    | Under => ordSPPure (pp2_under pre post) (getASP (obsASP prog))
    end.

  Definition tripleDSLPspec {A} (prog : divnd A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => ordSPPure (getDSLP (obsDSLP prog)) (pp2_over pre post)
    | Under => ordSPPure (pp2_under pre post) (getDSLP (obsDSLP prog))
    end.

  Theorem tripleASPDefEq {A} (prog : divnd A) kind pre post :
    tripleASP prog kind pre post <-> tripleASPspec prog kind pre post.
  Proof.
    unfold tripleASP, tripleASPspec, ordSPPure, pp2_over, pp2_under.
    destruct kind; split.
    - intros H p a [Hsub Hpost]. destruct (H a Hpost) as [Hpre Hreach].
      split; [ exact (Hsub Hpre) | exact Hreach ].
    - intros H a Hpost. exact (H pre a (conj (fun Hs => Hs) Hpost)).
    - intros H p a [Hp Hreach] Hsub.
      exact (H a (conj (Hsub Hp) Hreach)).
    - intros H a Hobs. exact (H pre a Hobs (fun Hs => Hs)).
  Qed.

  Theorem tripleDSLPDefEq {A} (prog : divnd A) kind pre post :
    tripleDSLP prog kind pre post <-> tripleDSLPspec prog kind pre post.
  Proof.
    unfold tripleDSLP, tripleDSLPspec, ordSPPure, pp2_over, pp2_under.
    destruct kind; split.
    - intros H p a [Hsub Hpost] Hout. exact (Hsub (H a Hpost Hout)).
    - intros H a Hpost. exact (H pre a (conj (fun Hs => Hs) Hpost)).
    - intros H p a Hdslp Hsub. apply (H a).
      intro Hout. exact (Hsub (Hdslp Hout)).
    - intros H a Hdslp. exact (H pre a Hdslp (fun Hs => Hs)).
  Qed.


  Definition tripleDSP {A}
    (prog : divnd A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall a, getDSP (obsDSP prog) pre a -> post a
    | Under => forall a, post a -> getDSP (obsDSP prog) pre a
    end.

  Definition tripleASLP {A}
    (prog : divnd A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall a, getASLP (obsASLP prog) pre a -> post a
    | Under => forall a, post a -> getASLP (obsASLP prog) pre a
    end.

  (** The degeneracy, transported to triples: a DSP triple is an ASP triple
      and an ASLP triple is a DSLP one. *)
  Theorem tripleDSP_is_tripleASP {A} (prog : divnd A) kind pre (post : A -> Prop) :
    tripleDSP prog kind pre post <-> tripleASP prog kind pre post.
  Proof.
    destruct kind; cbn; split.
    - intros H a Hp. exact (proj1 (obsDSP_is_obsASP prog pre a) (H a Hp)).
    - intros H a Hp. exact (proj2 (obsDSP_is_obsASP prog pre a) (H a Hp)).
    - intros H a Hx. exact (H a (proj2 (obsDSP_is_obsASP prog pre a) Hx)).
    - intros H a Hx. exact (H a (proj1 (obsDSP_is_obsASP prog pre a) Hx)).
  Qed.

  Theorem tripleASLP_is_tripleDSLP {A} (prog : divnd A) kind pre (post : A -> Prop) :
    tripleASLP prog kind pre post <-> tripleDSLP prog kind pre post.
  Proof.
    destruct kind; cbn; split.
    - intros H a Hp. exact (proj1 (obsASLP_is_obsDSLP prog pre a) (H a Hp)).
    - intros H a Hp. exact (proj2 (obsASLP_is_obsDSLP prog pre a) (H a Hp)).
    - intros H a Hx. exact (H a (proj2 (obsASLP_is_obsDSLP prog pre a) Hx)).
    - intros H a Hx. exact (H a (proj1 (obsASLP_is_obsDSLP prog pre a) Hx)).
  Qed.
  (** A [divergeD]-only program satisfies every [Over] triple and only the
      trivial [Under] ones — the slice sees nothing. *)
  Theorem tripleASP_divergeD_over {A} pre (post : A -> Prop) :
    tripleASP divergeD Over pre post.
  Proof. intros a Hc. destruct (obsASP_divergeD pre a Hc). Qed.

  Theorem tripleDSLP_divergeD_over {A} pre (post : A -> Prop) :
    tripleDSLP divergeD Over pre post -> forall a, post a.
  Proof. intros H a. exact (H a (obsDSLP_divergeD pre a)). Qed.

End PureTriples.

Arguments tripleASP {_}.
Arguments tripleDSLP {_}.
Arguments tripleDSP {_}.
Arguments tripleASLP {_}.

End PureObs.
