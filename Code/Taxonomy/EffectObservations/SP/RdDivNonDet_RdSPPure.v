From ExtLib Require Import Monad MonadReader ReaderMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  StExcNonDet StDivITree DivNonDet RdDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import DivNonDet_SPPure.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

(** * SP observations of [rddivnd] into the pure spec monads under [readerT]

    [rddivnd R A = readerT R divnd A].  The environment is read-only, so the
    outcome of a computation carries no final environment — it is just
    [option A], exactly what [DivNonDet_SPPure.v] observes.  The observations
    here therefore apply that file's pointwise, one environment at a time, and
    the target is the SAME transformer applied to the specification side:

      [rddivnd R A = readerT R divnd A]   -->   [ASPRd R A = readerT R ASPSP A]

    So the reader is threaded through the observation rather than absorbed into
    it, and every law reduces to the corresponding law of [PureObs].
    The four targets [ASPRd] / [DSLPRd] / [DSPRd] / [ASLPRd] are defined in
    the SP monad files themselves, each as [readerT R] over the corresponding
    pure monad, with laws from the generic [readerT] instances in
    [ComputationMonads/StDivITree.v].

    **The alternative reading, and why it is not here.**  One could instead let
    the precondition range over SETS of environments, giving

      [(R -> Prop) -> A -> Prop]

    which is the [StDivNonDet_SPSt.v] shape with the outcome's environment
    component dropped.  That is a genuinely different observation — it couples
    the environments, exactly as a shared [S -> Prop] couples initial states —
    and it is not any existing carrier, so it would need a new one.  Nothing
    below covers it.

    As in [DivNonDet_SPPure.v], DSP and ASLP degenerate: [obsDSP_is_obsASP] and
    [obsASLP_is_obsDSLP] hold environment by environment, so they hold here
    too. *)

Module RdPureObs.

Section RdObservations.
  Variable R : Type.

  (** The four observations: [PureObs]' applied under the reader. *)

  Definition obsASP {A} (m : rddivnd R A) : ASPRd R A :=
    mkReaderT (fun r => PureObs.obsASP (runReaderT m r)).

  Definition obsDSLP {A} (m : rddivnd R A) : DSLPRd R A :=
    mkReaderT (fun r => PureObs.obsDSLP (runReaderT m r)).

  Definition obsDSP {A} (m : rddivnd R A) : DSPRd R A :=
    mkReaderT (fun r => PureObs.obsDSP (runReaderT m r)).

  Definition obsASLP {A} (m : rddivnd R A) : ASLPRd R A :=
    mkReaderT (fun r => PureObs.obsASLP (runReaderT m r)).

  (** The readings, environment by environment. *)

  Lemma getASP_obsASP {A} (m : rddivnd R A) (r : R) p a :
    getASPRd (obsASP m) r p a
    <-> (p /\ unOptionT (runReaderT m r) (Some a)).
  Proof. exact (PureObs.getASP_obsASP (runReaderT m r) p a). Qed.

  Lemma getDSLP_obsDSLP {A} (m : rddivnd R A) (r : R) p a :
    getDSLPRd (obsDSLP m) r p a
    <-> (unOptionT (runReaderT m r) (Some a) -> p).
  Proof. exact (PureObs.getDSLP_obsDSLP (runReaderT m r) p a). Qed.

  (** The slice is blind to divergence, in every environment. *)

  Lemma obsASP_divergeD {A} (r : R) (p : Prop) (a : A) :
    ~ getASPRd (obsASP (divergeD : rddivnd R A)) r p a.
  Proof. exact (PureObs.obsASP_divergeD p a). Qed.

  Lemma obsDSLP_divergeD {A} (r : R) (p : Prop) (a : A) :
    getDSLPRd (obsDSLP (divergeD : rddivnd R A)) r p a.
  Proof. exact (PureObs.obsDSLP_divergeD p a). Qed.

  (** [ask] observes as "the result is this environment". *)

  Lemma obsASP_askD (r : R) (p : Prop) (a : R) :
    getASPRd (obsASP (askD R)) r p a <-> (p /\ a = r).
  Proof.
    rewrite getASP_obsASP. cbn.
    split; intros [Hp H]; split; try exact Hp; congruence.
  Qed.

  (** [local] reindexes the environment before observing. *)

  Lemma obsASP_localD {A} (f : R -> R) (m : rddivnd R A) (r : R) p (a : A) :
    getASPRd (obsASP (localD f m)) r p a
    <-> getASPRd (obsASP m) (f r) p a.
  Proof. rewrite !getASP_obsASP. cbn. split; intro H; exact H. Qed.

  (* ---- each observation is a monad morphism ---- *)

  (** Every law is the corresponding [PureObs] law read at each environment:
      [runReaderT] commutes with [ret] and [bind] on both sides definitionally,
      so the goals are literally the pure ones. *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : rddivnd R A)) (ret a).
  Proof. intro r. exact (PureObs.obsASP_ret a). Qed.

  Theorem obsASP_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    intro r.
    exact (PureObs.obsASP_bind (runReaderT x r) (fun a => runReaderT (f a) r)).
  Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : rddivnd R A)) (ret a).
  Proof. intro r. exact (PureObs.obsDSLP_ret a). Qed.

  Theorem obsDSLP_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    intro r.
    exact (PureObs.obsDSLP_bind (runReaderT x r) (fun a => runReaderT (f a) r)).
  Qed.

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : rddivnd R A)) (ret a).
  Proof. intro r. exact (PureObs.obsDSP_ret a). Qed.

  Theorem obsDSP_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    intro r.
    exact (PureObs.obsDSP_bind (runReaderT x r) (fun a => runReaderT (f a) r)).
  Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : rddivnd R A)) (ret a).
  Proof. intro r. exact (PureObs.obsASLP_ret a). Qed.

  Theorem obsASLP_bind {A B} (x : rddivnd R A) (f : A -> rddivnd R B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof.
    intro r.
    exact (PureObs.obsASLP_bind (runReaderT x r) (fun a => runReaderT (f a) r)).
  Qed.

  (** The degeneracy of DSP and ASLP holds environment by environment. *)

  Theorem obsDSP_is_obsASP {A} (m : rddivnd R A) (r : R) p (a : A) :
    getDSPRd (obsDSP m) r p a
    <-> getASPRd (obsASP m) r p a.
  Proof. exact (PureObs.obsDSP_is_obsASP (runReaderT m r) p a). Qed.

  Theorem obsASLP_is_obsDSLP {A} (m : rddivnd R A) (r : R) p (a : A) :
    getASLPRd (obsASLP m) r p a
    <-> getDSLPRd (obsDSLP m) r p a.
  Proof. exact (PureObs.obsASLP_is_obsDSLP (runReaderT m r) p a). Qed.

End RdObservations.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.

(* ==================================================================== *)
(** * Triples                                                            *)
(* ==================================================================== *)

(** The precondition may depend on the environment ([pre : R -> Prop]), and the
    triple is read pointwise: it must hold in every environment, at that
    environment's precondition.  This is the reader analogue of the pure
    triples, and it does NOT couple the environments — see the note in the file
    header on the alternative that does. *)

Inductive approxKind := | Under | Over.

Section RdTriples.

  Definition tripleASP {R A}
    (prog : rddivnd R A) (kind : approxKind)
    (pre : R -> Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall r a, getASPRd (obsASP prog) r (pre r) a -> post a
    | Under => forall r a, post a -> getASPRd (obsASP prog) r (pre r) a
    end.

  Definition tripleDSLP {R A}
    (prog : rddivnd R A) (kind : approxKind)
    (pre : R -> Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall r a, getDSLPRd (obsDSLP prog) r (pre r) a -> post a
    | Under => forall r a, post a -> getDSLPRd (obsDSLP prog) r (pre r) a
    end.

  Definition tripleDSP {R A}
    (prog : rddivnd R A) (kind : approxKind)
    (pre : R -> Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall r a, getDSPRd (obsDSP prog) r (pre r) a -> post a
    | Under => forall r a, post a -> getDSPRd (obsDSP prog) r (pre r) a
    end.

  Definition tripleASLP {R A}
    (prog : rddivnd R A) (kind : approxKind)
    (pre : R -> Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall r a, getASLPRd (obsASLP prog) r (pre r) a -> post a
    | Under => forall r a, post a -> getASLPRd (obsASLP prog) r (pre r) a
    end.

  (** Unfolded readings: the angelic triple quantifies over environments
      satisfying [pre], the demonic-liberal one over environments reaching the
      outcome. *)

  Theorem tripleASP_unfold {R A} (prog : rddivnd R A) pre (post : A -> Prop) :
    tripleASP prog Over pre post
    <-> (forall r a, pre r -> unOptionT (runReaderT prog r) (Some a) -> post a).
  Proof.
    unfold tripleASP. split.
    - intros H r a Hpre Hreach. exact (H r a (conj Hpre Hreach)).
    - intros H r a [Hpre Hreach]. exact (H r a Hpre Hreach).
  Qed.

  Theorem tripleDSLP_unfold {R A} (prog : rddivnd R A) pre (post : A -> Prop) :
    tripleDSLP prog Under pre post
    <-> (forall r a, post a -> unOptionT (runReaderT prog r) (Some a) -> pre r).
  Proof.
    unfold tripleDSLP. split.
    - intros H r a Hpost Hreach. exact (H r a Hpost Hreach).
    - intros H r a Hpost Hreach. exact (H r a Hpost Hreach).
  Qed.

  (** The degeneracy, transported to triples. *)

  Theorem tripleDSP_is_tripleASP {R A} (prog : rddivnd R A) kind pre (post : A -> Prop) :
    tripleDSP prog kind pre post <-> tripleASP prog kind pre post.
  Proof.
    destruct kind; cbn; split.
    - intros H r a Hp. exact (proj1 (obsDSP_is_obsASP R prog r (pre r) a) (H r a Hp)).
    - intros H r a Hp. exact (proj2 (obsDSP_is_obsASP R prog r (pre r) a) (H r a Hp)).
    - intros H r a Hx. exact (H r a (proj2 (obsDSP_is_obsASP R prog r (pre r) a) Hx)).
    - intros H r a Hx. exact (H r a (proj1 (obsDSP_is_obsASP R prog r (pre r) a) Hx)).
  Qed.

  Theorem tripleASLP_is_tripleDSLP {R A} (prog : rddivnd R A) kind pre (post : A -> Prop) :
    tripleASLP prog kind pre post <-> tripleDSLP prog kind pre post.
  Proof.
    destruct kind; cbn; split.
    - intros H r a Hp. exact (proj1 (obsASLP_is_obsDSLP R prog r (pre r) a) (H r a Hp)).
    - intros H r a Hp. exact (proj2 (obsASLP_is_obsDSLP R prog r (pre r) a) (H r a Hp)).
    - intros H r a Hx. exact (H r a (proj2 (obsASLP_is_obsDSLP R prog r (pre r) a) Hx)).
    - intros H r a Hx. exact (H r a (proj1 (obsASLP_is_obsDSLP R prog r (pre r) a) Hx)).
  Qed.

  (** A [divergeD]-only program satisfies every [Over] triple and only the
      trivial [Under] ones — the slice sees nothing, in any environment. *)

  Theorem tripleASP_divergeD_over {R A} pre (post : A -> Prop) :
    tripleASP (divergeD : rddivnd R A) Over pre post.
  Proof. intros r a Hc. destruct (obsASP_divergeD R r (pre r) a Hc). Qed.

  Theorem tripleDSLP_divergeD_over {R A} (r0 : R) pre (post : A -> Prop) :
    tripleDSLP (divergeD : rddivnd R A) Over pre post -> forall a, post a.
  Proof. intros H a. exact (H r0 a (obsDSLP_divergeD R r0 (pre r0) a)). Qed.

End RdTriples.

Arguments tripleASP {_} {_}.
Arguments tripleDSLP {_} {_}.
Arguments tripleDSP {_} {_}.
Arguments tripleASLP {_} {_}.

End RdPureObs.
