(** * Monad algebras, and the observations they induce.

    A port of the [MAlg] / [MAlgOrdered] / [MAlgLift] layer of the Loom
    development (POPL'26).

    An ALGEBRA for a computation monad [M] and an ASSERTION LANGUAGE [L] is
    a map

      [mu : M L -> L]

    collapsing a monadic collection of assertions into one, subject to
    [mu (ret p) = p] and a monotone bind congruence (Loom, Definitions 3.1
    and 3.2).  Loom's observation is that such a [mu] already IS an effect
    observation: it induces

      [WPof x post := mu (bind x (fun a => ret (post a)))]

    and the three properties one would otherwise prove per observation --
    the two monad-morphism laws AND monotonicity -- are theorems about [mu],
    proved once ([WPof_ret], [WPof_bind], [WPof_mono]; Loom, Theorem 3.3).

    The assertion language is a PARAMETER, which is what makes the
    transformer layer work (Loom, Sec. 3.4).  Each transformer says what it
    does to [L]:

      [stateT S]  : [L] becomes [S -> L]   (Loom eq. 14)
      [readerT R] : [L] becomes [R -> L]
      [optionT]   : [L] unchanged, with a parameter saying what an
                    uncaught [None] asserts (Loom's [MAlgExcept ε df])

    so an observation for a STACK is assembled from one algebra per layer,
    with no law re-proved.

    Differences from Loom, deliberate: Loom asks the assertion language to
    be a [CompleteLattice]; the algebra laws need only a preorder, so that
    is all [AsnLang] requires.  Loom states the ordered form and derives the
    equational one; here the ordered form is primitive and [aeq] is the
    derived equality, so no propositional extensionality is used.

    At [L = Prop] the specification monad is [WPure], and the [Prop] layer
    below ([obsA] and friends) is the specialisation the rest of this
    repository consumes. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.

Class AsnLang (L : Type) := {
  aleq : L -> L -> Prop ;
  aleq_refl : forall p, aleq p p ;
  aleq_trans : forall p q r, aleq p q -> aleq q r -> aleq p r
}.

#[global] Instance aleq_Reflexive {L} `{AsnLang L} : Reflexive aleq := aleq_refl.
#[global] Instance aleq_Transitive {L} `{AsnLang L} : Transitive aleq := aleq_trans.

Definition aeq {L} `{AsnLang L} (p q : L) : Prop := aleq p q /\ aleq q p.

#[global] Instance aeq_Reflexive {L} `{AsnLang L} : Reflexive aeq.
Proof. intro p. split; apply aleq_refl. Qed.
#[global] Instance aeq_Symmetric {L} `{AsnLang L} : Symmetric aeq.
Proof. intros p q [H1 H2]. split; assumption. Qed.
#[global] Instance aeq_Transitive {L} `{AsnLang L} : Transitive aeq.
Proof.
  intros p q r [H1 H2] [H3 H4].
  split; [ exact (aleq_trans _ _ _ H1 H3) | exact (aleq_trans _ _ _ H4 H2) ].
Qed.

#[global] Instance AsnLang_Prop : AsnLang Prop := {|
  aleq p q := p -> q ;
  aleq_refl := fun _ x => x ;
  aleq_trans := fun _ _ _ H1 H2 x => H2 (H1 x)
|}.

Definition AsnLang_fun (S : Type) {L : Type} (AL : AsnLang L) : AsnLang (S -> L) := {|
  aleq f g := forall s, aleq (f s) (g s) ;
  aleq_refl := fun f s => aleq_refl (f s) ;
  aleq_trans := fun f g h H1 H2 s => aleq_trans _ _ _ (H1 s) (H2 s)
|}.

Class MAlg (M : Type -> Type) (L : Type)
  {MM : Monad M} {EM : Eq1 M} {AL : AsnLang L} := {
  mu : M L -> L ;
  mu_proper : forall x y : M L, eq1 x y -> aeq (mu x) (mu y) ;
  mu_ret : forall p : L, aeq (mu (ret p)) p ;
  mu_bind : forall {A} (x : M A) (f g : A -> M L),
    (forall a, aleq (mu (f a)) (mu (g a))) -> aleq (mu (bind x f)) (mu (bind x g))
}.

Arguments mu {M} {L} {MM} {EM} {AL} {_}.

Section StateAlgebra.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {EE : @Eq1Equivalence M MM EM} {LM : @MonadLawsE M EM MM}
          {L : Type} {AL : AsnLang L} {AM : @MAlg M L MM EM AL}.
  Variable S : Type.

  #[local] Existing Instance Monad_stateT.

  (** Loom, eq. (14): [mu_StateT m = fun s => mu_M (apply <$> m s)]. *)
  Definition mu_stateT (x : stateT S M (S -> L)) : S -> L :=
    fun s => mu (bind (runStateT x s) (fun p => ret (fst p (snd p)))).

  #[local] Notation kap := (fun p : (S -> L) * S => ret (fst p (snd p))).

  Lemma mu_stateT_step {A} (h : A -> stateT S M (S -> L)) (x : stateT S M A) s :
    eq1 (bind (runStateT (bind x h) s) kap)
        (bind (runStateT x s)
           (fun p : A * S => bind (runStateT (h (fst p)) (snd p)) kap)).
  Proof.
    cbn [bind Monad_stateT runStateT].
    etransitivity; [ apply bind_bind |].
    apply Proper_bind; [ reflexivity | intros [a s']; reflexivity ].
  Qed.

  Lemma mu_stateT_proper (x y : stateT S M (S -> L)) :
    (forall s, eq1 (runStateT x s) (runStateT y s)) ->
    (forall s, aleq (mu_stateT x s) (mu_stateT y s))
    /\ (forall s, aleq (mu_stateT y s) (mu_stateT x s)).
  Proof.
    intro H.
    assert (Hs : forall s, aeq (mu_stateT x s) (mu_stateT y s)).
    { intro s. unfold mu_stateT. apply mu_proper.
      apply Proper_bind; [ exact (H s) | intro p; reflexivity ]. }
    split; intro s; [ exact (proj1 (Hs s)) | exact (proj2 (Hs s)) ].
  Qed.

  Lemma mu_stateT_ret (f : S -> L) :
    (forall s, aleq (mu_stateT (ret f) s) (f s))
    /\ (forall s, aleq (f s) (mu_stateT (ret f) s)).
  Proof.
    assert (Hs : forall s, aeq (mu_stateT (ret f) s) (f s)).
    { intro s. unfold mu_stateT.
      assert (He : eq1 (bind (runStateT (ret f : stateT S M (S -> L)) s) kap) (ret (f s))).
      { cbn [ret Monad_stateT runStateT].
        apply (bind_ret_l ((S -> L) * S) L (fun p => ret (fst p (snd p))) (f, s)). }
      destruct (mu_proper _ _ He) as [H1 H2].
      destruct (mu_ret (f s)) as [H3 H4].
      split; [ exact (aleq_trans _ _ _ H1 H3) | exact (aleq_trans _ _ _ H4 H2) ]. }
    split; intro s; [ exact (proj1 (Hs s)) | exact (proj2 (Hs s)) ].
  Qed.

  Lemma mu_stateT_bind {A} (x : stateT S M A) (f g : A -> stateT S M (S -> L)) :
    (forall a s, aleq (mu_stateT (f a) s) (mu_stateT (g a) s)) ->
    forall s, aleq (mu_stateT (bind x f) s) (mu_stateT (bind x g) s).
  Proof.
    intros Hfg s. unfold mu_stateT.
    transitivity (mu (bind (runStateT x s)
                       (fun p : A * S => bind (runStateT (f (fst p)) (snd p)) kap))).
    { exact (proj1 (mu_proper _ _ (mu_stateT_step f x s))). }
    transitivity (mu (bind (runStateT x s)
                       (fun p : A * S => bind (runStateT (g (fst p)) (snd p)) kap))).
    { apply mu_bind. intros [a s']. exact (Hfg a s'). }
    exact (proj2 (mu_proper _ _ (mu_stateT_step g x s))).
  Qed.

  Definition MAlg_stateT
    : @MAlg (stateT S M) (S -> L) (Monad_stateT S MM) (Eq1_stateT S M)
        (AsnLang_fun S AL).
  Proof.
    refine {| mu := mu_stateT |}.
    - exact mu_stateT_proper.
    - exact mu_stateT_ret.
    - exact (@mu_stateT_bind).
  Defined.

End StateAlgebra.

(* ---- Loom Theorem 3.3: the WP an algebra induces, and its properties ---- *)

Section Observation.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {EE : @Eq1Equivalence M MM EM} {LM : @MonadLawsE M EM MM}
          {L : Type} {AL : AsnLang L} {AM : @MAlg M L MM EM AL}.

  Definition WPof {A} (x : M A) (post : A -> L) : L :=
    mu (bind x (fun a => ret (post a))).

  Lemma mu_bind_aeq {A} (x : M A) (f g : A -> M L) :
    (forall a, aeq (mu (f a)) (mu (g a))) -> aeq (mu (bind x f)) (mu (bind x g)).
  Proof.
    intro H. split; apply mu_bind; intro a;
      [ exact (proj1 (H a)) | exact (proj2 (H a)) ].
  Qed.

  Theorem WPof_ret {A} (a : A) (post : A -> L) : aeq (WPof (ret a) post) (post a).
  Proof.
    unfold WPof.
    destruct (mu_proper _ (ret (post a))
                (bind_ret_l A L (fun a0 => ret (post a0)) a)) as [H1 H2].
    destruct (mu_ret (post a)) as [H3 H4].
    split; [ exact (aleq_trans _ _ _ H1 H3) | exact (aleq_trans _ _ _ H4 H2) ].
  Qed.

  Theorem WPof_mono {A} (x : M A) (post post' : A -> L) :
    (forall a, aleq (post a) (post' a)) -> aleq (WPof x post) (WPof x post').
  Proof.
    intro H. unfold WPof. apply mu_bind. intro a.
    destruct (mu_ret (post a)) as [H1 _]. destruct (mu_ret (post' a)) as [_ H2].
    exact (aleq_trans _ _ _ H1 (aleq_trans _ _ _ (H a) H2)).
  Qed.

  Theorem WPof_bind {A B} (x : M A) (f : A -> M B) (post : B -> L) :
    aeq (WPof (bind x f) post) (WPof x (fun a => WPof (f a) post)).
  Proof.
    unfold WPof.
    assert (Hb : aeq (mu (bind (bind x f) (fun b => ret (post b))))
                     (mu (bind x (fun a => bind (f a) (fun b => ret (post b)))))).
    { apply mu_proper. apply bind_bind. }
    assert (Hc : aeq (mu (bind x (fun a => bind (f a) (fun b => ret (post b)))))
                     (mu (bind x (fun a => ret (mu (bind (f a) (fun b => ret (post b)))))))).
    { apply mu_bind_aeq. intro a.
      destruct (mu_ret (mu (bind (f a) (fun b => ret (post b))))) as [H1 H2].
      split; [ exact H2 | exact H1 ]. }
    split.
    - exact (aleq_trans _ _ _ (proj1 Hb) (proj1 Hc)).
    - exact (aleq_trans _ _ _ (proj2 Hc) (proj2 Hb)).
  Qed.

End Observation.

(* ---- the algebra transformer for readerT: L becomes R -> L ---- *)

Section ReaderAlgebra.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {EE : @Eq1Equivalence M MM EM} {LM : @MonadLawsE M EM MM}
          {L : Type} {AL : AsnLang L} {AM : @MAlg M L MM EM AL}.
  Variable R : Type.

  #[local] Existing Instance Monad_readerT.

  Definition mu_readerT (x : readerT R M (R -> L)) : R -> L :=
    fun r => mu (bind (runReaderT x r) (fun f => ret (f r))).

  Lemma mu_readerT_proper (x y : readerT R M (R -> L)) :
    (forall r, eq1 (runReaderT x r) (runReaderT y r)) ->
    (forall r, aleq (mu_readerT x r) (mu_readerT y r))
    /\ (forall r, aleq (mu_readerT y r) (mu_readerT x r)).
  Proof.
    intro H.
    assert (Hs : forall r, aeq (mu_readerT x r) (mu_readerT y r)).
    { intro r. unfold mu_readerT. apply mu_proper.
      apply Proper_bind; [ exact (H r) | intro f; reflexivity ]. }
    split; intro r; [ exact (proj1 (Hs r)) | exact (proj2 (Hs r)) ].
  Qed.

  Lemma mu_readerT_ret (f : R -> L) :
    (forall r, aleq (mu_readerT (ret f) r) (f r))
    /\ (forall r, aleq (f r) (mu_readerT (ret f) r)).
  Proof.
    assert (Hs : forall r, aeq (mu_readerT (ret f) r) (f r)).
    { intro r. unfold mu_readerT.
      destruct (mu_proper (bind (runReaderT (ret f : readerT R M (R -> L)) r)
                             (fun h => ret (h r))) (ret (f r))) as [H1 H2].
      { cbn [ret Monad_readerT runReaderT].
        apply (bind_ret_l (R -> L) L (fun h => ret (h r)) f). }
      destruct (mu_ret (f r)) as [H3 H4].
      split; [ exact (aleq_trans _ _ _ H1 H3) | exact (aleq_trans _ _ _ H4 H2) ]. }
    split; intro r; [ exact (proj1 (Hs r)) | exact (proj2 (Hs r)) ].
  Qed.

  Lemma mu_readerT_bind {A} (x : readerT R M A) (f g : A -> readerT R M (R -> L)) :
    (forall a r, aleq (mu_readerT (f a) r) (mu_readerT (g a) r)) ->
    forall r, aleq (mu_readerT (bind x f) r) (mu_readerT (bind x g) r).
  Proof.
    intros Hfg r. unfold mu_readerT.
    assert (Hstep : forall (h : A -> readerT R M (R -> L)),
               eq1 (bind (runReaderT (bind x h) r) (fun k => ret (k r)))
                   (bind (runReaderT x r)
                      (fun a => bind (runReaderT (h a) r) (fun k => ret (k r))))).
    { intro h. cbn [bind Monad_readerT runReaderT]. apply bind_bind. }
    transitivity (mu (bind (runReaderT x r)
                        (fun a => bind (runReaderT (f a) r) (fun k => ret (k r))))).
    { exact (proj1 (mu_proper _ _ (Hstep f))). }
    transitivity (mu (bind (runReaderT x r)
                        (fun a => bind (runReaderT (g a) r) (fun k => ret (k r))))).
    { apply mu_bind. intro a. exact (Hfg a r). }
    exact (proj2 (mu_proper _ _ (Hstep g))).
  Qed.

  Definition MAlg_readerT
    : @MAlg (readerT R M) (R -> L) (Monad_readerT R MM) (Eq1_readerT R M)
        (AsnLang_fun R AL).
  Proof.
    refine {| mu := mu_readerT |}.
    - exact mu_readerT_proper.
    - exact mu_readerT_ret.
    - exact (@mu_readerT_bind).
  Defined.

End ReaderAlgebra.

(* ---- the algebra transformer for optionT: L unchanged, handler [none] ---- *)
(* Loom's [MAlgExcept ε df]: the assertion language does NOT change, and the
   parameter says what an uncaught exception asserts. *)

Section OptionAlgebra.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {EE : @Eq1Equivalence M MM EM} {LM : @MonadLawsE M EM MM}
          {L : Type} {AL : AsnLang L} {AM : @MAlg M L MM EM AL}.
  Variable none : L.

  #[local] Existing Instance Monad_optionT.

  Definition mu_optionT (x : optionT M L) : L :=
    mu (bind (unOptionT x)
          (fun o => ret (match o with Some p => p | None => none end))).

  Lemma mu_optionT_proper (x y : optionT M L) :
    eq1 x y -> aeq (mu_optionT x) (mu_optionT y).
  Proof.
    intro H. unfold mu_optionT. apply mu_proper.
    apply Proper_bind; [ exact H | intro o; reflexivity ].
  Qed.

  Lemma mu_optionT_ret (p : L) : aeq (mu_optionT (ret p)) p.
  Proof.
    unfold mu_optionT. cbn [ret Monad_optionT unOptionT].
    destruct (mu_proper (bind (ret (Some p))
                           (fun o => ret (match o with Some q => q | None => none end)))
                        (ret p)) as [H1 H2].
    { apply (bind_ret_l (option L) L
               (fun o => ret (match o with Some q => q | None => none end)) (Some p)). }
    destruct (mu_ret p) as [H3 H4].
    split; [ exact (aleq_trans _ _ _ H1 H3) | exact (aleq_trans _ _ _ H4 H2) ].
  Qed.

  Lemma mu_optionT_unfold {A} (x : optionT M A) (f : A -> optionT M L) :
    aeq (mu_optionT (bind x f))
        (mu (bind (unOptionT x)
               (fun o => match o with
                         | Some a =>
                             bind (unOptionT (f a))
                               (fun o' => ret (match o' with Some p => p | None => none end))
                         | None => ret none
                         end))).
  Proof.
    unfold mu_optionT. cbn [bind Monad_optionT unOptionT].
    apply mu_proper. etransitivity; [ apply bind_bind |].
    apply Proper_bind; [ reflexivity | intros [a|] ].
    - reflexivity.
    - apply (bind_ret_l (option L) L
               (fun o' => ret (match o' with Some p => p | None => none end)) None).
  Qed.

  Lemma mu_optionT_bind {A} (x : optionT M A) (f g : A -> optionT M L) :
    (forall a, aleq (mu_optionT (f a)) (mu_optionT (g a))) ->
    aleq (mu_optionT (bind x f)) (mu_optionT (bind x g)).
  Proof.
    intro Hfg.
    transitivity (mu (bind (unOptionT x)
                       (fun o => match o with
                                 | Some a => bind (unOptionT (f a))
                                     (fun o' => ret (match o' with Some p => p | None => none end))
                                 | None => ret none end))).
    { exact (proj1 (mu_optionT_unfold x f)). }
    transitivity (mu (bind (unOptionT x)
                       (fun o => match o with
                                 | Some a => bind (unOptionT (g a))
                                     (fun o' => ret (match o' with Some p => p | None => none end))
                                 | None => ret none end))).
    { apply mu_bind. intros [a|]; [ exact (Hfg a) | reflexivity ]. }
    exact (proj2 (mu_optionT_unfold x g)).
  Qed.

  Definition MAlg_optionT : MAlg (optionT M) L :=
    {| mu := mu_optionT ;
       mu_proper := mu_optionT_proper ;
       mu_ret := mu_optionT_ret ;
       mu_bind := @mu_optionT_bind |}.

End OptionAlgebra.

(* ================================================================= *)
(** ** The [Prop] layer: observations into [WPure]                    *)
(* ================================================================= *)

(** At [L = Prop] the assertion order is implication, [aeq] is [iff], and
    [Cont Prop] cut down by monotonicity is [WPure].  Monotonicity is
    [WPof_mono], so the observation lands in [WPure] with no extra
    hypothesis on [M] -- this is what the rest of the repository uses. *)

Section PropObservation.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {EE : @Eq1Equivalence M MM EM} {LM : @MonadLawsE M EM MM}
          {AM : @MAlg M Prop MM EM AsnLang_Prop}.

  #[program] Definition obsA {A} (x : M A) : WPure A :=
    fun post => WPof x post.
  Next Obligation.
    intros p q Hpq. exact (WPof_mono x p q Hpq).
  Qed.

  Lemma obsA_get {A} (x : M A) (post : A -> Prop) :
    getWPure (obsA x) post <-> WPof x post.
  Proof. reflexivity. Qed.

  Theorem obsA_ret {A} (a : A) : eq1 (obsA (ret a : M A)) (ret a).
  Proof. intro post. exact (WPof_ret a post). Qed.

  Theorem obsA_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsA (bind x f)) (bind (obsA x) (fun a => obsA (f a))).
  Proof. intro post. exact (WPof_bind x f post). Qed.

End PropObservation.

Arguments obsA {M} {MM} {EM} {AM} {A}.

(* ================================================================= *)
(** ** Lifting along [stateT]: the observation lands in [WSt]         *)
(* ================================================================= *)

(** This is Loom's [MAlgLift.mk_rep]: the assertion language becomes
    [S -> Prop], which on the [WPure] side is exactly the [stateT] layer of
    [WSt].  The observation is [obsA] at each initial state, and the two
    morphism laws are the base ones, threaded through [runStateT]. *)

Section StateObservation.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {LM : @MonadLawsE M EM MM} {AM : @MAlg M Prop MM EM AsnLang_Prop}.

  Variable S : Type.

  #[local] Existing Instance Monad_stateT.

  Definition obsASt {A} (x : stateT S M A) : WSt S A :=
    mkStateT (fun s => obsA (runStateT x s)).

  Lemma obsASt_get {A} (x : stateT S M A) (s : S) (post : A * S -> Prop) :
    getWPure (runStateT (obsASt x) s) post
    <-> mu (bind (runStateT x s) (fun p => ret (post p))).
  Proof. reflexivity. Qed.

  Theorem obsASt_ret {A} (a : A) : eq1 (obsASt (ret a)) (ret a).
  Proof.
    intros s post. cbn [runStateT obsASt].
    exact (obsA_ret (a, s) post).
  Qed.

  Theorem obsASt_bind {A B} (x : stateT S M A) (f : A -> stateT S M B) :
    eq1 (obsASt (bind x f)) (bind (obsASt x) (fun a => obsASt (f a))).
  Proof.
    (* [stateT]'s bind on both sides is the same reassociation, so this IS
       the base law at the initial state; the [Proper_bind] step only
       commutes [obsA] with the pair pattern ExtLib's [bind] introduces. *)
    intro s. unfold obsASt.
    cbn [runStateT bind Monad__WSt bindPs Monad_stateT].
    etransitivity.
    - apply (obsA_bind (runStateT x s)
               (fun vs : A * S => let (v, s0) := vs in runStateT (f v) s0)).
    - apply Proper_bind; [ reflexivity | intros [v s0]; reflexivity ].
  Qed.

End StateObservation.

Arguments obsASt {M} {MM} {EM} {AM} {S} {A}.

(* ================================================================= *)
(** ** Preserving a layer instead of collapsing it                    *)
(* ================================================================= *)

(** [MAlg_optionT] COLLAPSES its layer: [None] becomes an assertion and
    the layer disappears.  That is right when [None] means DIVERGENCE,
    which a specification need not name.  When it means an EXCEPTION the
    specification must still talk about it, so the layer has to be carried
    over to the spec side instead -- the difference between landing in
    [WSt S] and in [WStExc S].

    Carrying a layer over is functoriality: a monad morphism lifts through
    [optionT] and through [stateT].  [obsA] is a monad morphism
    ([obsA_ret], [obsA_bind]), so an observation for a stack is assembled
    layer by layer, each layer either COLLAPSED by an algebra or PRESERVED
    by a lift, with no law re-proved either way.

    [MMor] is deliberately not an [Instance] anywhere: the lifts are
    recursive in the shape [MMor M W -> MMor (T M) (T W)], which is the
    pattern that sends typeclass search exponential (see the root
    CLAUDE.md).  They are applied by hand. *)

Class MMor (M W : Type -> Type) {MM : Monad M} {MW : Monad W} {EW : Eq1 W} := {
  mmor : forall {A}, M A -> W A ;
  mmor_ret : forall A (a : A), eq1 (mmor (ret a)) (ret a) ;
  mmor_bind : forall A B (x : M A) (f : A -> M B),
    eq1 (mmor (bind x f)) (bind (mmor x) (fun a => mmor (f a)))
}.

Arguments mmor {M W MM MW EW} _ {A}.

(** An algebra is the morphism that collapses everything below it. *)
Definition MMor_of_MAlg {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
  (LM : @MonadLawsE M EM MM) (AM : @MAlg M Prop MM EM AsnLang_Prop) : MMor M WPure :=
  {| mmor A := @obsA M MM EM AM A ;
     mmor_ret := @obsA_ret M MM EM LM AM ;
     mmor_bind := @obsA_bind M MM EM LM AM |}.

Section LiftOption.
  Context {M W : Type -> Type} {MM : Monad M} {MW : Monad W} {EW : Eq1 W}.
  Context {EEW : @Eq1Equivalence W MW EW} {LW : @MonadLawsE W EW MW}.
  Variable phi : MMor M W.

  #[local] Existing Instance Eq1_optionT.

  Definition mmorOpt {A} (x : optionT M A) : optionT W A :=
    mkOptionT (mmor phi (unOptionT x)).

  Theorem mmorOpt_ret {A} (a : A) : eq1 (mmorOpt (ret a)) (ret a).
  Proof. exact (mmor_ret _ (Some a)). Qed.

  Theorem mmorOpt_bind {A B} (x : optionT M A) (f : A -> optionT M B) :
    eq1 (mmorOpt (bind x f)) (bind (mmorOpt x) (fun a => mmorOpt (f a))).
  Proof.
    unfold eq1, Eq1_optionT, mmorOpt.
    cbn [bind Monad_optionT unOptionT].
    etransitivity; [ apply mmor_bind |].
    apply Proper_bind; [ reflexivity |].
    intros [a|]; [ reflexivity | exact (mmor_ret _ (@None B)) ].
  Qed.

  Definition MMor_optionT : MMor (optionT M) (optionT W) :=
    {| mmor A := @mmorOpt A ;
       mmor_ret := @mmorOpt_ret ; mmor_bind := @mmorOpt_bind |}.

End LiftOption.

Section LiftState.
  Context {M W : Type -> Type} {MM : Monad M} {MW : Monad W} {EW : Eq1 W}.
  Context {EEW : @Eq1Equivalence W MW EW} {LW : @MonadLawsE W EW MW}.
  Variable S : Type.
  Variable phi : MMor M W.

  #[local] Existing Instance Eq1_stateT.
  #[local] Existing Instance Monad_stateT.

  Definition mmorSt {A} (x : stateT S M A) : stateT S W A :=
    mkStateT (fun s => mmor phi (runStateT x s)).

  Theorem mmorSt_ret {A} (a : A) : eq1 (mmorSt (ret a)) (ret a).
  Proof. intro s. exact (mmor_ret _ (a, s)). Qed.

  Theorem mmorSt_bind {A B} (x : stateT S M A) (f : A -> stateT S M B) :
    eq1 (mmorSt (bind x f)) (bind (mmorSt x) (fun a => mmorSt (f a))).
  Proof.
    intro s. unfold mmorSt. cbn [runStateT bind Monad_stateT].
    etransitivity; [ apply mmor_bind |].
    apply Proper_bind; [ reflexivity | intros [v s0]; reflexivity ].
  Qed.

  Definition MMor_stateT : MMor (stateT S M) (stateT S W) :=
    {| mmor A := @mmorSt A ;
       mmor_ret := @mmorSt_ret ; mmor_bind := @mmorSt_bind |}.

End LiftState.

Section LiftReader.
  Context {M W : Type -> Type} {MM : Monad M} {MW : Monad W} {EW : Eq1 W}.
  Context {EEW : @Eq1Equivalence W MW EW} {LW : @MonadLawsE W EW MW}.
  Variable R : Type.
  Variable phi : MMor M W.

  #[local] Existing Instance Eq1_readerT.
  #[local] Existing Instance Monad_readerT.

  (** A read-only environment is threaded, never collapsed: there is no
      algebra to choose, so a reader layer adds no observations. *)
  Definition mmorRd {A} (x : readerT R M A) : readerT R W A :=
    mkReaderT (fun r => mmor phi (runReaderT x r)).

  Theorem mmorRd_ret {A} (a : A) : eq1 (mmorRd (ret a)) (ret a).
  Proof. intro r. exact (mmor_ret _ a). Qed.

  Theorem mmorRd_bind {A B} (x : readerT R M A) (f : A -> readerT R M B) :
    eq1 (mmorRd (bind x f)) (bind (mmorRd x) (fun a => mmorRd (f a))).
  Proof.
    intro r. unfold mmorRd. cbn [runReaderT bind Monad_readerT].
    etransitivity; [ apply mmor_bind |].
    apply Proper_bind; [ reflexivity | intro a; reflexivity ].
  Qed.

  Definition MMor_readerT : MMor (readerT R M) (readerT R W) :=
    {| mmor A := @mmorRd A ;
       mmor_ret := @mmorRd_ret ; mmor_bind := @mmorRd_bind |}.

End LiftReader.
