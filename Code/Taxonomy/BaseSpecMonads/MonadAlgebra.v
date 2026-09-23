(** * Monad algebras, and the WP observations they induce.

    A port of the [MAlg] / [MAlgOrdered] / [MAlgLift] layer of the Loom
    development (POPL'26), cut down to what the [WPure] family needs: the
    assertion language is fixed to [Prop], so [Cont Prop] is [WPure] and the
    "logic lift" [Prop ~> S -> Prop] is the [stateT] layer of [WSt].

    An ALGEBRA for a computation monad [M] is a map

      [mu : M Prop -> Prop]

    collapsing a monadic collection of assertions into one, subject to
    [mu (ret p) <-> p] and a bind congruence.  Loom's observation is that
    such a [mu] already IS an effect observation: it induces

      [obsA x post := mu (bind x (fun a => ret (post a)))]   : M A -> WPure A

    and the monad-morphism laws of [obsA] -- the [obs_ret] and [obs_bind]
    that this repository proves by hand for each observation -- are theorems
    about [mu], proved once here ([obsA_ret], [obsA_bind]).

    The transformer layer follows Loom's [MAlgLift]: an algebra for [M] lifts
    along [optionT] (two ways: [None] as [False] or as [True]) and along
    [stateT] (where the assertion language becomes [S -> Prop], i.e. the
    target becomes [WSt S]), and each lift carries the morphism laws with it.
    So an observation for a STACK is assembled from one algebra per layer,
    with no law re-proved. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.

(* ================================================================= *)
(** ** Algebras                                                       *)
(* ================================================================= *)

(** Loom states the ordered form ([MAlgOrdered]) and derives the equational
    one; at [Prop] the order is implication, and the equational form is the
    derived [mu_bind_iff] below -- so no propositional extensionality is
    needed anywhere in this file. *)

Class MAlg (M : Type -> Type) {MM : Monad M} {EM : Eq1 M} := {
  mu : M Prop -> Prop ;
  mu_proper : forall x y : M Prop, eq1 x y -> (mu x <-> mu y) ;
  mu_ret : forall p : Prop, mu (ret p) <-> p ;
  mu_bind : forall {A} (x : M A) (f g : A -> M Prop),
    (forall a, mu (f a) -> mu (g a)) -> mu (bind x f) -> mu (bind x g)
}.

Arguments mu {M} {MM} {EM} {_}.

Section AlgebraFacts.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M} {AM : MAlg M}.

  Lemma mu_bind_iff {A} (x : M A) (f g : A -> M Prop) :
    (forall a, mu (f a) <-> mu (g a)) ->
    (mu (bind x f) <-> mu (bind x g)).
  Proof.
    intro H. split.
    - apply mu_bind. intro a. apply H.
    - apply mu_bind. intro a. apply H.
  Qed.
End AlgebraFacts.

(* ================================================================= *)
(** ** The observation an algebra induces                             *)
(* ================================================================= *)

Section Observation.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {LM : @MonadLawsE M EM MM} {AM : MAlg M}.

  (** Monotonicity -- [WPure]'s carrier condition -- is itself an instance
      of the bind law, so the observation lands in [WPure] with no extra
      hypothesis on [M]. *)
  #[program] Definition obsA {A} (x : M A) : WPure A :=
    fun post => mu (bind x (fun a => ret (post a))).
  Next Obligation.
    intros p q Hpq. apply mu_bind. intro a.
    rewrite !mu_ret. apply Hpq.
  Qed.

  Lemma obsA_get {A} (x : M A) (post : A -> Prop) :
    getWPure (obsA x) post <-> mu (bind x (fun a => ret (post a))).
  Proof. reflexivity. Qed.

  (** The two morphism laws, once and for all. *)

  Theorem obsA_ret {A} (a : A) : eq1 (obsA (ret a)) (ret a).
  Proof.
    intro post. rewrite obsA_get. cbn [getWPure retWPure].
    rewrite (mu_proper _ (ret (post a))); [ apply mu_ret |].
    apply (bind_ret_l A Prop (fun a0 => ret (post a0)) a).
  Qed.

  Theorem obsA_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsA (bind x f)) (bind (obsA x) (fun a => obsA (f a))).
  Proof.
    intro post. rewrite obsA_get. cbn [getWPure bindWPure].
    rewrite (mu_proper _ (bind x (fun a => bind (f a) (fun b => ret (post b)))));
      [| apply bind_bind ].
    apply mu_bind_iff. intro a. rewrite mu_ret. rewrite obsA_get. reflexivity.
  Qed.

End Observation.

Arguments obsA {M} {MM} {EM} {AM} {A}.

(* ================================================================= *)
(** ** Lifting an algebra along [optionT]                             *)
(* ================================================================= *)

(** The one choice the [option] layer offers is what [None] asserts.  Taking
    it to be [False] is the TOTAL reading (a [None] outcome breaks every
    specification), [True] the LIBERAL one (a [None] outcome is ignored).
    Both are algebras, so both induce observations with the laws already
    proved. *)

Section OptionAlgebra.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {EE : @Eq1Equivalence M MM EM}
          {LM : @MonadLawsE M EM MM} {AM : MAlg M}.

  Variable none : Prop.

  Definition mu_optionT (x : optionT M Prop) : Prop :=
    mu (bind (unOptionT x) (fun o => ret (match o with Some p => p | None => none end))).

  Lemma mu_optionT_proper (x y : optionT M Prop) :
    eq1 x y -> (mu_optionT x <-> mu_optionT y).
  Proof.
    intro H. unfold mu_optionT. apply mu_proper.
    apply Proper_bind; [ exact H | intro o; reflexivity ].
  Qed.

  Lemma mu_optionT_ret (p : Prop) : mu_optionT (ret p) <-> p.
  Proof.
    unfold mu_optionT. cbn [ret Monad_optionT unOptionT].
    rewrite (mu_proper _ (ret p)); [ apply mu_ret |].
    apply (bind_ret_l (option Prop) Prop
             (fun o => ret (match o with Some q => q | None => none end))
             (Some p)).
  Qed.

  (** [bind] on [optionT], with the [None] branch already collapsed to
      [none]: the [Some] branch is literally [mu_optionT] of the
      continuation, which is what makes the bind law immediate. *)
  Lemma mu_optionT_unfold {A} (x : optionT M A) (f : A -> optionT M Prop) :
    mu_optionT (bind x f)
    <-> mu (bind (unOptionT x)
              (fun o => match o with
                        | Some a =>
                            bind (unOptionT (f a))
                              (fun o' => ret (match o' with
                                              | Some p => p
                                              | None => none end))
                        | None => ret none
                        end)).
  Proof.
    unfold mu_optionT. cbn [bind Monad_optionT unOptionT].
    apply mu_proper. etransitivity; [ apply bind_bind |].
    apply Proper_bind; [ reflexivity | intros [a|] ].
    - reflexivity.
    - apply (bind_ret_l (option Prop) Prop
               (fun o' => ret (match o' with Some p => p | None => none end))
               None).
  Qed.

  Lemma mu_optionT_bind {A} (x : optionT M A) (f g : A -> optionT M Prop) :
    (forall a, mu_optionT (f a) -> mu_optionT (g a)) ->
    mu_optionT (bind x f) -> mu_optionT (bind x g).
  Proof.
    intro Hfg. rewrite !mu_optionT_unfold.
    apply mu_bind. intros [a|].
    - exact (Hfg a).
    - intro H. exact H.
  Qed.

  #[global] Instance MAlg_optionT : MAlg (optionT M) := {
    mu := mu_optionT ;
    mu_proper := mu_optionT_proper ;
    mu_ret := mu_optionT_ret ;
    mu_bind := @mu_optionT_bind
  }.

End OptionAlgebra.

Arguments mu_optionT {M} {MM} {EM} {AM} none x.
Arguments MAlg_optionT {M} {MM} {EM} {EE} {LM} {AM} none.

(* ================================================================= *)
(** ** Lifting along [stateT]: the observation lands in [WSt]         *)
(* ================================================================= *)

(** This is Loom's [MAlgLift.mk_rep]: the assertion language becomes
    [S -> Prop], which on the [WPure] side is exactly the [stateT] layer of
    [WSt].  The observation is [obsA] at each initial state, and the two
    morphism laws are the base ones, threaded through [runStateT]. *)

Section StateObservation.
  Context {M : Type -> Type} {MM : Monad M} {EM : Eq1 M}
          {LM : @MonadLawsE M EM MM} {AM : MAlg M}.

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
  (LM : @MonadLawsE M EM MM) (AM : MAlg M) : MMor M WPure :=
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
