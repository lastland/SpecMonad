(** * The four SP observations of [(optionT SetM)], assembled from its denotation.

    The stateless case of [StDivNonDet_SPSt_Rel.v].  With no state there
    is nothing to relate FROM, so a computation denotes a PREDICATE on
    outcomes ([prel], with its [ret] and [bind] laws in
    [BaseSpecMonads/SPRelDenote.v]) and the four readings are taken
    against a [Prop] precondition:

      [aspOfPred]  : the precondition holds AND the outcome is possible;
      [dslpOfPred] : the outcome being possible forces the precondition;
      [dspOfPred]  : both;   [aslpOfPred] : either.

    [DivNonDet_SPPure.v] writes the four out and proves [_ret] and [_bind]
    for each.  Here the instance below is the only input and all eight are
    citations.

    The outcome space is the TERMINATING SLICE [A]: there is no outcome
    denoting divergence, so none of the four can constrain it. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad SPRelDenote.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The denotation                                                 *)
(* ================================================================= *)

Section Outcomes.

  Lemma outcomes_ret {A} (a r : A) :
    unOptionT (ret a : (optionT SetM) A) (Some r) <-> r = a.
  Proof. cbn. split; intro H; congruence. Qed.

  (** One case only: the divergent branch cannot produce a [Some]. *)
  Lemma outcomes_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) (r : B) :
    unOptionT (x >>= f) (Some r)
    <-> (exists a, unOptionT x (Some a) /\ unOptionT (f a) (Some r)).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. destruct oy as [a|]; cbn in *.
      + exists a. split; [ exact H1 | exact H2 ].
      + congruence.
    - intros [a [H1 H2]]. exists (Some a). split; [ exact H1 | exact H2 ].
  Qed.

  Lemma outcomes_diverge {A} (r : A) :
    ~ unOptionT (divergeD : (optionT SetM) A) (Some r).
  Proof. cbn. intro H. congruence. Qed.

End Outcomes.

#[global] Instance PureRel_divnd : PureRel (optionT SetM) := {
  prel A m a := unOptionT m (Some a) ;
  prel_ret := @outcomes_ret ;
  prel_bind := @outcomes_bind
}.

(* ================================================================= *)
(** ** The four observations                                          *)
(* ================================================================= *)

Definition obsASP  {A} (m : (optionT SetM) A) : ASP  A := obsASPofP m.
Definition obsDSLP {A} (m : (optionT SetM) A) : DSLP A := obsDSLPofP m.
Definition obsDSP  {A} (m : (optionT SetM) A) : DSP  A := obsDSPofP m.
Definition obsASLP {A} (m : (optionT SetM) A) : ASLP A := obsASLPofP m.

(** ** What each reading says *)

Lemma getASP_obsASP {A} (m : (optionT SetM) A) p a :
  getASP (obsASP m) p a <-> (p /\ unOptionT m (Some a)).
Proof. exact (getASP_obsASPofP m p a). Qed.

Lemma getDSLP_obsDSLP {A} (m : (optionT SetM) A) p a :
  getDSLP (obsDSLP m) p a <-> (unOptionT m (Some a) -> p).
Proof. exact (getDSLP_obsDSLPofP m p a). Qed.

Lemma getDSP_obsDSP {A} (m : (optionT SetM) A) p a :
  getDSPPure (obsDSP m) p a
  <-> ((p /\ unOptionT m (Some a)) /\ (unOptionT m (Some a) -> p)).
Proof. exact (getDSPPure_obsDSPofP m p a). Qed.

Lemma getASLP_obsASLP {A} (m : (optionT SetM) A) p a :
  getASLPPure (obsASLP m) p a
  <-> ((p /\ unOptionT m (Some a)) \/ (unOptionT m (Some a) -> p)).
Proof. exact (getASLPPure_obsASLPofP m p a). Qed.

(** ** The morphism laws, for free *)

Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a)) (ret a).
Proof. exact (obsASPofP_ret a). Qed.
Theorem obsASP_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
Proof. exact (obsASPofP_bind x f). Qed.

Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a)) (ret a).
Proof. exact (obsDSLPofP_ret a). Qed.
Theorem obsDSLP_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
Proof. exact (obsDSLPofP_bind x f). Qed.

Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a)) (ret a).
Proof. exact (obsDSPofP_ret a). Qed.
Theorem obsDSP_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
Proof. exact (obsDSPofP_bind x f). Qed.

Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a)) (ret a).
Proof. exact (obsASLPofP_ret a). Qed.
Theorem obsASLP_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
Proof. exact (obsASLPofP_bind x f). Qed.

(** ** The slice is blind to divergence *)

Lemma obsASP_divergeD {A} (p : Prop) (a : A) :
  ~ getASP (obsASP divergeD) p a.
Proof. rewrite getASP_obsASP. intros [_ Hr]. exact (outcomes_diverge a Hr). Qed.

Lemma obsDSLP_divergeD {A} (p : Prop) (a : A) :
  getDSLP (obsDSLP divergeD) p a.
Proof. apply getDSLP_obsDSLP. intro Hr. destruct (outcomes_diverge a Hr). Qed.

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
    (prog : (optionT SetM) A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall a, getASP (obsASP prog) pre a -> post a
    | Under => forall a, post a -> getASP (obsASP prog) pre a
    end.

  Definition tripleDSLP {A}
    (prog : (optionT SetM) A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => forall a, getDSLP (obsDSLP prog) pre a -> post a
    | Under => forall a, post a -> getDSLP (obsDSLP prog) pre a
    end.

  Definition tripleASPspec {A} (prog : (optionT SetM) A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => ordSPPure (getASP (obsASP prog)) (pp2_over pre post)
    | Under => ordSPPure (pp2_under pre post) (getASP (obsASP prog))
    end.

  Definition tripleDSLPspec {A} (prog : (optionT SetM) A) (kind : approxKind)
    (pre : Prop) (post : A -> Prop) : Prop :=
    match kind with
    | Over  => ordSPPure (getDSLP (obsDSLP prog)) (pp2_over pre post)
    | Under => ordSPPure (pp2_under pre post) (getDSLP (obsDSLP prog))
    end.

  Theorem tripleASPDefEq {A} (prog : (optionT SetM) A) kind pre post :
    tripleASP prog kind pre post <-> tripleASPspec prog kind pre post.
  Proof.
    unfold tripleASP, tripleASPspec, ordSPPure, pp2_over, pp2_under.
    destruct kind; split.
    - intros H p a [Hsub Hpost].
      destruct (proj1 (getASP_obsASP prog pre a) (H a Hpost)) as [Hpre Hreach].
      apply getASP_obsASP. split; [ exact (Hsub Hpre) | exact Hreach ].
    - intros H a Hpost. exact (H pre a (conj (fun Hs => Hs) Hpost)).
    - intros H p a Hobs Hsub.
      destruct (proj1 (getASP_obsASP prog p a) Hobs) as [Hp Hreach].
      apply (H a). apply getASP_obsASP. split; [ exact (Hsub Hp) | exact Hreach ].
    - intros H a Hobs. exact (H pre a Hobs (fun Hs => Hs)).
  Qed.

  Theorem tripleDSLPDefEq {A} (prog : (optionT SetM) A) kind pre post :
    tripleDSLP prog kind pre post <-> tripleDSLPspec prog kind pre post.
  Proof.
    unfold tripleDSLP, tripleDSLPspec, ordSPPure, pp2_over, pp2_under.
    destruct kind; split.
    - intros H p a [Hsub Hpost]. apply getDSLP_obsDSLP. intro Hout.
      exact (Hsub (proj1 (getDSLP_obsDSLP prog pre a) (H a Hpost) Hout)).
    - intros H a Hpost. exact (H pre a (conj (fun Hs => Hs) Hpost)).
    - intros H p a Hdslp Hsub. apply (H a). apply getDSLP_obsDSLP. intro Hout.
      exact (Hsub (proj1 (getDSLP_obsDSLP prog p a) Hdslp Hout)).
    - intros H a Hdslp. exact (H pre a Hdslp (fun Hs => Hs)).
  Qed.

  (** A [divergeD]-only program satisfies every [Over] triple and only the
      trivial [Under] ones -- the slice sees nothing. *)
  Theorem tripleASP_divergeD_over {A} pre (post : A -> Prop) :
    tripleASP divergeD Over pre post.
  Proof. intros a Hc. destruct (obsASP_divergeD pre a Hc). Qed.

  Theorem tripleDSLP_divergeD_over {A} pre (post : A -> Prop) :
    tripleDSLP divergeD Over pre post -> forall a, post a.
  Proof. intros H a. exact (H a (obsDSLP_divergeD pre a)). Qed.

End PureTriples.

Arguments tripleASP {_}.
Arguments tripleDSLP {_}.
