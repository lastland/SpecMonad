(** * The four SP observations of [stdivnd], assembled from its relation.

    The SP counterpart of [WP/StDivNonDet_WSt_Algebra.v].  There the
    computation is collapsed layer by layer into an assertion; here there
    is nothing to collapse, because an SP specification IS a relation
    ([BaseSpecMonads/SPure.v]).  What a client supplies is therefore not an
    algebra but a DENOTATION -- [strel], with its [ret] and [bind] laws
    ([BaseSpecMonads/SPRelDenote.v]) -- and the four observations are four
    READINGS of that one relation:

      [aspOfRelSt]  : some [pre]-state reaches the outcome;
      [dslpOfRelSt] : every state reaching it is a [pre]-state;
      [dspOfRelSt]  : both;      [aslpOfRelSt] : either.

    [StDivNonDet_SPSt.v] writes the four out and then proves [_ret] and
    [_bind] for each -- eight law proofs.  Here the instance below is the
    only input, and all eight are citations.

    The outcome space is the TERMINATING SLICE [A * S]: there is no [r]
    denoting divergence, so none of the four can constrain it.  That is
    what [divergeD_*] at the end records. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad SPRelDenote.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The denotation                                                 *)
(* ================================================================= *)

Section Outcomes.
  Variable S : Type.

  (** [Some r] is the terminating outcome [r]; [None] is divergence. *)

  Lemma outcomes_ret {A} (a : A) (s : S) (r : A * S) :
    unOptionT (runStateT (ret a : stdivnd S A) s) (Some r) <-> r = (a, s).
  Proof. cbn. split; intro H; congruence. Qed.

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

  Lemma outcomes_diverge {A} (s : S) (r : A * S) :
    ~ unOptionT (runStateT (divergeD : stdivnd S A) s) (Some r).
  Proof. cbn. intro H. congruence. Qed.

End Outcomes.

(** The whole input: a relation and its two laws. *)
#[global] Instance StRel_stdivnd (S : Type) : StRel (stdivnd S) S := {
  strel A m s r := unOptionT (runStateT m s) (Some r) ;
  strel_ret := @outcomes_ret S ;
  strel_bind := @outcomes_bind S
}.

(* ================================================================= *)
(** ** The four observations                                          *)
(* ================================================================= *)

Section Observations.
  Variable S : Type.

  Definition obsASP  {A} (m : stdivnd S A) : ASPSt S A  := obsASPof m.
  Definition obsDSLP {A} (m : stdivnd S A) : DSLPSt S A := obsDSLPof m.
  Definition obsDSP  {A} (m : stdivnd S A) : DSPSt S A  := obsDSPof m.
  Definition obsASLP {A} (m : stdivnd S A) : ASLPSt S A := obsASLPof m.

  (** ** What each reading says

      One relation, four readings -- and the contrast between them is
      visible in these four statements alone. *)

  Lemma getProgASP_obsASP {A} (m : stdivnd S A) pre r :
    getASPSt (obsASP m) pre r
    <-> (exists s, pre s /\ unOptionT (runStateT m s) (Some r)).
  Proof. exact (getASPSt_obsASPof m pre r). Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivnd S A) pre r :
    getDSLPSt (obsDSLP m) pre r
    <-> (forall s, unOptionT (runStateT m s) (Some r) -> pre s).
  Proof. exact (getDSLPSt_obsDSLPof m pre r). Qed.

  Lemma getProgDSP_obsDSP {A} (m : stdivnd S A) pre r :
    getDSPSt (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) (Some r))
         /\ (forall s, unOptionT (runStateT m s) (Some r) -> pre s)).
  Proof. exact (getDSPSt_obsDSPof m pre r). Qed.

  Lemma getProgASLP_obsASLP {A} (m : stdivnd S A) pre r :
    getASLPSt (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) (Some r))
         \/ (forall s, unOptionT (runStateT m s) (Some r) -> pre s)).
  Proof. exact (getASLPSt_obsASLPof m pre r). Qed.

  (** ** The morphism laws, for free *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : stdivnd S A)) (ret a).
  Proof. exact (obsASPof_ret a). Qed.
  Theorem obsASP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof. exact (obsASPof_bind x f). Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : stdivnd S A)) (ret a).
  Proof. exact (obsDSLPof_ret a). Qed.
  Theorem obsDSLP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof. exact (obsDSLPof_bind x f). Qed.

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : stdivnd S A)) (ret a).
  Proof. exact (obsDSPof_ret a). Qed.
  Theorem obsDSP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof. exact (obsDSPof_bind x f). Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : stdivnd S A)) (ret a).
  Proof. exact (obsASLPof_ret a). Qed.
  Theorem obsASLP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof. exact (obsASLPof_bind x f). Qed.

  (** ** The slice is blind to divergence *)

  Lemma obsASP_divergeD {A} (pre : S -> Prop) (r : A * S) :
    ~ getASPSt (obsASP divergeD) pre r.
  Proof.
    rewrite getProgASP_obsASP. intros [s [_ Hr]].
    exact (outcomes_diverge S s r Hr).
  Qed.

  Lemma obsDSLP_divergeD {A} (pre : S -> Prop) (r : A * S) :
    getDSLPSt (obsDSLP divergeD) pre r.
  Proof.
    apply getProgDSLP_obsDSLP. intros s Hr.
    destruct (outcomes_diverge S s r Hr).
  Qed.

End Observations.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.

(* ==================================================================== *)
(** * Triples                                                            *)
(* ==================================================================== *)

Inductive approxKind := | Under | Over.

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
      comparison target: ASP/[Over] and DSLP/[Under], the two that are
      relation inclusions.  The other two are compared ambiently, because
      join preservation makes every ASP false at the empty precondition
      and meet preservation makes every DSLP true at the full one. *)

  Definition pp2asp_over {S A} (pre : S -> Prop) (post : A * S -> Prop)
    : ASPSt S A :=
    aspOfRelSt (fun s r => pre s -> post r).

  Definition pp2dslp_under {S A} (pre : S -> Prop) (post : A * S -> Prop)
    : DSLPSt S A :=
    dslpOfRelSt (fun s r => post r -> pre s).

  Definition tripleASPspec {S A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordASPSt (obsASP prog) (pp2asp_over pre post)
    | Under => False (* doesn't work *)
    end.

  Definition tripleDSLPspec {S A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => False (* doesn't work *)
    | Under => ordDSLPSt (pp2dslp_under pre post) (obsDSLP prog)
    end.

  Theorem tripleASPDefEq {S A} (prog : stdivnd S A) (kind : approxKind) pre post :
    tripleASP prog Over pre post <-> tripleASPspec prog Over pre post.
  Proof.
    (* [Over]: in-monad, and exact *)
    unfold tripleASP, tripleASPspec, pp2asp_over. rewrite ordASPSt_get. split.
    - intros H p r Hobs. apply getASPSt_of.
      apply getProgASP_obsASP in Hobs. destruct Hobs as [s [Hp Hout]].
      exists s. split; [ exact Hp |]. intro Hpre. apply H.
      apply getProgASP_obsASP. exists s. split; [ exact Hpre | exact Hout ].
    - intros H r Hobs.
      destruct (proj1 (getASPSt_of _ _ pre r) (H pre r Hobs)) as [s1 [Hp1 Himp]].
      exact (Himp Hp1).
  Qed.

  Theorem tripleDSLPDefEq {S A} (prog : stdivnd S A) (kind : approxKind) pre post :
    tripleDSLP prog Under pre post <-> tripleDSLPspec prog Under pre post.
  Proof.
    (* [Under]: in-monad, and exact *)
    unfold tripleDSLP, tripleDSLPspec, pp2dslp_under.
    rewrite ordDSLPSt_get. split.
    - intros H p r Hd. apply getProgDSLP_obsDSLP. intros s Hout.
      apply (proj1 (getDSLPSt_of _ _ p r) Hd). intro Hpost.
      exact (proj1 (getProgDSLP_obsDSLP S prog pre r) (H r Hpost) s Hout).
    - intros H r Hpost. apply getProgDSLP_obsDSLP. intros s Hout.
      refine (proj1 (getProgDSLP_obsDSLP S prog (fun t => post r -> pre t) r)
                (H (fun t => post r -> pre t) r _) s Hout Hpost).
      apply getDSLPSt_of. intros t Ht. exact Ht.
  Qed.

  (** A [divergeD]-only program satisfies every [Over] triple and only the
      trivial [Under] ones -- the slice sees nothing. *)
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
