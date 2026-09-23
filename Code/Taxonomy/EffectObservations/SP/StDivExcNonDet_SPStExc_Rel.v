(** * The four SP observations of [stdivexcnd], from its denotation.

    The exception-carrying case of [StDivNonDet_SPSt_Rel.v].  The outcome
    space is now [option (A * S)]: the EXCEPTIONAL outcome [None] is a
    result the specification can talk about, where DIVERGENCE (the outer
    [None] of [stdivexcnd]) is still invisible -- there is no outcome
    denoting it, so none of the four observations can constrain it.

    That is the whole difference from the stateful case, and it shows up
    in exactly one place: [xrel_bind] has an exception branch, where an
    exceptional outcome of the first stage IS an outcome of the composite
    and the continuation never runs ([BaseSpecMonads/SPRelDenote.v]).

    [StDivExcNonDet_SPStExc.v] writes the four observations out and proves
    [_ret] and [_bind] for each.  Here the instance below is the only
    input and all eight are citations. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad SPRelDenote.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The denotation                                                 *)
(* ================================================================= *)

Section Outcomes.
  Variable S : Type.

  (** [Some r] is a terminating outcome -- [r] itself being [Some] for a
      normal return and [None] for a raised exception.  The outer [None]
      is divergence. *)

  Lemma outcomes_ret {A} (a : A) (s : S) (r : option (A * S)) :
    unOptionT (unOptionT (runStateT (ret a : stdivexcnd S A) s)) (Some r)
    <-> r = Some (a, s).
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma outcomes_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B)
    (s : S) (r : option (B * S)) :
    unOptionT (unOptionT (runStateT (x >>= f) s)) (Some r)
    <-> (exists o, unOptionT (unOptionT (runStateT x s)) (Some o)
                   /\ match o with
                      | Some (a, s') =>
                          unOptionT (unOptionT (runStateT (f a) s')) (Some r)
                      | None => r = None
                      end).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. destruct oy as [[[a s']|]|]; cbn in *.
      + exists (Some (a, s')). split; [ exact H1 | exact H2 ].
      + exists None. split; [ exact H1 | congruence ].
      + congruence.
    - intros [o [H1 H2]]. destruct o as [[a s']|]; cbn in *.
      + exists (Some (Some (a, s'))). split; [ exact H1 | exact H2 ].
      + exists (Some None). split; [ exact H1 | cbn; congruence ].
  Qed.

  Lemma outcomes_divergeD {A} (s : S) (r : option (A * S)) :
    ~ unOptionT (unOptionT (runStateT (spinP S) s)) (Some r).
  Proof. cbn. intro H. congruence. Qed.

End Outcomes.

#[global] Instance StExcRel_stdivexcnd (S : Type) : StExcRel (stdivexcnd S) S := {
  xrel A m s r := unOptionT (unOptionT (runStateT m s)) (Some r) ;
  xrel_ret := @outcomes_ret S ;
  xrel_bind := @outcomes_bind S
}.

(* ================================================================= *)
(** ** The four observations                                          *)
(* ================================================================= *)

Section Observations.
  Variable S : Type.

  Definition obsASP  {A} (m : stdivexcnd S A) : ASPStExc  S A := obsASPofX m.
  Definition obsDSLP {A} (m : stdivexcnd S A) : DSLPStExc S A := obsDSLPofX m.
  Definition obsDSP  {A} (m : stdivexcnd S A) : DSPStExc  S A := obsDSPofX m.
  Definition obsASLP {A} (m : stdivexcnd S A) : ASLPStExc S A := obsASLPofX m.

  (** ** What each reading says *)

  Lemma getProg_obsASP {A} (m : stdivexcnd S A) pre r :
    getASPStExc (obsASP m) pre r
    <-> (exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r)).
  Proof. exact (getASPStExc_obsASPofX m pre r). Qed.

  Lemma getProg_obsDSLP {A} (m : stdivexcnd S A) pre r :
    getDSLPStExc (obsDSLP m) pre r
    <-> (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s).
  Proof. exact (getDSLPStExc_obsDSLPofX m pre r). Qed.

  Lemma getProg_obsDSP {A} (m : stdivexcnd S A) pre r :
    getDSPStExc (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r))
         /\ (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s)).
  Proof. exact (getDSPStExc_obsDSPofX m pre r). Qed.

  Lemma getProg_obsASLP {A} (m : stdivexcnd S A) pre r :
    getASLPStExc (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r))
         \/ (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s)).
  Proof. exact (getASLPStExc_obsASLPofX m pre r). Qed.

  (** ** The morphism laws, for free *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (obsASPofX_ret a). Qed.
  Theorem obsASP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof. exact (obsASPofX_bind x f). Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (obsDSLPofX_ret a). Qed.
  Theorem obsDSLP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof. exact (obsDSLPofX_bind x f). Qed.

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (obsDSPofX_ret a). Qed.
  Theorem obsDSP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof. exact (obsDSPofX_bind x f). Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : stdivexcnd S A)) (ret a).
  Proof. exact (obsASLPofX_ret a). Qed.
  Theorem obsASLP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof. exact (obsASLPofX_bind x f). Qed.

  (** ** Divergence is invisible; the exception is not

      [spinP] has no outcome at all, so ASP is empty on it and DSLP
      trivial -- exactly as in the divergence-only stack.  A [raise], by
      contrast, has the outcome [None], which both observations see. *)

  Lemma obsASP_divergeD {A} (pre : S -> Prop) (r : option (A * S)) :
    ~ getASPStExc (obsASP (spinP S)) pre r.
  Proof.
    rewrite getProg_obsASP. intros [s [_ Hr]].
    exact (outcomes_divergeD S s r Hr).
  Qed.

  Lemma obsDSLP_divergeD {A} (pre : S -> Prop) (r : option (A * S)) :
    getDSLPStExc (obsDSLP (spinP S)) pre r.
  Proof.
    apply getProg_obsDSLP. intros s Hr.
    destruct (outcomes_divergeD S s r Hr).
  Qed.

End Observations.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.
