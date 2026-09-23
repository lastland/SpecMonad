(** * Relational denotations, and the four SP observations they induce.

    The SP counterpart of [MonadAlgebra.v].  On the WP side an algebra
    [mu : M Prop -> Prop] collapses a monadic collection of assertions and
    induces an observation into [WPure]; on the SP side the arrows ARE
    relations ([ASPMonad.v]: [aspRel] is a bijection), so what plays the
    role of the algebra is the relation a computation denotes:

      [strel : M A -> S -> A * S -> Prop]

    subject to exactly the two facts every SP observation in this
    development is proved from -- [ret] denotes the identity-with-output and
    [bind] denotes relational composition with the state threaded.  Those
    are the [outcomes_ret] / [outcomes_bind] lemmas of the observation
    files, here promoted to the interface.

    From one such denotation all FOUR observations follow, since all four
    constructors take the same relation:

      [aspOfRelSt] / [dslpOfRelSt] / [dspOfRelSt] / [aslpOfRelSt]

    together with their eight monad-morphism laws, proved once below.  A
    client supplies [strel] and the two laws, and defines no observation
    law of its own. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPure ASPMonad DSLPMonad DSPMonad ASLPMonad.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The interface                                                  *)
(* ================================================================= *)

Class StRel (M : Type -> Type) {MM : Monad M} (S : Type) := {
  strel : forall {A}, M A -> S -> A * S -> Prop ;
  strel_ret : forall {A} (a : A) (s : S) (r : A * S),
    strel (ret a) s r <-> r = (a, s) ;
  strel_bind : forall {A B} (x : M A) (f : A -> M B) (s : S) (r : B * S),
    strel (bind x f) s r
    <-> (exists a s', strel x s (a, s') /\ strel (f a) s' r)
}.

Arguments strel {M} {MM} {S} {_} {A}.

(* ================================================================= *)
(** ** The four observations, and their laws                          *)
(* ================================================================= *)

Section Observations.
  Context {M : Type -> Type} {MM : Monad M} {S : Type} {RM : StRel M S}.

  Definition obsASPof  {A} (m : M A) : ASPSt  S A := aspOfRelSt  (strel m).
  Definition obsDSLPof {A} (m : M A) : DSLPSt S A := dslpOfRelSt (strel m).
  Definition obsDSPof  {A} (m : M A) : DSPSt  S A := dspOfRelSt  (strel m).
  Definition obsASLPof {A} (m : M A) : ASLPSt S A := aslpOfRelSt (strel m).

  (** The readings, at a shared precondition. *)

  Lemma getASPSt_obsASPof {A} (m : M A) pre r :
    getASPSt (obsASPof m) pre r <-> (exists s, pre s /\ strel m s r).
  Proof. apply getASPSt_of. Qed.

  Lemma getDSLPSt_obsDSLPof {A} (m : M A) pre r :
    getDSLPSt (obsDSLPof m) pre r <-> (forall s, strel m s r -> pre s).
  Proof. apply getDSLPSt_of. Qed.

  Lemma getDSPSt_obsDSPof {A} (m : M A) pre r :
    getDSPSt (obsDSPof m) pre r
    <-> ((exists s, pre s /\ strel m s r) /\ (forall s, strel m s r -> pre s)).
  Proof. apply getDSPSt_of. Qed.

  Lemma getASLPSt_obsASLPof {A} (m : M A) pre r :
    getASLPSt (obsASLPof m) pre r
    <-> ((exists s, pre s /\ strel m s r) \/ (forall s, strel m s r -> pre s)).
  Proof. apply getASLPSt_of. Qed.

  (** *** ASP and DSLP: the two morphism laws each. *)

  Theorem obsASPof_ret {A} (a : A) : eq1 (obsASPof (ret a)) (ret a).
  Proof.
    apply eq1_ASPSt_get. intros pre r. cbn [ret Monad_ASPSt].
    rewrite getASPSt_obsASPof, getASPSt_ret. split.
    - intros [s [Hp Hr]]. exists s.
      split; [ exact Hp | exact (proj1 (strel_ret a s r) Hr) ].
    - intros [s [Hp Heq]]. exists s.
      split; [ exact Hp | exact (proj2 (strel_ret a s r) Heq) ].
  Qed.

  Theorem obsASPof_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsASPof (bind x f)) (bind (obsASPof x) (fun a => obsASPof (f a))).
  Proof.
    apply eq1_ASPSt_get. intros pre r. cbn [bind Monad_ASPSt].
    rewrite getASPSt_obsASPof, getASPSt_bind.
    setoid_rewrite getASPSt_obsASPof. split.
    - intros [s [Hp Hrel]]. apply strel_bind in Hrel.
      destruct Hrel as [a [s' [Hx Hk]]].
      exists a, s'. split.
      + exists s. split; [ exact Hp | exact Hx ].
      + exists s'. split; [ reflexivity | exact Hk ].
    - intros [a [s' [[s [Hp Hx]] [s2 [Hs2 Hk]]]]]. subst s2.
      exists s. split; [ exact Hp |]. apply strel_bind.
      exists a, s'. split; [ exact Hx | exact Hk ].
  Qed.

  Theorem obsDSLPof_ret {A} (a : A) : eq1 (obsDSLPof (ret a)) (ret a).
  Proof.
    apply eq1_DSLPSt_get. intros pre r. cbn [ret Monad_DSLPSt].
    rewrite getDSLPSt_obsDSLPof, getDSLPSt_ret. split.
    - intros H s Heq. exact (H s (proj2 (strel_ret a s r) Heq)).
    - intros H s Hr. exact (H s (proj1 (strel_ret a s r) Hr)).
  Qed.

  Theorem obsDSLPof_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsDSLPof (bind x f)) (bind (obsDSLPof x) (fun a => obsDSLPof (f a))).
  Proof.
    apply eq1_DSLPSt_get. intros pre r. cbn [bind Monad_DSLPSt].
    rewrite getDSLPSt_obsDSLPof, getDSLPSt_bind.
    setoid_rewrite getDSLPSt_obsDSLPof. setoid_rewrite dslpRelSt_of. split.
    - intros H a s' Hf s Hx. apply H. apply strel_bind.
      exists a, s'. split; [ exact Hx | exact Hf ].
    - intros H s Hrel. apply strel_bind in Hrel.
      destruct Hrel as [a [s' [Hx Hk]]]. exact (H a s' Hk s Hx).
  Qed.

  (** *** DSP and ASLP: an element is determined by the relation it denotes
      ([dspRel_faithful] / [aslpRel_faithful]), and [ret] / [bind] denote
      the identity-with-output and relational composition ([SPure.RelDenote],
      [dspRelSt_bind_of] / [aslpRelSt_bind_of]) -- which is what [strel_ret]
      / [strel_bind] say of the computation. *)

  Theorem obsDSPof_ret {A} (a : A) : eq1 (obsDSPof (ret a)) (ret a).
  Proof.
    apply dspRel_faithful. intros [[] s] r. unfold obsDSPof.
    rewrite dspRelSt_of, strel_ret.
    cbn [ret Monad_DSPSt Monad_Arrow ret_arrow arr_pure Arrow_stateArrT].
    rewrite (@rd_pure DSPArr _ _ _ (@dspRel) _). cbn.
    split; intro H; symmetry; exact H.
  Qed.

  Theorem obsDSPof_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsDSPof (bind x f)) (bind (obsDSPof x) (fun a => obsDSPof (f a))).
  Proof.
    apply dspRel_faithful. intros [[] s] r. unfold obsDSPof.
    rewrite dspRelSt_of, strel_bind. symmetry.
    exact (dspRelSt_bind_of (strel x) (fun a => strel (f a)) s r).
  Qed.

  Theorem obsASLPof_ret {A} (a : A) : eq1 (obsASLPof (ret a)) (ret a).
  Proof.
    apply aslpRel_faithful. intros [[] s] r. unfold obsASLPof.
    rewrite aslpRelSt_of, strel_ret.
    cbn [ret Monad_ASLPSt Monad_Arrow ret_arrow arr_pure Arrow_stateArrT].
    rewrite (@rd_pure ASLPArr _ _ _ (@aslpRel) _). cbn.
    split; intro H; symmetry; exact H.
  Qed.

  Theorem obsASLPof_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsASLPof (bind x f)) (bind (obsASLPof x) (fun a => obsASLPof (f a))).
  Proof.
    apply aslpRel_faithful. intros [[] s] r. unfold obsASLPof.
    rewrite aslpRelSt_of, strel_bind. symmetry.
    exact (aslpRelSt_bind_of (strel x) (fun a => strel (f a)) s r).
  Qed.

End Observations.

Arguments obsASPof  {M} {MM} {S} {RM} {A}.
Arguments obsDSLPof {M} {MM} {S} {RM} {A}.
Arguments obsDSPof  {M} {MM} {S} {RM} {A}.
Arguments obsASLPof {M} {MM} {S} {RM} {A}.

(* ================================================================= *)
(** ** The stateless denotation                                       *)
(* ================================================================= *)

(** With no state there is no input to relate from, so a computation
    denotes a PREDICATE on outcomes rather than a relation, and the four
    readings are taken against a [Prop] precondition. *)

Class PureRel (M : Type -> Type) {MM : Monad M} := {
  prel : forall {A}, M A -> A -> Prop ;
  prel_ret : forall {A} (a a' : A), prel (ret a) a' <-> a' = a ;
  prel_bind : forall {A B} (x : M A) (f : A -> M B) (b : B),
    prel (bind x f) b <-> (exists a, prel x a /\ prel (f a) b)
}.

Arguments prel {M} {MM} {_} {A}.

Section PureObservations.
  Context {M : Type -> Type} {MM : Monad M} {RM : PureRel M}.

  Definition obsASPofP  {A} (m : M A) : ASP  A := aspOfPred  (prel m).
  Definition obsDSLPofP {A} (m : M A) : DSLP A := dslpOfPred (prel m).
  Definition obsDSPofP  {A} (m : M A) : DSP  A := dspOfPred  (prel m).
  Definition obsASLPofP {A} (m : M A) : ASLP A := aslpOfPred (prel m).

  Lemma getASP_obsASPofP {A} (m : M A) p a :
    getASP (obsASPofP m) p a <-> (p /\ prel m a).
  Proof. apply getASP_of. Qed.

  Lemma getDSLP_obsDSLPofP {A} (m : M A) p a :
    getDSLP (obsDSLPofP m) p a <-> (prel m a -> p).
  Proof. apply getDSLP_of. Qed.

  Lemma getDSPPure_obsDSPofP {A} (m : M A) p a :
    getDSPPure (obsDSPofP m) p a <-> ((p /\ prel m a) /\ (prel m a -> p)).
  Proof. apply getDSPPure_of. Qed.

  Lemma getASLPPure_obsASLPofP {A} (m : M A) p a :
    getASLPPure (obsASLPofP m) p a <-> ((p /\ prel m a) \/ (prel m a -> p)).
  Proof. apply getASLPPure_of. Qed.

  Theorem obsASPofP_ret {A} (a : A) : eq1 (obsASPofP (ret a)) (ret a).
  Proof.
    apply eq1_ASP_get. intros p a'. cbn [ret Monad_ASP].
    rewrite getASP_obsASPofP, getASP_ret. split.
    - intros [Hp Hr]. split; [ exact Hp | symmetry; exact (proj1 (prel_ret a a') Hr) ].
    - intros [Hp Heq]. split; [ exact Hp | apply prel_ret; symmetry; exact Heq ].
  Qed.

  Theorem obsASPofP_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsASPofP (bind x f)) (bind (obsASPofP x) (fun a => obsASPofP (f a))).
  Proof.
    apply eq1_ASP_get. intros p b. cbn [bind Monad_ASP].
    rewrite getASP_obsASPofP, getASP_bind.
    setoid_rewrite getASP_obsASPofP. split.
    - intros [Hp Hrel]. apply prel_bind in Hrel. destruct Hrel as [a [Hx Hk]].
      exists a. split; [ split; [ exact Hp | exact Hx ] | split; [ exact I | exact Hk ] ].
    - intros [a [[Hp Hx] [_ Hk]]]. split; [ exact Hp |].
      apply prel_bind. exists a. split; [ exact Hx | exact Hk ].
  Qed.

  Theorem obsDSLPofP_ret {A} (a : A) : eq1 (obsDSLPofP (ret a)) (ret a).
  Proof.
    apply eq1_DSLP_get. intros p a'. cbn [ret Monad_DSLP].
    rewrite getDSLP_obsDSLPofP, getDSLP_ret. split.
    - intros H Heq. apply H. apply prel_ret. symmetry. exact Heq.
    - intros H Hr. apply H. symmetry. exact (proj1 (prel_ret a a') Hr).
  Qed.

  Theorem obsDSLPofP_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsDSLPofP (bind x f)) (bind (obsDSLPofP x) (fun a => obsDSLPofP (f a))).
  Proof.
    apply eq1_DSLP_get. intros p b. cbn [bind Monad_DSLP].
    rewrite getDSLP_obsDSLPofP, getDSLP_bind.
    setoid_rewrite getDSLP_obsDSLPofP. split.
    - intros H a Hk Hx. apply H. apply prel_bind.
      exists a. split; [ exact Hx |].
      exact (proj1 (dslpRel_ofRel (fun _ => prel (f a)) tt b) Hk).
    - intros H Hrel. apply prel_bind in Hrel. destruct Hrel as [a [Hx Hk]].
      refine (H a _ Hx). unfold obsDSLPofP, dslpOfPred. apply dslpRel_ofRel. exact Hk.
  Qed.

  (** DSP and ASLP: an element is determined by its relation, and [ret] /
      [bind] denote the identity and relational composition. *)

  Lemma dspRelP_of {A} (Q : A -> Prop) a : dspRel (dspOfPred Q) tt a <-> Q a.
  Proof. exact (dspRel_ofRelArr (fun (_ : unit) a => Q a) tt a). Qed.

  Lemma aslpRelP_of {A} (Q : A -> Prop) a : aslpRel (aslpOfPred Q) tt a <-> Q a.
  Proof. exact (aslpRel_ofRelArr (fun (_ : unit) a => Q a) tt a). Qed.

  Theorem obsDSPofP_ret {A} (a : A) : eq1 (obsDSPofP (ret a)) (ret a).
  Proof.
    apply dspRel_faithful. intros [] a'. unfold obsDSPofP.
    rewrite dspRelP_of, prel_ret. symmetry.
    etransitivity; [ exact (@rd_pure DSPArr _ _ _ (@dspRel) _ unit A (fun _ => a) tt a') |].
    cbn. split; intro H; symmetry; exact H.
  Qed.

  Theorem obsDSPofP_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsDSPofP (bind x f)) (bind (obsDSPofP x) (fun a => obsDSPofP (f a))).
  Proof.
    apply dspRel_faithful. intros [] b. unfold obsDSPofP.
    rewrite dspRelP_of, prel_bind. symmetry.
    etransitivity;
      [ exact (rel_bind (arr := DSPArr) (rel := @dspRel)
                 (dspOfPred (prel x)) (fun a => dspOfPred (prel (f a))) tt b) |].
    split; intros [a [H1 H2]]; exists a.
    - split; [ exact (proj1 (dspRelP_of _ a) H1) | exact (proj1 (dspRelP_of _ b) H2) ].
    - split; [ exact (proj2 (dspRelP_of _ a) H1) | exact (proj2 (dspRelP_of _ b) H2) ].
  Qed.

  Theorem obsASLPofP_ret {A} (a : A) : eq1 (obsASLPofP (ret a)) (ret a).
  Proof.
    apply aslpRel_faithful. intros [] a'. unfold obsASLPofP.
    rewrite aslpRelP_of, prel_ret. symmetry.
    etransitivity; [ exact (@rd_pure ASLPArr _ _ _ (@aslpRel) _ unit A (fun _ => a) tt a') |].
    cbn. split; intro H; symmetry; exact H.
  Qed.

  Theorem obsASLPofP_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsASLPofP (bind x f)) (bind (obsASLPofP x) (fun a => obsASLPofP (f a))).
  Proof.
    apply aslpRel_faithful. intros [] b. unfold obsASLPofP.
    rewrite aslpRelP_of, prel_bind. symmetry.
    etransitivity;
      [ exact (rel_bind (arr := ASLPArr) (rel := @aslpRel)
                 (aslpOfPred (prel x)) (fun a => aslpOfPred (prel (f a))) tt b) |].
    split; intros [a [H1 H2]]; exists a.
    - split; [ exact (proj1 (aslpRelP_of _ a) H1) | exact (proj1 (aslpRelP_of _ b) H2) ].
    - split; [ exact (proj2 (aslpRelP_of _ a) H1) | exact (proj2 (aslpRelP_of _ b) H2) ].
  Qed.

End PureObservations.

Arguments obsASPofP  {M} {MM} {RM} {A}.
Arguments obsDSLPofP {M} {MM} {RM} {A}.
Arguments obsDSPofP  {M} {MM} {RM} {A}.
Arguments obsASLPofP {M} {MM} {RM} {A}.

(* ================================================================= *)
(** ** The denotation with an exception layer                         *)
(* ================================================================= *)

(** Outcomes now include the exceptional one, so the relation lands in
    [option (A * S)] and [bind]'s law has the exception case: an
    exceptional outcome of the first stage IS an outcome of the
    composite, and the continuation never runs. *)

Class StExcRel (M : Type -> Type) {MM : Monad M} (S : Type) := {
  xrel : forall {A}, M A -> S -> option (A * S) -> Prop ;
  xrel_ret : forall {A} (a : A) (s : S) (r : option (A * S)),
    xrel (ret a) s r <-> r = Some (a, s) ;
  xrel_bind : forall {A B} (x : M A) (f : A -> M B) (s : S) (r : option (B * S)),
    xrel (bind x f) s r
    <-> (exists o, xrel x s o /\
                   match o with
                   | Some (a, s') => xrel (f a) s' r
                   | None => r = None
                   end)
}.

Arguments xrel {M} {MM} {S} {_} {A}.

Section StExcObservations.
  Context {M : Type -> Type} {MM : Monad M} {S : Type} {RM : StExcRel M S}.

  Definition obsASPofX  {A} (m : M A) : ASPStExc  S A := aspOfRelStExc  (xrel m).
  Definition obsDSLPofX {A} (m : M A) : DSLPStExc S A := dslpOfRelStExc (xrel m).
  Definition obsDSPofX  {A} (m : M A) : DSPStExc  S A := dspOfRelStExc  (xrel m).
  Definition obsASLPofX {A} (m : M A) : ASLPStExc S A := aslpOfRelStExc (xrel m).

  Lemma getASPStExc_obsASPofX {A} (m : M A) pre r :
    getASPStExc (obsASPofX m) pre r <-> (exists s, pre s /\ xrel m s r).
  Proof. apply getASPStExc_of. Qed.

  Lemma getDSLPStExc_obsDSLPofX {A} (m : M A) pre r :
    getDSLPStExc (obsDSLPofX m) pre r <-> (forall s, xrel m s r -> pre s).
  Proof. apply getDSLPStExc_of. Qed.

  Lemma getDSPStExc_obsDSPofX {A} (m : M A) pre r :
    getDSPStExc (obsDSPofX m) pre r
    <-> ((exists s, pre s /\ xrel m s r) /\ (forall s, xrel m s r -> pre s)).
  Proof. apply getDSPStExc_of. Qed.

  Lemma getASLPStExc_obsASLPofX {A} (m : M A) pre r :
    getASLPStExc (obsASLPofX m) pre r
    <-> ((exists s, pre s /\ xrel m s r) \/ (forall s, xrel m s r -> pre s)).
  Proof. apply getASLPStExc_of. Qed.

  Theorem obsASPofX_ret {A} (a : A) : eq1 (obsASPofX (ret a)) (ret a).
  Proof.
    apply eq1_ASPStExc_get. intros pre r. cbn [ret Monad_ASPStExc].
    rewrite getASPStExc_obsASPofX, getASPStExc_ret. split.
    - intros [s [Hp Hr]]. exists s.
      split; [ exact Hp | exact (proj1 (xrel_ret a s r) Hr) ].
    - intros [s [Hp Heq]]. exists s.
      split; [ exact Hp | exact (proj2 (xrel_ret a s r) Heq) ].
  Qed.

  Theorem obsASPofX_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsASPofX (bind x f)) (bind (obsASPofX x) (fun a => obsASPofX (f a))).
  Proof.
    apply eq1_ASPStExc_get. intros pre r. cbn [bind Monad_ASPStExc].
    rewrite getASPStExc_obsASPofX, getASPStExc_bind.
    setoid_rewrite getASPStExc_obsASPofX. split.
    - intros [s [Hp Hrel]]. apply xrel_bind in Hrel.
      destruct Hrel as [[[a s']|] [Hx Hk]].
      + left. exists a, s'. split.
        * exists s. split; [ exact Hp | exact Hx ].
        * exists s'. split; [ reflexivity | exact Hk ].
      + right. split; [ exact Hk |]. exists s. split; [ exact Hp | exact Hx ].
    - intros [[a [s' [[s [Hp Hx]] [s2 [Hs2 Hk]]]]] | [-> [s [Hp Hx]]]].
      + subst s2. exists s. split; [ exact Hp |]. apply xrel_bind.
        exists (Some (a, s')). split; [ exact Hx | exact Hk ].
      + exists s. split; [ exact Hp |]. apply xrel_bind.
        exists None. split; [ exact Hx | reflexivity ].
  Qed.

  Theorem obsDSLPofX_ret {A} (a : A) : eq1 (obsDSLPofX (ret a)) (ret a).
  Proof.
    apply eq1_DSLPStExc_get. intros pre r. cbn [ret Monad_DSLPStExc].
    rewrite getDSLPStExc_obsDSLPofX, getDSLPStExc_ret. split.
    - intros H s Heq. exact (H s (proj2 (xrel_ret a s r) Heq)).
    - intros H s Hr. exact (H s (proj1 (xrel_ret a s r) Hr)).
  Qed.

  Theorem obsDSLPofX_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsDSLPofX (bind x f)) (bind (obsDSLPofX x) (fun a => obsDSLPofX (f a))).
  Proof.
    apply eq1_DSLPStExc_get. intros pre r. cbn [bind Monad_DSLPStExc].
    rewrite getDSLPStExc_obsDSLPofX, getDSLPStExc_bind.
    setoid_rewrite getDSLPStExc_obsDSLPofX. split.
    - intros H o Ho s Hx. apply H. apply xrel_bind.
      exists o. split; [ exact Hx |].
      destruct o as [[a s']|]; [| exact Ho ].
      unfold obsDSLPofX in Ho. rewrite dslpRelStExc_of in Ho. exact Ho.
    - intros H s Hrel. apply xrel_bind in Hrel.
      destruct Hrel as [o [Hx Hk]]. apply (H o); [| exact Hx ].
      destruct o as [[a s']|]; [| exact Hk ].
      unfold obsDSLPofX. rewrite dslpRelStExc_of. exact Hk.
  Qed.

  (** DSP and ASLP, as at the other two levels. *)

  Lemma dspRelX_of {A} (R : S -> option (A * S) -> Prop) s r :
    dspRel (dspOfRelStExc R) (tt, s) r <-> R s r.
  Proof. exact (dspRel_ofRelArr (fun (p : unit * S) r => R (snd p) r) (tt, s) r). Qed.

  Lemma aslpRelX_of {A} (R : S -> option (A * S) -> Prop) s r :
    aslpRel (aslpOfRelStExc R) (tt, s) r <-> R s r.
  Proof. exact (aslpRel_ofRelArr (fun (p : unit * S) r => R (snd p) r) (tt, s) r). Qed.

  Theorem obsDSPofX_ret {A} (a : A) : eq1 (obsDSPofX (ret a)) (ret a).
  Proof.
    apply dspRel_faithful. intros [[] s] o. unfold obsDSPofX.
    rewrite dspRelX_of, xrel_ret. symmetry.
    exact (relE_pure (arr := DSPArr) (rel := @dspRel) S (fun _ : unit => a) tt s o).
  Qed.

  Theorem obsDSPofX_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsDSPofX (bind x f)) (bind (obsDSPofX x) (fun a => obsDSPofX (f a))).
  Proof.
    apply dspRel_faithful. intros [[] s] o. unfold obsDSPofX.
    rewrite dspRelX_of, xrel_bind. symmetry.
    etransitivity;
      [ exact (relE_bind (arr := DSPArr) (rel := @dspRel) S
                 (dspOfRelStExc (xrel x)) (fun a => dspOfRelStExc (xrel (f a))) tt s o) |].
    split; intros [o1 [H1 H2]]; exists o1.
    - split; [ exact (proj1 (dspRelX_of _ s o1) H1) |].
      destruct o1 as [[a s']|]; [ exact (proj1 (dspRelX_of _ s' o) H2) | exact H2 ].
    - split; [ exact (proj2 (dspRelX_of _ s o1) H1) |].
      destruct o1 as [[a s']|]; [ exact (proj2 (dspRelX_of _ s' o) H2) | exact H2 ].
  Qed.

  Theorem obsASLPofX_ret {A} (a : A) : eq1 (obsASLPofX (ret a)) (ret a).
  Proof.
    apply aslpRel_faithful. intros [[] s] o. unfold obsASLPofX.
    rewrite aslpRelX_of, xrel_ret. symmetry.
    exact (relE_pure (arr := ASLPArr) (rel := @aslpRel) S (fun _ : unit => a) tt s o).
  Qed.

  Theorem obsASLPofX_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (obsASLPofX (bind x f)) (bind (obsASLPofX x) (fun a => obsASLPofX (f a))).
  Proof.
    apply aslpRel_faithful. intros [[] s] o. unfold obsASLPofX.
    rewrite aslpRelX_of, xrel_bind. symmetry.
    etransitivity;
      [ exact (relE_bind (arr := ASLPArr) (rel := @aslpRel) S
                 (aslpOfRelStExc (xrel x)) (fun a => aslpOfRelStExc (xrel (f a))) tt s o) |].
    split; intros [o1 [H1 H2]]; exists o1.
    - split; [ exact (proj1 (aslpRelX_of _ s o1) H1) |].
      destruct o1 as [[a s']|]; [ exact (proj1 (aslpRelX_of _ s' o) H2) | exact H2 ].
    - split; [ exact (proj2 (aslpRelX_of _ s o1) H1) |].
      destruct o1 as [[a s']|]; [ exact (proj2 (aslpRelX_of _ s' o) H2) | exact H2 ].
  Qed.

End StExcObservations.

Arguments obsASPofX  {M} {MM} {S} {RM} {A}.
Arguments obsDSLPofX {M} {MM} {S} {RM} {A}.
Arguments obsDSPofX  {M} {MM} {S} {RM} {A}.
Arguments obsASLPofX {M} {MM} {S} {RM} {A}.
