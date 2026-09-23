(** * An ALTERNATIVE construction of SP effect observations, by stacking.

    [SPRelDenote.v] asks a client for a DENOTATION at a fixed shape --
    [StRel] / [PureRel] / [StExcRel] -- and proves the client's eight
    monad-morphism laws from it.  The client still supplies [strel] and
    its two laws by hand, once per computation monad.

    This file offers the other half: the two laws themselves are DERIVED,
    by stacking transformer steps on a single hand-written base.  A client
    that is a tower of [optionT] and [stateT] over [SetM] supplies nothing.

    Nothing in [SPRelDenote.v] or its clients changes; this is an
    additional route to the same observations.  [EffectObservations/SP/
    StDivNonDet_SPSt_Tower.v] takes it for [stdivnd] and shows the result
    is DEFINITIONALLY the observation [StDivNonDet_SPSt_Rel.v] builds.

    THE SHAPE.  What varies between the three fixed shapes is exactly one
    thing: how you continue past an outcome.  [OShape] names it, and it
    governs both the denotation's [bind] law and the carrier's.

    COLLAPSE VS. KEEP.  [GRel_optionT] keeps a layer in the outcome shape;
    [GRel_divnd_slice] projects it away.  That fork is the SP counterpart
    of the WP side's [none : L] handler ([MonadAlgebra.v]), and unlike the
    WP side it is orthogonal to the choice of reading: each shape carries
    all four of ASP / DSLP / DSP / ASLP.

    NO GLOBAL INSTANCES.  Every construction below is a [Definition] and
    every use is pinned with [@].  The steps have the recursive shape
    [Foo ?base -> Foo (T ?base)] that this development has repeatedly seen
    send typeclass search exponential (see CLAUDE.md), so none of them is
    declared as an [Instance]. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The shape, and the denotation over it                          *)
(* ================================================================= *)

Class OShape (I : Type) (Out : Type -> Type) := {
  oeta  : forall {A}, I -> A -> Out A ;
  ostep : forall {A B}, (A -> I -> Out B -> Prop) -> Out A -> Out B -> Prop ;
  ostep_proper : forall {A B} (k k' : A -> I -> Out B -> Prop),
    (forall a i o, k a i o <-> k' a i o) ->
    forall w o, ostep k w o <-> ostep k' w o
}.

Arguments oeta  {I Out _ A}.
Arguments ostep {I Out _ A B}.

Class GRel (M : Type -> Type) {MM : Monad M} (I : Type) (Out : Type -> Type)
  {OS : OShape I Out} := {
  grel : forall {A}, M A -> I -> Out A -> Prop ;
  grel_ret : forall {A} (a : A) (i : I) (o : Out A),
    grel (ret a) i o <-> o = oeta i a ;
  grel_bind : forall {A B} (x : M A) (f : A -> M B) (i : I) (o : Out B),
    grel (bind x f) i o
    <-> exists w, grel x i w /\ ostep (fun a i' => grel (f a) i') w o
}.

Arguments grel {M MM I Out OS _ A}.

(* ================================================================= *)
(** ** The carriers, over any shape                                   *)
(* ================================================================= *)

Class ASPCar (I : Type) (Out : Type -> Type) {OS : OShape I Out}
  (C : Type -> Type) {MC : Monad C} {EC : Eq1 C} := {
  aof  : forall {A}, (I -> Out A -> Prop) -> C A ;
  aget : forall {A}, C A -> (I -> Prop) -> Out A -> Prop ;
  aget_of : forall {A} (R : I -> Out A -> Prop) P o,
    aget (aof R) P o <-> exists i, P i /\ R i o ;
  aeq1 : forall {A} (m n : C A),
    eq1 m n <-> (forall P o, aget m P o <-> aget n P o) ;
  aget_ret : forall {A} (x : A) P o,
    aget (ret x) P o <-> exists i, P i /\ o = oeta i x ;
  aget_bind : forall {A B} (m : C A) (k : A -> C B) P o,
    aget (bind m k) P o
    <-> exists w, aget m P w
                  /\ ostep (fun a i' => aget (k a) (fun j => j = i')) w o
}.

Arguments aof  {I Out OS C MC EC _ A}.
Arguments aget {I Out OS C MC EC _ A}.

Class DSLPCar (I : Type) (Out : Type -> Type) {OS : OShape I Out}
  (C : Type -> Type) {MC : Monad C} {EC : Eq1 C} := {
  dof  : forall {A}, (I -> Out A -> Prop) -> C A ;
  dget : forall {A}, C A -> (I -> Prop) -> Out A -> Prop ;
  drel : forall {A}, C A -> I -> Out A -> Prop ;
  dget_of : forall {A} (R : I -> Out A -> Prop) P o,
    dget (dof R) P o <-> (forall i, R i o -> P i) ;
  drel_of : forall {A} (R : I -> Out A -> Prop) i o,
    drel (dof R) i o <-> R i o ;
  deq1 : forall {A} (m n : C A),
    eq1 m n <-> (forall P o, dget m P o <-> dget n P o) ;
  dget_ret : forall {A} (x : A) P o,
    dget (ret x) P o <-> (forall i, o = oeta i x -> P i) ;
  dget_bind : forall {A B} (m : C A) (k : A -> C B) P o,
    dget (bind m k) P o
    <-> (forall w, ostep (fun a i' => drel (k a) i') w o -> dget m P w)
}.

Arguments dof  {I Out OS C MC EC _ A}.
Arguments dget {I Out OS C MC EC _ A}.
Arguments drel {I Out OS C MC EC _ A}.

(* ================================================================= *)
(** ** The four laws, proved once for every shape                     *)
(* ================================================================= *)

Section GenericASP.
  Context {M : Type -> Type} {MM : Monad M} {I : Type} {Out : Type -> Type}
          {OS : OShape I Out} {RM : GRel M I Out}
          {C : Type -> Type} {MC : Monad C} {EC : Eq1 C} {AC : ASPCar I Out C}.

  Definition gobsASP {A} (m : M A) : C A := aof (grel m).

  Lemma gobsASP_get {A} (m : M A) P o :
    aget (gobsASP m) P o <-> exists i, P i /\ grel m i o.
  Proof. apply aget_of. Qed.

  Theorem gobsASP_ret {A} (a : A) : eq1 (gobsASP (ret a)) (ret a).
  Proof.
    apply aeq1. intros P o.
    rewrite gobsASP_get, aget_ret. split.
    - intros [i [HP Hg]]. exists i.
      split; [ exact HP | exact (proj1 (grel_ret a i o) Hg) ].
    - intros [i [HP Ho]]. exists i.
      split; [ exact HP | exact (proj2 (grel_ret a i o) Ho) ].
  Qed.

  Theorem gobsASP_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (gobsASP (bind x f)) (bind (gobsASP x) (fun a => gobsASP (f a))).
  Proof.
    apply aeq1. intros P o.
    rewrite gobsASP_get, aget_bind.
    assert (Hk : forall a i' o',
               aget (gobsASP (f a)) (fun j => j = i') o' <-> grel (f a) i' o').
    { intros a i' o'. rewrite gobsASP_get. split.
      - intros [j [-> Hg]]. exact Hg.
      - intro Hg. exists i'. split; [ reflexivity | exact Hg ]. }
    split.
    - intros [i [HP Hg]]. apply grel_bind in Hg. destruct Hg as [w [Hx Hs]].
      exists w. split.
      + apply gobsASP_get. exists i. split; [ exact HP | exact Hx ].
      + exact (proj2 (ostep_proper _ _ (fun a i' o' => Hk a i' o') w o) Hs).
    - intros [w [Hx Hs]]. apply gobsASP_get in Hx. destruct Hx as [i [HP Hxw]].
      exists i. split; [ exact HP |]. apply grel_bind. exists w. split.
      + exact Hxw.
      + exact (proj1 (ostep_proper _ _ (fun a i' o' => Hk a i' o') w o) Hs).
  Qed.

End GenericASP.

Section GenericDSLP.
  Context {M : Type -> Type} {MM : Monad M} {I : Type} {Out : Type -> Type}
          {OS : OShape I Out} {RM : GRel M I Out}
          {C : Type -> Type} {MC : Monad C} {EC : Eq1 C} {DC : DSLPCar I Out C}.

  Definition gobsDSLP {A} (m : M A) : C A := dof (grel m).

  Lemma gobsDSLP_get {A} (m : M A) P o :
    dget (gobsDSLP m) P o <-> (forall i, grel m i o -> P i).
  Proof. apply dget_of. Qed.

  Lemma gobsDSLP_rel {A} (m : M A) i o : drel (gobsDSLP m) i o <-> grel m i o.
  Proof. apply drel_of. Qed.

  Theorem gobsDSLP_ret {A} (a : A) : eq1 (gobsDSLP (ret a)) (ret a).
  Proof.
    apply deq1. intros P o.
    rewrite gobsDSLP_get, dget_ret. split.
    - intros H i Ho. exact (H i (proj2 (grel_ret a i o) Ho)).
    - intros H i Hg. exact (H i (proj1 (grel_ret a i o) Hg)).
  Qed.

  Theorem gobsDSLP_bind {A B} (x : M A) (f : A -> M B) :
    eq1 (gobsDSLP (bind x f)) (bind (gobsDSLP x) (fun a => gobsDSLP (f a))).
  Proof.
    apply deq1. intros P o.
    rewrite gobsDSLP_get, dget_bind.
    assert (Hk : forall a i' o', drel (gobsDSLP (f a)) i' o' <-> grel (f a) i' o')
      by (intros; apply gobsDSLP_rel).
    split.
    - intros H w Hs. apply gobsDSLP_get. intros i Hx. apply H.
      apply grel_bind. exists w. split; [ exact Hx |].
      exact (proj1 (ostep_proper _ _ (fun a i' o' => Hk a i' o') w o) Hs).
    - intros H i Hg. apply grel_bind in Hg. destruct Hg as [w [Hx Hs]].
      refine (proj1 (gobsDSLP_get x P w) (H w _) i Hx).
      exact (proj2 (ostep_proper _ _ (fun a i' o' => Hk a i' o') w o) Hs).
  Qed.

End GenericDSLP.

(* ================================================================= *)
(** ** THE BASE: [SetM].  The only hand-written denotation.           *)
(* ================================================================= *)

Definition OShape_Id : OShape unit (fun A => A).
Proof.
  refine {| oeta := fun A _ a => a ; ostep := fun A B k w o => k w tt o |}.
  intros A B k k' H w o. apply H.
Defined.

Definition GRel_SetM : @GRel SetM _ unit (fun A => A) OShape_Id.
Proof.
  refine {| grel A m i o := m o |}.
  - intros A a i o. cbn. split; intro H; exact H.
  - intros A B x f i o. cbn. split.
    + intros [a [Hx Hf]]. exists a. split; [ exact Hx | exact Hf ].
    + intros [a [Hx Hf]]. exists a. split; [ exact Hx | exact Hf ].
Defined.

(* ================================================================= *)
(** ** STEP: optionT, KEEPING the layer.  [(I,Out) |-> (I,Out o option)] *)
(* ================================================================= *)

Section OptionStep.
  Context {I : Type} {Out : Type -> Type} {OS : OShape I Out}.

  Definition OShape_optionT : OShape I (fun A => Out (option A)).
  Proof.
    refine {| oeta := fun A i a => @oeta I Out OS (option A) i (Some a) ;
              ostep := fun A B k w o =>
                @ostep I Out OS (option A) (option B)
                  (fun oa i' o' =>
                     match oa with
                     | Some a => k a i' o'
                     | None => o' = @oeta I Out OS (option B) i' None
                     end) w o |}.
    intros A B k k' H w o.
    apply (@ostep_proper I Out OS (option A) (option B)).
    intros [a|] i' o'; [ apply H | reflexivity ].
  Defined.

  Context {M : Type -> Type} {MM : Monad M} (RM : @GRel M MM I Out OS).
  #[local] Existing Instance Monad_optionT.

  Definition GRel_optionT
    : @GRel (optionT M) _ I (fun A => Out (option A)) OShape_optionT.
  Proof.
    refine {| grel A m i o := @grel M MM I Out OS RM (option A) (unOptionT m) i o |}.
    - intros A a i o.
      exact (@grel_ret M MM I Out OS RM (option A) (Some a) i o).
    - intros A B x f i o.
      etransitivity;
        [ exact (@grel_bind M MM I Out OS RM (option A) (option B) (unOptionT x)
                   (fun oa => match oa with
                              | Some a => unOptionT (f a)
                              | None => @ret M MM (option B) None
                              end) i o) |].
      assert (Hc : forall (oa : option A) (i' : I) (o' : Out (option B)),
        @grel M MM I Out OS RM (option B)
          (match oa with
           | Some a => unOptionT (f a)
           | None => @ret M MM (option B) None end) i' o'
        <-> match oa with
            | Some a => @grel M MM I Out OS RM (option B) (unOptionT (f a)) i' o'
            | None => o' = @oeta I Out OS (option B) i' None
            end).
      { intros [a|] i' o'; [ reflexivity
        | exact (@grel_ret M MM I Out OS RM (option B) None i' o') ]. }
      split; intros [w [H1 H2]]; exists w; split; try exact H1.
      + exact (proj1 (@ostep_proper I Out OS (option A) (option B) _ _ Hc w o) H2).
      + exact (proj2 (@ostep_proper I Out OS (option A) (option B) _ _ Hc w o) H2).
  Defined.

End OptionStep.

(* ================================================================= *)
(** ** STEP: stateT.  [(I, Out) |-> (I * S, Out(- * S))]              *)
(* ================================================================= *)

Section StateStep.
  Context {I : Type} {Out : Type -> Type} {OS : OShape I Out}.
  Variable S : Type.

  Definition OShape_stateT : OShape (I * S)%type (fun A => Out (A * S)%type).
  Proof.
    refine {| oeta := fun A p a => @oeta I Out OS (A * S)%type (fst p) (a, snd p) ;
              ostep := fun A B k w o =>
                @ostep I Out OS (A * S)%type (B * S)%type
                  (fun q i2 o2 => k (fst q) (i2, snd q) o2) w o |}.
    intros A B k k' H w o.
    apply (@ostep_proper I Out OS (A * S)%type (B * S)%type).
    intros q i2 o2. apply H.
  Defined.

  Context {M : Type -> Type} {MM : Monad M} (RM : @GRel M MM I Out OS).
  #[local] Existing Instance Monad_stateT.

  Definition GRel_stateT
    : @GRel (stateT S M) _ (I * S)%type (fun A => Out (A * S)%type) OShape_stateT.
  Proof.
    refine {| grel A m p o :=
                @grel M MM I Out OS RM (A * S)%type (runStateT m (snd p)) (fst p) o |}.
    - intros A a p o.
      exact (@grel_ret M MM I Out OS RM (A * S)%type (a, snd p) (fst p) o).
    - intros A B x f p o.
      etransitivity;
        [ exact (@grel_bind M MM I Out OS RM (A * S)%type (B * S)%type
                   (runStateT x (snd p))
                   (fun vs => let (v, s2) := vs in runStateT (f v) s2) (fst p) o) |].
      assert (Hc : forall (q : (A * S)%type) (i2 : I) (o2 : Out (B * S)%type),
        @grel M MM I Out OS RM (B * S)%type
          (let (v, s2) := q in runStateT (f v) s2) i2 o2
        <-> @grel M MM I Out OS RM (B * S)%type
          (runStateT (f (fst q)) (snd q)) i2 o2).
      { intros [a s2] i2 o2. reflexivity. }
      split; intros [w [H1 H2]]; exists w; split; try exact H1.
      + exact (proj1 (@ostep_proper I Out OS (A * S)%type (B * S)%type _ _ Hc w o) H2).
      + exact (proj2 (@ostep_proper I Out OS (A * S)%type (B * S)%type _ _ Hc w o) H2).
  Defined.

End StateStep.

(* ================================================================= *)
(** ** STEP: optionT, SLICING the layer.                              *)
(*                                                                    *)
(*  The SP counterpart of the WP side's [none : L].  Sound because     *)
(*  [Some] is a sub-arrow: closed under composition, and nothing       *)
(*  outside it reaches it -- that is the [congruence] below.           *)
(* ================================================================= *)

Definition GRel_divnd_slice : @GRel (optionT SetM) _ unit (fun A => A) OShape_Id.
Proof.
  refine {| grel A m i o := @unOptionT SetM A m (Some o) |}.
  - intros A a i o. cbn. split; intro H; congruence.
  - intros A B x f i o. cbn. split.
    + intros [oa [Hx Hf]]. destruct oa as [a|]; cbn in *.
      * exists a. split; [ exact Hx | exact Hf ].
      * congruence.
    + intros [a [Hx Hf]]. exists (Some a). split; [ exact Hx | exact Hf ].
Defined.

(* ================================================================= *)
(** ** Carrier instances at the state shape                           *)
(* ================================================================= *)

Definition OShape_St (S : Type) : OShape S (fun A => (A * S)%type).
Proof.
  refine {| oeta := fun A s a => (a, s) ;
            ostep := fun A B k w o => k (fst w) (snd w) o |}.
  intros A B k k' H w o. apply H.
Defined.

Definition ASPCar_St (S : Type)
  : @ASPCar S (fun A => (A * S)%type) (OShape_St S) (ASPSt S) _ _.
Proof.
  refine {| aof := fun A R => aspOfRelSt R ;
            aget := fun A w P o => getASPSt w P o |}.
  - intros A R P o. apply getASPSt_of.
  - intros A m n. apply eq1_ASPSt_get.
  - intros A x P o. apply getASPSt_ret.
  - intros A B m k P o. etransitivity; [ exact (getASPSt_bind _ m k P o) |]. split.
    + intros [a [s' [Hm Hk]]]. exists (a, s'). split; [ exact Hm | exact Hk ].
    + intros [[a s'] [Hm Hk]]. exists a, s'. split; [ exact Hm | exact Hk ].
Defined.

Definition DSLPCar_St (S : Type)
  : @DSLPCar S (fun A => (A * S)%type) (OShape_St S) (DSLPSt S) _ _.
Proof.
  refine {| dof := fun A R => dslpOfRelSt R ;
            dget := fun A w P o => getDSLPSt w P o ;
            drel := fun A w i o => dslpRelSt w i o |}.
  - intros A R P o. apply getDSLPSt_of.
  - intros A R i o. apply dslpRelSt_of.
  - intros A m n. apply eq1_DSLPSt_get.
  - intros A x P o. apply getDSLPSt_ret.
  - intros A B m k P o. etransitivity; [ exact (getDSLPSt_bind _ m k P o) |]. split.
    + intros H w Hs. destruct w as [a s']. exact (H a s' Hs).
    + intros H a s' Hs. exact (H (a, s') Hs).
Defined.

(* ================================================================= *)
(** ** Carrier instances at the pure shape                            *)
(*                                                                    *)
(*  [ASP] / [DSLP] read against a bare [Prop] rather than an           *)
(*  [I -> Prop], so these pull the precondition back along [I = unit]. *)
(*  The only friction is [aget_bind]: [getASP_bind] normalises the     *)
(*  continuation's precondition to [True] where the generic statement  *)
(*  gives [tt = tt].  [getASP_mono] bridges it.                        *)
(* ================================================================= *)

Definition ASPCar_Pure : @ASPCar unit (fun A => A) OShape_Id ASP Monad_ASP Eq1_ASP.
Proof.
  refine {| aof := fun A R => aspOfPred (R tt) ;
            aget := fun A w P o => getASP w (P tt) o |}.
  - intros A R P o. rewrite getASP_of. split.
    + intros [Hp HR]. exists tt. split; [ exact Hp | exact HR ].
    + intros [[] [Hp HR]]. split; [ exact Hp | exact HR ].
  - intros A m n. rewrite eq1_ASP_get. split.
    + intros H P o. apply H.
    + intros H p o. exact (H (fun _ => p) o).
  - intros A x P o. cbn [oeta OShape_Id]. rewrite getASP_ret. split.
    + intros [Hp Hx]. exists tt. split; [ exact Hp | symmetry; exact Hx ].
    + intros [[] [Hp Ho]]. split; [ exact Hp | symmetry; exact Ho ].
  - intros A B m k P o. cbn [ostep OShape_Id].
    etransitivity; [ exact (getASP_bind m k (P tt) o) |]. split.
    + intros [a [Hm Hk]]. exists a. split; [ exact Hm |].
      exact (getASP_mono (k a) True (tt = tt) o (fun _ => eq_refl) Hk).
    + intros [a [Hm Hk]]. exists a. split; [ exact Hm |].
      exact (getASP_mono (k a) (tt = tt) True o (fun _ => I) Hk).
Defined.

Definition DSLPCar_Pure
  : @DSLPCar unit (fun A => A) OShape_Id DSLP Monad_DSLP Eq1_DSLP.
Proof.
  refine {| dof := fun A R => dslpOfPred (R tt) ;
            dget := fun A w P o => getDSLP w (P tt) o ;
            drel := fun A w i o => dslpRel w i o |}.
  - intros A R P o. rewrite getDSLP_of. split.
    + intros H [] HR. exact (H HR).
    + intros H HR. exact (H tt HR).
  - intros A R i o. destruct i. exact (dslpRel_ofRel (fun _ : unit => R tt) tt o).
  - intros A m n. rewrite eq1_DSLP_get. split.
    + intros H P o. apply H.
    + intros H p o. exact (H (fun _ => p) o).
  - intros A x P o. cbn [oeta OShape_Id].
    etransitivity; [ exact (getDSLP_ret x (P tt) o) |]. split.
    + intros H [] Ho. apply H. symmetry. exact Ho.
    + intros H Hx. exact (H tt (eq_sym Hx)).
  - intros A B m k P o. cbn [ostep OShape_Id].
    exact (getDSLP_bind m k (P tt) o).
Defined.

(* ================================================================= *)
(** ** The ASP carrier, from an arrow STACK rather than per shape     *)
(* ================================================================= *)

From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPArrowCore ASPArrowRel.

Section ASPOfStack.
  Context {I : Type} {Out : Type -> Type} {OS : OShape I Out}.
  Context {MC : Monad (fun A => ASPArr I (Out A))}
          {EC : Eq1 (fun A => ASPArr I (Out A))}.

  Hypothesis seq1 : forall A (m n : ASPArr I (Out A)),
    @eq1 (fun A => ASPArr I (Out A)) EC A m n
    <-> (forall P o, getASPArr m P o <-> getASPArr n P o).
  Hypothesis srel_ret : forall A (x : A) i o,
    aspRel (@ret _ MC A x) i o <-> o = oeta i x.
  Hypothesis srel_bind : forall A B (m : ASPArr I (Out A)) (k : A -> ASPArr I (Out B)) i o,
    aspRel (@bind _ MC A B m k) i o
    <-> exists w, aspRel m i w /\ ostep (fun a i' => aspRel (k a) i') w o.

  Definition ASPCar_ofStack : @ASPCar I Out OS (fun A => ASPArr I (Out A)) MC EC.
  Proof.
    refine {| aof := fun A R => ofRelASPArr R ;
              aget := fun A w P o => getASPArr w P o |}.
    - intros A R P o. rewrite get_aspRel. split.
      + intros [i [HP Hr]]. exists i.
        split; [ exact HP | exact (proj1 (aspRel_ofRel R i o) Hr) ].
      + intros [i [HP HR]]. exists i.
        split; [ exact HP | exact (proj2 (aspRel_ofRel R i o) HR) ].
    - exact seq1.
    - intros A x P o. rewrite get_aspRel. split.
      + intros [i [HP Hr]]. exists i.
        split; [ exact HP | exact (proj1 (srel_ret A x i o) Hr) ].
      + intros [i [HP Ho]]. exists i.
        split; [ exact HP | exact (proj2 (srel_ret A x i o) Ho) ].
    - intros A B m k P o.
      assert (Hk : forall a i' o',
                 getASPArr (k a) (fun j => j = i') o' <-> aspRel (k a) i' o').
      { intros a i' o'. rewrite get_aspRel. split.
        - intros [j [-> Hr]]. exact Hr.
        - intro Hr. exists i'. split; [ reflexivity | exact Hr ]. }
      rewrite get_aspRel. split.
      + intros [i [HP Hr]]. apply srel_bind in Hr. destruct Hr as [w [Hm Hs]].
        exists w. split.
        * apply get_aspRel. exists i. split; [ exact HP | exact Hm ].
        * exact (proj2 (ostep_proper _ _ (fun a i' o' => Hk a i' o') w o) Hs).
      + intros [w [Hm Hs]]. apply get_aspRel in Hm. destruct Hm as [i [HP Hmw]].
        exists i. split; [ exact HP |]. apply srel_bind. exists w. split.
        * exact Hmw.
        * exact (proj1 (ostep_proper _ _ (fun a i' o' => Hk a i' o') w o) Hs).
  Defined.

End ASPOfStack.

(* ================================================================= *)
(** ** The carrier steps, written out at each shape                   *)
(*                                                                    *)
(*  Each is [ofRelASPArr] / [getASPArr] at the transformed shape, with *)
(*  its four fields discharged from [get_aspRel] and [aspRel_ofRel]    *)
(*  (both already arrow-generic) plus that level's [sret] / [sbind].   *)
(*                                                                    *)
(*  UNLIKE [GRel_optionT] / [GRel_stateT], which derive their laws,    *)
(*  these TAKE [sret] / [sbind]: the computation-side transformers     *)
(*  unfold definitionally ([unOptionT (bind x f) = ...]) whereas       *)
(*  [bind_arrow] goes through [arr_app] and does not.                  *)
(* ================================================================= *)

Section OptionCarrierStep.
  Context {I : Type} {Out : Type -> Type} {OS : OShape I Out}.
  Context (MC : Monad (fun A => ASPArr I (Out (option A))))
          (EC : Eq1 (fun A => ASPArr I (Out (option A)))).

  Hypothesis seq1 : forall A (m n : ASPArr I (Out (option A))),
    @eq1 (fun A => ASPArr I (Out (option A))) EC A m n
    <-> (forall P o, getASPArr m P o <-> getASPArr n P o).
  Hypothesis sret : forall A (x : A) i o,
    aspRel (@ret _ MC A x) i o
    <-> o = @oeta I (fun A => Out (option A)) (@OShape_optionT I Out OS) A i x.
  Hypothesis sbind : forall A B (m : ASPArr I (Out (option A)))
                                (k : A -> ASPArr I (Out (option B))) i o,
    aspRel (@bind _ MC A B m k) i o
    <-> exists w, aspRel m i w
                  /\ @ostep I (fun A => Out (option A)) (@OShape_optionT I Out OS)
                       A B (fun a i' => aspRel (k a) i') w o.

  Definition ASPCarrier_optionT
    : @ASPCar I (fun A => Out (option A)) (@OShape_optionT I Out OS)
        (fun A => ASPArr I (Out (option A))) MC EC.
  Proof.
    refine {| aof := fun A R => ofRelASPArr R ;
              aget := fun A w P o => getASPArr w P o |}.
    - intros A R P o. rewrite get_aspRel. split.
      + intros [i [HP Hr]]. exists i.
        split; [ exact HP | exact (proj1 (aspRel_ofRel R i o) Hr) ].
      + intros [i [HP HR]]. exists i.
        split; [ exact HP | exact (proj2 (aspRel_ofRel R i o) HR) ].
    - exact seq1.
    - intros A x P o. rewrite get_aspRel. split.
      + intros [i [HP Hr]]. exists i.
        split; [ exact HP | exact (proj1 (sret A x i o) Hr) ].
      + intros [i [HP Ho]]. exists i.
        split; [ exact HP | exact (proj2 (sret A x i o) Ho) ].
    - intros A B m k P o.
      assert (Hk : forall a i' o',
                 getASPArr (k a) (fun j => j = i') o' <-> aspRel (k a) i' o').
      { intros a i' o'. rewrite get_aspRel. split.
        - intros [j [-> Hr]]. exact Hr.
        - intro Hr. exists i'. split; [ reflexivity | exact Hr ]. }
      rewrite get_aspRel. split.
      + intros [i [HP Hr]]. apply sbind in Hr. destruct Hr as [w [Hm Hs]].
        exists w. split.
        * apply get_aspRel. exists i. split; [ exact HP | exact Hm ].
        * exact (proj2 (@ostep_proper I (fun A => Out (option A))
                          (@OShape_optionT I Out OS) A B _ _
                          (fun a i' o' => Hk a i' o') w o) Hs).
      + intros [w [Hm Hs]]. apply get_aspRel in Hm. destruct Hm as [i [HP Hmw]].
        exists i. split; [ exact HP |]. apply sbind. exists w. split.
        * exact Hmw.
        * exact (proj1 (@ostep_proper I (fun A => Out (option A))
                          (@OShape_optionT I Out OS) A B _ _
                          (fun a i' o' => Hk a i' o') w o) Hs).
  Defined.

End OptionCarrierStep.

Section StateCarrierStep.
  Context {I : Type} {Out : Type -> Type} {OS : OShape I Out}.
  Variable S : Type.
  Context (MC : Monad (fun A => ASPArr (I * S)%type (Out (A * S)%type)))
          (EC : Eq1 (fun A => ASPArr (I * S)%type (Out (A * S)%type))).

  Hypothesis seq1 : forall A (m n : ASPArr (I * S)%type (Out (A * S)%type)),
    @eq1 (fun A => ASPArr (I * S)%type (Out (A * S)%type)) EC A m n
    <-> (forall P o, getASPArr m P o <-> getASPArr n P o).
  Hypothesis sret : forall A (x : A) i o,
    aspRel (@ret _ MC A x) i o
    <-> o = @oeta (I * S)%type (fun A => Out (A * S)%type)
              (@OShape_stateT I Out OS S) A i x.
  Hypothesis sbind : forall A B (m : ASPArr (I * S)%type (Out (A * S)%type))
                                (k : A -> ASPArr (I * S)%type (Out (B * S)%type)) i o,
    aspRel (@bind _ MC A B m k) i o
    <-> exists w, aspRel m i w
                  /\ @ostep (I * S)%type (fun A => Out (A * S)%type)
                       (@OShape_stateT I Out OS S) A B
                       (fun a i' => aspRel (k a) i') w o.

  Definition ASPCarrier_stateT
    : @ASPCar (I * S)%type (fun A => Out (A * S)%type) (@OShape_stateT I Out OS S)
        (fun A => ASPArr (I * S)%type (Out (A * S)%type)) MC EC.
  Proof.
    refine {| aof := fun A R => ofRelASPArr R ;
              aget := fun A w P o => getASPArr w P o |}.
    - intros A R P o. rewrite get_aspRel. split.
      + intros [i [HP Hr]]. exists i.
        split; [ exact HP | exact (proj1 (aspRel_ofRel R i o) Hr) ].
      + intros [i [HP HR]]. exists i.
        split; [ exact HP | exact (proj2 (aspRel_ofRel R i o) HR) ].
    - exact seq1.
    - intros A x P o. rewrite get_aspRel. split.
      + intros [i [HP Hr]]. exists i.
        split; [ exact HP | exact (proj1 (sret A x i o) Hr) ].
      + intros [i [HP Ho]]. exists i.
        split; [ exact HP | exact (proj2 (sret A x i o) Ho) ].
    - intros A B m k P o.
      assert (Hk : forall a i' o',
                 getASPArr (k a) (fun j => j = i') o' <-> aspRel (k a) i' o').
      { intros a i' o'. rewrite get_aspRel. split.
        - intros [j [-> Hr]]. exact Hr.
        - intro Hr. exists i'. split; [ reflexivity | exact Hr ]. }
      rewrite get_aspRel. split.
      + intros [i [HP Hr]]. apply sbind in Hr. destruct Hr as [w [Hm Hs]].
        exists w. split.
        * apply get_aspRel. exists i. split; [ exact HP | exact Hm ].
        * exact (proj2 (@ostep_proper (I * S)%type (fun A => Out (A * S)%type)
                          (@OShape_stateT I Out OS S) A B _ _
                          (fun a i' o' => Hk a i' o') w o) Hs).
      + intros [w [Hm Hs]]. apply get_aspRel in Hm. destruct Hm as [i [HP Hmw]].
        exists i. split; [ exact HP |]. apply sbind. exists w. split.
        * exact Hmw.
        * exact (proj1 (@ostep_proper (I * S)%type (fun A => Out (A * S)%type)
                          (@OShape_stateT I Out OS S) A B _ _
                          (fun a i' o' => Hk a i' o') w o) Hs).
  Defined.

End StateCarrierStep.

(* ================================================================= *)
(** ** The carriers, built by applying the steps                      *)
(* ================================================================= *)

(** The base: no step applies, so it goes through [ASPCar_ofStack]
    directly -- the only remaining use of that helper. *)
Definition ASPCarrier_base
  : @ASPCar unit (fun A => A) OShape_Id ASP Monad_ASP Eq1_ASP.
Proof.
  refine (@ASPCar_ofStack unit (fun A => A) OShape_Id Monad_ASP Eq1_ASP _ _ _).
  - intros A m n. reflexivity.
  - intros A x i o. destruct i. cbn [oeta OShape_Id].
    rewrite aspRel_retASP. split; intro H; symmetry; exact H.
  - intros A B m k i o. destruct i. cbn [ostep OShape_Id].
    exact (aspRel_bindASP m k tt o).
Defined.

(** [stateT] on top of the base. *)
Definition ASPCarrier_St (S : Type)
  : @ASPCar (unit * S)%type (fun A => (A * S)%type)
      (@OShape_stateT unit (fun A => A) OShape_Id S)
      (ASPSt S) (Monad_ASPSt S) (Eq1_ASPSt S).
Proof.
  refine (@ASPCarrier_stateT unit (fun A => A) OShape_Id S
            (Monad_ASPSt S) (Eq1_ASPSt S) _ _ _).
  - intros A m n. reflexivity.
  - intros A x [[] s] o. cbn [oeta OShape_stateT OShape_Id fst snd].
    exact (aspRelS_ret _ x tt s o).
  - intros A B m k [[] s] o. cbn [ostep OShape_stateT OShape_Id fst snd].
    etransitivity; [ exact (aspRelS_bind _ m k tt s o) |]. split.
    + intros [a [s' [Hm Hk]]]. exists (a, s'). split; [ exact Hm | exact Hk ].
    + intros [[a s'] [Hm Hk]]. exists a, s'. split; [ exact Hm | exact Hk ].
Defined.

(** [stateT] on top of [optionT] on top of the base -- the composition is
    visible in the shape argument. *)
Definition ASPCarrier_StExc (S : Type)
  : @ASPCar (unit * S)%type (fun A => option (A * S)%type)
      (@OShape_stateT unit (fun A => option A)
         (@OShape_optionT unit (fun A => A) OShape_Id) S)
      (ASPStExc S) (Monad_ASPStExc S) (Eq1_ASPStExc S).
Proof.
  refine (@ASPCarrier_stateT unit (fun A => option A)
            (@OShape_optionT unit (fun A => A) OShape_Id) S
            (Monad_ASPStExc S) (Eq1_ASPStExc S) _ _ _).
  - intros A m n. reflexivity.
  - intros A x [[] s] o.
    cbn [oeta OShape_stateT OShape_optionT OShape_Id fst snd].
    exact (aspRelE_ret _ x tt s o).
  - intros A B m k [[] s] o.
    cbn [ostep OShape_stateT OShape_optionT OShape_Id fst snd].
    etransitivity; [ exact (aspRelE_bind _ m k tt s o) |].
    split; intros [w [Hm Hk]]; exists w; split; try exact Hm;
      destruct w as [[a s2]|]; exact Hk.
Defined.

(** Previous names, kept so existing clients are unaffected. *)
Definition ASPCar_PureS := ASPCarrier_base.
Definition ASPCar_StS := ASPCarrier_St.
Definition ASPCar_StExcS := ASPCarrier_StExc.
