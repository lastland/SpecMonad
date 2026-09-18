(** * Dijkstra monads of the ASP and DSLP observations of [stdivnd]

    The terminating-slice counterpart of
    [Dijkstra_StDivExcNonDet_SPStExc.v]: DM4All's [Dtheta] over the two
    observations of [EffectObservations/SP/StDivNonDet_SPSt.v] that carry
    it.

    The construction is stated against [OrderedMonad]
    ([Classes/OrderedMonad.v]) rather than against a preorder, an [eq1]
    inclusion and a [bind] monotonicity hypothesis spelled out separately:
    those three ARE its fields, and [SpecificationMonads.v] already proves
    the instances for both spec monads used here ([OrderedMonad_ASPSt],
    [OrderedMonad_DSLPSt]).  So the enrichment work the [option]-indexed
    file does inline is here a citation.

    The observation and its two morphism laws are bundled the same way, as
    [EffObs], so a client never passes laws around. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Coq Require Import Morphisms RelationClasses Relation_Definitions.
From Incorrectness.Classes Require Import OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad SpecificationMonads.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  BaseGaloisConnections NewGaloisConnections.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivNonDet_SPSt.

Import MonadNotation.
Open Scope monad_scope.
Import StASP StDSLP StSP.
Import TermSliceObs.

(* ================================================================= *)
(** ** The Dijkstra monad of an effect observation                   *)
(* ================================================================= *)

(** An effect observation: a map with the two monad-morphism laws. *)
Class EffObs (M W : Type -> Type) {MM : Monad M} {MW : Monad W} {EW : Eq1 W} := {
  obs : forall {A}, M A -> W A ;
  obs_ret : forall A (a : A), eq1 (obs (ret a)) (ret a) ;
  obs_bind : forall A B (m : M A) (f : A -> M B),
    eq1 (obs (bind m f)) (bind (obs m) (fun a => obs (f a)))
}.

(** For a monad morphism [obs : M ~> W] into an ordered specification
    monad,

        DM A w := { m : M A | obs m <= w }

    with [ret] indexed by [ret^W], [bind] by [bind^W], and weakening along
    the order.  [DMop] is the opposite indexing, which is what the [Under]
    (incorrectness) triples need.  Nothing here is specific to [stdivnd] or
    to the SP side; the section is generic in both monads. *)

Section DijkstraOfObservation.

  Context {M W : Type -> Type} {MM : Monad M} {MW : Monad W} {EW : Eq1 W}.
  Context {EEW : @Eq1Equivalence W MW EW}.

  Context (ordW : forall A, relation (W A)) {OW : OrderedMonad W ordW}.
  Context {OB : @EffObs M W MM MW EW}.

  #[local] Existing Instance om_preorder.

  (** *** [DM]: the computation refines the specification *)

  Definition DM {A} (w : W A) : Type := { m : M A | ordW A (obs m) w }.

  #[program] Definition DM_ret {A} (a : A) : DM (ret a) := @ret M MM A a.
  Next Obligation. apply om_eq1. apply obs_ret. Qed.

  #[program] Definition DM_bind {A B} {w : W A} {wf : A -> W B}
    (m : DM w) (f : forall a, DM (wf a)) : DM (bind w wf) :=
    @bind M MM A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [ apply om_eq1; apply obs_bind |].
    apply om_bind; [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  (** The rule of consequence. *)
  #[program] Definition DM_wkn {A} {w w' : W A} (Hle : ordW A w w') (m : DM w)
    : DM w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact (proj2_sig m) | exact Hle ]. Qed.

  (** Every computation meets its own observation -- DM4All's [lift]. *)
  #[program] Definition DM_lift {A} (m : M A) : DM (obs m) := m.
  Next Obligation. reflexivity. Qed.

  (** *** [DMop]: the dual indexing *)

  Definition DMop {A} (w : W A) : Type := { m : M A | ordW A w (obs m) }.

  #[program] Definition DMop_ret {A} (a : A) : DMop (ret a) := @ret M MM A a.
  Next Obligation. apply om_eq1. symmetry. apply obs_ret. Qed.

  #[program] Definition DMop_bind {A B} {w : W A} {wf : A -> W B}
    (m : DMop w) (f : forall a, DMop (wf a)) : DMop (bind w wf) :=
    @bind M MM A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply om_eq1; symmetry; apply obs_bind ].
    apply om_bind; [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition DMop_wkn {A} {w w' : W A} (Hle : ordW A w' w) (m : DMop w)
    : DMop w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition DMop_lift {A} (m : M A) : DMop (obs m) := m.
  Next Obligation. reflexivity. Qed.

End DijkstraOfObservation.

(* ================================================================= *)
(** ** The two observations, as instances                            *)
(* ================================================================= *)

(** Each is the observation of [StDivNonDet_SPSt.v] together with the two
    laws that file proves.  Nothing else is supplied. *)

#[global] Instance EffObs_ASP (S : Type) : EffObs (stdivnd S) (ASPSt S) := {
  obs A m := obsASP m ;
  obs_ret := @obsASP_ret S ;
  obs_bind := @obsASP_bind S }.

#[global] Instance EffObs_DSLP (S : Type) : EffObs (stdivnd S) (DSLPSt S) := {
  obs A m := obsDSLP m ;
  obs_ret := @obsDSLP_ret S ;
  obs_bind := @obsDSLP_bind S }.

(** The [Pos]-enrichment of both spec monads, from [SpecificationMonads.v]. *)
#[local] Existing Instance OrderedMonad_ASPSt.
#[local] Existing Instance OrderedMonad_DSLPSt.

(* ================================================================= *)
(** ** The two instantiations                                        *)
(* ================================================================= *)

Definition Dasp {S A} (w : ASPSt S A) : Type :=
  DM (fun A => @ordASPSt S A) w.
Definition Dasp_op {S A} (w : ASPSt S A) : Type :=
  DMop (fun A => @ordASPSt S A) w.

Definition Ddslp {S A} (w : DSLPSt S A) : Type :=
  DM (fun A => @ordDSLPSt S A) w.
Definition Ddslp_op {S A} (w : DSLPSt S A) : Type :=
  DMop (fun A => @ordDSLPSt S A) w.

Section Operations.
  Variable S : Type.

  (** Both monads' operations are the generic ones; only the observation
      and its two laws change. *)

  Definition Dasp_ret {A} (a : A) : Dasp (ret a) :=
    DM_ret (fun A => @ordASPSt S A) a.

  Definition Dasp_bind {A B} {w : ASPSt S A} {wf : A -> ASPSt S B}
    (m : Dasp w) (f : forall a, Dasp (wf a)) : Dasp (bind w wf) :=
    DM_bind (fun A => @ordASPSt S A) m f.

  Definition Dasp_wkn {A} {w w' : ASPSt S A} (H : ordASPSt w w') (m : Dasp w)
    : Dasp w' :=
    DM_wkn (fun A => @ordASPSt S A) H m.

  Definition Dasp_lift {A} (m : stdivnd S A) : Dasp (obsASP m) :=
    DM_lift (fun A => @ordASPSt S A) m.

  Definition Ddslp_ret {A} (a : A) : Ddslp (ret a) :=
    DM_ret (fun A => @ordDSLPSt S A) a.

  Definition Ddslp_bind {A B} {w : DSLPSt S A} {wf : A -> DSLPSt S B}
    (m : Ddslp w) (f : forall a, Ddslp (wf a)) : Ddslp (bind w wf) :=
    DM_bind (fun A => @ordDSLPSt S A) m f.

  Definition Ddslp_op_ret {A} (a : A) : Ddslp_op (ret a) :=
    DMop_ret (fun A => @ordDSLPSt S A) a.

  Definition Ddslp_op_bind {A B} {w : DSLPSt S A} {wf : A -> DSLPSt S B}
    (m : Ddslp_op w) (f : forall a, Ddslp_op (wf a)) : Ddslp_op (bind w wf) :=
    DMop_bind (fun A => @ordDSLPSt S A) m f.

  Definition Ddslp_op_wkn {A} {w w' : DSLPSt S A} (H : ordDSLPSt w' w)
    (m : Ddslp_op w) : Ddslp_op w' :=
    DMop_wkn (fun A => @ordDSLPSt S A) H m.

  Definition Ddslp_op_lift {A} (m : stdivnd S A) : Ddslp_op (obsDSLP m) :=
    DMop_lift (fun A => @ordDSLPSt S A) m.

End Operations.

(* ================================================================= *)
(** ** Triples as Dijkstra typings                                   *)
(* ================================================================= *)

(** The two (observation, direction) pairs with an in-monad comparison
    target in [StDivNonDet_SPSt.v] -- ASP/[Over] and DSLP/[Under] -- are
    Dijkstra typings, and both are exact: the [DefEq] theorems there ARE
    the membership conditions. *)

Section TripleBridges.

  Variable S : Type.

  #[program] Definition ofTripleASPOver {A} (prog : stdivnd S A)
    (pre : S -> Prop) (post : A * S -> Prop)
    (H : tripleASP prog Over pre post) : Dasp (pp2asp_over pre post) := prog.
  Next Obligation. exact (proj1 (tripleASPDefEq prog Over pre post) H). Qed.

  Lemma toTripleASPOver {A} (pre : S -> Prop) (post : A * S -> Prop)
    (d : Dasp (pp2asp_over pre post)) :
    tripleASP (proj1_sig d) Over pre post.
  Proof.
    exact (proj2 (tripleASPDefEq (proj1_sig d) Over pre post) (proj2_sig d)).
  Qed.

  #[program] Definition ofTripleDSLPUnder {A} (prog : stdivnd S A)
    (pre : S -> Prop) (post : A * S -> Prop)
    (H : tripleDSLP prog Under pre post)
    : Ddslp_op (pp2dslp_under pre post) := prog.
  Next Obligation. exact (proj1 (tripleDSLPDefEq prog Under pre post) H). Qed.

  Lemma toTripleDSLPUnder {A} (pre : S -> Prop) (post : A * S -> Prop)
    (d : Ddslp_op (pp2dslp_under pre post)) :
    tripleDSLP (proj1_sig d) Under pre post.
  Proof.
    exact (proj2 (tripleDSLPDefEq (proj1_sig d) Under pre post) (proj2_sig d)).
  Qed.

End TripleBridges.
