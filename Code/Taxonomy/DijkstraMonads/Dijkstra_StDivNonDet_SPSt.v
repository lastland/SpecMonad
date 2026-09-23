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
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers SpecificationMonads.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad.
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

(* ================================================================= *)
(** ** Probes: programs cut out by a relation                        *)
(* ================================================================= *)

(** The counterexamples below need programs with a prescribed
    reachability relation.  [ExampleProgramDefs.v]'s programs live over
    [stdivexcnd], which has a second [option] layer, so these are the
    terminating-slice analogues. *)

Definition progOf {S A} (R : S -> A * S -> Prop) : stdivnd S A :=
  mkStateT (fun s => @mkOptionT StExcNonDet.SetM _
    (fun o => match o with Some r => R s r | None => False end)).

Lemma progOf_outcomes {S A} (R : S -> A * S -> Prop) s r :
  unOptionT (runStateT (progOf R) s) (Some r) <-> R s r.
Proof. cbn. reflexivity. Qed.

(* ================================================================= *)
(** ** Membership in [Dasp_op] is a relation inclusion               *)
(* ================================================================= *)

(** Whatever the index [w] is, [DMop] membership compares [w]'s singleton
    values, state by state, with the reachability relation of the
    program: [SingletonProg] leaves the order nothing else to look at. *)
Lemma Dasp_op_relational {S A} (w : ASPSt S A) (prog : stdivnd S A) :
  ordASPSt w (obsASP prog)
  <-> (forall s r, getASPSt w (fun t => t = s) r ->
                   unOptionT (runStateT prog s) (Some r)).
Proof.
  split.
  - intros H s r Hw.
    destruct (proj1 (getProgASP_obsASP S prog (fun t => t = s) r)
                (H (fun t => t = s) r Hw)) as [s' [Heq Hr]].
    subst s'. exact Hr.
  - intros Hrel p r Hw.
    destruct (proj1 (StASP.getProg_singleton S w p r) Hw) as [s0 [Hp Hs]].
    apply getProgASP_obsASP. exists s0. split; [ exact Hp | exact (Hrel s0 r Hs) ].
Qed.

(** The [Under] index one would like to use. *)
#[program] Definition pp2asp_under {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : ASPSt S A :=
  fun p r => exists s, p s /\ (pre s /\ post r).
Next Obligation.
  intros p r. split.
  - intros [s [Hp H]]. exists s. split; [ exact Hp |].
    exists s. split; [ reflexivity | exact H ].
  - intros [s0 [Hp [s [Heq H]]]]. subst s.
    exists s0. split; [ exact Hp | exact H ].
Qed.

(** Membership at that index is STRICTLY STRONGER than the triple: the
    order quantifies over all preconditions, which forces EVERY
    [pre]-state to reach EVERY [post]-outcome, where the triple asks only
    that SOME [pre]-state does. *)
Lemma Dasp_op_under_iff {S A} (prog : stdivnd S A)
  (pre : S -> Prop) (post : A * S -> Prop) :
  ordASPSt (pp2asp_under pre post) (obsASP prog)
  <-> (forall s r, pre s -> post r -> unOptionT (runStateT prog s) (Some r)).
Proof.
  split.
  - intros H s r Hpre Hpost.
    destruct (proj1 (getProgASP_obsASP S prog (fun t => t = s) r)
                (H (fun t => t = s) r
                   (ex_intro _ s (conj eq_refl (conj Hpre Hpost)))))
      as [s' [Heq Hr]].
    subst s'. exact Hr.
  - intros H p r [s [Hp [Hpre Hpost]]].
    apply getProgASP_obsASP. exists s.
    split; [ exact Hp | exact (H s r Hpre Hpost) ].
Qed.

(* ================================================================= *)
(** ** No index at all represents an ASP [Under] triple              *)
(* ================================================================= *)

(** The three programs: [(tt, 0)] is reached from [0] by one, from [1] by
    the other, and by neither in the third. *)
Definition aspU1 : stdivnd nat unit :=
  progOf (fun s (r : unit * nat) => s = 0 /\ r = (tt, 0)).
Definition aspU2 : stdivnd nat unit :=
  progOf (fun s (r : unit * nat) => s = 1 /\ r = (tt, 0)).
Definition aspU0 : stdivnd nat unit :=
  progOf (fun (_ : nat) (_ : unit * nat) => False).

(** Membership is always a relation inclusion ([Dasp_op_relational]), so
    the class of programs cut out by a fixed index is closed under
    INTERSECTION of reachability relations.  The [Under] triple is not:
    [aspU1] and [aspU2] both satisfy it, their intersection [aspU0] does
    not.  So no [w] has the triple as its fibre -- a statement about the
    ASP ORDER, not about the Dijkstra construction. *)
Theorem no_asp_under_index :
  ~ exists w : ASPSt nat unit,
      forall prog : stdivnd nat unit,
        ordASPSt w (obsASP prog) <->
        tripleASP prog Under (fun _ => True) (fun r : unit * nat => r = (tt, 0)).
Proof.
  intros [w Hiff].
  assert (H1 : ordASPSt w (obsASP aspU1)).
  { apply Hiff. intros r ->. apply getProgASP_obsASP.
    exists 0. split; [ exact I |]. apply progOf_outcomes. split; reflexivity. }
  assert (H2 : ordASPSt w (obsASP aspU2)).
  { apply Hiff. intros r ->. apply getProgASP_obsASP.
    exists 1. split; [ exact I |]. apply progOf_outcomes. split; reflexivity. }
  pose proof (proj1 (Dasp_op_relational w aspU1) H1) as R1.
  pose proof (proj1 (Dasp_op_relational w aspU2) H2) as R2.
  assert (H0 : ordASPSt w (obsASP aspU0)).
  { apply Dasp_op_relational. intros s r Hw.
    pose proof (proj1 (progOf_outcomes _ s r) (R1 s r Hw)) as [E1 _].
    pose proof (proj1 (progOf_outcomes _ s r) (R2 s r Hw)) as [E2 _].
    subst s. discriminate E2. }
  destruct (proj1 (getProgASP_obsASP nat aspU0 (fun _ => True) (tt, 0))
              (proj1 (Hiff aspU0) H0 (tt, 0) eq_refl)) as [s [_ Hr]].
  exact (proj1 (progOf_outcomes _ s (tt, 0)) Hr).
Qed.

(* ================================================================= *)
(** ** The [At]-order is not a [Pos]-enrichment                      *)
(* ================================================================= *)

(** Could a DIFFERENT order repair this?  The fibre of an index is a
    principal up-set, so the question is whether the [Under] fibre can be
    made principal.  It can -- by comparing only the IMAGES of the fixed
    precondition, which is the [At]-order [gen_asp_under] uses.  But that
    order is not a [Pos]-enrichment: [bind] re-binds the precondition
    slot to the INTERMEDIATE states, so two continuations with the same
    image from [pre] can still disagree once run at the states the first
    argument actually produced. *)
Definition aspK0 : unit -> stdivnd nat unit :=
  fun _ => progOf (fun s (r : unit * nat) => s = 0 /\ r = (tt, 9)).
Definition aspK1 : unit -> stdivnd nat unit :=
  fun _ => progOf (fun s (r : unit * nat) => s = 1 /\ r = (tt, 9)).

Theorem ordASPStAt_bind_not_mono :
  ~ (forall A B (pre : nat -> Prop) (m : ASPSt nat A) (k k' : A -> ASPSt nat B),
        (forall a, ordASPStAt pre (k a) (k' a)) ->
        ordASPStAt pre (bind m k) (bind m k')).
Proof.
  intro Hmono.
  assert (Hk : forall a, ordASPStAt (fun _ : nat => True)
                           (obsASP (aspK0 a)) (obsASP (aspK1 a))).
  { intros a r Hr. apply getProgASP_obsASP in Hr.
    destruct Hr as [s [_ Hr]]. apply progOf_outcomes in Hr.
    destruct Hr as [_ ->]. apply getProgASP_obsASP.
    exists 1. split; [ exact I |]. apply progOf_outcomes. split; reflexivity. }
  specialize (Hmono unit unit (fun _ => True) (obsASP aspU1)
                (fun a => obsASP (aspK0 a)) (fun a => obsASP (aspK1 a)) Hk (tt, 9)).
  assert (Hin : getASPSt (bind (obsASP aspU1) (fun a => obsASP (aspK0 a)))
                  (fun _ => True) (tt, 9)).
  { apply (obsASP_bind nat aspU1 aspK0). apply getProgASP_obsASP.
    exists 0. split; [ exact I |]. apply (outcomes_bind nat).
    exists tt, 0. split; apply progOf_outcomes; split; reflexivity. }
  specialize (Hmono Hin).
  apply (obsASP_bind nat aspU1 aspK1) in Hmono.
  apply getProgASP_obsASP in Hmono. destruct Hmono as [s [_ Hr]].
  apply (outcomes_bind nat) in Hr. destruct Hr as [a [s' [Hx Hk2]]].
  apply progOf_outcomes in Hx. destruct Hx as [_ Heq].
  injection Heq as Heq. subst s'.
  apply progOf_outcomes in Hk2. destruct Hk2 as [Hn _]. discriminate Hn.
Qed.

(* ================================================================= *)
(** ** Typeable and untypeable ASP examples                          *)
(* ================================================================= *)

(** [setTo n] overwrites the state from every initial state; [setIf0 n]
    does so only from [0]. *)
Definition setTo (n : nat) : stdivnd nat unit :=
  progOf (fun (_ : nat) (r : unit * nat) => r = (tt, n)).
Definition setIf0 (n : nat) : stdivnd nat unit :=
  progOf (fun s (r : unit * nat) => s = 0 /\ r = (tt, n)).

(** *** ASP / [Over]: an exact typing *)

Theorem setTo42_over : tripleASP (setTo 42) Over (fun _ : nat => True)
                         (fun r : unit * nat => snd r = 42).
Proof.
  intros r Hr. apply getProgASP_obsASP in Hr. destruct Hr as [s [_ Hr]].
  apply progOf_outcomes in Hr. subst r. reflexivity.
Qed.

Definition setTo42_over_D :
  Dasp (pp2asp_over (fun _ : nat => True) (fun r : unit * nat => snd r = 42)) :=
  ofTripleASPOver nat (setTo 42) _ _ setTo42_over.

(** *** ASP / [Under]: typeable when EVERY [pre]-state reaches EVERY
    [post]-outcome *)

#[program] Definition setTo42_under_Dop :
  Dasp_op (pp2asp_under (fun _ : nat => True)
             (fun r : unit * nat => r = (tt, 42))) := setTo 42.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r _ ->.
  apply progOf_outcomes. reflexivity.
Qed.

(** The same holds for any [n], so a single program carries a whole
    family of [Under] typings. *)
#[program] Definition setTo43_under_Dop :
  Dasp_op (pp2asp_under (fun _ : nat => True)
             (fun r : unit * nat => r = (tt, 43))) := setTo 43.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r _ ->.
  apply progOf_outcomes. reflexivity.
Qed.

(** *** ... and untypeable when only SOME [pre]-state does -- which is the
    normal situation for an incorrectness triple *)

Theorem setIf0_under_triple :
  tripleASP (setIf0 1) Under (fun _ : nat => True) (fun r : unit * nat => r = (tt, 1)).
Proof.
  intros r ->. apply getProgASP_obsASP. exists 0.
  split; [ exact I |]. apply progOf_outcomes. split; reflexivity.
Qed.

Theorem setIf0_under_not_Dasp_op :
  forall d : Dasp_op (pp2asp_under (fun _ : nat => True)
                        (fun r : unit * nat => r = (tt, 1))),
    proj1_sig d <> setIf0 1.
Proof.
  intros [prog Hd] Heq. cbn in Heq. subst prog.
  pose proof (proj1 (Dasp_op_under_iff (setIf0 1) _ _) Hd) as H.
  pose proof (proj1 (progOf_outcomes _ 5 (tt, 1)) (H 5 (tt, 1) I eq_refl))
    as [Hs _].
  discriminate Hs.
Qed.

(** The identical postcondition IS typeable once [pre] is the singleton
    [0]: there "some [pre]-state reaches it" and "every [pre]-state
    reaches it" coincide.  Contrast [setIf0_under_not_Dasp_op], which is
    the same program and outcome at [pre = True]. *)
#[program] Definition setIf0_under_P0_Dop :
  Dasp_op (pp2asp_under (fun s : nat => s = 0)
             (fun r : unit * nat => r = (tt, 1))) := setIf0 1.
Next Obligation.
  cbn beta. apply Dasp_op_under_iff. intros s r Hpre ->. subst s.
  apply progOf_outcomes. split; reflexivity.
Qed.
