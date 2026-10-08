(** * The Dijkstra monad of a monad morphism

    For a monad morphism [θ : M ~> W] into a specification monad, that is, a
    monad ordered by [le],

        DM θ le w  =  { m : M A | le (θ m) w }

    with [ret] indexed by [W]'s [ret], [bind] by [W]'s [bind], weakening
    along the order, and every computation typed by its own image.  This is
    the construction of Maillard et al., "Dijkstra Monads for All"
    (ICFP 2019, https://doi.org/10.1145/3341708).

    A specification monad is still one with its order flipped
    ([OrderedMonad_flip]), so the same construction at the flipped order
    gives a second Dijkstra monad,

        DMop θ le w  =  DM θ (flip le) w  =  { m : M A | le w (θ m) }.

    The construction asks for the morphism and for the order, and for
    nothing else.  The WP, ASP and DSLP morphisms of
    [Triples/MonadMorphisms.v] are lifts of a base morphism through the
    monad and arrow transformers, and the natural orders of their targets
    are lifts of the base orders.  So each of them has its Dijkstra monads
    at the base, with state, and with state and exceptions: the
    [OrderedTarget] instances below name the order and are all that is
    supplied.  DSP and ASLP are not specification monads for their natural
    order, so their morphisms have none.

    Triples are typings where the two say the same: a WP [Under] triple is
    a typing in [DM] and a WP [Over] triple one in [DMop], for all four WP
    readings, which is eight WP Dijkstra monads; ASP [Over] is a typing in
    [DM] and DSLP [Under] one in [DMop].

    The last part is about the two SP kinds that are left.  An ASP [Under]
    triple asks, for each result, for SOME start state that reaches it; a
    typing compares at every precondition, so it speaks of EVERY start
    state.  No index has the ASP [Under] triple as its typings
    ([no_asp_under_index]), nor the DSLP [Over] triple
    ([no_dslp_over_index]).  Without state there is one start point, the two
    readings agree, and the triple is a typing ([triple_under_aspPure]). *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws DivNonDetNE.
From Incorrectness.Taxonomy.Arrows Require Import Rel SPostArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  WPureMonad ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.Triples Require Import Triple MonadMorphisms.

(* ================================================================= *)
(** * The construction                                                *)
(* ================================================================= *)

(** The order of the target, for the monad and the equality the morphism is
    stated with. *)
Class OrderedTarget {M W : Type -> Type} (θ : forall A, M A -> W A)
  {Hθ : IsMonadMorphism θ} (le : forall A, relation (W A)) : Prop := {
  ot_equiv : @Eq1Equivalence W mor_monad_tgt mor_eq1_tgt ;
  ot_ordered : @OrderedMonad W mor_monad_tgt mor_eq1_tgt le
}.

Section DijkstraOfMorphism.
  Context {M W : Type -> Type}
    (θ : forall A, M A -> W A) (le : forall A, relation (W A)).

  (** [DM]: the image of the computation is below the index. *)
  Definition DM {A} (w : W A) : Type := { m : M A | le A (θ A m) w }.

  Context {Hθ : IsMonadMorphism θ} {HT : OrderedTarget θ le}.

  Local Notation retM A a := (@ret M (mor_monad_src (θ := θ)) A a).
  Local Notation bindM A B x k := (@bind M (mor_monad_src (θ := θ)) A B x k).
  Local Notation retW A a := (@ret W (mor_monad_tgt (θ := θ)) A a).
  Local Notation bindW A B w k := (@bind W (mor_monad_tgt (θ := θ)) A B w k).

  Lemma DM_ret_typing {A} (a : A) : le A (θ A (retM A a)) (retW A a).
  Proof. exact (@om_eq1 W _ _ le ot_ordered A _ _ (mm_ret mor_laws a)). Qed.

  Lemma DM_bind_typing {A B} (x : M A) (k : A -> M B)
    (w : W A) (wf : A -> W B) :
    le A (θ A x) w -> (forall a, le B (θ B (k a)) (wf a)) ->
    le B (θ B (bindM A B x k)) (bindW A B w wf).
  Proof.
    intros Hx Hk.
    destruct (@om_preorder W _ _ le ot_ordered B) as [_ Ht].
    refine (Ht _ _ _
              (@om_eq1 W _ _ le ot_ordered B _ _ (mm_bind mor_laws x k)) _).
    exact (@om_bind W _ _ le ot_ordered A B _ _ Hx _ _ Hk).
  Qed.

  (** *** The operations of [DM] *)

  Definition DM_ret {A} (a : A) : DM (retW A a) :=
    exist _ (retM A a) (DM_ret_typing a).

  Definition DM_bind {A B} {w : W A} {wf : A -> W B}
    (m : DM w) (f : forall a, DM (wf a)) : DM (bindW A B w wf) :=
    exist _ (bindM A B (proj1_sig m) (fun a => proj1_sig (f a)))
      (DM_bind_typing _ _ w wf (proj2_sig m) (fun a => proj2_sig (f a))).

  (** The rule of consequence. *)
  Definition DM_wkn {A} {w w' : W A} (Hle : le A w w') (m : DM w) : DM w' :=
    exist _ (proj1_sig m)
      (@PreOrder_Transitive _ _ (@om_preorder W _ _ le ot_ordered A)
         _ _ _ (proj2_sig m) Hle).

  (** Every computation is typed by its own image. *)
  Definition DM_lift {A} (m : M A) : DM (θ A m) :=
    exist _ m (@PreOrder_Reflexive _ _ (@om_preorder W _ _ le ot_ordered A) _).
End DijkstraOfMorphism.

(** ** The flipped order

    The order of a specification monad can be flipped, so [DM] at the flipped
    order is again a Dijkstra monad.  Its index is below the image of the
    computation. *)

Lemma OrderedTarget_flip {M W : Type -> Type} (θ : forall A, M A -> W A)
  {Hθ : IsMonadMorphism θ} (le : forall A, relation (W A)) :
  OrderedTarget θ le -> OrderedTarget θ (fun A x y => le A y x).
Proof.
  intros [He Ho].
  exact (@Build_OrderedTarget M W θ Hθ _ He (@OrderedMonad_flip W _ _ He le Ho)).
Qed.

Definition DMop {M W : Type -> Type} (θ : forall A, M A -> W A)
  (le : forall A, relation (W A)) {A} (w : W A) : Type :=
  DM θ (fun A x y => le A y x) w.

Section DijkstraOfMorphismOp.
  Context {M W : Type -> Type}
    (θ : forall A, M A -> W A) (le : forall A, relation (W A)).
  Context {Hθ : IsMonadMorphism θ} {HT : OrderedTarget θ le}.

  Local Notation flipped := (fun A x y => le A y x).
  Local Notation HTop := (OrderedTarget_flip θ le HT).

  Definition DMop_ret {A} (a : A)
    : DMop θ le (@ret W (mor_monad_tgt (θ := θ)) A a) :=
    @DM_ret M W θ flipped Hθ HTop A a.

  Definition DMop_bind {A B} {w : W A} {wf : A -> W B}
    (m : DMop θ le w) (f : forall a, DMop θ le (wf a))
    : DMop θ le (@bind W (mor_monad_tgt (θ := θ)) A B w wf) :=
    @DM_bind M W θ flipped Hθ HTop A B w wf m f.

  Definition DMop_wkn {A} {w w' : W A} (Hle : le A w' w) (m : DMop θ le w)
    : DMop θ le w' :=
    @DM_wkn M W θ flipped Hθ HTop A w w' Hle m.

  Definition DMop_lift {A} (m : M A) : DMop θ le (θ A m) :=
    @DM_lift M W θ flipped Hθ HTop A m.
End DijkstraOfMorphismOp.

(* ================================================================= *)
(** * The liftable morphisms                                          *)
(* ================================================================= *)

(** Each target is ordered, by its natural order, for the monad and the
    equality its morphism is stated with.  The WP targets carry the
    refinement order [WP_le] and its lifts; ASP and DSLP the pointwise order
    of their transformers.

    The DSP and ASLP morphisms have no instance.  DSP and ASLP are not
    specification monads for their natural order: [bind] is not monotone in
    its first argument ([not_OrderedMonad_DSPSt], [not_OrderedMonad_ASLPSt]).
    So they have no Dijkstra monad here. *)

#[global] Instance OrderedTarget_dwpPure :
  OrderedTarget (@dwpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_dwpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_dwpSt (S : Type) :
  OrderedTarget (@dwpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_dwpStExc (S : Type) :
  OrderedTarget (@dwpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_dwlpPure :
  OrderedTarget (@dwlpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_dwlpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_dwlpSt (S : Type) :
  OrderedTarget (@dwlpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwlpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_dwlpStExc (S : Type) :
  OrderedTarget (@dwlpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dwlpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_awpPure :
  OrderedTarget (@awpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_awpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_awpSt (S : Type) :
  OrderedTarget (@awpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_awpStExc (S : Type) :
  OrderedTarget (@awpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_awlpPure :
  OrderedTarget (@awlpPure) (@WP_le) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_awlpPure _
    Eq1Equivalence_WPure
    OrderedMonad_WPure.

#[global] Instance OrderedTarget_awlpSt (S : Type) :
  OrderedTarget (@awlpSt S) (@ordWSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awlpSt S) _
    (Eq1Equivalence__WSt S)
    (OrderedMonad_WSt S).

#[global] Instance OrderedTarget_awlpStExc (S : Type) :
  OrderedTarget (@awlpStExc S) (@ordWStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_awlpStExc S) _
    (Eq1Equivalence_stateT S (optionT WPure))
    (OrderedMonad_WStExc S).

#[global] Instance OrderedTarget_aspPure :
  OrderedTarget (@aspPure) (@ordASP) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_aspPure _
    Eq1Equivalence_ASP
    OrderedMonad_ASP.

#[global] Instance OrderedTarget_aspSt (S : Type) :
  OrderedTarget (@aspSt S) (@ordASPSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_aspSt S) _
    (Eq1Equivalence_ASPSt S)
    (OrderedMonad_ASPSt S).

#[global] Instance OrderedTarget_aspStExc (S : Type) :
  OrderedTarget (@aspStExc S) (@ordASPStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_aspStExc S) _
    (Eq1Equivalence_ASPStExc S)
    (OrderedMonad_ASPStExc S).

#[global] Instance OrderedTarget_dslpPure :
  OrderedTarget (@dslpPure) (@ordDSLP) :=
  @Build_OrderedTarget _ _ _ IsMonadMorphism_dslpPure _
    Eq1Equivalence_DSLP
    OrderedMonad_DSLP.

#[global] Instance OrderedTarget_dslpSt (S : Type) :
  OrderedTarget (@dslpSt S) (@ordDSLPSt S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dslpSt S) _
    (Eq1Equivalence_DSLPSt S)
    (OrderedMonad_DSLPSt S).

#[global] Instance OrderedTarget_dslpStExc (S : Type) :
  OrderedTarget (@dslpStExc S) (@ordDSLPStExc S) :=
  @Build_OrderedTarget _ _ _ (IsMonadMorphism_dslpStExc S) _
    (Eq1Equivalence_DSLPStExc S)
    (OrderedMonad_DSLPStExc S).

(** ** The twelve Dijkstra monads with state and exceptions

    Eight WP ones: each of the four readings, at the refinement order and at
    its flip.  Four SP ones: ASP and DSLP, each at its order and at its
    flip.  The same definitions make sense at the base and with state alone,
    with [DM] and [DMop] applied to the morphism of that level. *)
Section Named.
  Context {S A : Type}.

  Definition Ddwp (w : WStExc S A) : Type :=
    DM (@dwpStExc S) (@ordWStExc S) w.
  Definition Ddwp_op (w : WStExc S A) : Type :=
    DMop (@dwpStExc S) (@ordWStExc S) w.
  Definition Ddwlp (w : WStExc S A) : Type :=
    DM (@dwlpStExc S) (@ordWStExc S) w.
  Definition Ddwlp_op (w : WStExc S A) : Type :=
    DMop (@dwlpStExc S) (@ordWStExc S) w.
  Definition Dawp (w : WStExc S A) : Type :=
    DM (@awpStExc S) (@ordWStExc S) w.
  Definition Dawp_op (w : WStExc S A) : Type :=
    DMop (@awpStExc S) (@ordWStExc S) w.
  Definition Dawlp (w : WStExc S A) : Type :=
    DM (@awlpStExc S) (@ordWStExc S) w.
  Definition Dawlp_op (w : WStExc S A) : Type :=
    DMop (@awlpStExc S) (@ordWStExc S) w.

  Definition Dasp (w : ASPStExc S A) : Type :=
    DM (@aspStExc S) (@ordASPStExc S) w.
  Definition Dasp_op (w : ASPStExc S A) : Type :=
    DMop (@aspStExc S) (@ordASPStExc S) w.
  Definition Ddslp (w : DSLPStExc S A) : Type :=
    DM (@dslpStExc S) (@ordDSLPStExc S) w.
  Definition Ddslp_op (w : DSLPStExc S A) : Type :=
    DMop (@dslpStExc S) (@ordDSLPStExc S) w.
End Named.

(** A typing through a lifted WP morphism is a family of typings through the
    base morphism, one per start state. *)
Lemma wpSt_typing_pointwise {S A} (σ : forall A, divndNE A -> WPure A)
  (m : stdivndNE S A) (w : WSt S A) :
  ordWSt (stateT_map S σ A m) w
  <-> forall s, WP_le (σ _ (runStateT m s)) (runStateT w s).
Proof. reflexivity. Qed.

Lemma wpStExc_typing_pointwise {S A} (σ : forall A, divndNE A -> WPure A)
  (m : stdivexcndNE S A) (w : WStExc S A) :
  ordWStExc (stateT_map S (optionT_map σ) A m) w
  <-> forall s,
        WP_le (σ _ (unOptionT (runStateT m s))) (unOptionT (runStateT w s)).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** * Triples are typings                                             *)
(* ================================================================= *)

(** ** WP

    The index of a pre- and a postcondition, at the base and lifted start
    state by start state.  [wpUnder] is the least transformer that takes
    the postcondition into the precondition, [wpOver] the greatest one
    whose value at the postcondition is within the precondition. *)

Lemma wpUnder_mono {A} (pre : Prop) (post : A -> Prop) :
  wpure_mono (fun p : A -> Prop => pre /\ forall a, post a -> p a).
Proof.
  intros p q Hpq [Hpre Hsub]. split; [ exact Hpre |].
  intros a Ha. exact (Hpq a (Hsub a Ha)).
Qed.

Lemma wpOver_mono {A} (pre : Prop) (post : A -> Prop) :
  wpure_mono (fun p : A -> Prop => (forall a, p a -> post a) -> pre).
Proof.
  intros p q Hpq H Hsub. apply H. intros a Ha. exact (Hsub a (Hpq a Ha)).
Qed.

Definition wpUnderPure {A} (pre : Prop) (post : A -> Prop) : WPure A :=
  mkWPure _ (wpUnder_mono pre post).

Definition wpOverPure {A} (pre : Prop) (post : A -> Prop) : WPure A :=
  mkWPure _ (wpOver_mono pre post).

Definition wpUnderSt {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A := mkStateT (fun s => wpUnderPure (pre s) post).

Definition wpOverSt {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A := mkStateT (fun s => wpOverPure (pre s) post).

Definition wpUnderStExc {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : WStExc S A := mkStateT (fun s => mkOptionT (wpUnderPure (pre s) post)).

Definition wpOverStExc {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : WStExc S A := mkStateT (fun s => mkOptionT (wpOverPure (pre s) post)).

Lemma le_wpUnderPure {A} (w : WPure A) (pre : Prop) (post : A -> Prop) :
  (pre -> getWPure w post) <-> WP_le w (wpUnderPure pre post).
Proof.
  split.
  - intros H k [Hpre Hsub]. exact (getWPure_mono w post k Hsub (H Hpre)).
  - intros H Hpre. exact (H post (conj Hpre (fun a Ha => Ha))).
Qed.

Lemma le_wpOverPure {A} (w : WPure A) (pre : Prop) (post : A -> Prop) :
  (getWPure w post -> pre) <-> WP_le (wpOverPure pre post) w.
Proof.
  split.
  - intros H k Hk Hsub. exact (H (getWPure_mono w k post Hsub Hk)).
  - intros H Hw. exact (H post Hw (fun a Ha => Ha)).
Qed.

(** For any morphism into the three WP monads, so for all four readings:
    an [Under] triple is a typing in [DM] at [wpUnder], an [Over] triple a
    typing in [DMop] at [wpOver]. *)
Section WPTypings.
  Context {M : Type -> Type}.

  Theorem triple_under_wpPure (θ : forall A, M A -> WPure A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Under pre post
    <-> WP_le (θ A m) (wpUnderPure (pre tt) post).
  Proof.
    etransitivity; [| exact (le_wpUnderPure (θ A m) (pre tt) post) ].
    split; [ intros H Hp; exact (H tt Hp) | intros H [] Hp; exact (H Hp) ].
  Qed.

  Theorem triple_over_wpPure (θ : forall A, M A -> WPure A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Over pre post
    <-> WP_le (wpOverPure (pre tt) post) (θ A m).
  Proof.
    etransitivity; [| exact (le_wpOverPure (θ A m) (pre tt) post) ].
    split; [ intros H Hw; exact (H tt Hw) | intros H [] Hw; exact (H Hw) ].
  Qed.

  Context {S : Type}.

  Theorem triple_under_wpSt (θ : forall A, M A -> WSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Under pre post <-> ordWSt (θ A m) (wpUnderSt pre post).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpUnderPure (runStateT (θ A m) s) (pre s) post) (H s)).
    - exact (proj2 (le_wpUnderPure (runStateT (θ A m) s) (pre s) post) (H s)).
  Qed.

  Theorem triple_over_wpSt (θ : forall A, M A -> WSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Over pre post <-> ordWSt (wpOverSt pre post) (θ A m).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpOverPure (runStateT (θ A m) s) (pre s) post) (H s)).
    - exact (proj2 (le_wpOverPure (runStateT (θ A m) s) (pre s) post) (H s)).
  Qed.

  Theorem triple_under_wpStExc (θ : forall A, M A -> WStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Under pre post <-> ordWStExc (θ A m) (wpUnderStExc pre post).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpUnderPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
    - exact (proj2 (le_wpUnderPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
  Qed.

  Theorem triple_over_wpStExc (θ : forall A, M A -> WStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Over pre post <-> ordWStExc (wpOverStExc pre post) (θ A m).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpOverPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
    - exact (proj2 (le_wpOverPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
  Qed.
End WPTypings.

(** ** SP

    The index of a pre- and a postcondition is the arrow of a relation, at
    any pair of indices: for ASP [Over], the relation that sends a start
    point in the precondition into the postcondition; for DSLP [Under], the
    one that sends into the postcondition only from the precondition.  The
    three levels are this one statement at three pairs of indices.

    The other SP kinds are not typings in these orders: an ASP [Under]
    triple asks for some start point per result, while the order compares
    at every precondition. *)

Definition aspOver {X Y} (P : X -> Prop) (Q : Y -> Prop) : ASPArr X Y :=
  relASP (fun x y => P x -> Q y).

Definition dslpUnder {X Y} (P : X -> Prop) (Q : Y -> Prop) : DSLPArr X Y :=
  relDSLP (fun x y => Q y -> P x).

Lemma le_aspOver {X Y} (w : ASPArr X Y) (P : X -> Prop) (Q : Y -> Prop) :
  (forall y, getASPArr w P y -> Q y)
  <-> (forall P' y, getASPArr w P' y -> getASPArr (aspOver P Q) P' y).
Proof.
  split.
  - intros H P' y Hw.
    destruct (proj1 (get_aspRel w P' y) Hw) as [x [Hx Hr]].
    exists x. split; [ exact Hx |]. intro HP. apply H.
    exact (proj2 (get_aspRel w P y) (ex_intro _ x (conj HP Hr))).
  - intros H y Hw. destruct (H P y Hw) as [x [HP HQ]]. exact (HQ HP).
Qed.

Lemma le_dslpUnder {X Y} (w : DSLPArr X Y) (P : X -> Prop) (Q : Y -> Prop) :
  (forall y, Q y -> getDSLPArr w P y)
  <-> (forall P' y, getDSLPArr (dslpUnder P Q) P' y -> getDSLPArr w P' y).
Proof.
  split.
  - intros H P' y Ht. apply (proj2 (get_dslpRel w P' y)). intros x Hr.
    refine (Ht x _). intro HQ.
    exact (proj1 (get_dslpRel w P y) (H y HQ) x Hr).
  - intros H y HQ. apply (H P y). intros x Hx. exact (Hx HQ).
Qed.

Section SPTypings.
  Context {M : Type -> Type}.

  Theorem triple_over_aspPure (θ : forall A, M A -> ASP A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Over pre post <-> ordASP (θ A m) (aspOver pre post).
  Proof. exact (le_aspOver (θ A m) pre post). Qed.

  Theorem triple_under_dslpPure (θ : forall A, M A -> DSLP A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Under pre post <-> ordDSLP (dslpUnder pre post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) pre post). Qed.

  Context {S : Type}.

  Theorem triple_over_aspSt (θ : forall A, M A -> ASPSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Over pre post
    <-> ordASPSt (θ A m) (aspOver (fun p : unit * S => pre (snd p)) post).
  Proof. exact (le_aspOver (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_under_dslpSt (θ : forall A, M A -> DSLPSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Under pre post
    <-> ordDSLPSt (dslpUnder (fun p : unit * S => pre (snd p)) post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_over_aspStExc (θ : forall A, M A -> ASPStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Over pre post
    <-> ordASPStExc (θ A m)
          (aspOver (fun p : unit * S => pre (snd p)) post).
  Proof. exact (le_aspOver (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_under_dslpStExc (θ : forall A, M A -> DSLPStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Under pre post
    <-> ordDSLPStExc
          (dslpUnder (fun p : unit * S => pre (snd p)) post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) (fun p => pre (snd p)) post). Qed.
End SPTypings.

(* ================================================================= *)
(** * ASP [Under] and DSLP [Over] are not typings                     *)
(* ================================================================= *)

(** ** A typing is an inclusion of relations

    Whatever the index, a typing in [DMop] for ASP, and one in [DM] for
    DSLP, says that the relation the index denotes is included in the
    relation of the computation: the order leaves nothing else to look
    at. *)

Lemma le_relASP {X Y} (w : ASPArr X Y) (R : X -> Y -> Prop) :
  (forall P y, getASPArr w P y -> getASPArr (relASP R) P y)
  <-> (forall x y, aspRel w x y -> R x y).
Proof.
  split.
  - intros H x y Hw.
    destruct (H (fun z => z = x) y Hw) as [x' [E Hr]]. subst x'. exact Hr.
  - intros H P y Hw. destruct (proj1 (get_aspRel w P y) Hw) as [x [Hp Hr]].
    exists x. exact (conj Hp (H x y Hr)).
Qed.

Lemma relDSLP_le {X Y} (R : X -> Y -> Prop) (w : DSLPArr X Y) :
  (forall P y, getDSLPArr (relDSLP R) P y -> getDSLPArr w P y)
  <-> (forall x y, dslpRel w x y -> R x y).
Proof.
  split.
  - intros H x y Hw.
    exact (proj1 (get_dslpRel w (fun x' => R x' y) y)
             (H (fun x' => R x' y) y (fun a Ha => Ha)) x Hw).
  - intros H P y Ht. apply (proj2 (get_dslpRel w P y)).
    intros x Hr. exact (Ht x (H x y Hr)).
Qed.

(** ** The indices one would like to use

    For ASP [Under], the arrow of the relation between the precondition and
    the postcondition; for DSLP [Over], that between their complements. *)

Definition aspUnder {X Y} (P : X -> Prop) (Q : Y -> Prop) : ASPArr X Y :=
  relASP (fun x y => P x /\ Q y).

Definition dslpOver {X Y} (P : X -> Prop) (Q : Y -> Prop) : DSLPArr X Y :=
  relDSLP (fun x y => ~ P x /\ ~ Q y).

(** A typing at these indices says that EVERY start point in the
    precondition reaches EVERY result in the postcondition (for DSLP: every
    start point outside reaches every result outside). *)
Lemma le_aspUnder {X Y} (P : X -> Prop) (Q : Y -> Prop) (R : X -> Y -> Prop) :
  (forall P' y, getASPArr (aspUnder P Q) P' y -> getASPArr (relASP R) P' y)
  <-> (forall x y, P x -> Q y -> R x y).
Proof.
  etransitivity; [ exact (le_relASP (aspUnder P Q) R) |].
  split.
  - intros H x y HP HQ.
    exact (H x y (proj2 (aspRel_ofRel (fun x y => P x /\ Q y) x y)
                    (conj HP HQ))).
  - intros H x y Hw.
    destruct (proj1 (aspRel_ofRel (fun x y => P x /\ Q y) x y) Hw) as [HP HQ].
    exact (H x y HP HQ).
Qed.

Lemma dslpOver_le {X Y} (P : X -> Prop) (Q : Y -> Prop) (R : X -> Y -> Prop) :
  (forall P' y, getDSLPArr (relDSLP R) P' y -> getDSLPArr (dslpOver P Q) P' y)
  <-> (forall x y, ~ P x -> ~ Q y -> R x y).
Proof.
  etransitivity; [ exact (relDSLP_le R (dslpOver P Q)) |].
  split.
  - intros H x y HP HQ.
    exact (H x y (proj2 (dslpRel_ofRel (fun x y => ~ P x /\ ~ Q y) x y)
                    (conj HP HQ))).
  - intros H x y Hw.
    destruct (proj1 (dslpRel_ofRel (fun x y => ~ P x /\ ~ Q y) x y) Hw)
      as [HP HQ].
    exact (H x y HP HQ).
Qed.

(** That is stronger than the triple, which asks for SOME start point per
    result.  The typing gives the triple as soon as the precondition (for
    DSLP: its complement) is inhabited; the converse fails. *)
Lemma aspUnder_typing_triple {X Y} (P : X -> Prop) (Q : Y -> Prop)
  (R : X -> Y -> Prop) :
  (exists x, P x) -> (forall x y, P x -> Q y -> R x y) ->
  forall y, Q y -> getASPArr (relASP R) P y.
Proof. intros [x HP] H y HQ. exists x. exact (conj HP (H x y HP HQ)). Qed.

Lemma dslpOver_typing_triple {X Y} (P : X -> Prop) (Q : Y -> Prop)
  (R : X -> Y -> Prop) :
  (exists x, ~ P x) -> (forall x y, ~ P x -> ~ Q y -> R x y) ->
  forall y, getDSLPArr (relDSLP R) P y -> Q y.
Proof.
  intros [x HP] H y Hd. apply NNPP. intro HQ.
  exact (HP (Hd x (H x y HP HQ))).
Qed.

(** ** No index at all

    A computation with a prescribed relation between start states and
    results, which may also diverge. *)
Definition progOf {S A} (R : S -> A * S -> Prop) : stdivndNE S A :=
  mkStateT (fun s =>
    exist _
      (@mkOptionT SetM _
         (fun o : option (A * S) =>
            match o with Some r => R s r | None => True end))
      (ex_intro _ None I)).

Lemma progOf_out {S A} (R : S -> A * S -> Prop) (s : S) (r : A * S) :
  outSt (progOf R) s (Some r) <-> R s r.
Proof. reflexivity. Qed.

(** The typings with state, as inclusions into the outcomes. *)
Lemma aspSt_typing_op {S A} (w : ASPSt S A) (m : stdivndNE S A) :
  ordASPSt w (aspSt m)
  <-> (forall s r, aspRel w (tt, s) r -> outSt m s (Some r)).
Proof.
  etransitivity;
    [ exact (le_relASP w (fun us r => outSt m (snd us) (Some r))) |].
  split.
  - intros H s r Hw. exact (H (tt, s) r Hw).
  - intros H [[] s] r Hw. exact (H s r Hw).
Qed.

Lemma dslpSt_typing {S A} (m : stdivndNE S A) (w : DSLPSt S A) :
  ordDSLPSt (dslpSt m) w
  <-> (forall s r, dslpRel w (tt, s) r -> outSt m s (Some r)).
Proof.
  etransitivity;
    [ exact (relDSLP_le (fun us r => outSt m (snd us) (Some r)) w) |].
  split.
  - intros H s r Hw. exact (H (tt, s) r Hw).
  - intros H [[] s] r Hw. exact (H s r Hw).
Qed.

(** Three computations: the result [(tt, 0)] is reached from [0] by the
    first, from [1] by the second, and by the third from nowhere. *)
Definition reach0From0 : stdivndNE nat unit :=
  progOf (fun s (r : unit * nat) => s = 0 /\ r = (tt, 0)).
Definition reach0From1 : stdivndNE nat unit :=
  progOf (fun s (r : unit * nat) => s = 1 /\ r = (tt, 0)).
Definition reachNothing : stdivndNE nat unit :=
  progOf (fun (_ : nat) (_ : unit * nat) => False).

(** A typing is an inclusion of relations, so the computations typed by one
    index are closed under intersection of their relations.  The ASP
    [Under] triple is not: the first two computations satisfy it and the
    third, whose relation is their intersection, does not.  So no index has
    the triple as its typings.  This is a fact about the order of the ASP
    monad, not about the Dijkstra construction. *)
Theorem no_asp_under_index :
  ~ exists w : ASPSt nat unit,
      forall m : stdivndNE nat unit,
        ordASPSt w (aspSt m) <->
        triple (@aspSt nat) m Under
          (fun _ => True) (fun r : unit * nat => r = (tt, 0)).
Proof.
  intros [w Hiff].
  assert (H1 : ordASPSt w (aspSt reach0From0)).
  { apply (proj2 (Hiff reach0From0)). intros r Hr.
    exists (tt, 0). split; [ exact I | exact (conj eq_refl Hr) ]. }
  assert (H2 : ordASPSt w (aspSt reach0From1)).
  { apply (proj2 (Hiff reach0From1)). intros r Hr.
    exists (tt, 1). split; [ exact I | exact (conj eq_refl Hr) ]. }
  pose proof (proj1 (aspSt_typing_op w reach0From0) H1) as R1.
  pose proof (proj1 (aspSt_typing_op w reach0From1) H2) as R2.
  assert (H0 : ordASPSt w (aspSt reachNothing)).
  { apply (proj2 (aspSt_typing_op w reachNothing)). intros s r Hw.
    destruct (R1 s r Hw) as [E1 _]. destruct (R2 s r Hw) as [E2 _].
    subst s. discriminate E2. }
  destruct (proj1 (Hiff reachNothing) H0 (tt, 0) eq_refl) as [[[] s] [_ Hr]].
  exact Hr.
Qed.

(** The same for the DSLP [Over] triple, at the complements: the result
    [(tt, 0)] must be reached from somewhere. *)
Theorem no_dslp_over_index :
  ~ exists w : DSLPSt nat unit,
      forall m : stdivndNE nat unit,
        ordDSLPSt (dslpSt m) w <->
        triple (@dslpSt nat) m Over
          (fun _ => False) (fun r : unit * nat => r <> (tt, 0)).
Proof.
  intros [w Hiff].
  assert (H1 : ordDSLPSt (dslpSt reach0From0) w).
  { apply (proj2 (Hiff reach0From0)). intros r Hd E. subst r.
    exact (Hd (tt, 0) (conj eq_refl eq_refl)). }
  assert (H2 : ordDSLPSt (dslpSt reach0From1) w).
  { apply (proj2 (Hiff reach0From1)). intros r Hd E. subst r.
    exact (Hd (tt, 1) (conj eq_refl eq_refl)). }
  pose proof (proj1 (dslpSt_typing reach0From0 w) H1) as R1.
  pose proof (proj1 (dslpSt_typing reach0From1 w) H2) as R2.
  assert (H0 : ordDSLPSt (dslpSt reachNothing) w).
  { apply (proj2 (dslpSt_typing reachNothing w)). intros s r Hw.
    destruct (R1 s r Hw) as [E1 _]. destruct (R2 s r Hw) as [E2 _].
    subst s. discriminate E2. }
  exact (proj1 (Hiff reachNothing) H0 (tt, 0) (fun us Hr => Hr) eq_refl).
Qed.

(** ** Without state the ASP [Under] triple is a typing

    At the input [unit] there is one start point, so "some start point in
    the precondition" and "every start point in the precondition" say the
    same once the precondition holds.  This is all the statement uses: it
    is about any ASP element at unit input, and it is what fails with
    state. *)
Lemma le_aspUnder_unit {Y} (w : ASPArr unit Y)
  (P : unit -> Prop) (Q : Y -> Prop) :
  P tt ->
  ((forall y, Q y -> getASPArr w P y)
   <-> (forall P' y, getASPArr (aspUnder P Q) P' y -> getASPArr w P' y)).
Proof.
  intro Hp. split.
  - intros H P' y [[] [HP' [_ HQ]]].
    destruct (proj1 (get_aspRel w P y) (H y HQ)) as [[] [_ Hr]].
    exact (proj2 (get_aspRel w P' y) (ex_intro _ tt (conj HP' Hr))).
  - intros H y HQ. apply (H P y). exists tt. exact (conj Hp (conj Hp HQ)).
Qed.

Theorem triple_under_aspPure {M : Type -> Type} (θ : forall A, M A -> ASP A)
  {Hθ : IsMonadMorphism θ} {A} (m : M A)
  (pre : unit -> Prop) (post : A -> Prop) :
  pre tt ->
  (triple θ m Under pre post <-> ordASP (aspUnder pre post) (θ A m)).
Proof. exact (le_aspUnder_unit (θ A m) pre post). Qed.
