(** * The Dijkstra monad of a monad morphism

    For a monad morphism [θ : M ~> W] into a specification monad, that is, a
    monad ordered by [le],

        DM θ le w  =  { m : M A | le (θ m) w }

    with [ret] indexed by [W]'s [ret], [bind] by [W]'s [bind], weakening
    along the order, and every computation typed by its own image.  This is
    the construction of Maillard et al., "Dijkstra Monads for All"
    (ICFP 2019, https://doi.org/10.1145/3341708).  It satisfies their laws
    of a Dijkstra monad, the three monad laws and the three laws of
    weakening, whenever the source monad is lawful ([DM_laws]).

    A specification monad is still one with its order flipped
    ([OrderedMonad_flip]), so the same construction at the flipped order
    gives a second Dijkstra monad,

        DMop θ le w  =  DM θ (flip le) w  =  { m : M A | le w (θ m) }.

    The construction asks for the morphism and for the order ([OrderedTarget])
    and for nothing else.  The instances for the morphisms of each setting
    are in [DivNonDet/DijkstraMonads.v], [DivNonDetSt/DijkstraMonads.v] and
    [DivNonDetStExc/DijkstraMonads.v]. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.

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

(** ** The laws

    DM4All asks of a Dijkstra monad the three monad laws and three laws of
    weakening: weakening along reflexivity is the identity, two weakenings
    compose, and weakening commutes with [bind].  There the laws are
    equations between computations whose indices are equal by the laws of
    the specification monad, and the refinement proof lives in [SProp].

    Here the laws of [W] hold up to [eq1], so the two sides of a law have
    different indices, and a computation of [DM] is a computation of [M]
    with a proof.  Two of them are EQUAL when the computations of [M] are,
    whatever the indices and the proofs ([DM_eq]).  The two indices are then
    the two sides of the same law of [W].

    With that equality the six laws are those of [M]: the monad laws are
    [M]'s own, and weakening does not change the computation.  So [DM] is a
    Dijkstra monad as soon as the source monad is lawful for the equality
    the morphism is stated with ([DM_laws]). *)

Section DijkstraLaws.
  Context {M W : Type -> Type}
    (θ : forall A, M A -> W A) (le : forall A, relation (W A)).
  Context {Hθ : IsMonadMorphism θ} {HT : OrderedTarget θ le}.

  Definition DM_eq {A} {w w' : W A} (d : DM θ le w) (d' : DM θ le w') : Prop :=
    @eq1 M (mor_eq1_src (θ := θ)) A (proj1_sig d) (proj1_sig d').

  Record DijkstraLaws : Prop := {
    (* [DM_eq] is an equivalence, and [bind] respects it *)
    dm_eq_refl : forall A (w : W A) (d : DM θ le w), DM_eq d d ;
    dm_eq_sym : forall A (w w' : W A) (d : DM θ le w) (d' : DM θ le w'),
        DM_eq d d' -> DM_eq d' d ;
    dm_eq_trans : forall A (w w' w'' : W A)
        (d : DM θ le w) (d' : DM θ le w') (d'' : DM θ le w''),
        DM_eq d d' -> DM_eq d' d'' -> DM_eq d d'' ;
    dm_bind_proper : forall A B (w w' : W A) (wf wf' : A -> W B)
        (d : DM θ le w) (d' : DM θ le w')
        (f : forall a, DM θ le (wf a)) (f' : forall a, DM θ le (wf' a)),
        DM_eq d d' -> (forall a, DM_eq (f a) (f' a)) ->
        DM_eq (DM_bind θ le d f) (DM_bind θ le d' f') ;
    (* the monad laws *)
    dm_bind_ret_l : forall A B (a : A) (wf : A -> W B)
        (f : forall a, DM θ le (wf a)),
        DM_eq (DM_bind θ le (DM_ret θ le a) f) (f a) ;
    dm_bind_ret_r : forall A (w : W A) (d : DM θ le w),
        DM_eq (DM_bind θ le d (fun a => DM_ret θ le a)) d ;
    dm_bind_bind : forall A B C (w : W A) (wf : A -> W B) (wg : B -> W C)
        (d : DM θ le w) (f : forall a, DM θ le (wf a))
        (g : forall b, DM θ le (wg b)),
        DM_eq (DM_bind θ le (DM_bind θ le d f) g)
              (DM_bind θ le d (fun a => DM_bind θ le (f a) g)) ;
    (* the laws of weakening *)
    dm_wkn_id : forall A (w : W A) (H : le A w w) (d : DM θ le w),
        DM_eq (DM_wkn θ le H d) d ;
    dm_wkn_wkn : forall A (w1 w2 w3 : W A)
        (H12 : le A w1 w2) (H23 : le A w2 w3) (H13 : le A w1 w3)
        (d : DM θ le w1),
        DM_eq (DM_wkn θ le H23 (DM_wkn θ le H12 d)) (DM_wkn θ le H13 d) ;
    dm_wkn_bind : forall A B (w w' : W A) (wf wf' : A -> W B)
        (H : le A w w') (Hf : forall a, le B (wf a) (wf' a))
        (H' : le B (@bind W (mor_monad_tgt (θ := θ)) A B w wf)
                   (@bind W (mor_monad_tgt (θ := θ)) A B w' wf'))
        (d : DM θ le w) (f : forall a, DM θ le (wf a)),
        DM_eq (DM_wkn θ le H' (DM_bind θ le d f))
              (DM_bind θ le (DM_wkn θ le H d)
                 (fun a => DM_wkn θ le (Hf a) (f a)))
  }.

  Hypothesis EqM :
    @Eq1Equivalence M (mor_monad_src (θ := θ)) (mor_eq1_src (θ := θ)).
  Hypothesis LawsM :
    @MonadLawsE M (mor_eq1_src (θ := θ)) (mor_monad_src (θ := θ)).

  Theorem DM_laws : DijkstraLaws.
  Proof.
    destruct LawsM as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A w d. destruct (EqM A) as [Hr _ _]. exact (Hr (proj1_sig d)).
    - intros A w w' d d' H. destruct (EqM A) as [_ Hs _]. exact (Hs _ _ H).
    - intros A w w' w'' d d' d'' H1 H2. destruct (EqM A) as [_ _ Ht].
      exact (Ht _ _ _ H1 H2).
    - intros A B w w' wf wf' d d' f f' Hd Hf.
      exact (Lpb A B (proj1_sig d) (proj1_sig d') Hd
               (fun a => proj1_sig (f a)) (fun a => proj1_sig (f' a)) Hf).
    - intros A B a wf f. exact (Lbrl A B (fun a => proj1_sig (f a)) a).
    - intros A w d. exact (Lbrr A (proj1_sig d)).
    - intros A B C w wf wg d f g.
      exact (Lbb A B C (proj1_sig d) (fun a => proj1_sig (f a))
               (fun b => proj1_sig (g b))).
    - intros A w H d. destruct (EqM A) as [Hr _ _]. exact (Hr (proj1_sig d)).
    - intros A w1 w2 w3 H12 H23 H13 d. destruct (EqM A) as [Hr _ _].
      exact (Hr (proj1_sig d)).
    - intros A B w w' wf wf' H Hf H' d f. destruct (EqM B) as [Hr _ _].
      exact (Hr _).
  Qed.

  (** Lifting is compatible with the operations: a lifted [ret] is [DM_ret],
      and a lifted [bind] is the [DM_bind] of the lifted parts. *)
  Lemma DM_lift_ret {A} (a : A) :
    DM_eq (DM_lift θ le (@ret M (mor_monad_src (θ := θ)) A a)) (DM_ret θ le a).
  Proof. destruct (EqM A) as [Hr _ _]. exact (Hr _). Qed.

  Lemma DM_lift_bind {A B} (m : M A) (k : A -> M B) :
    DM_eq (DM_lift θ le (@bind M (mor_monad_src (θ := θ)) A B m k))
          (DM_bind θ le (DM_lift θ le m) (fun a => DM_lift θ le (k a))).
  Proof. destruct (EqM B) as [Hr _ _]. exact (Hr _). Qed.
End DijkstraLaws.

(** The same laws for [DMop]: it is [DM] at the flipped order. *)
Definition DijkstraLawsOp {M W : Type -> Type} (θ : forall A, M A -> W A)
  (le : forall A, relation (W A))
  {Hθ : IsMonadMorphism θ} {HT : OrderedTarget θ le} : Prop :=
  @DijkstraLaws M W θ (fun A x y => le A y x) Hθ (OrderedTarget_flip θ le HT).

Theorem DMop_laws {M W : Type -> Type} (θ : forall A, M A -> W A)
  (le : forall A, relation (W A))
  {Hθ : IsMonadMorphism θ} {HT : OrderedTarget θ le} :
  @Eq1Equivalence M (mor_monad_src (θ := θ)) (mor_eq1_src (θ := θ)) ->
  @MonadLawsE M (mor_eq1_src (θ := θ)) (mor_monad_src (θ := θ)) ->
  DijkstraLawsOp θ le.
Proof.
  intros EqM LawsM.
  exact (@DM_laws M W θ _ Hθ (OrderedTarget_flip θ le HT) EqM LawsM).
Qed.
