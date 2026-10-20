(** * Dijkstra-monad classes are local in the start state

    Take any specification monad [W] (a monad with a preorder for which
    [bind] is monotone in its continuation), any monad morphism
    [θ : RelSt S -> W] and any index [w], observed or not.  The classes

      [{R | w ⊑ θ R}]   and   [{R | θ R ⊑ w}]

    are both closed under GLUING BY START STATE: if [Y s] is in the class
    for every [s], so is [glue Y], which from start state [s] behaves like
    [Y s] ([glue_rel]).

    The proof splits any specification by its start state,

      [w ≡ θ choose >>= λs. θ (assumeAt s) ;; w]        ([split_by_start]),

    using only the monad laws of [W] and that [θ] is a morphism, and then
    uses monotonicity of [bind] in the continuation twice.  It is the
    monadic form of the [first]-law obstruction: [choose >>= λs. assumeAt s]
    carries the start state along as a context.

    O'Hearn's incorrectness triple is not closed under gluing once its
    precondition has two states: each [avoiding s] reaches the outcome from
    the precondition state that is not [s], and gluing them reaches nothing
    ([IL_not_Dijkstra_typable]).  So no specification monad, order,
    observation or index types it exactly, in either direction.  Triples
    that quantify over start states outermost (Hoare, Lisbon, the
    per-start-state WP triples) are local, and are not affected. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions Setoid.
From ExtLib Require Import Monad StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import OrderedMonad MonadMorphism.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import PredMonad.
From Incorrectness.Taxonomy.Readings Require Import StateReadings.

#[local] Existing Instance Monad_stateT.
#[local] Existing Instance Monad_RelSt | 0.
#[local] Existing Instance Eq1_RelSt | 0.

(* ================================================================= *)
(** ** Choosing a state, and asserting the start state                *)
(* ================================================================= *)

Section Programs.
  Variable S : Type.

  (** Return any state, leaving the state unchanged. *)
  Definition choose : RelSt S S := mkRelSt (fun st r => snd r = st).

  (** Succeed exactly when the current state is [s]. *)
  Definition assumeAt (s : S) : RelSt S unit := mkRelSt (fun st r => st = s /\ r = (tt, st)).

  (** From start state [s], behave like [Y s]. *)
  Definition glue {A} (Y : S -> RelSt S A) : RelSt S A :=
    bind choose (fun s => bind (assumeAt s) (fun _ => Y s)).

  Lemma choose_assumeAt : eq1 (bind choose assumeAt) (ret tt).
  Proof.
    intros st r. rewrite relSt_bind, relSt_ret. cbn. split.
    - intros [s [st' [-> [_ Hr]]]]. exact Hr.
    - intros ->. exists st, st. split; [ reflexivity | split; reflexivity ].
  Qed.

  Lemma glue_rel {A} (Y : S -> RelSt S A) st r :
    runStateT (glue Y) st r <-> runStateT (Y st) st r.
  Proof.
    unfold glue. rewrite relSt_bind. setoid_rewrite relSt_bind. cbn. split.
    - intros [s [st' [-> [u [st'' [[-> [=]] HY]]]]]]. subst. exact HY.
    - intros HY. exists st, st. split; [ reflexivity |].
      exists tt, st. split; [ split; reflexivity | exact HY ].
  Qed.
End Programs.

Arguments choose {S}.
Arguments assumeAt {S} s.
Arguments glue {S A} Y.

(* ================================================================= *)
(** ** Gluing, for any specification monad                            *)
(* ================================================================= *)

Section Locality.
  Variable S : Type.
  Context {W : Type -> Type} {MW : Monad W} {EW : Eq1 W}
          {EqW : @Eq1Equivalence W MW EW} {LW : @MonadLawsE W EW MW}.
  Variable le : forall A, relation (W A).
  Context {OW : @OrderedMonad W MW EW le}.
  Variable θ : forall A, RelSt S A -> W A.
  Hypothesis Hθ : @MonadMorphism (RelSt S) W (Monad_RelSt S) MW (Eq1_RelSt S) EW θ.

  #[local] Existing Instance om_preorder.

  (** Every specification is the union of its restrictions to single
      start states. *)
  Lemma split_by_start {A} (w : W A) :
    eq1 w (bind (θ _ choose) (fun s => bind (θ _ (assumeAt s)) (fun _ => w))).
  Proof.
    symmetry.
    transitivity (bind (bind (θ _ choose) (fun s => θ _ (assumeAt s))) (fun _ => w)).
    { symmetry. apply bind_bind. }
    transitivity (bind (θ _ (bind choose assumeAt)) (fun _ => w)).
    { apply Proper_bind; [ symmetry; exact (mm_bind Hθ choose assumeAt) | intro; reflexivity ]. }
    transitivity (bind (θ _ (ret tt)) (fun _ => w)).
    { apply Proper_bind; [ exact (mm_proper Hθ _ _ (choose_assumeAt S)) | intro; reflexivity ]. }
    transitivity (bind (ret tt) (fun _ => w)).
    { apply Proper_bind; [ exact (mm_ret Hθ tt) | intro; reflexivity ]. }
    apply bind_ret_l.
  Qed.

  Lemma theta_glue {A} (Y : S -> RelSt S A) :
    eq1 (θ _ (glue Y)) (bind (θ _ choose) (fun s => bind (θ _ (assumeAt s)) (fun _ => θ _ (Y s)))).
  Proof.
    unfold glue. etransitivity; [ exact (mm_bind Hθ _ _) |].
    apply Proper_bind; [ reflexivity | intro s ]. exact (mm_bind Hθ _ _).
  Qed.

  Theorem gluing_Dop {A} (w : W A) (Y : S -> RelSt S A) :
    (forall s, le A w (θ _ (Y s))) -> le A w (θ _ (glue Y)).
  Proof.
    intro H.
    transitivity (bind (θ _ choose) (fun s => bind (θ _ (assumeAt s)) (fun _ => w))).
    { apply om_eq1. apply split_by_start. }
    transitivity (bind (θ _ choose) (fun s => bind (θ _ (assumeAt s)) (fun _ => θ _ (Y s)))).
    { apply om_bind; [ reflexivity | intro s ].
      apply om_bind; [ reflexivity | intro u; exact (H s) ]. }
    apply om_eq1. symmetry. apply theta_glue.
  Qed.

  Theorem gluing_DM {A} (w : W A) (Y : S -> RelSt S A) :
    (forall s, le A (θ _ (Y s)) w) -> le A (θ _ (glue Y)) w.
  Proof.
    intro H.
    transitivity (bind (θ _ choose) (fun s => bind (θ _ (assumeAt s)) (fun _ => θ _ (Y s)))).
    { apply om_eq1. apply theta_glue. }
    transitivity (bind (θ _ choose) (fun s => bind (θ _ (assumeAt s)) (fun _ => w))).
    { apply om_bind; [ reflexivity | intro s ].
      apply om_bind; [ reflexivity | intro u; exact (H s) ]. }
    apply om_eq1. symmetry. apply split_by_start.
  Qed.

  (* ================================================================= *)
  (** *** O'Hearn's triple is not local                                *)
  (* ================================================================= *)

  Section IL.
    Variable A : Type.
    Hypothesis S_dec : forall x y : S, x = y \/ x <> y.
    Variables (p1 p2 : S) (r0 : A * S).
    Hypothesis Hne : p1 <> p2.

    Let P : S -> Prop := fun s => s = p1 \/ s = p2.
    Let Q : A * S -> Prop := fun r => r = r0.

    (** Reach [r0] from the precondition state that is not [s]. *)
    Definition avoiding (s : S) : RelSt S A :=
      mkRelSt (fun st r => r = r0 /\ (st = p1 \/ st = p2) /\ st <> s).

    Lemma avoiding_IL s : incorrectSt P Q (avoiding s).
    Proof.
      intros r Hr. destruct (S_dec s p1) as [-> | Hs].
      - exists p2. split; [ right; reflexivity |].
        cbn. split; [ exact Hr | split; [ right; reflexivity | intro E; exact (Hne (eq_sym E)) ] ].
      - exists p1. split; [ left; reflexivity |].
        cbn. split; [ exact Hr | split; [ left; reflexivity | intro E; exact (Hs (eq_sym E)) ] ].
    Qed.

    Lemma glue_avoiding_not_IL : ~ incorrectSt P Q (glue avoiding).
    Proof.
      intro H. destruct (H r0 eq_refl) as [st [_ Hst]].
      apply (proj1 (glue_rel S avoiding st r0)) in Hst. cbn in Hst.
      destruct Hst as [_ [_ Hneq]]. exact (Hneq eq_refl).
    Qed.

    Theorem IL_not_Dijkstra_typable (w : W A) :
      ~ (forall R, incorrectSt P Q R <-> le A w (θ _ R))
      /\ ~ (forall R, incorrectSt P Q R <-> le A (θ _ R) w).
    Proof.
      split; intro Hw; apply glue_avoiding_not_IL, Hw.
      - apply gluing_Dop. intro s. apply Hw, avoiding_IL.
      - apply gluing_DM. intro s. apply Hw, avoiding_IL.
    Qed.
  End IL.
End Locality.
