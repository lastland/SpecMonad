From Coq Require Import
  FunctionalExtensionality
  PropExtensionality
  RelationClasses.
From ExtLib Require Import
  Monad MonadLaws
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import WP SP.

Import MonadNotation.
Open Scope monad_scope.
Open Scope refinement_scope.

Definition PrePost (A B : Type) : Type :=
  ((A -> Prop) * (A -> B -> Prop))%type.

Definition PrePost_eq {A B} (x y : PrePost A B) : Prop :=
  (forall a, fst x a <-> fst y a) /\
  (forall a b, snd x a b <-> snd y a b).

#[global] Instance PrePost_eq_Equivalence {A B} :
  Equivalence (@PrePost_eq A B).
Proof.
  constructor.
  - intros x. split; reflexivity.
  - intros x y [HP HR]. split; intros; symmetry; auto.
  - intros x y z [HP1 HR1] [HP2 HR2].
    split; intros; etransitivity; eauto.
Qed.

Definition PrePost_le {A B} (x y : PrePost A B) : Prop :=
  (forall a, fst y a -> fst x a) /\
  (forall a b, snd x a b -> snd y a b).

Definition PP (S A : Type) : Type :=
  PrePost S (option (A * S)).

Definition retPP {S A} (a : A) : PP S A :=
  (fun _ => True, fun s r => r = Some (a, s)).

Definition bindPP {S A B}
  (m : PP S A) (k : A -> PP S B) : PP S B :=
  ( fun s =>
      fst m s /\
      forall a s', snd m s (Some (a, s')) -> fst (k a) s'
  , fun s r =>
      (r = None /\ snd m s None) \/
      exists a s',
        snd m s (Some (a, s')) /\ snd (k a) s' r
  ).

#[global] Instance Monad_PP (S : Type) : Monad (PP S) := {
  ret := fun A => @retPP S A;
  bind := fun A B => @bindPP S A B
}.

Definition Eq1_PP (S : Type) : Eq1 (PP S) :=
  fun A => @PrePost_eq S (option (A * S)).

#[global] Instance Eq1Equivalence_PP (S : Type) :
  @Eq1Equivalence (PP S) (Monad_PP S) (Eq1_PP S).
Proof.
  intro A. exact (@PrePost_eq_Equivalence S (option (A * S))).
Qed.

#[global] Instance MonadLawsE_PP (S : Type) :
  @MonadLawsE (PP S) (Eq1_PP S) (Monad_PP S).
Proof.
  constructor.
  - intros A B f a.
    unfold eq1, Eq1_PP, bindPP, retPP; cbn.
    split; intros; sauto limit: 200.
  - intros A m.
    unfold eq1, Eq1_PP, bindPP, retPP; cbn.
    split; intros; sauto limit: 200.
  - intros A B C m f g.
    unfold eq1, Eq1_PP, bindPP; cbn.
    split; intros; sauto limit: 200.
  - intros A B x y Hxy f g Hfg.
    unfold eq1, Eq1_PP, PrePost_eq, bindPP in *; cbn in *.
    destruct Hxy as [Hpre Hpost].
    split.
    + intros s. split.
      * intros [Hx Hk]. split.
        -- apply (proj1 (Hpre s)). exact Hx.
        -- intros a s' Hy.
           destruct (Hfg a) as [HfgP _].
           apply (proj1 (HfgP s')), Hk.
           apply (proj2 (Hpost s (Some (a, s')))). exact Hy.
      * intros [Hy Hk]. split.
        -- apply (proj2 (Hpre s)). exact Hy.
        -- intros a s' Hx.
           destruct (Hfg a) as [HfgP _].
           apply (proj2 (HfgP s')), Hk.
           apply (proj1 (Hpost s (Some (a, s')))). exact Hx.
    + intros s r. split.
      * intros [[Hr Hnone] | [a [s' [Hstep Hrest]]]].
        -- left. split; [exact Hr |].
           apply (proj1 (Hpost s None)). exact Hnone.
        -- right. exists a, s'. split.
           ++ apply (proj1 (Hpost s (Some (a, s')))). exact Hstep.
           ++ destruct (Hfg a) as [_ HfgR].
              apply (proj1 (HfgR s' r)). exact Hrest.
      * intros [[Hr Hnone] | [a [s' [Hstep Hrest]]]].
        -- left. split; [exact Hr |].
           apply (proj2 (Hpost s None)). exact Hnone.
        -- right. exists a, s'. split.
           ++ apply (proj2 (Hpost s (Some (a, s')))). exact Hstep.
           ++ destruct (Hfg a) as [_ HfgR].
              apply (proj2 (HfgR s' r)). exact Hrest.
Qed.

(** Hoare refinement is contravariant in the precondition and covariant
    in the postcondition. *)
Definition ppLe (S : Type) : OrderM (PP S) :=
  fun A => @PrePost_le S (option (A * S)).

#[global] Instance RefinementOrder_PP (S : Type) :
  RefinementOrder (PP S) := {
  refines := ppLe S
}.

#[global] Instance OrderedMonad_PP (S : Type) :
  @OrderedMonad (PP S) (Monad_PP S) (ppLe S).
Proof.
  constructor.
  - intros A x. split; intros; assumption.
  - intros A x y z [HxyP HxyR] [HyzP HyzR].
    split; intros; eauto.
  - intros A B x y f g [HxyP HxyR] Hfg.
    unfold ppLe, PrePost_le, bindPP in *; cbn in *.
    split.
    + intros s [Hy Hkg]. split.
      * apply HxyP. exact Hy.
      * intros a s' Hx.
        destruct (Hfg a) as [HfgP _].
        apply HfgP, Hkg, HxyR. exact Hx.
    + intros s r Hx.
      destruct Hx as [[Hr Hnone] | [a [s' [Hstep Hrest]]]].
      * left. split; [exact Hr | apply HxyR; exact Hnone].
      * right. exists a, s'. split.
        -- apply HxyR. exact Hstep.
        -- destruct (Hfg a) as [_ HfgR].
           apply HfgR. exact Hrest.
Qed.

Lemma eqLePP {S A} (x y : PP S A) :
  @eq1 (PP S) (Eq1_PP S) A x y -> ppLe S A x y.
Proof.
  intros [Hpre Hpost]. split.
  - intros s Hy. apply (proj2 (Hpre s)). exact Hy.
  - intros s r Hx. apply (proj1 (Hpost s r)). exact Hx.
Qed.

Definition falsePP {S A} : PP S A :=
  (fun _ => True, fun _ _ => False).

Definition truePP {S A} : PP S A :=
  (fun _ => False, fun _ _ => True).

Definition truthPP (S : Type) : TruthOrder (PP S) (ppLe S).
Proof.
  refine {| trueW := fun A => @truePP S A;
            falseW := fun A => @falsePP S A;
            truthPolarity := Forward |}.
  intros A w. split; split; cbn; intros; try contradiction; exact I.
Defined.

#[program] Definition pp2wp {S A} (pq : PP S A) : ProgWP S A := {|
  runProgWP :=
    mkStateT (fun s =>
      @mkOptionT PureWP _ (fun q =>
        fst pq s /\ forall r, snd pq s r -> q r))
|}.

#[global] Instance pp2wpMorphism (S : Type) :
  @MonadMorphism (PP S) (ProgWP S)
    (Monad_PP S) (Monad__ProgWP S) (Eq1__ProgWP S) (@pp2wp S).
Proof.
  constructor.
  - intros A a. apply wpExt. intros s q.
    cbn. firstorder congruence.
  - intros A B m k. apply wpExt. intros s q.
    cbn. split.
    + intros [[Hm Hpre] Hpost]. split; [exact Hm |].
      intros [[a s']|] Hstep.
      * split.
        -- apply (Hpre a s'). exact Hstep.
        -- intros r Hrest. apply Hpost. right.
           exists a, s'. split; assumption.
      * apply Hpost. left. split; [reflexivity | exact Hstep].
    + intros [Hm Hpost]. split.
      * split; [exact Hm |].
        intros a s' Hstep.
        exact (proj1 (Hpost (Some (a, s')) Hstep)).
      * intros r [[Hr Hnone] | [a [s' [Hstep Hrest]]]].
        -- subst r. exact (Hpost None Hnone).
        -- exact (proj2 (Hpost (Some (a, s')) Hstep) r Hrest).
Qed.

Definition wp2pp {S A} (w : ProgWP S A) : PP S A :=
  ( fun s =>
      unOptionT (runStateT (runProgWP w) s) (fun _ => True)
  , fun s r =>
      forall q,
        unOptionT (runStateT (runProgWP w) s) q -> q r
  ).

Theorem pp_wp_galois {S A} (pq : PP S A) (w : ProgWP S A) :
  pp2wp pq ⊑ w <-> pq ⊑ wp2pp w.
Proof.
  change (wpLe S A (pp2wp pq) w <-> ppLe S A pq (wp2pp w)).
  unfold wpLe, ppLe, PrePost_le, pp2wp, wp2pp; cbn.
  split.
  - intros H. split.
    + intros s Hw. exact (proj1 (H s (fun _ => True) Hw)).
    + intros s r Hr q Hw. exact (proj2 (H s q Hw) r Hr).
  - intros [Hpre Hpost] s q Hw. split.
    + apply Hpre.
      eapply progWPMono.
      * intros. exact I.
      * exact Hw.
    + intros r Hr. exact (Hpost s r Hr q Hw).
Qed.

(** ** [PP] specifications as raw SP comparison targets

    The legacy "full-pre / forget-pre" adjunction [sp2pp] / [pp2sp] was an
    artefact of the old relation carrier [ProgSP S A = S -> option (A * S) ->
    Prop], whose second component was literally the postcondition field of
    [PP].  An SP specification is now a PREDICATE TRANSFORMER
    [(S -> Prop) -> option (A * S) -> Prop], so that adjunction is neither
    typeable nor meaningful and has been removed rather than kept as a
    misleading wrapper.

    Its role is taken by the two raw comparison targets [pp2_over] and
    [pp2_under] of [SPSpec.v]: they turn a [PP]-style pre/post pair into a
    plain (unhealthy) [ProgSP], and both triple directions become inclusions
    in [ordProgSP].  Neither target is healthy — at the empty precondition
    [pp2_over] still yields [post r], and at the full one [pp2_under] holds
    with no single state carrying [pre] — which is exactly why the comparison
    happens in the ambient [ProgSP] and not inside a monad.

    The only property the characterisation needs is monotonicity of the
    observation in its precondition, which all four healthy monads have. *)

Definition MonoSP {S A} (w : @ProgSP S A) : Prop :=
  forall (P Q : S -> Prop) (r : option (A * S)),
    (forall s, P s -> Q s) -> w P r -> w Q r.

Theorem sp_over_raw {S A} (w : @ProgSP S A) (Hmono : MonoSP w)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  (forall r, w pre r -> post r) <-> ordProgSP w (pp2_over pre post).
Proof.
  unfold ordProgSP, pp2_over. split.
  - intros H p r Hw Hsub. exact (H r (Hmono p pre r Hsub Hw)).
  - intros H r Hw. exact (H pre r Hw (fun s Hs => Hs)).
Qed.

Theorem sp_under_raw {S A} (w : @ProgSP S A) (Hmono : MonoSP w)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  (forall r, post r -> w pre r) <-> ordProgSP (pp2_under pre post) w.
Proof.
  unfold ordProgSP, pp2_under. split.
  - intros H p r [Hsub Hpost]. exact (Hmono pre p r Hsub (H r Hpost)).
  - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
Qed.

Definition unaryPP {S A}
  (pre : S -> Prop) (post : option (A * S) -> Prop) : PP S A :=
  (pre, fun _ => post).

(** These interpretations preserve the direct triple quantifier order.
    The Galois connections above transport the refinement orientation
    supported by each adjunction; no reverse adjunction is assumed. *)
Definition wpPPApproxOps {M S}
  (direction : Direction) (recipe : LogicRecipe M (ProgWP S)) :
  @ApproxOps M (ProgWP S) direction recipe (PP S) := {|
  approxRel :=
    fun A m pq =>
      match direction with
      | Over =>
          forall s,
            fst pq s ->
            unOptionT
              (runStateT (runProgWP (theta (recipeDM recipe) A m)) s)
              (snd pq s)
      | Under =>
          forall s,
            unOptionT
              (runStateT (runProgWP (theta (recipeDM recipe) A m)) s)
              (snd pq s) ->
            fst pq s
      end
|}.

#[global] Existing Instance wpPPApproxOps.

Class DefaultState (S : Type) := {
  defaultState : S
}.

Arguments defaultState {S DefaultState}.

#[global] Instance DefaultState_nat : DefaultState nat := {
  defaultState := 0
}.

#[global] Instance DefaultState_prod {A B}
  `{DefaultState A} `{DefaultState B} : DefaultState (A * B) := {
  defaultState := (defaultState, defaultState)
}.

Definition closedPost {S A} `{DefaultState S} (pq : PP S A)
  (r : option (A * S)) : Prop :=
  snd pq defaultState r.

Definition spPPApproxOps {M W S}
  `{DefaultState S}
  (direction : Direction) (recipe : LogicRecipe M W)
  (read : forall A, W A -> (S -> Prop) -> option (A * S) -> Prop) :
  @ApproxOps M W direction recipe (PP S) := {|
  approxRel :=
    fun A m pq =>
      match direction with
      | Over =>
          forall r,
            read A (theta (recipeDM recipe) A m) (fst pq) r ->
            closedPost pq r
      | Under =>
          forall r,
            closedPost pq r ->
            read A (theta (recipeDM recipe) A m) (fst pq) r
      end
|}.

Theorem wpPPApprox_unary {M S A}
  (direction : Direction) (recipe : LogicRecipe M (ProgWP S))
  (m : M A) (pre : S -> Prop) (post : option (A * S) -> Prop) :
  @Approx M (ProgWP S) (PP S) direction recipe
    (wpPPApproxOps direction recipe) A m (unaryPP pre post) <->
  match direction with
  | Over =>
      forall s, pre s ->
        unOptionT
          (runStateT (runProgWP (theta (recipeDM recipe) A m)) s) post
  | Under =>
      forall s,
        unOptionT
          (runStateT (runProgWP (theta (recipeDM recipe) A m)) s) post ->
        pre s
  end.
Proof. destruct direction; reflexivity. Qed.

Theorem spPPApprox_unary {M W S A}
  `{DefaultState S}
  (direction : Direction) (recipe : LogicRecipe M W)
  (read : forall B, W B -> (S -> Prop) -> option (B * S) -> Prop)
  (m : M A) (pre : S -> Prop) (post : option (A * S) -> Prop) :
  @Approx M W (PP S) direction recipe
    (spPPApproxOps direction recipe read) A m (unaryPP pre post) <->
  match direction with
  | Over =>
      forall r, read A (theta (recipeDM recipe) A m) pre r -> post r
  | Under =>
      forall r, post r -> read A (theta (recipeDM recipe) A m) pre r
  end.
Proof. destruct direction; reflexivity. Qed.
