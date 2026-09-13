(** * Dijkstra monads of the WP observations of [stdivexcnd]

    DM4All's [Dtheta] construction over the four observations of
    [EffectObservations/WP/StDivExcNonDet_WStExc.v], its incorrectness dual
    [Dop], specified nondeterministic choice, and the worked examples of that
    file as Dijkstra typings. *)

From Coq Require Import Lia Classical_Prop PeanoNat Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.Arrows Require Import Rel SPostArr.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** Generic [WStExc] facts                                        *)
(* ================================================================= *)

(** The ingredients DM4All's [Dtheta] needs from the specification monad:
    a preorder, monotonicity of [bind] in both arguments ([Pos]-enrichment),
    and the fact that every element is monotone in its postcondition -- the
    latter is free here, since the [WPure] layer carries monotonicity in its
    carrier rather than as a side condition. *)

Section WStExcFacts.

  Variable S : Type.

  Lemma WStExc_mono {A} (w : WStExc S A) s (p q : option (A * S) -> Prop) :
    (forall r, p r -> q r) ->
    unOptionT (runStateT w s) p -> unOptionT (runStateT w s) q.
  Proof. exact (proj2_sig (unOptionT (runStateT w s)) p q). Qed.

  Lemma retP_unfold {A} (a : A) s p :
    unOptionT (runStateT (WPureMonad.retP S a) s) p <-> p (Some (a, s)).
  Proof. cbn. split; intro H; exact H. Qed.

  (** [bindP] is exactly the shape on the right of [obsDWP_bind] &c., up to
      the [prod] eta the kernel does not perform. *)
  Lemma bindP_unfold {A B} (w : WStExc S A) (k : A -> WStExc S B) s p :
    unOptionT (runStateT (WPureMonad.bindP S w k) s) p <->
    unOptionT (runStateT w s)
      (fun rx => match rx with
                 | Some (a, s') => unOptionT (runStateT (k a) s') p
                 | None => p None
                 end).
  Proof.
    cbn. split; intro H; revert H;
      apply WStExc_mono; intros [[a s']|]; cbn; intro H; exact H.
  Qed.

  #[global] Instance ordWStExc_PreOrder {A} : PreOrder (@ordWStExc S A).
  Proof.
    constructor.
    - intros w s p H. exact H.
    - intros w1 w2 w3 H1 H2 s p H. exact (H1 s p (H2 s p H)).
  Qed.

  Lemma ordWStExc_bindP {A B} (w w' : WStExc S A) (k k' : A -> WStExc S B) :
    ordWStExc w w' -> (forall a, ordWStExc (k a) (k' a)) ->
    ordWStExc (WPureMonad.bindP S w k) (WPureMonad.bindP S w' k').
  Proof.
    intros Hw Hk s p H.
    apply bindP_unfold. apply bindP_unfold in H.
    apply Hw in H. revert H. apply WStExc_mono.
    intros [[a s']|] Hr; [ exact (Hk a s' p Hr) | exact Hr ].
  Qed.

End WStExcFacts.

(* ================================================================= *)
(** ** Meets, joins, top and bottom on [WStExc]                      *)
(* ================================================================= *)

(** [orP] and [spinP] are not monadic operations, so the Dijkstra monad
    below cannot type them through [ret]/[bind].  They are given specs
    instead, and the four observations split into two algebras: the
    DEMONIC ones send [orP] to a meet and the ANGELIC ones to a join;
    divergence is [bot] for the TOTAL readings and [top] for the LIBERAL
    ones.  This is the extra structure a specification *monad* does not
    supply by itself. *)

Section WStExcLattice.

  Variable S : Type.

  Lemma meetWStExc_mono {A} (w1 w2 : WStExc S A) s :
    wpure_mono (fun p => unOptionT (runStateT w1 s) p /\ unOptionT (runStateT w2 s) p).
  Proof.
    intros p q Hpq [H1 H2]; split;
      [ exact (WStExc_mono S w1 s p q Hpq H1) | exact (WStExc_mono S w2 s p q Hpq H2) ].
  Qed.

  Definition meetWStExc {A} (w1 w2 : WStExc S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (meetWStExc_mono w1 w2 s))).

  Lemma joinWStExc_mono {A} (w1 w2 : WStExc S A) s :
    wpure_mono (fun p => unOptionT (runStateT w1 s) p \/ unOptionT (runStateT w2 s) p).
  Proof.
    intros p q Hpq [H|H];
      [ left; exact (WStExc_mono S w1 s p q Hpq H)
      | right; exact (WStExc_mono S w2 s p q Hpq H) ].
  Qed.

  Definition joinWStExc {A} (w1 w2 : WStExc S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (joinWStExc_mono w1 w2 s))).

  Definition topWStExc {A} : WStExc S A :=
    mkStateT (fun _ => @mkOptionT WPure _ (mkWPure (fun _ => True) (fun _ _ _ _ => I))).

  Lemma botWStExc_mono {A} : wpure_mono (fun _ : option (A * S) -> Prop => False).
  Proof. intros p q _ H. exact H. Qed.

  Definition botWStExc {A} : WStExc S A :=
    mkStateT (fun _ => @mkOptionT WPure _ (mkWPure _ (@botWStExc_mono A))).

  Lemma meetWStExc_mono2 {A} (w1 w1' w2 w2' : WStExc S A) :
    ordWStExc w1 w1' -> ordWStExc w2 w2' ->
    ordWStExc (meetWStExc w1 w2) (meetWStExc w1' w2').
  Proof. intros H1 H2 s p [Ha Hb]. split; [ exact (H1 s p Ha) | exact (H2 s p Hb) ]. Qed.

  Lemma joinWStExc_mono2 {A} (w1 w1' w2 w2' : WStExc S A) :
    ordWStExc w1 w1' -> ordWStExc w2 w2' ->
    ordWStExc (joinWStExc w1 w2) (joinWStExc w1' w2').
  Proof. intros H1 H2 s p [Ha|Hb]; [ left; exact (H1 s p Ha) | right; exact (H2 s p Hb) ]. Qed.

  (** Demonic choice is a meet. *)
  Lemma obsDWP_or {A} (m1 m2 : stdivexcnd S A) s p :
    unOptionT (runStateT (obsDWP (orP _ m1 m2)) s) p <->
    unOptionT (runStateT (meetWStExc (obsDWP m1) (obsDWP m2)) s) p.
  Proof.
    rewrite obsDWP_unfold. cbn. setoid_rewrite obsDWP_unfold. split.
    - intro H. split; intros oa Hoa; apply H; [ left | right ]; exact Hoa.
    - intros [H1 H2] oa [Hoa|Hoa]; [ exact (H1 oa Hoa) | exact (H2 oa Hoa) ].
  Qed.

  Lemma obsDWLP_or {A} (m1 m2 : stdivexcnd S A) s p :
    unOptionT (runStateT (obsDWLP (orP _ m1 m2)) s) p <->
    unOptionT (runStateT (meetWStExc (obsDWLP m1) (obsDWLP m2)) s) p.
  Proof.
    rewrite obsDWLP_unfold. cbn. setoid_rewrite obsDWLP_unfold. split.
    - intro H. split; intros oa Hoa; apply H; [ left | right ]; exact Hoa.
    - intros [H1 H2] oa [Hoa|Hoa]; [ exact (H1 oa Hoa) | exact (H2 oa Hoa) ].
  Qed.

  (** Angelic choice is a join. *)
  Lemma obsAWP_or {A} (m1 m2 : stdivexcnd S A) s p :
    unOptionT (runStateT (obsAWP (orP _ m1 m2)) s) p <->
    unOptionT (runStateT (joinWStExc (obsAWP m1) (obsAWP m2)) s) p.
  Proof.
    rewrite obsAWP_unfold. cbn. setoid_rewrite obsAWP_unfold. split.
    - intros [r [[H|H] Hp]]; [ left | right ]; exists r; split; assumption.
    - intros [[r [H Hp]] | [r [H Hp]]]; exists r; split;
        solve [ left; exact H | right; exact H | exact Hp ].
  Qed.

  Lemma obsAWLP_or {A} (m1 m2 : stdivexcnd S A) s p :
    unOptionT (runStateT (obsAWLP (orP _ m1 m2)) s) p <->
    unOptionT (runStateT (joinWStExc (obsAWLP m1) (obsAWLP m2)) s) p.
  Proof.
    rewrite obsAWLP_unfold. cbn. setoid_rewrite obsAWLP_unfold. split.
    - intros [[r [[H|H] Hp]] | [H|H]].
      + left; left; exists r; split; assumption.
      + right; left; exists r; split; assumption.
      + left; right; exact H.
      + right; right; exact H.
    - intros [[[r [H Hp]] | H] | [[r [H Hp]] | H]].
      + left; exists r; split; [ left; exact H | exact Hp ].
      + right; left; exact H.
      + left; exists r; split; [ right; exact H | exact Hp ].
      + right; right; exact H.
  Qed.

  (** Divergence is unsatisfiable for the total readings... *)
  Lemma obsDWP_spin {A} s p :
    unOptionT (runStateT (obsDWP (@spinP S A)) s) p <->
    unOptionT (runStateT (@botWStExc A) s) p.
  Proof.
    rewrite obsDWP_unfold. cbn. split; [ intro H; exact (H None eq_refl) | intros [] ].
  Qed.

  Lemma obsAWP_spin {A} s p :
    unOptionT (runStateT (obsAWP (@spinP S A)) s) p <->
    unOptionT (runStateT (@botWStExc A) s) p.
  Proof.
    rewrite obsAWP_unfold. cbn.
    split; [ intros [r [H _]]; discriminate H | intros [] ].
  Qed.

  (** ...and trivially satisfied for the liberal ones. *)
  Lemma obsDWLP_spin {A} s p :
    unOptionT (runStateT (obsDWLP (@spinP S A)) s) p <->
    unOptionT (runStateT (@topWStExc A) s) p.
  Proof.
    rewrite obsDWLP_unfold. cbn. split; [ intros _; exact I |].
    intros _ oa Hoa. cbn in Hoa. subst oa. exact I.
  Qed.

  Lemma obsAWLP_spin {A} s p :
    unOptionT (runStateT (obsAWLP (@spinP S A)) s) p <->
    unOptionT (runStateT (@topWStExc A) s) p.
  Proof.
    rewrite obsAWLP_unfold. cbn. split; [ intros _; exact I |].
    intros _. right. reflexivity.
  Qed.

End WStExcLattice.

(* ================================================================= *)
(** ** The Dijkstra monad of an effect observation                   *)
(* ================================================================= *)

(** DM4All's [Dtheta] (SPropMonadicStructures.v, section [OfMorphism]):
    given a monad morphism [theta : M ~> W] into an ordered specification
    monad, the Dijkstra monad is the subset type

        D A w := { m : M A | theta m <= w }

    with [ret] indexed by [ret^W], [bind] by [bind^W], and weakening along
    the refinement order.  Here [M = stdivexcnd S], [W = WStExc S], and
    [theta] is any of the four WP observations; [ordWStExc] is that same
    refinement order, so DM4All's [theta m <= w] is [ordWStExc (obs m) w]
    -- exactly the
    [tripleWPspec _ SubsetOf] side condition.

    The two hypotheses are precisely the monad morphism laws already
    proved above, so the four observations each yield a Dijkstra monad.
    Notice that no [SProp] and no proof irrelevance is needed: the
    membership condition is a [Prop] the carrier never depends on. *)

Section DijkstraOfObservation.

  Variable S : Type.
  Variable obs : forall A, stdivexcnd S A -> WStExc S A.
  Arguments obs {A} _.

  Hypothesis obs_ret : forall A (a : A) (s : S) p,
    unOptionT (runStateT (obs (ret a)) s) p <->
    unOptionT (runStateT (WPureMonad.retP S a) s) p.

  Hypothesis obs_bind : forall A B (x : stdivexcnd S A) (f : A -> stdivexcnd S B) s p,
    unOptionT (runStateT (obs (x >>= f)) s) p <->
    unOptionT (runStateT (obs x) s)
      (fun rx => match rx with
                 | Some (a, s') => unOptionT (runStateT (obs (f a)) s') p
                 | None => p None
                 end).

  #[local] Existing Instance Eq1__stdivexcnd.
  #[local] Existing Instance MonadLawsE__stdivexcnd.
  #[local] Instance Eq1Equivalence__stdivexcnd
    : @Eq1Equivalence (stdivexcnd S) (Monad__stdivexcnd S) (Eq1__stdivexcnd S)
    := Eq1Equivalence_stateT S (optionT (optionT SetM)).

  (** The morphism laws, restated as refinements in both directions. *)
  Lemma obs_ret_eq {A} (a : A) :
    ordWStExc (WPureMonad.retP S a) (obs (ret a)) /\ ordWStExc (obs (ret a)) (WPureMonad.retP S a).
  Proof. split; intros s p H; apply obs_ret; exact H. Qed.

  Lemma obs_bind_eq {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    ordWStExc (WPureMonad.bindP S (obs x) (fun a => obs (f a))) (obs (x >>= f)) /\
    ordWStExc (obs (x >>= f)) (WPureMonad.bindP S (obs x) (fun a => obs (f a))).
  Proof.
    split; intros s p H;
      [ apply bindP_unfold; apply obs_bind; exact H
      | apply obs_bind; apply bindP_unfold; exact H ].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** [D]: computations meeting their specification              *)
  (* --------------------------------------------------------------- *)

  Definition D {A} (w : WStExc S A) : Type :=
    { m : stdivexcnd S A | ordWStExc (obs m) w }.

  #[program] Definition retD {A} (a : A) : D (WPureMonad.retP S a) :=
    @ret (stdivexcnd S) _ A a.
  Next Obligation. apply obs_ret_eq. Qed.

  #[program] Definition bindD {A B} {w : WStExc S A} {wf : A -> WStExc S B}
    (m : D w) (f : forall a, D (wf a)) : D (WPureMonad.bindP S w wf) :=
    @bind (stdivexcnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [ apply obs_bind_eq |].
    apply ordWStExc_bindP; [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  (** Rule of consequence. *)
  #[program] Definition wknD {A} {w w' : WStExc S A}
    (Hle : ordWStExc w w') (m : D w) : D w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact (proj2_sig m) | exact Hle ]. Qed.

  (** Every computation meets its own observation -- DM4All's [lift]. *)
  #[program] Definition liftD {A} (m : stdivexcnd S A) : D (obs m) := m.
  Next Obligation. reflexivity. Qed.

  Lemma retD_carrier {A} (a : A) : proj1_sig (retD a) = @ret (stdivexcnd S) _ A a.
  Proof. reflexivity. Qed.

  Lemma bindD_carrier {A B} {w : WStExc S A} {wf : A -> WStExc S B}
    (m : D w) (f : forall a, D (wf a)) :
    proj1_sig (bindD m f) =
    @bind (stdivexcnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Proof. reflexivity. Qed.

  (** The monad laws.  DM4All states them as heterogeneous equalities
      transported along the spec monad's own laws; here [WStExc]'s laws
      hold up to [eq1] and not up to [eq], so the honest rendering is to
      compare CARRIERS up to [eq1] -- the indices differ by the
      corresponding [WStExc] law, which [wknD] absorbs. *)
  Definition D_eq {A} {w w' : WStExc S A} (m : D w) (n : D w') : Prop :=
    eq1 (proj1_sig m) (proj1_sig n).

  Lemma D_bind_ret_l {A B} (a : A) (wf : A -> WStExc S B) (f : forall x, D (wf x)) :
    D_eq (bindD (retD a) f) (f a).
  Proof.
    unfold D_eq.
    change (proj1_sig (bindD (retD a) f))
      with (@bind (stdivexcnd S) _ A B (@ret (stdivexcnd S) _ A a)
              (fun x => proj1_sig (f x))).
    rewrite bind_ret_l. reflexivity.
  Qed.

  Lemma D_bind_ret_r {A} (w : WStExc S A) (m : D w) : D_eq (bindD m retD) m.
  Proof.
    unfold D_eq.
    change (proj1_sig (bindD m retD))
      with (@bind (stdivexcnd S) _ A A (proj1_sig m) (fun y => @ret (stdivexcnd S) _ A y)).
    rewrite bind_ret_r. reflexivity.
  Qed.

  Lemma D_bind_bind {A B C} {w : WStExc S A} {wf : A -> WStExc S B}
    {wg : B -> WStExc S C}
    (m : D w) (f : forall a, D (wf a)) (g : forall b, D (wg b)) :
    D_eq (bindD (bindD m f) g) (bindD m (fun a => bindD (f a) g)).
  Proof. unfold D_eq. rewrite !bindD_carrier. rewrite bind_bind. reflexivity. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Nondeterministic choice, specified                         *)
  (* --------------------------------------------------------------- *)

  (** [orP] is not reachable from [ret]/[bind], so it gets its own rule,
      parametric in whichever binary spec combinator the observation
      turns it into (a meet demonically, a join angelically). *)
  Section Choice.

    Variable comb : forall A, WStExc S A -> WStExc S A -> WStExc S A.
    Arguments comb {A} _ _.

    Hypothesis comb_mono : forall A (w1 w1' w2 w2' : WStExc S A),
      ordWStExc w1 w1' -> ordWStExc w2 w2' -> ordWStExc (comb w1 w2) (comb w1' w2').

    Hypothesis obs_or : forall A (m1 m2 : stdivexcnd S A) s p,
      unOptionT (runStateT (obs (orP _ m1 m2)) s) p <->
      unOptionT (runStateT (comb (obs m1) (obs m2)) s) p.

    #[program] Definition orD {A} {w1 w2 : WStExc S A}
      (m1 : D w1) (m2 : D w2) : D (comb w1 w2) :=
      orP _ (proj1_sig m1) (proj1_sig m2).
    Next Obligation.
      intros s p H. apply obs_or.
      apply (comb_mono A (obs (proj1_sig m1)) w1 (obs (proj1_sig m2)) w2);
        [ exact (proj2_sig m1) | exact (proj2_sig m2) | exact H ].
    Qed.

  End Choice.

  (* --------------------------------------------------------------- *)
  (** *** [Dop]: the incorrectness dual                              *)
  (* --------------------------------------------------------------- *)

  (** The [SupersetOf] triples of this file are not of DM4All's shape:
      they ask for [obs m <= w], the opposite refinement.  The same two
      morphism laws give that dual a monad structure, because [bindP] is
      monotone in both arguments in EITHER direction. *)

  Definition Dop {A} (w : WStExc S A) : Type :=
    { m : stdivexcnd S A | ordWStExc w (obs m) }.

  #[program] Definition retDop {A} (a : A) : Dop (WPureMonad.retP S a) :=
    @ret (stdivexcnd S) _ A a.
  Next Obligation. apply obs_ret_eq. Qed.

  #[program] Definition bindDop {A B} {w : WStExc S A} {wf : A -> WStExc S B}
    (m : Dop w) (f : forall a, Dop (wf a)) : Dop (WPureMonad.bindP S w wf) :=
    @bind (stdivexcnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply obs_bind_eq ].
    apply ordWStExc_bindP; [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition wknDop {A} {w w' : WStExc S A}
    (Hle : ordWStExc w' w) (m : Dop w) : Dop w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition liftDop {A} (m : stdivexcnd S A) : Dop (obs m) := m.
  Next Obligation. reflexivity. Qed.

End DijkstraOfObservation.

(* ================================================================= *)
(** ** Triples are exactly Dijkstra typings                          *)
(* ================================================================= *)

Section DijkstraTriples.

  Variable S : Type.
  Variable obs : forall A, stdivexcnd S A -> WStExc S A.
  Arguments obs {A} _.

  (** [SubsetOf] (correctness): the pre/post pair read as a [WStExc]
      element is the index, and the triple is the membership proof.  The
      monotonicity side condition of [tripleWPDefEq] is discharged by
      [WStExc_mono], which holds for every element. *)
  #[program] Definition ofTripleSub {A} (prog : stdivexcnd S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop)
    (H : tripleWP (@obs A) prog pre SubsetOf post)
    : D S (@obs) (pp2wp_subset pre post) := prog.
  Next Obligation.
    apply (tripleWPDefEq S (@obs A) prog SubsetOf pre post (WStExc_mono S (obs prog))).
    exact H.
  Qed.

  (** [SupersetOf] (incorrectness): same, in the dual monad. *)
  #[program] Definition ofTripleSup {A} (prog : stdivexcnd S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop)
    (H : tripleWP (@obs A) prog pre SupersetOf post)
    : Dop S (@obs) (pp2wp_superset pre post) := prog.
  Next Obligation.
    apply (tripleWPDefEq S (@obs A) prog SupersetOf pre post (WStExc_mono S (obs prog))).
    exact H.
  Qed.

  Lemma toTripleSub {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (d : D S (@obs) (pp2wp_subset pre post)) :
    tripleWP (@obs A) (proj1_sig d) pre SubsetOf post.
  Proof.
    apply (tripleWPDefEq S (@obs A) (proj1_sig d) SubsetOf pre post
             (WStExc_mono S (obs (proj1_sig d)))).
    exact (proj2_sig d).
  Qed.

  Lemma toTripleSup {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (d : Dop S (@obs) (pp2wp_superset pre post)) :
    tripleWP (@obs A) (proj1_sig d) pre SupersetOf post.
  Proof.
    apply (tripleWPDefEq S (@obs A) (proj1_sig d) SupersetOf pre post
             (WStExc_mono S (obs (proj1_sig d)))).
    exact (proj2_sig d).
  Qed.

End DijkstraTriples.

(* ================================================================= *)
(** ** The four Dijkstra monads                                      *)
(* ================================================================= *)

Definition Ddwp  {S A} (w : WStExc S A) : Type := D S (@obsDWP S) w.
Definition Ddwlp {S A} (w : WStExc S A) : Type := D S (@obsDWLP S) w.
Definition Dawp  {S A} (w : WStExc S A) : Type := D S (@obsAWP S) w.
Definition Dawlp {S A} (w : WStExc S A) : Type := D S (@obsAWLP S) w.

Definition Ddwp_op  {S A} (w : WStExc S A) : Type := Dop S (@obsDWP S) w.
Definition Ddwlp_op {S A} (w : WStExc S A) : Type := Dop S (@obsDWLP S) w.
Definition Dawp_op  {S A} (w : WStExc S A) : Type := Dop S (@obsAWP S) w.
Definition Dawlp_op {S A} (w : WStExc S A) : Type := Dop S (@obsAWLP S) w.

Definition Ddwp_ret {S A} (a : A) : Ddwp (WPureMonad.retP S a) := retD S (@obsDWP S) (@obsDWP_ret S) a.
Definition Ddwp_bind {S A B} {w : WStExc S A} {wf : A -> WStExc S B}
  (m : Ddwp w) (f : forall a, Ddwp (wf a)) : Ddwp (WPureMonad.bindP S w wf) :=
  bindD S (@obsDWP S) (@obsDWP_bind S) m f.
Definition Ddwp_lift {S A} (m : stdivexcnd S A) : Ddwp (obsDWP m) := liftD S (@obsDWP S) m.
Definition Ddwp_wkn {S A} {w w' : WStExc S A} (H : ordWStExc w w') (m : Ddwp w) : Ddwp w' :=
  wknD S (@obsDWP S) H m.
Definition Ddwp_or {S A} {w1 w2 : WStExc S A} (m1 : Ddwp w1) (m2 : Ddwp w2)
  : Ddwp (meetWStExc S w1 w2) :=
  orD S (@obsDWP S) (@meetWStExc S) (@meetWStExc_mono2 S) (@obsDWP_or S) m1 m2.

Definition Ddwlp_ret {S A} (a : A) : Ddwlp (WPureMonad.retP S a) := retD S (@obsDWLP S) (@obsDWLP_ret S) a.
Definition Ddwlp_bind {S A B} {w : WStExc S A} {wf : A -> WStExc S B}
  (m : Ddwlp w) (f : forall a, Ddwlp (wf a)) : Ddwlp (WPureMonad.bindP S w wf) :=
  bindD S (@obsDWLP S) (@obsDWLP_bind S) m f.
Definition Ddwlp_lift {S A} (m : stdivexcnd S A) : Ddwlp (obsDWLP m) := liftD S (@obsDWLP S) m.
Definition Ddwlp_wkn {S A} {w w' : WStExc S A} (H : ordWStExc w w') (m : Ddwlp w) : Ddwlp w' :=
  wknD S (@obsDWLP S) H m.
Definition Ddwlp_or {S A} {w1 w2 : WStExc S A} (m1 : Ddwlp w1) (m2 : Ddwlp w2)
  : Ddwlp (meetWStExc S w1 w2) :=
  orD S (@obsDWLP S) (@meetWStExc S) (@meetWStExc_mono2 S) (@obsDWLP_or S) m1 m2.

Definition Dawp_ret {S A} (a : A) : Dawp (WPureMonad.retP S a) := retD S (@obsAWP S) (@obsAWP_ret S) a.
Definition Dawp_bind {S A B} {w : WStExc S A} {wf : A -> WStExc S B}
  (m : Dawp w) (f : forall a, Dawp (wf a)) : Dawp (WPureMonad.bindP S w wf) :=
  bindD S (@obsAWP S) (@obsAWP_bind S) m f.
Definition Dawp_lift {S A} (m : stdivexcnd S A) : Dawp (obsAWP m) := liftD S (@obsAWP S) m.
Definition Dawp_wkn {S A} {w w' : WStExc S A} (H : ordWStExc w w') (m : Dawp w) : Dawp w' :=
  wknD S (@obsAWP S) H m.
Definition Dawp_or {S A} {w1 w2 : WStExc S A} (m1 : Dawp w1) (m2 : Dawp w2)
  : Dawp (joinWStExc S w1 w2) :=
  orD S (@obsAWP S) (@joinWStExc S) (@joinWStExc_mono2 S) (@obsAWP_or S) m1 m2.

Definition Dawlp_ret {S A} (a : A) : Dawlp (WPureMonad.retP S a) := retD S (@obsAWLP S) (@obsAWLP_ret S) a.
Definition Dawlp_bind {S A B} {w : WStExc S A} {wf : A -> WStExc S B}
  (m : Dawlp w) (f : forall a, Dawlp (wf a)) : Dawlp (WPureMonad.bindP S w wf) :=
  bindD S (@obsAWLP S) (@obsAWLP_bind S) m f.
Definition Dawlp_lift {S A} (m : stdivexcnd S A) : Dawlp (obsAWLP m) := liftD S (@obsAWLP S) m.
Definition Dawlp_wkn {S A} {w w' : WStExc S A} (H : ordWStExc w w') (m : Dawlp w) : Dawlp w' :=
  wknD S (@obsAWLP S) H m.
Definition Dawlp_or {S A} {w1 w2 : WStExc S A} (m1 : Dawlp w1) (m2 : Dawlp w2)
  : Dawlp (joinWStExc S w1 w2) :=
  orD S (@obsAWLP S) (@joinWStExc S) (@joinWStExc_mono2 S) (@obsAWLP_or S) m1 m2.

(** Divergence: typeable only in the liberal monads, at [top]. *)
Definition Ddwlp_spin {S A} : Ddwlp (@topWStExc S A) :=
  Ddwlp_wkn (fun s p H => proj2 (obsDWLP_spin S s p) H) (Ddwlp_lift (@spinP S A)).
Definition Dawlp_spin {S A} : Dawlp (@topWStExc S A) :=
  Dawlp_wkn (fun s p H => proj2 (obsAWLP_spin S s p) H) (Dawlp_lift (@spinP S A)).

(* ================================================================= *)
(** ** The examples, as Dijkstra typings                             *)
(* ================================================================= *)

Definition postGe42 : option (unit * nat) -> Prop :=
  fun r => match r with Some (_, s) => s >= 42 | None => False end.
Definition postEq42 : option (unit * nat) -> Prop :=
  fun r => match r with Some (_, s) => s = 42 | None => False end.
Definition postEq43 : option (unit * nat) -> Prop :=
  fun r => match r with Some (_, s) => s = 43 | None => False end.

(** Each [SubsetOf] triple already IS the membership proof of the
    corresponding Dijkstra monad at the spec [pp2wp_subset pre post]. *)
Definition progA_ge42_D : Ddwp (pp2wp_subset (fun _ : nat => True) postGe42) :=
  ofTripleSub nat (@obsDWP nat) progA _ _ progA_DWP_all.

Definition progA_42_D : Dawp (pp2wp_subset (fun _ : nat => True) postEq42) :=
  ofTripleSub nat (@obsAWP nat) progA _ _ progA_AWP_42.

Definition progA_43_D : Dawp (pp2wp_subset (fun _ : nat => True) postEq43) :=
  ofTripleSub nat (@obsAWP nat) progA _ _ progA_AWP_43.

Definition progB_42_Ddwlp : Ddwlp (pp2wp_subset (fun _ : nat => True) postEq42) :=
  ofTripleSub nat (@obsDWLP nat) progB _ _ progB_DWLP_42.

Definition progB_42_Dawp : Dawp (pp2wp_subset (fun _ : nat => True) postEq42) :=
  ofTripleSub nat (@obsAWP nat) progB _ _ progB_AWP_42.

Definition progB_div_Dawlp : Dawlp (pp2wp_subset (fun _ : nat => True) (fun _ => False)) :=
  ofTripleSub nat (@obsAWLP nat) progB _ _ progB_has_divergent_branch.

(** The [SupersetOf] examples live in the dual monad. *)
Definition progA_100_Dawp_op :
  Dawp_op (pp2wp_superset (fun _ : nat => False)
             (fun r : option (unit * nat) => r = Some (tt, 100))) :=
  ofTripleSup nat (@obsAWP nat) progA _ _ progA_AWP_100_over.

Definition progRet_Ddwp_op : Ddwp_op (pp2wp_superset preEq0 postEq0) :=
  ofTripleSup nat (@obsDWP nat) progRet _ _ progRet_dwp_inc.

Definition progRet_Ddwlp_op : Ddwlp_op (pp2wp_superset preEq0 postEq0) :=
  ofTripleSup nat (@obsDWLP nat) progRet _ _ progRet_dwlp_inc.

(** The two negative examples say that no Dijkstra element at that index
    can have the program as its carrier. *)
Theorem progA_not_Ddwp_42 :
  forall d : Ddwp (pp2wp_subset (fun _ : nat => True) postEq42), proj1_sig d <> progA.
Proof.
  intros d Heq. apply progA_DWP_not42.
  pose proof (toTripleSub nat (@obsDWP nat) (fun _ => True) postEq42 d) as H.
  rewrite Heq in H. exact H.
Qed.

Theorem progB_not_Ddwp_42 :
  forall d : Ddwp (pp2wp_subset (fun _ : nat => True) postEq42), proj1_sig d <> progB.
Proof.
  intros d Heq. apply progB_DWP_unprovable.
  pose proof (toTripleSub nat (@obsDWP nat) (fun _ => True) postEq42 d) as H.
  rewrite Heq in H. exact H.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Compositional verification, DM4All-style                     *)
(* ----------------------------------------------------------------- *)

(** Rather than exhibiting a whole triple, build the program out of
    Dijkstra combinators -- its index is then inferred -- and weaken once
    at the end.  The carrier is the original program on the nose. *)

Definition progA_compositional : Ddwp _ :=
  Ddwp_bind (Ddwp_lift (put 42))  (fun _ =>
  Ddwp_bind (Ddwp_lift get)       (fun s : nat =>
  Ddwp_or   (Ddwp_lift (put s)) (Ddwp_lift (put (s + 1))))).

Lemma progA_compositional_carrier : proj1_sig progA_compositional = progA.
Proof. reflexivity. Qed.

Lemma progA_compositional_le :
  ordWStExc (WPureMonad.bindP nat (obsDWP (put 42)) (fun _ =>
             WPureMonad.bindP nat (obsDWP get) (fun s : nat =>
             meetWStExc nat (obsDWP (put s)) (obsDWP (put (s + 1))))))
            (pp2wp_subset (fun _ : nat => True) postGe42).
Proof.
  intros s p [_ Hsub]. cbn.
  intros oa ->. cbn. intros ob ->. cbn. split; intros oc ->; apply Hsub; cbn; lia.
Qed.

Definition progA_ge42_compositional : Ddwp (pp2wp_subset (fun _ : nat => True) postGe42) :=
  Ddwp_wkn progA_compositional_le progA_compositional.

(** [progB] demonic-liberal: the divergent branch contributes [top] to
    the meet, which is why the same spec is unprovable for [obsDWP]
    ([obsDWP_spin] makes it [bot]). *)
Definition progB_compositional_dwlp : Ddwlp _ :=
  Ddwlp_bind (Ddwlp_lift (put 42)) (fun _ =>
  Ddwlp_bind (Ddwlp_lift get)      (fun s : nat =>
  Ddwlp_or   (Ddwlp_lift (put s)) Ddwlp_spin)).

Lemma progB_compositional_dwlp_carrier : proj1_sig progB_compositional_dwlp = progB.
Proof. reflexivity. Qed.

Lemma progB_compositional_dwlp_le :
  ordWStExc (WPureMonad.bindP nat (obsDWLP (put 42)) (fun _ =>
             WPureMonad.bindP nat (obsDWLP get) (fun s : nat =>
             meetWStExc nat (obsDWLP (put s)) (@topWStExc nat unit))))
            (pp2wp_subset (fun _ : nat => True) postEq42).
Proof.
  intros s p [_ Hsub]. cbn.
  intros oa ->. cbn. intros ob ->. cbn. split; [| exact I ].
  intros oc ->. apply Hsub. reflexivity.
Qed.

Definition progB_42_compositional : Ddwlp (pp2wp_subset (fun _ : nat => True) postEq42) :=
  Ddwlp_wkn progB_compositional_dwlp_le progB_compositional_dwlp.

(** [progB] angelic-liberal: the divergent branch is the join's witness,
    so "some branch diverges" is provable with the empty postcondition. *)
Definition progB_compositional_awlp : Dawlp _ :=
  Dawlp_bind (Dawlp_lift (put 42)) (fun _ =>
  Dawlp_bind (Dawlp_lift get)      (fun s : nat =>
  Dawlp_or   (Dawlp_lift (put s)) Dawlp_spin)).

Lemma progB_compositional_awlp_le :
  ordWStExc (WPureMonad.bindP nat (obsAWLP (put 42)) (fun _ =>
             WPureMonad.bindP nat (obsAWLP get) (fun s : nat =>
             joinWStExc nat (obsAWLP (put s)) (@topWStExc nat unit))))
            (pp2wp_subset (fun _ : nat => True) (fun _ => False)).
Proof.
  intros s p [_ _]. cbn. left. exists (Some (tt, 42)). split; [ reflexivity |].
  cbn. left. exists (Some (42, 42)). split; [ reflexivity |].
  cbn. right. exact I.
Qed.

Definition progB_div_compositional
  : Dawlp (pp2wp_subset (fun _ : nat => True) (fun _ => False)) :=
  Dawlp_wkn progB_compositional_awlp_le progB_compositional_awlp.
