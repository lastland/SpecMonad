(** * Demonic liberal strongest postcondition

    [obsDSLP] reads the observed relation demonically and liberally: [r] is
    asserted at [pre] when EVERY state that reaches [r] satisfies [pre].
    Unreachable outcomes are asserted vacuously — that is the "liberal" part,
    and it is what makes [DSLPProgSP] the order-theoretic dual of
    [ASPProgSP]. *)

From Coq Require Import Lia RelationClasses Classical_Prop.
From ExtLib Require Import
  Monad MonadLaws MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program SP PrePost Examples.
From Incorrectness.Recipes.Examples.StExDv.Logics Require Import ASP.

Import MonadNotation.
Open Scope monad_scope.

Section ProgDSLPMonad.
  Variable S : Type.

  Definition MeetPreservingProg {A} (w : ProgSP A) : Prop :=
    TerminatingProg S w /\ ConjunctiveProg S w.

  Definition MSingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : option (A * S)),
      w pre r <-> forall s0, ~ pre s0 -> w (fun s => s <> s0) r.

  (** Dual of [join_to_singleton_prog]: index the meet by the subset
      [{s0 | ~ pre s0}] and take the CO-singleton [fun s => s <> s0] at each
      index.  The intersection of those co-singletons is pointwise [pre] (by
      [NNPP]), and the indexed meet is literally the right-hand side of
      [MSingletonProg]. *)
  Lemma meet_to_msingleton_prog {A} (w : ProgSP A) :
    MeetPreservingProg w -> MSingletonProg w.
  Proof.
    intros [HT HC] pre r.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    destruct (classic (exists s1, ~ pre s1)) as [[s1 Hs1] | Hno].
    - pose proof (HC { s0 : S | ~ pre s0 } (inhabits (exist (fun s0 => ~ pre s0) s1 Hs1))
                    (fun i s => s <> proj1_sig i) r) as Hm.
      cbv beta in Hm.
      assert (Heq : (fun s => forall i : { s0 : S | ~ pre s0 }, s <> proj1_sig i) = pre).
      { apply Hext. intro s. split.
        - intro Hall. apply NNPP. intro Hnp.
          exact (Hall (exist (fun s0 => ~ pre s0) s Hnp) eq_refl).
        - intros Hs i Heq. rewrite Heq in Hs. exact (proj2_sig i Hs). }
      rewrite Heq in Hm. split.
      + intros Hw s0 Hn0.
        exact (proj1 Hm Hw (exist (fun s0' => ~ pre s0') s0 Hn0)).
      + intro Hall. apply Hm. intro i. exact (Hall (proj1_sig i) (proj2_sig i)).
    - assert (Heq : pre = (fun _ : S => True)).
      { apply Hext. intro s. split; [ intros _; exact I |].
        intros _. apply NNPP. intro Hnp. exact (Hno (ex_intro _ s Hnp)). }
      rewrite Heq. split.
      + intros _ s0 Hn0. destruct (Hn0 I).
      + intros _. exact (HT r).
  Qed.

  Lemma msingleton_to_meet_prog {A} (w : ProgSP A) :
    MSingletonProg w -> MeetPreservingProg w.
  Proof.
    intro H. split.
    - intro r. apply (H (fun _ => True) r). intros s0 Hn0. destruct (Hn0 I).
    - intros I i0 p r. split.
      + intros Hw i. apply (H (fun s => p i s) r). intros s0 Hn0.
        exact (proj1 (H (fun s => forall j, p j s) r) Hw s0
                 (fun Hall => Hn0 (Hall i))).
      + intro Hall. apply (H (fun s => forall i, p i s) r). intros s0 Hn0.
        assert (Hex : exists i, ~ p i s0).
        { apply NNPP. intro Hno. apply Hn0. intro i. apply NNPP. intro Hnpi.
          exact (Hno (ex_intro _ i Hnpi)). }
        destruct Hex as [i Hnpi].
        exact (proj1 (H (fun s => p i s) r) (Hall i) s0 Hnpi).
  Qed.

  Theorem meet_iff_msingleton_prog {A} (w : ProgSP A) :
    MeetPreservingProg w <-> MSingletonProg w.
  Proof. split; [apply meet_to_msingleton_prog | apply msingleton_to_meet_prog]. Qed.

  Definition DSLPProgSP (A : Type) : Type := { w : ProgSP A | MSingletonProg w }.

  Definition getProgDSLP {A} (w : DSLPProgSP A) : ProgSP A :=
    proj1_sig w.

  (* ---------------------------------------------------------------- *)
  (** *** Co-set representation                                        *)
  (* ---------------------------------------------------------------- *)

  (** [SingletonProg w] makes [w] the ASP of its singleton values; dually,
      [MSingletonProg w] makes [w] the DSLP of its CO-SET
      [fun s r => ~ w (fun s' => s' <> s) r] ([msingletonProg_repr]).  The
      three lemmas below are all that the two obligations need; each writes
      its predicate transformer out in full rather than naming it. *)

  (** Anything of DSLP shape is [MSingletonProg]. *)
  Lemma dslp_msingleton {A} (R : S -> option (A * S) -> Prop) :
    MSingletonProg (fun pre r => forall s, R s r -> pre s).
  Proof.
    intros pre r. split.
    - intros H s0 Hns0 s Hs Heq. subst s. exact (Hns0 (H s0 Hs)).
    - intros H s Hs. apply NNPP. intro Hnp. exact (H s Hnp s Hs eq_refl).
  Qed.

  (** [MSingletonProg] only ever applies [w], so it transports along pointwise
      equivalence. *)
  Lemma msingletonProg_ext {A} (w1 w2 : ProgSP A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    MSingletonProg w1 -> MSingletonProg w2.
  Proof.
    intros Hext H pre r. split.
    - intros Hw s0 Hns0. apply Hext.
      exact (proj1 (H pre r) (proj2 (Hext pre r) Hw) s0 Hns0).
    - intro Hall. apply Hext. apply (proj2 (H pre r)).
      intros s0 Hns0. exact (proj2 (Hext _ r) (Hall s0 Hns0)).
  Qed.

  (** ... and conversely every [MSingletonProg] transformer IS of DSLP shape,
      for its co-set. *)
  Lemma msingletonProg_repr {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (pre : S -> Prop) (r : option (A * S)) :
    w pre r <-> (forall s, ~ w (fun s' => s' <> s) r -> pre s).
  Proof.
    split.
    - intros Hp s Hns. apply NNPP. intro Hnp.
      exact (Hns (proj1 (Hw pre r) Hp s Hnp)).
    - intro H. apply Hw. intros s0 Hns0.
      destruct (classic (w (fun s' => s' <> s0) r)) as [Hy | Hn];
        [exact Hy | destruct (Hns0 (H s0 Hn))].
  Qed.

  #[program] Definition retDSLPProg {A} (v : A) : DSLPProgSP A :=
    fun pre r => forall s0, r = Some (v, s0) -> pre s0.
  Next Obligation.
  Proof. exact (dslp_msingleton (fun s r => r = Some (v, s))). Qed.

  #[program] Definition bindDSLPProg {A B}
    (m : DSLPProgSP A) (k : A -> DSLPProgSP B) : DSLPProgSP B :=
    fun pre r =>
      (forall a, k a (fun s0 => m pre (Some (a, s0))) r) /\ (r = None -> m pre None).
  Next Obligation.
  Proof.
    pose proof (proj2_sig m) as Hm.
    pose proof (fun a => proj2_sig (k a)) as Hk.
    (* the body is the DSLP of the composite co-set: either [k a] reaches [r]
       from [s'] and [m] reaches [Some (a, s')] from [s], or [m] raises and
       [r = None] *)
    apply (msingletonProg_ext
             (fun pre r =>
                forall s,
                  ((exists a s', ~ proj1_sig (k a) (fun t => t <> s') r
                                 /\ ~ proj1_sig m (fun t => t <> s) (Some (a, s')))
                   \/ (r = None /\ ~ proj1_sig m (fun t => t <> s) None)) -> pre s)).
    - intros pre r. split.
      + intro H. split.
        * intro a. apply (msingletonProg_repr _ (Hk a)). intros s' Hck.
          apply (msingletonProg_repr _ Hm). intros s Hcm.
          apply H. left. exists a, s'. split; assumption.
        * intro Hr. apply (msingletonProg_repr _ Hm). intros s Hcm.
          apply H. right. split; assumption.
      + intros [H1 H2] s [[a [s' [Hck Hcm]]] | [Hr Hcm]].
        * exact (proj1 (msingletonProg_repr _ Hm _ (Some (a, s')))
                   (proj1 (msingletonProg_repr _ (Hk a) _ r) (H1 a) s' Hck) s Hcm).
        * exact (proj1 (msingletonProg_repr _ Hm _ None) (H2 Hr) s Hcm).
    - apply dslp_msingleton.
  Qed.

  #[global]
    Instance Monad_DSLPProgSP : Monad DSLPProgSP :=
    {| ret := fun _ => @retDSLPProg _ ;
      bind := fun _ _ => @bindDSLPProg _ _ |}.

  #[global] Instance Eq1__ProgDSLP : Eq1 DSLPProgSP :=
    fun A m n => forall pre r, getProgDSLP m pre r <-> getProgDSLP n pre r.

  #[global] Instance Eq1Equivalence__DSLPProgSP
    : @Eq1Equivalence DSLPProgSP _ Eq1__ProgDSLP.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  (** Three consequences of [MSingletonProg], all read off the co-set
      representation: monotonicity and congruence in the precondition, and
      preservation of MEETS of preconditions.  The last is what carries
      [bind_bind], dually to [getProg_join] on the ASP side. *)

  Lemma msingletonProg_mono {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros Hsub H. apply (msingletonProg_repr w Hw). intros s Hc.
    exact (Hsub s (proj1 (msingletonProg_repr w Hw P r) H s Hc)).
  Qed.

  Lemma msingletonProg_cong {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s <-> Q s) -> (w P r <-> w Q r).
  Proof.
    intro H. split; intro Hw'.
    - exact (msingletonProg_mono w Hw P Q r (fun s hs => proj1 (H s) hs) Hw').
    - exact (msingletonProg_mono w Hw Q P r (fun s hs => proj2 (H s) hs) Hw').
  Qed.

  Lemma msingletonProg_meet {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (I : Type) (p : I -> (S -> Prop)) (r : option (A * S)) :
    w (fun s => forall i, p i s) r <-> forall i, w (p i) r.
  Proof.
    split.
    - intros H i. apply (msingletonProg_repr w Hw). intros s Hc.
      exact (proj1 (msingletonProg_repr w Hw (fun s0 => forall j, p j s0) r) H s Hc i).
    - intro H. apply (msingletonProg_repr w Hw). intros s Hc i.
      exact (proj1 (msingletonProg_repr w Hw (p i) r) (H i) s Hc).
  Qed.

  #[global] Instance MonadLawsE__ProgDSLP
    : @MonadLawsE DSLPProgSP Eq1__ProgDSLP _.
  Proof.
    constructor.
    - (* bind_ret_l.  [getProgMSP (retDSLPProg x) pre (Some (a, s0))] is
         [forall s1, Some (a, s0) = Some (x, s1) -> pre s1], i.e. [pre s0] when
         [a = x] and vacuously true otherwise — and every [MSingletonProg]
         transformer fires at a vacuously-true precondition. *)
      intros A B f x. unfold eq1, Eq1__ProgDSLP. intros pre r. split.
      + intros [H1 _]. specialize (H1 x).
        exact (msingletonProg_mono _ (proj2_sig (f x)) _ pre r
                 (fun s0 h => h s0 eq_refl) H1).
      + intro H. split.
        * intro a. destruct (classic (a = x)) as [Heq | Hne].
          -- subst a.
             apply (msingletonProg_mono _ (proj2_sig (f x)) pre _ r); [| exact H].
             intros s0 Hp s1 Heq. assert (Hs : s0 = s1) by congruence.
             subst s1. exact Hp.
          -- apply (msingletonProg_repr _ (proj2_sig (f a))).
             intros s _ s1 Heq. exfalso. apply Hne. congruence.
        * intros _ s0 Heq. discriminate Heq.
    - (* bind_ret_r: the [Some] branch reads off at [r]'s own value/state, the
         [None] branch at [r = None] *)
      intros A m. unfold eq1, Eq1__ProgDSLP. intros pre r. split.
      + intros [H1 H2]. destruct r as [[a s0]|].
        * exact (H1 a s0 eq_refl).
        * exact (H2 eq_refl).
      + intro H. split.
        * intros a s0 Heq. subst r. exact H.
        * intro Hr. subst r. exact H.
    - (* bind_bind: the precondition handed to [g b] is a MEET over the
         intermediate value [a], and [g b] preserves meets *)
      intros A B C x f g. unfold eq1, Eq1__ProgDSLP. intros pre r.
      (* a [Some] outcome of [bind x f] never uses its [r = None] conjunct *)
      assert (Hsimp : forall b s1,
        getProgDSLP (bindDSLPProg x f) pre (Some (b, s1)) <->
        forall a, getProgDSLP (f a)
                    (fun s0 => getProgDSLP x pre (Some (a, s0))) (Some (b, s1))).
      { intros b s1. split.
        - intros [H1 _] a. exact (H1 a).
        - intro H. split; [exact H | intro Hc; discriminate Hc]. }
      assert (Hg : forall b,
        getProgDSLP (g b)
          (fun s1 => getProgDSLP (bindDSLPProg x f) pre (Some (b, s1))) r <->
        forall a, getProgDSLP (g b)
                    (fun s1 => getProgDSLP (f a)
                       (fun s0 => getProgDSLP x pre (Some (a, s0))) (Some (b, s1))) r).
      { intro b.
        transitivity (getProgDSLP (g b)
          (fun s1 => forall a, getProgDSLP (f a)
             (fun s0 => getProgDSLP x pre (Some (a, s0))) (Some (b, s1))) r).
        - apply (msingletonProg_cong _ (proj2_sig (g b))). exact (Hsimp b).
        - exact (msingletonProg_meet _ (proj2_sig (g b)) A
                   (fun a s1 => getProgDSLP (f a)
                      (fun s0 => getProgDSLP x pre (Some (a, s0))) (Some (b, s1))) r). }
      split.
      + intros [H1 H2]. split.
        * intro a. split.
          -- intro b. exact (proj1 (Hg b) (H1 b) a).
          -- intro Hr. exact (proj1 (H2 Hr) a).
        * intro Hr. exact (proj2 (H2 Hr) eq_refl).
      + intros [H1 H2]. split.
        * intro b. apply (proj2 (Hg b)). intro a. exact (proj1 (H1 a) b).
        * intro Hr. split.
          -- intro a. exact (proj2 (H1 a) Hr).
          -- intros _. exact (H2 Hr).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgDSLP in *. intros pre r.
      assert (Hstep : forall a,
        getProgDSLP (f a) (fun s0 => getProgDSLP x pre (Some (a, s0))) r <->
        getProgDSLP (g a) (fun s0 => getProgDSLP y pre (Some (a, s0))) r).
      { intro a.
        transitivity (getProgDSLP (g a)
                        (fun s0 => getProgDSLP x pre (Some (a, s0))) r).
        - exact (Hfg a _ r).
        - apply (msingletonProg_cong _ (proj2_sig (g a))).
          intro s0. exact (Hxy pre (Some (a, s0))). }
      split.
      + intros [H1 H2]. split.
        * intro a. exact (proj1 (Hstep a) (H1 a)).
        * intro Hr. exact (proj1 (Hxy pre None) (H2 Hr)).
      + intros [H1 H2]. split.
        * intro a. exact (proj2 (Hstep a) (H1 a)).
        * intro Hr. exact (proj2 (Hxy pre None) (H2 Hr)).
  Qed.
End ProgDSLPMonad.

Arguments retDSLPProg {_} {_}.
Arguments bindDSLPProg {_} {_} {_}.
Arguments getProgDSLP {_} {_}.

(* ==================================================================== *)
(** * Refinement orders and comparison targets, demonic-liberal part     *)
(* ==================================================================== *)

Section SpecOrdersDSLP.
  Variable S : Type.

  Definition ordProgDSLP {A} (m1 m2 : DSLPProgSP S A) : Prop :=
    forall pre r, getProgDSLP m1 pre r -> getProgDSLP m2 pre r.

  Definition ordProgDSLPAt {A} (pre : S -> Prop) (m1 m2 : DSLPProgSP S A) : Prop :=
    forall r, getProgDSLP m1 pre r -> getProgDSLP m2 pre r.

  #[program] Definition tDSLPunder {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPProgSP S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  #[program] Definition tDSLPover {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPProgSP S A :=
    fun p r => forall s, (~ post r /\ ~ pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => ~ post r /\ ~ pre s)). Qed.

  Lemma dslp_top {A} (w : DSLPProgSP S A) (r : option (A * S)) :
    getProgDSLP w (fun _ => True) r.
  Proof. apply (proj2_sig w). intros s0 Hn. destruct (Hn I). Qed.

  Lemma tDSLPover_at {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hco : exists s, ~ pre s) (r : option (A * S)) :
    getProgDSLP (tDSLPover pre post) pre r <-> post r.
  Proof.
    split.
    - intro H. apply NNPP. intro Hnp. destruct Hco as [s0 Hs0].
      exact (Hs0 (H s0 (conj Hnp Hs0))).
    - intros Hpost s [Hnp _]. destruct (Hnp Hpost).
  Qed.

  Theorem gen_dslp_under {A} (w : DSLPProgSP S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    (forall r, post r -> getProgDSLP w pre r)
    <-> ordProgDSLP (tDSLPunder pre post) w.
  Proof.
    split.
    - intros H p r Hd.
      apply (msingletonProg_repr S (getProgDSLP w) (proj2_sig w)).
      intros s Hns. apply Hd. intro Hpost.
      exact (proj1 (msingletonProg_repr S (getProgDSLP w) (proj2_sig w) pre r)
               (H r Hpost) s Hns).
    - intros H r Hpost. exact (H pre r (fun t Ht => Ht Hpost)).
  Qed.

  Theorem gen_dslp_over {A} (w : DSLPProgSP S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) (Hco : exists s, ~ pre s) :
    (forall r, getProgDSLP w pre r -> post r)
    <-> ordProgDSLPAt pre w (tDSLPover pre post).
  Proof.
    split.
    - intros H r Hd. exact (proj2 (tDSLPover_at pre post Hco r) (H r Hd)).
    - intros H r Hd. exact (proj1 (tDSLPover_at pre post Hco r) (H r Hd)).
  Qed.

  Lemma dslpMono {A} (w : DSLPProgSP S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getProgDSLP w P r -> getProgDSLP w Q r.
  Proof. exact (msingletonProg_mono S (getProgDSLP w) (proj2_sig w) P Q r). Qed.

  Theorem gen_dslp_over_raw {A} (w : DSLPProgSP S A) pre post :
    (forall r, getProgDSLP w pre r -> post r)
    <-> ordProgSP (getProgDSLP w) (pp2_over pre post).
  Proof.
    split.
    - intros H p r Hw Hsub. exact (H r (dslpMono w p pre r Hsub Hw)).
    - intros H r Hw. exact (H pre r Hw (fun s Hs => Hs)).
  Qed.

  Theorem gen_dslp_under_raw {A} (w : DSLPProgSP S A) pre post :
    (forall r, post r -> getProgDSLP w pre r)
    <-> ordProgSP (pp2_under pre post) (getProgDSLP w).
  Proof.
    split.
    - intros H p r [Hsub Hpost]. exact (dslpMono w pre p r Hsub (H r Hpost)).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
  Qed.

End SpecOrdersDSLP.

Arguments ordProgDSLP {_} {_}.
Arguments ordProgDSLPAt {_} {_}.
Arguments tDSLPunder {_} {_}.
Arguments tDSLPover {_} {_}.

(* ==================================================================== *)
(** * The demonic-liberal recipe layer                                   *)
(* ==================================================================== *)

Section DSLPRecipes.

  Variable S : Type.

  #[program] Definition dslpOf {A} (R : SPRel S A) : DSLPProgSP S A :=
    fun pre r => forall s, R s r -> pre s.
  Next Obligation. exact (dslp_msingleton S R). Qed.

  (** The CO-SET of a [MSingletonProg] transformer: the states it refuses to
      let the precondition exclude. *)
  Definition dslpRel {A} (w : DSLPProgSP S A) : SPRel S A :=
    fun s r => ~ getProgDSLP w (fun t => t <> s) r.

  Lemma dslpRel_of {A} (R : SPRel S A) :
    forall s r, dslpRel (dslpOf R) s r <-> R s r.
  Proof.
    intros s r. split.
    - intro H. apply NNPP. intro Hn. apply H.
      intros t Ht Heq. subst t. exact (Hn Ht).
    - intros Hr H. exact (H s Hr eq_refl).
  Qed.

  Lemma dslpOf_rel {A} (w : DSLPProgSP S A) (pre : S -> Prop) r :
    getProgDSLP w pre r <-> getProgDSLP (dslpOf (dslpRel w)) pre r.
  Proof. exact (msingletonProg_repr S (getProgDSLP w) (proj2_sig w) pre r). Qed.

  Definition dslpLe : OrderM (DSLPProgSP S) :=
    fun A w1 w2 => relLe (dslpRel w1) (dslpRel w2).

  (** Reading a relation as a DSLP is ANTITONE, so the observed-relation
      order is the transformer order reversed. *)
  Theorem dslp_le_transformer {A} (w1 w2 : DSLPProgSP S A) :
    dslpLe A w1 w2 <-> ordProgDSLP w2 w1.
  Proof.
    split.
    - intros H pre r Hw. apply dslpOf_rel.
      intros s Hs. exact (proj1 (dslpOf_rel w2 pre r) Hw s (H s r Hs)).
    - intros H s r Hs Hc. exact (Hs (H (fun t => t <> s) r Hc)).
  Qed.

  #[global] Instance OrderedMonad_DSLPProgSP :
    @OrderedMonad (DSLPProgSP S) (Monad_DSLPProgSP S) dslpLe.
  Proof.
    constructor.
    - intros A w s r H. exact H.
    - intros A x y z Hxy Hyz s r H. exact (Hyz s r (Hxy s r H)).
    - intros A B x y f g Hxy Hfg.
      apply dslp_le_transformer in Hxy.
      apply dslp_le_transformer.
      intros pre r [H1 H2]. split.
      + intro a.
        apply (dslpMono S (f a)
                 (fun s0 => getProgDSLP y pre (Some (a, s0)))
                 (fun s0 => getProgDSLP x pre (Some (a, s0))) r).
        * intros s Hs. exact (Hxy pre (Some (a, s)) Hs).
        * exact (proj1 (dslp_le_transformer (f a) (g a)) (Hfg a) _ r (H1 a)).
      + intro Hr. exact (Hxy pre None (H2 Hr)).
  Qed.

  Lemma eqLeDSLP {A} (x y : DSLPProgSP S A) :
    @eq1 (DSLPProgSP S) (Eq1__ProgDSLP S) A x y -> dslpLe A x y.
  Proof.
    intros H s r Hx Hc. apply Hx.
    exact (proj2 (H (fun t => t <> s) r) Hc).
  Qed.

  Definition truthDSLP : TruthOrder (DSLPProgSP S) dslpLe.
  Proof.
    refine {| trueW := fun A => dslpOf (fun (_ : S) (_ : option (A * S)) => True);
              falseW := fun A => dslpOf (fun (_ : S) (_ : option (A * S)) => False);
              truthPolarity := Forward |}.
    intros A w. split.
    - intros s r H. destruct (proj1 (dslpRel_of _ s r) H).
    - intros s r H. apply dslpRel_of. exact I.
  Defined.

  (** Generic in the observation, exactly as on the angelic side:
      [Logics/DLSP.v] supplies [obsDSLP] and its morphism proof. *)

  Definition makeDSLPDM
    (observation : EffectObs (prog S) (DSLPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (DSLPProgSP S)
        (Monad__nditprog S) (Monad_DSLPProgSP S) (Eq1__ProgDSLP S) observation)
    : DMRecipe (prog S) (DSLPProgSP S) :=
    {| monadM := Monad__nditprog S;
       eqM := Eq1__nditprog S;
       eqEquivM := Eq1Equivalence_nditprog S;
       lawsM := MonadLawsE__nditprog S;
       monadW := Monad_DSLPProgSP S;
       eqW := Eq1__ProgDSLP S;
       eqEquivW := Eq1Equivalence__DSLPProgSP S;
       lawsW := MonadLawsE__ProgDSLP S;
       orderW := dslpLe;
       orderedW := OrderedMonad_DSLPProgSP;
       eqLeW := @eqLeDSLP;
       truthOrder := truthDSLP;
       theta := observation;
       thetaMorphism := morphism |}.

  Definition logicDSLP
    (observation : EffectObs (prog S) (DSLPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (DSLPProgSP S)
        (Monad__nditprog S) (Monad_DSLPProgSP S) (Eq1__ProgDSLP S) observation)
    : Logic (makeDSLPDM observation morphism).
  Proof.
    refine {|
      meetW := fun A x y => dslpOf (fun s r => dslpRel x s r /\ dslpRel y s r);
      joinW := fun A x y => dslpOf (fun s r => dslpRel x s r \/ dslpRel y s r)
    |}.
    - intros A x y z. cbn. unfold dslpLe, relLe. split.
      + intro H. split; intros s r Hx;
          [ exact (proj1 (proj1 (dslpRel_of _ s r) (H s r Hx)))
          | exact (proj2 (proj1 (dslpRel_of _ s r) (H s r Hx))) ].
      + intros [Hy Hz] s r Hx. apply dslpRel_of.
        split; [exact (Hy s r Hx) | exact (Hz s r Hx)].
    - intros A x y z. cbn. unfold dslpLe, relLe. split.
      + intro H. split; intros s r Hw; apply H; apply dslpRel_of;
          [left | right]; exact Hw.
      + intros [Hx Hy] s r Hw.
        destruct (proj1 (dslpRel_of _ s r) Hw) as [H | H];
          [exact (Hx s r H) | exact (Hy s r H)].
  Defined.

  Definition makeDSLPRecipe
    (observation : EffectObs (prog S) (DSLPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (DSLPProgSP S)
        (Monad__nditprog S) (Monad_DSLPProgSP S) (Eq1__ProgDSLP S) observation)
    : LogicRecipe (prog S) (DSLPProgSP S) :=
    {| recipeDM := makeDSLPDM observation morphism;
       recipeLogic := logicDSLP observation morphism |}.

  (** The angelic and the demonic-liberal readings of one relation are
      contrapositives of each other. *)
  Theorem aspOf_dslpOf_contrapositive {A} (R : SPRel S A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgASP (aspOf R) pre r <-> ~ getProgDSLP (dslpOf R) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [s [Hp Hr]] H. exact (H s Hr Hp).
    - intro H. apply NNPP. intro Hn. apply H.
      intros s Hr Hp. exact (Hn (ex_intro _ s (conj Hp Hr))).
  Qed.

End DSLPRecipes.

Arguments dslpOf {_} {_}.
Arguments dslpRel {_} {_}.
Arguments dslpLe {_} {_}.

Definition dslpMonoSP {S A} (w : DSLPProgSP S A) : MonoSP (getProgDSLP w) :=
  dslpMono S w.

(* ==================================================================== *)
(** * The observation                                                    *)
(* ==================================================================== *)

(** Dually to [obsASP], which is the ASP of the terminating slice, this is
    its DSLP — so [MSingletonProg] is immediate from [dslp_msingleton]. *)
#[program] Definition obsDSLP {S A} (m : prog S A) : DSLPProgSP S A :=
  fun pre r => forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
Next Obligation.
  exact (dslp_msingleton S
           (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
Qed.

Lemma getProgMSP_obsDSLP {S A} (m : prog S A) pre r :
  getProgDSLP (obsDSLP m) pre r <-> forall s, obsRel m s r -> pre s.
Proof. split; intro H; exact H. Qed.

(** [obsDSLP m] is the DSLP of exactly the relation [obsRel m]. *)
Lemma dslpRel_obsDSLP {S A} (m : prog S A) :
  forall s r, dslpRel (obsDSLP m) s r <-> obsRel m s r.
Proof. intros s r. exact (dslpRel_of S (obsRel m) s r). Qed.

Theorem obsDSLP_ret {S A} (a : A) :
  eq1 (obsDSLP (ret a : prog S A)) (ret a).
Proof.
  unfold eq1, Eq1__ProgDSLP. intros pre r. split.
  - intros H s0 Heq. apply H. subst r. cbn. reflexivity.
  - intros H s Hr. apply H. cbn in Hr. congruence.
Qed.

Theorem obsDSLP_bind {S A B} (x : prog S A) (f : A -> prog S B) :
  eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
Proof.
  unfold eq1, Eq1__ProgDSLP. intros pre r. split.
  - intro H. split.
    + intros a s' Hf s Hx. apply H. apply (obsRel_bind x f).
      exists (Some (a, s')). split; [exact Hx | exact Hf].
    + intros Hr s Hx. apply H. apply (obsRel_bind x f).
      exists None. split; [exact Hx | congruence].
  - intros [H1 H2] s Hrel. apply (obsRel_bind x f) in Hrel.
    destruct Hrel as [o [Hx Hk]]. destruct o as [[a s']|].
    + exact (H1 a s' Hk s Hx).
    + exact (H2 Hk s Hx).
Qed.

#[global] Instance dslpMorphism (S : Type) :
  @MonadMorphism (prog S) (DSLPProgSP S)
    (Monad__nditprog S) (Monad_DSLPProgSP S) (Eq1__ProgDSLP S) (@obsDSLP S).
Proof.
  constructor.
  - intros A a. apply obsDSLP_ret.
  - intros A B m k. apply obsDSLP_bind.
Qed.

Definition dslpRecipe (S : Type) : LogicRecipe (prog S) (DSLPProgSP S) :=
  makeDSLPRecipe S (@obsDSLP S) (dslpMorphism S).

(* ==================================================================== *)
(** * The logic                                                          *)
(* ==================================================================== *)

Definition dlspPPApproxOps (S : Type) `{DS : DefaultState S}
  (direction : Direction) :
  @ApproxOps (prog S) (DSLPProgSP S) direction
    (dslpRecipe S) (PP S) :=
  spPPApproxOps direction (dslpRecipe S) (fun A => @getProgDSLP S A).

#[global] Existing Instance dlspPPApproxOps.

Definition DLSPTriple {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  Approx direction (dslpRecipe S) m (unaryPP pre post).

Theorem dlsp_over_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DLSPTriple Over m pre post <->
  forall r, (forall s, obsRel m s r -> pre s) -> post r.
Proof. reflexivity. Qed.

Theorem dlsp_under_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DLSPTriple Under m pre post <->
  forall r, post r -> forall s, obsRel m s r -> pre s.
Proof. reflexivity. Qed.

Theorem dlsp_triple_raw {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DLSPTriple direction m pre post <->
  match direction with
  | Over => ordProgSP (getProgDSLP (obsDSLP m)) (pp2_over pre post)
  | Under => ordProgSP (pp2_under pre post) (getProgDSLP (obsDSLP m))
  end.
Proof.
  destruct direction.
  - exact (sp_over_raw (getProgDSLP (obsDSLP m)) (dslpMonoSP (obsDSLP m)) pre post).
  - exact (sp_under_raw (getProgDSLP (obsDSLP m)) (dslpMonoSP (obsDSLP m)) pre post).
Qed.

(** For the [Under] direction the comparison target can itself be a DSLP,
    but the comparison REVERSES: reading a relation as a DSLP is antitone
    ([tripleDSLP_under_inmonad] of the commit). *)

#[program] Definition pp2dslp_under {S A}
  (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPProgSP S A :=
  fun p r => forall s, (post r -> pre s) -> p s.
Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

Theorem dlsp_under_inmonad {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DLSPTriple Under m pre post <->
  ordProgDSLP (pp2dslp_under pre post) (obsDSLP m).
Proof.
  split.
  - intros H p r Hd s Hout. apply Hd. intro Hpost. exact (H r Hpost s Hout).
  - intros H r Hpost s Hout.
    exact (H (fun t => post r -> pre t) r (fun t Ht => Ht) s Hout Hpost).
Qed.

(* ==================================================================== *)
(** * Examples                                                           *)
(* ==================================================================== *)

Definition dlspOnly {A} (wanted : A) : A -> Prop :=
  fun actual => actual = wanted.

(** [Some (tt, 1)] is reachable from [0] only, so it forces [P0]. *)
Theorem progEx_dlsp_1 :
  DLSPTriple Under progEx P0 (dlspOnly (Some (tt, 1))).
Proof.
  apply dlsp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 1)) in Hpost. subst r.
  intros s Hrel.
  unfold obsRel, progEx, orP in Hrel. cbn in Hrel.
  change (s = 0).
  destruct Hrel as [a [Ha Hrel]]. subst a. cbn in Hrel.
  destruct Hrel as [Hrel | Hrel]; inversion Hrel; lia.
Qed.

(** [Some (tt, 42)] is reachable from every state, so it does not. *)
Theorem progEx_dlsp_not_42 :
  ~ DLSPTriple Under progEx P0 (dlspOnly (Some (tt, 42))).
Proof.
  intro H. apply dlsp_under_spec in H.
  assert (Hpost : dlspOnly (Some (tt, 42)) (Some (tt, 42))).
  { reflexivity. }
  specialize (H (Some (tt, 42)) Hpost 1).
  assert (Hreach : obsRel progEx 1 (Some (tt, 42))).
  { unfold obsRel, progEx, orP. cbn. sauto limit: 200. }
  specialize (H Hreach). discriminate.
Qed.

(** [None] is unreachable, so the liberal reading asserts it vacuously. *)
Theorem progEx_dlsp_None :
  DLSPTriple Under progEx P0
    (dlspOnly (None : option (unit * nat))).
Proof.
  apply dlsp_under_spec.
  intros r Hpost.
  change (r = None) in Hpost. subst r.
  intros s Hrel.
  unfold obsRel, progEx, orP in Hrel. cbn in Hrel.
  sauto limit: 200.
Qed.

Theorem progEx_dlsp_not_99 :
  ~ DLSPTriple Under progEx P0 (dlspOnly (Some (tt, 99))).
Proof.
  intro H. apply dlsp_under_spec in H.
  assert (Hpost : dlspOnly (Some (tt, 99)) (Some (tt, 99))).
  { reflexivity. }
  specialize (H (Some (tt, 99)) Hpost 98).
  assert (Hreach : obsRel progEx 98 (Some (tt, 99))).
  { unfold obsRel, progEx, orP. cbn. sauto limit: 200. }
  specialize (H Hreach). discriminate.
Qed.

(* ==================================================================== *)
(** * Contrapositive transformers                                        *)
(* ==================================================================== *)

(** The angelic and the demonic-liberal readings of the SAME relation are
    contrapositives of each other.  This is the first place where both
    observations are in scope, so the instance of
    [aspOf_dslpOf_contrapositive] lives here. *)

Section ContrapositiveTransformers.
  Variable S : Type.

  Theorem obsASP_contrapositive {A} (m : prog S A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgASP (obsASP m) pre r <->
      ~ getProgDSLP (obsDSLP m) (fun x => ~ pre x) r.
  Proof. exact (aspOf_dslpOf_contrapositive S (obsRel m) pre r). Qed.

End ContrapositiveTransformers.

Theorem dlsp_asp_contrapositive {S A} (m : prog S A)
  (pre : S -> Prop) (r : option (A * S)) :
  getProgASP (obsASP m) pre r <->
    ~ getProgDSLP (obsDSLP m) (fun x => ~ pre x) r.
Proof. exact (obsASP_contrapositive S m pre r). Qed.
