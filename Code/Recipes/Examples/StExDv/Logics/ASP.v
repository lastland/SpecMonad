(** * Angelic strongest postcondition

    [obsASP] reads the observed relation angelically: [r] is asserted at
    [pre] when SOME [pre]-state reaches it.  This is the O'Hearn
    incorrectness reading; the interesting direction is [Under]
    (under-approximation: every asserted outcome is genuinely reachable). *)

From Coq Require Import Lia PeanoNat RelationClasses Classical_Prop.
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

Import MonadNotation.
Open Scope monad_scope.

Section ProgASPMonad.
  Variable S : Type.

  Definition JoinPreservingProg {A} (w : ProgSP A) : Prop :=
    StrictProg S w /\ DisjunctiveProg S w.

  Definition SingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : option (A * S)),
      w pre r <-> exists s0, pre s0 /\ w (fun s => s = s0) r.

  (** Index the join by the *subset* [{s0 | pre s0}] and take the singleton
      [fun s => s = s0] at each index: the union of those singletons is
      pointwise [pre], and the indexed join is literally the right-hand side
      of [SingletonProg].  Rewriting "pointwise" to "equal" is what needs
      [functional_extensionality] + [propositional_extensionality] here,
      exactly as [join_to_singleton] needs [propositional_extensionality]. *)
  Lemma join_to_singleton_prog {A} (w : ProgSP A) :
    JoinPreservingProg w -> SingletonProg w.
  Proof.
    intros [HS HD] pre r.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    destruct (classic (exists s1, pre s1)) as [[s1 Hs1] | Hno].
    - pose proof (HD { s0 : S | pre s0 } (inhabits (exist (fun s0 => pre s0) s1 Hs1))
                    (fun i s => s = proj1_sig i) r) as Hj.
      cbv beta in Hj.
      assert (Heq : (fun s => exists i : { s0 : S | pre s0 }, s = proj1_sig i) = pre).
      { apply Hext. intro s. split.
        - intros [i Heq]. rewrite Heq. exact (proj2_sig i).
        - intro Hs. exists (exist (fun s0 => pre s0) s Hs). reflexivity. }
      rewrite Heq in Hj. split.
      + intro Hw. destruct (proj1 Hj Hw) as [i Hwi].
        exists (proj1_sig i). split; [ exact (proj2_sig i) | exact Hwi ].
      + intros [s0 [Hs0 Hw]]. apply Hj.
        exists (exist (fun s0' => pre s0') s0 Hs0). exact Hw.
    - assert (Heq : pre = (fun _ : S => False)).
      { apply Hext. intro s. split;
          [ intro Hs; exact (Hno (ex_intro _ s Hs)) | intros [] ]. }
      rewrite Heq. split.
      + intro Hw. destruct (HS r Hw).
      + intros [s0 [[] _]].
  Qed.

  Lemma singleton_to_join_prog {A} (w : ProgSP A) :
    SingletonProg w -> JoinPreservingProg w.
  Proof.
    intro H. split.
    - intros r Hw. destruct (proj1 (H (fun _ => False) r) Hw) as [s0 [[] _]].
    - intros I i0 p r. split.
      + intro Hw. destruct (proj1 (H (fun s => exists i, p i s) r) Hw)
          as [s0 [[i Hpi] Hw']].
        exists i. apply (H (fun s => p i s) r).
        exists s0. split; [ exact Hpi | exact Hw' ].
      + intros [i Hw]. destruct (proj1 (H (fun s => p i s) r) Hw) as [s0 [Hpi Hw']].
        apply (H (fun s => exists j, p j s) r).
        exists s0. split; [ exists i; exact Hpi | exact Hw' ].
  Qed.

  Theorem join_iff_singleton_prog {A} (w : ProgSP A) :
    JoinPreservingProg w <-> SingletonProg w.
  Proof. split; [apply join_to_singleton_prog | apply singleton_to_join_prog ]. Qed.

  Definition ASPProgSP (A : Type) : Type := { w : ProgSP A | SingletonProg w }.

  Definition getProgASP {A} (w : ASPProgSP A) : ProgSP A :=
    proj1_sig w.

  Lemma getProg_singleton {A} (w : ASPProgSP A) (pre : S -> Prop) (r : option (A * S)) :
    getProgASP w pre r <-> exists s0, pre s0 /\ getProgASP w (fun s => s = s0) r.
  Proof. exact (proj2_sig w pre r). Qed.

  (** [SingletonProg] supplies congruence in the precondition for free — which
      is why the monad laws below need no extensionality axiom. *)
  Lemma getProg_cong {A} (w : ASPProgSP A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s <-> Q s) -> (getProgASP w P r <-> getProgASP w Q r).
  Proof.
    intro HPQ. split; intro H; apply getProg_singleton in H;
      destruct H as [s0 [Hs Hw]]; apply getProg_singleton; exists s0.
    - split; [exact (proj1 (HPQ s0) Hs) | exact Hw].
    - split; [exact (proj2 (HPQ s0) Hs) | exact Hw].
  Qed.

  Lemma getProg_join {A} (w : ASPProgSP A) (I : Type) (p : I -> (S -> Prop))
    (r : option (A * S)) :
    getProgASP w (fun s => exists i, p i s) r <-> exists i, getProgASP w (p i) r.
  Proof.
    split.
    - intro H. apply getProg_singleton in H. destruct H as [s0 [[i Hpi] Hw]].
      exists i. apply getProg_singleton. exists s0. split; [ exact Hpi | exact Hw ].
    - intros [i H]. apply getProg_singleton in H. destruct H as [s0 [Hpi Hw]].
      apply getProg_singleton. exists s0.
      split; [ exists i; exact Hpi | exact Hw ].
  Qed.

  #[program] Definition retASPProg {A} (a : A) : ASPProgSP A :=
    fun pre r => exists s0, pre s0 /\ r = Some (a, s0).
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s0 [Hp Heq]]. exists s0. split; [exact Hp |].
      exists s0. split; [reflexivity | exact Heq].
    - intros [s0 [Hp [s1 [Heq1 Heq2]]]]. subst s1.
      exists s0. split; [exact Hp | exact Heq2].
  Qed.

  #[program] Definition bindASPProg {A B}
    (m : ASPProgSP A) (k : A -> ASPProgSP B) : ASPProgSP B :=
    fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
  Next Obligation.
    unfold ASPProgSP. intros pre r.
    pose proof (proj2_sig m) as Hm. unfold SingletonProg in Hm.
    pose proof (fun a => proj2_sig (k a)) as Hk. unfold SingletonProg in Hk.
    split.
    - intros [[a Ha] | [Hr Hn]].
      + destruct (proj1 (Hk a _ r) Ha) as [s1 [Hms Hka]].
        destruct (proj1 (Hm pre (Some (a, s1))) Hms) as [s0 [Hp Hm0]].
        exists s0. split; [ exact Hp |]. left. exists a.
        apply (Hk a). exists s1. split; [ exact Hm0 | exact Hka ].
      + destruct (proj1 (Hm pre None) Hn) as [s0 [Hp Hm0]].
        exists s0. split; [ exact Hp |]. right. split; [ exact Hr | exact Hm0 ].
    - intros [s0 [Hp [[a Ha] | [Hr Hn]]]].
      + destruct (proj1 (Hk a _ r) Ha) as [s1 [Hms Hka]].
        left. exists a. apply (Hk a). exists s1. split; [| exact Hka ].
        apply (Hm pre (Some (a, s1))). exists s0. split; [ exact Hp | exact Hms ].
      + right. split; [ exact Hr |].
        apply (Hm pre None). exists s0. split; [ exact Hp | exact Hn ].
  Qed.

  #[global]
    Instance Monad__ASPProgSP : Monad ASPProgSP :=
    {| ret := fun _ => @retASPProg _ ;
      bind := fun _ _ => @bindASPProg _ _ |}.

  #[global] Instance Eq1__ProgASP : Eq1 ASPProgSP :=
    fun A m n => forall pre r, getProgASP m pre r <-> getProgASP n pre r.

  #[global] Instance Eq1Equivalence__ASPProgSP
    : @Eq1Equivalence ASPProgSP _ Eq1__ProgASP.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__ProgASP
    : @MonadLawsE ASPProgSP Eq1__ProgASP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ProgASP. intros pre r.
      (* the intermediate precondition [fun s => ret x can produce (x, s)]
         is pointwise [pre] *)
      assert (Hcong : forall s, getProgASP (retASPProg x) pre (Some (x, s)) <-> pre s).
      { intro s. split.
        - intros [s1 [Hp Heq]]. assert (Hs : s = s1) by congruence. subst s. exact Hp.
        - intro Hp. exists s. split; [exact Hp | reflexivity]. }
      split.
      + intros [[a Ha] | [_ Hn]].
        * (* only [a = x] can fire: the [ret] outcome pins the value *)
          assert (Hax : a = x).
          { pose proof Ha as Ha'. apply getProg_singleton in Ha'.
            destruct Ha' as [s0 [[s1 [_ Heq]] _]]. congruence. }
          subst a. exact (proj1 (getProg_cong (f x) _ pre r Hcong) Ha).
        * destruct Hn as [s0 [_ Heq]]. discriminate Heq.
      + intro H. left. exists x.
        exact (proj2 (getProg_cong (f x) _ pre r Hcong) H).
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1__ProgASP. intros pre r. split.
      + intros [[a [s0 [Hm Heq]]] | [Hr Hn]]; subst r; assumption.
      + intro H. destruct r as [[a s0]|].
        * left. exists a, s0. split; [exact H | reflexivity].
        * right. split; [reflexivity | exact H].
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ProgASP. intros pre r.
      (* the [Some] outcomes of [bind x f] never come from its [None] branch *)
      assert (Hsimp : forall b s1,
        getProgASP (bindASPProg x f) pre (Some (b, s1)) <->
        exists a, getProgASP (f a)
                    (fun s0 => getProgASP x pre (Some (a, s0))) (Some (b, s1))).
      { intros b s1. split.
        - intros [H | [Hc _]]; [exact H | discriminate Hc].
        - intro H. left. exact H. }
      (* ... so the continuation's precondition is an [A]-indexed join, and
         [g b] preserves it — this is the step [KenjiProgSP] cannot make *)
      assert (Hg : forall b,
        getProgASP (g b) (fun s1 => getProgASP (bindASPProg x f) pre (Some (b, s1))) r <->
        exists a, getProgASP (g b)
                    (fun s1 => getProgASP (f a)
                       (fun s0 => getProgASP x pre (Some (a, s0))) (Some (b, s1))) r).
      { intro b.
        transitivity (getProgASP (g b)
          (fun s1 => exists a, getProgASP (f a)
             (fun s0 => getProgASP x pre (Some (a, s0))) (Some (b, s1))) r).
        - apply getProg_cong. exact (Hsimp b).
        - exact (getProg_join (g b) A
                   (fun a s1 => getProgASP (f a)
                      (fun s0 => getProgASP x pre (Some (a, s0))) (Some (b, s1))) r). }
      split.
      + intros [[b Hb] | [Hr Hn]].
        * destruct (proj1 (Hg b) Hb) as [a Ha]. left. exists a. left. exists b. exact Ha.
        * destruct Hn as [[a Ha] | [_ Hx]].
          -- left. exists a. right. split; [exact Hr | exact Ha].
          -- right. split; [exact Hr | exact Hx].
      + intros [[a [[b Hb] | [Hr Ha]]] | [Hr Hx]].
        * left. exists b. apply (proj2 (Hg b)). exists a. exact Hb.
        * right. split; [exact Hr | left; exists a; exact Ha].
        * right. split; [exact Hr | right; split; [reflexivity | exact Hx]].
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgASP in *. intros pre r.
      assert (Hstep : forall a,
        getProgASP (f a) (fun s0 => getProgASP x pre (Some (a, s0))) r <->
        getProgASP (g a) (fun s0 => getProgASP y pre (Some (a, s0))) r).
      { intro a.
        transitivity (getProgASP (g a) (fun s0 => getProgASP x pre (Some (a, s0))) r).
        - exact (Hfg a _ r).
        - apply getProg_cong. intro s0. exact (Hxy pre (Some (a, s0))). }
      split.
      + intros [[a Ha] | [Hr Hn]].
        * left. exists a. exact (proj1 (Hstep a) Ha).
        * right. split; [exact Hr | exact (proj1 (Hxy pre None) Hn)].
      + intros [[a Ha] | [Hr Hn]].
        * left. exists a. exact (proj2 (Hstep a) Ha).
        * right. split; [exact Hr | exact (proj2 (Hxy pre None) Hn)].
  Qed.
End ProgASPMonad.

Arguments retASPProg {_} {_}.
Arguments bindASPProg {_} {_} {_}.
Arguments getProgASP {_} {_}.

(* ==================================================================== *)
(** * Refinement order and comparison targets                            *)
(* ==================================================================== *)

Section SpecOrdersASP.
  Variable S : Type.

  Definition ordProgASP {A} (m1 m2 : ASPProgSP S A) : Prop :=
    forall pre r, getProgASP m1 pre r -> getProgASP m2 pre r.

  (** Orders scoped to a single precondition, used by the two directions that
      are not relation inclusions. *)

  Definition ordProgASPAt {A} (pre : S -> Prop) (m1 m2 : ASPProgSP S A) : Prop :=
    forall r, getProgASP m1 pre r -> getProgASP m2 pre r.
  (** ** The in-monad comparison targets *)

  #[program] Definition tASPover {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPProgSP S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s. exists s0. split; assumption.
  Qed.

  #[program] Definition tASPunder {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPProgSP S A :=
    fun p r => exists s, p s /\ (pre s /\ post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s. exists s0. split; assumption.
  Qed.

  (** ** The degeneracies that force the two side conditions

      [SingletonProg] makes every ASP FALSE at the empty precondition, and
      dually [MSingletonProg] makes every DSLP TRUE at the full one.  So at
      those preconditions no target of the respective kind can see [post], and
      the corresponding nonemptiness hypothesis below is not removable. *)

  Lemma asp_bot {A} (w : ASPProgSP S A) (r : option (A * S)) :
    ~ getProgASP w (fun _ => False) r.
  Proof.
    intro Hc. destruct (proj1 (getProg_singleton S w _ r) Hc) as [s0 [[] _]].
  Qed.

  (** Each [At]-target, evaluated at [pre] itself, collapses to [post]. *)

  Lemma tASPunder_at {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hne : exists s, pre s) (r : option (A * S)) :
    getProgASP (tASPunder pre post) pre r <-> post r.
  Proof.
    split.
    - intros [s [_ [_ Hpost]]]. exact Hpost.
    - intro Hpost. destruct Hne as [s Hs].
      exists s. split; [ exact Hs | split; [ exact Hs | exact Hpost ] ].
  Qed.

  (** ** The four in-monad characterizations

      [Over] always compares [obs <= target]; [Under] always [target <= obs].
      The two that are relation inclusions (ASP/[Over], DSLP/[Under]) work in
      the GLOBAL order with no side condition; the two that are not work in the
      [At]-order and pay the nonemptiness condition their healthiness condition
      forces. *)

  Theorem gen_asp_over {A} (w : ASPProgSP S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    (forall r, getProgASP w pre r -> post r) <-> ordProgASP w (tASPover pre post).
  Proof.
    split.
    - intros H p r Hw.
      destruct (proj1 (getProg_singleton S w p r) Hw) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp |]. intro Hpre.
      apply H. apply getProg_singleton. exists s0. split; [ exact Hpre | exact Hs ].
    - intros H r Hw.
      destruct (H pre r Hw) as [s1 [Hp1 Himp]]. exact (Himp Hp1).
  Qed.

  Theorem gen_asp_under {A} (w : ASPProgSP S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) (Hne : exists s, pre s) :
    (forall r, post r -> getProgASP w pre r)
    <-> ordProgASPAt pre (tASPunder pre post) w.
  Proof.
    split.
    - intros H r Ht. exact (H r (proj1 (tASPunder_at pre post Hne r) Ht)).
    - intros H r Hpost. exact (H r (proj2 (tASPunder_at pre post Hne r) Hpost)).
  Qed.

  (** ** Monotonicity in the precondition, for each of the four monads

      Each follows from that monad's healthiness condition, and it is the only
      property the raw characterizations below need. *)

  Lemma aspMono {A} (w : ASPProgSP S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getProgASP w P r -> getProgASP w Q r.
  Proof.
    intros Hsub Hw.
    destruct (proj1 (getProg_singleton S w P r) Hw) as [s0 [Hp Hs]].
    apply getProg_singleton. exists s0. split; [ exact (Hsub s0 Hp) | exact Hs ].
  Qed.

  (** ** The raw characterizations, uniform across all four monads

      Each direction needs nothing but monotonicity, which is why the same two
      targets [pp2_over] / [pp2_under] serve all eight instances. *)

  Theorem gen_asp_over_raw {A} (w : ASPProgSP S A) pre post :
    (forall r, getProgASP w pre r -> post r)
    <-> ordProgSP (getProgASP w) (pp2_over pre post).
  Proof.
    split.
    - intros H p r Hw Hsub. exact (H r (aspMono w p pre r Hsub Hw)).
    - intros H r Hw. exact (H pre r Hw (fun s Hs => Hs)).
  Qed.

  Theorem gen_asp_under_raw {A} (w : ASPProgSP S A) pre post :
    (forall r, post r -> getProgASP w pre r)
    <-> ordProgSP (pp2_under pre post) (getProgASP w).
  Proof.
    split.
    - intros H p r [Hsub Hpost]. exact (aspMono w pre p r Hsub (H r Hpost)).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
  Qed.

End SpecOrdersASP.

Arguments ordProgASP {_} {_}.
Arguments ordProgASPAt {_} {_}.
Arguments tASPover {_} {_}.
Arguments tASPunder {_} {_}.
(* ==================================================================== *)
(** * The angelic recipe layer                                           *)
(* ==================================================================== *)

(** [aspOf] / [aspRel] exhibit [ASPProgSP] as a copy of the relation space:
    [aspRel_of] inverts [aspOf] and [aspOf_rel] is [getProg_singleton].  The
    monad is therefore ordered by INCLUSION OF THE OBSERVED RELATION, which
    on the angelic side is exactly the transformer order [ordProgASP]
    ([asp_le_transformer]).  That order is a complete lattice — bottom is the
    empty relation, top the full one, meet is intersection and join is union
    — and [bind] is monotone for it. *)

Section ASPRecipes.

  Variable S : Type.

  #[program] Definition aspOf {A} (R : SPRel S A) : ASPProgSP S A :=
    fun pre r => exists s, pre s /\ R s r.
  Next Obligation.
    intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
      exists s. split; [reflexivity | exact Hr].
    - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
      exists s0. split; assumption.
  Qed.

  Definition aspRel {A} (w : ASPProgSP S A) : SPRel S A :=
    fun s r => getProgASP w (fun t => t = s) r.

  Lemma aspRel_of {A} (R : SPRel S A) :
    forall s r, aspRel (aspOf R) s r <-> R s r.
  Proof.
    intros s r. split.
    - intros [s0 [Heq Hr]]. subst s0. exact Hr.
    - intro Hr. exists s. split; [reflexivity | exact Hr].
  Qed.

  (** Every element is the ASP of the relation it observes. *)
  Lemma aspOf_rel {A} (w : ASPProgSP S A) (pre : S -> Prop) r :
    getProgASP w pre r <-> getProgASP (aspOf (aspRel w)) pre r.
  Proof. exact (getProg_singleton S w pre r). Qed.

  Definition aspLe : OrderM (ASPProgSP S) :=
    fun A w1 w2 => relLe (aspRel w1) (aspRel w2).

  Theorem asp_le_transformer {A} (w1 w2 : ASPProgSP S A) :
    aspLe A w1 w2 <-> ordProgASP w1 w2.
  Proof.
    split.
    - intros H pre r Hw.
      destruct (proj1 (getProg_singleton S w1 pre r) Hw) as [s [Hp Hs]].
      apply (getProg_singleton S w2). exists s.
      split; [exact Hp | exact (H s r Hs)].
    - intros H s r Hs. exact (H (fun t => t = s) r Hs).
  Qed.

  #[global] Instance OrderedMonad_ASPProgSP :
    @OrderedMonad (ASPProgSP S) (Monad__ASPProgSP S) aspLe.
  Proof.
    constructor.
    - intros A w s r H. exact H.
    - intros A x y z Hxy Hyz s r H. exact (Hyz s r (Hxy s r H)).
    - intros A B x y f g Hxy Hfg.
      apply asp_le_transformer in Hxy.
      apply asp_le_transformer.
      intros pre r [[a Ha] | [Hr Hn]].
      + left. exists a.
        apply (aspMono S (g a)
                 (fun s0 => getProgASP x pre (Some (a, s0)))
                 (fun s0 => getProgASP y pre (Some (a, s0))) r).
        * intros s Hs. exact (Hxy pre (Some (a, s)) Hs).
        * exact (proj1 (asp_le_transformer (f a) (g a)) (Hfg a) _ r Ha).
      + right. split; [exact Hr | exact (Hxy pre None Hn)].
  Qed.

  Lemma eqLeASP {A} (x y : ASPProgSP S A) :
    @eq1 (ASPProgSP S) (Eq1__ProgASP S) A x y -> aspLe A x y.
  Proof. intros H s r Hx. exact (proj1 (H (fun t => t = s) r) Hx). Qed.

  Definition truthASP : TruthOrder (ASPProgSP S) aspLe.
  Proof.
    refine {| trueW := fun A => aspOf (fun (_ : S) (_ : option (A * S)) => True);
              falseW := fun A => aspOf (fun (_ : S) (_ : option (A * S)) => False);
              truthPolarity := Forward |}.
    intros A w. split.
    - intros s r H. destruct (proj1 (aspRel_of _ s r) H).
    - intros s r H. apply aspRel_of. exact I.
  Defined.

  (** The recipe is generic in the observation: [Logics/ASP.v] supplies
      [obsASP] and its morphism proof. *)

  Definition makeASPDM
    (observation : EffectObs (prog S) (ASPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (ASPProgSP S)
        (Monad__nditprog S) (Monad__ASPProgSP S) (Eq1__ProgASP S) observation)
    : DMRecipe (prog S) (ASPProgSP S) :=
    {| monadM := Monad__nditprog S;
       eqM := Eq1__nditprog S;
       eqEquivM := Eq1Equivalence_nditprog S;
       lawsM := MonadLawsE__nditprog S;
       monadW := Monad__ASPProgSP S;
       eqW := Eq1__ProgASP S;
       eqEquivW := Eq1Equivalence__ASPProgSP S;
       lawsW := MonadLawsE__ProgASP S;
       orderW := aspLe;
       orderedW := OrderedMonad_ASPProgSP;
       eqLeW := @eqLeASP;
       truthOrder := truthASP;
       theta := observation;
       thetaMorphism := morphism |}.

  Definition logicASP
    (observation : EffectObs (prog S) (ASPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (ASPProgSP S)
        (Monad__nditprog S) (Monad__ASPProgSP S) (Eq1__ProgASP S) observation)
    : Logic (makeASPDM observation morphism).
  Proof.
    refine {|
      meetW := fun A x y => aspOf (fun s r => aspRel x s r /\ aspRel y s r);
      joinW := fun A x y => aspOf (fun s r => aspRel x s r \/ aspRel y s r)
    |}.
    - intros A x y z. cbn. unfold aspLe, relLe. split.
      + intro H. split; intros s r Hx;
          [ exact (proj1 (proj1 (aspRel_of _ s r) (H s r Hx)))
          | exact (proj2 (proj1 (aspRel_of _ s r) (H s r Hx))) ].
      + intros [Hy Hz] s r Hx. apply aspRel_of.
        split; [exact (Hy s r Hx) | exact (Hz s r Hx)].
    - intros A x y z. cbn. unfold aspLe, relLe. split.
      + intro H. split; intros s r Hw; apply H; apply aspRel_of;
          [left | right]; exact Hw.
      + intros [Hx Hy] s r Hw.
        destruct (proj1 (aspRel_of _ s r) Hw) as [H | H];
          [exact (Hx s r H) | exact (Hy s r H)].
  Defined.

  Definition makeASPRecipe
    (observation : EffectObs (prog S) (ASPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (ASPProgSP S)
        (Monad__nditprog S) (Monad__ASPProgSP S) (Eq1__ProgASP S) observation)
    : LogicRecipe (prog S) (ASPProgSP S) :=
    {| recipeDM := makeASPDM observation morphism;
       recipeLogic := logicASP observation morphism |}.

End ASPRecipes.

Arguments aspOf {_} {_}.
Arguments aspRel {_} {_}.
Arguments aspLe {_} {_}.

Definition aspMonoSP {S A} (w : ASPProgSP S A) : MonoSP (getProgASP w) :=
  aspMono S w.

(* ==================================================================== *)
(** * The observation                                                    *)
(* ==================================================================== *)

(** The angelic reading of the terminating slice [obsRel]: [r] is asserted
    at [pre] when SOME [pre]-state reaches it.  [SingletonProg] is immediate
    from the shape. *)
#[program] Definition obsASP {S A} (m : prog S A) : ASPProgSP S A :=
  fun pre r => exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
Next Obligation.
  unfold SingletonProg. intros pre r. split.
  - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
    exists s. split; [reflexivity | exact Hr].
  - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
    exists s0. split; [exact Hp | exact Hr].
Qed.

Lemma getProg_obsASP {S A} (m : prog S A) pre r :
  getProgASP (obsASP m) pre r <-> exists s, pre s /\ obsRel m s r.
Proof. split; intro H; exact H. Qed.

(** [obsASP m] is the ASP of exactly the relation [obsRel m]. *)
Lemma aspRel_obsASP {S A} (m : prog S A) :
  forall s r, aspRel (obsASP m) s r <-> obsRel m s r.
Proof. intros s r. exact (aspRel_of S (obsRel m) s r). Qed.

Theorem obsASP_ret {S A} (a : A) :
  eq1 (obsASP (ret a : prog S A)) (ret a).
Proof.
  unfold eq1, Eq1__ProgASP. intros pre r. split.
  - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
    destruct r as [[b s']|]; cbn in Hr; congruence.
  - intros [s [Hp Heq]]. exists s. split; [exact Hp |].
    destruct r as [[b s']|]; cbn; congruence.
Qed.

Theorem obsASP_bind {S A B} (x : prog S A) (f : A -> prog S B) :
  eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
Proof.
  unfold eq1, Eq1__ProgASP. intros pre r. split.
  - intros [s [Hp Hrel]]. apply (obsRel_bind x f) in Hrel.
    destruct Hrel as [o [Hx Hk]]. destruct o as [[a s']|].
    + left. exists a, s'. split; [| exact Hk].
      exists s. split; [exact Hp | exact Hx].
    + right. split; [congruence |]. exists s. split; [exact Hp | exact Hx].
  - intros [[a [s' [[s [Hp Hx]] Hf]]] | [Hr [s [Hp Hx]]]].
    + exists s. split; [exact Hp |]. apply (obsRel_bind x f).
      exists (Some (a, s')). split; [exact Hx | exact Hf].
    + exists s. split; [exact Hp |]. apply (obsRel_bind x f).
      exists None. split; [exact Hx | congruence].
Qed.

#[global] Instance aspMorphism (S : Type) :
  @MonadMorphism (prog S) (ASPProgSP S)
    (Monad__nditprog S) (Monad__ASPProgSP S) (Eq1__ProgASP S) (@obsASP S).
Proof.
  constructor.
  - intros A a. apply obsASP_ret.
  - intros A B m k. apply obsASP_bind.
Qed.

Definition aspRecipe (S : Type) : LogicRecipe (prog S) (ASPProgSP S) :=
  makeASPRecipe S (@obsASP S) (aspMorphism S).

(* ==================================================================== *)
(** * The logic                                                          *)
(* ==================================================================== *)

Definition aspPPApproxOps (S : Type) `{DS : DefaultState S}
  (direction : Direction) :
  @ApproxOps (prog S) (ASPProgSP S) direction
    (aspRecipe S) (PP S) :=
  spPPApproxOps direction (aspRecipe S) (fun A => @getProgASP S A).

#[global] Existing Instance aspPPApproxOps.

Definition ASPTriple {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  Approx direction (aspRecipe S) m (unaryPP pre post).

(** The two directions, unfolded.  These are [tripleASP _ Over] and
    [tripleASP _ Under] of the commit. *)

Theorem asp_over_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ASPTriple Over m pre post <->
  forall r, (exists s, pre s /\ obsRel m s r) -> post r.
Proof. reflexivity. Qed.

Theorem asp_under_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ASPTriple Under m pre post <->
  forall r, post r -> exists s, pre s /\ obsRel m s r.
Proof. reflexivity. Qed.

(** ... and as inclusions against the raw comparison targets of [SPSpec.v]
    ([tripleASPDefEq] of the commit). *)

Theorem asp_triple_raw {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ASPTriple direction m pre post <->
  match direction with
  | Over => ordProgSP (getProgASP (obsASP m)) (pp2_over pre post)
  | Under => ordProgSP (pp2_under pre post) (getProgASP (obsASP m))
  end.
Proof.
  destruct direction.
  - exact (sp_over_raw (getProgASP (obsASP m)) (aspMonoSP (obsASP m)) pre post).
  - exact (sp_under_raw (getProgASP (obsASP m)) (aspMonoSP (obsASP m)) pre post).
Qed.

(** For the [Over] direction the comparison target can itself be angelic
    ([tripleASP_over_inmonad] of the commit). *)

#[program] Definition pp2asp_over {S A}
  (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPProgSP S A :=
  fun p r => exists s, p s /\ (pre s -> post r).
Next Obligation.
  intros p r. split.
  - intros [s [Hp Hm]]. exists s. split; [exact Hp |].
    exists s. split; [reflexivity | exact Hm].
  - intros [s0 [Hp [s [Heq Hm]]]]. subst s.
    exists s0. split; [exact Hp | exact Hm].
Qed.

Theorem asp_over_inmonad {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ASPTriple Over m pre post <-> ordProgASP (obsASP m) (pp2asp_over pre post).
Proof.
  split.
  - intros H p r [s [Hp Hout]]. exists s. split; [exact Hp |].
    intro Hpre. exact (H r (ex_intro _ s (conj Hpre Hout))).
  - intros H r [s [Hpre Hout]].
    destruct (H pre r (ex_intro _ s (conj Hpre Hout))) as [s1 [Hp1 Himp]].
    exact (Himp Hp1).
Qed.

(* ==================================================================== *)
(** * Examples                                                           *)
(* ==================================================================== *)

Definition aspAtLeast42 : option (unit * nat) -> Prop :=
  fun r =>
    match r with
    | Some (_, s) => s >= 42
    | None => False
    end.

Definition aspAt42 : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, 42).

Definition aspAt43 : option (unit * nat) -> Prop :=
  fun r => r = Some (tt, 43).

Theorem progA_all :
  ASPTriple Over progA (fun _ => True) aspAtLeast42.
Proof.
  apply asp_over_spec.
  intros r [sigma [_ Hrel]].
  unfold obsRel in Hrel.
  destruct r as [[[] s']|]; cbn in Hrel; sauto limit: 200.
Qed.

Theorem progA_42 :
  ASPTriple Under progA (fun _ => True) aspAt42.
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 42)) in Hpost. subst r.
  exists 0. split; [exact I|].
  unfold obsRel. cbn. sauto limit: 200.
Qed.

Theorem progA_43 :
  ASPTriple Under progA (fun _ => True) aspAt43.
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 43)) in Hpost. subst r.
  exists 0. split; [exact I|].
  unfold obsRel. cbn. sauto limit: 200.
Qed.

Theorem progB_42 :
  ASPTriple Under progB (fun _ => True) aspAt42.
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 42)) in Hpost. subst r.
  exists 0. split; [exact I|].
  unfold obsRel. cbn. sauto limit: 200.
Qed.

(** Divergence is invisible to the terminating slice, so the exceptional
    outcome [None] is not observed either. *)
Theorem progB_not_None :
  ASPTriple Over progB (fun _ => True) (fun r => r <> None).
Proof.
  apply asp_over_spec.
  intros r [sigma [_ Hrel]] ->.
  unfold obsRel in Hrel. cbn in Hrel. sauto limit: 200.
Qed.

Theorem progB_ASP_42 :
  ASPTriple Over progB (fun _ => True) aspAt42.
Proof.
  apply asp_over_spec.
  intros r [sigma [_ Hrel]].
  unfold obsRel in Hrel.
  destruct r as [[[] s']|]; cbn in Hrel; sauto limit: 200.
Qed.

(** [SingletonProg] makes every angelic specification FALSE at the empty
    precondition, so no [Under] triple can be proved there. *)
Theorem under_empty_pre_fails :
  ~ ASPTriple Under progA (fun _ => False) (fun _ => True).
Proof.
  intro H. apply asp_under_spec in H.
  destruct (H None I) as [s [Hfalse _]]. exact Hfalse.
Qed.

Theorem progRet_asp_inc :
  ASPTriple Under progRet preEq0 postEq0.
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 0)) in Hpost. subst r.
  exists 0. split; reflexivity.
Qed.

Module OHearnExamples.

  Import OHearnExample.

  Definition firstPost : option (unit * (nat * nat * nat)) -> Prop :=
    fun r =>
      match r with
      | Some (tt, (x, y, z)) =>
          z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
      | _ => False
      end.

  Definition z42Post : option (unit * (nat * nat * nat)) -> Prop :=
    fun r =>
      match r with
      | Some (tt, (_, _, z)) => z = 42
      | _ => False
      end.

  Theorem example_incorrect_1 :
    ASPTriple Under example_state
      (fun '(_, _, z) => z = 11) firstPost.
  Proof.
    apply asp_under_spec.
    intros [[[] [[x y] z]]|] H; [|contradiction].
    change
      (z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true)
      in H.
    destruct H as [-> [Hx Hy]].
    exists (x, y, 11). split; [reflexivity|].
    unfold obsRel. cbn. eexists. split; [reflexivity|].
    cbn. rewrite Hx, Hy. reflexivity.
  Qed.

  Theorem example_incorrect_2 :
    ASPTriple Under example_state (fun _ => True) z42Post.
  Proof.
    apply asp_under_spec.
    intros [[[] [[x y] z]]|] H; [|contradiction].
    change (z = 42) in H. subst z.
    exists (x, y, 42). split; [exact I|].
    unfold obsRel. cbn. eexists. split; [reflexivity|].
    cbn. destruct (Nat.even x); destruct (negb (Nat.even y)); reflexivity.
  Qed.

  Theorem example_incorrect_unprovable :
    ~ ASPTriple Under example_state
        (fun '(_, _, z) => z = 11) z42Post.
  Proof.
    intro H. apply asp_under_spec in H.
    specialize (H (Some (tt, (1, 0, 42)))).
    assert (Hpost : z42Post (Some (tt, (1, 0, 42)))).
    { reflexivity. }
    specialize (H Hpost).
    destruct H as [[[x y] z] [Hpre Hrel]].
    cbn in Hpre. subst z.
    unfold obsRel in Hrel. cbn in Hrel. destruct Hrel as [a [Ha Hrel]].
    subst a. cbn in Hrel.
    destruct (Nat.even x) eqn:Hx;
      destruct (negb (Nat.even y)) eqn:Hy;
      cbn in Hrel; inversion Hrel; subst; try discriminate Hx.
  Qed.

End OHearnExamples.

(** O'Hearn's "loom": the exception is reachable from SOME positive
    balance, which is bug PRESENCE. *)
Theorem progloom_triple_asp :
  ASPTriple Under WithdrawExample.progloom
    (fun balance => balance > 0) WithdrawExample.exceptionPost.
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (WithdrawExample.exceptionPost r) in Hpost.
  destruct r as [[[] n]|]; [contradiction|].
  exists 1. split; [cbn; lia|].
  unfold obsRel, WithdrawExample.progloom, pickP. cbn.
  exists (Some (Some (2, 1))). split.
  - exists 2. reflexivity.
  - cbn. exists (Some (Some (1, 1))). split; [reflexivity|].
    cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
Qed.

Theorem progloom_triple_asp_harder :
  ASPTriple Under WithdrawExample.progloom_harder
    (fun balance => balance > 0) WithdrawExample.exceptionPost.
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (WithdrawExample.exceptionPost r) in Hpost.
  destruct r as [[[] n]|]; [contradiction|].
  exists 2. split; [cbn; lia|].
  unfold obsRel, WithdrawExample.progloom_harder, pickP. cbn.
  exists (Some (Some (0, 2))). split.
  - exists 0. reflexivity.
  - cbn. exists (Some (Some (2, 2))). split; [reflexivity|].
    cbn. exists (Some None). split; [reflexivity|]. cbn. reflexivity.
Qed.

Definition aspOnly {A} (wanted : A) : A -> Prop :=
  fun actual => actual = wanted.

(** The four reachability classes of [progEx] relative to [P0 = {0}]:
    [Some (tt, 1)] and [Some (tt, 42)] are reachable, [None] and
    [Some (tt, 99)] are not. *)

Theorem progEx_asp_1 :
  ASPTriple Under progEx P0 (aspOnly (Some (tt, 1))).
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 1)) in Hpost. subst r.
  exists 0. split; [reflexivity|].
  unfold obsRel, progEx, orP. cbn. sauto limit: 200.
Qed.

Theorem progEx_asp_42 :
  ASPTriple Under progEx P0 (aspOnly (Some (tt, 42))).
Proof.
  apply asp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 42)) in Hpost. subst r.
  exists 0. split; [reflexivity|].
  unfold obsRel, progEx, orP. cbn. sauto limit: 200.
Qed.

Theorem progEx_asp_not_None :
  ~ ASPTriple Under progEx P0
      (aspOnly (None : option (unit * nat))).
Proof.
  intro H. apply asp_under_spec in H.
  assert (Hpost : aspOnly (None : option (unit * nat)) None).
  { reflexivity. }
  destruct (H None Hpost) as [s [_ Hreach]].
  unfold obsRel, progEx, orP in Hreach. cbn in Hreach.
  sauto limit: 200.
Qed.

Theorem progEx_asp_not_99 :
  ~ ASPTriple Under progEx P0 (aspOnly (Some (tt, 99))).
Proof.
  intro H. apply asp_under_spec in H.
  assert (Hpost : aspOnly (Some (tt, 99)) (Some (tt, 99))).
  { reflexivity. }
  destruct (H (Some (tt, 99)) Hpost) as [s [Hs Hreach]].
  change (s = 0) in Hs. subst s.
  unfold obsRel, progEx, orP in Hreach. cbn in Hreach.
  sauto lq: on limit: 200.
Qed.
