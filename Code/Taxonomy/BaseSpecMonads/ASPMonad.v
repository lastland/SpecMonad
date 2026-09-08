From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPostMonad SPPredicateTransformers.

Import MonadNotation.
Open Scope monad_scope.

Section PureASPMonad.
  Definition JoinPreserving {A} (w : SPPure A) : Prop :=
    Strict w /\ Disjunctive w.

  Definition Singleton {A} (w : SPPure A) : Prop :=    
    forall (p : Prop) (a : A), w p a <-> p /\ w True a.

  (** At [SPPure] the precondition is a [Prop], and under propositional
      extensionality there are only two of those up to equality.  So [Strict]
      already forces [Singleton]; [Disjunctive] is not needed here. *)
  Lemma join_to_singleton {A} (w : SPPure A) :
    JoinPreserving w -> Singleton w.
  Proof.
    intros [HS _] p a.
    assert (HT : p -> p = True).
    { intro Hp. apply propositional_extensionality.
      split; [ intros _; exact I | intros _; exact Hp ]. }
    split.
    - intro Hw.
      assert (Hp : p).
      { apply NNPP. intro Hnp.
        assert (HF : p = False)
          by (apply propositional_extensionality; split; [ exact Hnp | intros [] ]).
        rewrite HF in Hw. exact (HS a Hw). }
      split; [ exact Hp |]. rewrite (HT Hp) in Hw. exact Hw.
    - intros [Hp Hw]. rewrite (HT Hp). exact Hw.
  Qed.

  Lemma singleton_to_join {A} (w : SPPure A) :
    Singleton w -> JoinPreserving w.
  Proof.
    intro H. split.
    - intros a Hw. exact (proj1 (proj1 (H False a) Hw)).
    - intros I i0 p a. split.
      + intro Hw. destruct (proj1 (H (exists j, p j) a) Hw) as [[i Hpi] Htrue].
        exists i. exact (proj2 (H (p i) a) (conj Hpi Htrue)).
      + intros [i Hw]. destruct (proj1 (H (p i) a) Hw) as [Hpi Htrue].
        exact (proj2 (H (exists j, p j) a) (conj (ex_intro _ i Hpi) Htrue)).
  Qed.
  
  Theorem join_iff_singleton {A} (w : SPPure A) :
    JoinPreserving w <-> Singleton w.
  Proof. split; [apply join_to_singleton | apply singleton_to_join]. Qed.

  (* Equivalent to Kenji's formalization *)
  
  Theorem kenji_iff_singleton {A} (w : SPPure A) :
    (Monotone w /\ Codomain w) <-> Singleton w.
  Proof.
    split.
    - intros [Mon Cod] p a. split.
      + intro H. split.
        * exact (Cod p a H).
        * exact (Mon p True a (fun _ => I) H).
      + intros [hp hT].
        exact (Mon True p a (fun _ => hp) hT).
    - intro H. split.
      + intros p q a hpq hw.
        apply H. apply H in hw. destruct hw as [hp hT].
        exact (conj (hpq hp) hT).
      + intros p a hw. apply H in hw. exact (proj1 hw).
  Qed.

  Definition ASPSP (A : Type) : Type := { w : SPPure A | Singleton w }.

  Definition getASP {A} (w : ASPSP A) : SPPure A := proj1_sig w.

  Lemma getASP_singleton {A} (w : ASPSP A) (p : Prop) (a : A) :
    getASP w p a <-> (p /\ getASP w True a).
  Proof. exact (proj2_sig w p a). Qed.
  
  (** Directed forms, used instead of [rewrite]: the pattern [getSP ?w ?p ?a]
      is maximally general, so setoid-rewriting with it inside subset terms is
      catastrophically slow (minutes vs. tenths of a second). *)
  Definition getASP_split {A} (w : ASPSP A) (p : Prop) (a : A)
    : getASP w p a -> (p /\ getASP w True a) := proj1 (getASP_singleton w p a).
  Definition getASP_merge {A} (w : ASPSP A) (p : Prop) (a : A)
    : (p /\ getASP w True a) -> getASP w p a := proj2 (getASP_singleton w p a).
  
  #[program] Definition retASP {A} (v : A) : ASPSP A :=
    fun p a => p /\ a = v.
  Next Obligation.
  Proof. intros p a. tauto. Qed.
  
  #[program] Definition bindASP {A B} (m : ASPSP A) (k : A -> ASPSP B) : ASPSP B :=
    fun p b => exists a, (k a) (m p a) b.
  Next Obligation.
  Proof.
    intros p b. split.
    - (* pull [p] out through [k a], then through [m], and rebuild at [True] *)
      intros [a H].
      destruct (proj1 (proj2_sig (k a) (proj1_sig m p a) b) H) as [Hmp Hk].
      destruct (proj1 (proj2_sig m p a) Hmp) as [Hp HmT].
      split; [ exact Hp |]. exists a.
      exact (proj2 (proj2_sig (k a) (proj1_sig m True a) b) (conj HmT Hk)).
    - intros [Hp [a H]].
      destruct (proj1 (proj2_sig (k a) (proj1_sig m True a) b) H) as [HmT Hk].
      exists a.
      exact (proj2 (proj2_sig (k a) (proj1_sig m p a) b)
               (conj (proj2 (proj2_sig m p a) (conj Hp HmT)) Hk)).
  Qed.
        
  #[global] Instance Monad_ASPSP : Monad ASPSP :=
    {| ret := fun _ => retASP ;
      bind := fun _ _ => bindASP |}.

  #[global] Instance Eq1_ASPSP : Eq1 ASPSP :=
    fun A m n => forall p a, getASP m p a <-> getASP n p a.

  #[global] Instance Eq1Equivalence_ASPSP
    : @Eq1Equivalence ASPSP _ Eq1_ASPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a). specialize (H2 p a). tauto.
  Qed.

  #[global] Instance MonadLawsE_ASPSP
    : @MonadLawsE ASPSP Eq1_ASPSP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_ASPSP. intros p b. split.
      + intros [a H]. destruct (getASP_split (f a) _ b H) as [[Hp Heq] Hk].
        subst a. apply getASP_merge. split; assumption.
      + intro H. destruct (getASP_split (f x) p b H) as [Hp Hk].
        exists x. apply getASP_merge.
        split; [split; [exact Hp | reflexivity] | exact Hk].
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_ASPSP. intros p a. split.
      + intros [a0 [Hm Heq]]. subst a. exact Hm.
      + intro H. exists a. split; [exact H | reflexivity].
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_ASPSP. intros p c. split.
      + intros [b H]. destruct (getASP_split (g b) _ c H) as [[a Ha] Hg].
        exists a, b. apply getASP_merge. split; [exact Ha | exact Hg].
      + intros [a [b H]]. destruct (getASP_split (g b) _ c H) as [Hk Hg].
        exists b. apply getASP_merge. split; [exists a; exact Hk | exact Hg].
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_ASPSP in *. intros p b.
      split; intros [a H]; exists a;
        destruct (getASP_split _ _ b H) as [Hm Hk]; apply getASP_merge; split.
      + apply Hxy. exact Hm.
      + apply Hfg. exact Hk.
      + apply Hxy. exact Hm.
      + apply Hfg. exact Hk.
  Qed.
End PureASPMonad.

Section ProgASPMonad.
  Variable S : Type.

  Definition JoinPreservingProg {A} (w : SPStExc A) : Prop :=
    StrictProg S w /\ DisjunctiveProg S w.

  Definition SingletonProg {A} (w : SPStExc A) : Prop :=
    forall (pre : S -> Prop) (r : option (A * S)),
      w pre r <-> exists s0, pre s0 /\ w (fun s => s = s0) r.

  (** Index the join by the *subset* [{s0 | pre s0}] and take the singleton
      [fun s => s = s0] at each index: the union of those singletons is
      pointwise [pre], and the indexed join is literally the right-hand side
      of [SingletonProg].  Rewriting "pointwise" to "equal" is what needs
      [functional_extensionality] + [propositional_extensionality] here,
      exactly as [join_to_singleton] needs [propositional_extensionality]. *)
  Lemma join_to_singleton_prog {A} (w : SPStExc A) :
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

  Lemma singleton_to_join_prog {A} (w : SPStExc A) :
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

  Theorem join_iff_singleton_prog {A} (w : SPStExc A) :
    JoinPreservingProg w <-> SingletonProg w.
  Proof. split; [apply join_to_singleton_prog | apply singleton_to_join_prog ]. Qed.

  Definition ASPStExc (A : Type) : Type := { w : SPStExc A | SingletonProg w }.

  Definition getASPStExc {A} (w : ASPStExc A) : SPStExc A :=
    proj1_sig w.

  Lemma getProg_singleton {A} (w : ASPStExc A) (pre : S -> Prop) (r : option (A * S)) :
    getASPStExc w pre r <-> exists s0, pre s0 /\ getASPStExc w (fun s => s = s0) r.
  Proof. exact (proj2_sig w pre r). Qed.

  (** [SingletonProg] supplies congruence in the precondition for free — which
      is why the monad laws below need no extensionality axiom. *)
  Lemma getProg_cong {A} (w : ASPStExc A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s <-> Q s) -> (getASPStExc w P r <-> getASPStExc w Q r).
  Proof.
    intro HPQ. split; intro H; apply getProg_singleton in H;
      destruct H as [s0 [Hs Hw]]; apply getProg_singleton; exists s0.
    - split; [exact (proj1 (HPQ s0) Hs) | exact Hw].
    - split; [exact (proj2 (HPQ s0) Hs) | exact Hw].
  Qed.

  Lemma getProg_join {A} (w : ASPStExc A) (I : Type) (p : I -> (S -> Prop))
    (r : option (A * S)) :
    getASPStExc w (fun s => exists i, p i s) r <-> exists i, getASPStExc w (p i) r.
  Proof.
    split.
    - intro H. apply getProg_singleton in H. destruct H as [s0 [[i Hpi] Hw]].
      exists i. apply getProg_singleton. exists s0. split; [ exact Hpi | exact Hw ].
    - intros [i H]. apply getProg_singleton in H. destruct H as [s0 [Hpi Hw]].
      apply getProg_singleton. exists s0.
      split; [ exists i; exact Hpi | exact Hw ].
  Qed.

  #[program] Definition retASPStExc {A} (a : A) : ASPStExc A :=
    fun pre r => exists s0, pre s0 /\ r = Some (a, s0).
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s0 [Hp Heq]]. exists s0. split; [exact Hp |].
      exists s0. split; [reflexivity | exact Heq].
    - intros [s0 [Hp [s1 [Heq1 Heq2]]]]. subst s1.
      exists s0. split; [exact Hp | exact Heq2].
  Qed.

  #[program] Definition bindASPStExc {A B}
    (m : ASPStExc A) (k : A -> ASPStExc B) : ASPStExc B :=
    fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
  Next Obligation.
    unfold ASPStExc. intros pre r.
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
    Instance Monad__ASPStExc : Monad ASPStExc :=
    {| ret := fun _ => @retASPStExc _ ;
      bind := fun _ _ => @bindASPStExc _ _ |}.

  #[global] Instance Eq1__ASPStExc : Eq1 ASPStExc :=
    fun A m n => forall pre r, getASPStExc m pre r <-> getASPStExc n pre r.

  #[global] Instance Eq1Equivalence__ASPStExc
    : @Eq1Equivalence ASPStExc _ Eq1__ASPStExc.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__ASPStExc
    : @MonadLawsE ASPStExc Eq1__ASPStExc _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ASPStExc. intros pre r.
      (* the intermediate precondition [fun s => ret x can produce (x, s)]
         is pointwise [pre] *)
      assert (Hcong : forall s, getASPStExc (retASPStExc x) pre (Some (x, s)) <-> pre s).
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
      intros A x. unfold eq1, Eq1__ASPStExc. intros pre r. split.
      + intros [[a [s0 [Hm Heq]]] | [Hr Hn]]; subst r; assumption.
      + intro H. destruct r as [[a s0]|].
        * left. exists a, s0. split; [exact H | reflexivity].
        * right. split; [reflexivity | exact H].
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ASPStExc. intros pre r.
      (* the [Some] outcomes of [bind x f] never come from its [None] branch *)
      assert (Hsimp : forall b s1,
        getASPStExc (bindASPStExc x f) pre (Some (b, s1)) <->
        exists a, getASPStExc (f a)
                    (fun s0 => getASPStExc x pre (Some (a, s0))) (Some (b, s1))).
      { intros b s1. split.
        - intros [H | [Hc _]]; [exact H | discriminate Hc].
        - intro H. left. exact H. }
      (* ... so the continuation's precondition is an [A]-indexed join, and
         [g b] preserves it — this is the step [KenjiProgSP] cannot make *)
      assert (Hg : forall b,
        getASPStExc (g b) (fun s1 => getASPStExc (bindASPStExc x f) pre (Some (b, s1))) r <->
        exists a, getASPStExc (g b)
                    (fun s1 => getASPStExc (f a)
                       (fun s0 => getASPStExc x pre (Some (a, s0))) (Some (b, s1))) r).
      { intro b.
        transitivity (getASPStExc (g b)
          (fun s1 => exists a, getASPStExc (f a)
             (fun s0 => getASPStExc x pre (Some (a, s0))) (Some (b, s1))) r).
        - apply getProg_cong. exact (Hsimp b).
        - exact (getProg_join (g b) A
                   (fun a s1 => getASPStExc (f a)
                      (fun s0 => getASPStExc x pre (Some (a, s0))) (Some (b, s1))) r). }
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
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ASPStExc in *. intros pre r.
      assert (Hstep : forall a,
        getASPStExc (f a) (fun s0 => getASPStExc x pre (Some (a, s0))) r <->
        getASPStExc (g a) (fun s0 => getASPStExc y pre (Some (a, s0))) r).
      { intro a.
        transitivity (getASPStExc (g a) (fun s0 => getASPStExc x pre (Some (a, s0))) r).
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
  
Arguments retASPStExc {_} {_}.
Arguments bindASPStExc {_} {_} {_}.
Arguments getASPStExc {_} {_}.

(* ================================================================= *)
(** * Terminating-slice variant (factored out of SPSimplerSpecMonads.v) *)
(* ================================================================= *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.

Module StASP.
  Import StTrans.
Section ProgASPMonad.
  Variable S : Type.

  Definition JoinPreservingProg {A} (w : SPSt A) : Prop :=
    StrictProg S w /\ DisjunctiveProg S w.

  Definition SingletonProg {A} (w : SPSt A) : Prop :=
    forall (pre : S -> Prop) (r : A * S),
      w pre r <-> exists s0, pre s0 /\ w (fun s => s = s0) r.

  Lemma join_to_singleton_prog {A} (w : SPSt A) :
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

  Lemma singleton_to_join_prog {A} (w : SPSt A) :
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

  Definition ASPSt (A : Type) : Type := { w : SPSt A | SingletonProg w }.

  Definition getASPSt {A} (w : ASPSt A) : SPSt A := proj1_sig w.

  Lemma getProg_singleton {A} (w : ASPSt A) (pre : S -> Prop) (r : A * S) :
    getASPSt w pre r <-> exists s0, pre s0 /\ getASPSt w (fun s => s = s0) r.
  Proof. exact (proj2_sig w pre r). Qed.

  Lemma getProg_cong {A} (w : ASPSt A) (P Q : S -> Prop) (r : A * S) :
    (forall s, P s <-> Q s) -> (getASPSt w P r <-> getASPSt w Q r).
  Proof.
    intro HPQ. split; intro H; apply getProg_singleton in H;
      destruct H as [s0 [Hs Hw]]; apply getProg_singleton; exists s0.
    - split; [ exact (proj1 (HPQ s0) Hs) | exact Hw ].
    - split; [ exact (proj2 (HPQ s0) Hs) | exact Hw ].
  Qed.

  Lemma getProg_join {A} (w : ASPSt A) (I : Type) (p : I -> (S -> Prop))
    (r : A * S) :
    getASPSt w (fun s => exists i, p i s) r <-> exists i, getASPSt w (p i) r.
  Proof.
    split.
    - intro H. apply getProg_singleton in H. destruct H as [s0 [[i Hpi] Hw]].
      exists i. apply getProg_singleton. exists s0. split; [ exact Hpi | exact Hw ].
    - intros [i H]. apply getProg_singleton in H. destruct H as [s0 [Hpi Hw]].
      apply getProg_singleton. exists s0.
      split; [ exists i; exact Hpi | exact Hw ].
  Qed.

  (** [ret] and [bind].  Compare [SPSpecMonads]: there [bind] carried an extra
      [\/ (r = None /\ m pre None)] disjunct for the exceptional outcome.  With
      no such outcome the disjunct disappears. *)

  #[program] Definition retASPSt {A} (a : A) : ASPSt A :=
    fun pre r => exists s0, pre s0 /\ r = (a, s0).
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s0 [Hp Heq]]. exists s0. split; [ exact Hp |].
      exists s0. split; [ reflexivity | exact Heq ].
    - intros [s0 [Hp [s1 [Heq1 Heq2]]]]. subst s1.
      exists s0. split; [ exact Hp | exact Heq2 ].
  Qed.

  #[program] Definition bindASPSt {A B}
    (m : ASPSt A) (k : A -> ASPSt B) : ASPSt B :=
    fun pre r => exists a, k a (fun s0 => m pre (a, s0)) r.
  Next Obligation.
    unfold SingletonProg. intros pre r.
    pose proof (proj2_sig m) as Hm. unfold SingletonProg in Hm.
    pose proof (fun a => proj2_sig (k a)) as Hk. unfold SingletonProg in Hk.
    split.
    - intros [a Ha].
      destruct (proj1 (Hk a _ r) Ha) as [s1 [Hms Hka]].
      destruct (proj1 (Hm pre (a, s1)) Hms) as [s0 [Hp Hm0]].
      exists s0. split; [ exact Hp |]. exists a.
      apply (Hk a). exists s1. split; [ exact Hm0 | exact Hka ].
    - intros [s0 [Hp [a Ha]]].
      destruct (proj1 (Hk a _ r) Ha) as [s1 [Hms Hka]].
      exists a. apply (Hk a). exists s1. split; [| exact Hka ].
      apply (Hm pre (a, s1)). exists s0. split; [ exact Hp | exact Hms ].
  Qed.

  #[global] Instance Monad__ASPSt : Monad ASPSt :=
    {| ret := fun _ => @retASPSt _ ;
       bind := fun _ _ => @bindASPSt _ _ |}.

  #[global] Instance Eq1__ASPSt : Eq1 ASPSt :=
    fun A m n => forall pre r, getASPSt m pre r <-> getASPSt n pre r.

  #[global] Instance Eq1Equivalence__ASPSt
    : @Eq1Equivalence ASPSt _ Eq1__ASPSt.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__ASPSt
    : @MonadLawsE ASPSt Eq1__ASPSt _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ASPSt. intros pre r. split.
      + intros [a Ha].
        destruct (proj1 (getProg_singleton (f a) _ r) Ha) as [s0 [[s1 [Hp Heq]] Hw]].
        assert (Hax : a = x) by congruence. assert (Hss : s0 = s1) by congruence.
        subst a. subst s1.
        apply getProg_singleton. exists s0. split; [ exact Hp | exact Hw ].
      + intro H. destruct (proj1 (getProg_singleton (f x) pre r) H) as [s0 [Hp Hw]].
        exists x. apply getProg_singleton. exists s0. split; [| exact Hw ].
        exists s0. split; [ exact Hp | reflexivity ].
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ASPSt. intros pre r. split.
      + intros [a [s0 [Hm Heq]]]. subst r. exact Hm.
      + intro H. destruct r as [a s0]. exists a. exists s0.
        split; [ exact H | reflexivity ].
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ASPSt. intros pre r. split.
      + intros [b Hb].
        destruct (proj1 (getProg_join (g b) A
                           (fun a s1 => getASPSt (f a)
                                          (fun s0 => getASPSt x pre (a, s0)) (b, s1)) r)
                    Hb) as [a Ha].
        exists a. exists b. exact Ha.
      + intros [a [b Hb]]. exists b.
        apply (getProg_join (g b) A
                 (fun a0 s1 => getASPSt (f a0)
                                 (fun s0 => getASPSt x pre (a0, s0)) (b, s1)) r).
        exists a. exact Hb.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ASPSt in *. intros pre r.
      split; intros [a Ha]; exists a.
      + apply (getProg_cong (g a) (fun s0 => getASPSt x pre (a, s0)) _ r);
          [ intro s0; exact (Hxy pre (a, s0)) | apply Hfg; exact Ha ].
      + apply (getProg_cong (f a) (fun s0 => getASPSt y pre (a, s0)) _ r);
          [ intro s0; symmetry; exact (Hxy pre (a, s0)) | apply Hfg; exact Ha ].
  Qed.

End ProgASPMonad.

Arguments retASPSt {_} {_}.
Arguments bindASPSt {_} {_} {_}.
Arguments getASPSt {_} {_}.


(* ---- order and monotonicity ---- *)

Section StASPOrders.
  Variable S : Type.
  Definition ordASPSt {A} (m1 m2 : ASPSt S A) : Prop :=
    forall pre r, getASPSt m1 pre r -> getASPSt m2 pre r.
  Definition ordASPStAt {A} (pre : S -> Prop) (m1 m2 : ASPSt S A) : Prop :=
    forall r, getASPSt m1 pre r -> getASPSt m2 pre r.
  Lemma asp_bot {A} (w : ASPSt S A) (r : (A * S)) :
    ~ getASPSt w (fun _ => False) r.
  Proof.
    intro Hc. destruct (proj1 (getProg_singleton S w _ r) Hc) as [s0 [[] _]].
  Qed.
  Lemma aspMono {A} (w : ASPSt S A) (P Q : S -> Prop) (r : (A * S)) :
    (forall s, P s -> Q s) -> getASPSt w P r -> getASPSt w Q r.
  Proof.
    intros Hsub Hw.
    destruct (proj1 (getProg_singleton S w P r) Hw) as [s0 [Hp Hs]].
    apply getProg_singleton. exists s0. split; [ exact (Hsub s0 Hp) | exact Hs ].
  Qed.
End StASPOrders.
Arguments ordASPSt {_} {_}.
Arguments ordASPStAt {_} {_}.
End StASP.

(* ================================================================= *)
(** * Refinement order and monotonicity for ASP *)
(* ================================================================= *)

Section ASPOrders.
  Variable S : Type.
  Definition ordASPStExc {A} (m1 m2 : ASPStExc S A) : Prop :=
    forall pre r, getASPStExc m1 pre r -> getASPStExc m2 pre r.
  Definition ordASPStExcAt {A} (pre : S -> Prop) (m1 m2 : ASPStExc S A) : Prop :=
    forall r, getASPStExc m1 pre r -> getASPStExc m2 pre r.
  Lemma asp_bot {A} (w : ASPStExc S A) (r : option (A * S)) :
    ~ getASPStExc w (fun _ => False) r.
  Proof.
    intro Hc. destruct (proj1 (getProg_singleton S w _ r) Hc) as [s0 [[] _]].
  Qed.
  Lemma aspMono {A} (w : ASPStExc S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getASPStExc w P r -> getASPStExc w Q r.
  Proof.
    intros Hsub Hw.
    destruct (proj1 (getProg_singleton S w P r) Hw) as [s0 [Hp Hs]].
    apply getProg_singleton. exists s0. split; [ exact (Hsub s0 Hp) | exact Hs ].
  Qed.
End ASPOrders.

Arguments ordASPStExc {_} {_}.
Arguments ordASPStExcAt {_} {_}.
