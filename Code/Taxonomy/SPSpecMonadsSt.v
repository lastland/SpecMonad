From ExtLib Require Import
  Monad MonadState
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.

(** * SP specification monads over a PLAIN stateful outcome

    The development of [SPSpecMonads] indexed its transformers by the outcome
    type [option (A * S)] — state plus one distinguished "no result" token.
    This file is the same development over [A * S]: pure state, no exception
    and no divergence, so every outcome is a normal return.

    Almost nothing about the healthiness conditions or the carrier bridges
    depends on the outcome type; what changes is [bind], whose composite
    relation loses its [None] branch and becomes simply

      [Comp s r := exists a smid, R s (a, smid) /\ K a smid r].

    Everything lives in a module so the names can mirror [SPSpecMonads]
    exactly without clashing. *)

Module StSP.

Section Transformers.
  Variable S : Type.

  Definition ProgSP (A : Type) : Type := (S -> Prop) -> (A * S) -> Prop.

  Definition StrictProg {A} (w : ProgSP A) : Prop :=
    forall (r : A * S), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : ProgSP A) : Prop :=
    forall (r : A * S), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : ProgSP A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : A * S),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : A * S),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.

End Transformers.

Arguments ProgSP {_}.

(* ==================================================================== *)
(** * The angelic monad                                                  *)
(* ==================================================================== *)

Section ProgASPMonad.
  Variable S : Type.

  Definition JoinPreservingProg {A} (w : ProgSP A) : Prop :=
    StrictProg S w /\ DisjunctiveProg S w.

  Definition SingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : A * S),
      w pre r <-> exists s0, pre s0 /\ w (fun s => s = s0) r.

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

  Definition ASPProgSP (A : Type) : Type := { w : ProgSP A | SingletonProg w }.

  Definition getProgASP {A} (w : ASPProgSP A) : ProgSP A := proj1_sig w.

  Lemma getProg_singleton {A} (w : ASPProgSP A) (pre : S -> Prop) (r : A * S) :
    getProgASP w pre r <-> exists s0, pre s0 /\ getProgASP w (fun s => s = s0) r.
  Proof. exact (proj2_sig w pre r). Qed.

  Lemma getProg_cong {A} (w : ASPProgSP A) (P Q : S -> Prop) (r : A * S) :
    (forall s, P s <-> Q s) -> (getProgASP w P r <-> getProgASP w Q r).
  Proof.
    intro HPQ. split; intro H; apply getProg_singleton in H;
      destruct H as [s0 [Hs Hw]]; apply getProg_singleton; exists s0.
    - split; [ exact (proj1 (HPQ s0) Hs) | exact Hw ].
    - split; [ exact (proj2 (HPQ s0) Hs) | exact Hw ].
  Qed.

  Lemma getProg_join {A} (w : ASPProgSP A) (I : Type) (p : I -> (S -> Prop))
    (r : A * S) :
    getProgASP w (fun s => exists i, p i s) r <-> exists i, getProgASP w (p i) r.
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

  #[program] Definition retASPProg {A} (a : A) : ASPProgSP A :=
    fun pre r => exists s0, pre s0 /\ r = (a, s0).
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s0 [Hp Heq]]. exists s0. split; [ exact Hp |].
      exists s0. split; [ reflexivity | exact Heq ].
    - intros [s0 [Hp [s1 [Heq1 Heq2]]]]. subst s1.
      exists s0. split; [ exact Hp | exact Heq2 ].
  Qed.

  #[program] Definition bindASPProg {A B}
    (m : ASPProgSP A) (k : A -> ASPProgSP B) : ASPProgSP B :=
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

  #[global] Instance Monad__ASPProgSP : Monad ASPProgSP :=
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

  #[global] Instance MonadLaws__ProgASP
    : @MonadLawsE ASPProgSP Eq1__ProgASP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ProgASP. intros pre r. split.
      + intros [a Ha].
        destruct (proj1 (getProg_singleton (f a) _ r) Ha) as [s0 [[s1 [Hp Heq]] Hw]].
        assert (Hax : a = x) by congruence. assert (Hss : s0 = s1) by congruence.
        subst a. subst s1.
        apply getProg_singleton. exists s0. split; [ exact Hp | exact Hw ].
      + intro H. destruct (proj1 (getProg_singleton (f x) pre r) H) as [s0 [Hp Hw]].
        exists x. apply getProg_singleton. exists s0. split; [| exact Hw ].
        exists s0. split; [ exact Hp | reflexivity ].
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ProgASP. intros pre r. split.
      + intros [a [s0 [Hm Heq]]]. subst r. exact Hm.
      + intro H. destruct r as [a s0]. exists a. exists s0.
        split; [ exact H | reflexivity ].
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ProgASP. intros pre r. split.
      + intros [b Hb].
        destruct (proj1 (getProg_join (g b) A
                           (fun a s1 => getProgASP (f a)
                                          (fun s0 => getProgASP x pre (a, s0)) (b, s1)) r)
                    Hb) as [a Ha].
        exists a. exists b. exact Ha.
      + intros [a [b Hb]]. exists b.
        apply (getProg_join (g b) A
                 (fun a0 s1 => getProgASP (f a0)
                                 (fun s0 => getProgASP x pre (a0, s0)) (b, s1)) r).
        exists a. exact Hb.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgASP in *. intros pre r.
      split; intros [a Ha]; exists a.
      + apply (getProg_cong (g a) (fun s0 => getProgASP x pre (a, s0)) _ r);
          [ intro s0; exact (Hxy pre (a, s0)) | apply Hfg; exact Ha ].
      + apply (getProg_cong (f a) (fun s0 => getProgASP y pre (a, s0)) _ r);
          [ intro s0; symmetry; exact (Hxy pre (a, s0)) | apply Hfg; exact Ha ].
  Qed.

End ProgASPMonad.

Arguments retASPProg {_} {_}.
Arguments bindASPProg {_} {_} {_}.
Arguments getProgASP {_} {_}.

(* ==================================================================== *)
(** * The demonic-liberal monad                                          *)
(* ==================================================================== *)

Section ProgDSLPMonad.
  Variable S : Type.

  Definition MeetPreservingProg {A} (w : ProgSP A) : Prop :=
    TerminatingProg S w /\ ConjunctiveProg S w.

  Definition MSingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : A * S),
      w pre r <-> forall s0, ~ pre s0 -> w (fun s => s <> s0) r.

  (** Anything of DSLP shape is [MSingletonProg]. *)
  Lemma dslp_msingleton {A} (R : S -> (A * S) -> Prop) :
    MSingletonProg (fun pre r => forall s, R s r -> pre s).
  Proof.
    intros pre r. split.
    - intros H s0 Hns0 s Hs Heq. subst s. exact (Hns0 (H s0 Hs)).
    - intros H s Hs. apply NNPP. intro Hnp. exact (H s Hnp s Hs eq_refl).
  Qed.

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
    (pre : S -> Prop) (r : A * S) :
    w pre r <-> (forall s, ~ w (fun s' => s' <> s) r -> pre s).
  Proof.
    split.
    - intros Hp s Hns. apply NNPP. intro Hnp.
      exact (Hns (proj1 (Hw pre r) Hp s Hnp)).
    - intro H. apply Hw. intros s0 Hns0.
      destruct (classic (w (fun s' => s' <> s0) r)) as [Hy | Hn];
        [ exact Hy | destruct (Hns0 (H s0 Hn)) ].
  Qed.

  Lemma msingletonProg_mono {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : A * S) :
    (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros Hsub H. apply (msingletonProg_repr w Hw). intros s Hc.
    exact (Hsub s (proj1 (msingletonProg_repr w Hw P r) H s Hc)).
  Qed.

  Lemma msingletonProg_cong {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : A * S) :
    (forall s, P s <-> Q s) -> (w P r <-> w Q r).
  Proof.
    intro H. split; intro Hw'.
    - exact (msingletonProg_mono w Hw P Q r (fun s hs => proj1 (H s) hs) Hw').
    - exact (msingletonProg_mono w Hw Q P r (fun s hs => proj2 (H s) hs) Hw').
  Qed.

  Lemma msingletonProg_meet {A} (w : ProgSP A) (Hw : MSingletonProg w)
    (I : Type) (p : I -> (S -> Prop)) (r : A * S) :
    w (fun s => forall i, p i s) r <-> forall i, w (p i) r.
  Proof.
    split.
    - intros H i. apply (msingletonProg_repr w Hw). intros s Hc.
      exact (proj1 (msingletonProg_repr w Hw (fun s0 => forall j, p j s0) r) H s Hc i).
    - intro H. apply (msingletonProg_repr w Hw). intros s Hc i.
      exact (proj1 (msingletonProg_repr w Hw (p i) r) (H i) s Hc).
  Qed.

  Definition DSLPProgSP (A : Type) : Type := { w : ProgSP A | MSingletonProg w }.

  Definition getProgDSLP {A} (w : DSLPProgSP A) : ProgSP A := proj1_sig w.

  #[program] Definition retDSLPProg {A} (v : A) : DSLPProgSP A :=
    fun pre r => forall s0, r = (v, s0) -> pre s0.
  Next Obligation. exact (dslp_msingleton (fun s r => r = (v, s))). Qed.

  (** Dual to [bindASPProg]: [SPSpecMonads] carried an extra
      [/\ (r = None -> m pre None)] conjunct; with no exceptional outcome it
      disappears. *)
  #[program] Definition bindDSLPProg {A B}
    (m : DSLPProgSP A) (k : A -> DSLPProgSP B) : DSLPProgSP B :=
    fun pre r => forall a, k a (fun s0 => m pre (a, s0)) r.
  Next Obligation.
    pose proof (proj2_sig m) as Hm.
    pose proof (fun a => proj2_sig (k a)) as Hk.
    apply (msingletonProg_ext
             (fun pre r =>
                forall s,
                  (exists a s', ~ proj1_sig (k a) (fun t => t <> s') r
                                /\ ~ proj1_sig m (fun t => t <> s) (a, s')) -> pre s)).
    - intros pre r. split.
      + intros H a. apply (msingletonProg_repr _ (Hk a)). intros s' Hck.
        apply (msingletonProg_repr _ Hm). intros s Hcm.
        apply H. exists a, s'. split; assumption.
      + intros H1 s [a [s' [Hck Hcm]]].
        exact (proj1 (msingletonProg_repr _ Hm _ (a, s'))
                 (proj1 (msingletonProg_repr _ (Hk a) _ r) (H1 a) s' Hck) s Hcm).
    - apply dslp_msingleton.
  Qed.

  #[global] Instance Monad__DSLPProgSP : Monad DSLPProgSP :=
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

  Lemma msingletonProg_top {A} (w : ProgSP A) (Hw : MSingletonProg w) (r : A * S) :
    w (fun _ => True) r.
  Proof. apply Hw. intros s0 Hn. destruct (Hn I). Qed.

  #[global] Instance MonadLaws__ProgDSLP
    : @MonadLawsE DSLPProgSP Eq1__ProgDSLP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ProgDSLP. intros pre r. split.
      + intro H. specialize (H x).
        apply (msingletonProg_cong _ (proj2_sig (f x))
                 (fun s0 => forall s1, (x, s0) = (x, s1) -> pre s1) pre r); [| exact H ].
        intro s0. split.
        * intro Hc. exact (Hc s0 eq_refl).
        * intros Hp s1 Heq. assert (Hs : s0 = s1) by congruence. subst s1. exact Hp.
      + intros H a. destruct (classic (a = x)) as [Hax | Hne].
        * subst a.
          apply (msingletonProg_cong _ (proj2_sig (f x)) pre
                   (fun s0 => forall s1, (x, s0) = (x, s1) -> pre s1) r); [| exact H ].
          intro s0. split.
          -- intros Hp s1 Heq. assert (Hs : s0 = s1) by congruence. subst s1. exact Hp.
          -- intro Hc. exact (Hc s0 eq_refl).
        * apply (msingletonProg_cong _ (proj2_sig (f a)) (fun _ => True)
                   (fun s0 => forall s1, (a, s0) = (x, s1) -> pre s1) r).
          -- intro s0. split.
             ++ intros _ s1 Heq. assert (Hax : a = x) by congruence.
                destruct (Hne Hax).
             ++ intros _. exact I.
          -- exact (msingletonProg_top _ (proj2_sig (f a)) r).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ProgDSLP. intros pre r. split.
      + intro H. destruct r as [a0 s0]. exact (H a0 s0 eq_refl).
      + intros H a s0 Heq. subst r. exact H.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ProgDSLP. intros pre r. split.
      + intros H a b.
        exact (proj1 (msingletonProg_meet _ (proj2_sig (g b)) A
                        (fun a0 s1 => getProgDSLP (f a0)
                           (fun s0 => getProgDSLP x pre (a0, s0)) (b, s1)) r)
                 (H b) a).
      + intros H b.
        apply (msingletonProg_meet _ (proj2_sig (g b)) A
                 (fun a0 s1 => getProgDSLP (f a0)
                    (fun s0 => getProgDSLP x pre (a0, s0)) (b, s1)) r).
        intro a. exact (H a b).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgDSLP in *. intros pre r.
      split; intros H a.
      + apply (msingletonProg_cong _ (proj2_sig (g a))
                 (fun s0 => getProgDSLP x pre (a, s0))
                 (fun s0 => getProgDSLP y pre (a, s0)) r).
        * intro s0. exact (Hxy pre (a, s0)).
        * apply Hfg. exact (H a).
      + apply (msingletonProg_cong _ (proj2_sig (f a))
                 (fun s0 => getProgDSLP y pre (a, s0))
                 (fun s0 => getProgDSLP x pre (a, s0)) r).
        * intro s0. symmetry. exact (Hxy pre (a, s0)).
        * apply Hfg. exact (H a).
  Qed.

End ProgDSLPMonad.

Arguments retDSLPProg {_} {_}.
Arguments bindDSLPProg {_} {_} {_}.
Arguments getProgDSLP {_} {_}.


(* ==================================================================== *)
(** * Kenji's monotone / non-empty conditions                            *)
(* ==================================================================== *)

(** The [PureSP]-level Kenji conditions ([KenjiPureSP], [KenjiPureDSLP]) are
    about [Prop -> A -> Prop] and do not mention the outcome type at all, so
    they are unchanged from [SPSpecMonads] and are not repeated here.  Only the
    [ProgSP] level, which is indexed by the outcome type, needs a version over
    [A * S]. *)

Section KenjiProgSP.
  Variable S : Type.

  Definition MonotoneS {A} (w : ProgSP A) : Prop :=
    forall (p q : S -> Prop) (r : A * S), (forall (s : S), p s -> q s) -> w p r -> w q r.

  Definition CodomainS {A} (w : ProgSP A) : Prop :=
    forall (p : S -> Prop) (r : A * S), w p r -> (exists s, p s).

  Definition KenjiProgSP (A : Type) : Type :=
    { w : ProgSP A | MonotoneS w /\ CodomainS w }.

  Definition getKenjiProgSP {A} (w : KenjiProgSP A) : ProgSP A := proj1_sig w.

  #[program] Definition retKenjiProgSP {A} (v : A) : KenjiProgSP A :=
    fun pre r => exists s0, pre s0 /\ r = (v, s0).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s0 [Hp Heq]]. exists s0. split; [exact (Hpq s0 Hp) | exact Heq].
    - intros p r [s0 [Hp _]]. exists s0. exact Hp.
  Qed.

  #[program] Definition bindKenjiProgSP {A B}
    (m : KenjiProgSP A) (k : A -> KenjiProgSP B) : KenjiProgSP B :=
    fun pre r => exists a, k a (fun s0 => m pre (a, s0)) r.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [a Ha]. exists a.
      apply (proj1 (proj2_sig (k a))
               (fun s0 => proj1_sig m p (a, s0))
               (fun s0 => proj1_sig m q (a, s0)) r);
        [ intros s0 Hm; exact (proj1 (proj2_sig m) p q (a, s0) Hpq Hm) | exact Ha ].
    - intros p r [a Ha].
      destruct (proj2 (proj2_sig (k a))
                  (fun s0 => proj1_sig m p (a, s0)) r Ha) as [s0 Hm].
      exact (proj2 (proj2_sig m) p (a, s0) Hm).
  Qed.

  (** As in [SPSpecMonads], [KenjiProgSP] is CLOSED under the operations but is
      not a lawful monad: [bind_ret_r] holds outright, [bind_ret_l] holds
      because [CodomainS] rules out the wrong-[a] branches and [MonotoneS]
      supplies congruence in the precondition, and [bind_bind] FAILS. *)

  Theorem KenjiProgSP_bind_ret_r {A} (m : KenjiProgSP A)
    (pre : S -> Prop) (r : A * S) :
    getKenjiProgSP (bindKenjiProgSP m retKenjiProgSP) pre r <-> getKenjiProgSP m pre r.
  Proof.
    split.
    - intros [a [s0 [Hm Heq]]]. subst r. exact Hm.
    - intro H. destruct r as [a s0]. exists a, s0.
      split; [ exact H | reflexivity ].
  Qed.

  Theorem KenjiProgSP_bind_ret_l_kenji {A B} (v : A) (k : A -> KenjiProgSP B)
    (pre : S -> Prop) (r : B * S) :
    getKenjiProgSP (bindKenjiProgSP (retKenjiProgSP v) k) pre r
    <-> getKenjiProgSP (k v) pre r.
  Proof.
    split.
    - intros [a Ha].
      (* [CodomainS] of [k a] produces a witness, which forces [a = v] *)
      destruct (proj2 (proj2_sig (k a))
                  (fun s0 => proj1_sig (retKenjiProgSP v) pre (a, s0)) r Ha)
        as [s0 [s1 [Hp Heq]]].
      assert (Hav : a = v) by congruence. subst a.
      (* [MonotoneS] of [k v] then rewrites the precondition back to [pre] *)
      apply (proj1 (proj2_sig (k v))
               (fun s0 => proj1_sig (retKenjiProgSP v) pre (v, s0)) pre r);
        [| exact Ha ].
      intros s [s' [Hp' Heq']]. assert (Hss : s = s') by congruence.
      subst s. exact Hp'.
    - intro H. exists v.
      apply (proj1 (proj2_sig (k v)) pre
               (fun s0 => proj1_sig (retKenjiProgSP v) pre (v, s0)) r);
        [| exact H ].
      intros s Hs. exists s. split; [ exact Hs | reflexivity ].
  Qed.

End KenjiProgSP.

(** Associativity fails, for the same reason as over [option (A * S)]: the
    precondition handed to [g] on the right is a singleton [fun s1 => s1 = a],
    and [g] can see the difference between one state and two. *)
Module KenjiFailingBind.

  #[program] Definition m : KenjiProgSP bool bool :=
    fun pre r => exists s, pre s.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s Hs]. exists s. exact (Hpq s Hs).
    - intros p r [s Hs]. exists s. exact Hs.
  Qed.

  #[program] Definition k : bool -> KenjiProgSP bool unit :=
    fun a => fun pre r => (exists s, pre s) /\ r = (tt, a).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [[s Hs] Heq]. split; [ exists s; exact (Hpq s Hs) | exact Heq ].
    - intros p r [[s Hs] _]. exists s. exact Hs.
  Qed.

  #[program] Definition g : KenjiProgSP bool unit :=
    fun pre r => pre true /\ pre false.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [Ht Hf]. split; [ exact (Hpq true Ht) | exact (Hpq false Hf) ].
    - intros p r [Ht _]. exists true. exact Ht.
  Qed.

  Definition pre : bool -> Prop := fun _ => True.
  Definition r : unit * bool := (tt, true).

  Theorem KenjiProgSP_bind_bind_fails :
    ~ (forall (A B C S : Type) (m : KenjiProgSP S A) (f : A -> KenjiProgSP S B)
              (g : B -> KenjiProgSP S C) (pre : S -> Prop) (r : C * S),
         getKenjiProgSP S (bindKenjiProgSP S (bindKenjiProgSP S m f) g) pre r <->
           getKenjiProgSP S (bindKenjiProgSP S m (fun a => bindKenjiProgSP S (f a) g)) pre r).
  Proof.
    intro H.
    assert (HL : getKenjiProgSP bool
                   (bindKenjiProgSP bool (bindKenjiProgSP bool m k) (fun _ : unit => g))
                   pre r).
    { exists tt. split.
      - exists true. split; [ exists true; exists true; exact I | reflexivity ].
      - exists false. split; [ exists true; exists true; exact I | reflexivity ]. }
    destruct (proj1 (H bool unit unit bool m k (fun _ : unit => g) pre r) HL)
      as [a Ha].
    destruct Ha as [b Hb].
    destruct Hb as [[_ Het] [_ Hef]].
    assert (Ha1 : a = true) by congruence.
    assert (Ha2 : a = false) by congruence.
    congruence.
  Qed.

End KenjiFailingBind.

(* ==================================================================== *)
(** * The demonic monad                                                  *)
(* ==================================================================== *)

Section ProgDSPMonad.
  Variable S : Type.

  Definition StrictPositivelyMeetPreservingProg {A} (w : ProgSP A) : Prop :=
    StrictProg S w /\ ConjunctiveProg S w.
  
  Definition DSPProgSP (A : Type) : Type :=
    { w : ProgSP A | StrictPositivelyMeetPreservingProg w }.

  Definition getProgDSP {A} (w : DSPProgSP A) : ProgSP A := proj1_sig w.

  (** ** Recovery, well-formedness, congruence

      Everything below is stated about the raw transformer
      [fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)]
      and about the composite relation, written out; no auxiliary definitions
      are introduced. *)

  (** Probing that transformer at [fun _ => True] and at the co-singleton of
      [s] recovers [R s r] exactly.  This is the ONLY use of classical logic
      in the section: from "some state reaches [r]" together with "[fun t =>
      t <> s] is not a valid precondition for [r]" one concludes [R s r]. *)
  Lemma dsp_recov {A} (R : S -> (A * S) -> Prop)
    (s : S) (r : (A * S)) :
    (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
     /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s)))
    <-> R s r.
  Proof.
    split.
    - intros [[[t [_ Ht]] _] Hn]. apply NNPP. intro Hns. apply Hn. split.
      + exists t. split; [ intro Heq; subst t; exact (Hns Ht) | exact Ht ].
      + intros t' Ht' Heq. subst t'. exact (Hns Ht').
    - intro Hs. split.
      + split; [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
      + intros [_ Hall]. exact (Hall s Hs eq_refl).
  Qed.

  (** Consequently every such transformer inhabits [DSPProgSP]: this discharges
      each of the [#[program]] obligations below. *)
  Lemma dsp_wf {A} (R : S -> (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\
              (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
               /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s))))
           /\ (forall s,
                 (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
                  /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s)))
                 -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj2 (dsp_recov R s r) Hs) ].
      + intros s' H. exact (Hall s' (proj1 (dsp_recov R s' r) H)).
    - intros [[s [Hp H]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj1 (dsp_recov R s r) H) ].
      + intros s' Hs'. exact (Hall s' (proj2 (dsp_recov R s' r) Hs')).
  Qed.

  (** Extensionally equal relations give extensionally equal transformers. *)
  Lemma dsp_cong {A} (R R' : S -> (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\ R' s r) /\ (forall s, R' s r -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj1 (H s r) Hs) ].
      + intros s' Hs'. exact (Hall s' (proj2 (H s' r) Hs')).
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj2 (H s r) Hs) ].
      + intros s' Hs'. exact (Hall s' (proj1 (H s' r) Hs')).
  Qed.

  (** ... and extensionally equal transformers recover the same relation. *)
  Lemma dsp_rec_ext {A} (w1 w2 : @ProgSP S A)
    (H : forall pre r, w1 pre r <-> w2 pre r) :
    forall (s : S) (r : (A * S)),
      (w1 (fun _ => True) r /\ ~ w1 (fun t => t <> s) r)
      <-> (w2 (fun _ => True) r /\ ~ w2 (fun t => t <> s) r).
  Proof.
    intros s r. split.
    - intros [H1 H2]. split;
        [ exact (proj1 (H _ r) H1) | intro Hc; exact (H2 (proj2 (H _ r) Hc)) ].
    - intros [H1 H2]. split;
        [ exact (proj2 (H _ r) H1) | intro Hc; exact (H2 (proj1 (H _ r) Hc)) ].
  Qed.

  (** The carrier condition [StrictPositivelyMeetPreservingProg] says the same
      thing as "[w] is the DSP of its own recovered relation".  This is the
      bridge between the healthiness reading (which the type states) and the
      fixed-point reading (which the proofs use). *)
  Lemma dsp_carrier {A} (w : ProgSP A) :
    StrictPositivelyMeetPreservingProg w <->
      (forall (pre : S -> Prop) (r : (A * S)), w pre r <->
      ((exists s, pre s /\ (w (fun _ => True) r /\ ~ w (fun t => t <> s) r)) /\
         (forall s, (w (fun _ => True) r /\ ~ w (fun t => t <> s) r) -> pre s))).
  Proof.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    split.
    - intros [HS HC] pre r.
      (* the meet of the two-element family [{P, Q}] is [P] when [P <= Q] *)
      assert (Hmono : forall (P Q : S -> Prop) y,
                 (forall s, P s -> Q s) -> w P y -> w Q y).
      { intros P Q y Hpq Hw.
        assert (Heq : P = (fun s => forall b : bool, (if b then P else Q) s)).
        { apply Hext. intro s. split.
          - intros Hs b. destruct b; [ exact Hs | exact (Hpq s Hs) ].
          - intro Hb. exact (Hb true). }
        rewrite Heq in Hw.
        exact (proj1 (HC bool (inhabits true) (fun b => if b then P else Q) y) Hw false). }
      destruct (classic (w (fun _ => True) r)) as [Htop | Hntop].
      + (* [r] is reachable, so the meet of all preconditions forcing [r] is
           itself one: the least precondition *)
        pose (least := fun s => forall i : { q : S -> Prop | w q r }, proj1_sig i s).
        assert (Hleast : w least r).
        { unfold least.
          apply (HC { q : S -> Prop | w q r }
                   (inhabits (exist (fun q => w q r) (fun _ : S => True) Htop))
                   (fun i => proj1_sig i) r).
          intro i. exact (proj2_sig i). }
        assert (Hlb : forall q, w q r -> forall s, least s -> q s).
        { intros q Hq s Hs. exact (Hs (exist (fun q0 => w q0 r) q Hq)). }
        (* strictness is what makes the least precondition nonempty *)
        assert (Hne : exists s, least s).
        { apply NNPP. intro Hno. apply (HS r).
          assert (Heq : least = (fun _ : S => False)).
          { apply Hext. intro s. split;
              [ intro Hs; exact (Hno (ex_intro _ s Hs)) | intros [] ]. }
          rewrite Heq in Hleast. exact Hleast. }
        assert (Hrec : forall s, (w (fun _ => True) r /\ ~ w (fun t => t <> s) r)
                                 <-> least s).
        { intro s. split.
          - intros [_ Hn]. apply NNPP. intro Hns. apply Hn.
            apply (Hmono least (fun t => t <> s) r); [| exact Hleast ].
            intros t Ht Heq. subst t. exact (Hns Ht).
          - intros Hls. split; [ exact Htop |].
            intro Hc. exact (Hlb (fun t => t <> s) Hc s Hls eq_refl). }
        split.
        * intro Hw. split.
          -- destruct Hne as [s Hs]. exists s.
             split; [ exact (Hlb pre Hw s Hs) | exact (proj2 (Hrec s) Hs) ].
          -- intros s Hs. exact (Hlb pre Hw s (proj1 (Hrec s) Hs)).
        * intros [_ Hall].
          apply (Hmono least pre r); [| exact Hleast ].
          intros s Hs. exact (Hall s (proj2 (Hrec s) Hs)).
      + (* [r] is unreachable: both sides are false *)
        split.
        * intro Hw. exfalso. apply Hntop.
          apply (Hmono pre (fun _ => True) r); [ intros; exact I | exact Hw ].
        * intros [[s [_ [Htop _]]] _]. exfalso. exact (Hntop Htop).
    - intro HD. split.
      + intros r Hc.
        destruct (proj1 (HD (fun _ => False) r) Hc) as [[s [[] _]] _].
      + intros J Hi0 p x. destruct Hi0 as [i0]. split.
        * intro Hw.
          destruct (proj1 (HD (fun s => forall i : J, p i s) x) Hw)
            as [[s [Hms Hrec]] Hall].
          intro i. apply (HD (fun s => p i s) x). split.
          -- exists s. split; [ exact (Hms i) | exact Hrec ].
          -- intros s' Hrec'. exact (Hall s' Hrec' i).
        * intro Hall. apply (HD (fun s => forall i : J, p i s) x).
          assert (Hpred : forall s, (w (fun _ => True) x
                                     /\ ~ w (fun t => t <> s) x) -> forall i, p i s).
          { intros s Hrec i.
            exact (proj2 (proj1 (HD (fun s0 => p i s0) x) (Hall i)) s Hrec). }
          destruct (proj1 (HD (fun s0 => p i0 s0) x) (Hall i0)) as [[s0 [_ Hrec0]] _].
          split; [ exists s0; split; [ exact (Hpred s0 Hrec0) | exact Hrec0 ]
                 | exact Hpred ].
  Qed.

  Lemma dsp_shape_wf {A} (R : S -> (A * S) -> Prop) :
    StrictPositivelyMeetPreservingProg
      (fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)).
  Proof. apply dsp_carrier. intros pre r. exact (dsp_wf R pre r). Qed.

  Lemma getProgDSP_carrier {A} (w : DSPProgSP A) (pre : S -> Prop) (r : A * S) :
    getProgDSP w pre r <->
      ((exists s, pre s /\ (getProgDSP w (fun _ => True) r
                            /\ ~ getProgDSP w (fun t => t <> s) r)) /\
         (forall s, (getProgDSP w (fun _ => True) r
                     /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s)).
  Proof. exact (proj1 (dsp_carrier (getProgDSP w)) (proj2_sig w) pre r). Qed.

  (** ** The composite relation.  With no exceptional outcome it is a single
      existential over the intermediate state — no [match], no [None] case. *)

  Lemma comp_cong {A B} (R R' : S -> (A * S) -> Prop)
    (K K' : A -> S -> (B * S) -> Prop)
    (HR : forall s r, R s r <-> R' s r)
    (HK : forall a s r, K a s r <-> K' a s r) :
    forall (s : S) (r : B * S),
      (exists a smid, R s (a, smid) /\ K a smid r)
      <-> (exists a smid, R' s (a, smid) /\ K' a smid r).
  Proof.
    intros s r. split; intros [a [smid [H1 H2]]]; exists a, smid.
    - split; [ exact (proj1 (HR s _) H1) | exact (proj1 (HK a smid r) H2) ].
    - split; [ exact (proj2 (HR s _) H1) | exact (proj2 (HK a smid r) H2) ].
  Qed.

  Lemma comp_ret_l {A B} (v : A) (K : A -> S -> (B * S) -> Prop)
    (s : S) (r : B * S) :
    (exists a smid, (a, smid) = (v, s) /\ K a smid r) <-> K v s r.
  Proof.
    split.
    - intros [a [smid [Heq Hk]]].
      assert (Ha : a = v) by congruence. assert (Hs : smid = s) by congruence.
      subst a. subst smid. exact Hk.
    - intro Hk. exists v, s. split; [ reflexivity | exact Hk ].
  Qed.

  Lemma comp_ret_r {A} (R : S -> (A * S) -> Prop) (s : S) (r : A * S) :
    (exists a smid, R s (a, smid) /\ r = (a, smid)) <-> R s r.
  Proof.
    split.
    - intros [a [smid [HR Heq]]]. subst r. exact HR.
    - intro HR. destruct r as [a smid]. exists a, smid.
      split; [ exact HR | reflexivity ].
  Qed.

  Lemma comp_assoc {A B C} (R : S -> (A * S) -> Prop)
    (F : A -> S -> (B * S) -> Prop) (G : B -> S -> (C * S) -> Prop)
    (s : S) (r : C * S) :
    (exists b s2, (exists a s1, R s (a, s1) /\ F a s1 (b, s2)) /\ G b s2 r)
    <-> (exists a s1, R s (a, s1) /\ (exists b s2, F a s1 (b, s2) /\ G b s2 r)).
  Proof.
    split.
    - intros [b [s2 [[a [s1 [HR HF]]] HG]]].
      exists a, s1. split; [ exact HR |].
      exists b, s2. split; [ exact HF | exact HG ].
    - intros [a [s1 [HR [b [s2 [HF HG]]]]]].
      exists b, s2. split; [| exact HG ].
      exists a, s1. split; [ exact HR | exact HF ].
  Qed.

  (** ** [ret], the two projections, and [bind] *)

  #[program] Definition retDSPProg {A} (a : A) : DSPProgSP A :=
    fun pre r => (retASPProg a pre r) /\ (retDSLPProg a pre r).
  Next Obligation. exact (dsp_shape_wf (fun s r => r = (a, s))). Qed.

  Lemma aspPartdsp_closed {A} (w : DSPProgSP A) pre r :
    (getProgDSP w (fun _ => True) r /\ ~ getProgDSP w (fun s => ~ pre s) r)
    <-> (exists s, pre s /\ (getProgDSP w (fun _ => True) r
                             /\ ~ getProgDSP w (fun t => t <> s) r)).
  Proof.
    split.
    - intros [Htop Hn]. apply NNPP. intro Hno. apply Hn.
      apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split.
      + exists s0. split; [| exact Hr0 ].
        intro Hp. exact (Hno (ex_intro _ s0 (conj Hp Hr0))).
      + intros s Hs Hp. exact (Hno (ex_intro _ s (conj Hp Hs))).
    - intros [s [Hp Hs]]. split.
      + apply getProgDSP_carrier. split;
          [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
      + intro Hc.
        exact (proj2 (proj1 (getProgDSP_carrier w (fun t => ~ pre t) r) Hc) s Hs Hp).
  Qed.

  Lemma dslpPartdsp_closed {A} (w : DSPProgSP A) pre r :
    (getProgDSP w (fun _ => True) r -> getProgDSP w pre r)
    <-> (forall s, (getProgDSP w (fun _ => True) r
                    /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s).
  Proof.
    split.
    - intros H s Hs. refine (proj2 (proj1 (getProgDSP_carrier w pre r) (H _)) s Hs).
      apply getProgDSP_carrier. split;
        [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
    - intros Hall Htop. apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split; [ exists s0; split; [ exact (Hall s0 Hr0) | exact Hr0 ] | exact Hall ].
  Qed.

  Lemma singletonProg_ext {A} (w1 w2 : @ProgSP S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
  Qed.

  Lemma dsp_healthy_ext {A} (w1 w2 : @ProgSP S A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    StrictPositivelyMeetPreservingProg w1 -> StrictPositivelyMeetPreservingProg w2.
  Proof.
    intros Hext [HS HC]. split.
    - intros r Hc. exact (HS r (proj2 (Hext _ r) Hc)).
    - intros I i0 p r. split.
      + intros Hw i. apply Hext.
        exact (proj1 (HC I i0 p r) (proj2 (Hext _ r) Hw) i).
      + intro Hall. apply Hext. apply (HC I i0 p r).
        intro i. exact (proj2 (Hext _ r) (Hall i)).
  Qed.

  #[program] Definition aspPartdsp {A} (w : DSPProgSP A) : ASPProgSP S A :=
    fun pre r => getProgDSP w (fun _ => True) r /\ ~ getProgDSP w (fun s => ~ pre s) r.
  Next Obligation.
    apply (singletonProg_ext
             (fun pre r => exists s, pre s /\ (getProgDSP w (fun _ => True) r
                                               /\ ~ getProgDSP w (fun t => t <> s) r))).
    - intros pre r. exact (iff_sym (aspPartdsp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartdsp {A} (w : DSPProgSP A) : DSLPProgSP S A :=
    fun pre r => getProgDSP w (fun _ => True) r -> getProgDSP w pre r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (getProgDSP w (fun _ => True) r
                                      /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartdsp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem dsp_split {A} (w : DSPProgSP A) pre r :
    getProgDSP w pre r
    <-> (getProgASP (aspPartdsp w) pre r /\ getProgDSLP (dslpPartdsp w) pre r).
  Proof.
    refine (iff_trans (getProgDSP_carrier w pre r) _). split.
    - intros [He Hall]. split.
      + exact (proj2 (aspPartdsp_closed w pre r) He).
      + exact (proj2 (dslpPartdsp_closed w pre r) Hall).
    - intros [Ha Hd]. split.
      + exact (proj1 (aspPartdsp_closed w pre r) Ha).
      + exact (proj1 (dslpPartdsp_closed w pre r) Hd).
  Qed.

  Lemma bind_asp_parts {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgASP (bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a))) pre r
    <-> (exists s, pre s /\
           (exists a smid,
               (getProgDSP m (fun _ => True) (a, smid)
                /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
               /\ (getProgDSP (k a) (fun _ => True) r
                   /\ ~ getProgDSP (k a) (fun t => t <> smid) r))).
  Proof.
    split.
    - intros [a Hk].
      destruct (proj1 (aspPartdsp_closed (k a)
                         (fun s0 => getProgASP (aspPartdsp m) pre (a, s0)) r) Hk)
        as [smid [Hp Hrk]].
      destruct (proj1 (aspPartdsp_closed m pre (a, smid)) Hp) as [s [Hps Hrm]].
      exists s. split; [ exact Hps |]. exists a, smid.
      split; [ exact Hrm | exact Hrk ].
    - intros [s [Hps [a [smid [Hrm Hrk]]]]].
      exists a.
      exact (proj2 (aspPartdsp_closed (k a)
                      (fun s0 => getProgASP (aspPartdsp m) pre (a, s0)) r)
               (ex_intro _ smid
                  (conj (proj2 (aspPartdsp_closed m pre (a, smid))
                           (ex_intro _ s (conj Hps Hrm))) Hrk))).
  Qed.

  Lemma bind_dslp_parts {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgDSLP (bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a))) pre r
    <-> (forall s,
           (exists a smid,
               (getProgDSP m (fun _ => True) (a, smid)
                /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
               /\ (getProgDSP (k a) (fun _ => True) r
                   /\ ~ getProgDSP (k a) (fun t => t <> smid) r)) -> pre s).
  Proof.
    split.
    - intros H s [a [smid [Hrm Hrk]]].
      exact (proj1 (dslpPartdsp_closed m pre (a, smid))
               (proj1 (dslpPartdsp_closed (k a)
                         (fun s0 => getProgDSLP (dslpPartdsp m) pre (a, s0)) r)
                  (H a) smid Hrk) s Hrm).
    - intros H a.
      exact (proj2 (dslpPartdsp_closed (k a)
                      (fun s0 => getProgDSLP (dslpPartdsp m) pre (a, s0)) r)
               (fun smid Hrk =>
                  proj2 (dslpPartdsp_closed m pre (a, smid))
                    (fun s Hrm => H s (ex_intro _ a (ex_intro _ smid (conj Hrm Hrk))))))
      .
  Qed.

  #[program] Definition bindDSPProg {A B}
    (m : DSPProgSP A) (k : A -> DSPProgSP B) : DSPProgSP B :=
    fun pre r => bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a)) pre r /\
                   bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a)) pre r.
  Next Obligation.
    apply (dsp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists a smid,
                       (getProgDSP m (fun _ => True) (a, smid)
                        /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
                       /\ (getProgDSP (k a) (fun _ => True) r
                           /\ ~ getProgDSP (k a) (fun t => t <> smid) r)))
                /\ (forall s,
                      (exists a smid,
                          (getProgDSP m (fun _ => True) (a, smid)
                           /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
                          /\ (getProgDSP (k a) (fun _ => True) r
                              /\ ~ getProgDSP (k a) (fun t => t <> smid) r)) -> pre s))).
    - intros pre r. split.
      + intros [He Hall]. split;
          [ exact (proj2 (bind_asp_parts m k pre r) He)
          | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
      + intros [Ha Hd]. split;
          [ exact (proj1 (bind_asp_parts m k pre r) Ha)
          | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - apply dsp_shape_wf.
  Qed.

  Lemma bindDSPProg_dsp {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgDSP (bindDSPProg m k) pre r
    <-> ((exists s, pre s /\
            (exists a smid,
                (getProgDSP m (fun _ => True) (a, smid)
                 /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
                /\ (getProgDSP (k a) (fun _ => True) r
                    /\ ~ getProgDSP (k a) (fun t => t <> smid) r)))
         /\ (forall s,
               (exists a smid,
                   (getProgDSP m (fun _ => True) (a, smid)
                    /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
                   /\ (getProgDSP (k a) (fun _ => True) r
                       /\ ~ getProgDSP (k a) (fun t => t <> smid) r)) -> pre s)).
  Proof.
    split.
    - intros [Ha Hd]. split;
        [ exact (proj1 (bind_asp_parts m k pre r) Ha)
        | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - intros [He Hall]. split;
        [ exact (proj2 (bind_asp_parts m k pre r) He)
        | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
  Qed.

  Lemma rec_retDSPProg {A} (a : A) (s : S) (r : A * S) :
    (getProgDSP (retDSPProg a) (fun _ => True) r
     /\ ~ getProgDSP (retDSPProg a) (fun t => t <> s) r)
    <-> r = (a, s).
  Proof. exact (dsp_recov (fun s0 r0 => r0 = (a, s0)) s r). Qed.

  Lemma rec_bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B)
    (s : S) (r : B * S) :
    (getProgDSP (bindDSPProg m k) (fun _ => True) r
     /\ ~ getProgDSP (bindDSPProg m k) (fun t => t <> s) r)
    <-> (exists a smid,
            (getProgDSP m (fun _ => True) (a, smid)
             /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
            /\ (getProgDSP (k a) (fun _ => True) r
                /\ ~ getProgDSP (k a) (fun t => t <> smid) r)).
  Proof.
    refine (iff_trans (dsp_rec_ext _ _ (bindDSPProg_dsp m k) s r)
              (dsp_recov
                 (fun s0 r0 =>
                    exists a smid,
                      (getProgDSP m (fun _ => True) (a, smid)
                       /\ ~ getProgDSP m (fun t => t <> s0) (a, smid))
                      /\ (getProgDSP (k a) (fun _ => True) r0
                          /\ ~ getProgDSP (k a) (fun t => t <> smid) r0))
                 s r)).
  Qed.

  #[global] Instance Monad__DSPProgSP : Monad DSPProgSP :=
    {| ret := fun _ => @retDSPProg _ ;
       bind := fun _ _ => @bindDSPProg _ _ |}.

  #[global] Instance Eq1__ProgDSP : Eq1 DSPProgSP :=
    fun A m n => forall pre r, getProgDSP m pre r <-> getProgDSP n pre r.

  #[global] Instance Eq1Equivalence__DSPProgSP
    : @Eq1Equivalence DSPProgSP _ Eq1__ProgDSP.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLaws__ProgDSP
    : @MonadLawsE DSPProgSP Eq1__ProgDSP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (getProgDSP (retDSPProg x) (fun _ => True) (a, smid)
                      /\ ~ getProgDSP (retDSPProg x) (fun t => t <> s) (a, smid))
                     /\ (getProgDSP (f a) (fun _ => True) r0
                         /\ ~ getProgDSP (f a) (fun t => t <> smid) r0))
                 <-> (getProgDSP (f x) (fun _ => True) r0
                      /\ ~ getProgDSP (f x) (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP (retDSPProg x) (fun _ => True) r1
                                  /\ ~ getProgDSP (retDSPProg x) (fun t => t <> s1) r1)
                    (fun s1 r1 => r1 = (x, s1))
                    (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_retDSPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l x
                    (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp (retDSPProg x) f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier (f x) pre r)))).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : A * S),
                 (exists a smid,
                     (getProgDSP m (fun _ => True) (a, smid)
                      /\ ~ getProgDSP m (fun t => t <> s) (a, smid))
                     /\ (getProgDSP (retDSPProg a) (fun _ => True) r0
                         /\ ~ getProgDSP (retDSPProg a) (fun t => t <> smid) r0))
                 <-> (getProgDSP m (fun _ => True) r0
                      /\ ~ getProgDSP m (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getProgDSP (retDSPProg a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (retDSPProg a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => r1 = (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retDSPProg a1 s1 r1) s r0)
                 (comp_ret_r
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp m _ pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier m pre r)))).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : C * S),
                 (exists b smid,
                     (getProgDSP (bindDSPProg x f) (fun _ => True) (b, smid)
                      /\ ~ getProgDSP (bindDSPProg x f) (fun t => t <> s) (b, smid))
                     /\ (getProgDSP (g b) (fun _ => True) r0
                         /\ ~ getProgDSP (g b) (fun t => t <> smid) r0))
                 <-> (exists a smid,
                         (getProgDSP x (fun _ => True) (a, smid)
                          /\ ~ getProgDSP x (fun t => t <> s) (a, smid))
                         /\ (getProgDSP (bindDSPProg (f a) g) (fun _ => True) r0
                             /\ ~ getProgDSP (bindDSPProg (f a) g)
                                    (fun t => t <> smid) r0))).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP (bindDSPProg x f) (fun _ => True) r1
                                  /\ ~ getProgDSP (bindDSPProg x f) (fun t => t <> s1) r1)
                    (fun s1 r1 =>
                       exists a smid,
                         (getProgDSP x (fun _ => True) (a, smid)
                          /\ ~ getProgDSP x (fun t => t <> s1) (a, smid))
                         /\ (getProgDSP (f a) (fun _ => True) r1
                             /\ ~ getProgDSP (f a) (fun t => t <> smid) r1))
                    (fun b1 s1 r1 => getProgDSP (g b1) (fun _ => True) r1
                                     /\ ~ getProgDSP (g b1) (fun t => t <> s1) r1)
                    (fun b1 s1 r1 => getProgDSP (g b1) (fun _ => True) r1
                                     /\ ~ getProgDSP (g b1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_bindDSPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc
                       (fun s1 r1 => getProgDSP x (fun _ => True) r1
                                     /\ ~ getProgDSP x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                        /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                       (fun b1 s1 r1 => getProgDSP (g b1) (fun _ => True) r1
                                        /\ ~ getProgDSP (g b1) (fun t => t <> s1) r1)
                       s r0)
                    (comp_cong
                       (fun s1 r1 => getProgDSP x (fun _ => True) r1
                                     /\ ~ getProgDSP x (fun t => t <> s1) r1)
                       (fun s1 r1 => getProgDSP x (fun _ => True) r1
                                     /\ ~ getProgDSP x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 =>
                          exists b smid,
                            (getProgDSP (f a1) (fun _ => True) (b, smid)
                             /\ ~ getProgDSP (f a1) (fun t => t <> s1) (b, smid))
                            /\ (getProgDSP (g b) (fun _ => True) r1
                                /\ ~ getProgDSP (g b) (fun t => t <> smid) r1))
                       (fun a1 s1 r1 =>
                          getProgDSP (bindDSPProg (f a1) g) (fun _ => True) r1
                          /\ ~ getProgDSP (bindDSPProg (f a1) g) (fun t => t <> s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindDSPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindDSPProg_dsp (bindDSPProg x f) g pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp x (fun a => bindDSPProg (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgDSP in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (getProgDSP x (fun _ => True) (a, smid)
                      /\ ~ getProgDSP x (fun t => t <> s) (a, smid))
                     /\ (getProgDSP (f a) (fun _ => True) r0
                         /\ ~ getProgDSP (f a) (fun t => t <> smid) r0))
                 <-> (exists a smid,
                         (getProgDSP y (fun _ => True) (a, smid)
                          /\ ~ getProgDSP y (fun t => t <> s) (a, smid))
                         /\ (getProgDSP (g a) (fun _ => True) r0
                             /\ ~ getProgDSP (g a) (fun t => t <> smid) r0))).
      { intros s r0.
        exact (comp_cong
                 (fun s1 r1 => getProgDSP x (fun _ => True) r1
                               /\ ~ getProgDSP x (fun t => t <> s1) r1)
                 (fun s1 r1 => getProgDSP y (fun _ => True) r1
                               /\ ~ getProgDSP y (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                  /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getProgDSP (g a1) (fun _ => True) r1
                                  /\ ~ getProgDSP (g a1) (fun t => t <> s1) r1)
                 (fun s1 r1 => dsp_rec_ext (getProgDSP x) (getProgDSP y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    dsp_rec_ext (getProgDSP (f a1)) (getProgDSP (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindDSPProg_dsp x f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp y g pre r)))).
  Qed.

End ProgDSPMonad.

Arguments retDSPProg {_} {_}.
Arguments bindDSPProg {_} {_} {_}.
Arguments getProgDSP {_} {_}.

(* ==================================================================== *)
(** * The angelic-liberal monad                                          *)
(* ==================================================================== *)

Section ProgASLPMonad.
  Variable S : Type.

  Definition TerminatingPositivelyJoinPreserving {A} (w : ProgSP A) : Prop :=
    TerminatingProg S w /\ DisjunctiveProg S w.

  Definition ASLPProgSP (A : Type) : Type :=
    { w : ProgSP A | TerminatingPositivelyJoinPreserving w }.

  Definition getProgASLP {A} (w : ASLPProgSP A) : ProgSP A := proj1_sig w.

  Lemma aslp_recov {A} (R : S -> (A * S) -> Prop)
    (s : S) (r : (A * S)) :
    (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
     /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
    <-> R s r.
  Proof.
    split.
    - intros [Hne [[t [Heq Ht]] | Hall]]; [ subst t; exact Ht |].
      apply NNPP. intro Hns. apply Hne. right.
      intros t Ht. rewrite (Hall t Ht) in Ht. exact (Hns Ht).
    - intro Hs. split.
      + intros [[t [Hf _]] | Hall]; [ destruct Hf | exact (Hall s Hs) ].
      + left. exists s. split; [ reflexivity | exact Hs ].
  Qed.

  Lemma aslp_wf {A} (R : S -> (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\
              (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
               /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s))))
           \/ (forall s,
                 (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
                  /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
                 -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj2 (aslp_recov R s r) Hs) ].
      + right. intros s H. exact (Hall s (proj1 (aslp_recov R s r) H)).
    - intros [[s [Hp H]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj1 (aslp_recov R s r) H) ].
      + right. intros s Hs. exact (Hall s (proj2 (aslp_recov R s r) Hs)).
  Qed.

  Lemma aslp_cong {A} (R R' : S -> (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\ R' s r) \/ (forall s, R' s r -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj1 (H s r) Hs) ].
      + right. intros s Hs. exact (Hall s (proj2 (H s r) Hs)).
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj2 (H s r) Hs) ].
      + right. intros s Hs. exact (Hall s (proj1 (H s r) Hs)).
  Qed.

  Lemma aslp_rec_ext {A} (w1 w2 : @ProgSP S A)
    (H : forall pre r, w1 pre r <-> w2 pre r) :
    forall (s : S) (r : (A * S)),
      (~ w1 (fun _ => False) r /\ w1 (fun t => t = s) r)
      <-> (~ w2 (fun _ => False) r /\ w2 (fun t => t = s) r).
  Proof.
    intros s r. split.
    - intros [H1 H2]. split;
        [ intro Hc; exact (H1 (proj2 (H _ r) Hc)) | exact (proj1 (H _ r) H2) ].
    - intros [H1 H2]. split;
        [ intro Hc; exact (H1 (proj1 (H _ r) Hc)) | exact (proj2 (H _ r) H2) ].
  Qed.

  (** Dual of [dsp_carrier]: the healthiness condition that the type states is
      the same thing as "[w] is the ASLP of its own recovered relation", which
      is what the proofs use. *)
  Lemma aslp_carrier {A} (w : ProgSP A) :
    TerminatingPositivelyJoinPreserving w <->
      (forall (pre : S -> Prop) (r : (A * S)), w pre r <->
      ((exists s, pre s /\ (~ w (fun _ => False) r /\ w (fun t => t = s) r)) \/
         (forall s, (~ w (fun _ => False) r /\ w (fun t => t = s) r) -> pre s))).
  Proof.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    split.
    - intros [HT HD] pre r.
      (* the join of the two-element family [{P, Q}] is [Q] when [P <= Q] *)
      assert (Hmono : forall (P Q : S -> Prop) y,
                 (forall s, P s -> Q s) -> w P y -> w Q y).
      { intros P Q y Hpq Hw.
        assert (Heq : Q = (fun s => exists b : bool, (if b then P else Q) s)).
        { apply Hext. intro s. split.
          - intro Hs. exists false. exact Hs.
          - intros [b Hb]. destruct b; [ exact (Hpq s Hb) | exact Hb ]. }
        rewrite Heq.
        apply (HD bool (inhabits true) (fun b => if b then P else Q) y).
        exists true. exact Hw. }
      destruct (classic (w (fun _ => False) r)) as [Hbot | Hnbot].
      + split.
        * intros _. right. intros s [Hn _]. destruct (Hn Hbot).
        * intros _. apply (Hmono (fun _ => False) pre r); [ intros s [] | exact Hbot ].
      + (* [S] is inhabited, else top and bottom coincide *)
        assert (Hinh : exists s0 : S, True).
        { apply NNPP. intro Hno. apply Hnbot.
          assert (Heq : (fun _ : S => True) = (fun _ : S => False)).
          { apply Hext. intro s. split;
              [ intros _; exact (Hno (ex_intro _ s I)) | intros [] ]. }
          pose proof (HT r) as Htop. rewrite Heq in Htop. exact Htop. }
        destruct Hinh as [sinh _].
        (* top-preservation makes some singleton already force [r] *)
        assert (Hex : exists s, w (fun t => t = s) r).
        { assert (Heq : (fun _ : S => True) = (fun s => exists s0 : S, s = s0)).
          { apply Hext. intro s. split;
              [ intros _; exists s; reflexivity | intros _; exact I ]. }
          pose proof (HT r) as Htop. rewrite Heq in Htop.
          exact (proj1 (HD S (inhabits sinh) (fun s0 s => s = s0) r) Htop). }
        (* the join of all preconditions that FAIL to force [r] *)
        pose (bad := fun s => exists i : { q : S -> Prop | ~ w q r }, proj1_sig i s).
        assert (Hbad : ~ w bad r).
        { unfold bad. intro Hc.
          destruct (proj1 (HD { q : S -> Prop | ~ w q r }
                             (inhabits (exist (fun q => ~ w q r) (fun _ : S => False) Hnbot))
                             (fun i s => proj1_sig i s) r) Hc) as [i Hi].
          exact (proj2_sig i Hi). }
        assert (Hub : forall q, ~ w q r -> forall s, q s -> bad s).
        { intros q Hq s Hs. unfold bad.
          exists (exist (fun q0 => ~ w q0 r) q Hq). exact Hs. }
        assert (Hrec : forall s, (~ w (fun _ => False) r /\ w (fun t => t = s) r)
                                 <-> ~ bad s).
        { intro s. split.
          - intros [_ Hw] Hb. unfold bad in Hb. destruct Hb as [i Hi].
            apply (proj2_sig i).
            apply (Hmono (fun t => t = s) (proj1_sig i) r);
              [ intros t Ht; rewrite Ht; exact Hi | exact Hw ].
          - intro Hnb. split; [ exact Hnbot |].
            apply NNPP. intro Hnw.
            exact (Hnb (Hub (fun t => t = s) Hnw s eq_refl)). }
        assert (Hmain : w pre r <-> exists s, pre s /\ ~ bad s).
        { split.
          - intro Hw. apply NNPP. intro Hno. apply Hbad.
            apply (Hmono pre bad r); [| exact Hw ].
            intros s Hs. apply NNPP. intro Hnb.
            exact (Hno (ex_intro _ s (conj Hs Hnb))).
          - intros [s [Hs Hnb]]. apply NNPP. intro Hnw.
            exact (Hnb (Hub pre Hnw s Hs)). }
        split.
        * intro Hw. left. destruct (proj1 Hmain Hw) as [s [Hs Hnb]].
          exists s. split; [ exact Hs | exact (proj2 (Hrec s) Hnb) ].
        * intros [[s [Hs Hr']] | Hall].
          -- apply Hmain. exists s.
             split; [ exact Hs | exact (proj1 (Hrec s) Hr') ].
          -- destruct Hex as [s0 Hs0]. apply Hmain. exists s0.
             split; [ exact (Hall s0 (conj Hnbot Hs0))
                    | exact (proj1 (Hrec s0) (conj Hnbot Hs0)) ].
    - intro HD. split.
      + intro r. apply (HD (fun _ => True) r). right. intros s _. exact I.
      + intros J Hi0 p r. destruct Hi0 as [i0]. split.
        * intro Hw. destruct (proj1 (HD (fun s => exists i : J, p i s) r) Hw)
            as [[s [[i Hpi] Hrec]] | Hall].
          -- exists i. apply (HD (fun s0 => p i s0) r). left.
             exists s. split; [ exact Hpi | exact Hrec ].
          -- destruct (classic (exists s, ~ w (fun _ => False) r
                                          /\ w (fun t => t = s) r)) as [[s0 Hs0] | Hno].
             ++ destruct (Hall s0 Hs0) as [i Hpi].
                exists i. apply (HD (fun s0' => p i s0') r). left.
                exists s0. split; [ exact Hpi | exact Hs0 ].
             ++ exists i0. apply (HD (fun s0 => p i0 s0) r). right.
                intros s Hrec. exfalso. exact (Hno (ex_intro _ s Hrec)).
        * intros [i Hw]. apply (HD (fun s => exists j : J, p j s) r).
          destruct (proj1 (HD (fun s0 => p i s0) r) Hw) as [[s [Hpi Hrec]] | Hall].
          -- left. exists s. split; [ exists i; exact Hpi | exact Hrec ].
          -- right. intros s Hrec. exists i. exact (Hall s Hrec).
  Qed.

  Lemma aslp_shape_wf {A} (R : S -> (A * S) -> Prop) :
    TerminatingPositivelyJoinPreserving
      (fun pre r => (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s)).
  Proof. apply aslp_carrier. intros pre r. exact (aslp_wf R pre r). Qed.

  Lemma getProgASLP_carrier {A} (w : ASLPProgSP A) (pre : S -> Prop) (r : A * S) :
    getProgASLP w pre r <->
      ((exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                            /\ getProgASLP w (fun t => t = s) r)) \/
         (forall s, (~ getProgASLP w (fun _ => False) r
                     /\ getProgASLP w (fun t => t = s) r) -> pre s)).
  Proof. exact (proj1 (aslp_carrier (getProgASLP w)) (proj2_sig w) pre r). Qed.

  (** ** [ret], the two projections, and [bind] *)

  #[program] Definition retASLPProg {A} (a : A) : ASLPProgSP A :=
    fun pre r => (retASPProg a pre r) \/ (retDSLPProg a pre r).
  Next Obligation. exact (aslp_shape_wf (fun s r => r = (a, s))). Qed.

  Lemma aspPartaslp_closed {A} (w : ASLPProgSP A) pre r :
    (~ getProgASLP w (fun _ => False) r /\ getProgASLP w pre r)
    <-> (exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                             /\ getProgASLP w (fun t => t = s) r)).
  Proof.
    split.
    - intros [Hn Hw]. destruct (proj1 (getProgASLP_carrier w pre r) Hw) as [He | Hall];
        [ exact He |].
      apply NNPP. intro Hno. apply Hn. apply getProgASLP_carrier. right.
      intros s Hs. exfalso. exact (Hno (ex_intro _ s (conj (Hall s Hs) Hs))).
    - intros [s [Hp Hs]]. split.
      + intro Hc. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hc)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply getProgASLP_carrier. left. exists s. split; [ exact Hp | exact Hs ].
  Qed.

  Lemma dslpPartaslp_closed {A} (w : ASLPProgSP A) pre r :
    (getProgASLP w (fun _ => False) r \/ ~ getProgASLP w (fun s => ~ pre s) r)
    <-> (forall s, (~ getProgASLP w (fun _ => False) r
                    /\ getProgASLP w (fun t => t = s) r) -> pre s).
  Proof.
    split.
    - intros [Hbot | Hn] s Hs.
      + exfalso. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hbot)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply NNPP. intro Hnp. apply Hn. apply getProgASLP_carrier. left.
        exists s. split; [ exact Hnp | exact Hs ].
    - intro Hall.
      destruct (classic (exists s, ~ getProgASLP w (fun _ => False) r
                                   /\ getProgASLP w (fun t => t = s) r))
        as [[s0 Hs0] | Hno].
      + right. intro Hc.
        destruct (proj1 (getProgASLP_carrier w (fun t => ~ pre t) r) Hc)
          as [[s [Hnp Hs]] | Hev].
        * exact (Hnp (Hall s Hs)).
        * exact (Hev s0 Hs0 (Hall s0 Hs0)).
      + left. apply getProgASLP_carrier. right. intros s Hs.
        exfalso. exact (Hno (ex_intro _ s Hs)).
  Qed.

  Lemma aslp_healthy_ext {A} (w1 w2 : @ProgSP S A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    TerminatingPositivelyJoinPreserving w1 -> TerminatingPositivelyJoinPreserving w2.
  Proof.
    intros Hext [HT HD]. split.
    - intro r. apply Hext. exact (HT r).
    - intros I i0 p r. split.
      + intro Hw. destruct (proj1 (HD I i0 p r) (proj2 (Hext _ r) Hw)) as [i Hi].
        exists i. apply Hext. exact Hi.
      + intros [i Hi]. apply Hext. apply (HD I i0 p r).
        exists i. exact (proj2 (Hext _ r) Hi).
  Qed.

  #[program] Definition aspPartaslp {A} (w : ASLPProgSP A) : ASPProgSP S A :=
    fun pre r => ~ getProgASLP w (fun _ => False) r /\ getProgASLP w pre r.
  Next Obligation.
    apply (singletonProg_ext S
             (fun pre r => exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                                               /\ getProgASLP w (fun t => t = s) r))).
    - intros pre r. exact (iff_sym (aspPartaslp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartaslp {A} (w : ASLPProgSP A) : DSLPProgSP S A :=
    fun pre r => getProgASLP w (fun _ => False) r \/ ~ getProgASLP w (fun s => ~ pre s) r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (~ getProgASLP w (fun _ => False) r
                                      /\ getProgASLP w (fun t => t = s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartaslp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem aslp_split {A} (w : ASLPProgSP A) pre r :
    getProgASLP w pre r
    <-> (getProgASP (aspPartaslp w) pre r \/ getProgDSLP (dslpPartaslp w) pre r).
  Proof.
    refine (iff_trans (getProgASLP_carrier w pre r) _). split.
    - intros [He | Hall].
      + left. exact (proj2 (aspPartaslp_closed w pre r) He).
      + right. exact (proj2 (dslpPartaslp_closed w pre r) Hall).
    - intros [Ha | Hd].
      + left. exact (proj1 (aspPartaslp_closed w pre r) Ha).
      + right. exact (proj1 (dslpPartaslp_closed w pre r) Hd).
  Qed.

  Lemma bind_asp_parts' {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgASP (bindASPProg (aspPartaslp m) (fun a => aspPartaslp (k a))) pre r
    <-> (exists s, pre s /\
           (exists a smid,
               (~ getProgASLP m (fun _ => False) (a, smid)
                /\ getProgASLP m (fun t => t = s) (a, smid))
               /\ (~ getProgASLP (k a) (fun _ => False) r
                   /\ getProgASLP (k a) (fun t => t = smid) r))).
  Proof.
    split.
    - intros [a Hk].
      destruct (proj1 (aspPartaslp_closed (k a)
                         (fun s0 => getProgASP (aspPartaslp m) pre (a, s0)) r) Hk)
        as [smid [Hp Hrk]].
      destruct (proj1 (aspPartaslp_closed m pre (a, smid)) Hp) as [s [Hps Hrm]].
      exists s. split; [ exact Hps |]. exists a, smid.
      split; [ exact Hrm | exact Hrk ].
    - intros [s [Hps [a [smid [Hrm Hrk]]]]].
      exists a.
      exact (proj2 (aspPartaslp_closed (k a)
                      (fun s0 => getProgASP (aspPartaslp m) pre (a, s0)) r)
               (ex_intro _ smid
                  (conj (proj2 (aspPartaslp_closed m pre (a, smid))
                           (ex_intro _ s (conj Hps Hrm))) Hrk))).
  Qed.

  Lemma bind_dslp_parts' {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgDSLP (bindDSLPProg (dslpPartaslp m) (fun a => dslpPartaslp (k a))) pre r
    <-> (forall s,
           (exists a smid,
               (~ getProgASLP m (fun _ => False) (a, smid)
                /\ getProgASLP m (fun t => t = s) (a, smid))
               /\ (~ getProgASLP (k a) (fun _ => False) r
                   /\ getProgASLP (k a) (fun t => t = smid) r)) -> pre s).
  Proof.
    split.
    - intros H s [a [smid [Hrm Hrk]]].
      exact (proj1 (dslpPartaslp_closed m pre (a, smid))
               (proj1 (dslpPartaslp_closed (k a)
                         (fun s0 => getProgDSLP (dslpPartaslp m) pre (a, s0)) r)
                  (H a) smid Hrk) s Hrm).
    - intros H a.
      exact (proj2 (dslpPartaslp_closed (k a)
                      (fun s0 => getProgDSLP (dslpPartaslp m) pre (a, s0)) r)
               (fun smid Hrk =>
                  proj2 (dslpPartaslp_closed m pre (a, smid))
                    (fun s Hrm => H s (ex_intro _ a (ex_intro _ smid (conj Hrm Hrk)))))).
  Qed.

  #[program] Definition bindASLPProg {A B}
    (m : ASLPProgSP A) (k : A -> ASLPProgSP B) : ASLPProgSP B :=
    fun pre r => bindASPProg (aspPartaslp m) (fun a => aspPartaslp (k a)) pre r \/
                   bindDSLPProg (dslpPartaslp m) (fun a => dslpPartaslp (k a)) pre r.
  Next Obligation.
    apply (aslp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists a smid,
                       (~ getProgASLP m (fun _ => False) (a, smid)
                        /\ getProgASLP m (fun t => t = s) (a, smid))
                       /\ (~ getProgASLP (k a) (fun _ => False) r
                           /\ getProgASLP (k a) (fun t => t = smid) r)))
                \/ (forall s,
                      (exists a smid,
                          (~ getProgASLP m (fun _ => False) (a, smid)
                           /\ getProgASLP m (fun t => t = s) (a, smid))
                          /\ (~ getProgASLP (k a) (fun _ => False) r
                              /\ getProgASLP (k a) (fun t => t = smid) r)) -> pre s))).
    - intros pre r. split.
      + intros [He | Hall];
          [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
          | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
      + intros [Ha | Hd];
          [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
          | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - apply aslp_shape_wf.
  Qed.

  Lemma bindASLPProg_aslp {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgASLP (bindASLPProg m k) pre r
    <-> ((exists s, pre s /\
            (exists a smid,
                (~ getProgASLP m (fun _ => False) (a, smid)
                 /\ getProgASLP m (fun t => t = s) (a, smid))
                /\ (~ getProgASLP (k a) (fun _ => False) r
                    /\ getProgASLP (k a) (fun t => t = smid) r)))
         \/ (forall s,
               (exists a smid,
                   (~ getProgASLP m (fun _ => False) (a, smid)
                    /\ getProgASLP m (fun t => t = s) (a, smid))
                   /\ (~ getProgASLP (k a) (fun _ => False) r
                       /\ getProgASLP (k a) (fun t => t = smid) r)) -> pre s)).
  Proof.
    split.
    - intros [Ha | Hd];
        [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
        | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - intros [He | Hall];
        [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
        | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
  Qed.

  Lemma rec_retASLPProg {A} (a : A) (s : S) (r : A * S) :
    (~ getProgASLP (retASLPProg a) (fun _ => False) r
     /\ getProgASLP (retASLPProg a) (fun t => t = s) r)
    <-> r = (a, s).
  Proof. exact (aslp_recov (fun s0 r0 => r0 = (a, s0)) s r). Qed.

  Lemma rec_bindASLPProg {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B)
    (s : S) (r : B * S) :
    (~ getProgASLP (bindASLPProg m k) (fun _ => False) r
     /\ getProgASLP (bindASLPProg m k) (fun t => t = s) r)
    <-> (exists a smid,
            (~ getProgASLP m (fun _ => False) (a, smid)
             /\ getProgASLP m (fun t => t = s) (a, smid))
            /\ (~ getProgASLP (k a) (fun _ => False) r
                /\ getProgASLP (k a) (fun t => t = smid) r)).
  Proof.
    refine (iff_trans (aslp_rec_ext _ _ (bindASLPProg_aslp m k) s r)
              (aslp_recov
                 (fun s0 r0 =>
                    exists a smid,
                      (~ getProgASLP m (fun _ => False) (a, smid)
                       /\ getProgASLP m (fun t => t = s0) (a, smid))
                      /\ (~ getProgASLP (k a) (fun _ => False) r0
                          /\ getProgASLP (k a) (fun t => t = smid) r0))
                 s r)).
  Qed.

  #[global] Instance Monad__ASLPProgSP : Monad ASLPProgSP :=
    {| ret := fun _ => @retASLPProg _ ;
       bind := fun _ _ => @bindASLPProg _ _ |}.

  #[global] Instance Eq1__ProgASLP : Eq1 ASLPProgSP :=
    fun A m n => forall pre r, getProgASLP m pre r <-> getProgASLP n pre r.

  #[global] Instance Eq1Equivalence__ASLPProgSP
    : @Eq1Equivalence ASLPProgSP _ Eq1__ProgASLP.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLaws__ProgASLP
    : @MonadLawsE ASLPProgSP Eq1__ProgASLP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ProgASLP. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (~ getProgASLP (retASLPProg x) (fun _ => False) (a, smid)
                      /\ getProgASLP (retASLPProg x) (fun t => t = s) (a, smid))
                     /\ (~ getProgASLP (f a) (fun _ => False) r0
                         /\ getProgASLP (f a) (fun t => t = smid) r0))
                 <-> (~ getProgASLP (f x) (fun _ => False) r0
                      /\ getProgASLP (f x) (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP (retASLPProg x) (fun _ => False) r1
                                  /\ getProgASLP (retASLPProg x) (fun t => t = s1) r1)
                    (fun s1 r1 => r1 = (x, s1))
                    (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                     /\ getProgASLP (f a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                     /\ getProgASLP (f a1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_retASLPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l S x
                    (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                     /\ getProgASLP (f a1) (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp (retASLPProg x) f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier (f x) pre r)))).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ProgASLP. intros pre r.
      assert (Hc : forall (s : S) (r0 : A * S),
                 (exists a smid,
                     (~ getProgASLP m (fun _ => False) (a, smid)
                      /\ getProgASLP m (fun t => t = s) (a, smid))
                     /\ (~ getProgASLP (retASLPProg a) (fun _ => False) r0
                         /\ getProgASLP (retASLPProg a) (fun t => t = smid) r0))
                 <-> (~ getProgASLP m (fun _ => False) r0
                      /\ getProgASLP m (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP m (fun _ => False) r1
                                  /\ getProgASLP m (fun t => t = s1) r1)
                    (fun s1 r1 => ~ getProgASLP m (fun _ => False) r1
                                  /\ getProgASLP m (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getProgASLP (retASLPProg a1) (fun _ => False) r1
                                     /\ getProgASLP (retASLPProg a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => r1 = (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retASLPProg a1 s1 r1) s r0)
                 (comp_ret_r S
                    (fun s1 r1 => ~ getProgASLP m (fun _ => False) r1
                                  /\ getProgASLP m (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp m _ pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier m pre r)))).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ProgASLP. intros pre r.
      assert (Hc : forall (s : S) (r0 : C * S),
                 (exists b smid,
                     (~ getProgASLP (bindASLPProg x f) (fun _ => False) (b, smid)
                      /\ getProgASLP (bindASLPProg x f) (fun t => t = s) (b, smid))
                     /\ (~ getProgASLP (g b) (fun _ => False) r0
                         /\ getProgASLP (g b) (fun t => t = smid) r0))
                 <-> (exists a smid,
                         (~ getProgASLP x (fun _ => False) (a, smid)
                          /\ getProgASLP x (fun t => t = s) (a, smid))
                         /\ (~ getProgASLP (bindASLPProg (f a) g) (fun _ => False) r0
                             /\ getProgASLP (bindASLPProg (f a) g)
                                  (fun t => t = smid) r0))).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP (bindASLPProg x f) (fun _ => False) r1
                                  /\ getProgASLP (bindASLPProg x f) (fun t => t = s1) r1)
                    (fun s1 r1 =>
                       exists a smid,
                         (~ getProgASLP x (fun _ => False) (a, smid)
                          /\ getProgASLP x (fun t => t = s1) (a, smid))
                         /\ (~ getProgASLP (f a) (fun _ => False) r1
                             /\ getProgASLP (f a) (fun t => t = smid) r1))
                    (fun b1 s1 r1 => ~ getProgASLP (g b1) (fun _ => False) r1
                                     /\ getProgASLP (g b1) (fun t => t = s1) r1)
                    (fun b1 s1 r1 => ~ getProgASLP (g b1) (fun _ => False) r1
                                     /\ getProgASLP (g b1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_bindASLPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc S
                       (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                                     /\ getProgASLP x (fun t => t = s1) r1)
                       (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                        /\ getProgASLP (f a1) (fun t => t = s1) r1)
                       (fun b1 s1 r1 => ~ getProgASLP (g b1) (fun _ => False) r1
                                        /\ getProgASLP (g b1) (fun t => t = s1) r1)
                       s r0)
                    (comp_cong S
                       (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                                     /\ getProgASLP x (fun t => t = s1) r1)
                       (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                                     /\ getProgASLP x (fun t => t = s1) r1)
                       (fun a1 s1 r1 =>
                          exists b smid,
                            (~ getProgASLP (f a1) (fun _ => False) (b, smid)
                             /\ getProgASLP (f a1) (fun t => t = s1) (b, smid))
                            /\ (~ getProgASLP (g b) (fun _ => False) r1
                                /\ getProgASLP (g b) (fun t => t = smid) r1))
                       (fun a1 s1 r1 =>
                          ~ getProgASLP (bindASLPProg (f a1) g) (fun _ => False) r1
                          /\ getProgASLP (bindASLPProg (f a1) g) (fun t => t = s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindASLPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindASLPProg_aslp (bindASLPProg x f) g pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp x (fun a => bindASLPProg (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgASLP in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (~ getProgASLP x (fun _ => False) (a, smid)
                      /\ getProgASLP x (fun t => t = s) (a, smid))
                     /\ (~ getProgASLP (f a) (fun _ => False) r0
                         /\ getProgASLP (f a) (fun t => t = smid) r0))
                 <-> (exists a smid,
                         (~ getProgASLP y (fun _ => False) (a, smid)
                          /\ getProgASLP y (fun t => t = s) (a, smid))
                         /\ (~ getProgASLP (g a) (fun _ => False) r0
                             /\ getProgASLP (g a) (fun t => t = smid) r0))).
      { intros s r0.
        exact (comp_cong S
                 (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                               /\ getProgASLP x (fun t => t = s1) r1)
                 (fun s1 r1 => ~ getProgASLP y (fun _ => False) r1
                               /\ getProgASLP y (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                  /\ getProgASLP (f a1) (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getProgASLP (g a1) (fun _ => False) r1
                                  /\ getProgASLP (g a1) (fun t => t = s1) r1)
                 (fun s1 r1 => aslp_rec_ext (getProgASLP x) (getProgASLP y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    aslp_rec_ext (getProgASLP (f a1)) (getProgASLP (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindASLPProg_aslp x f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp y g pre r)))).
  Qed.

End ProgASLPMonad.

Arguments retASLPProg {_} {_}.
Arguments bindASLPProg {_} {_} {_}.
Arguments getProgASLP {_} {_}.
End StSP.
