From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPostMonad SPPredicateTransformers ASPMonad.

Import MonadNotation.
Open Scope monad_scope.

Section PureDSLPMonad.
  Definition MeetPreserving {A} (w : SPPure A) : Prop :=
    Terminating w /\ Conjunctive w.

  Definition MSingleton {A} (w : SPPure A) : Prop :=
    forall (p : Prop) (a : A), w p a <-> p \/ w False a.

  (** Dually to [join_to_singleton]: at [SPPure] the precondition is a [Prop],
      so [Terminating] alone already forces [MSingleton]; [Conjunctive] is not
      needed here. *)
  Lemma meet_to_msingleton {A} (w : SPPure A) :
    MeetPreserving w -> MSingleton w.
  Proof.
    intros [HT _] p a. destruct (classic p) as [Hp | Hnp].
    - assert (Heq : p = True)
        by (apply propositional_extensionality;
            split; [ intros _; exact I | intros _; exact Hp ]).
      rewrite Heq. split; [ intros _; left; exact I | intros _; exact (HT a) ].
    - assert (Heq : p = False)
        by (apply propositional_extensionality; split; [ exact Hnp | intros [] ]).
      rewrite Heq. split;
        [ intro Hw; right; exact Hw | intros [[] | Hf]; exact Hf ].
  Qed.

  Lemma msingleton_to_meet {A} (w : SPPure A) :
    MSingleton w -> MeetPreserving w.
  Proof.
    intro H. split.
    - intro a. apply H. left. exact I.
    - intros I i0 p a. split.
      + intro Hw. destruct (proj1 (H (forall i, p i) a) Hw) as [Hall | Hf].
        * intro i. apply H. left. exact (Hall i).
        * intro i. apply H. right. exact Hf.
      + intro Hall. apply H.
        destruct (classic (w False a)) as [Hf | Hnf]; [ right; exact Hf |].
        left. intro i. destruct (proj1 (H (p i) a) (Hall i)) as [Hpi | Hf];
          [ exact Hpi | destruct (Hnf Hf) ].
  Qed.

  (** Dually to [strict_to_singleton]: [meet_to_msingleton] uses only its
      [Terminating] half, so [Terminating] alone forces [MSingleton]. *)
  Lemma terminating_to_msingleton {A} (w : SPPure A) :
    Terminating w -> MSingleton w.
  Proof.
    intros HT p a. destruct (classic p) as [Hp | Hnp].
    - assert (Heq : p = True)
        by (apply propositional_extensionality;
            split; [ intros _; exact I | intros _; exact Hp ]).
      rewrite Heq. split; [ intros _; left; exact I | intros _; exact (HT a) ].
    - assert (Heq : p = False)
        by (apply propositional_extensionality; split; [ exact Hnp | intros [] ]).
      rewrite Heq. split; [ intro H; right; exact H | intros [[] | H]; exact H ].
  Qed.

  (** [MSingleton] gives the OTHER connective too. *)
  Lemma msingleton_to_disjunctive {A} (w : SPPure A) :
    MSingleton w -> Disjunctive w.
  Proof.
    intros H I i0 p a. rewrite (H (exists i, p i) a). split.
    - intros [[i Hi] | Hf].
      + exists i. apply H. left. exact Hi.
      + exists i0. apply H. right. exact Hf.
    - intros [i Hi]. destruct (proj1 (H (p i) a) Hi) as [Hp | Hf];
        [ left; exists i; exact Hp | right; exact Hf ].
  Qed.

  Theorem meet_iff_msingleton {A} (w : SPPure A) :
    MeetPreserving w <-> MSingleton w.
  Proof. split; [apply meet_to_msingleton | apply msingleton_to_meet]. Qed.

  Theorem kenjidslp_iff_msingleton {A} (w : SPPure A) :
    KenjiPureDSLP w <-> MSingleton w.
  Proof.
    split.
    - intros [Hmono Hcod] p a. split.
      + intro Hw. destruct (classic p) as [Hp | Hnp]; [left; exact Hp |].
        right. exact (Hmono p False a Hnp Hw).
      + intros [Hp | Hf];
          [ exact (Hcod p a Hp) | exact (Hmono False p a (False_ind p) Hf) ].
    - intro H. split.
      + intros p q a Hpq Hw. apply H.
        destruct (proj1 (H p a) Hw) as [Hp | Hf];
          [ left; exact (Hpq Hp) | right; exact Hf ].
      + intros p a Hp. apply H. left. exact Hp.
  Qed.

  Definition DSLPSP (A : Type) : Type := { w : SPPure A | MSingleton w }.

  Definition getDSLP {A} (w : DSLPSP A) : SPPure A := proj1_sig w.

  Lemma getMSP_singleton {A} (w : DSLPSP A) (p : Prop) (a : A) :
    getDSLP w p a <-> (p \/ getDSLP w False a).
  Proof. exact (proj2_sig w p a). Qed.

  (** Directed forms, used instead of [rewrite] for the same performance reason
      as [getSP_split] / [getSP_merge]. *)
  Definition getMSP_split {A} (w : DSLPSP A) (p : Prop) (a : A)
    : getDSLP w p a -> (p \/ getDSLP w False a) := proj1 (getMSP_singleton w p a).
  Definition getMSP_merge {A} (w : DSLPSP A) (p : Prop) (a : A)
    : (p \/ getDSLP w False a) -> getDSLP w p a := proj2 (getMSP_singleton w p a).

  Lemma getMSP_mono {A} (w : DSLPSP A) (p q : Prop) (a : A) :
    (p -> q) -> getDSLP w p a -> getDSLP w q a.
  Proof.
    intros Hpq H. apply getMSP_merge.
    destruct (getMSP_split w p a H) as [Hp | Hf];
      [left; exact (Hpq Hp) | right; exact Hf].
  Qed.

  #[program] Definition retDSLP {A} (v : A) : DSLPSP A :=
    fun p a => a = v -> p.
  Next Obligation.
  Proof.
    intros p a. split.
    - intro H. destruct (classic p) as [Hp | Hnp]; [left; exact Hp |].
      right. intro Heq. exact (Hnp (H Heq)).
    - intros [Hp | Hn] Heq; [exact Hp | destruct (Hn Heq)].
  Qed.

  #[program] Definition bindDSLP {A B} (m : DSLPSP A) (k : A -> DSLPSP B)
    : DSLPSP B :=
    fun p b => forall a, (k a) (m p a) b.
  Next Obligation.
  Proof.
    intros p b. split.
    - (* [p] fails ==> nothing in the co-set of [m] can meet the co-set of [k] *)
      intro H. destruct (classic p) as [Hp | Hnp]; [left; exact Hp |].
      right. intro a. specialize (H a).
      apply (proj2_sig (k a) (proj1_sig m False a) b).
      destruct (proj1 (proj2_sig (k a) (proj1_sig m p a) b) H) as [Hmp | Hkf];
        [| right; exact Hkf ].
      left. destruct (proj1 (proj2_sig m p a) Hmp) as [Hp | Hmf];
        [ destruct (Hnp Hp) | exact Hmf ].
    - intros [Hp | H] a.
      + apply (proj2_sig (k a) (proj1_sig m p a) b). left.
        apply (proj2_sig m p a). left. exact Hp.
      + specialize (H a).
        apply (proj2_sig (k a) (proj1_sig m p a) b).
        destruct (proj1 (proj2_sig (k a) (proj1_sig m False a) b) H) as [Hmf | Hkf];
          [| right; exact Hkf ].
        left. apply (proj2_sig m p a). right. exact Hmf.
  Qed.

  #[global] Instance Monad_DSLPSP : Monad DSLPSP :=
    {| ret := fun _ => retDSLP ;
      bind := fun _ _ => bindDSLP |}.

  #[global] Instance Eq1_DSLPSP : Eq1 DSLPSP :=
    fun A m n => forall p a, getDSLP m p a <-> getDSLP n p a.

  #[global] Instance Eq1Equivalence_DSLPSP
    : @Eq1Equivalence DSLPSP _ Eq1_DSLPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a). specialize (H2 p a). tauto.
  Qed.

  (** Meet preservation and congruence in the [Prop] argument, both derived
      from [MSingleton] — the duals of [getSP]'s join/congruence facts. *)
  Lemma getMSP_meet {A} (w : DSLPSP A) (I : Type) (p : I -> Prop) (a : A) :
    getDSLP w (forall i, p i) a <-> forall i, getDSLP w (p i) a.
  Proof.
    split.
    - intros H i. apply getMSP_merge.
      destruct (getMSP_split w _ a H) as [Hall | Hf];
        [ left; exact (Hall i) | right; exact Hf ].
    - intro Hall. apply getMSP_merge.
      destruct (classic (getDSLP w False a)) as [Hf | Hnf]; [ right; exact Hf |].
      left. intro i. destruct (getMSP_split w _ a (Hall i)) as [Hpi | Hf];
        [ exact Hpi | destruct (Hnf Hf) ].
  Qed.

  Lemma getMSP_cong {A} (w : DSLPSP A) (p q : Prop) (a : A) :
    (p <-> q) -> (getDSLP w p a <-> getDSLP w q a).
  Proof.
    intro Hpq. split; intro H; apply getMSP_merge;
      destruct (getMSP_split w _ a H) as [Hx | Hf].
    - left. exact (proj1 Hpq Hx).
    - right. exact Hf.
    - left. exact (proj2 Hpq Hx).
    - right. exact Hf.
  Qed.

  #[global] Instance MonadLawsE_DSLPSP
    : @MonadLawsE DSLPSP Eq1_DSLPSP _.
  Proof.
    constructor.
    - (* bind_ret_l: only [a = x] contributes; every other [a] gets a
         vacuously-true precondition, on which any [MSingleton] fires *)
      intros A B f x. unfold eq1, Eq1_DSLPSP. intros p b. split.
      + intro H. specialize (H x).
        apply (getMSP_mono (f x) (x = x -> p) p b); [| exact H].
        intro Himp. exact (Himp eq_refl).
      + intros H a. destruct (classic (a = x)) as [Heq | Hne].
        * subst a. apply (getMSP_mono (f x) p (x = x -> p) b); [| exact H].
          intros Hp _. exact Hp.
        * apply (getMSP_mono (f a) True (a = x -> p) b).
          -- intros _ Heq. destruct (Hne Heq).
          -- apply getMSP_merge. left. exact I.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_DSLPSP. intros p a. split.
      + intro H. exact (H a eq_refl).
      + intros H a0 Heq. subst a0. exact H.
    - (* bind_bind: the precondition handed to [g b] is a MEET over [a], and
         [g b] preserves meets — the exact dual of the [bindASP] argument *)
      intros A B C x f g. unfold eq1, Eq1_DSLPSP. intros p c. split.
      + intros H a b.
        exact (proj1 (getMSP_meet (g b) A
                        (fun a0 => getDSLP (f a0) (getDSLP x p a0) b) c) (H b) a).
      + intros H b.
        apply (getMSP_meet (g b) A (fun a => getDSLP (f a) (getDSLP x p a) b) c).
        intro a. exact (H a b).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_DSLPSP in *. intros p b.
      split; intros H a; specialize (H a).
      + exact (proj1 (Hfg a _ b)
                 (proj1 (getMSP_cong (f a) _ _ b (Hxy p a)) H)).
      + exact (proj2 (getMSP_cong (f a) _ _ b (Hxy p a))
                 (proj2 (Hfg a _ b) H)).
  Qed.
End PureDSLPMonad.

(* ================================================================= *)
(** ** Orders on the pure variant                                     *)
(* ================================================================= *)

Section PureDSLPOrders.
  Definition ordDSLPSP {A} (m1 m2 : DSLPSP A) : Prop :=
    forall p a, getDSLP m1 p a -> getDSLP m2 p a.
  Definition ordDSLPSPAt {A} (pre : Prop) (m1 m2 : DSLPSP A) : Prop :=
    forall a, getDSLP m1 pre a -> getDSLP m2 pre a.

  (** Dual to [asp_bot_pure]: [MSingleton] makes every DSLP true at [True]. *)
  Lemma dslp_top_pure {A} (w : DSLPSP A) (a : A) : getDSLP w True a.
  Proof. exact (getMSP_merge w True a (or_introl I)). Qed.
End PureDSLPOrders.

Section ProgDSLPMonad.
  Variable S : Type.

  Definition MeetPreservingProg {A} (w : SPStExc A) : Prop :=
    TerminatingProg S w /\ ConjunctiveProg S w.

  Definition MSingletonProg {A} (w : SPStExc A) : Prop :=
    forall (pre : S -> Prop) (r : option (A * S)),
      w pre r <-> forall s0, ~ pre s0 -> w (fun s => s <> s0) r.

  (** Dual of [join_to_singleton_prog]: index the meet by the subset
      [{s0 | ~ pre s0}] and take the CO-singleton [fun s => s <> s0] at each
      index.  The intersection of those co-singletons is pointwise [pre] (by
      [NNPP]), and the indexed meet is literally the right-hand side of
      [MSingletonProg]. *)
  Lemma meet_to_msingleton_prog {A} (w : SPStExc A) :
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

  Lemma msingleton_to_meet_prog {A} (w : SPStExc A) :
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

  Theorem meet_iff_msingleton_prog {A} (w : SPStExc A) :
    MeetPreservingProg w <-> MSingletonProg w.
  Proof. split; [apply meet_to_msingleton_prog | apply msingleton_to_meet_prog]. Qed.

  Definition DSLPStExc (A : Type) : Type := { w : SPStExc A | MSingletonProg w }.

  Definition getDSLPStExc {A} (w : DSLPStExc A) : SPStExc A :=
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
  Lemma msingletonProg_ext {A} (w1 w2 : SPStExc A) :
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
  Lemma msingletonProg_repr {A} (w : SPStExc A) (Hw : MSingletonProg w)
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

  #[program] Definition retDSLPStExc {A} (v : A) : DSLPStExc A :=
    fun pre r => forall s0, r = Some (v, s0) -> pre s0.
  Next Obligation.
  Proof. exact (dslp_msingleton (fun s r => r = Some (v, s))). Qed.

  #[program] Definition bindDSLPStExc {A B}
    (m : DSLPStExc A) (k : A -> DSLPStExc B) : DSLPStExc B :=
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
    Instance Monad__DSLPStExc : Monad DSLPStExc :=
    {| ret := fun _ => @retDSLPStExc _ ;
      bind := fun _ _ => @bindDSLPStExc _ _ |}.

  #[global] Instance Eq1__DSLPStExc : Eq1 DSLPStExc :=
    fun A m n => forall pre r, getDSLPStExc m pre r <-> getDSLPStExc n pre r.

  #[global] Instance Eq1Equivalence__DSLPStExc
    : @Eq1Equivalence DSLPStExc _ Eq1__DSLPStExc.
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

  Lemma msingletonProg_mono {A} (w : SPStExc A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros Hsub H. apply (msingletonProg_repr w Hw). intros s Hc.
    exact (Hsub s (proj1 (msingletonProg_repr w Hw P r) H s Hc)).
  Qed.

  Lemma msingletonProg_cong {A} (w : SPStExc A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s <-> Q s) -> (w P r <-> w Q r).
  Proof.
    intro H. split; intro Hw'.
    - exact (msingletonProg_mono w Hw P Q r (fun s hs => proj1 (H s) hs) Hw').
    - exact (msingletonProg_mono w Hw Q P r (fun s hs => proj2 (H s) hs) Hw').
  Qed.

  Lemma msingletonProg_meet {A} (w : SPStExc A) (Hw : MSingletonProg w)
    (I : Type) (p : I -> (S -> Prop)) (r : option (A * S)) :
    w (fun s => forall i, p i s) r <-> forall i, w (p i) r.
  Proof.
    split.
    - intros H i. apply (msingletonProg_repr w Hw). intros s Hc.
      exact (proj1 (msingletonProg_repr w Hw (fun s0 => forall j, p j s0) r) H s Hc i).
    - intro H. apply (msingletonProg_repr w Hw). intros s Hc i.
      exact (proj1 (msingletonProg_repr w Hw (p i) r) (H i) s Hc).
  Qed.

  #[global] Instance MonadLawsE__DSLPStExc
    : @MonadLawsE DSLPStExc Eq1__DSLPStExc _.
  Proof.
    constructor.
    - (* bind_ret_l.  [getProgMSP (retDSLPStExc x) pre (Some (a, s0))] is
         [forall s1, Some (a, s0) = Some (x, s1) -> pre s1], i.e. [pre s0] when
         [a = x] and vacuously true otherwise — and every [MSingletonProg]
         transformer fires at a vacuously-true precondition. *)
      intros A B f x. unfold eq1, Eq1__DSLPStExc. intros pre r. split.
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
      intros A m. unfold eq1, Eq1__DSLPStExc. intros pre r. split.
      + intros [H1 H2]. destruct r as [[a s0]|].
        * exact (H1 a s0 eq_refl).
        * exact (H2 eq_refl).
      + intro H. split.
        * intros a s0 Heq. subst r. exact H.
        * intro Hr. subst r. exact H.
    - (* bind_bind: the precondition handed to [g b] is a MEET over the
         intermediate value [a], and [g b] preserves meets *)
      intros A B C x f g. unfold eq1, Eq1__DSLPStExc. intros pre r.
      (* a [Some] outcome of [bind x f] never uses its [r = None] conjunct *)
      assert (Hsimp : forall b s1,
        getDSLPStExc (bindDSLPStExc x f) pre (Some (b, s1)) <->
        forall a, getDSLPStExc (f a)
                    (fun s0 => getDSLPStExc x pre (Some (a, s0))) (Some (b, s1))).
      { intros b s1. split.
        - intros [H1 _] a. exact (H1 a).
        - intro H. split; [exact H | intro Hc; discriminate Hc]. }
      assert (Hg : forall b,
        getDSLPStExc (g b)
          (fun s1 => getDSLPStExc (bindDSLPStExc x f) pre (Some (b, s1))) r <->
        forall a, getDSLPStExc (g b)
                    (fun s1 => getDSLPStExc (f a)
                       (fun s0 => getDSLPStExc x pre (Some (a, s0))) (Some (b, s1))) r).
      { intro b.
        transitivity (getDSLPStExc (g b)
          (fun s1 => forall a, getDSLPStExc (f a)
             (fun s0 => getDSLPStExc x pre (Some (a, s0))) (Some (b, s1))) r).
        - apply (msingletonProg_cong _ (proj2_sig (g b))). exact (Hsimp b).
        - exact (msingletonProg_meet _ (proj2_sig (g b)) A
                   (fun a s1 => getDSLPStExc (f a)
                      (fun s0 => getDSLPStExc x pre (Some (a, s0))) (Some (b, s1))) r). }
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
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__DSLPStExc in *. intros pre r.
      assert (Hstep : forall a,
        getDSLPStExc (f a) (fun s0 => getDSLPStExc x pre (Some (a, s0))) r <->
        getDSLPStExc (g a) (fun s0 => getDSLPStExc y pre (Some (a, s0))) r).
      { intro a.
        transitivity (getDSLPStExc (g a)
                        (fun s0 => getDSLPStExc x pre (Some (a, s0))) r).
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

Arguments retDSLPStExc {_} {_}.
Arguments bindDSLPStExc {_} {_} {_}.
Arguments getDSLPStExc {_} {_}.

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
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad.

Module StDSLP.
  Import StTrans StASP.
Section ProgDSLPMonad.
  Variable S : Type.

  Definition MeetPreservingProg {A} (w : SPSt A) : Prop :=
    TerminatingProg S w /\ ConjunctiveProg S w.

  Definition MSingletonProg {A} (w : SPSt A) : Prop :=
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

  Lemma msingletonProg_ext {A} (w1 w2 : SPSt A) :
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
  Lemma msingletonProg_repr {A} (w : SPSt A) (Hw : MSingletonProg w)
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

  Lemma msingletonProg_mono {A} (w : SPSt A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : A * S) :
    (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros Hsub H. apply (msingletonProg_repr w Hw). intros s Hc.
    exact (Hsub s (proj1 (msingletonProg_repr w Hw P r) H s Hc)).
  Qed.

  Lemma msingletonProg_cong {A} (w : SPSt A) (Hw : MSingletonProg w)
    (P Q : S -> Prop) (r : A * S) :
    (forall s, P s <-> Q s) -> (w P r <-> w Q r).
  Proof.
    intro H. split; intro Hw'.
    - exact (msingletonProg_mono w Hw P Q r (fun s hs => proj1 (H s) hs) Hw').
    - exact (msingletonProg_mono w Hw Q P r (fun s hs => proj2 (H s) hs) Hw').
  Qed.

  Lemma msingletonProg_meet {A} (w : SPSt A) (Hw : MSingletonProg w)
    (I : Type) (p : I -> (S -> Prop)) (r : A * S) :
    w (fun s => forall i, p i s) r <-> forall i, w (p i) r.
  Proof.
    split.
    - intros H i. apply (msingletonProg_repr w Hw). intros s Hc.
      exact (proj1 (msingletonProg_repr w Hw (fun s0 => forall j, p j s0) r) H s Hc i).
    - intro H. apply (msingletonProg_repr w Hw). intros s Hc i.
      exact (proj1 (msingletonProg_repr w Hw (p i) r) (H i) s Hc).
  Qed.

  Definition DSLPSt (A : Type) : Type := { w : SPSt A | MSingletonProg w }.

  Definition getDSLPSt {A} (w : DSLPSt A) : SPSt A := proj1_sig w.

  #[program] Definition retDSLPSt {A} (v : A) : DSLPSt A :=
    fun pre r => forall s0, r = (v, s0) -> pre s0.
  Next Obligation. exact (dslp_msingleton (fun s r => r = (v, s))). Qed.

  (** Dual to [bindASPSt]: [SPSpecMonads] carried an extra
      [/\ (r = None -> m pre None)] conjunct; with no exceptional outcome it
      disappears. *)
  #[program] Definition bindDSLPSt {A B}
    (m : DSLPSt A) (k : A -> DSLPSt B) : DSLPSt B :=
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

  #[global] Instance Monad__DSLPSt : Monad DSLPSt :=
    {| ret := fun _ => @retDSLPSt _ ;
       bind := fun _ _ => @bindDSLPSt _ _ |}.

  #[global] Instance Eq1__DSLPSt : Eq1 DSLPSt :=
    fun A m n => forall pre r, getDSLPSt m pre r <-> getDSLPSt n pre r.

  #[global] Instance Eq1Equivalence__DSLPSt
    : @Eq1Equivalence DSLPSt _ Eq1__DSLPSt.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  Lemma msingletonProg_top {A} (w : SPSt A) (Hw : MSingletonProg w) (r : A * S) :
    w (fun _ => True) r.
  Proof. apply Hw. intros s0 Hn. destruct (Hn I). Qed.

  #[global] Instance MonadLawsE__DSLPSt
    : @MonadLawsE DSLPSt Eq1__DSLPSt _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__DSLPSt. intros pre r. split.
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
      intros A m. unfold eq1, Eq1__DSLPSt. intros pre r. split.
      + intro H. destruct r as [a0 s0]. exact (H a0 s0 eq_refl).
      + intros H a s0 Heq. subst r. exact H.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__DSLPSt. intros pre r. split.
      + intros H a b.
        exact (proj1 (msingletonProg_meet _ (proj2_sig (g b)) A
                        (fun a0 s1 => getDSLPSt (f a0)
                           (fun s0 => getDSLPSt x pre (a0, s0)) (b, s1)) r)
                 (H b) a).
      + intros H b.
        apply (msingletonProg_meet _ (proj2_sig (g b)) A
                 (fun a0 s1 => getDSLPSt (f a0)
                    (fun s0 => getDSLPSt x pre (a0, s0)) (b, s1)) r).
        intro a. exact (H a b).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__DSLPSt in *. intros pre r.
      split; intros H a.
      + apply (msingletonProg_cong _ (proj2_sig (g a))
                 (fun s0 => getDSLPSt x pre (a, s0))
                 (fun s0 => getDSLPSt y pre (a, s0)) r).
        * intro s0. exact (Hxy pre (a, s0)).
        * apply Hfg. exact (H a).
      + apply (msingletonProg_cong _ (proj2_sig (f a))
                 (fun s0 => getDSLPSt y pre (a, s0))
                 (fun s0 => getDSLPSt x pre (a, s0)) r).
        * intro s0. symmetry. exact (Hxy pre (a, s0)).
        * apply Hfg. exact (H a).
  Qed.

End ProgDSLPMonad.

Arguments retDSLPSt {_} {_}.
Arguments bindDSLPSt {_} {_} {_}.
Arguments getDSLPSt {_} {_}.


(* ---- order and monotonicity ---- *)

Section StDSLPOrders.
  Variable S : Type.
  Definition ordDSLPSt {A} (m1 m2 : DSLPSt S A) : Prop :=
    forall pre r, getDSLPSt m1 pre r -> getDSLPSt m2 pre r.
  Definition ordDSLPStAt {A} (pre : S -> Prop) (m1 m2 : DSLPSt S A) : Prop :=
    forall r, getDSLPSt m1 pre r -> getDSLPSt m2 pre r.
  Lemma dslp_top {A} (w : DSLPSt S A) (r : (A * S)) :
    getDSLPSt w (fun _ => True) r.
  Proof. apply (proj2_sig w). intros s0 Hn. destruct (Hn I). Qed.
  Lemma dslpMono {A} (w : DSLPSt S A) (P Q : S -> Prop) (r : (A * S)) :
    (forall s, P s -> Q s) -> getDSLPSt w P r -> getDSLPSt w Q r.
  Proof. exact (msingletonProg_mono S (getDSLPSt w) (proj2_sig w) P Q r). Qed.
End StDSLPOrders.
Arguments ordDSLPSt {_} {_}.
Arguments ordDSLPStAt {_} {_}.
End StDSLP.

(* ================================================================= *)
(** * Refinement order and monotonicity for DSLP *)
(* ================================================================= *)

Section DSLPOrders.
  Variable S : Type.
  Definition ordDSLPStExc {A} (m1 m2 : DSLPStExc S A) : Prop :=
    forall pre r, getDSLPStExc m1 pre r -> getDSLPStExc m2 pre r.
  Definition ordDSLPStExcAt {A} (pre : S -> Prop) (m1 m2 : DSLPStExc S A) : Prop :=
    forall r, getDSLPStExc m1 pre r -> getDSLPStExc m2 pre r.
  Lemma dslp_top {A} (w : DSLPStExc S A) (r : option (A * S)) :
    getDSLPStExc w (fun _ => True) r.
  Proof. apply (proj2_sig w). intros s0 Hn. destruct (Hn I). Qed.
  Lemma dslpMono {A} (w : DSLPStExc S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getDSLPStExc w P r -> getDSLPStExc w Q r.
  Proof. exact (msingletonProg_mono S (getDSLPStExc w) (proj2_sig w) P Q r). Qed.
End DSLPOrders.

Arguments ordDSLPStExc {_} {_}.
Arguments ordDSLPStExcAt {_} {_}.

(* ================================================================= *)
(** ** The reader-indexed variant                                    *)
(* ================================================================= *)

(** [DSLPRd R A = readerT R DSLPSP A]: one [DSLPSP] per environment.  The
    precondition slot stays a bare [Prop], so environments are specified
    INDEPENDENTLY — the pointwise lift, not a shared [R -> Prop].  Every fibre is [MSingleton], so a [DSLPRd R A] is exactly a relation
    [R -> A -> Prop], read demonically.

    Laws come from the generic [readerT] instances in
    [ComputationMonads/TransformerLaws.v] over [Monad_DSLPSP]. *)

From ExtLib Require Import ReaderMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

Section RdDSLPMonad.
  Variable R : Type.

  Definition DSLPRd (A : Type) : Type := readerT R DSLPSP A.

  Definition getDSLPRd {A} (w : DSLPRd A) (r : R) : SPPure A :=
    getDSLP (runReaderT w r).

  #[global] Instance Monad__DSLPRd : Monad DSLPRd :=
    @Monad_readerT R DSLPSP Monad_DSLPSP.

  #[global] Instance Eq1__DSLPRd : Eq1 DSLPRd :=
    Eq1_readerT R DSLPSP.

  #[global] Instance Eq1Equivalence__DSLPRd
    : @Eq1Equivalence DSLPRd _ Eq1__DSLPRd :=
    Eq1Equivalence_readerT R DSLPSP.

  #[global] Instance MonadLawsE__DSLPRd
    : @MonadLawsE DSLPRd Eq1__DSLPRd Monad__DSLPRd :=
    MonadLawsE_readerT R DSLPSP.

  Definition ordDSLPRd {A} (m1 m2 : DSLPRd A) : Prop :=
    forall r p a, getDSLPRd m1 r p a -> getDSLPRd m2 r p a.
  Definition ordDSLPRdAt {A} (pre : R -> Prop) (m1 m2 : DSLPRd A) : Prop :=
    forall r a, getDSLPRd m1 r (pre r) a -> getDSLPRd m2 r (pre r) a.

End RdDSLPMonad.

Arguments getDSLPRd {_} {_}.
