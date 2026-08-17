From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.

(** * The strongest-postcondition specification monads

    Predicate transformers [(S -> Prop) -> option (A * S) -> Prop], carved into
    four monads by four healthiness conditions:

      - [ASPProgSP]   -- [SingletonProg]                         (angelic)
      - [DSLPProgSP]  -- [MSingletonProg]                         (demonic, liberal)
      - [DSPProgSP]   -- [StrictProg /\ ConjunctiveProg]          (demonic)
      - [ASLPProgSP]  -- [TerminatingProg /\ DisjunctiveProg]     (angelic, liberal)

    Nothing here mentions a computation monad: these are the targets that
    observations map INTO.  [NonDetItObservationNew] and [NonDetObservationNew]
    supply the observations. *)

Definition PureSP (A : Type) : Type := Prop -> A -> Prop.

Section KenjiPureSP.
  Definition Monotone {A} (w : PureSP A) : Prop :=
    forall (p q : Prop) (a : A), (p -> q) -> w p a -> w q a.

  Definition Codomain {A} (w : PureSP A) : Prop :=
    forall (p : Prop) (a : A), w p a -> p.

  Definition KenjiPureSP (A : Type) : Type := { w : PureSP A | Monotone w /\ Codomain w }.

  Definition getKenjiPureSP {A} (w : KenjiPureSP A) : PureSP A := proj1_sig w.

  #[program] Definition retKenjiPureSP {A} (v : A) : KenjiPureSP A :=
    fun pre a => pre /\ a = v.
  Next Obligation.
  Proof.
    split.
    - intros p q a Hpq [Hp Heq]. split; [exact (Hpq Hp) | exact Heq].
    - intros p a [Hp _]. exact Hp.
  Qed.
  
  #[program] Definition bindKenjiPureSP {A B} (m : KenjiPureSP A) (k : A -> KenjiPureSP B) : KenjiPureSP B :=
    fun pre b => exists a, k a (m pre a) b.
  Next Obligation.
  Proof.
    split.
    - (* monotone: weaken [pre] inside [m], then inside [k a] *)
      intros p q b Hpq [a Ha]. exists a.
      apply (proj1 (proj2_sig (k a)) (proj1_sig m p a) (proj1_sig m q a) b);
        [ intro Hm; exact (proj1 (proj2_sig m) p q a Hpq Hm) | exact Ha ].
    - (* codomain: [k a] returns its argument, which [m] returns [p] from *)
      intros p b [a Ha].
      exact (proj2 (proj2_sig m) p a (proj2 (proj2_sig (k a)) (proj1_sig m p a) b Ha)).
  Qed.
  
End KenjiPureSP.

Arguments KenjiPureSP {_}.

Section KenjiProgSP.
  Variable S : Type.

  Definition ProgSP (A : Type) : Type := (S -> Prop) -> (option (A * S) -> Prop).
  
  Definition MonotoneS {A} (w : ProgSP A) : Prop :=
    forall (p q : S -> Prop) (r : option (A * S)), (forall (s : S), p s -> q s) -> w p r -> w q r.

  Definition CodomainS {A} (w : ProgSP A) : Prop :=
    forall (p : S -> Prop) (r : option (A * S)), w p r -> (exists s, p s).

  Definition KenjiProgSP (A : Type) : Type := { w : ProgSP A | MonotoneS w /\ CodomainS w }.

  Definition getKenjiProgSP {A} (w : KenjiProgSP A) : ProgSP A := proj1_sig w.

  #[program] Definition retKenjiProgSP {A} (v : A) : KenjiProgSP A :=
    fun pre r => exists s0, pre s0 /\ r = Some (v, s0).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s0 [Hp Heq]]. exists s0. split; [exact (Hpq s0 Hp) | exact Heq].
    - intros p r [s0 [Hp _]]. exists s0. exact Hp.
  Qed.

  #[program] Definition bindKenjiProgSP {A B} (m : KenjiProgSP A) (k : A -> KenjiProgSP B) : KenjiProgSP B :=
    fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [[a Ha] | [Hr Hn]].
      + left. exists a.
        apply (proj1 (proj2_sig (k a))
                 (fun s0 => proj1_sig m p (Some (a, s0)))
                 (fun s0 => proj1_sig m q (Some (a, s0))) r);
          [ intros s0 Hm; exact (proj1 (proj2_sig m) p q (Some (a, s0)) Hpq Hm)
          | exact Ha ].
      + right. split; [ exact Hr | exact (proj1 (proj2_sig m) p q None Hpq Hn) ].
    - intros p r [[a Ha] | [_ Hn]].
      + destruct (proj2 (proj2_sig (k a))
                    (fun s0 => proj1_sig m p (Some (a, s0))) r Ha) as [s0 Hm].
        exact (proj2 (proj2_sig m) p (Some (a, s0)) Hm).
      + exact (proj2 (proj2_sig m) p None Hn).
  Qed.

  (* ---- the two laws that do hold ---- *)

  Theorem KenjiProgSP_bind_ret_r {A} (m : KenjiProgSP A)
    (pre : S -> Prop) (r : option (A * S)) :
    getKenjiProgSP (bindKenjiProgSP m retKenjiProgSP) pre r <-> getKenjiProgSP m pre r.
  Proof.
    split.
    - intros [[a [s0 [Hm Heq]]] | [Hr Hn]]; subst r; assumption.
    - intro H. destruct r as [[a s0]|].
      + left. exists a, s0. split; [exact H | reflexivity].
      + right. split; [reflexivity | exact H].
  Qed.

  Theorem KenjiProgSP_bind_ret_l_kenji {A B} (v : A) (k : A -> KenjiProgSP B)
    (pre : S -> Prop) (r : option (B * S)) :
    getKenjiProgSP (bindKenjiProgSP (retKenjiProgSP v) k) pre r <-> getKenjiProgSP (k v) pre r.
  Proof.
    split.
    - intros [[a Ha] | [_ [s1 [_ Heq]]]]; [| discriminate Heq].
      (* [CodomainS] of [k a] produces a witness, which forces [a = v] *)
      destruct (proj2 (proj2_sig (k a))
                  (fun s0 => proj1_sig (retKenjiProgSP v) pre (Some (a, s0))) r Ha)
        as [s0 [s1 [Hp Heq]]].
      assert (Hav : a = v) by congruence. subst a.
      (* [MonotoneS] of [k v] then rewrites the precondition back to [pre] *)
      apply (proj1 (proj2_sig (k v))
               (fun s0 => proj1_sig (retKenjiProgSP v) pre (Some (v, s0))) pre r);
        [| exact Ha ].
      intros s [s' [Hp' Heq']]. assert (Hss : s = s') by congruence.
      subst s. exact Hp'.
    - intro H. left. exists v.
      apply (proj1 (proj2_sig (k v)) pre
               (fun s0 => proj1_sig (retKenjiProgSP v) pre (Some (v, s0))) r);
        [| exact H ].
      intros s Hs. exists s. split; [ exact Hs | reflexivity ].
  Qed.
End KenjiProgSP.

Arguments ProgSP {_}.

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
    fun a => fun pre r => (exists s, pre s) /\ r = Some (tt, a).
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
  Definition r : option (unit * bool) := Some (tt, true).

  (* S := bool, A := bool, B := C := unit *)
  
  (** LHS **)
  
  (* bind (bind m k) (fun _ : unit => g) pre r <->
     (exists b : unit, g (fun s1 => (bind m k) pre (Some (b, s1))) r) \/ (r = None /\ (bind m k) pre None) <->
     (exists b : unit, g (fun s1 => (bind m k) pre (Some (b, s1))) r) <->
     g (fun s1 => (bind m k) pre (Some (tt, s1))) r <-> (see below)
     g (fun s1 => True) r <-> (unfold g)
     True /\ True <-> True
   *)
  
  (* (bind m k) pre (Some (tt, s1)) <-> (unfold bind)
     exists a, k a (fun s0 => m pre (Some (a, s0))) (Some (tt, s1)) <-> (unfold k)
     exists a, (exists s, m pre (Some (a, s))) /\ a = s1 <-> (unfold m)
     exists a, (exists s, pre s) /\ a = s1 <-> (a := true)
     exists s, pre s <-> (s := s1)
     True *)

  (** RHS **)
  
  (* bind m (fun a => bind (k a) (fun _ : unit => g)) pre r <->
     (exists a : bool, (bind (k a) g) (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None) <->
     (exists a : bool, (bind (k a) g) (fun s0 => m pre (Some (a, s0))) r) <->
     (exists a : bool, (bind (k a) g) (fun _ => exists s, pre s) r) <->
     (exists a : bool, (bind (k a) g) (fun _ => True) r) <->
     (exists a : bool, False) <-> False
   *)

  (* (bind (k a) g) (fun _ => True) r <->
     (exists b : unit, g (fun s1 => k a (fun _ => True) (Some (b, s1))) r) \/ (r = None /\ k a (fun _ => True) None) <->
     (exists b : unit, g (fun s1 => k a (fun _ => True) (Some (b, s1))) r) <->
     g (fun s1 => k a (fun _ => True) (Some (tt, s1))) r <-> (see below)
     g (fun s1 => s1 = a) r <->
     (fun s1 => s1 = a) true /\ (fun s1 => s1 = a) false <->
     (true = a) /\ (false a) <-> False *)

  (* k a (fun _ => True) (Some (tt, s1)) <->
     (exists s, True) /\ Some (tt, s1) = Some (tt, a) <->
     s1 = a *)
  
  Theorem ProgSP_bind_bind_fails :
    ~ (forall (A B C S : Type) (m : KenjiProgSP S A) (f : A -> KenjiProgSP S B)
              (g : B -> KenjiProgSP S C) (pre : S -> Prop) (r : option (C * S)),
         getKenjiProgSP S (bindKenjiProgSP S (bindKenjiProgSP S m f) g) pre r <->
           getKenjiProgSP S (bindKenjiProgSP S m (fun a => bindKenjiProgSP S (f a) g)) pre r).
  Proof.
    intro H.
    (* LHS holds: the precondition handed to [g] is constantly [True] *)
    assert (HL : getKenjiProgSP bool
                   (bindKenjiProgSP bool (bindKenjiProgSP bool m k) (fun _ : unit => g))
                   pre r).
    { left. exists tt. split.
      - left. exists true. split; [ exists true; exists true; exact I | reflexivity ].
      - left. exists false. split; [ exists true; exists true; exact I | reflexivity ]. }
    (* RHS does not: [g] is now handed the singleton [fun s1 => s1 = a] *)
    destruct (proj1 (H bool unit unit bool m k (fun _ : unit => g) pre r) HL)
      as [[a Ha] | [Hr _]]; [| discriminate Hr].
    destruct Ha as [[b Hb] | [Hr _]]; [| discriminate Hr].
    destruct Hb as [[_ Het] [_ Hef]].
    assert (Ha1 : a = true) by congruence.
    assert (Ha2 : a = false) by congruence.
    congruence.
  Qed.

(* INTUITION: The problematic predicate transformer here is
   g := fun pre r => pre true /\ pre false. It requires that
   two distinct initial states satisfy the precondition. The
   LHS of the bind simplifies as follows:
   bind (bind m k) (fun _ : unit => g) pre r <-> g (fun s1 => True) r.
   The precondition passed to g is not problematic, since it always returns
   True. However the RHS of the bind simplies as follows:
   bind m (fun a => (bind k a) (fun _ : unit => g)) pre r <->
   (exists a : bool, g (fun s1 => s1 = a) r) <->
   (exists a : bool, (a = true) /\ (a = false). *)

End KenjiFailingBind.

Section PurePredicateTransformers.
  Definition Strict {A} (w : PureSP A) : Prop :=
    forall (a : A), ~ w False a.

  Definition Terminating {A} (w : PureSP A) : Prop :=
    forall (a : A), w True a.

  Definition Conjunctive {A} (w : PureSP A) : Prop :=
    forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
      w (forall i, p i) a <-> forall i, w (p i) a.

  Definition Disjunctive {A} (w : PureSP A) : Prop :=
    forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
      w (exists i, p i) a <-> exists i, w (p i) a.
End PurePredicateTransformers.

Section ProgPredicateTransformers.
  Variable S : Type.

  Definition StrictProg {A} (w : ProgSP A) : Prop :=
    forall (r : option (A * S)), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : ProgSP A) : Prop :=
    forall (r : option (A * S)), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : ProgSP A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
End ProgPredicateTransformers.

Section PureASPMonad.
  Definition JoinPreserving {A} (w : PureSP A) : Prop :=
    Strict w /\ Disjunctive w.

  Definition Singleton {A} (w : PureSP A) : Prop :=    
    forall (p : Prop) (a : A), w p a <-> p /\ w True a.

  (** At [PureSP] the precondition is a [Prop], and under propositional
      extensionality there are only two of those up to equality.  So [Strict]
      already forces [Singleton]; [Disjunctive] is not needed here. *)
  Lemma join_to_singleton {A} (w : PureSP A) :
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

  Lemma singleton_to_join {A} (w : PureSP A) :
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
  
  Theorem join_iff_singleton {A} (w : PureSP A) :
    JoinPreserving w <-> Singleton w.
  Proof. split; [apply join_to_singleton | apply singleton_to_join]. Qed.

  (* Equivalent to Kenji's formalization *)
  
  Theorem kenji_iff_singleton {A} (w : PureSP A) :
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

  Definition ASPSP (A : Type) : Type := { w : PureSP A | Singleton w }.

  Definition getASP {A} (w : ASPSP A) : PureSP A := proj1_sig w.

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
Section KenjiPureDSLP.
  Definition CodomainDSLP {A} (w : PureSP A) : Prop :=
    forall (p : Prop) (a : A), p -> w p a.

  Definition KenjiPureDSLP {A} (w : PureSP A) : Prop := Monotone w /\ CodomainDSLP w.
End KenjiPureDSLP.

Section PureDSLPMonad.
  Definition MeetPreserving {A} (w : PureSP A) : Prop :=
    Terminating w /\ Conjunctive w.

  Definition MSingleton {A} (w : PureSP A) : Prop :=
    forall (p : Prop) (a : A), w p a <-> p \/ w False a.

  (** Dually to [join_to_singleton]: at [PureSP] the precondition is a [Prop],
      so [Terminating] alone already forces [MSingleton]; [Conjunctive] is not
      needed here. *)
  Lemma meet_to_msingleton {A} (w : PureSP A) :
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

  Lemma msingleton_to_meet {A} (w : PureSP A) :
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

  Theorem meet_iff_msingleton {A} (w : PureSP A) :
    MeetPreserving w <-> MSingleton w.
  Proof. split; [apply meet_to_msingleton | apply msingleton_to_meet]. Qed.

  Theorem kenjidslp_iff_msingleton {A} (w : PureSP A) :
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

  Definition DSLPSP (A : Type) : Type := { w : PureSP A | MSingleton w }.

  Definition getDSLP {A} (w : DSLPSP A) : PureSP A := proj1_sig w.

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
  Lemma dsp_recov {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
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
  Lemma dsp_wf {A} (R : S -> option (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : option (A * S)),
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
  Lemma dsp_cong {A} (R R' : S -> option (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : option (A * S)),
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
    forall (s : S) (r : option (A * S)),
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
      (forall (pre : S -> Prop) (r : option (A * S)), w pre r <->
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

  (** Everything of DSP shape inhabits the carrier — this discharges each
      [#[program]] obligation below. *)
  Lemma dsp_shape_wf {A} (R : S -> option (A * S) -> Prop) :
    StrictPositivelyMeetPreservingProg
      (fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)).
  Proof. apply dsp_carrier. intros pre r. exact (dsp_wf R pre r). Qed.

  (** ... and every carrier element is the DSP of its recovered relation. *)
  Lemma getProgDSP_carrier {A} (w : DSPProgSP A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgDSP w pre r <->
      ((exists s, pre s /\ (getProgDSP w (fun _ => True) r
                            /\ ~ getProgDSP w (fun t => t <> s) r)) /\
         (forall s, (getProgDSP w (fun _ => True) r
                     /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s)).
  Proof. exact (proj1 (dsp_carrier (getProgDSP w)) (proj2_sig w) pre r). Qed.

  (** ** The composite relation, and its unit/associativity laws

      The composite quantifies over the INTERMEDIATE OUTCOME [o : option (A * S)]
      and splits on it, rather than pairing an explicit [exists a smid] branch
      with a separate [None] branch.  This is the same shape as
      [outcomes_bind]. *)

  Lemma comp_cong {A B} (R R' : S -> option (A * S) -> Prop)
    (K K' : A -> S -> option (B * S) -> Prop)
    (HR : forall s r, R s r <-> R' s r)
    (HK : forall a s r, K a s r <-> K' a s r) :
    forall (s : S) (r : option (B * S)),
      (exists o, R s o /\ match o with
                          | Some (a, smid) => K a smid r
                          | None => r = None
                          end)
      <-> (exists o, R' s o /\ match o with
                               | Some (a, smid) => K' a smid r
                               | None => r = None
                               end).
  Proof.
    intros s r. split.
    - intros [[[a smid]|] [H1 H2]]; [ exists (Some (a, smid)) | exists None ];
        split; solve [ exact (proj1 (HR s _) H1)
                     | exact (proj1 (HK a smid r) H2) | exact H2 ].
    - intros [[[a smid]|] [H1 H2]]; [ exists (Some (a, smid)) | exists None ];
        split; solve [ exact (proj2 (HR s _) H1)
                     | exact (proj2 (HK a smid r) H2) | exact H2 ].
  Qed.

  Lemma comp_ret_l {A B} (v : A) (K : A -> S -> option (B * S) -> Prop)
    (s : S) (r : option (B * S)) :
    (exists o : option (A * S), o = Some (v, s)
        /\ match o with
           | Some (a, smid) => K a smid r
           | None => r = None
           end)
    <-> K v s r.
  Proof.
    split.
    - intros [o [Heq Hk]]. subst o. exact Hk.
    - intro Hk. exists (Some (v, s)). split; [ reflexivity | exact Hk ].
  Qed.

  Lemma comp_ret_r {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
    (exists o, R s o /\ match o with
                        | Some (a, smid) => r = Some (a, smid)
                        | None => r = None
                        end)
    <-> R s r.
  Proof.
    split.
    - intros [[[a smid]|] [HR Heq]]; subst r; exact HR.
    - intro HR. exists r. split; [ exact HR |].
      destruct r as [[a smid]|]; reflexivity.
  Qed.

  Lemma comp_assoc {A B C} (R : S -> option (A * S) -> Prop)
    (F : A -> S -> option (B * S) -> Prop)
    (G : B -> S -> option (C * S) -> Prop) (s : S) (r : option (C * S)) :
    (exists o2 : option (B * S),
        (exists o1 : option (A * S),
            R s o1 /\ match o1 with
                      | Some (a, s1) => F a s1 o2
                      | None => o2 = None
                      end)
        /\ match o2 with
           | Some (b, s2) => G b s2 r
           | None => r = None
           end)
    <-> (exists o1 : option (A * S),
            R s o1 /\ match o1 with
                      | Some (a, s1) =>
                          exists o2 : option (B * S),
                            F a s1 o2 /\ match o2 with
                                         | Some (b, s2) => G b s2 r
                                         | None => r = None
                                         end
                      | None => r = None
                      end).
  Proof.
    split.
    - intros [o2 [[o1 [HR HF]] HG]]. exists o1. split; [ exact HR |].
      destruct o1 as [[a s1]|].
      + exists o2. split; [ exact HF | exact HG ].
      + subst o2. exact HG.
    - intros [o1 [HR H]]. destruct o1 as [[a s1]|].
      + destruct H as [o2 [HF HG]]. exists o2. split; [| exact HG ].
        exists (Some (a, s1)). split; [ exact HR | exact HF ].
      + exists None. split; [| exact H ].
        exists None. split; [ exact HR | reflexivity ].
  Qed.


  (** ** [ret] and [bind] *)

  #[program] Definition retDSPProg {A} (a : A) : DSPProgSP A :=
    fun pre r => (retASPProg a pre r) /\ (retDSLPProg a pre r).
  Next Obligation. exact (dsp_shape_wf (fun s r => r = Some (a, s))). Qed.

  (* We would like bindDSPProg to match retDSPProg, but this requires
     converting DSPProgSP to both ASPProgSP and DSLPProgSP. *)

  (** The two probe forms are the ASP and the DSLP of the recovered relation. *)
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

  (** Both healthiness classes transport along pointwise equivalence. *)
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
    getProgDSP w pre r <-> (getProgASP (aspPartdsp w) pre r /\ getProgDSLP (dslpPartdsp w) pre r).
  Proof.
    refine (iff_trans (getProgDSP_carrier w pre r) _). split.
    - intros [He Hall]. split.
      + exact (proj2 (aspPartdsp_closed w pre r) He).
      + exact (proj2 (dslpPartdsp_closed w pre r) Hall).
    - intros [Ha Hd]. split.
      + exact (proj1 (aspPartdsp_closed w pre r) Ha).
      + exact (proj1 (dslpPartdsp_closed w pre r) Hd).
  Qed.

  (** Both binds compute the SAME composite relation, one existentially and
      one universally — which is why the conjunction below is the DSP of it. *)
  Lemma bind_asp_parts {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgASP (bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a))) pre r
    <-> (exists s, pre s /\
           (exists o, (getProgDSP m (fun _ => True) o
                       /\ ~ getProgDSP m (fun t => t <> s) o)
                      /\ match o with
                         | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                             /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                         | None => r = None
                         end)).
  Proof.
    split.
    - intros [[a Hk] | [Hr Hm]].
      + destruct (proj1 (aspPartdsp_closed (k a)
                           (fun s0 => getProgASP (aspPartdsp m) pre (Some (a, s0))) r) Hk)
          as [smid [Hp Hrk]].
        destruct (proj1 (aspPartdsp_closed m pre (Some (a, smid))) Hp) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists (Some (a, smid)). split; [ exact Hrm | exact Hrk ].
      + destruct (proj1 (aspPartdsp_closed m pre None) Hm) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists None. split; [ exact Hrm | exact Hr ].
    - intros [s [Hps [[[a smid]|] [Hrm Hrk]]]].
      + left. exists a.
        exact (proj2 (aspPartdsp_closed (k a)
                        (fun s0 => getProgASP (aspPartdsp m) pre (Some (a, s0))) r)
                 (ex_intro _ smid
                    (conj (proj2 (aspPartdsp_closed m pre (Some (a, smid)))
                             (ex_intro _ s (conj Hps Hrm))) Hrk))).
      + right. split; [ exact Hrk |].
        exact (proj2 (aspPartdsp_closed m pre None) (ex_intro _ s (conj Hps Hrm))).
  Qed.

  Lemma bind_dslp_parts {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgDSLP (bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a))) pre r
    <-> (forall s,
           (exists o, (getProgDSP m (fun _ => True) o
                       /\ ~ getProgDSP m (fun t => t <> s) o)
                      /\ match o with
                         | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                             /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                         | None => r = None
                         end) -> pre s).
  Proof.
    split.
    - intros [H1 H2] s [[[a smid]|] [Hrm Hrk]].
      + exact (proj1 (dslpPartdsp_closed m pre (Some (a, smid)))
                 (proj1 (dslpPartdsp_closed (k a)
                           (fun s0 => getProgDSLP (dslpPartdsp m) pre (Some (a, s0))) r)
                    (H1 a) smid Hrk) s Hrm).
      + exact (proj1 (dslpPartdsp_closed m pre None) (H2 Hrk) s Hrm).
    - intro H. split.
      + intro a.
        exact (proj2 (dslpPartdsp_closed (k a)
                        (fun s0 => getProgDSLP (dslpPartdsp m) pre (Some (a, s0))) r)
                 (fun smid Hrk =>
                    proj2 (dslpPartdsp_closed m pre (Some (a, smid)))
                      (fun s Hrm => H s (ex_intro _ (Some (a, smid)) (conj Hrm Hrk))))).
      + intro Hr.
        exact (proj2 (dslpPartdsp_closed m pre None)
                 (fun s Hrm => H s (ex_intro _ None (conj Hrm Hr)))).
  Qed.

  #[program] Definition bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) : DSPProgSP B :=
    fun pre r => bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a)) pre r /\
                   bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a)) pre r.
  Next Obligation.
    apply (dsp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists o, (getProgDSP m (fun _ => True) o
                               /\ ~ getProgDSP m (fun t => t <> s) o)
                              /\ match o with
                                 | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                                     /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                                 | None => r = None
                                 end))
                /\ (forall s,
                      (exists o, (getProgDSP m (fun _ => True) o
                                  /\ ~ getProgDSP m (fun t => t <> s) o)
                                 /\ match o with
                                    | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                                        /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                                    | None => r = None
                                    end) -> pre s))).
    - intros pre r. split.
      + intros [He Hall]. split;
          [ exact (proj2 (bind_asp_parts m k pre r) He)
          | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
      + intros [Ha Hd]. split;
          [ exact (proj1 (bind_asp_parts m k pre r) Ha)
          | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - apply dsp_shape_wf.
  Qed.

  (** The relation recovered from [retDSPProg a] is [fun s r => r = Some (a, s)]. *)
  Lemma rec_retDSPProg {A} (a : A) (s : S) (r : option (A * S)) :
    (getProgDSP (retDSPProg a) (fun _ => True) r
     /\ ~ getProgDSP (retDSPProg a) (fun t => t <> s) r)
    <-> r = Some (a, s).
  Proof. exact (dsp_recov (fun s0 r0 => r0 = Some (a, s0)) s r). Qed.

  (** [bindDSPProg m k] is pointwise the DSP of the composite relation. *)
  Lemma bindDSPProg_dsp {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgDSP (bindDSPProg m k) pre r
    <-> ((exists s, pre s /\
            (exists o, (getProgDSP m (fun _ => True) o
                        /\ ~ getProgDSP m (fun t => t <> s) o)
                       /\ match o with
                          | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                              /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                          | None => r = None
                          end))
         /\ (forall s,
               (exists o, (getProgDSP m (fun _ => True) o
                           /\ ~ getProgDSP m (fun t => t <> s) o)
                          /\ match o with
                             | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                                 /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                             | None => r = None
                             end) -> pre s)).
  Proof.
    split.
    - intros [Ha Hd]. split;
        [ exact (proj1 (bind_asp_parts m k pre r) Ha)
        | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - intros [He Hall]. split;
        [ exact (proj2 (bind_asp_parts m k pre r) He)
        | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
  Qed.

  (** The relation recovered from [bindDSPProg m k] is the composite. *)
  Lemma rec_bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B)
    (s : S) (r : option (B * S)) :
    (getProgDSP (bindDSPProg m k) (fun _ => True) r
     /\ ~ getProgDSP (bindDSPProg m k) (fun t => t <> s) r)
    <-> (exists o, (getProgDSP m (fun _ => True) o
                    /\ ~ getProgDSP m (fun t => t <> s) o)
                   /\ match o with
                      | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                          /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                      | None => r = None
                      end).
  Proof.
    refine (iff_trans (dsp_rec_ext _ _ (bindDSPProg_dsp m k) s r)
              (dsp_recov
                 (fun s0 r0 =>
                    exists o, (getProgDSP m (fun _ => True) o
                               /\ ~ getProgDSP m (fun t => t <> s0) o)
                              /\ match o with
                                 | Some (a, smid) => getProgDSP (k a) (fun _ => True) r0
                                                     /\ ~ getProgDSP (k a) (fun t => t <> smid) r0
                                 | None => r0 = None
                                 end)
                 s r)).
  Qed.

  #[global]
    Instance Monad__DSPProgSP : Monad DSPProgSP :=
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
    - (* bind_ret_l : the composite of [retDSPProg x] with [f] is [f x] *)
      intros A B f x. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (getProgDSP (retDSPProg x) (fun _ => True) o
                             /\ ~ getProgDSP (retDSPProg x) (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (f a) (fun _ => True) r0
                                   /\ ~ getProgDSP (f a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (getProgDSP (f x) (fun _ => True) r0
                      /\ ~ getProgDSP (f x) (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP (retDSPProg x) (fun _ => True) r1
                                  /\ ~ getProgDSP (retDSPProg x) (fun t => t <> s1) r1)
                    (fun s1 r1 => r1 = Some (x, s1))
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
    - (* bind_ret_r : the composite of [m] with [retDSPProg] is [m] *)
      intros A m. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (A * S)),
                 (exists o, (getProgDSP m (fun _ => True) o
                             /\ ~ getProgDSP m (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (retDSPProg a) (fun _ => True) r0
                                   /\ ~ getProgDSP (retDSPProg a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
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
                    (fun a1 s1 r1 => r1 = Some (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retDSPProg a1 s1 r1) s r0)
                 (comp_ret_r
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp m _ pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier m pre r)))).
    - (* bind_bind : associativity of the composite *)
      intros A B C x f g. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (C * S)),
                 (exists o, (getProgDSP (bindDSPProg x f) (fun _ => True) o
                             /\ ~ getProgDSP (bindDSPProg x f) (fun t => t <> s) o)
                            /\ match o with
                               | Some (b, smid) =>
                                   getProgDSP (g b) (fun _ => True) r0
                                   /\ ~ getProgDSP (g b) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (getProgDSP x (fun _ => True) o
                                 /\ ~ getProgDSP x (fun t => t <> s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       getProgDSP (bindDSPProg (f a) g) (fun _ => True) r0
                                       /\ ~ getProgDSP (bindDSPProg (f a) g)
                                              (fun t => t <> smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP (bindDSPProg x f) (fun _ => True) r1
                                  /\ ~ getProgDSP (bindDSPProg x f) (fun t => t <> s1) r1)
                    (fun s1 r1 =>
                       exists o, (getProgDSP x (fun _ => True) o
                                  /\ ~ getProgDSP x (fun t => t <> s1) o)
                                 /\ match o with
                                    | Some (a, smid) =>
                                        getProgDSP (f a) (fun _ => True) r1
                                        /\ ~ getProgDSP (f a) (fun t => t <> smid) r1
                                    | None => r1 = None
                                    end)
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
                          exists o, (getProgDSP (f a1) (fun _ => True) o
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) o)
                                    /\ match o with
                                       | Some (b, smid) =>
                                           getProgDSP (g b) (fun _ => True) r1
                                           /\ ~ getProgDSP (g b) (fun t => t <> smid) r1
                                       | None => r1 = None
                                       end)
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
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (getProgDSP x (fun _ => True) o
                             /\ ~ getProgDSP x (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (f a) (fun _ => True) r0
                                   /\ ~ getProgDSP (f a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (getProgDSP y (fun _ => True) o
                                 /\ ~ getProgDSP y (fun t => t <> s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       getProgDSP (g a) (fun _ => True) r0
                                       /\ ~ getProgDSP (g a) (fun t => t <> smid) r0
                                   | None => r0 = None
                                   end)).
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
Section ProgASLPMonad.
  Variable S : Type.

  Definition TerminatingPositivelyJoinPreserving {A} (w : ProgSP A) : Prop :=
    TerminatingProg S w /\ DisjunctiveProg S w.

  Definition ASLPProgSP (A : Type) : Type :=
    { w : ProgSP A | TerminatingPositivelyJoinPreserving w }.

  Definition getProgASLP {A} (w : ASLPProgSP A) : ProgSP A := proj1_sig w.

  Lemma aslp_recov {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
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

  Lemma aslp_wf {A} (R : S -> option (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : option (A * S)),
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

  Lemma aslp_cong {A} (R R' : S -> option (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : option (A * S)),
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
    forall (s : S) (r : option (A * S)),
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
      (forall (pre : S -> Prop) (r : option (A * S)), w pre r <->
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

  (** Everything of ASLP shape inhabits the carrier — this discharges each
      [#[program]] obligation below. *)
  Lemma aslp_shape_wf {A} (R : S -> option (A * S) -> Prop) :
    TerminatingPositivelyJoinPreserving
      (fun pre r => (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s)).
  Proof. apply aslp_carrier. intros pre r. exact (aslp_wf R pre r). Qed.

  (** ... and every carrier element is the ASLP of its recovered relation. *)
  Lemma getProgASLP_carrier {A} (w : ASLPProgSP A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgASLP w pre r <->
      ((exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                            /\ getProgASLP w (fun t => t = s) r)) \/
         (forall s, (~ getProgASLP w (fun _ => False) r
                     /\ getProgASLP w (fun t => t = s) r) -> pre s)).
  Proof. exact (proj1 (aslp_carrier (getProgASLP w)) (proj2_sig w) pre r). Qed.

  #[program] Definition retASLPProg {A} (a : A) : ASLPProgSP A :=
    fun pre r => (retASPProg a pre r) \/ (retDSLPProg a pre r).
  Next Obligation. exact (aslp_shape_wf (fun s r => r = Some (a, s))). Qed.

  (** The two probe forms are the ASP and the DSLP of the recovered relation. *)
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
                                   /\ getProgASLP w (fun t => t = s) r)) as [[s0 Hs0] | Hno].
      + right. intro Hc.
        destruct (proj1 (getProgASLP_carrier w (fun t => ~ pre t) r) Hc)
          as [[s [Hnp Hs]] | Hev].
        * exact (Hnp (Hall s Hs)).
        * exact (Hev s0 Hs0 (Hall s0 Hs0)).
      + left. apply getProgASLP_carrier. right. intros s Hs.
        exfalso. exact (Hno (ex_intro _ s Hs)).
  Qed.

  Lemma singletonProg_ext' {A} (w1 w2 : @ProgSP S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
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
    apply (singletonProg_ext'
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
    getProgASLP w pre r <-> (getProgASP (aspPartaslp w) pre r \/ getProgDSLP (dslpPartaslp w) pre r).
  Proof.
    refine (iff_trans (getProgASLP_carrier w pre r) _). split.
    - intros [He | Hall].
      + left. exact (proj2 (aspPartaslp_closed w pre r) He).
      + right. exact (proj2 (dslpPartaslp_closed w pre r) Hall).
    - intros [Ha | Hd].
      + left. exact (proj1 (aspPartaslp_closed w pre r) Ha).
      + right. exact (proj1 (dslpPartaslp_closed w pre r) Hd).
  Qed.

  (** Both binds compute the SAME composite relation. *)
  Lemma bind_asp_parts' {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgASP (bindASPProg (aspPartaslp m) (fun a => aspPartaslp (k a))) pre r
    <-> (exists s, pre s /\
           (exists o, (~ getProgASLP m (fun _ => False) o
                       /\ getProgASLP m (fun t => t = s) o)
                      /\ match o with
                         | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                             /\ getProgASLP (k a) (fun t => t = smid) r
                         | None => r = None
                         end)).
  Proof.
    split.
    - intros [[a Hk] | [Hr Hm]].
      + destruct (proj1 (aspPartaslp_closed (k a)
                           (fun s0 => getProgASP (aspPartaslp m) pre (Some (a, s0))) r) Hk)
          as [smid [Hp Hrk]].
        destruct (proj1 (aspPartaslp_closed m pre (Some (a, smid))) Hp) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists (Some (a, smid)). split; [ exact Hrm | exact Hrk ].
      + destruct (proj1 (aspPartaslp_closed m pre None) Hm) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists None. split; [ exact Hrm | exact Hr ].
    - intros [s [Hps [[[a smid]|] [Hrm Hrk]]]].
      + left. exists a.
        exact (proj2 (aspPartaslp_closed (k a)
                        (fun s0 => getProgASP (aspPartaslp m) pre (Some (a, s0))) r)
                 (ex_intro _ smid
                    (conj (proj2 (aspPartaslp_closed m pre (Some (a, smid)))
                             (ex_intro _ s (conj Hps Hrm))) Hrk))).
      + right. split; [ exact Hrk |].
        exact (proj2 (aspPartaslp_closed m pre None) (ex_intro _ s (conj Hps Hrm))).
  Qed.

  Lemma bind_dslp_parts' {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgDSLP (bindDSLPProg (dslpPartaslp m) (fun a => dslpPartaslp (k a))) pre r
    <-> (forall s,
           (exists o, (~ getProgASLP m (fun _ => False) o
                       /\ getProgASLP m (fun t => t = s) o)
                      /\ match o with
                         | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                             /\ getProgASLP (k a) (fun t => t = smid) r
                         | None => r = None
                         end) -> pre s).
  Proof.
    split.
    - intros [H1 H2] s [[[a smid]|] [Hrm Hrk]].
      + exact (proj1 (dslpPartaslp_closed m pre (Some (a, smid)))
                 (proj1 (dslpPartaslp_closed (k a)
                           (fun s0 => getProgDSLP (dslpPartaslp m) pre (Some (a, s0))) r)
                    (H1 a) smid Hrk) s Hrm).
      + exact (proj1 (dslpPartaslp_closed m pre None) (H2 Hrk) s Hrm).
    - intro H. split.
      + intro a.
        exact (proj2 (dslpPartaslp_closed (k a)
                        (fun s0 => getProgDSLP (dslpPartaslp m) pre (Some (a, s0))) r)
                 (fun smid Hrk =>
                    proj2 (dslpPartaslp_closed m pre (Some (a, smid)))
                      (fun s Hrm => H s (ex_intro _ (Some (a, smid)) (conj Hrm Hrk))))).
      + intro Hr.
        exact (proj2 (dslpPartaslp_closed m pre None)
                 (fun s Hrm => H s (ex_intro _ None (conj Hrm Hr)))).
  Qed.

  #[program] Definition bindASLPProg {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) : ASLPProgSP B :=
    fun pre r => bindASPProg (aspPartaslp m) (fun a => aspPartaslp (k a)) pre r \/
                   bindDSLPProg (dslpPartaslp m) (fun a => dslpPartaslp (k a)) pre r.
  Next Obligation.
    apply (aslp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists o, (~ getProgASLP m (fun _ => False) o
                               /\ getProgASLP m (fun t => t = s) o)
                              /\ match o with
                                 | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                                     /\ getProgASLP (k a) (fun t => t = smid) r
                                 | None => r = None
                                 end))
                \/ (forall s,
                      (exists o, (~ getProgASLP m (fun _ => False) o
                                  /\ getProgASLP m (fun t => t = s) o)
                                 /\ match o with
                                    | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                                        /\ getProgASLP (k a) (fun t => t = smid) r
                                    | None => r = None
                                    end) -> pre s))).
    - intros pre r. split.
      + intros [He | Hall];
          [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
          | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
      + intros [Ha | Hd];
          [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
          | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - apply aslp_shape_wf.
  Qed.

  (** [bindASLPProg m k] is pointwise the ASLP of the composite relation. *)
  Lemma bindASLPProg_aslp {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgASLP (bindASLPProg m k) pre r
    <-> ((exists s, pre s /\
            (exists o, (~ getProgASLP m (fun _ => False) o
                        /\ getProgASLP m (fun t => t = s) o)
                       /\ match o with
                          | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                              /\ getProgASLP (k a) (fun t => t = smid) r
                          | None => r = None
                          end))
         \/ (forall s,
               (exists o, (~ getProgASLP m (fun _ => False) o
                           /\ getProgASLP m (fun t => t = s) o)
                          /\ match o with
                             | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                                 /\ getProgASLP (k a) (fun t => t = smid) r
                             | None => r = None
                             end) -> pre s)).
  Proof.
    split.
    - intros [Ha | Hd];
        [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
        | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - intros [He | Hall];
        [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
        | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
  Qed.

  Lemma rec_retASLPProg {A} (a : A) (s : S) (r : option (A * S)) :
    (~ getProgASLP (retASLPProg a) (fun _ => False) r
     /\ getProgASLP (retASLPProg a) (fun t => t = s) r)
    <-> r = Some (a, s).
  Proof. exact (aslp_recov (fun s0 r0 => r0 = Some (a, s0)) s r). Qed.

  Lemma rec_bindASLPProg {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B)
    (s : S) (r : option (B * S)) :
    (~ getProgASLP (bindASLPProg m k) (fun _ => False) r
     /\ getProgASLP (bindASLPProg m k) (fun t => t = s) r)
    <-> (exists o, (~ getProgASLP m (fun _ => False) o
                    /\ getProgASLP m (fun t => t = s) o)
                   /\ match o with
                      | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                          /\ getProgASLP (k a) (fun t => t = smid) r
                      | None => r = None
                      end).
  Proof.
    refine (iff_trans (aslp_rec_ext _ _ (bindASLPProg_aslp m k) s r)
              (aslp_recov
                 (fun s0 r0 =>
                    exists o, (~ getProgASLP m (fun _ => False) o
                               /\ getProgASLP m (fun t => t = s0) o)
                              /\ match o with
                                 | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r0
                                                     /\ getProgASLP (k a) (fun t => t = smid) r0
                                 | None => r0 = None
                                 end)
                 s r)).
  Qed.


  #[global]
    Instance Monad__ASLPProgSP : Monad ASLPProgSP :=
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
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (~ getProgASLP (retASLPProg x) (fun _ => False) o
                             /\ getProgASLP (retASLPProg x) (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (f a) (fun _ => False) r0
                                   /\ getProgASLP (f a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (~ getProgASLP (f x) (fun _ => False) r0
                      /\ getProgASLP (f x) (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP (retASLPProg x) (fun _ => False) r1
                                  /\ getProgASLP (retASLPProg x) (fun t => t = s1) r1)
                    (fun s1 r1 => r1 = Some (x, s1))
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
      assert (Hc : forall (s : S) (r0 : option (A * S)),
                 (exists o, (~ getProgASLP m (fun _ => False) o
                             /\ getProgASLP m (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (retASLPProg a) (fun _ => False) r0
                                   /\ getProgASLP (retASLPProg a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
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
                    (fun a1 s1 r1 => r1 = Some (a1, s1))
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
      assert (Hc : forall (s : S) (r0 : option (C * S)),
                 (exists o, (~ getProgASLP (bindASLPProg x f) (fun _ => False) o
                             /\ getProgASLP (bindASLPProg x f) (fun t => t = s) o)
                            /\ match o with
                               | Some (b, smid) =>
                                   ~ getProgASLP (g b) (fun _ => False) r0
                                   /\ getProgASLP (g b) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (~ getProgASLP x (fun _ => False) o
                                 /\ getProgASLP x (fun t => t = s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       ~ getProgASLP (bindASLPProg (f a) g)
                                           (fun _ => False) r0
                                       /\ getProgASLP (bindASLPProg (f a) g)
                                            (fun t => t = smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP (bindASLPProg x f) (fun _ => False) r1
                                  /\ getProgASLP (bindASLPProg x f) (fun t => t = s1) r1)
                    (fun s1 r1 =>
                       exists o, (~ getProgASLP x (fun _ => False) o
                                  /\ getProgASLP x (fun t => t = s1) o)
                                 /\ match o with
                                    | Some (a, smid) =>
                                        ~ getProgASLP (f a) (fun _ => False) r1
                                        /\ getProgASLP (f a) (fun t => t = smid) r1
                                    | None => r1 = None
                                    end)
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
                          exists o, (~ getProgASLP (f a1) (fun _ => False) o
                                     /\ getProgASLP (f a1) (fun t => t = s1) o)
                                    /\ match o with
                                       | Some (b, smid) =>
                                           ~ getProgASLP (g b) (fun _ => False) r1
                                           /\ getProgASLP (g b) (fun t => t = smid) r1
                                       | None => r1 = None
                                       end)
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
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (~ getProgASLP x (fun _ => False) o
                             /\ getProgASLP x (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (f a) (fun _ => False) r0
                                   /\ getProgASLP (f a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (~ getProgASLP y (fun _ => False) o
                                 /\ getProgASLP y (fun t => t = s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       ~ getProgASLP (g a) (fun _ => False) r0
                                       /\ getProgASLP (g a) (fun t => t = smid) r0
                                   | None => r0 = None
                                   end)).
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
