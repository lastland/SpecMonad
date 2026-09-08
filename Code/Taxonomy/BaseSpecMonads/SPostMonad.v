(** * [SPost]: the strongest-postcondition (forward predicate transformer) monad

        [Over p    := { q : Prop | q -> p }]        propositions implying [p]
        [SPost A   := { f : forall p:Prop, A -> Over p | monotone in p }]

        [ret a    := fun p y => (p /\ a = y)]
        [bind m k := fun p y => exists a, (k a) (m p a) y]

    A forward transformer: given a precondition [p] it says, of each result
    [a], what is known after — and that knowledge always IMPLIES [p], which is
    what the [Over] subtype records.  [bind] threads [m]'s postcondition at
    [a] in as the precondition of [k a]; that is the whole content of forward
    composition.

    This is DM4all's [SP] / [ForwardPredTransformer]
    ([sprop/SpecificationMonads.v], [Section StrongestPostcondition]),
    transcribed from [SProp] to [Prop].  DM4all proves the laws as equalities
    and so needs [sprop_ext] and functional extensionality; taking [Eq1] to be
    pointwise iff on the underlying propositions, the same laws hold here with
    NO axioms.

    Both carrier conditions earn their keep in the proofs: [over] supplies the
    witness that makes [bind_bind] go through left-to-right, and monotonicity
    is what lets a precondition be replaced by an equivalent one.

    Wrapped in a module: [Taxonomy/SPost.v] uses the name [SPost] for the
    strongest-postcondition ARROWS over [SPRecord], and [SPSpecMonads.v] binds
    [SPPure] to the unrestricted [Prop -> A -> Prop]. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.

Module SPM.

  (* ================================================================= *)
  (** ** [Over p]: propositions implying [p]                           *)
  (* ================================================================= *)

  Record Over (p : Prop) : Type := mkOver { base : Prop ; over : base -> p }.

  Arguments mkOver {p} base over.
  Arguments base {p}.
  Arguments over {p}.

  (* ================================================================= *)
  (** ** The carrier                                                   *)
  (* ================================================================= *)

  Definition SPostT (A : Type) : Type := forall (p : Prop), A -> Over p.

  Definition sp_mono {A} (f : SPostT A) : Prop :=
    forall (p1 p2 : Prop) (a : A),
      (p1 -> p2) -> base (f p1 a) -> base (f p2 a).

  Definition SPost (A : Type) : Type := { f : SPostT A | sp_mono f }.

  (** [app m p a] is [m]'s postcondition at precondition [p] and result [a]. *)
  Definition app {A} (m : SPost A) (p : Prop) (a : A) : Prop :=
    base (proj1_sig m p a).

  Lemma app_over {A} (m : SPost A) (p : Prop) (a : A) : app m p a -> p.
  Proof. exact (over (proj1_sig m p a)). Qed.

  Lemma app_mono {A} (m : SPost A) (p1 p2 : Prop) (a : A) :
    (p1 -> p2) -> app m p1 a -> app m p2 a.
  Proof. exact (proj2_sig m p1 p2 a). Qed.

  (* ================================================================= *)
  (** ** [ret] and [bind]                                              *)
  (* ================================================================= *)

  Definition retSPT {A} (a : A) : SPostT A :=
    fun p y => mkOver (p /\ a = y) (fun H => proj1 H).

  Lemma retSP_mono {A} (a : A) : sp_mono (retSPT a).
  Proof.
    intros p1 p2 y Himp H. cbn in *.
    split; [ exact (Himp (proj1 H)) | exact (proj2 H) ].
  Qed.

  Definition retSP {A} (a : A) : SPost A := exist _ (retSPT a) (retSP_mono a).

  Lemma bind_over {A B} (m : SPost A) (k : A -> SPost B) (p : Prop) (y : B) :
    (exists a, app (k a) (app m p a) y) -> p.
  Proof.
    intros [a H]. exact (app_over m p a (app_over (k a) (app m p a) y H)).
  Qed.

  Definition bindSPT {A B} (m : SPost A) (k : A -> SPost B) : SPostT B :=
    fun p y => mkOver (exists a, app (k a) (app m p a) y) (bind_over m k p y).

  Lemma bindSP_mono {A B} (m : SPost A) (k : A -> SPost B) :
    sp_mono (bindSPT m k).
  Proof.
    intros p1 p2 y Himp H. cbn in *. destruct H as [a H]. exists a.
    exact (app_mono (k a) _ _ y (app_mono m p1 p2 a Himp) H).
  Qed.

  Definition bindSP {A B} (m : SPost A) (k : A -> SPost B) : SPost B :=
    exist _ (bindSPT m k) (bindSP_mono m k).

  #[global]
  Instance Monad_SPost : Monad SPost := {
    ret  := @retSP ;
    bind := @bindSP
  }.

  (** Pointwise equivalence of the underlying propositions. *)
  #[global]
  Instance Eq1_SPost : Eq1 SPost :=
    fun A m1 m2 => forall p a, app m1 p a <-> app m2 p a.

  (** [app] of [ret] and [bind], for rewriting. *)

  Lemma app_ret {A} (a : A) p y : app (retSP a) p y <-> (p /\ a = y).
  Proof. split; intro H; exact H. Qed.

  Lemma app_bind {A B} (m : SPost A) (k : A -> SPost B) p y :
    app (bindSP m k) p y <-> (exists a, app (k a) (app m p a) y).
  Proof. split; intro H; exact H. Qed.

End SPM.

(* ================================================================= *)
(** ** Monad laws                                                    *)
(* ================================================================= *)

Module SPMFacts.
  Import SPM.

  #[global]
  Instance Eq1Equivalence_SPost : @Eq1Equivalence SPost _ Eq1_SPost.
  Proof.
    constructor; repeat intro; unfold eq1, Eq1_SPost in *.
    - reflexivity.
    - symmetry. apply H.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  #[global]
  Instance MonadLawsE_SPost : @MonadLawsE SPost Eq1_SPost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. intros p y. cbn. split.
      + intros [a H].
        (* [over] on the inner application recovers [p /\ x = a] *)
        destruct (app_over (f a) (app (retSP x) p a) y H) as [Hp Heq].
        subst a. exact (app_mono (f x) _ p y (fun H0 => proj1 H0) H).
      + intro H. exists x.
        exact (app_mono (f x) p _ y (fun Hp => conj Hp eq_refl) H).
    - (* bind_ret_r *)
      intros A m p a. cbn. split.
      + intros [a' [H Heq]]. subst a'. exact H.
      + intro H. exists a. split; [ exact H | reflexivity ].
    - (* bind_bind *)
      intros A B C m f g p z. cbn. split.
      + intros [b H].
        (* [over] hands us the intermediate witness the RHS needs *)
        destruct (app_over (g b) _ z H) as [a Ha].
        exists a, b.
        exact (app_mono (g b) _ _ z (fun _ => Ha) H).
      + intros [a [b H]]. exists b.
        exact (app_mono (g b) _ _ z (fun Hf => ex_intro _ a Hf) H).
    - (* Proper_bind *)
      intros A B m1 m2 Hm k1 k2 Hk p y. cbn.
      unfold eq1, Eq1_SPost in Hm, Hk. split.
      + intros [a H]. exists a.
        apply (app_mono (k2 a) (app m1 p a) (app m2 p a) y
                 (fun H0 => proj1 (Hm p a) H0)).
        exact (proj1 (Hk a (app m1 p a) y) H).
      + intros [a H]. exists a.
        apply (app_mono (k1 a) (app m2 p a) (app m1 p a) y
                 (fun H0 => proj2 (Hm p a) H0)).
        exact (proj2 (Hk a (app m2 p a) y) H).
  Qed.

End SPMFacts.

(* Initial attempts based on SPost and Kenji's work *)

Section KenjiPureSP.
  Definition Monotone {A} (w : SPPure A) : Prop :=
    forall (p q : Prop) (a : A), (p -> q) -> w p a -> w q a.

  Definition Codomain {A} (w : SPPure A) : Prop :=
    forall (p : Prop) (a : A), w p a -> p.

  Definition KenjiPureSP (A : Type) : Type := { w : SPPure A | Monotone w /\ Codomain w }.

  Definition getKenjiPureSP {A} (w : KenjiPureSP A) : SPPure A := proj1_sig w.

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
  
  Definition MonotoneS {A} (w : SPStExc A) : Prop :=
    forall (p q : S -> Prop) (r : option (A * S)), (forall (s : S), p s -> q s) -> w p r -> w q r.

  Definition CodomainS {A} (w : SPStExc A) : Prop :=
    forall (p : S -> Prop) (r : option (A * S)), w p r -> (exists s, p s).

  Definition KenjiProgSP (A : Type) : Type := { w : SPStExc A | MonotoneS w /\ CodomainS w }.

  Definition getKenjiProgSP {A} (w : KenjiProgSP A) : SPStExc A := proj1_sig w.

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

Section KenjiPureDSLP.
  Definition CodomainDSLP {A} (w : SPPure A) : Prop :=
    forall (p : Prop) (a : A), p -> w p a.

  Definition KenjiPureDSLP {A} (w : SPPure A) : Prop := Monotone w /\ CodomainDSLP w.
End KenjiPureDSLP.


(* ================================================================= *)
(** * Kenji-style [SPSt]: the terminating-slice twin of the above      *)
(* ================================================================= *)
(* --- Kenji-style simpler SPStExc, terminating slice --- *)

Module StKenji.
  Import StTrans.
Section KenjiProgSP.
  Variable S : Type.

  Definition MonotoneS {A} (w : SPSt A) : Prop :=
    forall (p q : S -> Prop) (r : A * S), (forall (s : S), p s -> q s) -> w p r -> w q r.

  Definition CodomainS {A} (w : SPSt A) : Prop :=
    forall (p : S -> Prop) (r : A * S), w p r -> (exists s, p s).

  Definition KenjiProgSP (A : Type) : Type :=
    { w : SPSt A | MonotoneS w /\ CodomainS w }.

  Definition getKenjiProgSP {A} (w : KenjiProgSP A) : SPSt A := proj1_sig w.

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

End StKenji.
