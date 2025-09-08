From Coq Require Import RelationClasses.
Require Import Coq.Program.Basics.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Hint Unfold compose : mst.

Set Implicit Arguments.

Section ForwardPredicateTransformer.
  Definition _SPost S A :=
    forall (s0 : S) (pre : Prop),
      A -> S -> {p : Prop | p -> pre}.

  Definition SPost S A :=
    { w : _SPost S A | forall s0 p q r s1,
        (p -> q) -> proj1_sig (w s0 p r s1) -> proj1_sig (w s0 q r s1)  }.

  Program Definition retSPost {S A} (a : A) : SPost S A :=
    fun s0 pre r s1 => pre /\ r = a /\ s0 = s1.

  Program Definition bindSPost {S A B}
    (m : SPost S A) (k : A -> SPost S B) : SPost S B :=
    fun s0 pre b s1 =>
      exists a s', k a s' (m s0 pre a s') b s1.
  Next Obligation. sfirstorder. Qed.
  Next Obligation.
    destruct m as [m Hp]; cbn in *.
    exists H0. exists H1. destruct (k H0) as [ka Hkp] eqn:Hk.
    cbn in *. eapply Hkp; eauto.
  Qed.

    Program Definition getSPost {S} : SPost S S :=
    fun s0 pre r s1 => r = s0 /\ s1 = s0 /\ pre.

  Program Definition putSPost {S} (s : S) : SPost S unit :=
    fun s0 pre r s1 => pre /\ s1 = s0.

  #[global] Instance Monad__SPost {S} : Monad (SPost S) :=
    {| ret := fun _ => retSPost ;
       bind := fun _ _ => bindSPost |}.

  #[global] Instance MonadState__SPost {S} : MonadState S (SPost S) :=
    {| get := getSPost ;
       put := putSPost |}.

  Definition ordSPost {S A} (sp1 sp2:SPost S A) : Prop :=
    forall s0 pre r s1,
      proj1_sig (proj1_sig sp1 s0 pre r s1) -> proj1_sig (proj1_sig sp2 s0 pre r s1).

  Instance : forall {S A}, Transitive (@ordSPost S A).
  Proof. cbn. sfirstorder. Qed.
End ForwardPredicateTransformer.

Hint Unfold getSPost putSPost retSPost bindSPost ordSPost : mst.

Section PredMonad.
  Definition Pred S A := S -> A -> S -> Prop.

  Program Definition retPred {S A} (a : A) : Pred S A :=
    fun s0 r s1 => r = a /\ s0 = s1.

  Program Definition bindPred {S A B} (m : Pred S A) (k : A -> Pred S B) : Pred S B :=
    fun s0 r s1 => exists a s', m s0 a s' /\ k a s' r s1.

  Definition ordPred {S A} (P1 P2:Pred S A) : Prop :=
    forall s0 r s1, P1 s0 r s1 -> P2 s0 r s1.

  Instance : forall {S A}, Transitive (@ordPred S A).
  Proof. cbv. sfirstorder. Qed.

  Program Definition getPred {S} : Pred S S :=
    fun s0 r s1 => r = s0 /\ s1 = s0.

  Program Definition putPred {S} (s : S) : Pred S unit :=
    fun s0 r s1 => s1 = s.

  #[global] Instance Monad__Pred {S} : Monad (Pred S) :=
    {| ret := fun _ => retPred ;
       bind := fun _ _ => bindPred |}.

  #[global] Instance MonadState__Pred {S} : MonadState S (Pred S) :=
    {| get := getPred ;
       put := putPred |}.
End PredMonad.

Section PrePostMonad.
  Definition PrePost S A := prod (S -> Prop) (S -> A -> S -> Prop).

  Definition ordPrePost {S A} (pp1 pp2:PrePost S A) : Prop :=
    (forall s0, fst pp2 s0 -> fst pp1 s0) /\ (forall s0 r s1, fst pp2 s0 -> (snd pp1) s0 r s1 -> snd pp2 s0 r s1).

  Instance : forall {S A}, Transitive (@ordPrePost S A).
  Proof. cbv. intros S A [Px Qx] [Py Qy] [Pz Qz] hxy hyz.
          sfirstorder. Qed.    
End PrePostMonad.

Section RelationPred2PrePost.

  Program Definition p2pp {S A} (P:Pred S A) : PrePost S A :=
    (fun _ => True, P).

  Program Definition pp2p {S A} (pp:PrePost S A) : Pred S A :=
    fun s0 r s1 => fst pp s0 -> snd pp s0 r s1.

  Lemma loop_p2pp_pp2p {S A} (pp:PrePost S A):
    ordPrePost (p2pp (pp2p pp)) pp.
  Proof.
    destruct pp as [P Q].
    cbv.
    split.
    + sfirstorder.
    + intros r Hpre Hpq.
      sfirstorder.
  Qed.

  Lemma loop_p2pp_pp2p' {S A} (pp:PrePost S A):
    ordPrePost pp (p2pp (pp2p pp)).
  Proof.
    destruct pp as [P Q].
    cbv.
    split.
    + admit. (** impossible to prove **)
    + intros r Hpre Hpq.
      sfirstorder.
  Abort.

  Lemma loop_pp2p_p2pp {S A} (P:Pred S A) :
    ordPred (pp2p (p2pp P)) P.
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Lemma loop_pp2p_p2pp' {S A} (P:Pred S A) :
    ordPred P (pp2p (p2pp P)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Lemma adjunction_pp_p {S A} (P:Pred S A) (pp:PrePost S A) :
    ordPred P (pp2p pp) <-> ordPrePost (p2pp P) pp.
  Proof.
    split.
    + sfirstorder.
    + sfirstorder.
  Qed.
End RelationPred2PrePost.

Section RelationPred2SPost.
  Program Definition p2sp {S A} (P:Pred S A) : SPost S A :=
    fun s0 pre r s1 => pre /\ P s0 r s1.

  Program Definition sp2p {S A} (sp:SPost S A) : Pred S A :=
    fun s0 => sp s0 True.

  Theorem inverse_sp2p_p2sp {S A} (P:Pred S A) :
    ordPred (sp2p (p2sp P)) P.
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem inverse_sp2p_p2sp' {S A} (P:Pred S A) :
    ordPred P (sp2p (p2sp P)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem inverse_p2sp_sp2p {S A} (sp:SPost S A) :
    ordSPost sp (p2sp (sp2p sp)).
  Proof.
    split.
    + destruct sp. sfirstorder.
    + unfold sp2p.
      destruct sp.
      eauto.
  Qed.

  Theorem inverse_p2sp_sp2p' {S A} (sp:SPost S A) :
    ordSPost (p2sp (sp2p sp)) sp.
  Proof.  
    cbv. destruct sp. 
    intros.
    specialize (p s0 True pre r s1).
    sfirstorder.
  Qed.
End RelationPred2SPost.

Section RelationSPost2PrePost.
  Program Definition pp2sp {S A} (pp:PrePost S A) : SPost S A :=
    (p2sp ∘ pp2p) pp.

  Definition sp2pp {S A} (sp:SPost S A) : PrePost S A :=
    (p2pp ∘ sp2p) sp.

  Lemma loop_pp2sp_sp2pp {S A} (sp:SPost S A):
    ordSPost sp (pp2sp (sp2pp sp)).
  Proof.
    unfold pp2sp. unfold sp2pp. unfold compose.
    unfold ordSPost.
    intros.
    simpl.
    split.
    - destruct sp. sfirstorder.
    - apply loop_pp2p_p2pp.
      cbv.
      destruct sp.
      cbv in *.
      specialize (p s0 pre True r s1).
      sfirstorder. 
  Qed.
  
  Lemma loop_sp2pp_pp2sp {S A} (pp:PrePost S A):
    ordPrePost (sp2pp (pp2sp pp)) pp.
  Proof.
    unfold pp2sp. unfold sp2pp. unfold compose.
    unfold ordPrePost.
    simpl.
    destruct pp as [P Q].
    cbv.
    split.
    - sfirstorder.
    - intros r Hpre Hpq.
      sfirstorder.
  Qed.

  Lemma adjunction_sp_pp {S A} (pp:PrePost S A) (sp:SPost S A) :
    ordSPost sp (pp2sp pp) <-> ordPrePost (sp2pp sp) pp.
  Proof.
    unfold sp2pp. unfold pp2sp. unfold compose.
    split.
    + intros H. 
      apply adjunction_pp_p.
      unfold ordPred.
      destruct pp as [P Q].
      cbv.
      intros.
      specialize (H s0 (P s0) r s1).
      cbv in H.
      apply H.
      ++ destruct sp. specialize (p s0 True (P s0) r s1). sfirstorder.
      ++ sfirstorder.
    + intros H.
      unfold ordPred in H.
      destruct pp as [P Q].
      cbv.
      intros.
      cbv in H.
      destruct H.      
      split.
      specialize (H1 s0 r s1).
      ++ destruct sp. hauto.
      ++ destruct sp. intros. apply H1.
      +++ sfirstorder.
      +++ specialize (p s0 pre True r s1). sfirstorder. 
  Qed.

  Theorem strengthen_pre {S A} (P1 P2:S -> Prop) (Q:S -> A -> S -> Prop) :
    (forall s0, (P2 s0 -> P1 s0)) ->
    ordSPost (pp2sp (P1, Q)) (pp2sp (P2, Q)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post {S A} (P:S -> Prop) (Q1 Q2:S -> A -> S -> Prop) :
    (forall s0 r s1, (Q1 s0 r s1 -> Q2 s0 r s1)) -> 
      ordSPost (pp2sp (P, Q1)) (pp2sp (P, Q2)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim {S A} P (Q1 Q2:S -> A -> S -> Prop) :
    ordSPost (pp2sp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) (pp2sp (P, Q1)) /\
    ordSPost (pp2sp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) (pp2sp (P, Q2)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_intro {S A} (P:S -> Prop) (Q1 Q2:S -> A -> S -> Prop) (m:SPost S A) :
    ordSPost (pp2sp (P, Q1)) m ->
    ordSPost (pp2sp (P, Q2)) m ->
    ordSPost (pp2sp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) m.
  Proof.
    unfold ordSPost, pp2sp, p2sp, compose, pp2p. simpl.
    intros.
    specialize H with s0 pre r s1.
    specialize H0 with s0 pre r s1.
    sfirstorder.
  Qed.
End RelationSPost2PrePost.


Section WeakestPreconditionTransformer.

  Definition _WP S A :=
    (A -> S -> Prop) -> (S -> Prop).

  Definition wp_monotonicity {S A} (w:_WP S A) : Prop := 
    forall p q,
      (forall r s1, p r s1 -> q r s1) -> 
        (forall s0, w p s0 -> w q s0).    

  Definition WP S A :=
    { w : _WP S A | wp_monotonicity w }.

  Definition ordWP {S A} (m1 m2 : WP S A) : Prop :=
    forall p s0, proj1_sig m1 p s0 -> proj1_sig m2 p s0.

  Instance : forall {S A}, Transitive (@ordWP S A).
  Proof. cbn. sfirstorder. Qed.

  Program Definition retWP {S A} (a : A) : WP S A :=
    fun p s0 => p a s0.
  Next Obligation. sfirstorder. Qed.

  Program Definition bindWP {S A B}
    (m : WP S A) (k : A -> WP S B) : WP S B :=
    fun p => m (fun a s1 => k a p s1).
  Next Obligation.
    destruct m as [m Hmm].
    (* destruct k as [k' Hkm]. *)
    unfold wp_monotonicity in *. simpl.
    intros.
    assert (forall a s1, proj1_sig (k a) p s1 -> proj1_sig (k a) q s1). {
      simpl. intros. destruct (k a) as [ka Hkm]. unfold wp_monotonicity in Hkm. 
      simpl.
      simpl in H1.
      specialize Hkm with p q s1. apply Hkm. sfirstorder. sfirstorder.
    }

    specialize Hmm with (fun a s1 => proj1_sig (k a) p s1) (fun a s1 => proj1_sig (k a) q s1) s0.
    apply Hmm. sfirstorder. sfirstorder.
  Qed.

  Program Definition getWP {S} : WP S S :=
    fun p s0 => p s0 s0.
  Next Obligation. sfirstorder. Qed.

  Program Definition putWP {S} (s : S) : WP S unit :=
    fun p s0 => p tt s.
  Next Obligation. sfirstorder. Qed.

  #[global] Instance Monad__WP {S} : Monad (WP S) :=
    {| ret := fun _ => retWP ;
       bind := fun _ _ => bindWP |}.

  #[global] Instance MonadState__WP {S} : MonadState S (WP S) :=
    {| get := getWP ;
       put := putWP |}.
End WeakestPreconditionTransformer.

Hint Unfold getWP putWP retWP bindWP ordWP : mst.

Section RelationWP2PrePost.

  Definition wp2pp {S A} (w : WP S A) : (S -> Prop) * (S -> A -> S -> Prop) :=
    (proj1_sig w (fun _ _ => True), fun s0 a s1 => forall p, proj1_sig w p s0 -> p a s1).

  Program Definition pp2wp {S A} (pp:PrePost S A) : WP S A :=
    fun p s0 => fst pp s0 /\ (forall r s1, snd pp s0 r s1 -> p r s1).
  Next Obligation. cbv. sfirstorder. Qed.

  Theorem strengthen_pre_pp2wp {S A} (P1 P2:S -> Prop) (Q:S -> A -> S -> Prop) :
    (forall s0, P2 s0 -> P1 s0) ->
      ordWP (pp2wp (P2, Q)) (pp2wp (P1, Q)) .
  Proof.
    cbv.
    intros.
    split.
    + sfirstorder.
    + sfirstorder.
  Qed.

  Theorem weaken_post_pp2wp {S A} (P:S -> Prop) (Q1 Q2:S -> A -> S -> Prop) :
    (forall s0 r s1, Q1 s0 r s1 -> Q2 s0 r s1) ->
      ordWP (pp2wp (P, Q2)) (pp2wp (P, Q1)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim_pp2wp {S A} P (Q1 Q2:S -> A -> S -> Prop) :
    ordWP (pp2wp (P, Q1)) (pp2wp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) /\
    ordWP (pp2wp (P, Q2)) (pp2wp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_intro_pp2wp {S A} (P:S -> Prop) (Q1 Q2:S -> A -> S -> Prop) (m:WP S A) :
    ordWP (pp2wp (P, Q1)) m ->
    ordWP (pp2wp (P, Q2)) m ->
    ordWP (pp2wp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) m.
  Proof.
    unfold ordWP, pp2wp. simpl.
    intros.
    
    specialize H with (fun r s1 => Q2 s0 r s1 -> p r s1) s0.
  Admitted.
End RelationWP2PrePost.

Section RelationWP2Pred.
  Definition wp2p {S A} (w : WP S A) : Pred S A :=
    (pp2p ∘ wp2pp) w.

  Definition p2wp {S A} (P:Pred S A) : WP S A :=
    (pp2wp ∘ p2pp) P.
  
End RelationWP2Pred.