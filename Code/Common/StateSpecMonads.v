From Coq Require Import RelationClasses.
Require Import Coq.Program.Basics.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

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

  Definition ordSPost {S A} (sp1 sp2:SPost S A) : Prop :=
    forall s0 pre r s1,
      proj1_sig (proj1_sig sp2 s0 pre r s1) -> proj1_sig (proj1_sig sp1 s0 pre r s1).
  (** !!!! Contravariant *)  
End ForwardPredicateTransformer.

Section PredMonad.
  Definition Pred S A := S -> A -> S -> Prop.

  Program Definition retPred {S A} (a : A) : Pred S A :=
    fun s0 r s1 => r = a /\ s0 = s1.

  Program Definition bindPred {S A B} (m : Pred S A) (k : A -> Pred S B) : Pred S B :=
    fun s0 r s1 => exists a s', m s0 a s' /\ k a s' r s1.

  Definition ordPred {S A} (P1 P2:Pred S A) : Prop :=
    forall s0 r s1, P2 s0 r s1 -> P1 s0 r s1.
  (** !!!! Contravariant *)

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
    ordPred (pp2p pp) P <-> ordPrePost (p2pp P) pp.
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
    ordSPost (p2sp (sp2p sp)) sp.
  Proof.
    split.
    + destruct sp. sfirstorder.
    + unfold sp2p.
      destruct sp.
      eauto.
  Qed.

  Theorem inverse_p2sp_sp2p' {S A} (sp:SPost S A) :
    ordSPost sp (p2sp (sp2p sp)).
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
    ordSPost (pp2sp (sp2pp sp)) sp.
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
    ordSPost (pp2sp pp) sp <-> ordPrePost (sp2pp sp) pp.
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
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp (P1, Q)) s0 pre r s1) -> 
      (P2 s0 -> P1 s0) ->
      proj1_sig (proj1_sig (pp2sp (P2, Q)) s0 pre r s1).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post {S A} (P:S -> Prop) (Q1 Q2:S -> A -> S -> Prop) :
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp (P, Q1)) s0 pre r s1) -> 
      (Q1 s0 r s1 -> Q2 s0 r s1) ->
      proj1_sig (proj1_sig (pp2sp (P, Q2)) s0 pre r s1).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim {S A} P (Q1 Q2:S -> A -> S -> Prop) :
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) s0 pre r s1) ->
      proj1_sig (proj1_sig (pp2sp (P, Q1)) s0 pre r s1) /\
      proj1_sig (proj1_sig (pp2sp (P, Q2)) s0 pre r s1).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_intro {S A} (P:S -> Prop) (Q1 Q2:S -> A -> S -> Prop) :
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp (P, Q1)) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp (P, Q2)) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp (P, (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1))) s0 pre r s1).
  Proof.
    cbv.
    sfirstorder.
  Qed.
End RelationSPost2PrePost.