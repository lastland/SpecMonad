From Coq Require Import RelationClasses.
Require Import Coq.Program.Basics.
From Hammer Require Import Hammer Tactics.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Set Implicit Arguments.

Section ForwardPredicateTransformer.
  Definition _SPost A := forall (pre : Prop),
      A -> {p : Prop | p -> pre}.

  Definition SPost A :=
    { w : _SPost A | forall p q r,
        (p -> q) -> proj1_sig (w p r) -> proj1_sig (w q r)  }.

  Program Definition retSPost {A} (a : A) : SPost A :=
    fun pre r => pre /\ r = a.

  Program Definition bindSPost {A B}
    (m : SPost A) (k : A -> SPost B) : SPost B :=
    fun pre b =>
      exists a, k a (m pre a) b.
  Next Obligation. sfirstorder. Qed.
  Next Obligation.
    destruct m as [m Hp]; cbn in *.
    exists H0. destruct (k H0) as [ka Hkp] eqn:Hk.
    cbn in *. eapply Hkp; eauto.
  Qed.

  Definition ordSPost {A} (sp1 sp2:SPost A) : Prop :=
    forall pre r,
      proj1_sig (proj1_sig sp2 pre r) -> proj1_sig (proj1_sig sp1 pre r).
  (** !!!! Contravariant *)  
End ForwardPredicateTransformer.

Section PredMonad.

  Definition Pred A := A -> Prop.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun r => r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun r => exists a, m a /\ k a r.

  Definition ordPred {A} (P1 P2:Pred A) : Prop :=
    forall r, P2 r -> P1 r.
  (** !!!! Contravariant *)
End PredMonad.

Section PrePostMonad.
  Variable A : Type.

  Definition PrePost := prod Prop (A -> Prop).

  Definition ordPrePost (pp1 pp2:PrePost) : Prop :=
    (fst pp2 -> fst pp1) /\ (forall r, fst pp2 -> snd pp1 r -> snd pp2 r).
End PrePostMonad.

Section RelationPred2PrePost.

  Program Definition p2pp {A} (P:Pred A) : PrePost A :=
    (True, P).

  Program Definition pp2p {A} (pp:PrePost A) : Pred A :=
    fun r => fst pp -> snd pp r.

  Lemma loop_p2pp_pp2p {A} (pp:PrePost A):
    ordPrePost (p2pp (pp2p pp)) pp.
  Proof.
    destruct pp as [P Q].
    cbv.
    split.
    + sfirstorder.
    + intros r Hpre Hpq.
      specialize (Hpq Hpre).
      sfirstorder.
  Qed.

  Lemma loop_pp2p_p2pp {A} (P:Pred A) :
    ordPred (pp2p (p2pp P)) P.
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Lemma adjunction_pp_p {A} (P:Pred A) (pp:PrePost A) :
    ordPred (pp2p pp) P <-> ordPrePost (p2pp P) pp.
  Proof.
    split.
    + sfirstorder.
    + sfirstorder.
  Qed.
End RelationPred2PrePost.

Section RelationPred2PrePost.
  Program Definition p2sp {A} (P:Pred A) : SPost A :=
    fun pre r => pre /\ P r.

  Program Definition sp2p {A} (sp:SPost A) : Pred A :=
    sp True.

  Theorem inverse_sp2p_p2sp {A} (P:Pred A) :
    ordPred (sp2p (p2sp P)) P.
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem inverse_sp2p_p2sp' {A} (P:Pred A) :
    ordPred P (sp2p (p2sp P)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem inverse_p2sp_sp2p {A} (sp:SPost A) :
    ordSPost (p2sp (sp2p sp)) sp.
  Proof.
    split.
    + destruct sp. sfirstorder.
    + unfold sp2p.
      assert (pre -> True). { sfirstorder. }
      destruct sp.
      simpl in *.
      eauto.
  Qed.

  Theorem inverse_p2sp_sp2p' {A} (sp:SPost A) :
    ordSPost sp (p2sp (sp2p sp)).
  Proof.  
    cbv. destruct sp. sfirstorder.
  Qed.
End RelationPred2PrePost.

Section RelationSPost2PrePost.
  Program Definition pp2sp {A} (pp:PrePost A) : SPost A :=
    (p2sp ∘ pp2p) pp.

  Definition sp2pp {A} (sp:SPost A) : PrePost A :=
    (p2pp ∘ sp2p) sp.

  Lemma loop_pp2sp_sp2pp {A} (sp:SPost A):
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
      sfirstorder. 
  Qed.
  
  Lemma loop_sp2pp_pp2sp {A} (pp:PrePost A):
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

  Lemma adjunction_sp_pp {A} (pp:PrePost A) (sp:SPost A) :
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
      specialize (H P r).
      cbv in H.
      apply H.
      ++ destruct sp. sfirstorder.
      ++ sfirstorder.
    + intros H.
      unfold ordPred in H.
      destruct pp as [P Q].
      cbv.
      intros.
      cbv in H.
      destruct H.      
      split.
      specialize (H1 r).
      ++ destruct sp. hauto.
      ++ destruct sp. intros. apply H1.
      +++ sfirstorder.
      +++ sfirstorder.
  Qed.

  Theorem strengthen_pre {A} (P1 P2:Prop) (Q:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P1, Q)) pre r) -> 
      (P2 -> P1) ->
      proj1_sig (proj1_sig (pp2sp (P2, Q)) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post {A} (P:Prop) (Q1 Q2:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P, Q1)) pre r) -> 
      (forall r, Q1 r -> Q2 r) ->
      proj1_sig (proj1_sig (pp2sp (P, Q2)) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim {A} P (Q1 Q2:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P, (fun r => Q1 r /\ Q2 r))) pre r) ->
      proj1_sig (proj1_sig (pp2sp (P, Q1)) pre r) /\
      proj1_sig (proj1_sig (pp2sp (P, Q2)) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_intro {A} (P:Prop) (Q1 Q2:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P, Q1)) pre r) -> 
      proj1_sig (proj1_sig (pp2sp (P, Q2)) pre r) -> 
      proj1_sig (proj1_sig (pp2sp (P, (fun r => Q1 r /\ Q2 r))) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.
End RelationSPost2PrePost.