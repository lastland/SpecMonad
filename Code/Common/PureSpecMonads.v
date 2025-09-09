From Coq Require Import RelationClasses.
Require Import Coq.Program.Basics.
From Hammer Require Import Hammer Tactics.

Notation "f ∘ g" := (compose f g) (at level 40, left associativity).

Set Implicit Arguments.

Section PrePostMonad.
  Definition PrePost A := prod Prop (A -> Prop).

  Definition ordPrePost {A} (pp1 pp2:PrePost A) : Prop :=
    (fst pp2 -> fst pp1) /\ (forall r, fst pp2 -> snd pp1 r -> snd pp2 r).
  (** This order is tweaked:           ^^^^^^^^^^.
      Necessary for having a Galois connection between PrePost and Pred
      using pp2p and p2pp.
      
      The Galois connection is not used further in proofs. *)

  (** Correctness laws *)
  Theorem strengthen_pre_pp {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordPrePost (P1, Q) (P2, Q).
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post_pp {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordPrePost (P, Q1) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim_pp {A} P (Q1 Q2:A -> Prop) :
    ordPrePost (P, (fun r => Q1 r /\ Q2 r)) (P, Q1) /\
    ordPrePost (P, (fun r => Q1 r /\ Q2 r)) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp {A} (P:Prop) (Q1 Q2:A -> Prop) (m:PrePost A):
    ordPrePost m (P, Q1) ->
    ordPrePost m (P, Q2) ->
    ordPrePost m (P, (fun r => Q1 r /\ Q2 r)).
  Proof. cbv. sfirstorder. Qed.
End PrePostMonad.

Instance : forall {A}, Transitive (@ordPrePost A).
Proof. sfirstorder. Qed.

Instance : forall {A}, Reflexive (@ordPrePost A).
Proof. sfirstorder. Qed.

Section PredMonad.
  Definition Pred A := A -> Prop.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun r => r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun r => exists a, m a /\ k a r.

  Definition ordPred {A} (P1 P2:Pred A) : Prop :=
    forall r, P1 r -> P2 r.
End PredMonad.

Instance : forall {A}, Transitive (@ordPred A).
Proof. sfirstorder. Qed.

Instance : forall {A}, Reflexive (@ordPred A).
Proof. sfirstorder. Qed.

Section RelationPred2PrePost.
  Program Definition p2pp {A} (P:Pred A) : PrePost A :=
    (True, P).

  Program Definition pp2p {A} (pp:PrePost A) : Pred A :=
    fun r => fst pp -> snd pp r.

  Lemma loop_p2pp_pp2p {A} (pp:PrePost A):
    ordPrePost (p2pp (pp2p pp)) pp.
  Proof. cbv. firstorder. Qed. 

  Lemma loop_p2pp_pp2p' {A} (pp:PrePost A):
    ordPrePost pp (p2pp (pp2p pp)).
  Proof. destruct pp as [P Q]. cbv. split. admit. (** impossible to prove **)
  Abort.

  Lemma inverse_pp2p_p2pp {A} (P:Pred A) :
    ordPred P (pp2p (p2pp P)) /\ ordPred (pp2p (p2pp P)) P.
  Proof. cbv. sfirstorder. Qed.

  Lemma adjunction_pp_p {A} (P:Pred A) (pp:PrePost A) :
    ordPred P (pp2p pp) <-> ordPrePost (p2pp P) pp.
  Proof. sfirstorder. Qed.

  Theorem strengthen_pre_pp2p {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordPred (pp2p (P1, Q)) (pp2p (P2, Q)).
  Proof.
    intros HP2iP1.
    apply adjunction_pp_p.
    pose proof (loop_p2pp_pp2p (P1, Q)).
    pose proof (strengthen_pre_pp Q HP2iP1).
    transitivity (P1, Q); assumption.
  Qed.

  Theorem weaken_post_pp2p {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordPred (pp2p (P, Q1)) (pp2p (P, Q2)).
  Proof.
    intros HQ1iQ2.
    apply adjunction_pp_p.
    pose proof (loop_p2pp_pp2p (P, Q1)).
    pose proof (weaken_post_pp P Q1 Q2 HQ1iQ2).
    transitivity (P, Q1); assumption.
  Qed.

  Theorem post_conj_elim_pp2p {A} P (Q1 Q2:A -> Prop) :
    ordPred (pp2p (P, (fun r => Q1 r /\ Q2 r))) (pp2p (P, Q1)) /\
    ordPred (pp2p (P, (fun r => Q1 r /\ Q2 r))) (pp2p (P, Q2)).
  Proof. 
    pose proof (post_conj_elim_pp P Q1 Q2).
    destruct H.
    split; apply adjunction_pp_p;
    pose proof (loop_p2pp_pp2p (P, (fun r => Q1 r /\ Q2 r)));
    transitivity (P, (fun r => Q1 r /\ Q2 r)); assumption.
   Qed.

  Theorem post_conj_intro_pp2p {A} (P:Prop) (Q1 Q2:A -> Prop) (m:Pred A):
    ordPred m (pp2p (P, Q1)) ->
    ordPred m (pp2p (P, Q2)) ->
    ordPred m (pp2p (P, (fun r => Q1 r /\ Q2 r))).
  Proof.
    intros H1 H2.
    apply adjunction_pp_p in H1.
    apply adjunction_pp_p in H2.
    apply adjunction_pp_p.
    pose proof (post_conj_intro_pp H1 H2).
    assumption.
  Qed.
End RelationPred2PrePost.

Section RelationPred2PrePostStandard.
  (** Looking at the standard ordering for PrePost *)
  Definition ordPrePost_standard {A} (pp1 pp2:PrePost A) : Prop :=
    (fst pp2 -> fst pp1) /\ (forall r, snd pp1 r -> snd pp2 r).

  Instance : forall {A}, Transitive (@ordPrePost_standard A).
  Proof. cbn. sfirstorder. Qed.

  Theorem strengthen_pre_pp_standard {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordPrePost_standard (P1, Q) (P2, Q).
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post_pp_standard {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordPrePost_standard (P, Q1) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim_pp_standard {A} P (Q1 Q2:A -> Prop) :
    ordPrePost_standard (P, (fun r => Q1 r /\ Q2 r)) (P, Q1) /\
    ordPrePost_standard (P, (fun r => Q1 r /\ Q2 r)) (P, Q2).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp_standard {A} (P:Prop) (Q1 Q2:A -> Prop) (m:PrePost A):
    ordPrePost_standard m (P, Q1) ->
    ordPrePost_standard m (P, Q2) ->
    ordPrePost_standard m (P, (fun r => Q1 r /\ Q2 r)).
  Proof. cbv. sfirstorder. Qed.    

  Lemma loop_p2pp_pp2p_standard {A} (pp:PrePost A):
    ordPrePost_standard (p2pp (pp2p pp)) pp.
  Proof. cbv. firstorder. destruct pp. apply H. Abort. 

  Lemma loop_p2pp_pp2p_standard {A} (pp:PrePost A):
    ordPrePost_standard pp (p2pp (pp2p pp)).
  Proof. destruct pp as [P Q]. cbv. split. Abort. (** impossible to prove **)

  Lemma adjunction_pp_p_standard {A} (P:Pred A) (pp:PrePost A) :
    ordPred P (pp2p pp) <-> ordPrePost_standard (p2pp P) pp.
  Proof. cbv. split. destruct pp. + admit. + sfirstorder. Abort.

  Theorem strengthen_pre_pp2p_standard {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordPred (pp2p (P1, Q)) (pp2p (P2, Q)).
  Proof. cbv. sfirstorder. Qed.

  Theorem weaken_post_pp2p_standard {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordPred (pp2p (P, Q1)) (pp2p (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_elim_pp2p_standard {A} P (Q1 Q2:A -> Prop) :
    ordPred (pp2p (P, (fun r => Q1 r /\ Q2 r))) (pp2p (P, Q1)) /\
    ordPred (pp2p (P, (fun r => Q1 r /\ Q2 r))) (pp2p (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp2p_standard {A} (P:Prop) (Q1 Q2:A -> Prop) (m:Pred A):
    ordPred m (pp2p (P, Q1)) ->
    ordPred m (pp2p (P, Q2)) ->
    ordPred m (pp2p (P, (fun r => Q1 r /\ Q2 r))).
  Proof. cbv. sfirstorder. Qed.
End RelationPred2PrePostStandard.

Section ForwardPredicateTransformer.
  Definition _SPost A :=
    forall (pre : Prop),
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
      proj1_sig (proj1_sig sp1 pre r) -> proj1_sig (proj1_sig sp2 pre r).
End ForwardPredicateTransformer.

Section RelationPred2SPost.
  Program Definition p2sp {A} (P:Pred A) : SPost A :=
    fun pre r => pre /\ P r.

  Program Definition sp2p {A} (sp:SPost A) : Pred A :=
    sp True.

  Theorem inverse_sp2p_p2sp {A} (P:Pred A) :
    ordPred (sp2p (p2sp P)) P /\ ordPred P (sp2p (p2sp P)).
  Proof. cbv. sfirstorder. Qed.

  Theorem inverse_p2sp_sp2p {A} (sp:SPost A) :
    ordSPost sp (p2sp (sp2p sp)) /\ ordSPost (p2sp (sp2p sp)) sp.
  Proof.
    destruct sp.
    split. split.
    + sfirstorder.
    + unfold sp2p. eauto.
    + cbv. sfirstorder.
  Qed.
End RelationPred2SPost.

Section RelationSPost2PrePost.
  Program Definition pp2sp {A} (pp:PrePost A) : SPost A :=
    (p2sp ∘ pp2p) pp.

  Definition sp2pp {A} (sp:SPost A) : PrePost A :=
    (p2pp ∘ sp2p) sp.

  Lemma loop_pp2sp_sp2pp {A} (sp:SPost A):
    ordSPost sp (pp2sp (sp2pp sp)).
  Proof.
    unfold pp2sp. unfold sp2pp. unfold compose.
    unfold ordSPost.
    intros.
    simpl.
    split.
    - destruct sp. sfirstorder.
    - apply inverse_pp2p_p2pp.
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

  Theorem strengthen_pre_pp2sp {A} (P1 P2:Prop) (Q:A -> Prop) :
    (P2 -> P1) ->
    ordSPost (pp2sp (P1, Q)) (pp2sp (P2, Q)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post_pp2sp {A} (P:Prop) (Q1 Q2:A -> Prop) :
    (forall r, Q1 r -> Q2 r) ->
    ordSPost (pp2sp (P, Q1)) (pp2sp (P, Q2)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim_pp2sp {A} P (Q1 Q2:A -> Prop) :
    ordSPost (pp2sp (P, (fun r => Q1 r /\ Q2 r))) (pp2sp (P, Q1)) /\
    ordSPost (pp2sp (P, (fun r => Q1 r /\ Q2 r))) (pp2sp (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp2sp {A} (P:Prop) (Q1 Q2:A -> Prop) (m:SPost A):
    ordSPost m (pp2sp (P, Q1)) ->
    ordSPost m (pp2sp (P, Q2)) ->
    ordSPost m (pp2sp (P, (fun r => Q1 r /\ Q2 r))).
  Proof. cbv. sfirstorder. Qed.
End RelationSPost2PrePost.