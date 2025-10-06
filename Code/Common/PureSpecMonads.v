From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.Notations Common.Classes.

Set Implicit Arguments.

Section PrePostMonad.
  Variable A:Type.

  #[global] Instance PurePre : PreT :=
    {|
      Pre := Prop ;
      ordPre := fun P1 P2 => P1 -> P2 
    |}.

  #[global] Instance PurePost : PostT :=
    {|
      Post := fun A => A -> Prop ;
      ordPost := fun _ Q1 Q2 => forall r, Q1 r -> Q2 r ;
      conjPost := fun _ Q1 Q2 r => Q1 r /\ Q2 r
    |}.

  #[global] Program Instance PurePrePost : PrePostT PurePre PurePost :=
    {|
      ordPrePost := fun _ pp1 pp2 =>
    (ordPre (fst pp2) (fst pp1)) /\ (fst pp2 -> ordPost (snd pp1) (snd pp2))
  (** This order is tweaked:           ^^^^^^^^^^.
      Necessary for having a Galois connection between PrePost and Pred
      using pp2p (P,Q) = fun r -> Q r and p2pp P = (True, P).
      
      The Galois connection is not used further in proofs. *)
    |}.

  (** Correctness laws *)
  #[global] Instance PurePrePostLaws : PrePostLaws PurePrePost.
  sfirstorder.
  Qed.
End PrePostMonad.

Section PredMonad.
  Definition Pred A := Post A.

  Program Definition retPred {A} (a : A) : Pred A :=
    fun r => r = a.

  Program Definition bindPred {A B} (m : Pred A) (k : A -> Pred B) : Pred B :=
    fun r => exists a, m a /\ k a r.

  #[global] Instance Monad__Pred : Monad Pred :=
    {| ret := fun _ => retPred ;
       bind := fun _ _ => bindPred |}.

  #[global] Instance PredMonad__Pred : PredMonad Pred :=
    {| monadPred := Monad__Pred ;
       ordPred := fun {A} P1 P2 => forall r, P1 r -> P2 r |}.

  #[global] Instance PredMonadLaws__Pred : PredMonadLaws Pred.
  sfirstorder.
  Qed.
    
End PredMonad.

Section RelationPred2PrePost.

  #[global] Instance GaloisPure :
    GaloisPrePostPred Pred PurePre PurePost :=
    {| p2pp := fun _ P => (True, P) ;
       pp2p := fun _ pp r => fst pp -> snd pp r
    |}.

  #[global] Instance GaloisPureLaws : 
    GaloisPrePostPredLaws Pred PurePre PurePost.
  sfirstorder.
  Qed.

  Lemma loop_p2pp_pp2p' {A} (pp:PrePost A):
    ordPrePost pp (p2pp (pp2p pp)).
  Proof. destruct pp as [P Q]. cbv. Abort. (** impossible to prove **)

  Theorem strengthen_pre_pp2p {A} (P1 P2:Pre) (Q:Post A) :
    ordPre P2 P1 ->
    ordPred (pp2p (P1, Q)) (pp2p (P2, Q)).
  Proof.
    apply strengthen_pre_pp2p.
    apply PurePrePostLaws. apply GaloisPureLaws.
  Qed.

  Theorem weaken_post_pp2p {A} (P:Pre) (Q1 Q2:Post A) :
    ordPost Q1 Q2 ->
    ordPred (pp2p (P, Q1)) (pp2p (P, Q2)).
  Proof.
    apply weaken_post_pp2p.
    apply PurePrePostLaws. apply GaloisPureLaws.
  Qed.

  Theorem post_conj_elim_pp2p {A} P (Q1 Q2:Post A) :
    ordPred (pp2p (P, conjPost Q1 Q2)) (pp2p (P, Q1)) /\
    ordPred (pp2p (P, conjPost Q1 Q2)) (pp2p (P, Q2)).
  Proof.
    apply post_conj_elim_pp2p.
    apply PurePrePostLaws. apply GaloisPureLaws.
  Qed.

  Theorem post_conj_intro_pp2p {A} (P:Pre) (Q1 Q2:Post A) (m:Pred A):
    ordPred m (pp2p (P, Q1)) ->
    ordPred m (pp2p (P, Q2)) ->
    ordPred m (pp2p (P, conjPost Q1 Q2)).
  Proof.
    apply post_conj_intro_pp2p.
    apply PurePrePostLaws. apply GaloisPureLaws.
  Qed.
End RelationPred2PrePost.

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
  
  Hint Unfold pp2sp sp2pp ordPost : spec_monads.

  Lemma loop_pp2sp_sp2pp {A} (sp:SPost A):
    ordSPost sp (pp2sp (sp2pp sp)).
  Proof.
    autounfold with spec_monads.
    intros; split; destruct sp. 
    - sfirstorder.
    - cbv in *. sfirstorder.
  Qed.
  
  Lemma loop_sp2pp_pp2sp {A} (pp:PrePost A):
    ordPrePost (sp2pp (pp2sp pp)) pp.
  Proof.
    autounfold with spec_monads.
    intros; split; destruct pp; sfirstorder.
  Qed.

  Lemma adjunction_sp_pp {A} (pp:PrePost A) (sp:SPost A) :
    ordSPost sp (pp2sp pp) <-> ordPrePost (sp2pp sp) pp.
  Proof.
    autounfold with spec_monads.
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
      ++ destruct sp. hauto.
      ++ destruct sp. intros. apply H1.
      +++ sfirstorder.
      +++ sfirstorder.
  Qed.

  Theorem strengthen_pre_pp2sp {A} (P1 P2:Pre) (Q:Post A) :
    ordPre P2 P1 ->
    ordSPost (pp2sp (P1, Q)) (pp2sp (P2, Q)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post_pp2sp {A} (P:Pre) (Q1 Q2:Post A) :
    ordPost Q1 Q2 ->
    ordSPost (pp2sp (P, Q1)) (pp2sp (P, Q2)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim_pp2sp {A} P (Q1 Q2:Post A) :
    ordSPost (pp2sp (P, conjPost Q1 Q2)) (pp2sp (P, Q1)) /\
    ordSPost (pp2sp (P, conjPost Q1 Q2)) (pp2sp (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp2sp {A} (P:Pre) (Q1 Q2:Post A) (m:SPost A):
    ordSPost m (pp2sp (P, Q1)) ->
    ordSPost m (pp2sp (P, Q2)) ->
    ordSPost m (pp2sp (P, conjPost Q1 Q2)).
  Proof. cbv. sfirstorder. Qed.
End RelationSPost2PrePost.
