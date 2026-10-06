From ExtLib Require Import Monad.
From Hammer Require Import Tactics.
From Incorrectness Require Import
  Common.Notations Common.Classes Common.PureSpecMonads.

Set Implicit Arguments.

Section OptionMonad.
  Variable A:Type.

  Definition OptionPost := fun A => option A -> Prop.

  #[global] Instance OptionPostT : PostT OptionPost :=
    {|
      ordPost := fun _ Q1 Q2 => forall r, Q1 r -> Q2 r ;
      conjPost := fun _ Q1 Q2 r => Q1 r /\ Q2 r
    |}.

  #[global] Program Instance OptionPrePost : PrePostT PurePre OptionPost :=
    {|
      ordPrePost := fun _ pp1 pp2 =>
    (ordPre (fst pp2) (fst pp1)) /\ (fst pp2 -> ordPost (snd pp1) (snd pp2))
    |}.

  (** Correctness laws *)
  #[global] Instance PurePrePostLaws : PrePostLaws OptionPrePost.
  sfirstorder.
  Qed.
End OptionMonad.

Section PredMonad.
  Definition OptionPred A := OptionPost A.

  Program Definition retPred {A} (a : A) : OptionPred A :=
    fun r => r = Some a.

  Program Definition bindPred {A B} (m : OptionPred A) (k : A -> OptionPred B) : OptionPred B :=
    fun r => exists a, m (Some a) /\ k a r.

  #[global] Instance Monad__Pred : Monad (OptionPred) :=
    {| ret := fun _ => retPred ;
       bind := fun _ _ => bindPred |}.    

  #[global] Instance PredMonad__Pred : PredMonad OptionPred :=
    {| monadPred := Monad__Pred ;
       ordPred := fun {A} P1 P2 => forall r, P1 r -> P2 r |}.

  #[global] Instance PredMonadLaws__Pred : PredMonadLaws OptionPred.
  sfirstorder.
  Qed.
End PredMonad.

Section RelationPred2PrePost.
  #[global] Instance GaloisPure :
    GaloisPrePostPred OptionPred PurePre OptionPost :=
    {| p2pp := fun _ P => (True, P) ;
       pp2p := fun _ pp r => fst pp -> snd pp r
    |}.

  #[global] Instance GaloisPureLaws : 
    GaloisPrePostPredLaws OptionPred PurePre OptionPost.
  sfirstorder.
  Qed.
End RelationPred2PrePost.

Section ForwardPredicateTransformer.
  Definition _SPost A :=
    forall (pre : Prop),
      option A -> {p : Prop | p -> pre}.

  Definition SPost A :=
    { w : _SPost A | forall p q r,
        (p -> q) -> proj1_sig (w p r) -> proj1_sig (w q r)  }.

  Program Definition retSPost {A} (a : A) : SPost A :=
    fun pre r => pre /\ r = Some a.

  Program Definition bindSPost {A B}
    (m : SPost A) (k : A -> SPost B) : SPost B :=
    fun pre b =>
      exists a, k a (m pre (Some a)) b.
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
  Program Definition p2sp {A} (P:OptionPred A) : SPost A :=
    fun pre r => pre /\ P r.

  Program Definition sp2p {A} (sp:SPost A) : OptionPred A :=
    sp True.

  Theorem inverse_sp2p_p2sp {A} (P:OptionPred A) :
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

  Theorem strengthen_pre_pp2sp {A} (P1 P2:PurePre) (Q:OptionPost A) :
    ordPre P2 P1 ->
    ordSPost (pp2sp (P1, Q)) (pp2sp (P2, Q)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post_pp2sp {A} (P:PurePre) (Q1 Q2:OptionPost A) :
    ordPost Q1 Q2 ->
    ordSPost (pp2sp (P, Q1)) (pp2sp (P, Q2)).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim_pp2sp {A} P (Q1 Q2:OptionPost A) :
    ordSPost (pp2sp (P, conjPost Q1 Q2)) (pp2sp (P, Q1)) /\
    ordSPost (pp2sp (P, conjPost Q1 Q2)) (pp2sp (P, Q2)).
  Proof. cbv. sfirstorder. Qed.

  Theorem post_conj_intro_pp2sp {A} (P:PurePre) (Q1 Q2:OptionPost A) (m:SPost A):
    ordSPost m (pp2sp (P, Q1)) ->
    ordSPost m (pp2sp (P, Q2)) ->
    ordSPost m (pp2sp (P, conjPost Q1 Q2)).
  Proof. cbv. sfirstorder. Qed.
End RelationSPost2PrePost.
