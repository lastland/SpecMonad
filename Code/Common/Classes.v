From Coq Require Import RelationClasses Relation_Definitions.
From ExtLib Require Import Monad MonadLaws.
From Hammer Require Import Hammer Tactics.

Class PreT :=
  {
    Pre : Type ;
    ordPre : Pre -> Pre -> Prop
  }.

Class PostT :=
  {
    Post : Type -> Type ;
    ordPost : forall {A}, Post A -> Post A -> Prop ;
    conjPost : forall {A}, Post A -> Post A -> Post A
  }.

Class PrePostT (p : PreT) (q : PostT) :=
  {
    PrePost A := prod Pre (Post A) ;
    ordPrePost : forall {A}, relation (PrePost A) 
  }.

Class PrePostLaws {p q} (pp : PrePostT p q) :=
  {
    strengthen_pre_pp :
      forall A (P1 P2:Pre) (Q:Post A),
        ordPre P2 P1 -> ordPrePost (P1, Q) (P2, Q);
    weaken_post_pp : 
      forall A (P:Pre) (Q1 Q2:Post A),
        ordPost Q1 Q2 -> ordPrePost (P, Q1) (P, Q2) ;
    post_conj_elim_pp :
      forall A P (Q1 Q2:Post A),
        ordPrePost (P, conjPost Q1 Q2) (P, Q1) /\
          ordPrePost (P, conjPost Q1 Q2) (P, Q2) ;
    post_conj_intro_pp :
      forall A (P:Pre) (Q1 Q2:Post A) (m:PrePost A),
        ordPrePost m (P, Q1) ->
        ordPrePost m (P, Q2) ->
        ordPrePost m (P, conjPost Q1 Q2) ;
    preorderPrePost : forall {A}, PreOrder (@ordPrePost _ _ pp A)
  }.

#[global] Existing Instance preorderPrePost.

Class PredMonad (Pred : Type -> Type) :=
  {
    monadPred : Monad Pred ;
    ordPred : forall {A}, relation (Pred A)
  }.

Class PredMonadLaws Pred `{PredMonad Pred} :=
  {
    preorderPredMonad : forall {A}, PreOrder (@ordPred Pred _ A)
  }.

#[global] Existing Instance preorderPredMonad.

Class GaloisPrePostPred Pred pre post
  (* Why do I need @ before PrePostT here? *)
  `{PredMonad Pred} `{@PrePostT pre post} :=
  {
    p2pp : forall {A}, Pred A -> PrePost A ;
    pp2p : forall {A}, PrePost A -> Pred A
  }.

Class GaloisPrePostPredLaws
  Pred pre post
  `{PredMonad Pred} `{@PrePostT pre post}
  {g : GaloisPrePostPred Pred pre post} :=
  {
    loop_p2pp_pp2p : forall {A} (pp:PrePost A),
      ordPrePost (p2pp (pp2p pp)) pp ;
    inverse_pp2p_p2pp : forall {A} (P:Pred A),
      ordPred P (pp2p (p2pp P)) /\ ordPred (pp2p (p2pp P)) P ;
    adjunction_pp_p : forall {A} (P:Pred A) (pp:PrePost A),
      ordPred P (pp2p pp) <-> ordPrePost (p2pp P) pp ;
  }.

Section GaloisOtherLaws.

  Variable A : Type.
  Variables (Pred : Type -> Type) (pre: PreT) (post : PostT).
  Context `{PredMonad Pred} {pp : @PrePostT pre post}.
  Context `{@PrePostLaws _ _ pp}. 
  Context {g : GaloisPrePostPred Pred pre post}.
  Context {gl : GaloisPrePostPredLaws Pred pre post}.

  Theorem strengthen_pre_pp2p (P1 P2:Pre) (Q:Post A) :
    ordPre P2 P1 ->
    ordPred (pp2p (P1, Q)) (pp2p (P2, Q)).
  Proof.
    intros HP2iP1.
    apply adjunction_pp_p.
    pose proof (loop_p2pp_pp2p (P1, Q)).
    pose proof (strengthen_pre_pp _ _ _ Q HP2iP1).
    transitivity (P1, Q); assumption.
  Qed.

  Theorem weaken_post_pp2p (P:Pre) (Q1 Q2:Post A) :
    ordPost Q1 Q2 ->
    ordPred (pp2p (P, Q1)) (pp2p (P, Q2)).
  Proof.
    intros HQ1iQ2.
    apply adjunction_pp_p.
    pose proof (loop_p2pp_pp2p (P, Q1)).
    pose proof (weaken_post_pp _ P _ _ HQ1iQ2).
    transitivity (P, Q1); assumption.
  Qed.

  Theorem post_conj_elim_pp2p P (Q1 Q2:Post A) :
    ordPred (pp2p (P, conjPost Q1 Q2)) (pp2p (P, Q1)) /\
      ordPred (pp2p (P, conjPost Q1 Q2)) (pp2p (P, Q2)).
  Proof. 
    pose proof (post_conj_elim_pp _ P Q1 Q2).
    destruct H. destruct gl. 
    split; apply adjunction_pp_p;
      pose proof (loop_p2pp_pp2p0 _ (P, conjPost Q1 Q2));
      transitivity (P, conjPost Q1 Q2); sfirstorder.
  Qed.

  Theorem post_conj_intro_pp2p (P:Pre) (Q1 Q2:Post A) (m:Pred A):
    ordPred m (pp2p (P, Q1)) ->
    ordPred m (pp2p (P, Q2)) ->
    ordPred m (pp2p (P, conjPost Q1 Q2)).
  Proof.
    intros H1 H2.
    apply adjunction_pp_p in H1.
    apply adjunction_pp_p in H2.
    apply adjunction_pp_p.
    pose proof (post_conj_intro_pp _ _ _ _ _ H1 H2).
    assumption.
  Qed.

End GaloisOtherLaws.
