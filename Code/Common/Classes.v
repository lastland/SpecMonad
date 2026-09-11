From Coq Require Import RelationClasses Relation_Definitions.
From ExtLib Require Import Monad MonadLaws.
From Hammer Require Import Tactics.

Class PreT (Pre : Type) :=
  {
    ordPre : Pre -> Pre -> Prop
  }.

Class PostT (Post : Type -> Type) :=
  {
    ordPost : forall {A}, Post A -> Post A -> Prop ;
    conjPost : forall {A}, Post A -> Post A -> Post A
  }.

Class PrePostT (Pre : Type) (Post : Type -> Type)
  `{PreT Pre} `{PostT Post} :=
  {
    PrePost A := prod Pre (Post A) ;
    ordPrePost : forall {A}, relation (PrePost A) 
  }.

Class PrePostLaws {Pre : Type} {Post : Type -> Type}
                  `{PreT Pre} `{PostT Post}
                  (pp : PrePostT Pre Post) :=
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
    preorderPrePost : forall {A}, PreOrder (@ordPrePost _ _ _ _ _ A)
  }.

#[global] Existing Instance preorderPrePost.

Class PredMonad (Pred : Type -> Type) :=
  {
    monadPred : Monad Pred ;
    ordPred : forall {A}, relation (Pred A) ;
    eqPred : forall {A}, relation (Pred A) :=
      fun _ x y => ordPred x y /\ ordPred y x
  }.

Class PredMonadLaws Pred `{PredMonad Pred} :=
  {
    preorderPredMonad : forall {A}, PreOrder (@ordPred Pred _ A) ;
    equivalencePredMonad : forall {A}, Equivalence (@eqPred Pred _ A) ;
  }.

#[global] Existing Instance preorderPredMonad.

Class GaloisPrePostPred Pred Pre Post
  `{PredMonad Pred} `{PrePostT Pre Post} :=
  {
    p2pp : forall {A}, Pred A -> PrePost A ;
    pp2p : forall {A}, PrePost A -> Pred A
  }.

Class GaloisPrePostPredLaws
  Pred Pre Post
  `{PredMonad Pred} `{PrePostT Pre Post}
  {g : GaloisPrePostPred Pred Pre Post} :=
  {
    loop_p2pp_pp2p : forall {A} (pp:PrePost A),
      ordPrePost (p2pp (pp2p pp)) pp ;
    inverse_pp2p_p2pp : forall {A} (p:Pred A),
      eqPred p (pp2p (p2pp p)) ;
    adjunction_pp_p : forall {A} (p:Pred A) (pp:PrePost A),
      ordPred p (pp2p pp) <-> ordPrePost (p2pp p) pp ;
  }.

Section GaloisOtherLaws.

  Variable A : Type.
  Variables (Pred : Type -> Type) (Pre : Type) (Post : Type -> Type).
  Context `{pp : PrePostT Pre Post}.
  Context `{PredMonad Pred}.
  Context {pl: @PrePostLaws _ _ _ _ pp}. 
  Context {g : GaloisPrePostPred Pred Pre Post}.
  Context {gl : GaloisPrePostPredLaws Pred Pre Post}.

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
    sauto lq: on.
  Qed.

End GaloisOtherLaws.
