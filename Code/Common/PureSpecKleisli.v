From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import Common.Notations Common.Classes.
From Coq Require Import RelationClasses Relation_Definitions.

Set Implicit Arguments.

Definition pointwise_eq {A B} : relation (A -> B) :=
  fun f g => forall a, f a = g a.

Notation "f =1 g" := (pointwise_eq f g) (at level 42).

Instance Eq__pointwise {A B} : Equivalence (@pointwise_eq A B).
Proof. sfirstorder. Qed.

(** We no longer consider a single monad, but a Kleisli category. *)
Definition Kleisli (m : Type -> Type) a b := a -> m b.

(** This is the Kleisli category of the identity mnonad; but also just the same
    as the reader monad. *)
Definition PureKleisli := Kleisli id.  

Section PrePostKleisli.
  
  Variables A B : Type.

  (** The subset type is to make sure that [dualPrePost] is an ordering
      relation, shown later. *)
  Definition PurePre := { ap : A * (A -> Prop) | snd ap (fst ap) }.
  (** I cannot make [PurePost] parameterize over [A], because I won't be able to
      define [dualPrePost] that way. *)
  Definition PurePost := B -> Prop.

  Program Definition ordPre (P1 P2 : PurePre) :=
    forall a, snd P1 a -> snd P2 a.
  Definition ordPost (Q1 Q2 : PurePost) :=
    forall b, Q1 b -> Q2 b.

  Definition conjPost (Q1 Q2 : PurePost) : PurePost :=
    fun b => Q1 b /\ Q2 b.
  Definition disjPost (Q1 Q2 : PurePost) : PurePost :=
    fun b => Q1 b \/ Q2 b.

  #[global] Instance PreOrder__ordPre : PreOrder ordPre.
  Proof. sfirstorder. Qed.

  #[global] Instance PreOrder__ordPost : PreOrder ordPost.
  Proof. sfirstorder. Qed.

  Program Definition ordPrePost (pp1 pp2 : PurePre * PurePost) :=
    match pp1, pp2 with
    | (P1, Q1), (P2, Q2) =>
        ordPre P2 P1 /\
          forall a, snd P2 a -> forall b, Q1 b -> Q2 b
    end.

  #[global] Instance PreOrder__PrePost : PreOrder ordPrePost.
  Proof.
    constructor.
    - fcrush.
    - intros [] [] []. sfirstorder.
  Qed.
  
  (** Correctness laws of [ordPrePost]. This corresponds to the laws of Hoare
      logic. *)
  Theorem strengthen_pre_pp :
    forall (P1 P2 : PurePre) (Q : PurePost),
      ordPre P2 P1 -> ordPrePost (P1, Q) (P2, Q).
  Proof. sfirstorder. Qed.
    
  Theorem weaken_post_pp : 
    forall P Q1 Q2,
      ordPost Q1 Q2 -> ordPrePost (P, Q1) (P, Q2).
  Proof. sfirstorder. Qed.
  
  Theorem post_conj_elim_pp :
    forall P (Q1 Q2 : PurePost),
      ordPrePost (P, conjPost Q1 Q2) (P, Q1) /\
        ordPrePost (P, conjPost Q1 Q2) (P, Q2).
  Proof. sfirstorder. Qed.

  Theorem post_conj_intro_pp :
    forall P (Q1 Q2 : PurePost) (m : PurePre * PurePost),
      ordPrePost m (P, Q1) ->
      ordPrePost m (P, Q2) ->
      ordPrePost m (P, conjPost Q1 Q2).
  Proof. fcrush. Qed.

  (** Now we introduce a different order, which corresponds to the incorrectness
      logic. *)
  Program Definition dualPrePost (pp1 pp2 : PurePre * PurePost) :=
    match pp1, pp2 with
    | (P1, Q1), (P2, Q2) =>
        ordPre P1 P2 /\
          forall b, Q2 b -> (exists a, snd P2 a /\ Q1 b)
    end.

  (** It is a preorder. *)
  #[global] Instance PreOrder__dualPrePost : PreOrder dualPrePost.
  Proof.
    constructor.
    - intros []. fcrush.
    - intros [] [] []. sfirstorder.
  Qed.

  (** Correctness laws of [dualPrePost]. These correspond to the laws of the
      incorrectness logic. *)
  Theorem weaken_pre_pp : forall (P1 P2 : PurePre) (Q : PurePost),
      ordPre P1 P2 -> dualPrePost (P1, Q) (P2, Q).
  Proof. sauto lq: on. Qed.

  Theorem strengthen_post_pp : 
      forall (P : PurePre) (Q1 Q2 : PurePost),
        ordPost Q2 Q1 -> dualPrePost (P, Q1) (P, Q2).
  Proof. fcrush. Qed.

  Theorem post_disj_elim_pp :
      forall P (Q1 Q2 : PurePost),
        dualPrePost (P, disjPost Q1 Q2) (P, Q1) /\
          dualPrePost (P, disjPost Q1 Q2) (P, Q2).
  Proof. fcrush. Qed.

  Theorem post_disj_intro_pp :
      forall P (Q1 Q2 : PurePost) (m: PurePre * PurePost),
        dualPrePost m (P, Q1) ->
        dualPrePost m (P, Q2) ->
        dualPrePost m (P, conjPost Q1 Q2).
  Proof. hauto lq: on. Qed.
  
  (** Interactions between [ordPrePost] and [dualPrePost]. These correspond to
      the principles of agreement and denial. *)
  Theorem pre_post_agreement :
    forall P1 P2 P3 Q1 Q2 Q3,
      dualPrePost (P2, Q2) (P1, Q1) ->
      ordPrePost (P2, Q2) (P3, Q3) ->
      ordPre P1 P3 ->
      ordPost Q1 Q3.
  Proof. sfirstorder. Qed.

  Theorem pre_post_denial :
    forall P1 P2 P3 Q1 Q2 Q3,
      dualPrePost (P2, Q2) (P1, Q1) ->
      ordPre P1 P3 ->
      not (ordPost Q1 Q3) ->
      not (ordPrePost (P2, Q2) (P3, Q3)).
  Proof. sfirstorder. Qed.
      
End PrePostKleisli.

Arguments PurePre : clear implicits.
Arguments PurePost : clear implicits.

Section PredKleisli.
  
  Variables A B : Type.
  
  (** There are two possible Preds: A -> B -> Prop and (A -> B) -> Prop. Both
      seem to make sense. *)
  Definition PurePred := (A -> B) -> Prop.

  Definition ordPred (P1 P2 : PurePred) : Prop :=
    forall f1 f2, f1 =1 f2 -> P1 f1 -> P2 f2.

End PredKleisli.

Section PredArrow.

  Variables A B C : Type.

  Definition arrPred (f : A -> B) : PurePred A B :=
    fun f' => f =1 f'.

  Definition compPred 
    (l : PurePred A B) (r : PurePred B C) : PurePred A C :=
    fun f => exists (g : A -> B) (h : B -> C), l g /\ r h /\ f =1 fun a => h (g a).

  Definition firstPred (p : PurePred A B) : PurePred (A * C) (B * C) :=
    fun f => exists l, (fun '(a, c) => (l a, c)) =1 f /\ p l.

  Definition leftPred (p : PurePred A B) : PurePred (A + C) (B + C) :=
    fun f => exists l, (fun ac => match ac with
                       | inl a => inl (l a)
                       | inr c => inr c
                       end) =1 f /\ p l.

  (* Not sure about this one. *)
  Definition appPred : PurePred (PurePred A B * A) B :=
    fun f => exists l, exists p, forall a, f (p, a) = l a /\ p l.

  (** TODO: I don't like proving arrow laws; leaving them as future work for
      now. *)
  
End PredArrow.


Section RelationPred2PrePost.
  
  Variables A B : Type.

  Program Definition p2pp (a : A) (p : PurePred A B) : PurePre A * PurePost B :=
    ((a, fun _ => True), fun b => p (fun _ => b)).

  Program Definition pp2p (pp : PurePre A * PurePost B) : PurePred A B :=
    fun f => match pp with
          | (ap, q) =>
              match ap with
              | (a, p) => p a -> q (f a)  
              end
          end.

  Theorem adjunction_p_pp : forall a p pp,
    ordPrePost (p2pp a p) pp <-> ordPred p (pp2p pp).
  Proof.
    destruct pp. unfold ordPrePost, ordPred, ordPre, ordPost.
    cbn. destruct p0 as [[a0 p0] Hp0]. cbn in *. split.
    - intros. destruct H. eapply H3. apply H2.
      (** Missing some invariance of [Pred]? *)
  Abort.


  (*
  Lemma loop_p2pp_pp2p (a : A) (p : PurePred A B) :
    ordPred p (pp2p (p2pp a p)) /\ ordPred (pp2p (p2pp a p)) p.
  Proof.
    unfold PurePred in p. split.
    - unfold p2pp, pp2p, ordPred. cbn. intros.
      admit.
    - unfold p2pp, pp2p, ordPred. cbn. intros.
      hammer.

  Qed.

  Lemma loop_pp2p_p2pp (pp : PurePre A * PurePost A B) :
    ordPrePost (p2pp (pp2p pp)) pp.
  Proof. destruct pp. sfirstorder. Qed.
   *)

End RelationPred2PrePost.

Section ForwardPredicateTransformer.
  
  Variables A B : Type.

  Definition _SPost A B := A ->
    forall (pre : Prop), B -> {p : Prop | p -> pre}.

  Definition SPost A B :=
    { w : _SPost A B | forall a p q r,
        (p -> q) -> proj1_sig (w a p r) -> proj1_sig (w a q r)  }.
  (*
  Definition _SPost A B :=
    forall (pre : A -> Prop), B -> {p : Prop | p -> pre}.

  Definition SPost A :=
    { w : _SPost A | forall p q r,
        (p -> q) -> proj1_sig (w p r) -> proj1_sig (w q r)  }.
   *)

  Program Definition ordSPost (sp1 sp2: SPost A B) : Prop :=
    forall a pre b,
      proj1_sig (proj1_sig sp1 a pre b) ->
      proj1_sig (proj1_sig sp2 a pre b).

  Instance PreOrder__SPost : PreOrder ordSPost.
  Proof. sfirstorder. Qed.
  
End ForwardPredicateTransformer.

(*
Section RelationPred2SPost.
  
  Variables A B : Type.
  
  Program Definition p2sp (p : PurePred A B) : SPost A B :=
    fun a pre b => pre /\ p a b.

  Program Definition sp2p (sp : SPost A B) : PurePred A B :=
    fun a => sp a True.

  Theorem adjunction_p_sp : forall p sp,
      ordPred p (sp2p sp) <-> ordSPost (p2sp p) sp.
  Proof.
    intros. unfold ordPred, ordSPost.
    destruct sp as [sp' Hsp]. cbn in *.
    sfirstorder.
  Qed.

End RelationPred2SPost.

Section RelationSPost2PrePost.

  Variables A B : Type.

  Program Definition pp2sp
    (pp : PurePre A * PurePost B) : SPost A B.
  unfold SPost. destruct pp as [p q]. destruct p as [p Hp].
  unfold _SPost. econstructor.
  Unshelve.
  2: { intros a pre b.
    
  }
  
  
    p2sp (pp2p pp).

  Definition sp2pp (sp : SPost A B) : PurePre A * PurePost A B :=
    p2pp (sp2p sp).

  Lemma loop_pp2sp_sp2pp (sp : SPost A B):
    ordSPost sp (pp2sp (sp2pp sp)).
  Proof.
    intros; split; destruct sp; [sfirstorder |].
    cbn in *. unfold sp2p. cbn.
    sauto lq: on drew: off.
  Qed.
  
  Lemma loop_sp2pp_pp2sp (pp : PurePre A * PurePost A B) :
    ordPrePost (sp2pp (pp2sp pp)) pp.
  Proof.
    destruct pp. sfirstorder.
  Qed.

  Theorem adjunction_sp_pp : forall pp sp,
      ordPrePost (sp2pp sp) pp <-> ordSPost sp (pp2sp pp).
  Proof.
    intros. unfold pp2sp, sp2pp.
    destruct pp. destruct sp. cbn in *. split.
    - split; [sfirstorder |]. cbn in *. destruct H.
      intros. specialize (H1 a ltac:(assumption) b).
      apply H1. unfold sp2p. cbn. sauto lq: on drew: off.
    - split; [sfirstorder |]. intros.
      unfold sp2p in H1. cbn in H1.
      unfold ordSPost in H. cbn in H.
      eapply H; [sauto lq: on | assumption].
  Qed.
End RelationSPost2PrePost.
*)
