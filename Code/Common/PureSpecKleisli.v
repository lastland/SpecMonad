From ExtLib Require Import Monad.
From Hammer Require Import Tactics.
From Coq Require Import RelationClasses Relation_Definitions.

Import MonadNotation.

Set Implicit Arguments.

Definition pointwise_eq {A B} : relation (A -> B) :=
  fun f g => forall a, f a = g a.
Notation "f =1 g" := (pointwise_eq f g) (at level 42).

Definition pointwise_eq2 {A B C} : relation (A -> B -> C) :=
  fun f g => forall a, f a =1 g a.
Notation "f =2 g" := (pointwise_eq f g) (at level 42).

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
        dualPrePost m (P, disjPost Q1 Q2).
  Proof. sauto. Qed.
  
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

(* Class Default (A : Type) := { default : A }. *)

Section PrePostMonads.

  (* [PurePost] is a monad. I'm not sure about these definitions yet. *)
  Program Definition retPost {B} (b : B) : PurePost B :=
    fun b' => b = b'.

  Program Definition bindPost {B C}
    (m : PurePost B) (k : B -> PurePost C) : PurePost C :=
    fun c => exists b, m b /\ (k b) c.

  (*
  Monad B   := PurePre A * PurePost B ;
  Comonad A := PurePre A * PurePost B                                
  *)

  (* [PurePre] is a comonad. I'm not sure about these definitions yet. *)
  Program Definition extractPre {A}
    (p : PurePre A) : A := fst p.

  Program Definition extendPrePost {A B}
    (k : PurePre A -> B) (a : PurePre A) : PurePre B :=
    (k a, (fun b => exists a', k a' = b)).
  Next Obligation.
    exists a. reflexivity.
  Qed.
  
End PrePostMonads.

Section PredKleisli.
  
  Variables A B : Type.
  
  (* This is similar to: [{p : (a * (A -> B -> Prop)) | exists b, snd p (fst p) b}] but we
  can actually extract [b] in this version. We need to be able to extract b in
  [p2pp]. *)
  Definition PurePred := { p : (A * (A -> B * (B -> Prop)))%type
                         | match p with
                           | (a, p) =>
                               match (p a) with
                                 | (b, p') => p' b
                               end
                           end }.

  Program Definition ordPred (P1 P2 : PurePred) : Prop :=
    forall a b, snd (snd P1 a) b -> snd (snd P2 a) b.

End PredKleisli.

Section PredMonadComonad.

  Variables A B : Type.

  Program Definition retPred (b : B) : PurePred unit B :=
    (tt, fun _ => (b, fun b' => b = b')).

  Program Definition bindPred {C}
    (m : PurePred A B) (k : B -> PurePred A C) : PurePred A C :=
    match m with
    | (a, fa) =>
        match fa a with
        | (b, fb) =>
            match k b with
            | (a', fa') =>
                match fa' a' with
                | (c, fc) =>
                    (a, (fun a => (c, fc)))
                end
            end
        end
    end.
  Next Obligation.
    sauto.
  Qed.
  
  Program Definition extractPred (b : PurePred A B) : A := fst b.

  Program Definition extendPred {C}
    (k : PurePred A B -> C) (a : PurePred A B) : PurePred C B :=
    (* This one feels too simple, which makes me feel I could have made a
       mistake somewhere... This may become clear when working on comonad
       laws. *)
    match a with
    | (a', fa) =>
        match fa a' with
        | (b, fb) =>
            (k a, fun c => (b, fb))
        end
    end.
  Next Obligation.
    sauto.
  Qed. 

  (** TODO: Monad and comonad laws. *)
End PredMonadComonad.

(* TODO: at some point, refactor this codebase to be based on two types of
     predicates: normal predicate [A -> Prop] and nonempty predicate [A * (A ->
     Prop)]. *)
Definition NEPrePost A B :=
  { pp : B * PurePre A * PurePost B |
    match pp with
    | (b, exist _ (a, pre) _, post) =>
        pre a -> post b
    end }.

Ltac destruct_ne_pp pp :=
  let a := fresh "a" in
  let b := fresh "b" in
  let pre := fresh "pre" in
  let post := fresh "post" in
  let Hpre := fresh "Hpre" in
  let Hpp := fresh "Hpp" in
  destruct pp as [[[b [[a pre] Hpre]] post] Hpp].
              
Section RelationPred2PrePost.
  
  Variables A B : Type.

  (* [p2pp] does not need to produce [NEPrePost]. *)
  Program Definition p2pp' (p : PurePred A B) : PurePre A * PurePost B :=
    match p with
    | (a, fa) => 
        (* Intentionally kept simple for easy reasoning. *)
        ((a, (fun a => snd (fa a) (fst (fa a)))),
          fun b => snd (fa a) b) (* It seems wrong that this depends on [a]. *)
    end.
  Next Obligation.
    pose proof (proj2_sig p). rewrite <- Heq_p in H.
    destruct (fa a) eqn:Hfa. assumption.
  Qed.
    
  (* This one produces [NEPrePost] for symmetry. *)
  Program Definition p2pp (p : PurePred A B) : NEPrePost A B :=
    match p with
    | (a, fa) => 
        (* Intentionally kept simple (avoid pattern match on [fa a]) for easy
           reasoning. *)
        (fst (fa a), (a, (fun a => snd (fa a) (fst (fa a)))),
          fun b => snd (fa a) b)
    end.
  Next Obligation.
    pose proof (proj2_sig p). rewrite <- Heq_p in H.
    destruct (fa a) eqn:Hfa. assumption.
  Qed.

  (* This needs to be over [NEPrePost]. *)
  Program Definition pp2p (pp : NEPrePost A B) : PurePred A B :=
    match pp with
    | (b, pre', post) =>
        match pre' with
        | (a, pre) =>
            (a, fun a => (b, fun b => pre a -> post b))
        end
    end.
  (*
  Next Obligation.
    pose proof (proj2_sig p). rewrite <- Heq_p in H0. 
    exists a. destruct (fa a) eqn:Hfa. cbn in *. assumption.
  Qed. *)
  Next Obligation.
    pose proof (proj2_sig pp). cbn in H0. rewrite <- Heq_pp in H0.
    destruct pre'. cbn in *. rewrite <- Heq_pre' in H0. solve [auto].
  Qed.

  Program Definition ordPrePost' (p q : NEPrePost A B) : Prop :=
    ordPrePost (snd (fst p), snd p) (snd (fst q), snd q).

  Theorem loop_p2pp_pp2p : forall pp,
      ordPrePost' (p2pp (pp2p pp)) pp.
  Proof.
    intros. destruct_ne_pp pp. cbv. split.
    - hauto.
    - hauto lq: on drew: off.
  Qed.
    
  Theorem inverse_pp2p_p2pp : forall (p : PurePred A B),
      ordPred p (pp2p (p2pp p)) /\ ordPred (pp2p (p2pp p)) p.
  Proof.
    intros. destruct p as [[a fa] Ha]. cbv. split.
    - intros. destruct (fa a0) eqn:Hfaa0.
      destruct (fa a) eqn:Hfaa.
      (* Not provable *)
  Abort.

  Theorem adjunction_p_pp : forall p pp,
    ordPrePost' (p2pp p) pp <-> ordPred p (pp2p pp).
  Proof.
    intros. destruct p as [[a fa] Ha].
    destruct_ne_pp pp. cbn in Hpre.
    unfold ordPrePost', ordPrePost, ordPred, ordPre. cbn. split.
    - intros. destruct H as [H H2].
      eapply H2. apply H1. 
    (* Not provable. *)
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

(*
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
*)
