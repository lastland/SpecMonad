(** * The pre/post relational arrow [PrePost].

    [PrePost A B := (A -> Prop) * (A -> B -> Prop)] packages a Hoare
    triple [{P} _ {R}] where the post-relation [R] may reference the
    initial state [a].  Making the post-relation depend on the input
    [a] (rather than just on [b]) lets [arr_pure id] hold the diagonal
    [fun a b => a = b], so a strict Hughes-style [Arrow] instance
    works without coarsening the equivalence.

    This file establishes:
    - [Arrow] / [ArrowLaws] for [PrePost], with [arrow_eq = @eq]
      (bridged from pointwise iff via funext + propext);
    - a [Monad] in the second argument (for fixed [A]), with
      [Eq1] = pointwise iff and the standard [MonadLawsE].

    Galois connections relating [PrePost] to [Pred] and [WPArr] are
    collected in [Taxonomy/Galois.v]. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Type definition                                                *)
(* ================================================================= *)

Definition PrePost (A B : Type) : Type :=
  ((A -> Prop) * (A -> B -> Prop))%type.

Lemma PrePost_eq {A B} (pq1 pq2 : PrePost A B) :
  (forall a, fst pq1 a <-> fst pq2 a) ->
  (forall a b, snd pq1 a b <-> snd pq2 a b) ->
  pq1 = pq2.
Proof.
  destruct pq1 as [P1 R1]; destruct pq2 as [P2 R2]; simpl; intros HP HR.
  f_equal.
  - extensionality a. apply propositional_extensionality, HP.
  - extensionality a. extensionality b.
    apply propositional_extensionality, HR.
Qed.

(* ================================================================= *)
(** ** Arrow instance                                                 *)
(* ================================================================= *)

#[global]
Instance ArrowEq_PrePost : ArrowEq PrePost := {
  arrow_eq := fun A B => @eq (PrePost A B)
}.

#[global]
Instance Arrow_PrePost : Arrow PrePost := {
  arr_pure := fun A B f =>
    (fun _ : A => True, fun a b => f a = b) ;
  arr_comp := fun A B C pq1 pq2 =>
    ( fun a => fst pq1 a /\ (forall b, snd pq1 a b -> fst pq2 b)
    , fun a c => exists b, snd pq1 a b /\ snd pq2 b c ) ;
  arr_first := fun A B C pq =>
    ( fun p : (A * C)%type => fst pq (fst p)
    , fun p q => snd pq (fst p) (fst q) /\ snd p = snd q )
}.

#[global]
Instance ArrowLaws_PrePost : ArrowLaws PrePost.
Proof.
  constructor; intros.
  - (* comp_id_l: arr_pure id ⨟ f = f *)
    apply PrePost_eq; simpl.
    + intros a. split.
      * intros [_ HP]. exact (HP a eq_refl).
      * intros HP. split; [exact I |]. intros b ->. exact HP.
    + intros a c. split.
      * intros [b [-> HR]]. exact HR.
      * intros HR. exists a. split; [reflexivity | exact HR].
  - (* comp_id_r: f ⨟ arr_pure id = f *)
    apply PrePost_eq; simpl.
    + intros a. split.
      * intros [HP _]. exact HP.
      * intros HP. split; [exact HP | intros _ _; exact I].
    + intros a c. split.
      * intros [b [HR ->]]. exact HR.
      * intros HR. exists c. split; [exact HR | reflexivity].
  - (* comp_assoc *)
    apply PrePost_eq; simpl.
    + intros a. split.
      * intros [[HP HQ] HFh]. split; [exact HP |]. intros b HRf.
        split; [exact (HQ b HRf) |]. intros c HRg.
        apply HFh. exists b. split; [exact HRf | exact HRg].
      * intros [HP HFgh]. split.
        -- split; [exact HP |]. intros b HRf. exact (proj1 (HFgh b HRf)).
        -- intros c [b [HRf HRg]]. exact (proj2 (HFgh b HRf) c HRg).
    + intros a d. split.
      * intros [c [[b [HRf HRg]] HRh]].
        exists b. split; [exact HRf |]. exists c. split; [exact HRg | exact HRh].
      * intros [b [HRf [c [HRg HRh]]]].
        exists c. split; [exists b; split; [exact HRf | exact HRg] | exact HRh].
  - (* pure_comp *)
    apply PrePost_eq; simpl.
    + intros a. split.
      * intros _. exact I.
      * intros _. split; [exact I | intros _ _; exact I].
    + intros a c. split.
      * intros [b [<- ->]]. reflexivity.
      * intros <-. exists (f a). split; reflexivity.
  - (* first_pure *)
    apply PrePost_eq; simpl.
    + intros [a c]. simpl. reflexivity.
    + intros [a c] [b c']. simpl. split.
      * intros [-> ->]. reflexivity.
      * intros Heq. inversion Heq. subst. split; reflexivity.
  - (* first_comp *)
    apply PrePost_eq; simpl.
    + intros [a d]. simpl. split.
      * (* LHS pre -> RHS pre *)
        intros [HP HQ]. split; [exact HP |].
        intros [b d'] [HRf Hd]. simpl in *. subst d'. apply HQ. exact HRf.
      * (* RHS pre -> LHS pre *)
        intros [HP HQ]. split; [exact HP |].
        intros b HRf. apply (HQ (b, d)). simpl.
        split; [exact HRf | reflexivity].
    + intros [a d] [c d']. simpl. split.
      * (* LHS post -> RHS post *)
        intros [[b [HRf HRg]] Hdd]. subst d'.
        exists (b, d). simpl. split.
        -- split; [exact HRf | reflexivity].
        -- split; [exact HRg | reflexivity].
      * (* RHS post -> LHS post *)
        intros [[b d''] [[HRf Hd1] [HRg Hd2]]]. simpl in *.
        subst d'' d'.
        split; [| reflexivity]. exists b. split; [exact HRf | exact HRg].
  - (* first_fst *)
    apply PrePost_eq; simpl.
    + intros [a0 c]. simpl. split.
      * (* LHS pre -> RHS pre *)
        intros [HP _]. split; [exact I |]. intros a ->. exact HP.
      * (* RHS pre -> LHS pre *)
        intros [_ HQ]. split.
        -- exact (HQ a0 eq_refl).
        -- intros _ _. exact I.
    + intros [a0 c] b. simpl. split.
      * (* LHS post -> RHS post *)
        intros [[b' c'] [[HRf Hcc] Hbb]]. simpl in *. subst c' b'.
        exists a0. split; [reflexivity | exact HRf].
      * (* RHS post -> LHS post *)
        intros [a [Haa HRf]]. subst a. exists (b, c). simpl.
        split; [split; [exact HRf | reflexivity] | reflexivity].
  - (* first_assoc *)
    apply PrePost_eq; simpl.
    + intros [[a c] d]. simpl. split.
      * (* LHS pre -> RHS pre *)
        intros [HP _]. split; [exact I |].
        intros q Heq. unfold assoc_prod in Heq. subst q. simpl. exact HP.
      * (* RHS pre -> LHS pre *)
        intros [_ HQ]. split.
        -- exact (HQ (a, (c, d)) eq_refl).
        -- intros _ _. exact I.
    + intros [[a c] d] [b' [c' d']]. simpl. split.
      * (* LHS post -> RHS post *)
        intros [[[b c''] d''] [[[HRf Hcc] Hdd] Heq]]. simpl in *.
        unfold assoc_prod in Heq.
        exists (a, (c, d)). split.
        -- unfold assoc_prod. reflexivity.
        -- simpl. split.
           ++ replace b' with b by congruence. exact HRf.
           ++ congruence.
      * (* RHS post -> LHS post *)
        intros [[a' [c'' d'']] [Heq [HRf Hcd]]]. simpl in *.
        unfold assoc_prod in Heq.
        exists ((b', c), d). simpl. split.
        -- split; [split; [| reflexivity] | reflexivity].
           replace a' with a in HRf by congruence. exact HRf.
        -- unfold assoc_prod. congruence.
  - (* comp_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PrePost.
    intros; subst; reflexivity.
  - (* first_proper *)
    unfold Proper, respectful, arrow_eq, ArrowEq_PrePost.
    intros; subst; reflexivity.
Qed.

(* ================================================================= *)
(** ** Monad instance (second argument, [A] fixed)                    *)
(* ================================================================= *)

Section PrePostMonad.

  Context {A : Type}.

  Definition retPrePost {B} (b : B) : PrePost A B :=
    (fun _ => True, fun _ b' => b = b').

  Definition bindPrePost {B C}
    (m : PrePost A B) (k : B -> PrePost A C) : PrePost A C :=
    ( fun a => fst m a /\ (forall b, snd m a b -> fst (k b) a)
    , fun a c => exists b, snd m a b /\ snd (k b) a c ).

  #[global]
  Instance Monad_PrePost : Monad (PrePost A) := {
    ret := @retPrePost ;
    bind := @bindPrePost
  }.

  #[global]
  Instance Eq1_PrePost : Eq1 (PrePost A) :=
    fun B m1 m2 =>
      (forall a,   fst m1 a   <-> fst m2 a) /\
      (forall a b, snd m1 a b <-> snd m2 a b).

  #[global]
  Instance Eq1Equivalence_PrePost
    : @Eq1Equivalence (PrePost A) _ Eq1_PrePost.
  Proof.
    intros B; constructor.
    - (* Reflexive *)
      intros m. unfold eq1, Eq1_PrePost.
      split; intros; reflexivity.
    - (* Symmetric *)
      intros m1 m2 H. unfold eq1, Eq1_PrePost in *.
      destruct H as [HP HR]. split; intros.
      + symmetry. apply HP.
      + symmetry. apply HR.
    - (* Transitive *)
      intros m1 m2 m3 H1 H2. unfold eq1, Eq1_PrePost in *.
      destruct H1 as [HP1 HR1]. destruct H2 as [HP2 HR2].
      split; intros.
      + etransitivity; [apply HP1 | apply HP2].
      + etransitivity; [apply HR1 | apply HR2].
  Qed.

  #[global]
  Instance MonadLawsE_PrePost
    : @MonadLawsE (PrePost A) Eq1_PrePost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros B C f x.
      unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost, retPrePost. cbn.
      split.
      + intros a. split.
        * intros [_ HP]. exact (HP x eq_refl).
        * intros HP. split; [exact I |]. intros b ->. exact HP.
      + intros a c. split.
        * intros [b [-> HR]]. exact HR.
        * intros HR. exists x. split; [reflexivity | exact HR].
    - (* bind_ret_r *)
      intros B m.
      unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost, retPrePost. cbn.
      split.
      + intros a. split.
        * intros [HP _]. exact HP.
        * intros HP. split; [exact HP | intros _ _; exact I].
      + intros a b. split.
        * intros [b' [HR ->]]. exact HR.
        * intros HR. exists b. split; [exact HR | reflexivity].
    - (* bind_bind *)
      intros B C D m f g.
      unfold eq1, Eq1_PrePost.
      cbn. unfold bindPrePost. cbn.
      split.
      + intros a. split.
        * intros [[HP HRf] HFg].
          split; [exact HP |]. intros b HR.
          split; [exact (HRf b HR) |]. intros c HRf'.
          apply HFg. exists b. split; [exact HR | exact HRf'].
        * intros [HP HFgh]. split.
          -- split; [exact HP |]. intros b HR.
             exact (proj1 (HFgh b HR)).
          -- intros c [b [HR HRf']].
             exact (proj2 (HFgh b HR) c HRf').
      + intros a d. split.
        * intros [c [[b [HR HRf]] HRg]].
          exists b. split; [exact HR |].
          exists c. split; [exact HRf | exact HRg].
        * intros [b [HR [c [HRf HRg]]]].
          exists c. split; [exists b; split; [exact HR | exact HRf] | exact HRg].
    - (* Proper_bind *)
      intros B C m1 m2 Hm k1 k2 Hk.
      unfold eq1, Eq1_PrePost in *.
      destruct Hm as [HmP HmR].
      cbn. unfold bindPrePost. cbn.
      split.
      + intros a. split.
        * intros [HP HRf]. split; [apply HmP; exact HP |].
          intros b HR2. assert (HR1 : snd m1 a b) by (apply HmR; exact HR2).
          specialize (HRf b HR1).
          destruct (Hk b) as [HkP _]. apply HkP. exact HRf.
        * intros [HP HRf]. split; [apply HmP; exact HP |].
          intros b HR1. assert (HR2 : snd m2 a b) by (apply HmR; exact HR1).
          specialize (HRf b HR2).
          destruct (Hk b) as [HkP _]. apply HkP. exact HRf.
      + intros a c. split.
        * intros [b [HR1 HRf]].
          exists b. split; [apply HmR; exact HR1 |].
          destruct (Hk b) as [_ HkR]. apply HkR. exact HRf.
        * intros [b [HR2 HRf]].
          exists b. split; [apply HmR; exact HR2 |].
          destruct (Hk b) as [_ HkR]. apply HkR. exact HRf.
  Qed.

End PrePostMonad.

(** Galois connections with other spec types are collected in
    [Taxonomy/Galois.v]. *)
