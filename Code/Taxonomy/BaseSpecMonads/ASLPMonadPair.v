(** * [ASLPPair]: the angelic-liberal strongest postcondition as a PAIR

    Dual to [DSPMonadPair.v], and with the same diagnosis: [bind] is not
    monotone for [ordASLPSt], because an ASLP assertion mentions BOTH
    bounds on the outcome relation -- [r] is asserted at [pre] when SOME
    [pre]-state reaches [r] OR ONLY [pre]-states reach it -- while a fibre
    of an order is one-sided.

    The carrier is again the product [ASPSt x DSLPSt] with componentwise
    operations and the componentwise order, so the enrichment is inherited
    and [ASLPPair] IS a specification monad.  Only the READING differs:
    where [DSPMonadPair] takes the conjunction of the two components,
    [readASLP] takes the DISJUNCTION.

    Consequently an ASLP index carries the same two pieces of data as a DSP
    one -- a relation for the angelic component, a pre/post bound for the
    demonic one -- but they are read as alternatives rather than as joint
    obligations, which is why an ASLP triple is discharged by SPLITTING the
    postcondition between them (see
    [EffectObservations/SP/StDivNonDet_SPStPair.v]). *)

From Coq Require Import RelationClasses Morphisms.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad ASLPMonad.

Import MonadNotation.
Open Scope monad_scope.

Import StTrans StASP StDSLP StASLP.

Module StASLPPair.

Section ASLPPair.
  Variable S : Type.
  #[local] Obligation Tactic := (intros; cbn beta).

  Definition ASLPPair (A : Type) : Type := (ASPSt S A * DSLPSt S A)%type.

  Definition aspPart {A} (w : ASLPPair A) : ASPSt S A := fst w.
  Definition dslpPart {A} (w : ASLPPair A) : DSLPSt S A := snd w.

  (** ** Monad structure, componentwise *)

  Definition retASLPPair {A} (a : A) : ASLPPair A := (ret a, ret a).

  Definition bindASLPPair {A B} (w : ASLPPair A) (wf : A -> ASLPPair B) : ASLPPair B :=
    (bind (aspPart w) (fun a => aspPart (wf a)),
     bind (dslpPart w) (fun a => dslpPart (wf a))).

  #[global] Instance Monad__ASLPPair : Monad ASLPPair :=
    {| ret := fun _ => @retASLPPair _ ;
       bind := fun _ _ => @bindASLPPair _ _ |}.

  (** ** The order, componentwise *)

  Definition ordASLPPair {A} (w1 w2 : ASLPPair A) : Prop :=
    ordASPSt (aspPart w1) (aspPart w2) /\ ordDSLPSt (dslpPart w1) (dslpPart w2).

  #[global] Instance ordASLPPair_PreOrder {A} : PreOrder (@ordASLPPair A).
  Proof.
    constructor.
    - intros w. split; reflexivity.
    - intros w1 w2 w3 [H1 H2] [H3 H4]. split; etransitivity; eassumption.
  Qed.

  Lemma ordASLPPair_bind {A B} (w w' : ASLPPair A) (k k' : A -> ASLPPair B) :
    ordASLPPair w w' -> (forall a, ordASLPPair (k a) (k' a)) ->
    ordASLPPair (bind w k) (bind w' k').
  Proof.
    intros [H1 H2] Hk. split.
    - apply ordASPSt_bind; [ exact H1 | intro a; exact (proj1 (Hk a)) ].
    - apply ordDSLPSt_bind; [ exact H2 | intro a; exact (proj2 (Hk a)) ].
  Qed.

  (** ** The ASLP reading: the DISJUNCTION of the two components *)

  Definition readASLP {A} (w : ASLPPair A) : @SPSt S A :=
    fun pre r => getASPSt (aspPart w) pre r \/ getDSLPSt (dslpPart w) pre r.

  Lemma readASLP_mono {A} (w : ASLPPair A) (P Q : S -> Prop) (r : A * S) :
    (forall s, P s -> Q s) -> readASLP w P r -> readASLP w Q r.
  Proof.
    intros Hsub [Ha | Hd].
    - left. exact (aspMono S (aspPart w) P Q r Hsub Ha).
    - right. exact (dslpMono S (dslpPart w) P Q r Hsub Hd).
  Qed.

  (** ** Indices built from a relation *)

  #[program] Definition aspOfRel {A} (R : S -> (A * S) -> Prop) : ASPSt S A :=
    fun pre r => exists s, pre s /\ R s r.
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s [Hp Hw]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hw ].
    - intros [s0 [Hp [s [Heq Hw]]]]. subst s. exists s0. split; assumption.
  Qed.

  #[program] Definition dslpOfRel {A} (R : S -> (A * S) -> Prop) : DSLPSt S A :=
    fun pre r => forall s, R s r -> pre s.
  Next Obligation. exact (dslp_msingleton S R). Qed.

  Lemma readASLP_ofRel {A} (R : S -> (A * S) -> Prop) pre r :
    readASLP (aspOfRel R, dslpOfRel R) pre r
    <-> ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s)).
  Proof. split; intro H; exact H. Qed.

End ASLPPair.

Arguments ASLPPair _ _.
Arguments aspPart {_} {_}.
Arguments dslpPart {_} {_}.
Arguments retASLPPair {_} {_}.
Arguments bindASLPPair {_} {_} {_}.
Arguments ordASLPPair {_} {_}.
Arguments readASLP {_} {_}.
Arguments aspOfRel {_} {_}.
Arguments dslpOfRel {_} {_}.

End StASLPPair.
