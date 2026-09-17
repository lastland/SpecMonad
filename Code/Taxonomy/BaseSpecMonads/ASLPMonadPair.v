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
From Incorrectness.Classes Require Import OrderedMonad.
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

  (** ** Equality and laws, componentwise *)

  #[global] Instance Eq1__ASLPPair : Eq1 ASLPPair :=
    fun A w1 w2 => eq1 (aspPart w1) (aspPart w2) /\ eq1 (dslpPart w1) (dslpPart w2).

  #[global] Instance Eq1Equivalence__ASLPPair
    : @Eq1Equivalence ASLPPair _ Eq1__ASLPPair.
  Proof.
    intro A. destruct (Eq1Equivalence__ASPSt S A) as [Ra Sa Ta].
    destruct (Eq1Equivalence__DSLPSt S A) as [Rd Sd Td].
    constructor.
    - intro w. split; [ apply Ra | apply Rd ].
    - intros w1 w2 [H1 H2]. split; [ exact (Sa _ _ H1) | exact (Sd _ _ H2) ].
    - intros w1 w2 w3 [H1 H2] [H3 H4].
      split; [ exact (Ta _ _ _ H1 H3) | exact (Td _ _ _ H2 H4) ].
  Qed.

  #[global] Instance MonadLawsE__ASLPPair
    : @MonadLawsE ASLPPair Eq1__ASLPPair Monad__ASLPPair.
  Proof.
    destruct (MonadLawsE__ASPSt S) as [Abrl Abrr Abb Apb].
    destruct (MonadLawsE__DSLPSt S) as [Dbrl Dbrr Dbb Dpb].
    constructor.
    - intros A B f x. split;
        [ exact (Abrl A B (fun a => aspPart (f a)) x)
        | exact (Dbrl A B (fun a => dslpPart (f a)) x) ].
    - intros A x. split; [ exact (Abrr A (aspPart x)) | exact (Dbrr A (dslpPart x)) ].
    - intros A B C x f g. split;
        [ exact (Abb A B C (aspPart x) (fun a => aspPart (f a)) (fun b => aspPart (g b)))
        | exact (Dbb A B C (dslpPart x) (fun a => dslpPart (f a)) (fun b => dslpPart (g b))) ].
    - intros A B x y [Hx1 Hx2] f g Hfg. split;
        [ exact (Apb A B (aspPart x) (aspPart y) Hx1
                   (fun a => aspPart (f a)) (fun a => aspPart (g a))
                   (fun a => proj1 (Hfg a)))
        | exact (Dpb A B (dslpPart x) (dslpPart y) Hx2
                   (fun a => dslpPart (f a)) (fun a => dslpPart (g a))
                   (fun a => proj2 (Hfg a))) ].
  Qed.

  (** ** A specification monad *)

  #[global] Instance OrderedMonad_ASLPPair : OrderedMonad ASLPPair (@ordASLPPair).
  Proof.
    constructor.
    - intro A. exact ordASLPPair_PreOrder.
    - intros A x y [H1 H2]. split;
        [ intros pre r H; exact (proj1 (H1 pre r) H)
        | intros pre r H; exact (proj1 (H2 pre r) H) ].
    - intros A B w w' Hw k k' Hk. exact (ordASLPPair_bind w w' k k' Hw Hk).
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
