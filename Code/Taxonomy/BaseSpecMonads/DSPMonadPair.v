(** * [DSPPair]: the demonic strongest postcondition as a PAIR of bounds

    [DSPSt] is a monad and [ordDSPSt] is a preorder, but [bind] is not
    monotone for it, so [DSPSt] itself is NOT a specification monad in the
    sense of DM4All and carries no Dijkstra monad.  (The no-go theorems are
    stated for the [StExc] variant in
    [EffectObservations/SP/StDivExcNonDet_SPStExc.v]; their witnesses use
    no exceptional outcome, so they port verbatim.)

    The obstruction is that a DSP assertion is TWO-SIDED — [r] is
    asserted at [pre] when SOME [pre]-state reaches [r] (a lower bound on
    the outcome relation) AND ONLY [pre]-states reach it (an upper bound) —
    while a fibre of an order is one-sided.  The order that does encode
    both sides at once, [ordDSPSt], is exactly the one [bind] does not
    respect.

    Carrying the two bounds in two components fixes this.  [DSPPair] is the
    product [ASPSt x DSLPSt] with componentwise operations and the
    componentwise order — note that each component keeps its OWN direction,
    [ordASPSt] being inclusion of the underlying relation and [ordDSLPSt]
    its converse.  The enrichment is then inherited one component at a time
    from [ordASPSt_bind] and [ordDSLPSt_bind], so [DSPPair] IS a
    specification monad, and the DSP reading is recovered as the
    conjunction of the two components ([readDSP]). *)

From Coq Require Import RelationClasses Morphisms.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad.

Import MonadNotation.
Open Scope monad_scope.

Import StTrans StASP StDSLP StDSP.

Module StDSPPair.

Section DSPPair.
  Variable S : Type.
  #[local] Obligation Tactic := (intros; cbn beta).

  Definition DSPPair (A : Type) : Type := (ASPSt S A * DSLPSt S A)%type.

  Definition aspPart {A} (w : DSPPair A) : ASPSt S A := fst w.
  Definition dslpPart {A} (w : DSPPair A) : DSLPSt S A := snd w.

  (** ** Monad structure, componentwise *)

  Definition retDSPPair {A} (a : A) : DSPPair A := (ret a, ret a).

  Definition bindDSPPair {A B} (w : DSPPair A) (wf : A -> DSPPair B) : DSPPair B :=
    (bind (aspPart w) (fun a => aspPart (wf a)),
     bind (dslpPart w) (fun a => dslpPart (wf a))).

  #[global] Instance Monad__DSPPair : Monad DSPPair :=
    {| ret := fun _ => @retDSPPair _ ;
       bind := fun _ _ => @bindDSPPair _ _ |}.

  (** ** The order, componentwise -- each component in its own direction *)

  Definition ordDSPPair {A} (w1 w2 : DSPPair A) : Prop :=
    ordASPSt (aspPart w1) (aspPart w2) /\ ordDSLPSt (dslpPart w1) (dslpPart w2).

  #[global] Instance ordDSPPair_PreOrder {A} : PreOrder (@ordDSPPair A).
  Proof.
    constructor.
    - intros w. split; reflexivity.
    - intros w1 w2 w3 [H1 H2] [H3 H4]. split; etransitivity; eassumption.
  Qed.

  (** The [Pos]-enrichment, inherited one component at a time. *)
  Lemma ordDSPPair_bind {A B} (w w' : DSPPair A) (k k' : A -> DSPPair B) :
    ordDSPPair w w' -> (forall a, ordDSPPair (k a) (k' a)) ->
    ordDSPPair (bind w k) (bind w' k').
  Proof.
    intros [H1 H2] Hk. split.
    - apply ordASPSt_bind; [ exact H1 | intro a; exact (proj1 (Hk a)) ].
    - apply ordDSLPSt_bind; [ exact H2 | intro a; exact (proj2 (Hk a)) ].
  Qed.

  (** ** The DSP reading: the conjunction of the two components *)

  Definition readDSP {A} (w : DSPPair A) : @SPSt S A :=
    fun pre r => getASPSt (aspPart w) pre r /\ getDSLPSt (dslpPart w) pre r.

  Lemma readDSP_mono {A} (w : DSPPair A) (P Q : S -> Prop) (r : A * S) :
    (forall s, P s -> Q s) -> readDSP w P r -> readDSP w Q r.
  Proof.
    intros Hsub [Ha Hd]. split.
    - exact (aspMono S (aspPart w) P Q r Hsub Ha).
    - exact (dslpMono S (dslpPart w) P Q r Hsub Hd).
  Qed.

  (** ** Indices built from a relation

      The angelic component of an index is normally a relation -- the
      behaviour being claimed -- and the demonic one a pre/post bound. *)

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

  (** A pair built from ONE relation reads back as the DSP of that
      relation -- the sanity check that [readDSP] is the DSP shape. *)
  Lemma readDSP_ofRel {A} (R : S -> (A * S) -> Prop) pre r :
    readDSP (aspOfRel R, dslpOfRel R) pre r
    <-> ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)).
  Proof. split; intro H; exact H. Qed.

End DSPPair.

Arguments DSPPair _ _.
Arguments aspPart {_} {_}.
Arguments dslpPart {_} {_}.
Arguments retDSPPair {_} {_}.
Arguments bindDSPPair {_} {_} {_}.
Arguments ordDSPPair {_} {_}.
Arguments readDSP {_} {_}.
Arguments aspOfRel {_} {_}.
Arguments dslpOfRel {_} {_}.

End StDSPPair.
