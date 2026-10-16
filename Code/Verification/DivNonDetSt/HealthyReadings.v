(** * The four stateful WP readings land in their refined monads

    The stateful readings [dwpSt] &c. of [Morphisms.v] are [stateT_map S]
    of the base readings and target [WSt S].  Their corestrictions
    [dwpSt_DWPSt] &c., the stateful morphisms θ^DWP &c., are the lifts
    [stateT_map S] of the base corestrictions of
    [DivNonDet/HealthyReadings.v], hence monad morphisms
    [stdivndNE S ~> DWPSt S] &c. by [MonadMorphism_stateT]
    ([dwpSt_DWPSt_morphism] &c.). *)

From ExtLib Require Import Monad StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad TransformerLaws.
From Incorrectness.WP Require Import WPure WPVariants.
From Incorrectness.Verification.DivNonDet Require Import Computation Morphisms HealthyReadings.
From Incorrectness.Verification.DivNonDetSt Require Import Computation Morphisms.

Definition dwpSt_DWPSt {S A} (m : stdivndNE S A) : DWPSt S A :=
  stateT_map S (@dwpPure_DWP) A m.
Definition dwlpSt_DWLPSt {S A} (m : stdivndNE S A) : DWLPSt S A :=
  stateT_map S (@dwlpPure_DWLP) A m.
Definition awpSt_AWPSt {S A} (m : stdivndNE S A) : AWPSt S A :=
  stateT_map S (@awpPure_AWP) A m.
Definition awlpSt_AWLPSt {S A} (m : stdivndNE S A) : AWLPSt S A :=
  stateT_map S (@awlpPure_AWLP) A m.

Lemma dwpSt_DWPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DWPSt S) (Monad__stdivndNE S) (Monad_DWPSt S)
    (Eq1__stdivndNE S) (Eq1_DWPSt S) (@dwpSt_DWPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE DWP Monad__divndNE Monad_DWP
           Eq1__divndNE Eq1_DWP Eq1Equivalence_DWP MonadLawsE_DWP
           S (@dwpPure_DWP) dwpPure_DWP_morphism).
Qed.

Lemma dwlpSt_DWLPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (DWLPSt S) (Monad__stdivndNE S) (Monad_DWLPSt S)
    (Eq1__stdivndNE S) (Eq1_DWLPSt S) (@dwlpSt_DWLPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE DWLP Monad__divndNE Monad_DWLP
           Eq1__divndNE Eq1_DWLP Eq1Equivalence_DWLP MonadLawsE_DWLP
           S (@dwlpPure_DWLP) dwlpPure_DWLP_morphism).
Qed.

Lemma awpSt_AWPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (AWPSt S) (Monad__stdivndNE S) (Monad_AWPSt S)
    (Eq1__stdivndNE S) (Eq1_AWPSt S) (@awpSt_AWPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE AWP Monad__divndNE Monad_AWP
           Eq1__divndNE Eq1_AWP Eq1Equivalence_AWP MonadLawsE_AWP
           S (@awpPure_AWP) awpPure_AWP_morphism).
Qed.

Lemma awlpSt_AWLPSt_morphism (S : Type) :
  @MonadMorphism (stdivndNE S) (AWLPSt S) (Monad__stdivndNE S) (Monad_AWLPSt S)
    (Eq1__stdivndNE S) (Eq1_AWLPSt S) (@awlpSt_AWLPSt S).
Proof.
  exact (@MonadMorphism_stateT divndNE AWLP Monad__divndNE Monad_AWLP
           Eq1__divndNE Eq1_AWLP Eq1Equivalence_AWLP MonadLawsE_AWLP
           S (@awlpPure_AWLP) awlpPure_AWLP_morphism).
Qed.
