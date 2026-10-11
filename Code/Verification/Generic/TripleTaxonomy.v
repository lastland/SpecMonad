(** * The four SP readings of one relation

    The SP edges of Verscht and Kaminski's diagram (POPL 2025, Figure 10)
    hold between the four readings of one relation, at arbitrary indices.
    The diagram itself is proved for computations with state in
    [DivNonDetSt/TriplesTaxonomy.v] and with state and exceptions in
    [DivNonDetStExc/TriplesTaxonomy.v]. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Relational Require Import Rel.
From Incorrectness.SP Require Import SPostArr DSPASLPArr.
From Incorrectness.PTMonadTaxonomy Require Import TransformerRelations.
From Incorrectness.PTMonadTaxonomy Require Import
  Carriers MonadTaxonomy.
From Incorrectness.Verification.Generic Require Import Triple.

(* ================================================================= *)
(** * The four SP readings of one relation                           *)
(* ================================================================= *)

Section OneRelation.
  Context {X Y : Type} (R : Rel X Y).

  Lemma dsp_incl_asp :
    pt_incl (Forward (getDSP (dspOfRelArr R))) (Forward (getASPArr (relASP R))).
  Proof. intros P y H. exact (proj1 H). Qed.

  Lemma dsp_incl_dslp :
    pt_incl (Forward (getDSP (dspOfRelArr R))) (Forward (getDSLPArr (relDSLP R))).
  Proof. intros P y H. exact (proj2 H). Qed.

  Lemma asp_incl_aslp :
    pt_incl (Forward (getASPArr (relASP R))) (Forward (getASLP (aslpOfRelArr R))).
  Proof. intros P y H. exact (or_introl H). Qed.

  Lemma dslp_incl_aslp :
    pt_incl (Forward (getDSLPArr (relDSLP R))) (Forward (getASLP (aslpOfRelArr R))).
  Proof. intros P y H. exact (or_intror H). Qed.

  (** Classical: [contra_asp_dslp_rel] and [contra_dsp_aslp_rel], at two
      elements that denote [R]. *)
  Lemma asp_contra_dslp :
    pt_contra (Forward (getASPArr (relASP R))) (Forward (getDSLPArr (relDSLP R))).
  Proof.
    exact (proj2 (contra_asp_dslp_rel (relASP R) (relDSLP R))
             (fun x y => iff_trans (aspRel_ofRel R x y)
                           (iff_sym (dslpRel_ofRel R x y)))).
  Qed.

  Lemma dslp_contra_asp :
    pt_contra (Forward (getDSLPArr (relDSLP R))) (Forward (getASPArr (relASP R))).
  Proof.
    exact (Contrapositive_sym (aspMono (relASP R)) (dslpMono (relDSLP R))
             asp_contra_dslp).
  Qed.

  Lemma dsp_contra_aslp :
    pt_contra (Forward (getDSP (dspOfRelArr R))) (Forward (getASLP (aslpOfRelArr R))).
  Proof.
    exact (proj2 (contra_dsp_aslp_rel (dspOfRelArr R) (aslpOfRelArr R))
             (fun x y => iff_trans (dspRel_ofRelArr R x y)
                           (iff_sym (aslpRel_ofRelArr R x y)))).
  Qed.

  Lemma aslp_contra_dsp :
    pt_contra (Forward (getASLP (aslpOfRelArr R))) (Forward (getDSP (dspOfRelArr R))).
  Proof.
    exact (Contrapositive_sym (dspMono (dspOfRelArr R)) (aslpMono (aslpOfRelArr R))
             dsp_contra_aslp).
  Qed.
End OneRelation.
