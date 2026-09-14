(** * Connections between Stateful DSP/ASLP and Stateful PrePost

    This module establishes the Galois connections and adjunctions
    between the stateful strongest-postcondition monads ([StDSP.DSPSt]
    and [StASLP.ASLPSt]) and the stateful PrePost monad
    ([stateT S PPM.PrePost]).

    For both SP monads:
    - [L] equips the computation with the trivial precondition [True]
      and the recovered relation [relDSPSt] / [relASLPSt].
    - [G] reads the postcondition of the stateful PrePost computation
      into the canonical DSP / ASLP shape.

    We prove:
    - Recovery of [G]: the recovered relation of [G p] is exactly [post p].
    - Adjunction: [PPSt_le (L w) p <-> ord w (G p)], reusing
      [pred_pp_adjunction] pointwise.
    - Unit and counit: [G (L w) ≈ w] and [L (G p) <= p].
    - Monotonicity and Proper on Eq1 for all four maps.
    - Return and bind preservation for BOTH maps [L] and [G].
    - Positive embedded examples from [SPBindOrderCounterexample]. *)

From Coq Require Import Morphisms RelationClasses Classical_Prop.
From ExtLib Require Import Monad StateMonad.
From ITree Require Import Basics.Monad Extra.Dijkstra.DijkstraMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  PredMonad PrePostMonad BaseGaloisConnections StatePrePostMonad
  DSPMonad ASLPMonad SPBindOrderCounterexample.

(* [PPM] is deliberately not imported to avoid shadowing [pre] / [post]. *)

(* ================================================================= *)
(** ** Stateful DSP - PrePost Connection                              *)
(* ================================================================= *)

Section StDSPConnections.
  Variable S : Type.

  #[local] Existing Instance Monad__PPSt.
  #[local] Existing Instance Eq1__PPSt.

  (** Left map: trivial precondition [True] and recovered relation. *)
  Definition dspSt2ppSt {A : Type} (w : StDSP.DSPSt S A) : stateT S PPM.PrePost A :=
    mkStateT (fun s => (True, StDSP.relDSPSt w s)).

  Local Obligation Tactic := idtac.

  (** Right map: forget PrePost precondition and package post relation into DSP shape. *)
  #[program] Definition ppSt2dspSt {A : Type} (p : stateT S PPM.PrePost A) : StDSP.DSPSt S A :=
    fun pre r =>
      (exists s, pre s /\ PPM.post (runStateT p s) r) /\
      (forall s, PPM.post (runStateT p s) r -> pre s).
  Next Obligation.
    intros A p.
    exact (StDSP.dsp_shape_wf S (fun s r => PPM.post (runStateT p s) r)).
  Qed.

  (** Recovery of G: reading recovered relation of [ppSt2dspSt p] gives [PPM.post]. *)
  Lemma relDSPSt_ppSt2dspSt {A : Type} (p : stateT S PPM.PrePost A) (s : S) (r : A * S) :
    StDSP.relDSPSt (ppSt2dspSt p) s r <-> PPM.post (runStateT p s) r.
  Proof.
    apply (StDSP.relDSPSt_of_shape S (fun s0 r0 => PPM.post (runStateT p s0) r0) (ppSt2dspSt p)).
    intros pre r0. reflexivity.
  Qed.

  (** Pointwise adjunction reusing [pred_pp_adjunction]. *)
  Theorem dsp_pp_adjunction {A : Type} (w : StDSP.DSPSt S A) (p : stateT S PPM.PrePost A) :
    PPSt_le (dspSt2ppSt w) p <-> StDSP.ordDSPSt w (ppSt2dspSt p).
  Proof.
    split.
    - intros H s r Hw.
      assert (Hpp : PP_le (runStateT (dspSt2ppSt w) s) (runStateT p s)) by exact (H s).
      apply (proj2 (relDSPSt_ppSt2dspSt p s r)).
      apply (proj1 (pred_pp_adjunction (StDSP.relDSPSt w s) (runStateT p s)) Hpp).
      exact Hw.
    - intros H s.
      apply (proj2 (pred_pp_adjunction (StDSP.relDSPSt w s) (runStateT p s))).
      intros r Hw.
      apply (proj1 (relDSPSt_ppSt2dspSt p s r)).
      exact (H s r Hw).
  Qed.

  (** Unit of adjunction: [G (L w) ≈ w]. *)
  Theorem ppSt2dspSt_dspSt2ppSt {A : Type} (w : StDSP.DSPSt S A) :
    @eq1 (StDSP.DSPSt S) (StDSP.Eq1__DSPSt S) A (ppSt2dspSt (dspSt2ppSt w)) w.
  Proof.
    apply (proj1 (@StDSP.ordDSPSt_eq1 S A _ _)).
    split.
    - intros s r H.
      apply (proj1 (relDSPSt_ppSt2dspSt (dspSt2ppSt w) s r)) in H.
      exact H.
    - intros s r H.
      apply (proj2 (relDSPSt_ppSt2dspSt (dspSt2ppSt w) s r)).
      exact H.
  Qed.

  (** Counit of adjunction: [L (G p) <= p]. *)
  Theorem dspSt2ppSt_ppSt2dspSt {A : Type} (p : stateT S PPM.PrePost A) :
    PPSt_le (dspSt2ppSt (ppSt2dspSt p)) p.
  Proof.
    apply (proj2 (dsp_pp_adjunction (ppSt2dspSt p) p)).
    apply StDSP.ordDSPSt_refl.
  Qed.

  (** Order monotonicity of [dspSt2ppSt]. *)
  Theorem dspSt2ppSt_mono {A : Type} (w1 w2 : StDSP.DSPSt S A) :
    StDSP.ordDSPSt w1 w2 -> PPSt_le (dspSt2ppSt w1) (dspSt2ppSt w2).
  Proof.
    intros H s. split; [ intros _; exact I | intros r Hrel; exact (H s r Hrel) ].
  Qed.

  (** Order monotonicity of [ppSt2dspSt]. *)
  Theorem ppSt2dspSt_mono {A : Type} (p1 p2 : stateT S PPM.PrePost A) :
    PPSt_le p1 p2 -> StDSP.ordDSPSt (ppSt2dspSt p1) (ppSt2dspSt p2).
  Proof.
    intros H s r Hrel.
    apply (proj2 (relDSPSt_ppSt2dspSt p2 s r)).
    apply (proj2 (H s) r).
    apply (proj1 (relDSPSt_ppSt2dspSt p1 s r)).
    exact Hrel.
  Qed.

  (** [dspSt2ppSt] respects Eq1. *)
  Theorem dspSt2ppSt_Proper_eq1 {A : Type} :
    Proper (@eq1 (StDSP.DSPSt S) (StDSP.Eq1__DSPSt S) A ==>
            @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A) dspSt2ppSt.
  Proof.
    intros w1 w2 Hw.
    apply (proj1 (PPSt_le_eq1 (dspSt2ppSt w1) (dspSt2ppSt w2))).
    split; apply dspSt2ppSt_mono.
    - exact (proj1 (proj2 (@StDSP.ordDSPSt_eq1 S A w1 w2) Hw)).
    - exact (proj2 (proj2 (@StDSP.ordDSPSt_eq1 S A w1 w2) Hw)).
  Qed.

  (** [ppSt2dspSt] respects Eq1. *)
  Theorem ppSt2dspSt_Proper_eq1 {A : Type} :
    Proper (@eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A ==>
            @eq1 (StDSP.DSPSt S) (StDSP.Eq1__DSPSt S) A) ppSt2dspSt.
  Proof.
    intros p1 p2 Hp.
    apply (proj1 (@StDSP.ordDSPSt_eq1 S A _ _)).
    split; apply ppSt2dspSt_mono.
    - exact (proj1 (proj2 (PPSt_le_eq1 p1 p2) Hp)).
    - exact (proj2 (proj2 (PPSt_le_eq1 p1 p2) Hp)).
  Qed.

  (** Return preservation for [dspSt2ppSt]. *)
  Theorem dspSt2ppSt_ret {A : Type} (a : A) :
    @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A
      (dspSt2ppSt (StDSP.retDSPSt a))
      (@ret (stateT S PPM.PrePost) (Monad__PPSt S) A a).
  Proof.
    intros s. split; [ reflexivity |].
    intro r. exact (@StDSP.rec_retDSPProg S A a s r).
  Qed.

  (** Bind preservation for [dspSt2ppSt]. *)
  Theorem dspSt2ppSt_bind {A B : Type} (m : StDSP.DSPSt S A) (k : A -> StDSP.DSPSt S B) :
    @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) B
      (dspSt2ppSt (StDSP.bindDSPSt m k))
      (@bind (stateT S PPM.PrePost) (Monad__PPSt S) A B
         (dspSt2ppSt m) (fun a => dspSt2ppSt (k a))).
  Proof.
    intros s. split.
    - cbn. split.
      + intros _. split; [ exact I | intros [a smid] _; exact I ].
      + intros _; exact I.
    - intro r.
      refine (iff_trans (@StDSP.rec_bindDSPProg S A B m k s r) _).
      cbn. split.
      + intros [a [smid [Hm Hk]]].
        exists (a, smid). split; [ exact Hm | exact Hk ].
      + intros [[a smid] [Hm Hk]].
        exists a, smid. split; [ exact Hm | exact Hk ].
  Qed.

  (** Return preservation for [ppSt2dspSt]. *)
  Theorem ppSt2dspSt_ret {A : Type} (a : A) :
    @eq1 (StDSP.DSPSt S) (StDSP.Eq1__DSPSt S) A
      (ppSt2dspSt (@ret (stateT S PPM.PrePost) (Monad__PPSt S) A a))
      (StDSP.retDSPSt a).
  Proof.
    apply (proj1 (@StDSP.ordDSPSt_eq1 S A _ _)).
    split; intros s r H.
    - apply (proj1 (relDSPSt_ppSt2dspSt _ s r)) in H.
      apply (proj2 (@StDSP.rec_retDSPProg S A a s r)).
      exact H.
    - apply (proj2 (relDSPSt_ppSt2dspSt _ s r)).
      apply (proj1 (@StDSP.rec_retDSPProg S A a s r)).
      exact H.
  Qed.

  (** Bind preservation for [ppSt2dspSt]. *)
  Theorem ppSt2dspSt_bind {A B : Type} (p : stateT S PPM.PrePost A)
    (f : A -> stateT S PPM.PrePost B) :
    @eq1 (StDSP.DSPSt S) (StDSP.Eq1__DSPSt S) B
      (ppSt2dspSt (@bind (stateT S PPM.PrePost) (Monad__PPSt S) A B p f))
      (StDSP.bindDSPSt (ppSt2dspSt p) (fun a => ppSt2dspSt (f a))).
  Proof.
    apply (proj1 (@StDSP.ordDSPSt_eq1 S B _ _)).
    split; intros s r H.
    - apply (proj1 (relDSPSt_ppSt2dspSt _ s r)) in H.
      apply (proj2 (@StDSP.rec_bindDSPProg S A B (ppSt2dspSt p) (fun a => ppSt2dspSt (f a)) s r)).
      destruct H as [[a smid] [Hp Hf]].
      exists a, smid. split.
      + apply (proj2 (relDSPSt_ppSt2dspSt p s (a, smid))). exact Hp.
      + apply (proj2 (relDSPSt_ppSt2dspSt (f a) smid r)). exact Hf.
    - apply (proj2 (relDSPSt_ppSt2dspSt _ s r)).
      apply (proj1 (@StDSP.rec_bindDSPProg S A B (ppSt2dspSt p) (fun a => ppSt2dspSt (f a)) s r)) in H.
      destruct H as [a [smid [Hp Hf]]].
      exists (a, smid). split.
      + apply (proj1 (relDSPSt_ppSt2dspSt p s (a, smid))). exact Hp.
      + apply (proj1 (relDSPSt_ppSt2dspSt (f a) smid r)). exact Hf.
  Qed.

End StDSPConnections.

Arguments dspSt2ppSt {_} {_}.
Arguments ppSt2dspSt {_} {_}.

(* ================================================================= *)
(** ** Stateful ASLP - PrePost Connection                             *)
(* ================================================================= *)

Section StASLPConnections.
  Variable S : Type.

  #[local] Existing Instance Monad__PPSt.
  #[local] Existing Instance Eq1__PPSt.

  (** Left map: trivial precondition [True] and recovered relation. *)
  Definition aslpSt2ppSt {A : Type} (w : StASLP.ASLPSt S A) : stateT S PPM.PrePost A :=
    mkStateT (fun s => (True, StASLP.relASLPSt w s)).

  Local Obligation Tactic := idtac.

  (** Right map: forget PrePost precondition and package post relation into ASLP shape. *)
  #[program] Definition ppSt2aslpSt {A : Type} (p : stateT S PPM.PrePost A) : StASLP.ASLPSt S A :=
    fun pre r =>
      (exists s, pre s /\ PPM.post (runStateT p s) r) \/
      (forall s, PPM.post (runStateT p s) r -> pre s).
  Next Obligation.
    intros A p.
    exact (StASLP.aslp_shape_wf S (fun s r => PPM.post (runStateT p s) r)).
  Qed.

  (** Recovery of G: reading recovered relation of [ppSt2aslpSt p] gives [PPM.post]. *)
  Lemma relASLPSt_ppSt2aslpSt {A : Type} (p : stateT S PPM.PrePost A) (s : S) (r : A * S) :
    StASLP.relASLPSt (ppSt2aslpSt p) s r <-> PPM.post (runStateT p s) r.
  Proof.
    apply (StASLP.relASLPSt_of_shape S (fun s0 r0 => PPM.post (runStateT p s0) r0) (ppSt2aslpSt p)).
    intros pre r0. reflexivity.
  Qed.

  (** Pointwise adjunction reusing [pred_pp_adjunction]. *)
  Theorem aslp_pp_adjunction {A : Type} (w : StASLP.ASLPSt S A) (p : stateT S PPM.PrePost A) :
    PPSt_le (aslpSt2ppSt w) p <-> StASLP.ordASLPSt w (ppSt2aslpSt p).
  Proof.
    split.
    - intros H s r Hw.
      assert (Hpp : PP_le (runStateT (aslpSt2ppSt w) s) (runStateT p s)) by exact (H s).
      apply (proj2 (relASLPSt_ppSt2aslpSt p s r)).
      apply (proj1 (pred_pp_adjunction (StASLP.relASLPSt w s) (runStateT p s)) Hpp).
      exact Hw.
    - intros H s.
      apply (proj2 (pred_pp_adjunction (StASLP.relASLPSt w s) (runStateT p s))).
      intros r Hw.
      apply (proj1 (relASLPSt_ppSt2aslpSt p s r)).
      exact (H s r Hw).
  Qed.

  (** Unit of adjunction: [G (L w) ≈ w]. *)
  Theorem ppSt2aslpSt_aslpSt2ppSt {A : Type} (w : StASLP.ASLPSt S A) :
    @eq1 (StASLP.ASLPSt S) (StASLP.Eq1__ASLPSt S) A (ppSt2aslpSt (aslpSt2ppSt w)) w.
  Proof.
    apply (proj1 (@StASLP.ordASLPSt_eq1 S A _ _)).
    split.
    - intros s r H.
      apply (proj1 (relASLPSt_ppSt2aslpSt (aslpSt2ppSt w) s r)) in H.
      exact H.
    - intros s r H.
      apply (proj2 (relASLPSt_ppSt2aslpSt (aslpSt2ppSt w) s r)).
      exact H.
  Qed.

  (** Counit of adjunction: [L (G p) <= p]. *)
  Theorem aslpSt2ppSt_ppSt2aslpSt {A : Type} (p : stateT S PPM.PrePost A) :
    PPSt_le (aslpSt2ppSt (ppSt2aslpSt p)) p.
  Proof.
    apply (proj2 (aslp_pp_adjunction (ppSt2aslpSt p) p)).
    apply StASLP.ordASLPSt_refl.
  Qed.

  (** Order monotonicity of [aslpSt2ppSt]. *)
  Theorem aslpSt2ppSt_mono {A : Type} (w1 w2 : StASLP.ASLPSt S A) :
    StASLP.ordASLPSt w1 w2 -> PPSt_le (aslpSt2ppSt w1) (aslpSt2ppSt w2).
  Proof.
    intros H s. split; [ intros _; exact I | intros r Hrel; exact (H s r Hrel) ].
  Qed.

  (** Order monotonicity of [ppSt2aslpSt]. *)
  Theorem ppSt2aslpSt_mono {A : Type} (p1 p2 : stateT S PPM.PrePost A) :
    PPSt_le p1 p2 -> StASLP.ordASLPSt (ppSt2aslpSt p1) (ppSt2aslpSt p2).
  Proof.
    intros H s r Hrel.
    apply (proj2 (relASLPSt_ppSt2aslpSt p2 s r)).
    apply (proj2 (H s) r).
    apply (proj1 (relASLPSt_ppSt2aslpSt p1 s r)).
    exact Hrel.
  Qed.

  (** [aslpSt2ppSt] respects Eq1. *)
  Theorem aslpSt2ppSt_Proper_eq1 {A : Type} :
    Proper (@eq1 (StASLP.ASLPSt S) (StASLP.Eq1__ASLPSt S) A ==>
            @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A) aslpSt2ppSt.
  Proof.
    intros w1 w2 Hw.
    apply (proj1 (PPSt_le_eq1 (aslpSt2ppSt w1) (aslpSt2ppSt w2))).
    split; apply aslpSt2ppSt_mono.
    - exact (proj1 (proj2 (@StASLP.ordASLPSt_eq1 S A w1 w2) Hw)).
    - exact (proj2 (proj2 (@StASLP.ordASLPSt_eq1 S A w1 w2) Hw)).
  Qed.

  (** [ppSt2aslpSt] respects Eq1. *)
  Theorem ppSt2aslpSt_Proper_eq1 {A : Type} :
    Proper (@eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A ==>
            @eq1 (StASLP.ASLPSt S) (StASLP.Eq1__ASLPSt S) A) ppSt2aslpSt.
  Proof.
    intros p1 p2 Hp.
    apply (proj1 (@StASLP.ordASLPSt_eq1 S A _ _)).
    split; apply ppSt2aslpSt_mono.
    - exact (proj1 (proj2 (PPSt_le_eq1 p1 p2) Hp)).
    - exact (proj2 (proj2 (PPSt_le_eq1 p1 p2) Hp)).
  Qed.

  (** Return preservation for [aslpSt2ppSt]. *)
  Theorem aslpSt2ppSt_ret {A : Type} (a : A) :
    @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A
      (aslpSt2ppSt (StASLP.retASLPSt a))
      (@ret (stateT S PPM.PrePost) (Monad__PPSt S) A a).
  Proof.
    intros s. split; [ reflexivity |].
    intro r. exact (@StASLP.rec_retASLPProg S A a s r).
  Qed.

  (** Bind preservation for [aslpSt2ppSt]. *)
  Theorem aslpSt2ppSt_bind {A B : Type} (m : StASLP.ASLPSt S A) (k : A -> StASLP.ASLPSt S B) :
    @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) B
      (aslpSt2ppSt (StASLP.bindASLPSt m k))
      (@bind (stateT S PPM.PrePost) (Monad__PPSt S) A B
         (aslpSt2ppSt m) (fun a => aslpSt2ppSt (k a))).
  Proof.
    intros s. split.
    - cbn. split.
      + intros _. split; [ exact I | intros [a smid] _; exact I ].
      + intros _; exact I.
    - intro r.
      refine (iff_trans (@StASLP.rec_bindASLPProg S A B m k s r) _).
      cbn. split.
      + intros [a [smid [Hm Hk]]].
        exists (a, smid). split; [ exact Hm | exact Hk ].
      + intros [[a smid] [Hm Hk]].
        exists a, smid. split; [ exact Hm | exact Hk ].
  Qed.

  (** Return preservation for [ppSt2aslpSt]. *)
  Theorem ppSt2aslpSt_ret {A : Type} (a : A) :
    @eq1 (StASLP.ASLPSt S) (StASLP.Eq1__ASLPSt S) A
      (ppSt2aslpSt (@ret (stateT S PPM.PrePost) (Monad__PPSt S) A a))
      (StASLP.retASLPSt a).
  Proof.
    apply (proj1 (@StASLP.ordASLPSt_eq1 S A _ _)).
    split; intros s r H.
    - apply (proj1 (relASLPSt_ppSt2aslpSt _ s r)) in H.
      apply (proj2 (@StASLP.rec_retASLPProg S A a s r)).
      exact H.
    - apply (proj2 (relASLPSt_ppSt2aslpSt _ s r)).
      apply (proj1 (@StASLP.rec_retASLPProg S A a s r)).
      exact H.
  Qed.

  (** Bind preservation for [ppSt2aslpSt]. *)
  Theorem ppSt2aslpSt_bind {A B : Type} (p : stateT S PPM.PrePost A)
    (f : A -> stateT S PPM.PrePost B) :
    @eq1 (StASLP.ASLPSt S) (StASLP.Eq1__ASLPSt S) B
      (ppSt2aslpSt (@bind (stateT S PPM.PrePost) (Monad__PPSt S) A B p f))
      (StASLP.bindASLPSt (ppSt2aslpSt p) (fun a => ppSt2aslpSt (f a))).
  Proof.
    apply (proj1 (@StASLP.ordASLPSt_eq1 S B _ _)).
    split; intros s r H.
    - apply (proj1 (relASLPSt_ppSt2aslpSt _ s r)) in H.
      apply (proj2 (@StASLP.rec_bindASLPProg S A B (ppSt2aslpSt p) (fun a => ppSt2aslpSt (f a)) s r)).
      destruct H as [[a smid] [Hp Hf]].
      exists a, smid. split.
      + apply (proj2 (relASLPSt_ppSt2aslpSt p s (a, smid))). exact Hp.
      + apply (proj2 (relASLPSt_ppSt2aslpSt (f a) smid r)). exact Hf.
    - apply (proj2 (relASLPSt_ppSt2aslpSt _ s r)).
      apply (proj1 (@StASLP.rec_bindASLPProg S A B (ppSt2aslpSt p) (fun a => ppSt2aslpSt (f a)) s r)) in H.
      destruct H as [a [smid [Hp Hf]]].
      exists (a, smid). split.
      + apply (proj1 (relASLPSt_ppSt2aslpSt p s (a, smid))). exact Hp.
      + apply (proj1 (relASLPSt_ppSt2aslpSt (f a) smid r)). exact Hf.
  Qed.

End StASLPConnections.

Arguments aslpSt2ppSt {_} {_}.
Arguments ppSt2aslpSt {_} {_}.

(* ================================================================= *)
(** ** Positive embedded Boolean examples                            *)
(* ================================================================= *)

Section EmbeddedExamples.
  Import SPBindOrderCounterexample.

  #[local] Existing Instance Monad__PPSt.
  #[local] Existing Instance Eq1__PPSt.

  (** 1. Embedded comparisons: [L (xOf R0) <= L (xOf R1)] *)

  Theorem dsp_embedded_order :
    PPSt_le (dspSt2ppSt (dspOf R0)) (dspSt2ppSt (dspOf R1)).
  Proof.
    exact (dspSt2ppSt_mono bool (dspOf R0) (dspOf R1) dsp_order_rel).
  Qed.

  Theorem aslp_embedded_order :
    PPSt_le (aslpSt2ppSt (aslpOf R0)) (aslpSt2ppSt (aslpOf R1)).
  Proof.
    exact (aslpSt2ppSt_mono bool (aslpOf R0) (aslpOf R1) aslp_order_rel).
  Qed.

  (** 2. Sequencing via stateful PrePost [OrderedMonad.monot] *)

  Theorem dsp_embedded_sequenced :
    PPSt_le
      (bind (dspSt2ppSt (dspOf R0)) (fun a => dspSt2ppSt (dspOf (K a))))
      (bind (dspSt2ppSt (dspOf R1)) (fun a => dspSt2ppSt (dspOf (K a)))).
  Proof.
    exact (@monot (stateT bool PPM.PrePost) (Monad__PPSt bool)
             (OrderM__PPSt bool) (OrderedMonad__PPSt bool)
             unit unit
             (dspSt2ppSt (dspOf R0)) (dspSt2ppSt (dspOf R1))
             (fun a => dspSt2ppSt (dspOf (K a)))
             (fun a => dspSt2ppSt (dspOf (K a)))
             dsp_embedded_order
             (fun a => @reflex (stateT bool PPM.PrePost) (Monad__PPSt bool)
                        (OrderM__PPSt bool) (OrderedMonad__PPSt bool)
                        unit (dspSt2ppSt (dspOf (K a))))).
  Qed.

  Theorem aslp_embedded_sequenced :
    PPSt_le
      (bind (aslpSt2ppSt (aslpOf R0)) (fun a => aslpSt2ppSt (aslpOf (K a))))
      (bind (aslpSt2ppSt (aslpOf R1)) (fun a => aslpSt2ppSt (aslpOf (K a)))).
  Proof.
    exact (@monot (stateT bool PPM.PrePost) (Monad__PPSt bool)
             (OrderM__PPSt bool) (OrderedMonad__PPSt bool)
             unit unit
             (aslpSt2ppSt (aslpOf R0)) (aslpSt2ppSt (aslpOf R1))
             (fun a => aslpSt2ppSt (aslpOf (K a)))
             (fun a => aslpSt2ppSt (aslpOf (K a)))
             aslp_embedded_order
             (fun a => @reflex (stateT bool PPM.PrePost) (Monad__PPSt bool)
                        (OrderM__PPSt bool) (OrderedMonad__PPSt bool)
                        unit (aslpSt2ppSt (aslpOf (K a))))).
  Qed.

  (** 3. Relate via L-bind preservation *)

  Theorem dsp_sequenced_embedded_relate :
    @eq1 (stateT bool PPM.PrePost) (Eq1__PPSt bool) unit
      (dspSt2ppSt (StDSP.bindDSPSt (dspOf R0) (fun a => dspOf (K a))))
      (bind (dspSt2ppSt (dspOf R0)) (fun a => dspSt2ppSt (dspOf (K a)))).
  Proof.
    exact (dspSt2ppSt_bind bool (dspOf R0) (fun a => dspOf (K a))).
  Qed.

  Theorem aslp_sequenced_embedded_relate :
    @eq1 (stateT bool PPM.PrePost) (Eq1__PPSt bool) unit
      (aslpSt2ppSt (StASLP.bindASLPSt (aslpOf R0) (fun a => aslpOf (K a))))
      (bind (aslpSt2ppSt (aslpOf R0)) (fun a => aslpSt2ppSt (aslpOf (K a)))).
  Proof.
    exact (aslpSt2ppSt_bind bool (aslpOf R0) (fun a => aslpOf (K a))).
  Qed.

  Theorem dsp_transported_sequenced :
    PPSt_le
      (dspSt2ppSt (StDSP.bindDSPSt (dspOf R0) (fun a => dspOf (K a))))
      (dspSt2ppSt (StDSP.bindDSPSt (dspOf R1) (fun a => dspOf (K a)))).
  Proof.
    exact (dspSt2ppSt_mono bool _ _ dsp_sequenced).
  Qed.

  Theorem aslp_transported_sequenced :
    PPSt_le
      (aslpSt2ppSt (StASLP.bindASLPSt (aslpOf R0) (fun a => aslpOf (K a))))
      (aslpSt2ppSt (StASLP.bindASLPSt (aslpOf R1) (fun a => aslpOf (K a)))).
  Proof.
    exact (aslpSt2ppSt_mono bool _ _ aslp_sequenced).
  Qed.

  Theorem dsp_embedded_sequenced_iff :
    PPSt_le
      (dspSt2ppSt (StDSP.bindDSPSt (dspOf R0) (fun a => dspOf (K a))))
      (dspSt2ppSt (StDSP.bindDSPSt (dspOf R1) (fun a => dspOf (K a))))
    <->
    PPSt_le
      (bind (dspSt2ppSt (dspOf R0)) (fun a => dspSt2ppSt (dspOf (K a))))
      (bind (dspSt2ppSt (dspOf R1)) (fun a => dspSt2ppSt (dspOf (K a)))).
  Proof.
    apply PPSt_le_Proper.
    - exact dsp_sequenced_embedded_relate.
    - exact (dspSt2ppSt_bind bool (dspOf R1) (fun a => dspOf (K a))).
  Qed.

  Theorem aslp_embedded_sequenced_iff :
    PPSt_le
      (aslpSt2ppSt (StASLP.bindASLPSt (aslpOf R0) (fun a => aslpOf (K a))))
      (aslpSt2ppSt (StASLP.bindASLPSt (aslpOf R1) (fun a => aslpOf (K a))))
    <->
    PPSt_le
      (bind (aslpSt2ppSt (aslpOf R0)) (fun a => aslpSt2ppSt (aslpOf (K a))))
      (bind (aslpSt2ppSt (aslpOf R1)) (fun a => aslpSt2ppSt (aslpOf (K a)))).
  Proof.
    apply PPSt_le_Proper.
    - exact aslp_sequenced_embedded_relate.
    - exact (aslpSt2ppSt_bind bool (aslpOf R1) (fun a => aslpOf (K a))).
  Qed.

End EmbeddedExamples.
