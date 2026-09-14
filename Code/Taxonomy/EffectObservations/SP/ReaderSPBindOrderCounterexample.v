From ExtLib Require Import Monad MonadReader ReaderMonad.
From Coq Require Import Bool.Bool.

(** * Ordered-bind counterexamples for coupled reader DSP and ASLP

    These observations use a shared [bool -> Prop] precondition and
    order actual ExtLib reader computations by implication of their
    observations.  Binding with one fixed continuation swaps a constant
    reader and [ask], breaking the original observation order.

    The existing [DSPRd] and [ASLPRd] carriers instead specify each
    environment independently.  Their pointwise readerT binds are
    monotone, as shown by [bindDSPRd_mono] and [bindASLPRd_mono]. *)

Module ReaderSPBindOrderCounterexample.

  (** A constant reader, an environment reader, and their common
      continuation, which XORs the returned Boolean with the environment. *)
  Definition m0 : reader bool bool := ret false.
  Definition m1 : reader bool bool := ask.
  Definition k (b : bool) : reader bool bool :=
    bind (ask : reader bool bool) (fun r => ret (xorb b r)).

  (** Ordinary reader bind runs the continuation under the same
      environment as the prefix, so [k] exchanges the two behaviors:
      [bind m0 k] returns the environment, as [ask] does, while
      [bind m1 k] constantly returns [false], as [m0] does. *)
  Lemma bind_m0 : forall r, runReader (bind m0 k) r = r.
  Proof. intro r; destruct r; reflexivity. Qed.

  Lemma bind_m1 : forall r, runReader (bind m1 k) r = false.
  Proof. intro r; destruct r; reflexivity. Qed.

  Definition dspOf {A} (m : reader bool A)
    (P : bool -> Prop) (a : A) : Prop :=
    (exists r, P r /\ runReader m r = a) /\
    (forall r, runReader m r = a -> P r).

  Definition aslpOf {A} (m : reader bool A)
    (P : bool -> Prop) (a : A) : Prop :=
    (exists r, P r /\ runReader m r = a) \/
    (forall r, runReader m r = a -> P r).

  Definition ordCoupled {A}
    (w v : (bool -> Prop) -> A -> Prop) : Prop :=
    forall P a, w P a -> v P a.

  Lemma dsp_ask P a : dspOf m1 P a <-> P a.
  Proof.
    split.
    - intros [_ Hall]; exact (Hall a eq_refl).
    - intro H; split.
      + exists a; split; [exact H | reflexivity].
      + intros r E; change (r = a) in E; now subst r.
  Qed.

  Lemma aslp_ask P a : aslpOf m1 P a <-> P a.
  Proof.
    split.
    - intros [[r [H E]] | Hall].
      + change (r = a) in E; now subst r.
      + exact (Hall a eq_refl).
    - intro H; left; exists a; split; [exact H | reflexivity].
  Qed.

  Lemma dsp_order : ordCoupled (dspOf m0) (dspOf m1).
  Proof.
    intros P a [[r [Hp Hr]] Hall].
    apply dsp_ask; exact (Hall a Hr).
  Qed.

  Lemma aslp_order : ordCoupled (aslpOf m1) (aslpOf m0).
  Proof.
    intros P a H.
    pose proof (proj1 (aslp_ask P a) H) as Ha.
    destruct a.
    - right; intros r E; discriminate E.
    - left; exists false; split; [exact Ha | reflexivity].
  Qed.

  (** At [P r := r = false], the reader from the left bind has only
      predecessor [false] for outcome [false].  The right bind also has
      predecessor [true], which violates the universal conjunct. *)
  Theorem dsp_counterexample :
    exists (m n : reader bool bool) (f : bool -> reader bool bool),
      ordCoupled (dspOf m) (dspOf n) /\
      ~ ordCoupled (dspOf (bind m f)) (dspOf (bind n f)).
  Proof.
    exists m0, m1, k.
    split; [exact dsp_order |]; intro Hle.
    assert (Hl : dspOf (bind m0 k) (fun r => r = false) false).
    { split.
      - exists false; split; [reflexivity | exact (bind_m0 false)].
      - intros r E; exact (eq_trans (eq_sym (bind_m0 r)) E). }
    destruct (Hle _ _ Hl) as [_ Hall].
    assert (E : true = false) by exact (Hall true (bind_m1 true)).
    discriminate E.
  Qed.

  (** At [P r := r = true], the left bind reaches [false] from [true].
      The right bind has only predecessor [false] for that outcome,
      so neither ASLP disjunct holds. *)
  Theorem aslp_counterexample :
    exists (m n : reader bool bool) (f : bool -> reader bool bool),
      ordCoupled (aslpOf m) (aslpOf n) /\
      ~ ordCoupled (aslpOf (bind m f)) (aslpOf (bind n f)).
  Proof.
    exists m1, m0, k.
    split; [exact aslp_order |]; intro Hle.
    assert (Hl : aslpOf (bind m1 k) (fun r => r = true) false).
    { left; exists true; split; [reflexivity | exact (bind_m1 true)]. }
    destruct (Hle _ _ Hl) as [[r [Hr Hout]] | Hall].
    - subst r; discriminate Hout.
    - assert (E : false = true) by exact (Hall false (bind_m0 false)).
      discriminate E.
  Qed.

  Corollary dsp_bind_not_monotone :
    ~ (forall (m n : reader bool bool) (f : bool -> reader bool bool),
      ordCoupled (dspOf m) (dspOf n) ->
      ordCoupled (dspOf (bind m f)) (dspOf (bind n f))).
  Proof.
    intro H; destruct dsp_counterexample as [m [n [f [Hle Hbad]]]].
    exact (Hbad (H m n f Hle)).
  Qed.

  Corollary aslp_bind_not_monotone :
    ~ (forall (m n : reader bool bool) (f : bool -> reader bool bool),
      ordCoupled (aslpOf m) (aslpOf n) ->
      ordCoupled (aslpOf (bind m f)) (aslpOf (bind n f))).
  Proof.
    intro H; destruct aslp_counterexample as [m [n [f [Hle Hbad]]]].
    exact (Hbad (H m n f Hle)).
  Qed.

End ReaderSPBindOrderCounterexample.
