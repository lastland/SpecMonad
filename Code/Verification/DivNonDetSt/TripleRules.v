(** * Sequencing triples with state (paper, Section 5)

    WP   For any monad morphism [θ] into [WSt S], triples compose along
         [bind] ([wpSt_bind_under], [wpSt_bind_over]), by the morphism law
         for [bind] ([wpSt_bind_read]) and the monotonicity of [θ m].  With
         the morphisms [dwpSt], [dwlpSt], [awpSt], [awlpSt] of
         [Morphisms.v] these give the eight kinds of WP triples.

    SP   The ASP and DSLP triples compose in both directions
         ([aspSt_bind_over], [aspSt_bind_under], [dslpSt_bind_under],
         [dslpSt_bind_over]), through the terminating outcomes of [bind]
         ([outSt_bind_Some]).  An under-approximate DSP triple is an ASP and
         a DSLP triple ([dspSt_under_iff]), an over-approximate ASLP triple
         likewise ([aslpSt_over_iff]); these compose through their
         components ([dspSt_bind_under], [aslpSt_bind_over]).

    The side condition relating the intermediate postcondition [Q0] of [m]
    and the preconditions [Pa a] of the continuation is

      [Q0 (a, s) -> Pa a s]   WP under, ASP over (Hoare), DSLP over,
                              ASLP over
      [Pa a s -> Q0 (a, s)]   WP over, ASP under (incorrectness), DSLP
                              under, DSP under

    and the rules whose conclusion asks for a witness through the
    continuation for every final state (ASP under, DSLP over, and so DSP
    under and ASLP over) also need the returned type [A] to be inhabited,
    since an empty [A] makes the premise on the continuation vacuous
    ([TriplesExamples/DSPSequencing.v]). *)

From ExtLib Require Import Monad StateMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.WP Require Import WPure.
From Incorrectness.SP Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDetSt Require Import Computation Morphisms Triples.

Section WPSequencing.
  Context {M : Type -> Type} {MonadM : Monad M} {Eq1M : Eq1 M} {S : Type}.
  Variable θ : forall A, M A -> WSt S A.
  Context {Iθ : IsMonadMorphism θ}.
  Hypothesis Hθ :
    @MonadMorphism M (WSt S) MonadM (Monad__WSt S) Eq1M (Eq1__WSt S) θ.

  (** The morphism law for [bind], read at a start state. *)
  Lemma wpSt_bind_read {A B} (m : M A) (f : A -> M B) (Q : B * S -> Prop) (s : S) :
    getWPure (runStateT (θ B (bind m f)) s) Q
    <-> getWPure (runStateT (θ A m) s)
          (fun '(a, s') => getWPure (runStateT (θ B (f a)) s') Q).
  Proof.
    etransitivity; [ exact (mm_bind Hθ m f s Q) |].
    split; apply (getWPure_mono (runStateT (θ A m) s)); intros [a s'] H; exact H.
  Qed.

  Theorem wpSt_bind_under {A B} (m : M A) (f : A -> M B)
    (P : S -> Prop) (Q0 : A * S -> Prop) (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
    triple θ m Under P Q0 -> (forall a, triple θ (f a) Under (Pa a) Q) ->
    (forall a s, Q0 (a, s) -> Pa a s) -> triple θ (bind m f) Under P Q.
  Proof.
    cbn. intros Hm Hf Hside s Hs. apply (proj2 (wpSt_bind_read m f Q s)).
    apply (getWPure_mono (runStateT (θ A m) s) Q0); [| exact (Hm s Hs) ].
    intros [a s'] Hq0. exact (Hf a s' (Hside a s' Hq0)).
  Qed.

  Theorem wpSt_bind_over {A B} (m : M A) (f : A -> M B)
    (P : S -> Prop) (Q0 : A * S -> Prop) (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
    triple θ m Over P Q0 -> (forall a, triple θ (f a) Over (Pa a) Q) ->
    (forall a s, Pa a s -> Q0 (a, s)) -> triple θ (bind m f) Over P Q.
  Proof.
    cbn. intros Hm Hf Hside s Hs. apply Hm.
    apply (getWPure_mono (runStateT (θ A m) s)
             (fun '(a, s') => getWPure (runStateT (θ B (f a)) s') Q));
      [| exact (proj1 (wpSt_bind_read m f Q s) Hs) ].
    intros [a s'] Hw. exact (Hside a s' (Hf a s' Hw)).
  Qed.
End WPSequencing.

Section SP.
  Context {S : Type}.

  Lemma outSt_bind_Some {A B} (m : stdivndNE S A) (f : A -> stdivndNE S B) (s : S) (r : B * S) :
    outSt (bind m f) s (Some r)
    <-> exists a s', outSt m s (Some (a, s')) /\ outSt (f a) s' (Some r).
  Proof.
    etransitivity; [ exact (outSt_bind m f s (Some r)) |]. split.
    - intros [[[a s']|] [H1 H2]]; [ exists a, s'; exact (conj H1 H2) |].
      discriminate H2.
    - intros [a [s' [H1 H2]]]. exists (Some (a, s')). exact (conj H1 H2).
  Qed.

  Context {A B : Type} (m : stdivndNE S A) (f : A -> stdivndNE S B)
    (P : S -> Prop) (Q0 : A * S -> Prop) (Pa : A -> S -> Prop) (Q : B * S -> Prop).

  Theorem aspSt_bind_over :
    triple (@aspSt S) m Over P Q0 ->
    (forall a, triple (@aspSt S) (f a) Over (Pa a) Q) ->
    (forall a s, Q0 (a, s) -> Pa a s) ->
    triple (@aspSt S) (bind m f) Over P Q.
  Proof.
    intros Hm Hf Hside r [[u s] [Hs Hr]]. cbn in Hr.
    apply outSt_bind_Some in Hr. destruct Hr as [a [s' [H1 H2]]].
    apply (Hf a r). exists (tt, s'). split; [| exact H2 ].
    apply Hside, Hm. exists (u, s). exact (conj Hs H1).
  Qed.

  Theorem aspSt_bind_under :
    inhabited A ->
    triple (@aspSt S) m Under P Q0 ->
    (forall a, triple (@aspSt S) (f a) Under (Pa a) Q) ->
    (forall a s, Pa a s -> Q0 (a, s)) ->
    triple (@aspSt S) (bind m f) Under P Q.
  Proof.
    intros [a0] Hm Hf Hside r Hr.
    destruct (Hf a0 r Hr) as [[u s'] [Hp Hf2]].
    destruct (Hm (a0, s') (Hside a0 s' Hp)) as [[u0 s] [Hs H1]].
    exists (u0, s). split; [ exact Hs |]. apply outSt_bind_Some.
    exists a0, s'. exact (conj H1 Hf2).
  Qed.

  Theorem dslpSt_bind_under :
    triple (@dslpSt S) m Under P Q0 ->
    (forall a, triple (@dslpSt S) (f a) Under (Pa a) Q) ->
    (forall a s, Pa a s -> Q0 (a, s)) ->
    triple (@dslpSt S) (bind m f) Under P Q.
  Proof.
    intros Hm Hf Hside r Hr [u s] H. cbn in H.
    apply outSt_bind_Some in H. destruct H as [a [s' [H1 H2]]].
    exact (Hm (a, s') (Hside a s' (Hf a r Hr (tt, s') H2)) (u, s) H1).
  Qed.

  Theorem dslpSt_bind_over :
    inhabited A ->
    triple (@dslpSt S) m Over P Q0 ->
    (forall a, triple (@dslpSt S) (f a) Over (Pa a) Q) ->
    (forall a s, Q0 (a, s) -> Pa a s) ->
    triple (@dslpSt S) (bind m f) Over P Q.
  Proof.
    intros [a0] Hm Hf Hside r Hr. apply (Hf a0 r). intros [u s'] H2.
    apply (Hside a0 s'), Hm. intros [u0 s] H1. apply Hr.
    apply outSt_bind_Some. exists a0, s'. exact (conj H1 H2).
  Qed.
End SP.

Section Decomposition.
  Context {S A : Type} (m : stdivndNE S A) (P : S -> Prop) (Q : A * S -> Prop).

  Theorem dspSt_under_iff :
    triple (@dspSt S) m Under P Q
    <-> triple (@aspSt S) m Under P Q /\ triple (@dslpSt S) m Under P Q.
  Proof.
    split; [ intro H; split; intros y Hy; apply (H y Hy) |].
    intros [H1 H2] y Hy. exact (conj (H1 y Hy) (H2 y Hy)).
  Qed.

  Theorem aslpSt_over_iff :
    triple (@aslpSt S) m Over P Q
    <-> triple (@aspSt S) m Over P Q /\ triple (@dslpSt S) m Over P Q.
  Proof.
    split; [ intro H; split; intros y Hy; apply H; [ left | right ]; exact Hy |].
    intros [H1 H2] y [Hy | Hy]; [ exact (H1 y Hy) | exact (H2 y Hy) ].
  Qed.
End Decomposition.

Theorem dspSt_bind_under {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (Q0 : A * S -> Prop) (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  inhabited A ->
  triple (@dspSt S) m Under P Q0 ->
  (forall a, triple (@dspSt S) (f a) Under (Pa a) Q) ->
  (forall a s, Pa a s -> Q0 (a, s)) ->
  triple (@dspSt S) (bind m f) Under P Q.
Proof.
  intros HA Hm Hf Hside. apply dspSt_under_iff.
  destruct (proj1 (dspSt_under_iff m P Q0) Hm) as [Ha Hd]. split.
  - exact (aspSt_bind_under m f P Q0 Pa Q HA Ha
             (fun a => proj1 (proj1 (dspSt_under_iff (f a) (Pa a) Q) (Hf a))) Hside).
  - exact (dslpSt_bind_under m f P Q0 Pa Q Hd
             (fun a => proj2 (proj1 (dspSt_under_iff (f a) (Pa a) Q) (Hf a))) Hside).
Qed.

Theorem aslpSt_bind_over {S A B} (m : stdivndNE S A) (f : A -> stdivndNE S B)
  (P : S -> Prop) (Q0 : A * S -> Prop) (Pa : A -> S -> Prop) (Q : B * S -> Prop) :
  inhabited A ->
  triple (@aslpSt S) m Over P Q0 ->
  (forall a, triple (@aslpSt S) (f a) Over (Pa a) Q) ->
  (forall a s, Q0 (a, s) -> Pa a s) ->
  triple (@aslpSt S) (bind m f) Over P Q.
Proof.
  intros HA Hm Hf Hside. apply aslpSt_over_iff.
  destruct (proj1 (aslpSt_over_iff m P Q0) Hm) as [Ha Hd]. split.
  - exact (aspSt_bind_over m f P Q0 Pa Q Ha
             (fun a => proj1 (proj1 (aslpSt_over_iff (f a) (Pa a) Q) (Hf a))) Hside).
  - exact (dslpSt_bind_over m f P Q0 Pa Q HA Hd
             (fun a => proj2 (proj1 (aslpSt_over_iff (f a) (Pa a) Q) (Hf a))) Hside).
Qed.
