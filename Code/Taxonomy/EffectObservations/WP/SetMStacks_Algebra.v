(** * The stacks over [SetM], by algebra-transformer composition

    [SetM] is the BASE: its two algebras ([MAlg_SetM_demonic] /
    [MAlg_SetM_angelic], [DivNonDet_WPure_Algebra.v]) are the one place the
    demonic/angelic choice is made, and they are the only algebras written
    by hand.  Everything above is composition:

      [MAlg_div dh]  = [MAlg_optionT] over the base   -- divergence, handler [dh]
      [MAlg_st S]    = [MAlg_stateT]  over that       -- state,  [L] becomes [S -> L]
      [MAlg_rd R]    = [MAlg_readerT] over that       -- reader, [L] becomes [R -> L]

    NO MONAD-MORPHISM LAW IS PROVED HERE.  [WPof_ret], [WPof_bind] and
    [WPof_mono] hold for every algebra ([MonadAlgebra.v], Loom's Thm. 3.3),
    so each composite is an effect observation as soon as it is written.

    [WPof_st] and [WPof_rd] state what the whole stack computes, ONCE and
    parametrically in the base algebra and the handler: run the program,
    then collapse the outcome set with the base algebra, sending divergence
    to [dh].  Instantiating the two bases against the two handlers gives the
    four observations of [stdivnd] -- [WPof_st_DWP] and friends below are
    literally [obsDWP] / [obsDWLP] / [obsAWP] / [obsAWLP]'s readings, each
    obtained by [etransitivity] through the generic theorem.

    Note the explicit [@] on [mu] / [bind] / [ret] in the two [mu_*_bind]
    helpers.  Left to inference these take minutes: [Monad_optionT] and
    [Monad_stateT] are recursive instances, so an unresolved [Monad ?M]
    sends the search exponential (root CLAUDE.md).  Pinned, the file
    compiles in under a second. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad ReaderMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StExcNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import DivNonDet_WPure_Algebra.

Section SetMStacks.
  (** The base algebra: demonic or angelic, supplied by the caller. *)
  Context (AM : MAlg SetM Prop).
  (** The divergence handler: [False] total, [True] liberal. *)
  Variable dh : Prop.

  Definition MAlg_div : MAlg (optionT SetM) Prop := MAlg_optionT (AM := AM) dh.

  Section St.
    Variable S : Type.

    Definition MAlg_st
      : @MAlg (stateT S (optionT SetM)) (S -> Prop) _ _ (AsnLang_fun S AsnLang_Prop) :=
      MAlg_stateT (AM := MAlg_div) S.

    (** The whole stack's WP, in one statement: run [m] from [s], collapse
        the outcome set with the BASE algebra, sending divergence to [dh]. *)
    Theorem WPof_st {A} (m : stateT S (optionT SetM) A) (post : A -> S -> Prop) (s : S) :
      aeq (@WPof _ _ _ _ (AsnLang_fun S AsnLang_Prop) MAlg_st A m post s)
          (mu (bind (unOptionT (runStateT m s))
                 (fun oa => ret (match oa with
                                 | Some (a, s') => post a s'
                                 | None => dh
                                 end)))).
    Proof.
      unfold WPof, MAlg_st, MAlg_div.
      cbn [mu MAlg_stateT mu_stateT MAlg_optionT mu_optionT].
      apply mu_proper.
      cbn [bind ret Monad_stateT Monad_optionT runStateT unOptionT].
      etransitivity; [ apply bind_bind |].
      etransitivity; [ apply bind_bind |].
      apply Proper_bind; [ reflexivity | intros [[a s']|] ].
      - etransitivity; [ apply bind_ret_l |]. cbv beta iota. cbn [fst snd].
        etransitivity; [ apply bind_ret_l |]. cbv beta iota. reflexivity.
      - etransitivity; [ apply bind_ret_l |]. cbv beta iota.
        etransitivity; [ apply bind_ret_l |]. cbv beta iota. reflexivity.
    Qed.

  End St.

  Section Rd.
    Variable R : Type.

    Definition MAlg_rd
      : @MAlg (readerT R (optionT SetM)) (R -> Prop) _ _ (AsnLang_fun R AsnLang_Prop) :=
      MAlg_readerT (AM := MAlg_div) R.

    Theorem WPof_rd {A} (m : readerT R (optionT SetM) A) (post : A -> R -> Prop) (r : R) :
      aeq (@WPof _ _ _ _ (AsnLang_fun R AsnLang_Prop) MAlg_rd A m post r)
          (mu (bind (unOptionT (runReaderT m r))
                 (fun oa => ret (match oa with
                                 | Some a => post a r
                                 | None => dh
                                 end)))).
    Proof.
      unfold WPof, MAlg_rd, MAlg_div.
      cbn [mu MAlg_readerT mu_readerT MAlg_optionT mu_optionT].
      apply mu_proper.
      cbn [bind ret Monad_readerT Monad_optionT runReaderT unOptionT].
      etransitivity; [ apply bind_bind |].
      etransitivity; [ apply bind_bind |].
      apply Proper_bind; [ reflexivity | intros [a|] ].
      - etransitivity; [ apply bind_ret_l |]. cbv beta iota.
        etransitivity; [ apply bind_ret_l |]. cbv beta iota. reflexivity.
      - etransitivity; [ apply bind_ret_l |]. cbv beta iota.
        etransitivity; [ apply bind_ret_l |]. cbv beta iota. reflexivity.
    Qed.

  End Rd.

End SetMStacks.

(* ================================================================= *)
(** ** The four observations of [stdivnd], by composition             *)
(* ================================================================= *)


Lemma mu_demonic_bind {A} (X : SetM A) (k : A -> Prop) :
  @mu SetM Prop Monad_SetM Eq1_SetM AsnLang_Prop MAlg_SetM_demonic
     (@bind SetM Monad_SetM A Prop X (fun a => @ret SetM Monad_SetM Prop (k a)))
  <-> (forall a, X a -> k a).
Proof.
  cbn [mu MAlg_SetM_demonic]. unfold mu_SetM_demonic. cbn [bind ret Monad_SetM].
  split.
  - intros H a Ha. exact (H (k a) (ex_intro _ a (conj Ha eq_refl))).
  - intros H p [a [Ha ->]]. exact (H a Ha).
Qed.

Lemma mu_angelic_bind {A} (X : SetM A) (k : A -> Prop) :
  @mu SetM Prop Monad_SetM Eq1_SetM AsnLang_Prop MAlg_SetM_angelic
     (@bind SetM Monad_SetM A Prop X (fun a => @ret SetM Monad_SetM Prop (k a)))
  <-> (exists a, X a /\ k a).
Proof.
  cbn [mu MAlg_SetM_angelic]. unfold mu_SetM_angelic. cbn [bind ret Monad_SetM].
  split.
  - intros [p [[a [Ha ->]] Hp]]. exists a. split; assumption.
  - intros [a [Ha Hk]]. exists (k a). split; [| exact Hk ].
    exists a. split; [ exact Ha | reflexivity ].
Qed.

Section Four.
  Variable S : Type.

  Definition MAlg_st_DWP  := MAlg_st MAlg_SetM_demonic False S.
  Definition MAlg_st_DWLP := MAlg_st MAlg_SetM_demonic True  S.
  Definition MAlg_st_AWP  := MAlg_st MAlg_SetM_angelic False S.
  Definition MAlg_st_AWLP := MAlg_st MAlg_SetM_angelic True  S.

  Context {A : Type} (m : stateT S (optionT SetM) A) (post : A -> S -> Prop) (s : S).

  Theorem WPof_st_DWP :
    @WPof _ _ _ _ (AsnLang_fun S AsnLang_Prop) MAlg_st_DWP A m post s
    <-> (forall oa, unOptionT (runStateT m s) oa ->
                    match oa with Some (a, s') => post a s' | None => False end).
  Proof.
    etransitivity; [ exact (WPof_st MAlg_SetM_demonic False S m post s) |].
    apply mu_demonic_bind.
  Qed.

  Theorem WPof_st_DWLP :
    @WPof _ _ _ _ (AsnLang_fun S AsnLang_Prop) MAlg_st_DWLP A m post s
    <-> (forall oa, unOptionT (runStateT m s) oa ->
                    match oa with Some (a, s') => post a s' | None => True end).
  Proof.
    etransitivity; [ exact (WPof_st MAlg_SetM_demonic True S m post s) |].
    apply mu_demonic_bind.
  Qed.

  Theorem WPof_st_AWP :
    @WPof _ _ _ _ (AsnLang_fun S AsnLang_Prop) MAlg_st_AWP A m post s
    <-> (exists oa, unOptionT (runStateT m s) oa
                    /\ match oa with Some (a, s') => post a s' | None => False end).
  Proof.
    etransitivity; [ exact (WPof_st MAlg_SetM_angelic False S m post s) |].
    apply mu_angelic_bind.
  Qed.

  Theorem WPof_st_AWLP :
    @WPof _ _ _ _ (AsnLang_fun S AsnLang_Prop) MAlg_st_AWLP A m post s
    <-> (exists oa, unOptionT (runStateT m s) oa
                    /\ match oa with Some (a, s') => post a s' | None => True end).
  Proof.
    etransitivity; [ exact (WPof_st MAlg_SetM_angelic True S m post s) |].
    apply mu_angelic_bind.
  Qed.

End Four.
