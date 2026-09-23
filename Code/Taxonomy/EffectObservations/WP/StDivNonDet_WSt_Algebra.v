(** * The four WP observations of [stdivnd], assembled from algebras.

    [stdivnd S A = stateT S divnd A]  -->  [WSt S A = stateT S WPure A]

      - [divnd]  : COLLAPSED, by the four algebras of
                   [DivNonDet_WPure_Algebra.v];
      - [stateT] : PRESERVED, by [MMor_stateT].

    [StDivNonDet_WSt.v] defines the same four by writing each predicate
    transformer out, proving a [wpure_mono] lemma for each, and then
    proving [_ret] and [_bind] for each -- eight law proofs, all of the
    same shape.  Here the state layer is threaded -- at each initial state
    the observation IS the pure one of the program run from that state --
    so the eight laws are citations.

    The triple machinery at the end is [StDivNonDet_WSt.v]'s, adapted: it is
    generic in the observation, so it serves all four.  Its monotonicity
    side condition is discharged here rather than assumed -- every element
    of [WSt] is monotone by construction ([getWPure_mono]). *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import
  DivNonDet_WPure_Algebra.

Import MonadNotation.
Open Scope monad_scope.

Local Definition getNE_T {S A} (m : stdivndNE S A) : stateT S (optionT SetM) A :=
  StDivNonDet.getNE m.
#[local] Coercion getNE_T : stdivndNE >-> stateT.

Section Observations.
  Variable S : Type.

  (** One lift, four times. *)
  Definition MMorSt_DWP  : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_DWP.
  Definition MMorSt_DWLP : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_DWLP.
  Definition MMorSt_AWP  : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_AWP.
  Definition MMorSt_AWLP : MMor (stdivnd S) (WSt S) := MMor_stateT S MMor_AWLP.

  Definition obsDWP {A} (m : stdivndNE S A) : WSt S A := mmor MMorSt_DWP (getNE m).
  Definition obsDWLP {A} (m : stdivndNE S A) : WSt S A := mmor MMorSt_DWLP (getNE m).
  Definition obsAWP {A} (m : stdivndNE S A) : WSt S A := mmor MMorSt_AWP (getNE m).
  Definition obsAWLP {A} (m : stdivndNE S A) : WSt S A := mmor MMorSt_AWLP (getNE m).

  (** ** What each one says, in terms of the outcome set

      [_at] says the observation at each initial state is the PURE
      observation of the program run from there; composing it with the
      [divnd] characterisation gives the statements
      [StDivNonDet_WSt.v] proves by unfolding a hand-written transformer. *)

  Lemma obsDWP_at {A} (m : stdivndNE S A) (s : S) :
    runStateT (obsDWP m) s = obsDWPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsDWLP_at {A} (m : stdivndNE S A) (s : S) :
    runStateT (obsDWLP m) s = obsDWLPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsAWP_at {A} (m : stdivndNE S A) (s : S) :
    runStateT (obsAWP m) s = obsAWPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsAWLP_at {A} (m : stdivndNE S A) (s : S) :
    runStateT (obsAWLP m) s = obsAWLPp (runStateT m s).
  Proof. reflexivity. Qed.

  Lemma obsDWP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWP m) s post
    <-> (forall oa, unOptionT (runStateT m s) oa ->
                    match oa with Some r => post r | None => False end).
  Proof. rewrite obsDWP_at. apply obsDWPp_get. Qed.

  Lemma obsDWLP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWLP m) s post
    <-> (forall oa, unOptionT (runStateT m s) oa ->
                    match oa with Some r => post r | None => True end).
  Proof. rewrite obsDWLP_at. apply obsDWLPp_get. Qed.

  Lemma obsAWP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsAWP m) s post
    <-> (exists r, unOptionT (runStateT m s) (Some r) /\ post r).
  Proof. rewrite obsAWP_at. apply obsAWPp_get. Qed.

  Lemma obsAWLP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsAWLP m) s post
    <-> ((exists r, unOptionT (runStateT m s) (Some r) /\ post r)
         \/ unOptionT (runStateT m s) None).
  Proof. rewrite obsAWLP_at. apply obsAWLPp_get. Qed.

  (** ** The morphism laws, for free *)

  Theorem obsDWP_ret {A} (a : A) : eq1 (obsDWP (ret a : stdivndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_DWP) A a). Qed.
  Theorem obsDWP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsDWP (x >>= f)) (obsDWP x >>= (fun a => obsDWP (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_DWP) A B x f). Qed.

  Theorem obsDWLP_ret {A} (a : A) : eq1 (obsDWLP (ret a : stdivndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_DWLP) A a). Qed.
  Theorem obsDWLP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsDWLP (x >>= f)) (obsDWLP x >>= (fun a => obsDWLP (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_DWLP) A B x f). Qed.

  Theorem obsAWP_ret {A} (a : A) : eq1 (obsAWP (ret a : stdivndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_AWP) A a). Qed.
  Theorem obsAWP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsAWP (x >>= f)) (obsAWP x >>= (fun a => obsAWP (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_AWP) A B x f). Qed.

  Theorem obsAWLP_ret {A} (a : A) : eq1 (obsAWLP (ret a : stdivndNE S A)) (ret a).
  Proof. exact (mmor_ret (MMor := MMorSt_AWLP) A a). Qed.
  Theorem obsAWLP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) :
    eq1 (obsAWLP (x >>= f)) (obsAWLP x >>= (fun a => obsAWLP (f a))).
  Proof. exact (mmor_bind (MMor := MMorSt_AWLP) A B x f). Qed.

End Observations.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.
Arguments obsDWP_unfold {_} {_}.
Arguments obsDWLP_unfold {_} {_}.
Arguments obsAWP_unfold {_} {_}.
Arguments obsAWLP_unfold {_} {_}.

Inductive approxKindWP := | SubsetOf | SupersetOf.

#[program] Definition pp2wp_subset {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A :=
  mkStateT (fun s0 => mkWPure (fun p => pre s0 /\ (forall r, post r -> p r)) _).
Next Obligation.
  intros p q Hpq [Hpre Hsub]. split; [ exact Hpre |].
  intros r Hr. exact (Hpq r (Hsub r Hr)).
Qed.

#[program] Definition pp2wp_superset {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A :=
  mkStateT (fun s0 => mkWPure (fun p => (forall r, p r -> post r) -> pre s0) _).
Next Obligation.
  intros p q Hpq H Hsub. apply H. intros r Hr. exact (Hsub r (Hpq r Hr)).
Qed.

Section NDWPTriples.

  (** Generic in the observation, and stated for plain [stdivnd]: the
      observations of this file do not need the nonempty subset type. *)

  Definition tripleWP {S A}
    (obs : stdivndNE S A -> WSt S A)
    (prog : stdivndNE S A)
    (pre : S -> Prop)
    (kind : approxKindWP)
    (post : A * S -> Prop) : Prop :=
    match kind with
    | SubsetOf   => forall s, pre s -> runStateT (obs prog) s post
    | SupersetOf => forall s, runStateT (obs prog) s post -> pre s
    end.

  Definition tripleWPspec {S A}
    (obs : stdivndNE S A -> WSt S A)
    (prog : stdivndNE S A)
    (pre : S -> Prop)
    (kind : approxKindWP)
    (post : A * S -> Prop) : Prop :=
    match kind with
    | SubsetOf   => ordWSt (obs prog) (pp2wp_subset pre post)
    | SupersetOf => ordWSt (pp2wp_superset pre post) (obs prog)
    end.

  Theorem tripleWPDefEq {S A}
    (obs : stdivndNE S A -> WSt S A)
    (prog : stdivndNE S A)
    (kind : approxKindWP)
    (pre : S -> Prop)
    (post : A * S -> Prop) :
    tripleWP obs prog pre kind post <-> tripleWPspec obs prog pre kind post.
  Proof.
    pose proof (fun s => getWPure_mono (runStateT (obs prog) s)) as Hmono.
    unfold tripleWP, tripleWPspec, ordWSt, pp2wp_subset, pp2wp_superset.
    destruct kind; cbn [runStateT]; split.
    - intros H s p [Hpre Hsub]. apply (Hmono s post p Hsub). exact (H s Hpre).
    - intros H s Hpre. apply (H s post). split; [ exact Hpre | intros r hr; exact hr ].
    - intros H s p Hwp Hsub. apply H. apply (Hmono s p post Hsub). exact Hwp.
    - intros H s Hwp. apply (H s post Hwp). intros r hr; exact hr.
  Qed.

End NDWPTriples.

(* ================================================================= *)
(** ** The same observation, from the ALGEBRA transformer            *)
(* ================================================================= *)

(** The four observations above are assembled with [MMor_stateT], which
    PRESERVES the state layer.  Loom takes the other route (Sec. 3.4, eq.
    14): [stateT] carries an ALGEBRA too, with the assertion language
    changing from [L] to [S -> L].  [MonadAlgebra.MAlg_stateT] is that
    transformer, and this section checks it computes what it should --
    applied to the demonic-total algebra of [divnd] it yields exactly
    [obsDWP]'s reading, so the two routes agree.

    The shapes differ: Loom's [Cont (S -> Prop) A] is
    [(A -> S -> Prop) -> S -> Prop], where [WSt S A] is
    [S -> (A * S -> Prop) -> Prop].  They are isomorphic by currying and a
    swap; the statement below is the algebra route read at that isomorphism. *)

Section LoomStateAlgebra.
  Variable S : Type.

  (** The state algebra, from the divergence algebra, by Loom's eq. (14). *)
  Definition MAlg_DWP_St
    : @MAlg (stateT S (optionT SetM)) (S -> Prop) _ _ (AsnLang_fun S AsnLang_Prop) :=
    @MAlg_stateT (optionT SetM) _ _ _ _ Prop AsnLang_Prop MAlg_DWP S.

  Lemma WPof_St_DWP {A} (m : stateT S (optionT SetM) A)
    (post : A -> S -> Prop) (s : S) :
    @WPof _ _ _ _ (AsnLang_fun S AsnLang_Prop) MAlg_DWP_St A m post s
    <-> (forall oa, unOptionT (runStateT m s) oa ->
                    match oa with Some (a, s') => post a s' | None => False end).
  Proof.
    cbv [WPof MAlg_DWP_St MAlg_stateT mu_stateT MAlg_DWP MAlg_optionT
         mu_optionT MAlg_SetM_demonic mu mu_SetM_demonic].
    cbn [bind ret Monad_stateT Monad_optionT runStateT unOptionT Monad_SetM].
    split.
    - intros H oa Ho. destruct oa as [[a s']|].
      + apply (H (post a s')). exists (Some (post a s')). split; [| reflexivity ].
        exists (Some (post a, s')). split; [| reflexivity ].
        exists (Some (a, s')). split; [ exact Ho | reflexivity ].
      + apply (H False). exists None. split; [| reflexivity ].
        exists None. split; [| reflexivity ].
        exists None. split; [ exact Ho | reflexivity ].
    - intros H p [a [[a0 [[a1 [Ho H1]] H2]] H3]].
      destruct a1 as [[v s'']|]; cbn in H1; subst a0; cbn in H2; subst a;
        cbn in H3; subst p.
      + exact (H (Some (v, s'')) Ho).
      + exact (H None Ho).
  Qed.

End LoomStateAlgebra.
