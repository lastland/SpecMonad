From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import NewGaloisConnections.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

(** * SP observations for [stdivnd]

    [stdivnd S A = stateT S (optionT SetM) A] is the nondeterministic, possibly
    divergent stateful monad of [StDivNonDet]: its outcome set has type
    [option (A * S) -> Prop], with [None] read as divergence.

    The targets [ASPStExc], [DSLPStExc], [DSPStExc], and [ASLPStExc] come
    from [BaseSpecMonads].  Each bundles a transformer of shape
    [(S -> Prop) -> option (A * S) -> Prop] with its well-formedness proof.
    This file supplies the computation-specific readings, their return/bind
    preservation laws, and the triples that use them.

    Unlike [StDivExcNonDet_SPStExc.v], which projects away divergence,
    this file retains [None] as an outcome.  Its transformers can therefore
    constrain divergence directly:
    [getASPStExc (obsASP m) pre None] says "some [pre]-state may diverge" and
    [getDSLPStExc (obsDSLP m) pre None] says "every state that may diverge
    satisfies [pre]".

    [FullOutcomeObs] qualifies these names.  The file imports the computation
    and specification modules, not a sibling observation module. *)

Module FullOutcomeObs.

Section NDObservations.
  Variable S : Type.

  (** The raw outcome laws are owned by the computation module
      [StExcNonDet]: [stdivnd S] IS [stateT S (optionT SetM)] with the same
      dictionaries, so [StExcNonDet.outcomes_ret] and
      [StExcNonDet.outcomes_bind] — with [None] read here as the absorbing
      divergence token rather than an exception — apply to this module's
      [ret]/[>>=] by definitional conversion. *)

  (* ================================================================== *)
  (** ** The four observations                                          *)
  (* ================================================================== *)

  (** Outcome space is the FULL [option (A * S)]: [r = None] is divergence,
      so these observations can constrain divergent behaviour. *)
  #[program] Definition obsASP {A} (m : stdivnd S A) : ASPMonad.ASPStExc S A :=
    fun pre (r : option (A * S)) => exists s, pre s /\ unOptionT (runStateT m s) r.
  Next Obligation.
    intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hr ].
    - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hr ].
  Qed.

  #[program] Definition obsDSLP {A} (m : stdivnd S A) : DSLPMonad.DSLPStExc S A :=
    fun pre (r : option (A * S)) => forall s, unOptionT (runStateT m s) r -> pre s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => unOptionT (runStateT m s) r)).
  Qed.

  #[program] Definition obsDSP {A} (m : stdivnd S A) : DSPMonad.DSPStExc S A :=
    fun pre (r : option (A * S)) => (obsASP m pre r) /\ (obsDSLP m pre r).
  Next Obligation.
    exact (dsp_shape_wf S (fun s r => unOptionT (runStateT m s) r)).
  Qed.

  #[program] Definition obsASLP {A} (m : stdivnd S A) : ASLPMonad.ASLPStExc S A :=
    fun pre (r : option (A * S)) => (obsASP m pre r) \/ (obsDSLP m pre r).
  Next Obligation.
    exact (aslp_shape_wf S (fun s r => unOptionT (runStateT m s) r)).
  Qed.

  (** Applying an observation IS the corresponding reading of the outcome set. *)
  Lemma getProgASP_obsASP {A} (m : stdivnd S A) pre r :
    getASPStExc (obsASP m) pre r
    <-> (exists s, pre s /\ unOptionT (runStateT m s) r).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : stdivnd S A) pre r :
    getDSLPStExc (obsDSLP m) pre r
    <-> (forall s, unOptionT (runStateT m s) r -> pre s).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgDSP_obsDSP {A} (m : stdivnd S A) pre r :
    getDSPStExc (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) r)
         /\ (forall s, unOptionT (runStateT m s) r -> pre s)).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgASLP_obsASLP {A} (m : stdivnd S A) pre r :
    getASLPStExc (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) r)
         \/ (forall s, unOptionT (runStateT m s) r -> pre s)).
  Proof. split; intro H; exact H. Qed.

  (* ================================================================== *)
  (** ** Each observation is a monad morphism                           *)
  (* ================================================================== *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ASPStExc. intros pre r. split.
    - intros [s [Hp Hr]]. exists s.
      split; [ exact Hp | exact (proj1 (StExcNonDet.outcomes_ret S a s r) Hr) ].
    - intros [s [Hp Heq]]. exists s.
      split; [ exact Hp | exact (proj2 (StExcNonDet.outcomes_ret S a s r) Heq) ].
  Qed.

  Theorem obsASP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    unfold eq1, Eq1__ASPStExc. intros pre r. split.
    - intros [s [Hp Hrel]].
      apply (StExcNonDet.outcomes_bind S x f s r) in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[a s']|].
      + left. exists a, s'. split; [| exact Hk ].
        exists s. split; [ exact Hp | exact Hx ].
      + right. split; [ exact Hk |]. exists s. split; [ exact Hp | exact Hx ].
    - intros [[a [s' [[s [Hp Hx]] Hf]]] | [Hr [s [Hp Hx]]]].
      + exists s. split; [ exact Hp |].
        apply (StExcNonDet.outcomes_bind S x f s r).
        exists (Some (a, s')). split; [ exact Hx | exact Hf ].
      + exists s. split; [ exact Hp |].
        apply (StExcNonDet.outcomes_bind S x f s r).
        exists None. split; [ exact Hx | exact Hr ].
  Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__DSLPStExc. intros pre r. split.
    - intros H s0 Heq.
      exact (H s0 (proj2 (StExcNonDet.outcomes_ret S a s0 r) Heq)).
    - intros H s Hr. exact (H s (proj1 (StExcNonDet.outcomes_ret S a s r) Hr)).
  Qed.

  Theorem obsDSLP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    unfold eq1, Eq1__DSLPStExc. intros pre r. split.
    - intro H. split.
      + intros a s' Hf s Hx. apply H.
        apply (StExcNonDet.outcomes_bind S x f s r).
        exists (Some (a, s')). split; [ exact Hx | exact Hf ].
      + intros Hr s Hx. apply H.
        apply (StExcNonDet.outcomes_bind S x f s r).
        exists None. split; [ exact Hx | exact Hr ].
    - intros [H1 H2] s Hrel.
      apply (StExcNonDet.outcomes_bind S x f s r) in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[a s']|].
      + exact (H1 a s' Hk s Hx).
      + exact (H2 Hk s Hx).
  Qed.

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__DSPStExc. intros pre r.
    apply (dsp_cong S
             (fun s r0 => unOptionT (runStateT (ret a : stdivnd S A) s) r0)
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. exact (StExcNonDet.outcomes_ret S a s r0).
  Qed.

  Theorem obsDSP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    unfold eq1, Eq1__DSPStExc. intros pre r.
    rewrite (bindDSPProg_dsp S (obsDSP x) (fun a => obsDSP (f a))).
    refine (iff_trans (dsp_cong S _ _ (StExcNonDet.outcomes_bind S x f) pre r) _).
    exact (iff_sym (dsp_cong S _ _
                      (dsp_comp_recov_option S A B
                         (fun (s : S) (o : option (A * S)) =>
                            unOptionT (runStateT x s) o)
                         (fun (a : A) (t : S) (ob : option (B * S)) =>
                            unOptionT (runStateT (f a) t) ob)) pre r)).
  Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : stdivnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ASLPStExc. intros pre r.
    apply (aslp_cong S
             (fun s r0 => unOptionT (runStateT (ret a : stdivnd S A) s) r0)
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. exact (StExcNonDet.outcomes_ret S a s r0).
  Qed.

  Theorem obsASLP_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof.
    unfold eq1, Eq1__ASLPStExc. intros pre r.
    rewrite (bindASLPProg_aslp S (obsASLP x) (fun a => obsASLP (f a))).
    refine (iff_trans (aslp_cong S _ _ (StExcNonDet.outcomes_bind S x f) pre r) _).
    exact (iff_sym (aslp_cong S _ _
                      (aslp_comp_recov_option S A B
                         (fun (s : S) (o : option (A * S)) =>
                            unOptionT (runStateT x s) o)
                         (fun (a : A) (t : S) (ob : option (B * S)) =>
                            unOptionT (runStateT (f a) t) ob)) pre r)).
  Qed.

End NDObservations.

Arguments obsASP {_} {_}.
Arguments obsDSLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsASLP {_} {_}.

(* ==================================================================== *)
(** * Triples                                                            *)
(* ==================================================================== *)

Section NDTriples.

  Definition tripleASP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getASPStExc (obsASP prog) pre r -> post r
    | Under => forall r, post r -> getASPStExc (obsASP prog) pre r
    end.

  Definition tripleDSLP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getDSLPStExc (obsDSLP prog) pre r -> post r
    | Under => forall r, post r -> getDSLPStExc (obsDSLP prog) pre r
    end.

  Definition tripleDSP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getDSPStExc (obsDSP prog) pre r -> post r
    | Under => forall r, post r -> getDSPStExc (obsDSP prog) pre r
    end.

  Definition tripleASLP {S A}
    (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getASLPStExc (obsASLP prog) pre r -> post r
    | Under => forall r, post r -> getASLPStExc (obsASLP prog) pre r
    end.

  #[program] Definition pp2asp_over' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPStExc S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hc ].
  Qed.

  #[program] Definition pp2dslp_under' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPStExc S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  (** [tripleASP _ Over pre post] is [Out <= {(s,r) | pre s -> post r}]. *)
  Theorem tripleASP_over_inmonad {S A} (prog : stdivnd S A) pre post :
    tripleASP prog Over pre post
    <-> ordASPStExc (obsASP prog) (pp2asp_over' pre post).
  Proof.
    split.
    - intros H p r [s [Hp Hout]]. exists s. split; [ exact Hp |].
      intro Hpre. exact (H r (ex_intro _ s (conj Hpre Hout))).
    - intros H r [s [Hpre Hout]].
      destruct (H pre r (ex_intro _ s (conj Hpre Hout))) as [s1 [Hp1 Himp]].
      exact (Himp Hp1).
  Qed.

  (** Dually, [tripleDSLP _ Under pre post] is [Out <= {(s,r) | post r -> pre s}].
      Note the comparison REVERSES, because reading a relation as a DSLP is
      antitone in the relation. *)
  Theorem tripleDSLP_under_inmonad {S A} (prog : stdivnd S A) pre post :
    tripleDSLP prog Under pre post
    <-> ordDSLPStExc (pp2dslp_under' pre post) (obsDSLP prog).
  Proof.
    split.
    - intros H p r Hd s Hout. apply Hd. intro Hpost. exact (H r Hpost s Hout).
    - intros H r Hpost s Hout.
      exact (H (fun t => post r -> pre t) r (fun t Ht => Ht) s Hout Hpost).
  Qed.

  (** ** The other two directions, via an order scoped to one precondition

      The targets below characterize [tripleASP _ Under] and
      [tripleDSLP _ Over] using orders at [pre].  Their well-formedness
      conditions force side conditions: ASP is false at the empty
      precondition, while DSLP is true at the full precondition.

      Evaluating the ASP target at [pre] therefore recovers [post] only
      when [exists s, pre s]; the DSLP target requires [exists s, ~ pre s].
      The following [_at] lemmas state these conditions explicitly. *)

  #[program] Definition pp2asp_under' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPStExc S A :=
    fun p r => exists s, p s /\ (pre s /\ post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hc ].
  Qed.

  #[program] Definition pp2dslp_over' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPStExc S A :=
    fun p r => forall s, (~ post r /\ ~ pre s) -> p s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => ~ post r /\ ~ pre s)).
  Qed.

  (** Each target, evaluated AT [pre] itself, collapses to [post]. *)

  Lemma pp2asp_under'_at {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hne : exists s, pre s) (r : option (A * S)) :
    getASPStExc (pp2asp_under' pre post) pre r <-> post r.
  Proof.
    split.
    - intros [s [_ [_ Hpost]]]. exact Hpost.
    - intro Hpost. destruct Hne as [s Hs].
      exists s. split; [ exact Hs | split; [ exact Hs | exact Hpost ] ].
  Qed.

  Lemma pp2dslp_over'_at {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hco : exists s, ~ pre s) (r : option (A * S)) :
    getDSLPStExc (pp2dslp_over' pre post) pre r <-> post r.
  Proof.
    split.
    - intro H. apply NNPP. intro Hnp. destruct Hco as [s0 Hs0].
      exact (Hs0 (H s0 (conj Hnp Hs0))).
    - intros Hpost s [Hnp _]. destruct (Hnp Hpost).
  Qed.

  (** [Under] compares [target <= obs]; [Over] compares [obs <= target] — the
      same convention as the two global cases above. *)

  Theorem tripleASP_under_inmonad {S A} (prog : stdivnd S A) pre post
    (Hne : exists s, pre s) :
    tripleASP prog Under pre post
    <-> ordASPStExcAt pre (pp2asp_under' pre post) (obsASP prog).
  Proof.
    split.
    - intros H r Ht. exact (H r (proj1 (pp2asp_under'_at pre post Hne r) Ht)).
    - intros H r Hpost. exact (H r (proj2 (pp2asp_under'_at pre post Hne r) Hpost)).
  Qed.

  Theorem tripleDSLP_over_inmonad {S A} (prog : stdivnd S A) pre post
    (Hco : exists s, ~ pre s) :
    tripleDSLP prog Over pre post
    <-> ordDSLPStExcAt pre (obsDSLP prog) (pp2dslp_over' pre post).
  Proof.
    split.
    - intros H r Hd. exact (proj2 (pp2dslp_over'_at pre post Hco r) (H r Hd)).
    - intros H r Hd. exact (proj1 (pp2dslp_over'_at pre post Hco r) (H r Hd)).
  Qed.
End NDTriples.

Arguments tripleASP {_} {_}.
Arguments tripleDSLP {_} {_}.
Arguments tripleDSP {_} {_}.
Arguments tripleASLP {_} {_}.

End FullOutcomeObs.
