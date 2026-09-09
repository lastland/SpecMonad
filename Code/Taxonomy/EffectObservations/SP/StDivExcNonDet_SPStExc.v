(** * SP observations of [stdivexcnd] into [SPStExc]

    The observations [obsASP] / [obsDSLP] / [obsDSP] / [obsASLP], the triples
    they support, and worked examples over [progEx].  How the four
    observations relate to one another — and to the WP observations — lives in
    [Taxonomy_StDivExcNonDet_StExc.v]. *)

From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import BaseGaloisConnections NewGaloisConnections.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy.EffectObservations.WP Require Import StDivExcNonDet_WStExc.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.

From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.

Section ObsASP.
  Variable S : Type.
  
  #[program] Definition obsASP {A} (m : stdivexcnd S A) : ASPStExc S A :=
    fun pre r => exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
      exists s. split; [reflexivity | exact Hr].
    - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
      exists s0. split; [exact Hp | exact Hr].
  Qed.

  Lemma getProg_obsASP {A} (m : stdivexcnd S A) pre r :
    getASPStExc (obsASP m) pre r
    <-> exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
  Proof. split; intro H; exact H. Qed.

  (* ---------------- [obsASP] is a monad morphism ---------------- *)

  Lemma outcomes_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) s ob :
    unOptionT (unOptionT (runStateT (x >>= f) s)) ob <->
    (exists oy, unOptionT (unOptionT (runStateT x s)) oy /\
       match oy with
       | Some (Some (a, s')) => unOptionT (unOptionT (runStateT (f a) s')) ob
       | Some None => ob = Some None
       | None => ob = None
       end).
  Proof.
    cbn. split; intros [oy [H1 H2]]; exists oy; split; [exact H1 | | exact H1 |];
      destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  Qed.

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : stdivexcnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ASPStExc. intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
      destruct r as [[b s']|]; cbn in Hr; congruence.
    - intros [s [Hp Heq]]. exists s. split; [exact Hp |].
      destruct r as [[b s']|]; cbn; congruence.
  Qed.

  Theorem obsASP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    unfold eq1, Eq1__ASPStExc. intros pre r. split.
    - intros [s [Hp Hrel]]. apply outcomes_bind in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[[a s']|]|].
      + left. exists a, s'. split; [| exact Hk].
        exists s. split; [exact Hp | exact Hx].
      + right. split; [congruence |]. exists s. split; [exact Hp | exact Hx].
      + discriminate Hk.
    - intros [[a [s' [[s [Hp Hx]] Hf]]] | [Hr [s [Hp Hx]]]].
      + exists s. split; [exact Hp |]. apply outcomes_bind.
        exists (Some (Some (a, s'))). split; [exact Hx | exact Hf].
      + exists s. split; [exact Hp |]. apply outcomes_bind.
        exists (Some None). split; [exact Hx | congruence].
  Qed.

End ObsASP.

Arguments obsASP {_} {_}.

Section ASPTriple.
  Definition tripleASP {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
      match kind with
      | Over => forall r, getASPStExc (obsASP prog) pre r -> post r
      | Under => forall r, post r -> getASPStExc (obsASP prog) pre r
      end.

  (** Neither of these is [SingletonProg], so they are plain [SPStExc]: at the
      empty precondition [pp2_over] still yields [post r], and at the full
      one [pp2_under] holds even when no single state carries [pre]. *)
  Definition tripleASPspec {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match kind with
    | Over => ordSPStExc (getASPStExc (obsASP prog)) (pp2_over pre post)
    | Under => ordSPStExc (pp2_under pre post) (getASPStExc (obsASP prog))
    end.

  Theorem tripleASPDefEq {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleASP prog kind pre post <-> tripleASPspec prog kind pre post.
  Proof.
    unfold tripleASP, tripleASPspec, ordSPStExc, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: instantiate the quantified precondition at [pre] itself *)
      intros H p r [Hsub Hpost]. destruct (H r Hpost) as [s [Hpre Hreach]].
      exists s. split; [ exact (Hsub s Hpre) | exact Hreach ].
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - intros H p r [s [Hp Hreach]] Hsub.
      exact (H r (ex_intro _ s (conj (Hsub s Hp) Hreach))).
    - intros H r Hobs. exact (H pre r Hobs (fun s Hs => Hs)).
  Qed.


  (** For this ONE direction the comparison target can itself be an ASP:
      [tripleASP _ Over pre post] unfolds to the relation inclusion
      [Out <= {(s,r) | pre s -> post r}], and that relation read as an ASP is
      the target.  (The [Under] direction has no such form — it asserts that
      SOME [pre]-state reaches [r], a disjunction over states, and the ASP
      order only ever expresses containment of one fixed relation.) *)
  #[program] Definition pp2asp_over' {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : ASPStExc S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hm]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hm ].
    - intros [s0 [Hp [s [Heq Hm]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hm ].
  Qed.

  Theorem tripleASP_over_inmonad {S A}
    (prog : stdivexcnd S A)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
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
End ASPTriple.

Arguments tripleASP {_} {_}.

Section ObsDSLP.
  Variable S : Type.

  (** The demonic-liberal observation: [r] forces [pre] at every state that can
      reach it.  Dually to [obsASP], which is the ASP of the same terminating
      slice [unOptionT (unOptionT (runStateT m s)) (Some r)], this is its DSLP —
      so [MSingletonProg] is immediate from [dslp_msingleton]. *)
  #[program] Definition obsDSLP {A} (m : stdivexcnd S A) : DSLPStExc S A :=
    fun pre r => forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
  Qed.

  Lemma getProgMSP_obsDSLP {A} (m : stdivexcnd S A) pre r :
    getDSLPStExc (obsDSLP m) pre r
    <-> forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
  Proof. split; intro H; exact H. Qed.

  (* --------------- [obsDSLP] is a monad morphism --------------- *)

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : stdivexcnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__DSLPStExc. intros pre r. split.
    - intros H s0 Heq. apply H. subst r. cbn. reflexivity.
    - intros H s Hr. apply H. cbn in Hr. congruence.
  Qed.

  Theorem obsDSLP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    unfold eq1, Eq1__DSLPStExc. intros pre r. split.
    - intro H. split.
      + (* normal return: [x] reaches [Some (a, s')], then [f a] reaches [r] *)
        intros a s' Hf s Hx. apply H. apply outcomes_bind.
        exists (Some (Some (a, s'))). split; [exact Hx | exact Hf].
      + (* exception: [x] raises, and [r] must be [None] *)
        intros Hr s Hx. apply H. apply outcomes_bind.
        exists (Some None). split; [exact Hx | congruence].
    - intros [H1 H2] s Hrel. apply outcomes_bind in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[[a s']|]|].
      + exact (H1 a s' Hk s Hx).
      + assert (Hr : r = None) by congruence. exact (H2 Hr s Hx).
      + discriminate Hk.
  Qed.
End ObsDSLP.

Arguments obsDSLP {_} {_}.

Section DSLPTriple.
  Definition tripleDSLP {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getDSLPStExc (obsDSLP prog) pre r -> post r
    | Under => forall r, post r -> getDSLPStExc (obsDSLP prog) pre r
    end.


  (** As on the ASP side, neither of these is [MSingletonProg], so both are
      plain [SPStExc].  They are in fact the same two transformers used for
      ASP: the [Over] / [Under] readings turn only on the observation being
      monotone in its precondition, which all four observations are. *)
  Definition tripleDSLPspec {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => ordSPStExc (getDSLPStExc (obsDSLP prog)) (pp2_over pre post)
    | Under => ordSPStExc (pp2_under pre post) (getDSLPStExc (obsDSLP prog))
    end.

  Theorem tripleDSLPDefEq {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleDSLP prog kind pre post <-> tripleDSLPspec prog kind pre post.
  Proof.
    unfold tripleDSLP, tripleDSLPspec, ordSPStExc, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: push the quantified precondition through [pre <= p] *)
      intros H p r [Hsub Hpost] s Hout. exact (Hsub s (H r Hpost s Hout)).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* Over: pull it back through [p <= pre] *)
      intros H p r Hdslp Hsub. apply (H r).
      intros s Hout. exact (Hsub s (Hdslp s Hout)).
    - intros H r Hdslp. exact (H pre r Hdslp (fun s Hs => Hs)).
  Qed.

  (** Dually, [tripleDSLP _ Under pre post] is the relation inclusion
      [Out <= {(s,r) | post r -> pre s}].  Note the comparison REVERSES —
      [pp2 <= obs] rather than [obs <= pp2] — because reading a relation as a
      DSLP is antitone in the relation. *)
  #[program] Definition pp2dslp_under' {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : DSLPStExc S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  Theorem tripleDSLP_under_inmonad {S A}
    (prog : stdivexcnd S A)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleDSLP prog Under pre post
    <-> ordDSLPStExc (pp2dslp_under' pre post) (obsDSLP prog).
  Proof.
    split.
    - intros H p r Hd s Hout. apply Hd. intro Hpost. exact (H r Hpost s Hout).
    - intros H r Hpost s Hout.
      exact (H (fun t => post r -> pre t) r (fun t Ht => Ht) s Hout Hpost).
  Qed.
End DSLPTriple.

Arguments tripleDSLP {_} {_}.

Section ObsDSP.
  Variable S : Type.

  #[program] Definition obsDSP {A} (m : stdivexcnd S A) : DSPStExc S A :=
    fun pre r => (obsASP m pre r) /\ (obsDSLP m pre r).
  Next Obligation.
    exact (dsp_shape_wf S (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
  Qed.

  Lemma getProgDSP_obsDSP {A} (m : stdivexcnd S A) pre r :
    getDSPStExc (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r))
         /\ (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s)).
  Proof. split; intro H; exact H. Qed.

  (* ---------------- [obsDSP] is a monad morphism ---------------- *)

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : stdivexcnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__DSPStExc. intros pre r.
    apply (dsp_cong S
             (fun s r0 => unOptionT (unOptionT (runStateT (ret a : stdivexcnd S A) s))
                            (Some r0))
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. destruct r0 as [[b s']|]; cbn; split; intro H; congruence.
  Qed.

  Theorem obsDSP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    unfold eq1, Eq1__DSPStExc. intros pre r.
    (* the two probes collapse back to the raw outcome relation *)
    assert (Hx : forall s y,
               (getDSPStExc (obsDSP x) (fun _ => True) y
                /\ ~ getDSPStExc (obsDSP x) (fun t => t <> s) y)
               <-> unOptionT (unOptionT (runStateT x s)) (Some y)).
    { intros s y.
      exact (dsp_recov S
               (fun s1 r1 => unOptionT (unOptionT (runStateT x s1)) (Some r1)) s y). }
    assert (Hf : forall a s y,
               (getDSPStExc (obsDSP (f a)) (fun _ => True) y
                /\ ~ getDSPStExc (obsDSP (f a)) (fun t => t <> s) y)
               <-> unOptionT (unOptionT (runStateT (f a) s)) (Some y)).
    { intros a s y.
      exact (dsp_recov S
               (fun s1 r1 => unOptionT (unOptionT (runStateT (f a) s1)) (Some r1)) s y). }
    refine (iff_trans
              (dsp_cong S
                 (fun s r0 => unOptionT (unOptionT (runStateT (x >>= f) s)) (Some r0))
                 (fun s r0 =>
                    exists o, (getDSPStExc (obsDSP x) (fun _ => True) o
                               /\ ~ getDSPStExc (obsDSP x) (fun t => t <> s) o)
                              /\ match o with
                                 | Some (a, smid) =>
                                     getDSPStExc (obsDSP (f a)) (fun _ => True) r0
                                     /\ ~ getDSPStExc (obsDSP (f a)) (fun t => t <> smid) r0
                                 | None => r0 = None
                                 end)
                 _ pre r)
              (iff_sym (bindDSPProg_dsp S (obsDSP x) (fun a => obsDSP (f a)) pre r))).
    intros s r0. split.
    - intro H. apply (outcomes_bind S) in H. destruct H as [oy [Hxx Hk]].
      destruct oy as [[[a s']|]|].
      + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
      + exists None. split; [ apply Hx; exact Hxx | congruence ].
      + discriminate Hk.
    - intros [[[a s']|] [Hm Hk]].
      + apply Hx in Hm. apply Hf in Hk. apply (outcomes_bind S).
        exists (Some (Some (a, s'))). split; [ exact Hm | exact Hk ].
      + apply Hx in Hm. apply (outcomes_bind S).
        exists (Some None). split; [ exact Hm | congruence ].
  Qed.
End ObsDSP.

Arguments obsDSP {_} {_}.

Section DSPTriple.
  Definition tripleDSP {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getDSPStExc (obsDSP prog) pre r -> post r
    | Under => forall r, post r -> getDSPStExc (obsDSP prog) pre r
    end.

  Definition tripleDSPspec {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => ordSPStExc (getDSPStExc (obsDSP prog)) (pp2_over pre post)
    | Under => ordSPStExc (pp2_under pre post) (getDSPStExc (obsDSP prog))
    end.

  Theorem tripleDSPDefEq {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleDSP prog kind pre post <-> tripleDSPspec prog kind pre post.
  Proof.
    unfold tripleDSP, tripleDSPspec, ordSPStExc, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: both conjuncts of the DSP move along [pre <= p] *)
      intros H p r [Hsub Hpost].
      destruct (H r Hpost) as [[s [Hp Hout]] Hall]. split.
      + exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* Over: and along [p <= pre] in the other direction *)
      intros H p r [[s [Hp Hout]] Hall] Hsub. apply (H r). split.
      + exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hobs. exact (H pre r Hobs (fun s Hs => Hs)).
  Qed.
End DSPTriple.

Arguments tripleDSP {_} {_}.
Section ObsASLP.
  Variable S : Type.

  #[program] Definition obsASLP {A} (m : stdivexcnd S A) : ASLPStExc S A :=
    fun pre r => (obsASP m pre r) \/ (obsDSLP m pre r).
  Next Obligation.
    exact (aslp_shape_wf S (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
  Qed.

  Lemma getProgASLP_obsASLP {A} (m : stdivexcnd S A) pre r :
    getASLPStExc (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r))
         \/ (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s)).
  Proof. split; intro H; exact H. Qed.

  (* ---------------- [obsASLP] is a monad morphism ---------------- *)

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : stdivexcnd S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ASLPStExc. intros pre r.
    apply (aslp_cong S
             (fun s r0 => unOptionT (unOptionT (runStateT (ret a : stdivexcnd S A) s))
                            (Some r0))
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. destruct r0 as [[b s']|]; cbn; split; intro H; congruence.
  Qed.

  Theorem obsASLP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof.
    unfold eq1, Eq1__ASLPStExc. intros pre r.
    assert (Hx : forall s y,
               (~ getASLPStExc (obsASLP x) (fun _ => False) y
                /\ getASLPStExc (obsASLP x) (fun t => t = s) y)
               <-> unOptionT (unOptionT (runStateT x s)) (Some y)).
    { intros s y.
      exact (aslp_recov S
               (fun s1 r1 => unOptionT (unOptionT (runStateT x s1)) (Some r1)) s y). }
    assert (Hf : forall a s y,
               (~ getASLPStExc (obsASLP (f a)) (fun _ => False) y
                /\ getASLPStExc (obsASLP (f a)) (fun t => t = s) y)
               <-> unOptionT (unOptionT (runStateT (f a) s)) (Some y)).
    { intros a s y.
      exact (aslp_recov S
               (fun s1 r1 => unOptionT (unOptionT (runStateT (f a) s1)) (Some r1)) s y). }
    refine (iff_trans
              (aslp_cong S
                 (fun s r0 => unOptionT (unOptionT (runStateT (x >>= f) s)) (Some r0))
                 (fun s r0 =>
                    exists o, (~ getASLPStExc (obsASLP x) (fun _ => False) o
                               /\ getASLPStExc (obsASLP x) (fun t => t = s) o)
                              /\ match o with
                                 | Some (a, smid) =>
                                     ~ getASLPStExc (obsASLP (f a)) (fun _ => False) r0
                                     /\ getASLPStExc (obsASLP (f a)) (fun t => t = smid) r0
                                 | None => r0 = None
                                 end)
                 _ pre r)
              (iff_sym (bindASLPProg_aslp S (obsASLP x) (fun a => obsASLP (f a)) pre r))).
    intros s r0. split.
    - intro H. apply (outcomes_bind S) in H. destruct H as [oy [Hxx Hk]].
      destruct oy as [[[a s']|]|].
      + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
      + exists None. split; [ apply Hx; exact Hxx | congruence ].
      + discriminate Hk.
    - intros [[[a s']|] [Hm Hk]].
      + apply Hx in Hm. apply Hf in Hk. apply (outcomes_bind S).
        exists (Some (Some (a, s'))). split; [ exact Hm | exact Hk ].
      + apply Hx in Hm. apply (outcomes_bind S).
        exists (Some None). split; [ exact Hm | congruence ].
  Qed.
End ObsASLP.

Arguments obsASLP {_} {_}.

Section ASLPTriple.
  Definition tripleASLP {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getASLPStExc (obsASLP prog) pre r -> post r
    | Under => forall r, post r -> getASLPStExc (obsASLP prog) pre r
    end.


  Definition tripleASLPspec {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => ordSPStExc (getASLPStExc (obsASLP prog)) (pp2_over pre post)
    | Under => ordSPStExc (pp2_under pre post) (getASLPStExc (obsASLP prog))
    end.

  Theorem tripleASLPDefEq {S A}
    (prog : stdivexcnd S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleASLP prog kind pre post <-> tripleASLPspec prog kind pre post.
  Proof.
    unfold tripleASLP, tripleASLPspec, ordSPStExc, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: whichever disjunct held still holds after weakening *)
      intros H p r [Hsub Hpost].
      destruct (H r Hpost) as [[s [Hp Hout]] | Hall].
      + left. exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + right. intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* Over *)
      intros H p r Hobs Hsub. apply (H r).
      destruct Hobs as [[s [Hp Hout]] | Hall].
      + left. exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + right. intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hobs. exact (H pre r Hobs (fun s Hs => Hs)).
  Qed.
End ASLPTriple.

Arguments tripleASLP {_} {_}.

Section SPExamples.
  Definition P0 : nat -> Prop := fun s => s = 0.

  (** [progEx] from state [s] yields exactly [Some (tt, s + 1)] and
      [Some (tt, 42)], and never raises.  So relative to [P0 = {0}] the four
      outcomes below realise the four reachability classes:
      [Some (tt, 1)]  reachable only from [P0]      — both ASP and DSLP hold;
      [Some (tt, 42)] reachable from [P0] and outside — ASP only;
      [None]          unreachable                    — DSLP only (vacuously);
      [Some (tt, 99)] reachable only from outside    — neither. *)

  #[program] Theorem progEx_asp_1 :
    (obsASP progEx) P0 (Some (tt, 1)).
  Proof. exists 0. split; [reflexivity | cbn; sauto]. Qed.

  #[program] Theorem progEx_dslp_1 :
    (obsDSLP progEx) P0 (Some (tt, 1)).
  Proof. intros s Hr. cbn in Hr. unfold P0. sauto lq: on. Qed.

  #[program] Theorem progEx_dsp_1 :
    (obsDSP progEx) P0 (Some (tt, 1)).
  Proof. split; [exact progEx_asp_1 | exact progEx_dslp_1]. Qed.

  #[program] Theorem progEx_aslp_1 :
    (obsASLP progEx) P0 (Some (tt, 1)).
  Proof. left. exact progEx_asp_1. Qed.
  
  #[program] Theorem progEx_asp_42 :
    (obsASP progEx) P0 (Some (tt, 42)).
  Proof. exists 0. split; [reflexivity | cbn; sauto]. Qed.

  #[program] Theorem progEx_dslp_not_42 :
    ~ (obsDSLP progEx) P0 (Some (tt, 42)).
  Proof.
    intro H. specialize (H 1).
    assert (Hreach : unOptionT (unOptionT (runStateT progEx 1))
                       (Some (Some (tt, 42)))) by (cbn; sauto).
    specialize (H Hreach). unfold P0 in H. discriminate.
  Qed.

  #[program] Theorem progEx_dsp_not_42 :
    ~ (obsDSP progEx) P0 (Some (tt, 42)).
  Proof. intros [_ Hdslp]. exact (progEx_dslp_not_42 Hdslp). Qed.

  #[program] Theorem progEx_aslp_42 :
    (obsASLP progEx) P0 (Some (tt, 42)).
  Proof. left. exact progEx_asp_42. Qed.

  #[program] Theorem progEx_asp_not_None :
    ~ (obsASP progEx) P0 None.
  Proof. intros [s [_ Hr]]. cbn in Hr. sauto. Qed.

  #[program] Theorem progEx_dslp_None :
    (obsDSLP progEx) P0 None.
  Proof. intros s Hr. cbn in Hr. sauto. Qed.

  #[program] Theorem progEx_dsp_not_None :
    ~ (obsDSP progEx) P0 None.
  Proof. intros [Hasp _]. exact (progEx_asp_not_None Hasp). Qed.

  #[program] Theorem progEx_aslp_None :
    (obsASLP progEx) P0 None.
  Proof. right. exact progEx_dslp_None. Qed.

  #[program] Theorem progEx_asp_not_99 :
    ~ (obsASP progEx) P0 (Some (tt, 99)).
  Proof. intros [s [Hp Hr]]. unfold P0 in Hp. subst s. cbn in Hr. sauto. Qed.

  #[program] Theorem progEx_dslp_not_99 :
    ~ (obsDSLP progEx) P0 (Some (tt, 99)).
  Proof.
    intro H. specialize (H 98).
    assert (Hreach : unOptionT (unOptionT (runStateT progEx 98))
                       (Some (Some (tt, 99)))) by (cbn; sauto).
    specialize (H Hreach). unfold P0 in H. discriminate.
  Qed.

  #[program] Theorem progEx_dsp_not_99 :
    ~ (obsDSP progEx) P0 (Some (tt, 99)).
  Proof. intros [Hasp _]. exact (progEx_asp_not_99 Hasp). Qed.

  #[program] Theorem progEx_aslp_not_99 :
    ~ (obsASLP progEx) P0 (Some (tt, 99)).
  Proof.
    intros [Hasp | Hdslp];
      [ exact (progEx_asp_not_99 Hasp) | exact (progEx_dslp_not_99 Hdslp) ].
  Qed.
End SPExamples.

(* ================================================================= *)
(** ** ASP / DSP examples                                             *)
(* ================================================================= *)

Section ASPExamples.
  Theorem progA_all :
    tripleASP progA Over
      (fun _ => True)
      (fun r =>
         match r with
         | Some (_, s') => s' >= 42
         | None => False
         end).
  Proof.
    unfold tripleASP. intros r [sigma [_ Hrel]].
    destruct r as [[[] s'] |]; cbn in Hrel; sauto.
  Qed.

  Theorem progA_42 :
    tripleASP progA Under
      (fun _ => True)
      (fun r => r = Some (tt, 42)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split.
    - exact I.
    - cbn. sauto.
  Qed.

  Theorem progA_43 :
    tripleASP progA Under
      (fun _ => True)
      (fun r => r = Some (tt, 43)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split.
    - exact I.
    - cbn. sauto.
  Qed.

  Theorem progB_42 :
    tripleASP progB Under
      (fun _ => True)
      (fun r => r = Some (tt, 42)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split; [exact I | sauto].
  Qed.

  Theorem progB_not_None :
    tripleASP progB Over
      (fun _ => True)
      (fun r => r <> None).
  Proof.
    unfold tripleASP. intros r [sigma [_ Hrel]] ->. cbn in Hrel. sauto.
  Qed.

    Theorem progEx_under :
    tripleASP progEx Under
      (fun _ => True)
      (fun r => r = Some (tt, 1)).
  Proof.
    intros r ->. exists 0. split; [exact I | cbn; sauto].
  Qed.

End ASPExamples.

Theorem example_incorrect_1 :
    tripleASP example_state Under
      (fun '(x, _, z) => z = 11)
      (fun r =>
         match r with
         | Some (tt, (x, y, z)) =>
             z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
         | _ => False
         end).
Proof.
  unfold tripleASP.
  intros [[[] [[x y] z]]|] H; [| contradiction].
  destruct H as [-> [Hx Hy]].
  exists (x, y, 11). split; [reflexivity |].
  cbn. eexists. split; [reflexivity |].
  cbn. rewrite Hx, Hy. reflexivity.
Qed.

Theorem example_incorrect_2 :
  tripleASP example_state Under
    (fun _ => True)
    (fun r =>
       match r with
       | Some (tt, (_, _, z)) => z = 42
         | _ => False
       end).
Proof.
  unfold tripleASP.
  intros [[[] [[x y] z]]|] H; [| contradiction].
  cbn in H. subst z.
  (* the final state itself is a witness: both branches preserve [x], [y]
       and either set [z := 42] or leave it at [42] *)
  exists (x, y, 42). split; [exact I |].
  cbn. eexists. split; [reflexivity |].
  cbn. destruct (Nat.even x); destruct (negb (Nat.even y)); reflexivity.
Qed.

Theorem example_incorrect_unprovable :
  ~ tripleASP example_state Under
    (fun '(_, _, z) => z = 11)
    (fun r =>
           match r with
           | Some (tt, (_, _, z)) => z = 42
           | _ => False
           end).
Proof.
  (* [Some (tt, (1, 0, 42))] satisfies the postcondition but is reachable
     only from itself — and its [z] is [42], not [11] *)
    intro H.
    specialize (H (Some (tt, (1, 0, 42))) eq_refl).
    destruct H as [[[x y] z] [Hpre Hrel]].
    cbn in Hpre. subst z.
    cbn in Hrel. destruct Hrel as [a [Ha Hrel]]. subst a. cbn in Hrel.
    destruct (Nat.even x) eqn:Hx; destruct (negb (Nat.even y)) eqn:Hy;
      cbn in Hrel; inversion Hrel; subst; try discriminate Hx.
Qed.

Theorem progRet_asp_inc :
  tripleASP progRet Under preEq0 postEq0.
Proof.
  intros r Hpost. unfold postEq0 in Hpost. subst r.
  exists 0. split; [reflexivity | cbn; sauto].
Qed.

Theorem progRet_dsp_inc :
  tripleDSP progRet Under preEq0 postEq0.
Proof.
  intros r Hpost. split; [ exact (progRet_asp_inc r Hpost) |].
  unfold postEq0 in Hpost. subst r.
  intros s Hr. cbn in Hr. unfold preEq0. sauto.
Qed.

