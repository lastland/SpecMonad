From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy Require Import NonDetDivProg SPSpecMonads.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

(** * SP observations for [nddprog]

    [nddprog S A = stateT S (optionT SetM) A] is the nondeterministic, possibly
    DIVERGENT stateful monad of [NonDetDivProg]: its outcome set has type
    [option (A * S) -> Prop], with [None] read as divergence.

    The specification monads of [NonDetItObservationNew] never mention the
    computation monad: they are predicate transformers
    [(S -> Prop) -> option (A * S) -> Prop] carved out by a healthiness
    condition.  So the whole of that development — [ASPProgSP], [DSLPProgSP],
    [DSPProgSP], [ASLPProgSP], their monad instances and laws, the carrier
    bridges, [pp2*] and [ordProgSP] — is reused verbatim here.  What this file
    re-does is the ONE layer that depends on the computation monad: the four
    observations, that they are monad morphisms, and the triples over them.

    Note the contrast with [nditprog].  There the SP observations read the
    TERMINATING SLICE [unOptionT (unOptionT (runStateT m s)) (Some r)], which
    discards the divergent outcome, so the [nditprog] spec transformers cannot
    talk about divergence at all.  Here [None] is an ordinary member of the
    outcome set, so the transformers constrain divergence directly: e.g.
    [getProgASP (obsASP m) pre None] says "some [pre]-state may diverge" and
    [getProgDSLP (obsDSLP m) pre None] says "every state that may diverge
    satisfies [pre]".

    Everything is wrapped in a module so the names do not clash with the
    [nditprog] observations of the imported file. *)

Module NDObs.

Section NDObservations.
  Variable S : Type.

  (** The outcome set of a bind, one step.  Two cases rather than [nditprog]'s
      three: normal return, and divergence — which is absorbing, exactly the
      propagation rule divergence needs. *)
  Lemma outcomes_bind {A B} (x : nddprog S A) (f : A -> nddprog S B) s ob :
    unOptionT (runStateT (x >>= f) s) ob <->
    (exists oy, unOptionT (runStateT x s) oy /\
       match oy with
       | Some (a, s') => unOptionT (runStateT (f a) s') ob
       | None => ob = None
       end).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. exists oy. split; [ exact H1 |].
      destruct oy as [[a s0]|]; cbn in *; [ exact H2 | congruence ].
    - intros [oy [H1 H2]]. exists oy. split; [ exact H1 |].
      destruct oy as [[a s0]|]; cbn in *; [ exact H2 | congruence ].
  Qed.

  Lemma outcomes_ret {A} (a : A) (s : S) (r : option (A * S)) :
    unOptionT (runStateT (ret a : nddprog S A) s) r <-> r = Some (a, s).
  Proof. cbn. split; intro H; congruence. Qed.

  (* ================================================================== *)
  (** ** The four observations                                          *)
  (* ================================================================== *)

  #[program] Definition obsASP {A} (m : nddprog S A) : ASPProgSP S A :=
    fun pre r => exists s, pre s /\ unOptionT (runStateT m s) r.
  Next Obligation.
    intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hr ].
    - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hr ].
  Qed.

  #[program] Definition obsDSLP {A} (m : nddprog S A) : DSLPProgSP S A :=
    fun pre r => forall s, unOptionT (runStateT m s) r -> pre s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => unOptionT (runStateT m s) r)).
  Qed.

  #[program] Definition obsDSP {A} (m : nddprog S A) : DSPProgSP S A :=
    fun pre r => (obsASP m pre r) /\ (obsDSLP m pre r).
  Next Obligation.
    exact (dsp_shape_wf S (fun s r => unOptionT (runStateT m s) r)).
  Qed.

  #[program] Definition obsASLP {A} (m : nddprog S A) : ASLPProgSP S A :=
    fun pre r => (obsASP m pre r) \/ (obsDSLP m pre r).
  Next Obligation.
    exact (aslp_shape_wf S (fun s r => unOptionT (runStateT m s) r)).
  Qed.

  (** Applying an observation IS the corresponding reading of the outcome set. *)
  Lemma getProgASP_obsASP {A} (m : nddprog S A) pre r :
    getProgASP (obsASP m) pre r
    <-> (exists s, pre s /\ unOptionT (runStateT m s) r).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgDSLP_obsDSLP {A} (m : nddprog S A) pre r :
    getProgDSLP (obsDSLP m) pre r
    <-> (forall s, unOptionT (runStateT m s) r -> pre s).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgDSP_obsDSP {A} (m : nddprog S A) pre r :
    getProgDSP (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) r)
         /\ (forall s, unOptionT (runStateT m s) r -> pre s)).
  Proof. split; intro H; exact H. Qed.

  Lemma getProgASLP_obsASLP {A} (m : nddprog S A) pre r :
    getProgASLP (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (runStateT m s) r)
         \/ (forall s, unOptionT (runStateT m s) r -> pre s)).
  Proof. split; intro H; exact H. Qed.

  (* ================================================================== *)
  (** ** Each observation is a monad morphism                           *)
  (* ================================================================== *)

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : nddprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgASP. intros pre r. split.
    - intros [s [Hp Hr]]. exists s.
      split; [ exact Hp | exact (proj1 (outcomes_ret a s r) Hr) ].
    - intros [s [Hp Heq]]. exists s.
      split; [ exact Hp | exact (proj2 (outcomes_ret a s r) Heq) ].
  Qed.

  Theorem obsASP_bind {A B} (x : nddprog S A) (f : A -> nddprog S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    unfold eq1, Eq1__ProgASP. intros pre r. split.
    - intros [s [Hp Hrel]]. apply outcomes_bind in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[a s']|].
      + left. exists a, s'. split; [| exact Hk ].
        exists s. split; [ exact Hp | exact Hx ].
      + right. split; [ exact Hk |]. exists s. split; [ exact Hp | exact Hx ].
    - intros [[a [s' [[s [Hp Hx]] Hf]]] | [Hr [s [Hp Hx]]]].
      + exists s. split; [ exact Hp |]. apply outcomes_bind.
        exists (Some (a, s')). split; [ exact Hx | exact Hf ].
      + exists s. split; [ exact Hp |]. apply outcomes_bind.
        exists None. split; [ exact Hx | exact Hr ].
  Qed.

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : nddprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgDSLP. intros pre r. split.
    - intros H s0 Heq. exact (H s0 (proj2 (outcomes_ret a s0 r) Heq)).
    - intros H s Hr. exact (H s (proj1 (outcomes_ret a s r) Hr)).
  Qed.

  Theorem obsDSLP_bind {A B} (x : nddprog S A) (f : A -> nddprog S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    unfold eq1, Eq1__ProgDSLP. intros pre r. split.
    - intro H. split.
      + intros a s' Hf s Hx. apply H. apply outcomes_bind.
        exists (Some (a, s')). split; [ exact Hx | exact Hf ].
      + intros Hr s Hx. apply H. apply outcomes_bind.
        exists None. split; [ exact Hx | exact Hr ].
    - intros [H1 H2] s Hrel. apply outcomes_bind in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[a s']|].
      + exact (H1 a s' Hk s Hx).
      + exact (H2 Hk s Hx).
  Qed.

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : nddprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgDSP. intros pre r.
    apply (dsp_cong S
             (fun s r0 => unOptionT (runStateT (ret a : nddprog S A) s) r0)
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. exact (outcomes_ret a s r0).
  Qed.

  Theorem obsDSP_bind {A B} (x : nddprog S A) (f : A -> nddprog S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    unfold eq1, Eq1__ProgDSP. intros pre r.
    assert (Hx : forall s y,
               (getProgDSP (obsDSP x) (fun _ => True) y
                /\ ~ getProgDSP (obsDSP x) (fun t => t <> s) y)
               <-> unOptionT (runStateT x s) y).
    { intros s y.
      exact (dsp_recov S (fun s1 r1 => unOptionT (runStateT x s1) r1) s y). }
    assert (Hf : forall a s y,
               (getProgDSP (obsDSP (f a)) (fun _ => True) y
                /\ ~ getProgDSP (obsDSP (f a)) (fun t => t <> s) y)
               <-> unOptionT (runStateT (f a) s) y).
    { intros a s y.
      exact (dsp_recov S (fun s1 r1 => unOptionT (runStateT (f a) s1) r1) s y). }
    refine (iff_trans
              (dsp_cong S
                 (fun s r0 => unOptionT (runStateT (x >>= f) s) r0)
                 (fun s r0 =>
                    exists o, (getProgDSP (obsDSP x) (fun _ => True) o
                               /\ ~ getProgDSP (obsDSP x) (fun t => t <> s) o)
                              /\ match o with
                                 | Some (a, smid) =>
                                     getProgDSP (obsDSP (f a)) (fun _ => True) r0
                                     /\ ~ getProgDSP (obsDSP (f a)) (fun t => t <> smid) r0
                                 | None => r0 = None
                                 end)
                 _ pre r)
              (iff_sym (bindDSPProg_dsp S (obsDSP x) (fun a => obsDSP (f a)) pre r))).
    intros s r0. split.
    - intro H. apply outcomes_bind in H. destruct H as [oy [Hxx Hk]].
      destruct oy as [[a s']|].
      + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
      + exists None. split; [ apply Hx; exact Hxx | exact Hk ].
    - intros [[[a s']|] [Hm Hk]].
      + apply Hx in Hm. apply Hf in Hk. apply outcomes_bind.
        exists (Some (a, s')). split; [ exact Hm | exact Hk ].
      + apply Hx in Hm. apply outcomes_bind.
        exists None. split; [ exact Hm | exact Hk ].
  Qed.

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : nddprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgASLP. intros pre r.
    apply (aslp_cong S
             (fun s r0 => unOptionT (runStateT (ret a : nddprog S A) s) r0)
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. exact (outcomes_ret a s r0).
  Qed.

  Theorem obsASLP_bind {A B} (x : nddprog S A) (f : A -> nddprog S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
  Proof.
    unfold eq1, Eq1__ProgASLP. intros pre r.
    assert (Hx : forall s y,
               (~ getProgASLP (obsASLP x) (fun _ => False) y
                /\ getProgASLP (obsASLP x) (fun t => t = s) y)
               <-> unOptionT (runStateT x s) y).
    { intros s y.
      exact (aslp_recov S (fun s1 r1 => unOptionT (runStateT x s1) r1) s y). }
    assert (Hf : forall a s y,
               (~ getProgASLP (obsASLP (f a)) (fun _ => False) y
                /\ getProgASLP (obsASLP (f a)) (fun t => t = s) y)
               <-> unOptionT (runStateT (f a) s) y).
    { intros a s y.
      exact (aslp_recov S (fun s1 r1 => unOptionT (runStateT (f a) s1) r1) s y). }
    refine (iff_trans
              (aslp_cong S
                 (fun s r0 => unOptionT (runStateT (x >>= f) s) r0)
                 (fun s r0 =>
                    exists o, (~ getProgASLP (obsASLP x) (fun _ => False) o
                               /\ getProgASLP (obsASLP x) (fun t => t = s) o)
                              /\ match o with
                                 | Some (a, smid) =>
                                     ~ getProgASLP (obsASLP (f a)) (fun _ => False) r0
                                     /\ getProgASLP (obsASLP (f a)) (fun t => t = smid) r0
                                 | None => r0 = None
                                 end)
                 _ pre r)
              (iff_sym (bindASLPProg_aslp S (obsASLP x) (fun a => obsASLP (f a)) pre r))).
    intros s r0. split.
    - intro H. apply outcomes_bind in H. destruct H as [oy [Hxx Hk]].
      destruct oy as [[a s']|].
      + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
      + exists None. split; [ apply Hx; exact Hxx | exact Hk ].
    - intros [[[a s']|] [Hm Hk]].
      + apply Hx in Hm. apply Hf in Hk. apply outcomes_bind.
        exists (Some (a, s')). split; [ exact Hm | exact Hk ].
      + apply Hx in Hm. apply outcomes_bind.
        exists None. split; [ exact Hm | exact Hk ].
  Qed.

  (* ================================================================== *)
  (** ** Contrapositive pairs                                           *)
  (* ================================================================== *)

  Theorem obsASP_contrapositive {A} (m : nddprog S A) pre r :
    getProgASP (obsASP m) pre r <-> ~ getProgDSLP (obsDSLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [s [Hp Hr]] Hall. exact (Hall s Hr Hp).
    - intro Hnn. apply NNPP. intro Habs. apply Hnn.
      intros s Hr Hp. apply Habs. exists s. split; [ exact Hp | exact Hr ].
  Qed.

  Theorem obsDSLP_contrapositive {A} (m : nddprog S A) pre r :
    getProgDSLP (obsDSLP m) pre r <-> ~ getProgASP (obsASP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros Hall [s [Hnp Hr]]. exact (Hnp (Hall s Hr)).
    - intros Hnn s Hr. apply NNPP. intro Hnp.
      exact (Hnn (ex_intro _ s (conj Hnp Hr))).
  Qed.
  
  Theorem obsDSP_contrapositive {A} (m : nddprog S A) pre r :
    getProgDSP (obsDSP m) pre r <-> ~ getProgASLP (obsASLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] Hall] [[s' [Hnp Hr']] | Hall'].
      + exact (Hnp (Hall s' Hr')).
      + exact (Hall' s Hr Hp).
    - intro Hnn. split.
      + apply NNPP. intro Hnex. apply Hnn. right.
        intros s Hr Hp. apply Hnex. exists s. split; [ exact Hp | exact Hr ].
      + intros s Hr. apply NNPP. intro Hnp. apply Hnn. left.
        exists s. split; [ exact Hnp | exact Hr ].
  Qed.

  Theorem obsASLP_contrapositive {A} (m : nddprog S A) pre r :
    getProgASLP (obsASLP m) pre r <-> ~ getProgDSP (obsDSP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] | Hall] [[s0 [Hnp0 Hr0]] Hall0].
      + exact (Hall0 s Hr Hp).
      + exact (Hnp0 (Hall s0 Hr0)).
    - intro Hnn.
      destruct (classic (exists s, pre s /\ unOptionT (runStateT m s) r))
        as [He | Hno]; [ left; exact He |].
      right. intros s Hr. apply NNPP. intro Hnp.
      apply Hnn. split.
      + exists s. split; [ exact Hnp | exact Hr ].
      + intros s0 Hr0 Hp0. exact (Hno (ex_intro _ s0 (conj Hp0 Hr0))).
  Qed.

  Theorem DSP_conjunction {A} (m : nddprog S A) pre r :
    getProgDSP (obsDSP m) pre r <-> (getProgASP (obsASP m) pre r /\ getProgDSLP (obsDSLP m) pre r).
  Proof. split; intro H; exact H. Qed.

  Theorem ASLP_disjunction {A} (m : nddprog S A) pre r :
    getProgASLP (obsASLP m) pre r <-> (getProgASP (obsASP m) pre r \/ getProgDSLP (obsDSLP m) pre r).
  Proof. split; intro H; exact H. Qed.

  Theorem ASP_ordering {A} (m : nddprog S A) pre r :
    getProgASP (obsASP m) pre r -> getProgASLP (obsASLP m) pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem DSP_ordering {A} (m : nddprog S A) pre r :
    getProgDSP (obsDSP m) pre r -> getProgASP (obsASP m) pre r.
  Proof. exact (@proj1 _ _). Qed.

  Theorem DSP_DSLP_ordering {A} (m : nddprog S A) pre r :
    getProgDSP (obsDSP m) pre r -> getProgDSLP (obsDSLP m) pre r.
  Proof. exact (@proj2 _ _). Qed.

  Theorem DSLP_ordering {A} (m : nddprog S A) pre r :
    getProgDSLP (obsDSLP m) pre r -> getProgASLP (obsASLP m) pre r.
  Proof. intro H. right. exact H. Qed.


    
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
    (prog : nddprog S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getProgASP (obsASP prog) pre r -> post r
    | Under => forall r, post r -> getProgASP (obsASP prog) pre r
    end.

  Definition tripleDSLP {S A}
    (prog : nddprog S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getProgDSLP (obsDSLP prog) pre r -> post r
    | Under => forall r, post r -> getProgDSLP (obsDSLP prog) pre r
    end.

  Definition tripleDSP {S A}
    (prog : nddprog S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getProgDSP (obsDSP prog) pre r -> post r
    | Under => forall r, post r -> getProgDSP (obsDSP prog) pre r
    end.

  Definition tripleASLP {S A}
    (prog : nddprog S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getProgASLP (obsASLP prog) pre r -> post r
    | Under => forall r, post r -> getProgASLP (obsASLP prog) pre r
    end.

  #[program] Definition pp2asp_over' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPProgSP S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hc ].
  Qed.

  #[program] Definition pp2dslp_under' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPProgSP S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  (** [tripleASP _ Over pre post] is [Out <= {(s,r) | pre s -> post r}]. *)
  Theorem tripleASP_over_inmonad {S A} (prog : nddprog S A) pre post :
    tripleASP prog Over pre post
    <-> ordProgASP (obsASP prog) (pp2asp_over' pre post).
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
  Theorem tripleDSLP_under_inmonad {S A} (prog : nddprog S A) pre post :
    tripleDSLP prog Under pre post
    <-> ordProgDSLP (pp2dslp_under' pre post) (obsDSLP prog).
  Proof.
    split.
    - intros H p r Hd s Hout. apply Hd. intro Hpost. exact (H r Hpost s Hout).
    - intros H r Hpost s Hout.
      exact (H (fun t => post r -> pre t) r (fun t Ht => Ht) s Hout Hpost).
  Qed.

  (** ** The other two directions, via an order scoped to one precondition

      [tripleASP _ Under] and [tripleDSLP _ Over] are NOT relation inclusions —
      each asserts an existential over states — so no target characterises them
      in the GLOBAL orders [ordProgASP] / [ordProgDSLP]
      (the witnessing programs have several incomparable minimal elements).

      Scoping the order to the single precondition [pre] removes exactly the
      information that made those up-sets non-principal, and then a target does
      exist.  The price is a nonemptiness side condition, and it is the one each
      healthiness condition forces: [SingletonProg] makes every ASP FALSE at the
      empty precondition, so [pre] must be inhabited; dually [MSingletonProg]
      makes every DSLP TRUE at the full precondition, so [pre] must be
      co-inhabited.  Neither condition is removable. *)

  #[program] Definition pp2asp_under' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPProgSP S A :=
    fun p r => exists s, p s /\ (pre s /\ post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hc ].
  Qed.

  #[program] Definition pp2dslp_over' {S A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPProgSP S A :=
    fun p r => forall s, (~ post r /\ ~ pre s) -> p s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => ~ post r /\ ~ pre s)).
  Qed.

  (** Each target, evaluated AT [pre] itself, collapses to [post]. *)

  Lemma pp2asp_under'_at {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hne : exists s, pre s) (r : option (A * S)) :
    getProgASP (pp2asp_under' pre post) pre r <-> post r.
  Proof.
    split.
    - intros [s [_ [_ Hpost]]]. exact Hpost.
    - intro Hpost. destruct Hne as [s Hs].
      exists s. split; [ exact Hs | split; [ exact Hs | exact Hpost ] ].
  Qed.

  Lemma pp2dslp_over'_at {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hco : exists s, ~ pre s) (r : option (A * S)) :
    getProgDSLP (pp2dslp_over' pre post) pre r <-> post r.
  Proof.
    split.
    - intro H. apply NNPP. intro Hnp. destruct Hco as [s0 Hs0].
      exact (Hs0 (H s0 (conj Hnp Hs0))).
    - intros Hpost s [Hnp _]. destruct (Hnp Hpost).
  Qed.

  (** [Under] compares [target <= obs]; [Over] compares [obs <= target] — the
      same convention as the two global cases above. *)

  Theorem tripleASP_under_inmonad {S A} (prog : nddprog S A) pre post
    (Hne : exists s, pre s) :
    tripleASP prog Under pre post
    <-> ordProgASPAt pre (pp2asp_under' pre post) (obsASP prog).
  Proof.
    split.
    - intros H r Ht. exact (H r (proj1 (pp2asp_under'_at pre post Hne r) Ht)).
    - intros H r Hpost. exact (H r (proj2 (pp2asp_under'_at pre post Hne r) Hpost)).
  Qed.

  Theorem tripleDSLP_over_inmonad {S A} (prog : nddprog S A) pre post
    (Hco : exists s, ~ pre s) :
    tripleDSLP prog Over pre post
    <-> ordProgDSLPAt pre (obsDSLP prog) (pp2dslp_over' pre post).
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

(* ==================================================================== *)
(** * The taxonomy of triples                                            *)
(* ==================================================================== *)

Section NDTaxonomy.
  Variable S : Type.

  (** [Over]: the observation is a premise, so the WEAKEST transformer gives
      the STRONGEST triple — [ASLP => {ASP, DSLP} => DSP]. *)

  Theorem cc_aslp_implies_asp A (m : nddprog S A) pre post :
    tripleASLP m Over pre post -> tripleASP m Over pre post.
  Proof. intros H r Hasp. apply (H r). left. exact Hasp. Qed.

  Theorem cc_aslp_implies_dslp A (m : nddprog S A) pre post :
    tripleASLP m Over pre post -> tripleDSLP m Over pre post.
  Proof. intros H r Hdslp. apply (H r). right. exact Hdslp. Qed.

  Theorem cc_asp_implies_dsp A (m : nddprog S A) pre post :
    tripleASP m Over pre post -> tripleDSP m Over pre post.
  Proof. intros H r [Hasp _]. exact (H r Hasp). Qed.

  Theorem cc_dslp_implies_dsp A (m : nddprog S A) pre post :
    tripleDSLP m Over pre post -> tripleDSP m Over pre post.
  Proof. intros H r [_ Hdslp]. exact (H r Hdslp). Qed.

  (** [Under]: the observation is the conclusion, so everything flips. *)

  Theorem ii_dsp_implies_asp A (m : nddprog S A) pre post :
    tripleDSP m Under pre post -> tripleASP m Under pre post.
  Proof. intros H r Hpost. exact (proj1 (H r Hpost)). Qed.

  Theorem ii_dsp_implies_dslp A (m : nddprog S A) pre post :
    tripleDSP m Under pre post -> tripleDSLP m Under pre post.
  Proof. intros H r Hpost. exact (proj2 (H r Hpost)). Qed.

  Theorem ii_asp_implies_aslp A (m : nddprog S A) pre post :
    tripleASP m Under pre post -> tripleASLP m Under pre post.
  Proof. intros H r Hpost. left. exact (H r Hpost). Qed.

  Theorem ii_dslp_implies_aslp A (m : nddprog S A) pre post :
    tripleDSLP m Under pre post -> tripleASLP m Under pre post.
  Proof. intros H r Hpost. right. exact (H r Hpost). Qed.

  (** The two contrapositive diagonals. *)

  Theorem ci_asp_dslp_contrapositive A (m : nddprog S A) pre post :
    tripleASP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSLP m Under pre post.
  Proof.
    intros Hii r Hpost s Hr. apply NNPP. intro Hnpre.
    apply (Hii r); [| exact Hpost ].
    exists s. split; [ exact Hnpre | exact Hr ].
  Qed.

  Theorem ci_dslp_asp_contrapositive A (m : nddprog S A) pre post :
    tripleDSLP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASP m Under pre post.
  Proof.
    intros Hii r Hpost. apply NNPP. intro Hnex.
    apply (Hii r); [| exact Hpost ].
    intros s Hr Hpre. apply Hnex. exists s. split; [ exact Hpre | exact Hr ].
  Qed.

  Theorem ci_aslp_dsp_contrapositive A (m : nddprog S A) pre post :
    tripleASLP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSP m Under pre post.
  Proof.
    intros H r Hpost. split.
    - apply NNPP. intro Hnex. apply (H r); [| exact Hpost ]. right.
      intros s Hr Hp. apply Hnex. exists s. split; [ exact Hp | exact Hr ].
    - intros s Hr. apply NNPP. intro Hnp. apply (H r); [| exact Hpost ]. left.
      exists s. split; [ exact Hnp | exact Hr ].
  Qed.

  Theorem ci_aslp_dsp_contrapositive' A (m : nddprog S A) pre post :
    tripleDSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASLP m Over pre post.
  Proof.
    intros H r Haslp. apply NNPP. intro Hnpost.
    destruct (H r Hnpost) as [[s0 [Hnp Hr0]] Hall].
    destruct Haslp as [[s [Hp Hr]] | Hall2].
    - exact (Hall s Hr Hp).
    - exact (Hnp (Hall2 s0 Hr0)).
  Qed.

  Theorem ci_dsp_aslp_contrapositive A (m : nddprog S A) pre post :
    tripleDSP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleASLP m Under pre post.
  Proof.
    intros H r Hpost. apply NNPP. intro Hno.
    apply (H r); [| exact Hpost ]. split.
    - (* [~ asp pre] is [dslp (~pre)] ... *)
      apply NNPP. intro Hnex. apply Hno. right.
      intros s Hr. apply NNPP. intro Hnp.
      exact (Hnex (ex_intro _ s (conj Hnp Hr))).
    - (* ... and [~ dslp pre] is [asp (~pre)] *)
      intros s Hr. apply NNPP. intro Hnnp. apply Hno. left.
      exists s. split; [ apply NNPP; exact Hnnp | exact Hr ].
  Qed.



  Theorem ci_dslp_asp_contrapositive' A (m : nddprog S A) pre post :
    tripleASP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
    tripleDSLP m Over pre post.
  Proof.
    intros H r Hdslp. apply NNPP. intro Hnpost.
    destruct (H r Hnpost) as [s [Hnp Hr]].
    exact (Hnp (Hdslp s Hr)).
  Qed.

End NDTaxonomy.

End NDObs.
