(** * SP observations of [stdivnd] into the PAIR specification monads

    [obsDSP] and [obsASLP] are monad morphisms into lawful monads, but
    neither [ordDSPSt] nor [ordASLPSt] is preserved by [bind], so neither
    carries a Dijkstra monad: a DSP (resp. ASLP) assertion constrains the
    outcome relation from BOTH sides, and a fibre of an order constrains it
    from one.

    Splitting the two sides into two components fixes this.  This file
    observes [stdivnd] into [DSPPair] and [ASLPPair] -- both of them the
    product [ASPSt x DSLPSt], differing only in how a pair is READ -- and
    builds the Dijkstra monads [Ddsp] and [Daslp] over them.  The payoff is
    that the triples are exactly the fibres:

    - a DSP [Under] triple is a pair of an angelic WITNESS relation and a
      demonic pre/post bound ([tripleDSP_is_witnessed]);
    - an ASLP [Under] triple is the same data plus a SPLIT of the
      postcondition, since the ASLP reading is a disjunction
      ([tripleASLP_is_split]). *)

From Coq Require Import RelationClasses Morphisms Lia.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad
  BaseGaloisConnections NewGaloisConnections DSPMonadPair ASLPMonadPair.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivNonDet_SPSt.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

Import StTrans StASP StDSLP StDSP StASLP StSP.
Import TermSliceObs.

(* ================================================================= *)
(** ** The paired observations                                       *)
(* ================================================================= *)

Section PairObservations.
  Variable S : Type.
  #[local] Obligation Tactic := (intros; cbn beta).

  Definition obsDSPPair {A} (m : stdivnd S A) : StDSPPair.DSPPair S A :=
    (obsASP m, obsDSLP m).

  Definition obsASLPPair {A} (m : stdivnd S A) : StASLPPair.ASLPPair S A :=
    (obsASP m, obsDSLP m).

  (** Both readings agree with the observations already in
      [StDivNonDet_SPSt.v]: [readDSP] is the conjunction [obsDSP] takes,
      [readASLP] the disjunction [obsASLP] takes. *)

  Lemma readDSP_obsDSPPair {A} (m : stdivnd S A) pre r :
    StDSPPair.readDSP (obsDSPPair m) pre r <-> getDSPSt (obsDSP m) pre r.
  Proof. split; intro H; exact H. Qed.

  Lemma readASLP_obsASLPPair {A} (m : stdivnd S A) pre r :
    StASLPPair.readASLP (obsASLPPair m) pre r <-> getASLPSt (obsASLP m) pre r.
  Proof. split; intro H; exact H. Qed.

  (** ** The morphism laws, componentwise *)

  Lemma obsDSPPair_ret {A} (a : A) :
    StDSPPair.ordDSPPair (StDSPPair.retDSPPair a) (obsDSPPair (ret a)).
  Proof.
    split.
    - intros pre r H. apply (obsASP_ret S a). exact H.
    - intros pre r H. apply (obsDSLP_ret S a). exact H.
  Qed.

  Lemma obsDSPPair_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    StDSPPair.ordDSPPair
      (StDSPPair.bindDSPPair (obsDSPPair x) (fun a => obsDSPPair (f a)))
      (obsDSPPair (x >>= f)).
  Proof.
    split.
    - intros pre r H. apply (obsASP_bind S x f). exact H.
    - intros pre r H. apply (obsDSLP_bind S x f). exact H.
  Qed.

  Lemma obsASLPPair_ret {A} (a : A) :
    StASLPPair.ordASLPPair (StASLPPair.retASLPPair a) (obsASLPPair (ret a)).
  Proof.
    split.
    - intros pre r H. apply (obsASP_ret S a). exact H.
    - intros pre r H. apply (obsDSLP_ret S a). exact H.
  Qed.

  Lemma obsASLPPair_bind {A B} (x : stdivnd S A) (f : A -> stdivnd S B) :
    StASLPPair.ordASLPPair
      (StASLPPair.bindASLPPair (obsASLPPair x) (fun a => obsASLPPair (f a)))
      (obsASLPPair (x >>= f)).
  Proof.
    split.
    - intros pre r H. apply (obsASP_bind S x f). exact H.
    - intros pre r H. apply (obsDSLP_bind S x f). exact H.
  Qed.

  (* --------------------------------------------------------------- *)
  (** ** The two Dijkstra monads, in the [Under] direction            *)
  (* --------------------------------------------------------------- *)

  Definition Ddsp {A} (w : StDSPPair.DSPPair S A) : Type :=
    { m : stdivnd S A | StDSPPair.ordDSPPair w (obsDSPPair m) }.

  #[program] Definition Ddsp_ret {A} (a : A) : Ddsp (StDSPPair.retDSPPair a) :=
    @ret (stdivnd S) _ A a.
  Next Obligation. apply obsDSPPair_ret. Qed.

  #[program] Definition Ddsp_bind {A B} {w : StDSPPair.DSPPair S A}
    {wf : A -> StDSPPair.DSPPair S B}
    (m : Ddsp w) (f : forall a, Ddsp (wf a)) : Ddsp (StDSPPair.bindDSPPair w wf) :=
    @bind (stdivnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply obsDSPPair_bind ].
    apply StDSPPair.ordDSPPair_bind;
      [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition Ddsp_wkn {A} {w w' : StDSPPair.DSPPair S A}
    (Hle : StDSPPair.ordDSPPair w' w) (m : Ddsp w) : Ddsp w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition Ddsp_lift {A} (m : stdivnd S A) : Ddsp (obsDSPPair m) := m.
  Next Obligation. reflexivity. Qed.

  Definition Daslp {A} (w : StASLPPair.ASLPPair S A) : Type :=
    { m : stdivnd S A | StASLPPair.ordASLPPair w (obsASLPPair m) }.

  #[program] Definition Daslp_ret {A} (a : A) : Daslp (StASLPPair.retASLPPair a) :=
    @ret (stdivnd S) _ A a.
  Next Obligation. apply obsASLPPair_ret. Qed.

  #[program] Definition Daslp_bind {A B} {w : StASLPPair.ASLPPair S A}
    {wf : A -> StASLPPair.ASLPPair S B}
    (m : Daslp w) (f : forall a, Daslp (wf a))
    : Daslp (StASLPPair.bindASLPPair w wf) :=
    @bind (stdivnd S) _ A B (proj1_sig m) (fun a => proj1_sig (f a)).
  Next Obligation.
    etransitivity; [| apply obsASLPPair_bind ].
    apply StASLPPair.ordASLPPair_bind;
      [ exact (proj2_sig m) | intro a; exact (proj2_sig (f a)) ].
  Qed.

  #[program] Definition Daslp_wkn {A} {w w' : StASLPPair.ASLPPair S A}
    (Hle : StASLPPair.ordASLPPair w' w) (m : Daslp w) : Daslp w' := proj1_sig m.
  Next Obligation. etransitivity; [ exact Hle | exact (proj2_sig m) ]. Qed.

  #[program] Definition Daslp_lift {A} (m : stdivnd S A) : Daslp (obsASLPPair m) := m.
  Next Obligation. reflexivity. Qed.

End PairObservations.

Arguments obsDSPPair {_} {_}.
Arguments obsASLPPair {_} {_}.
Arguments Ddsp {_} {_}.
Arguments Daslp {_} {_}.

(* ================================================================= *)
(** ** Triples, and the fibre theorems                               *)
(* ================================================================= *)

Section PairTriples.
  Variable S : Type.

  Definition tripleDSP {A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getDSPSt (obsDSP prog) pre r -> post r
    | Under => forall r, post r -> getDSPSt (obsDSP prog) pre r
    end.

  Definition tripleASLP {A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => forall r, getASLPSt (obsASLP prog) pre r -> post r
    | Under => forall r, post r -> getASLPSt (obsASLP prog) pre r
    end.

  (** Membership of the ANGELIC component is relation inclusion: "every
      pair the index claims, the program really has". *)
  Lemma aspOfRel_memD {A} (W : S -> (A * S) -> Prop) (m : stdivnd S A) :
    ordASPSt (StDSPPair.aspOfRel W) (obsASP m) <->
    (forall s r, W s r -> unOptionT (runStateT m s) (Some r)).
  Proof.
    split.
    - intros H s r Hw.
      destruct (H (fun t => t = s) r (ex_intro _ s (conj eq_refl Hw))) as [t [-> Ht]].
      exact Ht.
    - intros H pre r [s [Hp Hw]]. exists s. split; [ exact Hp | exact (H s r Hw) ].
  Qed.

  Lemma aspOfRel_memA {A} (W : S -> (A * S) -> Prop) (m : stdivnd S A) :
    ordASPSt (StASLPPair.aspOfRel W) (obsASP m) <->
    (forall s r, W s r -> unOptionT (runStateT m s) (Some r)).
  Proof.
    split.
    - intros H s r Hw.
      destruct (H (fun t => t = s) r (ex_intro _ s (conj eq_refl Hw))) as [t [-> Ht]].
      exact Ht.
    - intros H pre r [s [Hp Hw]]. exists s. split; [ exact Hp | exact (H s r Hw) ].
  Qed.

  (** A DSP [Under] triple IS a fibre: an angelic witness relation for the
      lower bound, a demonic pre/post pair for the upper one. *)
  Theorem tripleDSP_is_witnessed {A} (m : stdivnd S A)
    (pre : S -> Prop) (post : (A * S) -> Prop) :
    tripleDSP m Under pre post <->
    exists W : S -> (A * S) -> Prop,
      (forall s r, W s r -> pre s)
      /\ (forall r, post r -> exists s, W s r)
      /\ StDSPPair.ordDSPPair
           (StDSPPair.aspOfRel W, tDSLPunder pre post) (obsDSPPair m).
  Proof.
    split.
    - intro H.
      exists (fun s r => pre s /\ post r /\ unOptionT (runStateT m s) (Some r)).
      split; [ intros s r [Hp _]; exact Hp |]. split.
      + intros r Hpost.
        destruct (proj1 (getProgDSP_obsDSP S m pre r) (H r Hpost)) as [[s [Hp Hr]] _].
        exists s. split; [ exact Hp | split; [ exact Hpost | exact Hr ] ].
      + split.
        * apply aspOfRel_memD. intros s r [_ [_ Hr]]. exact Hr.
        * apply (gen_dslp_under S (obsDSLP m) pre post). intros r Hpost.
          apply getProgDSLP_obsDSLP.
          exact (proj2 (proj1 (getProgDSP_obsDSP S m pre r) (H r Hpost))).
    - intros [W [Hsrc [Hcov [Hasp Hdslp]]]] r Hpost.
      apply getProgDSP_obsDSP. split.
      + destruct (Hcov r Hpost) as [s Hw]. exists s.
        split; [ exact (Hsrc s r Hw) | exact (proj1 (aspOfRel_memD W m) Hasp s r Hw) ].
      + apply getProgDSLP_obsDSLP.
        exact (proj2 (gen_dslp_under S (obsDSLP m) pre post) Hdslp r Hpost).
  Qed.

  (** An ASLP [Under] triple is the same data plus a SPLIT of [post]:
      the ASLP reading is a disjunction, so each outcome must be justified
      either angelically (it is reached) or demonically (only [pre]-states
      reach it). *)
  Theorem tripleASLP_is_split {A} (m : stdivnd S A)
    (pre : S -> Prop) (post : (A * S) -> Prop) :
    tripleASLP m Under pre post <->
    exists (W : S -> (A * S) -> Prop) (postA postD : (A * S) -> Prop),
      (forall r, post r -> postA r \/ postD r)
      /\ (forall s r, W s r -> pre s)
      /\ (forall r, postA r -> exists s, W s r)
      /\ StASLPPair.ordASLPPair
           (StASLPPair.aspOfRel W, tDSLPunder pre postD) (obsASLPPair m).
  Proof.
    split.
    - intro H.
      exists (fun s r => pre s /\ unOptionT (runStateT m s) (Some r)),
             (fun r => post r /\ exists s, pre s /\ unOptionT (runStateT m s) (Some r)),
             (fun r => post r /\ forall s, unOptionT (runStateT m s) (Some r) -> pre s).
      split.
      + intros r Hpost.
        destruct (proj1 (getProgASLP_obsASLP S m pre r) (H r Hpost)) as [Ha | Hd].
        * left. split; [ exact Hpost | exact Ha ].
        * right. split; [ exact Hpost | exact Hd ].
      + split; [ intros s r [Hp _]; exact Hp |]. split.
        * intros r [_ [s [Hp Hr]]]. exists s. split; [ exact Hp | exact Hr ].
        * split.
          -- apply aspOfRel_memA. intros s r [_ Hr]. exact Hr.
          -- apply (gen_dslp_under S (obsDSLP m) pre _). intros r [_ Hd].
             apply getProgDSLP_obsDSLP. exact Hd.
    - intros [W [postA [postD [Hsplit [Hsrc [Hcov [Hasp Hdslp]]]]]]] r Hpost.
      apply getProgASLP_obsASLP. destruct (Hsplit r Hpost) as [HA | HD].
      + left. destruct (Hcov r HA) as [s Hw]. exists s.
        split; [ exact (Hsrc s r Hw) | exact (proj1 (aspOfRel_memA W m) Hasp s r Hw) ].
      + right. apply getProgDSLP_obsDSLP.
        exact (proj2 (gen_dslp_under S (obsDSLP m) pre postD) Hdslp r HD).
  Qed.

End PairTriples.

Arguments tripleDSP {_} {_}.
Arguments tripleASLP {_} {_}.

(* ================================================================= *)
(** ** The spec (ordering) form, and its equivalence with the triples *)
(* ================================================================= *)

Section PairTripleSpecs.
  Variable S : Type.

  (** [Under] -- the direction the pair was built for -- is an ORDERING
      statement inside the pair monad: a witnessed angelic bound together
      with a demonic pre/post bound.  The existential is the WITNESS, and
      it cannot be removed: by [no_asp_under_index] no single index has the
      angelic half as its fibre.  For ASLP the data additionally includes a
      SPLIT of [post], because its reading is a disjunction.

      [Over] has no in-monad form either way, so it stays the ambient
      comparison against [pp2_over] -- made through the READING of the
      pair, which by [readDSP_obsDSPPair] is the old [obsDSP]. *)

  Definition tripleDSPspec {A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordSPSt (StDSPPair.readDSP (obsDSPPair prog)) (pp2_over pre post)
    | Under =>
        exists W : S -> (A * S) -> Prop,
          (forall s r, W s r -> pre s)
          /\ (forall r, post r -> exists s, W s r)
          /\ StDSPPair.ordDSPPair
               (StDSPPair.aspOfRel W, tDSLPunder pre post) (obsDSPPair prog)
    end.

  Theorem tripleDSPDefEq {A} (prog : stdivnd S A) kind pre post :
    tripleDSP prog kind pre post <-> tripleDSPspec prog kind pre post.
  Proof.
    destruct kind.
    - (* [Under]: the in-monad ordering, with the witness *)
      exact (tripleDSP_is_witnessed S prog pre post).
    - (* [Over]: the ambient comparison, through the reading *)
      unfold tripleDSP, tripleDSPspec, ordSPSt, pp2_over. split.
      + intros H p r Hread Hsub. apply H. apply readDSP_obsDSPPair.
        exact (StDSPPair.readDSP_mono S (obsDSPPair prog) p pre r Hsub Hread).
      + intros H r Hobs. apply (H pre r).
        * apply readDSP_obsDSPPair. exact Hobs.
        * intros s Hs. exact Hs.
  Qed.

  Definition tripleASLPspec {A} (prog : stdivnd S A) (kind : approxKind)
    (pre : S -> Prop) (post : (A * S) -> Prop) : Prop :=
    match kind with
    | Over  => ordSPSt (StASLPPair.readASLP (obsASLPPair prog)) (pp2_over pre post)
    | Under =>
        exists (W : S -> (A * S) -> Prop) (postA postD : (A * S) -> Prop),
          (forall r, post r -> postA r \/ postD r)
          /\ (forall s r, W s r -> pre s)
          /\ (forall r, postA r -> exists s, W s r)
          /\ StASLPPair.ordASLPPair
               (StASLPPair.aspOfRel W, tDSLPunder pre postD) (obsASLPPair prog)
    end.

  Theorem tripleASLPDefEq {A} (prog : stdivnd S A) kind pre post :
    tripleASLP prog kind pre post <-> tripleASLPspec prog kind pre post.
  Proof.
    destruct kind.
    - (* [Under]: the in-monad ordering, with witness and split *)
      exact (tripleASLP_is_split S prog pre post).
    - (* [Over]: the ambient comparison, through the reading *)
      unfold tripleASLP, tripleASLPspec, ordSPSt, pp2_over. split.
      + intros H p r Hread Hsub. apply H. apply readASLP_obsASLPPair.
        exact (StASLPPair.readASLP_mono S (obsASLPPair prog) p pre r Hsub Hread).
      + intros H r Hobs. apply (H pre r).
        * apply readASLP_obsASLPPair. exact Hobs.
        * intros s Hs. exact Hs.
  Qed.

End PairTripleSpecs.

Arguments tripleDSPspec {_} {_}.
Arguments tripleASLPspec {_} {_}.
(* ================================================================= *)
(** ** Examples                                                      *)
(* ================================================================= *)

Section PairExamples.

  (** Outcome computations for the three primitives used below. *)
  Lemma reach_get {S} (s : S) r :
    unOptionT (runStateT (get : stdivnd S S) s) (Some r) <-> r = (s, s).
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma reach_put {S} (s' s : S) r :
    unOptionT (runStateT (put s' : stdivnd S unit) s) (Some r) <-> r = (tt, s').
  Proof. cbn. split; intro H; congruence. Qed.

  Lemma reach_orD {S A} (m1 m2 : stdivnd S A) s r :
    unOptionT (runStateT (orD m1 m2) s) (Some r)
    <-> (unOptionT (runStateT m1 s) (Some r) \/ unOptionT (runStateT m2 s) (Some r)).
  Proof. cbn. split; intro H; exact H. Qed.

  (** [incrD] is deterministic, so its two bounds coincide; [twoD] is
      nondeterministic and reaches [(tt,1)] from EVERY state, which the
      demonic bound of a DSP triple forbids but the disjunctive ASLP
      reading tolerates. *)

  Definition incrD : stdivnd nat unit := s <- get ;; put (s + 1).
  Definition twoD  : stdivnd nat unit := orD (put 1) (put 2).

  Definition pre0 : nat -> Prop := fun s => s = 0.
  Definition post1 : (unit * nat) -> Prop := fun r => r = (tt, 1).
  Definition W_incr : nat -> (unit * nat) -> Prop := fun s r => s = 0 /\ r = (tt, 1).

  (* ---- DSP: a witness for the angelic half, a bound for the demonic ---- *)

  Lemma incrD_asp : ordASPSt (StDSPPair.aspOfRel W_incr) (obsASP incrD).
  Proof.
    apply aspOfRel_memD. intros s r [-> ->].
    apply (outcomes_bind nat). exists 0, 0.
    split; [ apply reach_get; reflexivity | apply reach_put; reflexivity ].
  Qed.

  Lemma incrD_dslp : ordDSLPSt (tDSLPunder pre0 post1) (obsDSLP incrD).
  Proof.
    apply (gen_dslp_under nat (obsDSLP incrD) pre0 post1).
    intros r Hpost. unfold post1 in Hpost. subst r.
    apply getProgDSLP_obsDSLP. intros s Hs.
    destruct (proj1 (outcomes_bind nat get (fun t => put (t + 1)) s (tt, 1)) Hs)
      as [a [s' [Hg Hp]]].
    apply reach_get in Hg. injection Hg as -> ->.
    apply reach_put in Hp. injection Hp as Hp. unfold pre0. lia.
  Qed.

  Definition incrD_Ddsp
    : Ddsp (StDSPPair.aspOfRel W_incr, tDSLPunder pre0 post1) :=
    exist _ incrD (conj incrD_asp incrD_dslp).

  Corollary incrD_tripleDSP : tripleDSP incrD Under pre0 post1.
  Proof.
    apply tripleDSP_is_witnessed. exists W_incr. split.
    - intros s r [Hs _]. exact Hs.
    - split.
      + intros r ->. exists 0. split; reflexivity.
      + exact (proj2_sig incrD_Ddsp).
  Qed.

  (* ---- ASLP: the same data, plus a split of the postcondition ---- *)

  Definition post19 : (unit * nat) -> Prop := fun r => r = (tt, 1) \/ r = (tt, 9).
  Definition post9  : (unit * nat) -> Prop := fun r => r = (tt, 9).

  Lemma twoD_asp : ordASPSt (StASLPPair.aspOfRel W_incr) (obsASP twoD).
  Proof.
    apply aspOfRel_memA. intros s r [-> ->].
    apply reach_orD. left. apply reach_put. reflexivity.
  Qed.

  Lemma twoD_dslp : ordDSLPSt (tDSLPunder pre0 post9) (obsDSLP twoD).
  Proof.
    apply (gen_dslp_under nat (obsDSLP twoD) pre0 post9).
    intros r Hpost. unfold post9 in Hpost. subst r.
    apply getProgDSLP_obsDSLP. intros s Hs.
    apply reach_orD in Hs. destruct Hs as [H | H]; apply reach_put in H;
      discriminate H.
  Qed.

  Definition twoD_Daslp
    : Daslp (StASLPPair.aspOfRel W_incr, tDSLPunder pre0 post9) :=
    exist _ twoD (conj twoD_asp twoD_dslp).

  Corollary twoD_tripleASLP : tripleASLP twoD Under pre0 post19.
  Proof.
    apply tripleASLP_is_split. exists W_incr, post1, post9. split.
    - intros r [-> | ->]; [ left; reflexivity | right; reflexivity ].
    - split; [ intros s r [Hs _]; exact Hs |]. split.
      + intros r ->. exists 0. split; reflexivity.
      + exact (proj2_sig twoD_Daslp).
  Qed.

  (** The same outcome is NOT a DSP triple for [twoD]: the demonic bound
      fails, because [(tt,1)] is reached from every state. *)
  Theorem twoD_not_tripleDSP : ~ tripleDSP twoD Under pre0 post1.
  Proof.
    intro H.
    destruct (proj1 (getProgDSP_obsDSP nat twoD pre0 (tt, 1)) (H (tt,1) eq_refl))
      as [_ Hall].
    assert (H5 : unOptionT (runStateT twoD 5) (Some (tt, 1))).
    { apply reach_orD. left. apply reach_put. reflexivity. }
    discriminate (Hall 5 H5).
  Qed.

End PairExamples.
