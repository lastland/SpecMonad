From Coq Require Import Classical_Prop.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import PrePostMonad WPureMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import BaseGaloisConnections.

(* Second adjunction between PrePost and MonoWP *)
Definition wp2pp_over {A} (w : WPure A) : PPM.PrePost A :=
  ( forall p, runWPure w p
    , fun x => exists p, ~ (runWPure w p) /\ p x ).

#[program] Definition pp2wp_over {A} (pp : PPM.PrePost A) : WPure A :=
  fun post => (forall x, post x -> PPM.post pp x) -> PPM.pre pp.
Next Obligation.
  intros k1 k2 Hk H Hsub. apply H. intros x Hx. exact (Hsub x (Hk x Hx)).
Qed.

Theorem wp_pp_over_adjunction {A} (pp : PPM.PrePost A) (w : WPure A) :
  PP_le (wp2pp_over w) pp <-> WP_le w (pp2wp_over pp).
Proof.
  unfold PP_le, WP_le, wp2pp_over, pp2wp_over, PPM.pre, PPM.post,
    runWPure, runWPure; cbn.
  split.
  - intros [H1 H2] q Hq.
    destruct (classic (proj1_sig w q)) as [Hy | Hn]; [ exact Hy |].
    exact (H1 (Hq (fun a Ha => H2 a (ex_intro _ q (conj Hn Ha)))) q).
  - intro H. split.
    + intros Hpre q. exact (H q (fun _ => Hpre)).
    + intros a [q [Hnq Hqa]].
      assert (Hn : ~ ((forall x, q x -> PPM.post pp x) -> PPM.pre pp))
        by (intro Hc; exact (Hnq (H q Hc))).
      exact (proj1 (imply_to_and _ _ Hn) a Hqa).
Qed.

(* ================================================================= *)
(** * Embeddings between [PrePost] pairs and the four SP spec monads  *)
(* ================================================================= *)

Inductive approxKind := | Under | Over.

Section SPPrePostEmbeddings.
  Variable S : Type.

  #[program] Definition pp2asp_over {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPStExc S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s. exists s0. split; assumption.
  Qed.

  #[program] Definition pp2asp_under {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : ASPStExc S A :=
    fun p r => exists s, p s /\ (pre s /\ post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s. exists s0. split; assumption.
  Qed.

  #[program] Definition pp2dslp_under {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPStExc S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  #[program] Definition pp2dslp_over {A}
    (pre : S -> Prop) (post : option (A * S) -> Prop) : DSLPStExc S A :=
    fun p r => forall s, (~ post r /\ ~ pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => ~ post r /\ ~ pre s)). Qed.

  (** ** The degeneracies that force the two side conditions

      [SingletonProg] makes every ASP FALSE at the empty precondition, and
      dually [MSingletonProg] makes every DSLP TRUE at the full one.  So at
      those preconditions no target of the respective kind can see [post], and
      the corresponding nonemptiness hypothesis below is not removable. *)
  (** Each [At]-target, evaluated at [pre] itself, collapses to [post]. *)

  Lemma tASPunder_at {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hne : exists s, pre s) (r : option (A * S)) :
    getASPStExc (pp2asp_under pre post) pre r <-> post r.
  Proof.
    split.
    - intros [s [_ [_ Hpost]]]. exact Hpost.
    - intro Hpost. destruct Hne as [s Hs].
      exists s. split; [ exact Hs | split; [ exact Hs | exact Hpost ] ].
  Qed.

  Lemma tDSLPover_at {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    (Hco : exists s, ~ pre s) (r : option (A * S)) :
    getDSLPStExc (pp2dslp_over pre post) pre r <-> post r.
  Proof.
    split.
    - intro H. apply NNPP. intro Hnp. destruct Hco as [s0 Hs0].
      exact (Hs0 (H s0 (conj Hnp Hs0))).
    - intros Hpost s [Hnp _]. destruct (Hnp Hpost).
  Qed.

  (** ** The four in-monad characterizations

      [Over] always compares [obs <= target]; [Under] always [target <= obs].
      ASP/[Over] and DSLP/[Under] use the global order without a side
      condition.  The other two characterizations use an [At]-order and
      the nonemptiness hypotheses forced by the targets' well-formedness. *)

  Theorem gen_asp_over {A} (w : ASPStExc S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    (forall r, getASPStExc w pre r -> post r) <-> ordASPStExc w (pp2asp_over pre post).
  Proof.
    split.
    - intros H p r Hw.
      destruct (proj1 (getProg_singleton S w p r) Hw) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp |]. intro Hpre.
      apply H. apply getProg_singleton. exists s0. split; [ exact Hpre | exact Hs ].
    - intros H r Hw.
      destruct (H pre r Hw) as [s1 [Hp1 Himp]]. exact (Himp Hp1).
  Qed.

  Theorem gen_asp_under {A} (w : ASPStExc S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) (Hne : exists s, pre s) :
    (forall r, post r -> getASPStExc w pre r)
    <-> ordASPStExcAt pre (pp2asp_under pre post) w.
  Proof.
    split.
    - intros H r Ht. exact (H r (proj1 (tASPunder_at pre post Hne r) Ht)).
    - intros H r Hpost. exact (H r (proj2 (tASPunder_at pre post Hne r) Hpost)).
  Qed.

  Theorem gen_dslp_under {A} (w : DSLPStExc S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    (forall r, post r -> getDSLPStExc w pre r)
    <-> ordDSLPStExc (pp2dslp_under pre post) w.
  Proof.
    split.
    - intros H p r Hd.
      apply (msingletonProg_repr S (getDSLPStExc w) (proj2_sig w)).
      intros s Hns. apply Hd. intro Hpost.
      exact (proj1 (msingletonProg_repr S (getDSLPStExc w) (proj2_sig w) pre r)
               (H r Hpost) s Hns).
    - intros H r Hpost. exact (H pre r (fun t Ht => Ht Hpost)).
  Qed.

  Theorem gen_dslp_over {A} (w : DSLPStExc S A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) (Hco : exists s, ~ pre s) :
    (forall r, getDSLPStExc w pre r -> post r)
    <-> ordDSLPStExcAt pre w (pp2dslp_over pre post).
  Proof.
    split.
    - intros H r Hd. exact (proj2 (tDSLPover_at pre post Hco r) (H r Hd)).
    - intros H r Hd. exact (proj1 (tDSLPover_at pre post Hco r) (H r Hd)).
  Qed.

  (** The plain (non-[SingletonProg]) Hoare-pair embeddings that the [*spec]
      forms of the triples compare against. *)
  Definition pp2_over {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : @SPStExc S A :=
    fun p r => (forall s, p s -> pre s) -> post r.

  Definition pp2_under {A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : @SPStExc S A :=
    fun p r => (forall s, pre s -> p s) /\ post r.
End SPPrePostEmbeddings.

Arguments pp2_over {_} {_}.
Arguments pp2_under {_} {_}.
Arguments pp2asp_over {_} {_}.
Arguments pp2asp_under {_} {_}.
Arguments pp2dslp_under {_} {_}.
Arguments pp2dslp_over {_} {_}.

(* ================================================================= *)
(** * The same embeddings for the TERMINATING SLICE                   *)
(*                                                                    *)
(** Outcomes are [A * S] rather than [option (A * S)]; otherwise this  *)
(** is the development above verbatim.  Namespaced so the names can    *)
(** mirror the option-outcome ones exactly.                            *)
(* ================================================================= *)

Module StSP.
  Import StTrans StASP StDSLP StDSP StASLP.

Inductive approxKind := | Under | Over.

Section SPPrePostEmbeddings.
  Variable S : Type.
  
  (** ** The in-monad comparison targets *)

  #[program] Definition tASPover {A}
    (pre : S -> Prop) (post : (A * S) -> Prop) : ASPSt S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s. exists s0. split; assumption.
  Qed.

  #[program] Definition tASPunder {A}
    (pre : S -> Prop) (post : (A * S) -> Prop) : ASPSt S A :=
    fun p r => exists s, p s /\ (pre s /\ post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hc]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hc ].
    - intros [s0 [Hp [s [Heq Hc]]]]. subst s. exists s0. split; assumption.
  Qed.

  #[program] Definition tDSLPunder {A}
    (pre : S -> Prop) (post : (A * S) -> Prop) : DSLPSt S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  #[program] Definition tDSLPover {A}
    (pre : S -> Prop) (post : (A * S) -> Prop) : DSLPSt S A :=
    fun p r => forall s, (~ post r /\ ~ pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => ~ post r /\ ~ pre s)). Qed.

  (** ** The degeneracies that force the two side conditions

      [SingletonProg] makes every ASP FALSE at the empty precondition, and
      dually [MSingletonProg] makes every DSLP TRUE at the full one.  So at
      those preconditions no target of the respective kind can see [post], and
      the corresponding nonemptiness hypothesis below is not removable. *)
  (** Each [At]-target, evaluated at [pre] itself, collapses to [post]. *)

  Lemma tASPunder_at {A} (pre : S -> Prop) (post : (A * S) -> Prop)
    (Hne : exists s, pre s) (r : (A * S)) :
    getASPSt (tASPunder pre post) pre r <-> post r.
  Proof.
    split.
    - intros [s [_ [_ Hpost]]]. exact Hpost.
    - intro Hpost. destruct Hne as [s Hs].
      exists s. split; [ exact Hs | split; [ exact Hs | exact Hpost ] ].
  Qed.

  Lemma tDSLPover_at {A} (pre : S -> Prop) (post : (A * S) -> Prop)
    (Hco : exists s, ~ pre s) (r : (A * S)) :
    getDSLPSt (tDSLPover pre post) pre r <-> post r.
  Proof.
    split.
    - intro H. apply NNPP. intro Hnp. destruct Hco as [s0 Hs0].
      exact (Hs0 (H s0 (conj Hnp Hs0))).
    - intros Hpost s [Hnp _]. destruct (Hnp Hpost).
  Qed.

  (** ** The four in-monad characterizations

      [Over] always compares [obs <= target]; [Under] always [target <= obs].
      ASP/[Over] and DSLP/[Under] use the global order without a side
      condition.  The other two characterizations use an [At]-order and
      the nonemptiness hypotheses forced by the targets' well-formedness. *)

  Theorem gen_asp_over {A} (w : ASPSt S A)
    (pre : S -> Prop) (post : (A * S) -> Prop) :
    (forall r, getASPSt w pre r -> post r) <-> ordASPSt w (tASPover pre post).
  Proof.
    split.
    - intros H p r Hw.
      destruct (proj1 (getProg_singleton S w p r) Hw) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp |]. intro Hpre.
      apply H. apply getProg_singleton. exists s0. split; [ exact Hpre | exact Hs ].
    - intros H r Hw.
      destruct (H pre r Hw) as [s1 [Hp1 Himp]]. exact (Himp Hp1).
  Qed.

  Theorem gen_asp_under {A} (w : ASPSt S A)
    (pre : S -> Prop) (post : (A * S) -> Prop) (Hne : exists s, pre s) :
    (forall r, post r -> getASPSt w pre r)
    <-> ordASPStAt pre (tASPunder pre post) w.
  Proof.
    split.
    - intros H r Ht. exact (H r (proj1 (tASPunder_at pre post Hne r) Ht)).
    - intros H r Hpost. exact (H r (proj2 (tASPunder_at pre post Hne r) Hpost)).
  Qed.

  Theorem gen_dslp_under {A} (w : DSLPSt S A)
    (pre : S -> Prop) (post : (A * S) -> Prop) :
    (forall r, post r -> getDSLPSt w pre r)
    <-> ordDSLPSt (tDSLPunder pre post) w.
  Proof.
    split.
    - intros H p r Hd.
      apply (msingletonProg_repr S (getDSLPSt w) (proj2_sig w)).
      intros s Hns. apply Hd. intro Hpost.
      exact (proj1 (msingletonProg_repr S (getDSLPSt w) (proj2_sig w) pre r)
               (H r Hpost) s Hns).
    - intros H r Hpost. exact (H pre r (fun t Ht => Ht Hpost)).
  Qed.

  Theorem gen_dslp_over {A} (w : DSLPSt S A)
    (pre : S -> Prop) (post : (A * S) -> Prop) (Hco : exists s, ~ pre s) :
    (forall r, getDSLPSt w pre r -> post r)
    <-> ordDSLPStAt pre w (tDSLPover pre post).
  Proof.
    split.
    - intros H r Hd. exact (proj2 (tDSLPover_at pre post Hco r) (H r Hd)).
    - intros H r Hd. exact (proj1 (tDSLPover_at pre post Hco r) (H r Hd)).
  Qed.
End SPPrePostEmbeddings.

Arguments tASPover {_} {_}.
Arguments tASPunder {_} {_}.
Arguments tDSLPunder {_} {_}.
Arguments tDSLPover {_} {_}.

End StSP.

(* ================================================================= *)
(** ** The pure copies                                                *)
(* ================================================================= *)

(** The state-free case: the Hoare pair is a [PPM.PrePost A], so [pre] is a
    [Prop] and [post] a predicate on results.  The shapes collapse by dropping
    the witness — [exists s, p s /\ _] becomes [p /\ _], and
    [forall s, _ -> p s] becomes [_ -> p].

    Names mirror the option-outcome ones above; the module is what tells them
    apart, as with [StSP]. *)

Module PureSP.

  #[program] Definition pp2asp_over {A} (pre : Prop) (post : A -> Prop)
    : ASPSP A := fun p a => p /\ (pre -> post a).
  Next Obligation. intros p a. split; [ tauto | tauto ]. Qed.

  #[program] Definition pp2asp_under {A} (pre : Prop) (post : A -> Prop)
    : ASPSP A := fun p a => p /\ (pre /\ post a).
  Next Obligation. intros p a. split; [ tauto | tauto ]. Qed.

  (** Unlike the additive pair above, both multiplicative ones need [classic]:
      [((post a -> pre) -> p) <-> p \/ ~ (post a -> pre)] is not constructive. *)
  #[program] Definition pp2dslp_under {A} (pre : Prop) (post : A -> Prop)
    : DSLPSP A := fun p a => (post a -> pre) -> p.
  Next Obligation.
    intros p a. split.
    - intro H. destruct (classic (post a -> pre)) as [Hy | Hn];
        [ left; exact (H Hy) | right; intro Hy; exact (Hn Hy) ].
    - intros [Hp | Hf] Hy; [ exact Hp | destruct (Hf Hy) ].
  Qed.

  #[program] Definition pp2dslp_over {A} (pre : Prop) (post : A -> Prop)
    : DSLPSP A := fun p a => (~ post a /\ ~ pre) -> p.
  Next Obligation.
    intros p a. split.
    - intro H. destruct (classic (~ post a /\ ~ pre)) as [Hy | Hn];
        [ left; exact (H Hy) | right; intro Hy; exact (Hn Hy) ].
    - intros [Hp | Hf] Hy; [ exact Hp | destruct (Hf Hy) ].
  Qed.

  (** The same diagonal as the stateful case: ASP is global on [Over] and
      scoped on [Under], DSLP the mirror image.  The two side conditions are
      the pure shadows of [exists s, pre s] / [exists s, ~ pre s], and are not
      removable — see [asp_bot_pure] / [dslp_top_pure]. *)

  Theorem gen_asp_over {A} (w : ASPSP A) (pre : Prop) (post : A -> Prop) :
    (forall a, getASP w pre a -> post a)
    <-> ordASPSP w (pp2asp_over pre post).
  Proof.
    unfold ordASPSP; cbn. split.
    - intros H p a Hw. destruct (getASP_split w p a Hw) as [Hp Ht].
      split; [ exact Hp
             | intro Hpre; apply H; exact (getASP_merge w pre a (conj Hpre Ht)) ].
    - intros H a Hw. destruct (getASP_split w pre a Hw) as [Hpre Ht].
      exact (proj2 (H pre a Hw) Hpre).
  Qed.

  Theorem gen_asp_under {A} (w : ASPSP A) (pre : Prop) (post : A -> Prop)
    (Hne : pre) :
    (forall a, post a -> getASP w pre a)
    <-> ordASPSPAt pre (pp2asp_under pre post) w.
  Proof.
    unfold ordASPSPAt; cbn. split.
    - intros H a [_ [_ Hpost]]. exact (H a Hpost).
    - intros H a Hpost. apply H. split; [ exact Hne | split; assumption ].
  Qed.

  Theorem gen_dslp_under {A} (w : DSLPSP A) (pre : Prop) (post : A -> Prop) :
    (forall a, post a -> getDSLP w pre a)
    <-> ordDSLPSP (pp2dslp_under pre post) w.
  Proof.
    unfold ordDSLPSP; cbn. split.
    - intros H p a Hemb.
      destruct (classic (post a -> pre)) as [Hy | Hn].
      + exact (getMSP_merge w p a (or_introl (Hemb Hy))).
      + apply not_imply_elim in Hn as Hpost.
        apply not_imply_elim2 in Hn as Hnpre.
        destruct (getMSP_split w pre a (H a Hpost)) as [Hc | Hf];
          [ destruct (Hnpre Hc) | exact (getMSP_merge w p a (or_intror Hf)) ].
    - intros H a Hpost. apply H. intro Hy. exact (Hy Hpost).
  Qed.

  Theorem gen_dslp_over {A} (w : DSLPSP A) (pre : Prop) (post : A -> Prop)
    (Hco : ~ pre) :
    (forall a, getDSLP w pre a -> post a)
    <-> ordDSLPSPAt pre w (pp2dslp_over pre post).
  Proof.
    unfold ordDSLPSPAt; cbn. split.
    - intros H a Hw [Hnp _]. destruct (Hnp (H a Hw)).
    - intros H a Hw. apply NNPP. intro Hnp.
      exact (Hco (H a Hw (conj Hnp Hco))).
  Qed.

End PureSP.
