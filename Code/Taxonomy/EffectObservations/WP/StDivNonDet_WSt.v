(** * WP observations of [stdivndNE] into [WSt]

    The WP counterpart of [SP/StDivNonDet_SPSt.v].  The source is the
    non-empty fragment of the nondeterministic, possibly divergent monad

      [stdivndNE S A]   outcome set [option (A * S) -> Prop], [None] = divergence

    and the target is [WSt] from [BaseSpecMonads/WPureMonad.v].  Its evaluator
    takes an initial state and a postcondition on [A * S], so the postcondition
    describes normal returns only.  The observation can still see divergence
    in the source.  Each reading chooses how to handle that outcome:

      [obsDWP]   demonic total    -- every outcome terminates and satisfies [post]
      [obsDWLP]  demonic liberal  -- every terminating outcome satisfies [post]
      [obsAWP]   angelic total    -- some terminating outcome satisfies [post]
      [obsAWLP]  angelic liberal  -- ... or divergence is possible

    [getNE_nonEmpty] supplies the outcome witness used by [obsDWP_strict],
    [obsAWLP_top], and selected taxonomy inclusions.  Without it, an empty
    outcome set would satisfy demonic total WP at [False] vacuously and fail
    angelic liberal WP at [True].  The postcondition-monotonicity proofs
    below do not use non-emptiness.

    [TermSliceObsWP] qualifies the four observations, their triples, and
    their return/bind preservation laws. *)

From ExtLib Require Import StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad.
Require Import Coq.Logic.Classical_Prop.

Import MonadNotation.
Open Scope monad_scope.

Module TermSliceObsWP.
Section NDObservationWP.

  Variable S : Type.
  (** Demonic WP (total): ALL outcomes must terminate and satisfy [post]. *)
  Lemma obsDWP_mono {A} (m : stdivndNE S A) (s : S) :
    wpure_mono (fun (post : A * S -> Prop) =>
      match runStateT (getNE m) s with
      | mkOptionT outcomes =>
          forall oa, outcomes oa ->
            match oa with Some r => post r | None => False end
      end).
  Proof.
    intros p q Hpq H. destruct (runStateT (getNE m) s) as [outcomes].
    intros oa Ho. specialize (H oa Ho).
    destruct oa as [r|]; [ exact (Hpq r H) | exact H ].
  Qed.

  Definition obsDWP {A} (m : stdivndNE S A) : WSt S A :=
    mkStateT (fun s => mkWPure _ (obsDWP_mono m s)).

  (** Demonic WLP (partial): ALL TERMINATING outcomes satisfy [post];
      divergence is acceptable. *)
  Lemma obsDWLP_mono {A} (m : stdivndNE S A) (s : S) :
    wpure_mono (fun (post : A * S -> Prop) =>
      match runStateT (getNE m) s with
      | mkOptionT outcomes =>
          forall oa, outcomes oa ->
            match oa with Some r => post r | None => True end
      end).
  Proof.
    intros p q Hpq H. destruct (runStateT (getNE m) s) as [outcomes].
    intros oa Ho. specialize (H oa Ho).
    destruct oa as [r|]; [ exact (Hpq r H) | exact H ].
  Qed.

  Definition obsDWLP {A} (m : stdivndNE S A) : WSt S A :=
    mkStateT (fun s => mkWPure _ (obsDWLP_mono m s)).

  (** Angelic WP (total): SOME terminating outcome satisfies [post]. *)
  Lemma obsAWP_mono {A} (m : stdivndNE S A) (s : S) :
    wpure_mono (fun (post : A * S -> Prop) =>
      match runStateT (getNE m) s with
      | mkOptionT outcomes => exists r, outcomes (Some r) /\ post r
      end).
  Proof.
    intros p q Hpq H. destruct (runStateT (getNE m) s) as [outcomes].
    destruct H as [r [Ho Hp]]. exists r. split; [ exact Ho | exact (Hpq r Hp) ].
  Qed.

  Definition obsAWP {A} (m : stdivndNE S A) : WSt S A :=
    mkStateT (fun s => mkWPure _ (obsAWP_mono m s)).

  (** Angelic WLP (partial): SOME terminating outcome satisfies [post],
      OR divergence is possible. *)
  Lemma obsAWLP_mono {A} (m : stdivndNE S A) (s : S) :
    wpure_mono (fun (post : A * S -> Prop) =>
      match runStateT (getNE m) s with
      | mkOptionT outcomes =>
          (exists r, outcomes (Some r) /\ post r) \/ outcomes None
      end).
  Proof.
    intros p q Hpq H. destruct (runStateT (getNE m) s) as [outcomes].
    destruct H as [[r [Ho Hp]] | Hn];
      [ left; exists r; split; [ exact Ho | exact (Hpq r Hp) ] | right; exact Hn ].
  Qed.

  Definition obsAWLP {A} (m : stdivndNE S A) : WSt S A :=
    mkStateT (fun s => mkWPure _ (obsAWLP_mono m s)).

  (* --------------------------------------------------------------- *)
  (** *** Unfolding                                                    *)
  (* --------------------------------------------------------------- *)

  Lemma obsDWP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWP m) s post
    <-> (forall oa, unOptionT (runStateT (getNE m) s) oa ->
                    match oa with Some r => post r | None => False end).
  Proof. unfold obsDWP. cbn. destruct (runStateT (getNE m) s) as [outcomes]. reflexivity. Qed.

  Lemma obsDWLP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsDWLP m) s post
    <-> (forall oa, unOptionT (runStateT (getNE m) s) oa ->
                    match oa with Some r => post r | None => True end).
  Proof. unfold obsDWLP. cbn. destruct (runStateT (getNE m) s) as [outcomes]. reflexivity. Qed.

  Lemma obsAWP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsAWP m) s post
    <-> (exists r, unOptionT (runStateT (getNE m) s) (Some r) /\ post r).
  Proof. unfold obsAWP. cbn. destruct (runStateT (getNE m) s) as [outcomes]. reflexivity. Qed.

  Lemma obsAWLP_unfold {A} (m : stdivndNE S A) s (post : A * S -> Prop) :
    runStateT (obsAWLP m) s post
    <-> ((exists r, unOptionT (runStateT (getNE m) s) (Some r) /\ post r)
         \/ unOptionT (runStateT (getNE m) s) None).
  Proof. unfold obsAWLP. cbn. destruct (runStateT (getNE m) s) as [outcomes]. reflexivity. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Collapse when divergence is impossible                       *)
  (* --------------------------------------------------------------- *)

  Theorem obsDPCollapse {A} (m : stdivndNE S A) (post : A * S -> Prop) s :
    (~ mayDivergeNE m s) ->
    (runStateT (obsDWP m) s post <-> runStateT (obsDWLP m) s post).
  Proof.
    intro Hnd. unfold mayDivergeNE, mayDiverge in Hnd. cbn.
    destruct (runStateT (getNE m) s) as [outcomes]. cbn in Hnd. split.
    - intros H oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [ exact H | exact I ].
    - intros H oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [ exact H | exfalso; exact (Hnd Hoa) ].
  Qed.

  Theorem obsAPCollapse {A} (m : stdivndNE S A) (post : A * S -> Prop) s :
    (~ mayDivergeNE m s) ->
    (runStateT (obsAWP m) s post <-> runStateT (obsAWLP m) s post).
  Proof.
    intro Hnd. unfold mayDivergeNE, mayDiverge in Hnd. cbn.
    destruct (runStateT (getNE m) s) as [outcomes]. cbn in Hnd. split.
    - intro H. left. exact H.
    - intros [H | Hdiv]; [ exact H | exfalso; exact (Hnd Hdiv) ].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** [divergeD]: rejected by the total readings, accepted by the
          liberal ones                                                 *)
  (* --------------------------------------------------------------- *)

  Theorem obsDWP_divergeD {A} (post : A * S -> Prop) s :
    ~ runStateT (obsDWP (divergeNE : stdivndNE S A)) s post.
  Proof. cbn. intro H. exact (H None eq_refl). Qed.

  Theorem obsDWLP_divergeD {A} (post : A * S -> Prop) s :
    runStateT (obsDWLP (divergeNE : stdivndNE S A)) s post.
  Proof. cbn. intros oa Heq. assert (E : oa = None) by congruence. rewrite E. exact I. Qed.

  Theorem obsAWP_divergeD {A} (post : A * S -> Prop) s :
    ~ runStateT (obsAWP (divergeNE : stdivndNE S A)) s post.
  Proof. cbn. intros [r [Hr _]]. discriminate Hr. Qed.

  Theorem obsAWLP_divergeD {A} (post : A * S -> Prop) s :
    runStateT (obsAWLP (divergeNE : stdivndNE S A)) s post.
  Proof. cbn. right. reflexivity. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Monotonicity in the postcondition                            *)
  (* --------------------------------------------------------------- *)

  Theorem obsDWP_monotonic {A} (m : stdivndNE S A) s (p q : A * S -> Prop) :
    (forall r, p r -> q r) -> runStateT (obsDWP m) s p -> runStateT (obsDWP m) s q.
  Proof.
    intros H Hp0. apply obsDWP_unfold.
    pose proof (proj1 (obsDWP_unfold m s p) Hp0) as Hp.
    intros oa Hoa. specialize (Hp oa Hoa).
    destruct oa as [r|]; [ exact (H _ Hp) | exact Hp ].
  Qed.

  Theorem obsDWLP_monotonic {A} (m : stdivndNE S A) s (p q : A * S -> Prop) :
    (forall r, p r -> q r) -> runStateT (obsDWLP m) s p -> runStateT (obsDWLP m) s q.
  Proof.
    intros H Hp0. apply obsDWLP_unfold.
    pose proof (proj1 (obsDWLP_unfold m s p) Hp0) as Hp.
    intros oa Hoa. specialize (Hp oa Hoa).
    destruct oa as [r|]; [ exact (H _ Hp) | exact I ].
  Qed.

  Theorem obsAWP_monotonic {A} (m : stdivndNE S A) s (p q : A * S -> Prop) :
    (forall r, p r -> q r) -> runStateT (obsAWP m) s p -> runStateT (obsAWP m) s q.
  Proof.
    intros H Hp0. apply obsAWP_unfold.
    destruct (proj1 (obsAWP_unfold m s p) Hp0) as [r [Hr Hpost]].
    exists r. split; [ exact Hr | exact (H _ Hpost) ].
  Qed.

  Theorem obsAWLP_monotonic {A} (m : stdivndNE S A) s (p q : A * S -> Prop) :
    (forall r, p r -> q r) -> runStateT (obsAWLP m) s p -> runStateT (obsAWLP m) s q.
  Proof.
    intros H Hp0. apply obsAWLP_unfold.
    destruct (proj1 (obsAWLP_unfold m s p) Hp0) as [[r [Hr Hpost]] | Hdiv].
    - left. exists r. split; [ exact Hr | exact (H _ Hpost) ].
    - right. exact Hdiv.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Strictness and top preservation from non-empty outcomes

      Neither of these holds over the unrestricted [stdivnd]: the
      empty outcome set satisfies the demonic total formula at [False]
      vacuously and fails the angelic liberal formula at [True].  The
      [stdivndNE] witness rules out this case. *)

  Theorem obsDWP_strict {A} (m : stdivndNE S A) s :
    ~ runStateT (obsDWP m) s (fun _ => False).
  Proof.
    intro H0. pose proof (proj1 (obsDWP_unfold m s _) H0) as H.
    destruct (getNE_nonEmpty S m s) as [[r|] Ho]; exact (H _ Ho).
  Qed.

  Theorem obsAWLP_top {A} (m : stdivndNE S A) s :
    runStateT (obsAWLP m) s (fun _ => True).
  Proof.
    apply obsAWLP_unfold. destruct (getNE_nonEmpty S m s) as [[r|] Ho].
    - left. exists r. exact (conj Ho I).
    - right. exact Ho.
  Qed.

End NDObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.
Arguments obsDWP_unfold {_} {_}.
Arguments obsDWLP_unfold {_} {_}.
Arguments obsAWP_unfold {_} {_}.
Arguments obsAWLP_unfold {_} {_}.

(* ================================================================= *)
(** ** Triples                                                       *)
(* ================================================================= *)

Inductive approxKindWP := | SubsetOf | SupersetOf.

Lemma pp2wp_subset_mono {S A} (pre : S -> Prop) (post : A * S -> Prop) (s0 : S) :
  wpure_mono (fun p => pre s0 /\ (forall r, post r -> p r)).
Proof.
  intros p q Hpq [Hpre Hsub]. split; [ exact Hpre |].
  intros r Hr. exact (Hpq r (Hsub r Hr)).
Qed.

Definition pp2wp_subset {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A :=
  mkStateT (fun s0 => mkWPure _ (pp2wp_subset_mono pre post s0)).

Lemma pp2wp_superset_mono {S A} (pre : S -> Prop) (post : A * S -> Prop) (s0 : S) :
  wpure_mono (fun p => (forall r, p r -> post r) -> pre s0).
Proof.
  intros p q Hpq H Hsub. apply H. intros r Hr. exact (Hsub r (Hpq r Hr)).
Qed.

Definition pp2wp_superset {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A :=
  mkStateT (fun s0 => mkWPure _ (pp2wp_superset_mono pre post s0)).

Section NDWPTriples.

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
    | SubsetOf   => ordWSt (pp2wp_subset pre post) (obs prog)
    | SupersetOf => ordWSt (obs prog) (pp2wp_superset pre post)
    end.

  Theorem tripleWPDefEq {S A}
    (obs : stdivndNE S A -> WSt S A)
    (prog : stdivndNE S A)
    (kind : approxKindWP)
    (pre : S -> Prop)
    (post : A * S -> Prop)
    (Hmono : forall s (p q : A * S -> Prop),
        (forall r, p r -> q r) ->
        runStateT (obs prog) s p -> runStateT (obs prog) s q) :
    tripleWP obs prog pre kind post <-> tripleWPspec obs prog pre kind post.
  Proof.
    unfold tripleWP, tripleWPspec, ordWSt, pp2wp_subset, pp2wp_superset.
    destruct kind; cbn [runStateT]; split.
    - intros H s p [Hpre Hsub]. apply (Hmono s post p Hsub). exact (H s Hpre).
    - intros H s Hpre. apply (H s post). split; [ exact Hpre | intros r hr; exact hr ].
    - intros H s p Hwp Hsub. apply H. apply (Hmono s p post Hsub). exact Hwp.
    - intros H s Hwp. apply (H s post Hwp). intros r hr; exact hr.
  Qed.

End NDWPTriples.

Arguments tripleWP {_} {_}.
(* ================================================================= *)
(** ** Monad morphism laws                                           *)
(* ================================================================= *)

Section NDMonadMorphismLawsWP.

  Variable S : Type.

  Lemma outcomes_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) s ob :
    unOptionT (runStateT (getNE (x >>= f)) s) ob <->
    (exists oy, unOptionT (runStateT (getNE x) s) oy /\
       match oy with
       | Some (a, s') => unOptionT (runStateT (getNE (f a)) s') ob
       | None => ob = None
       end).
  Proof.
    cbn. split.
    - intros [oy [H1 H2]]. exists oy. split; [ exact H1 |].
      destruct oy as [[a s0]|]; cbn in *; [ exact H2 | congruence ].
    - intros [oy [H1 H2]]. exists oy. split; [ exact H1 |].
      destruct oy as [[a s0]|]; cbn in *; [ exact H2 | congruence ].
  Qed.

  (** [ret]: every observation of [ret a] is [post] at [(a, s)]. *)

  Lemma obsDWP_ret {A} (a : A) (post : A * S -> Prop) s :
    runStateT (obsDWP (ret a : stdivndNE S A)) s post <-> post (a, s).
  Proof.
    cbn. split.
    - intro H. exact (H (Some (a, s)) eq_refl).
    - intros Hp oa Heq. assert (E : oa = Some (a, s)) by congruence.
      rewrite E. exact Hp.
  Qed.

  Lemma obsDWLP_ret {A} (a : A) (post : A * S -> Prop) s :
    runStateT (obsDWLP (ret a : stdivndNE S A)) s post <-> post (a, s).
  Proof.
    cbn. split.
    - intro H. exact (H (Some (a, s)) eq_refl).
    - intros Hp oa Heq. assert (E : oa = Some (a, s)) by congruence.
      rewrite E. exact Hp.
  Qed.

  Lemma obsAWP_ret {A} (a : A) (post : A * S -> Prop) s :
    runStateT (obsAWP (ret a : stdivndNE S A)) s post <-> post (a, s).
  Proof.
    cbn. split.
    - intros [r [Hr Hp]]. assert (E : r = (a, s)) by congruence. subst r. exact Hp.
    - intro Hp. exists (a, s). split; [ reflexivity | exact Hp ].
  Qed.

  Lemma obsAWLP_ret {A} (a : A) (post : A * S -> Prop) s :
    runStateT (obsAWLP (ret a : stdivndNE S A)) s post <-> post (a, s).
  Proof.
    cbn. split.
    - intros [[r [Hr Hp]] | Hdiv].
      + assert (E : r = (a, s)) by congruence. subst r. exact Hp.
      + discriminate Hdiv.
    - intro Hp. left. exists (a, s). split; [ reflexivity | exact Hp ].
  Qed.

  (** [bind]: the Dijkstra [wp_bind] law. *)

  Lemma obsDWP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) s post :
    runStateT (obsDWP (x >>= f)) s post
    <-> runStateT (obsDWP x) s
          (fun ars => runStateT (obsDWP (f (fst ars))) (snd ars) post).
  Proof.
    split.
    - intro H. pose proof (proj1 (obsDWP_unfold (x >>= f) s post) H) as Hb.
      apply obsDWP_unfold. intros oa Hoa. destruct oa as [[a s']|].
      + apply obsDWP_unfold. intros ob Hob.
        exact (Hb ob (proj2 (outcomes_bind x f s ob)
                        (ex_intro _ (Some (a, s')) (conj Hoa Hob)))).
      + exact (Hb None (proj2 (outcomes_bind x f s None)
                          (ex_intro _ None (conj Hoa eq_refl)))).
    - intro H. pose proof (proj1 (obsDWP_unfold x s _) H) as Hx.
      apply obsDWP_unfold. intros ob Hob.
      destruct (proj1 (outcomes_bind x f s ob) Hob) as [[[a s']|] [Hxo Hk]].
      + exact (proj1 (obsDWP_unfold (f a) s' post) (Hx (Some (a, s')) Hxo) ob Hk).
      + destruct (Hx None Hxo).
  Qed.

  Lemma obsDWLP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) s post :
    runStateT (obsDWLP (x >>= f)) s post
    <-> runStateT (obsDWLP x) s
          (fun ars => runStateT (obsDWLP (f (fst ars))) (snd ars) post).
  Proof.
    split.
    - intro H. pose proof (proj1 (obsDWLP_unfold (x >>= f) s post) H) as Hb.
      apply obsDWLP_unfold. intros oa Hoa. destruct oa as [[a s']|]; [| exact I ].
      apply obsDWLP_unfold. intros ob Hob.
      exact (Hb ob (proj2 (outcomes_bind x f s ob)
                      (ex_intro _ (Some (a, s')) (conj Hoa Hob)))).
    - intro H. pose proof (proj1 (obsDWLP_unfold x s _) H) as Hx.
      apply obsDWLP_unfold. intros ob Hob.
      destruct (proj1 (outcomes_bind x f s ob) Hob) as [[[a s']|] [Hxo Hk]].
      + exact (proj1 (obsDWLP_unfold (f a) s' post) (Hx (Some (a, s')) Hxo) ob Hk).
      + assert (E : ob = None) by exact Hk. rewrite E. exact I.
  Qed.

  Lemma obsAWP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) s post :
    runStateT (obsAWP (x >>= f)) s post
    <-> runStateT (obsAWP x) s
          (fun ars => runStateT (obsAWP (f (fst ars))) (snd ars) post).
  Proof.
    split.
    - intro H. destruct (proj1 (obsAWP_unfold (x >>= f) s post) H) as [ob [Hob Hp]].
      destruct (proj1 (outcomes_bind x f s (Some ob)) Hob) as [[[a s']|] [Hxo Hk]].
      + apply obsAWP_unfold. exists (a, s'). split; [ exact Hxo |].
        apply obsAWP_unfold. exists ob. exact (conj Hk Hp).
      + discriminate Hk.
    - intro H. destruct (proj1 (obsAWP_unfold x s _) H) as [[a s'] [Hxo Hk]].
      destruct (proj1 (obsAWP_unfold (f a) s' post) Hk) as [ob [Hob Hp]].
      apply obsAWP_unfold. exists ob. split; [| exact Hp ].
      apply outcomes_bind. exists (Some (a, s')). exact (conj Hxo Hob).
  Qed.

  Lemma obsAWLP_bind {A B} (x : stdivndNE S A) (f : A -> stdivndNE S B) s post :
    runStateT (obsAWLP (x >>= f)) s post
    <-> runStateT (obsAWLP x) s
          (fun ars => runStateT (obsAWLP (f (fst ars))) (snd ars) post).
  Proof.
    split.
    - intro H. apply obsAWLP_unfold.
      destruct (proj1 (obsAWLP_unfold (x >>= f) s post) H) as [[ob [Hob Hp]] | Hdiv].
      + destruct (proj1 (outcomes_bind x f s (Some ob)) Hob) as [[[a s']|] [Hxo Hk]].
        * left. exists (a, s'). split; [ exact Hxo |].
          apply obsAWLP_unfold. left. exists ob. exact (conj Hk Hp).
        * discriminate Hk.
      + destruct (proj1 (outcomes_bind x f s None) Hdiv) as [[[a s']|] [Hxo Hk]].
        * left. exists (a, s'). split; [ exact Hxo |].
          apply obsAWLP_unfold. right. exact Hk.
        * right. exact Hxo.
    - intro H. apply obsAWLP_unfold.
      destruct (proj1 (obsAWLP_unfold x s _) H) as [[[a s'] [Hxo Hk]] | Hdiv].
      + destruct (proj1 (obsAWLP_unfold (f a) s' post) Hk) as [[ob [Hob Hp]] | Hkdiv].
        * left. exists ob. split; [| exact Hp ].
          apply outcomes_bind. exists (Some (a, s')). exact (conj Hxo Hob).
        * right. apply outcomes_bind. exists (Some (a, s')). exact (conj Hxo Hkdiv).
      + right. apply outcomes_bind. exists None. exact (conj Hdiv eq_refl).
  Qed.

End NDMonadMorphismLawsWP.

End TermSliceObsWP.
