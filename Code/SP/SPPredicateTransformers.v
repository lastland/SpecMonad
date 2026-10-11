From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.

Section BasePredicateTransformers.
  Definition SPPure (A : Type) : Type := Prop -> A -> Prop.

  Variable S : Type.

  Definition SPSt (A : Type) : Type := (S -> Prop) -> (A * S) -> Prop.

  Definition SPStExc (A : Type) : Type := (S -> Prop) -> option (A * S) -> Prop.
End BasePredicateTransformers.

Arguments SPSt {_}.
Arguments SPStExc {_}.

Section PurePredicateTransformers.
  Definition Strict {A} (w : SPPure A) : Prop :=
    forall (a : A), ~ w False a.

  Definition Terminating {A} (w : SPPure A) : Prop :=
    forall (a : A), w True a.

  Definition Conjunctive {A} (w : SPPure A) : Prop :=
    forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
      w (forall i, p i) a <-> forall i, w (p i) a.

  Definition Disjunctive {A} (w : SPPure A) : Prop :=
    forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
      w (exists i, p i) a <-> exists i, w (p i) a.
End PurePredicateTransformers.

Section ProgPredicateTransformers.
  Variable S : Type.

  Definition StrictProg {A} (w : SPStExc A) : Prop :=
    forall (r : option (A * S)), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : SPStExc A) : Prop :=
    forall (r : option (A * S)), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : SPStExc A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : SPStExc A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : option (A * S)),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
End ProgPredicateTransformers.

(* ================================================================= *)
(** * Terminating-slice variant (factored out of SPSimplerSpecMonads.v) *)
(* ================================================================= *)


Import MonadNotation.
Open Scope monad_scope.

Module StTrans.
Section Transformers.
  Variable S : Type.

  Definition StrictProg {A} (w : SPSt A) : Prop :=
    forall (r : A * S), ~ w (fun _ => False) r.

  Definition TerminatingProg {A} (w : SPSt A) : Prop :=
    forall (r : A * S), w (fun _ => True) r.

  Definition ConjunctiveProg {A} (w : SPSt A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : A * S),
      w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

  Definition DisjunctiveProg {A} (w : SPSt A) : Prop :=
    forall (I : Type), inhabited I ->
    forall (p : I -> (S -> Prop)) (r : A * S),
      w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.

End Transformers.


(* ---- orders and generic monotonicity ---- *)

Section StTransOrders.
  Variable S : Type.
  Definition ordSPSt {A} (m1 m2 : @SPSt S A) : Prop :=
    forall pre r, m1 pre r -> m2 pre r.
  (** Pointwise-equivalent preconditions are equal, so a transformer — an
      opaque function of the precondition — cannot tell them apart. *)
  Lemma predExt (X Y : S -> Prop) : (forall s, X s <-> Y s) -> X = Y.
  Proof.
    intro H. apply functional_extensionality. intro s.
    apply propositional_extensionality. exact (H s).
  Qed.

  (** Preserving NON-EMPTY meets already implies monotonicity: index the meet
      by [bool] over the pair {P, Q} and use [P = P /\ Q] when [P <= Q].  The
      empty meet — i.e. termination — plays no part. *)
  Theorem conjunctive_implies_monotone {A} (w : SPSt A) :
    ConjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HC P Q r Hsub Hw.
    assert (Heq : P = (fun s => forall b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intros Hp [|]; [ exact Hp | exact (Hsub s Hp) ].
      - intro H. exact (H true). }
    rewrite Heq in Hw.
    exact (proj1 (HC bool (inhabits true)
                    (fun b s => if b then P s else Q s) r) Hw false).
  Qed.

  (** Dually, for non-empty joins, via [Q = P \/ Q]. *)
  Theorem disjunctive_implies_monotone {A} (w : SPSt A) :
    DisjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HD P Q r Hsub Hw.
    assert (Heq : Q = (fun s => exists b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intro Hq. exists false. exact Hq.
      - intros [[|] H]; [ exact (Hsub s H) | exact H ]. }
    rewrite Heq.
    apply (HD bool (inhabits true) (fun b s => if b then P s else Q s) r).
    exists true. exact Hw.
  Qed.
End StTransOrders.
Arguments ordSPSt {_} {_}.
End StTrans.

(* ================================================================= *)
(** * Refinement order on the raw transformers, and monotonicity *)
(* ================================================================= *)

Section SPOrders.
  Variable S : Type.
  Definition ordSPStExc {A} (m1 m2 : @SPStExc S A) : Prop :=
    forall pre r, m1 pre r -> m2 pre r.
  (** Pointwise-equivalent preconditions are equal, so a transformer — an
      opaque function of the precondition — cannot tell them apart. *)
  Lemma predExt (X Y : S -> Prop) : (forall s, X s <-> Y s) -> X = Y.
  Proof.
    intro H. apply functional_extensionality. intro s.
    apply propositional_extensionality. exact (H s).
  Qed.

  (** Preserving NON-EMPTY meets already implies monotonicity: index the meet
      by [bool] over the pair {P, Q} and use [P = P /\ Q] when [P <= Q].  The
      empty meet — i.e. termination — plays no part. *)
  Theorem conjunctive_implies_monotone {A} (w : SPStExc A) :
    ConjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HC P Q r Hsub Hw.
    assert (Heq : P = (fun s => forall b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intros Hp [|]; [ exact Hp | exact (Hsub s Hp) ].
      - intro H. exact (H true). }
    rewrite Heq in Hw.
    exact (proj1 (HC bool (inhabits true)
                    (fun b s => if b then P s else Q s) r) Hw false).
  Qed.

  (** Dually, for non-empty joins, via [Q = P \/ Q]. *)
  Theorem disjunctive_implies_monotone {A} (w : SPStExc A) :
    DisjunctiveProg S w ->
    forall (P Q : S -> Prop) r, (forall s, P s -> Q s) -> w P r -> w Q r.
  Proof.
    intros HD P Q r Hsub Hw.
    assert (Heq : Q = (fun s => exists b : bool, if b then P s else Q s)).
    { apply predExt. intro s. split.
      - intro Hq. exists false. exact Hq.
      - intros [[|] H]; [ exact (Hsub s H) | exact H ]. }
    rewrite Heq.
    apply (HD bool (inhabits true) (fun b s => if b then P s else Q s) r).
    exists true. exact Hw.
  Qed.
End SPOrders.

Arguments ordSPStExc {_} {_}.

From ExtLib Require Import MonadState StateMonad.
From Incorrectness.Relational Require Import PredMonad.
From Incorrectness.WP Require Import WPureMonad.

Module SPStMonotone.
(* A stateful forward predicate transformer is monotone when it
  is order-preserving as a map from (S -> Prop) to (A × S -> Prop)
  (with pointwise order inherited from Prop) *)
Definition SPStMonotone  {S A} `(sp : @SPSt S A) :=
  forall (pre pre' : S -> Prop) r, (forall s, pre s -> pre' s) -> sp pre r -> sp pre' r.

(* The (angelic) monadic operations on stateful forward predicate
  transformers (SPSt) lift to monotone forward predicate transformers *)
Definition SPStMon S A := { sp : @SPSt S A | SPStMonotone sp }.

(* We lift the usual pointwise order on forward predicate transformers to
  monotone forward predicate transformers.  *)
Definition ordSPStMon {S A} (m m' : SPStMon S A) :=
  forall pre r, proj1_sig m pre r -> proj1_sig m' pre r.
Notation "m ≦ m'" := (ordSPStMon m m') (at level 70).
Notation "m ≈ m'" := (ordSPStMon m m' /\ ordSPStMon m' m).

Instance: forall {S A}, Reflexive (@ordSPStMon S A).
Proof. intros ?????; easy. Qed.

Instance: forall {S A}, Transitive (@ordSPStMon S A).
Proof. intros ??? ** ? **; eauto. Qed.


Module AngelicMonotone. Section AngelicMonotone.
  Context {S : Type}.
  Let SPStMon A := SPStMon S A.

  #[program]
  Definition retP {A} (a : A) : SPStMon A := fun pre r => pre (snd r) /\ fst r = a.
  Next Obligation. red. intuition. Qed.
  #[program]
  Definition bindP {A B} (m : SPStMon A) (f : A -> SPStMon B) : SPStMon B :=
    fun pre r => exists a si, m pre (a, si) /\ f a (fun s' => s' = si) r.
  Next Obligation.
    red. intros * ? (? & ? & ? & ?); eexists _, _; intuition eauto.
    eapply (proj2_sig m); eassumption.
  Qed.

  #[global]
    Instance Monad__AngelicSPStMon : Monad SPStMon :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  #[program]
  Definition bindAlt {A B} (m : SPStMon A) (f : A -> SPStMon B) : SPStMon B :=
    fun pre r => exists a si prei, m pre (a, si) /\ f a prei r /\ (forall s, prei s -> s = si).
  Next Obligation.
    red. intros * ? (? & ? & ? & ?); eexists _, _, _; intuition eauto.
    eapply (proj2_sig m); eassumption.
  Qed.

  (* The bind operation is monotone in both arguments with respect to this order. *)
  Lemma bind_monotone {A B} (m m' : SPStMon A) (f f' : A -> SPStMon B) :
    m ≦ m' -> (forall a, f a ≦ f' a) -> bind m f ≦ bind m' f'.
  Proof.
    intros hm hf pre r (a&si&?&?); exists a, si; split.
    1: now apply hm.
    now apply hf.
  Qed.

  Lemma bind_bindAlt_equiv {A B} (m : SPStMon A) (f : A -> SPStMon B) :
    bind m f ≈ bindAlt m f.
  Proof.
    split; intros ??.
    - intros (?&?&?&?); eexists _, _, _; repeat split; try eassumption; cbn; easy.
    - intros (?&?&?&?&?&?); eexists _, _; split ; [eassumption|].
      eapply (proj2_sig (f _)); eassumption.
  Qed.


  (* These operations satisfy the right unitality and associativity from the usual monadic laws,
    but not the left unitality. In the latter case, we can however retain an inequation. *)

  Lemma runit {A} (m : SPStMon A) : bind m ret ≈ m.
  Proof.
    split; intros ??; cbn.
    - intros (?&?&?&?&?); subst; now rewrite surjective_pairing.
    - intros ?. exists (fst r), (snd r). rewrite <-surjective_pairing.
      easy.
  Qed.

  Lemma assoc {A B C} (m : SPStMon A) (f : A -> SPStMon B) (g : B -> SPStMon C) :
    bind m (fun a => bind (f a) g) ≈ bind (bind m f) g.
  Proof.
    split; intros ??; cbn.
    - intros (a & s1 & hm & b & s2 & hf & hg).
      exists b, s2; split; [|assumption].
      exists a, s1; now split.
    - intros (b & s2 & (a & s1 & hm & hf) & hg).
      exists a, s1; split; [assumption|].
      exists b, s2; now split.
  Qed.

  Lemma lunit {A B} (a : A) (f : A -> SPStMon B) : bind (ret a) f ≦ f a.
  Proof. intros ?? (?&?& [] &?); cbn in *; subst.
    revert H1; apply (proj2_sig (f a)).
    intros; subst; easy.
  Qed.

  Definition inhabited (X : Type) := exists x : X, True.

  Lemma lunitStrictlyLax  : inhabited S -> exists A B (a : A) (f : A -> SPStMon B), ~(f a ≦ bind (ret a) f).
  Proof.
    intros [s0]. unshelve eexists unit, unit, tt, (fun _ => exist _ (fun _ _ => True) _).
    - constructor.
    - intros h. now destruct (h (fun _ => False) (tt, s0) I) as (?&?& [] & ?).
  Qed.

  Definition map {A B} (f : A -> B) : SPStMon A -> SPStMon B :=
    fun m => bind m (fun a => ret (f a)).

  Lemma map_alt {A B} (f : A -> B) m pre r :
    proj1_sig (map f m) pre r <-> exists a, proj1_sig m pre (a, snd r) /\ fst r = f a.
  Proof.
    split; cbn.
    - intros (?&?&?&?&?); subst; eexists; eauto.
    - intros (?&?&?); eexists _,_; eauto.
  Qed.


  Lemma map_id {A} (m : SPStMon A) : map (fun x => x) m ≈ m.
  Proof.
    split.
    - intros ?? (?&?&?&?&?); rewrite surjective_pairing; now subst.
    (* Holds for any left-skew monad *)
    - unfold map; apply runit.
  Qed.

  Lemma map_comp {A B C} (f : A -> B) (g : B -> C) m :
    map g (map f m) ≈ map (fun a => g (f a)) m.
  Proof.
    split.
    (* Holds for any left-skew monad *)
    - unfold map.
      transitivity (bind m (fun a => bind (ret (f a)) (fun b => ret (g b)))).
      1: apply assoc.
      apply bind_monotone ; [reflexivity|].
      intros; apply (lunit (f a)).
    - intros ?? (?&?&?)%map_alt.
      eapply map_alt; eexists; split; [|eassumption].
      eapply map_alt; cbn; eexists; split; [| reflexivity]; assumption.
  Qed.

  Import PredSt.

  #[program]
  Definition fromPred {A} (p : PredSt S A) : SPStMon A :=
    fun pre r => exists s0, pre s0 /\ runStateT p s0 r.
  Next Obligation.
    red; intros * ? (?&?&?); eexists; split; eauto.
  Qed.

  Lemma fromPred_ret {A} (a : A) : fromPred (ret a) ≈ ret a.
  Proof.
    split; unfold fromPred.
    - intros ?? (?&?& ->); cbn in *; split; eauto.
    - intros ?? [? <-]; cbn; eexists; split; eauto.
      now rewrite surjective_pairing.
  Qed.

  Lemma fromPred_bind {A B} (m : PredSt S A) (f : A -> PredSt S B) :
    fromPred (bind m f) ≈ bind (fromPred m) (fun a => fromPred (f a)).
  Proof.
    split; intros ??; unfold fromPred; cbn; unfold PredM.bindPred.
    - intros (? & ? & [] & ? & ?); eexists _, _; split; eexists; split; cbn in *; eauto.
    - intros (?&?&(?&?&?)&?&->&?). eexists; split; eauto; eexists (_,_); split; eauto.
  Qed.

  #[program]
  Definition Ladj {A} (sp : SPStMon A) (w : WSt S A) :=
    forall pre post, (forall r, sp pre r -> post r) <-> (forall s0, pre s0 -> runStateT w s0 post).

  #[local] Notation "m ≈WSt m'" := (ordWSt m m' /\ ordWSt m' m) (at level 70).
  (* Ladj is *not* monotone in any of its arguments *)
  (* But it is compatible with the equivalence relation induced by the preorder *)
  Definition Ladj_equiv {A} {sp sp' : SPStMon A} {w w' : WSt S A} :
    sp ≈ sp' -> w ≈WSt w' -> Ladj sp w -> Ladj sp' w'.
  Proof.
    intros eqvsp eqvw hadj;  intros ??; split; intros h.
    - intros s hpre. eapply eqvw. revert s hpre. eapply (proj1 (hadj _ _)).
      intros ? ?%eqvsp; eauto.
    - intros r hpre%eqvsp; revert r hpre; eapply hadj.
      intros ??; eapply eqvw; eauto.
  Qed.

  Definition Ladj_equiv' {A} {sp sp' : SPStMon A} {w w' : WSt S A} :
    sp ≈ sp' -> w ≈WSt w' -> Ladj sp' w' -> Ladj sp w.
  Proof.
    intros eqvsp eqvw ? ; eapply Ladj_equiv; eauto; split; first [eapply eqvsp| eapply eqvw].
  Qed.

  Lemma Ladj_ret {A} (a : A) : Ladj (ret a) (ret a).
  Proof.
    intros ??; split.
    - intros H **; cbn; eapply H; cbn; split; eauto.
    - intros H [] []; subst; now apply H.
  Qed.

  Lemma Ladj_bind {A B} (spm : SPStMon A) (wm : WSt S A) (spf : A -> SPStMon B) (wf : A -> WSt S B) :
    Ladj spm wm -> (forall a, Ladj (spf a) (wf a)) -> Ladj (bind spm spf) (bind wm wf).
  Proof.
    intros hm hf ??; split.
    - intros H. cbn in H.
      cbn.
      intros s0 hpre. set (p := fun _ => _).
      apply (hm pre p); eauto.
      intros []; subst p. intros; cbn.
      eapply (hf a (fun s' => s' = s) post); eauto.
    - intros H [] (?&?&?&?); cbn in *.
      revert H1. apply hf.
      intros ?? ; subst.
      revert H0; eapply (hm pre (fun a => (let (v, s) := a in runStateT (wf v) s) post)).
      intros **. eauto.
  Qed.

  (* Composing pred2pp and pp2wp*)
  #[program]
  Definition pred2WSt {A} (p : PredSt S A) : WSt S A :=
    {| runStateT s post := forall r, runStateT p s r -> post r|}.
  Next Obligation.
    intros ?? ** ; eauto.
  Qed.

  Lemma pred2WSt_ret {A} (a : A): pred2WSt (ret a) ≈WSt ret a.
  Proof.
    split; intros ??; cbn.
    - now intros ?? ->.
    - intros h; now apply h.
  Qed.
  Lemma pred2WSt_bind {A B} (p : PredSt S A) (f : A -> PredSt S B) :
      pred2WSt (bind p f) ≈WSt bind (pred2WSt p) (fun a => pred2WSt (f a)).
  Proof.
    split; intros ??; cbn.
    - intros h ? ([]&hp&?); now apply (h _ hp).
    - intros h [] ? ??; apply h; eexists; split; eauto.
  Qed.

  Lemma Ladj_fromPred {A} (p : PredSt S A) : Ladj (fromPred p) (pred2WSt p).
  Proof.
    intros ??; cbn; split.
    - intros h **; apply h; eexists; eauto.
    - intros ?? (?&?&?); eauto.
  Qed.

  (* right adjoints elements are conjunctive and terminating *)
  Lemma Ladj_lim {A} (sp : SPStMon A) (w : WSt S A) : Ladj sp w -> forall I (post : I -> A * S -> Prop),
    forall s, runStateT w s (fun r => forall i, post i r) <-> forall i,  runStateT w s (post i).
  Proof.
    intros hadj I post r; split.
    - intros hsp i; revert hsp; eapply (getWPure_mono (runStateT w _)); eauto.
    - eapply (proj1 (hadj (fun s => forall i, runStateT w s (post i)) _)).
      intros ? hw i; revert hw; apply hadj; eauto.
  Qed.

  (* left adjoints elements are disjunctive and strict *)
  Lemma Ladj_colim {A} (sp : SPStMon A) (w : WSt S A) : Ladj sp w -> forall I (pre : I -> S -> Prop),
    forall r, proj1_sig sp (fun s => exists i, pre i s) r <-> exists i, proj1_sig sp (pre i) r.
  Proof.
    intros hadj I pre r; split.
    - intros hsp; pattern r; revert hsp; eapply (proj2 (hadj _ _)).
      intros ? [? hpre]; revert hpre; apply hadj; eauto.
    - intros [i hsp]; revert hsp; eapply (proj2_sig  sp); eauto.
  Qed.

  #[program]
  Definition toPred {A} (sp : SPStMon A) : PredSt S A :=
    {| runStateT s0 := sp (fun s => s = s0) |}.


  #[local] Notation "m ≈P m'" := (ordPredSt m m' /\ ordPredSt m' m) (at level 70).
  Lemma toPred_ret {A} (a : A) : toPred (ret a) ≈P ret a.
  Proof.
    split; intros ??; cbn.
    - intros [<- <-]; now rewrite surjective_pairing.
    - intros ->; eauto.
  Qed.

  Lemma toPred_bind {A B} (spm : SPStMon A) (spf : A -> SPStMon B) :
    toPred (bind spm spf) ≈P bind (toPred spm) (fun a=> toPred (spf a)).
  Proof.
    split; intros ??; cbn.
    - intros (?&?&?&?). eexists; split; eassumption.
    - intros ([]&?&?). eexists _, _; split; eassumption.
  Qed.

  Lemma fromPred_toPred_adj {A} (p : PredSt S A) (sp : SPStMon A) :
    fromPred p ≦ sp <-> ordPredSt p (toPred sp).
  Proof.
    split.
    - intros h ???; eapply h; cbn; eexists; split; eauto.
    - intros h ?? (?&?&H%h); revert H; cbn.
      apply (proj2_sig sp); intros; subst; eauto.
  Qed.
  (* toPred (fromPred p) ≈P p always *)
  (* fromPred (toPred sp) ≈ sp when sp is strict and disjunctive *)

  Lemma Ladj_pred {A} (sp : SPStMon A) (w : WSt S A) : Ladj sp w <-> exists p, sp ≈ fromPred p /\ w ≈WSt pred2WSt p.
  Proof.
    split.
    - intros hadj. exists (toPred sp); split.
      + split; intros ??; unfold fromPred; cbn.
        * intros hsp.
          assert (proj1_sig sp (fun s => exists (s0 : {s0 | pre s0}), s = proj1_sig s0) r).
          1: revert hsp; eapply (proj2_sig sp); intros ??; unshelve eexists (exist _ _ _); cbn; eauto.
          eapply (Ladj_colim _ _ hadj) in H.
          destruct H as [[??] ?]; eexists; split; eauto.
        * intros (?&?&H); revert H; eapply (proj2_sig sp); now intros ? ->.
      + split; intros ??; cbn.
        * intros H. eapply (proj1 (hadj _ _)) in H; eauto.
        * intros ?; eapply (proj2 (hadj _ _)); now intros ? ->.
    - intros (?&?&?); eapply Ladj_equiv'; eauto; apply Ladj_fromPred.
  Qed.

End AngelicMonotone. End AngelicMonotone.

Module DemonicMonotone. Section DemonicMonotone.
  Context {S : Type}.
  Let SPStMon A := SPStMon S A.

  #[program]
  Definition retP {A} (a : A) : SPStMon A :=
    fun pre r => fst r = a -> pre (snd r).
  Next Obligation. red; intros **; eauto. Qed.

  #[program]
  Definition bindP {A B} (m : SPStMon A) (f : A -> SPStMon B) : SPStMon B :=
    fun pre r => forall a si, (forall prei, f a prei r -> prei si) -> m pre (a,si).
  Next Obligation.
    red; intros **; eapply (proj2_sig m); eauto.
  Qed.

  #[global]
    Instance Monad__DemonicSPStMon : Monad SPStMon :=
    {| ret := fun _ => @retP _ ;
       bind := fun _ _ => @bindP _ _ |}.

  Lemma bind_monotone {A B} (m m' : SPStMon A) (f f' : A -> SPStMon B) :
    m ≦ m' -> (forall a, f a ≦ f' a) -> bind m f ≦ bind m' f'.
  Proof.
    intros hm hf pre r hmf ?? h; apply hm, hmf.
    intros; now apply h, hf.
  Qed.


  Lemma lunit {A B} (a : A) (f : A -> SPStMon B) : f a ≦ bind (ret a) f.
  Proof.
    intros ?? hfa a' si hfa' ?; cbn in *; subst; eapply hfa'; assumption.
  Qed.

  Lemma runit {A} (m : SPStMon A) : bind m ret ≦ m.
  Proof.
    intros ? [] hmret; apply hmret; cbn; eauto.
  Qed.

  Lemma assoc {A B C} (m : SPStMon A) (f : A -> SPStMon B) (g : B -> SPStMon C) :
    bind m (fun a => bind (f a) g) ≦ bind (bind m f) g.
  Proof.
    intros ??; cbn; intros h  ?? hg ?? hf; apply h; intros pre1 hfg.
    eapply hf, hfg, hg.
  Qed.

  Definition map {A B} (f : A -> B) : SPStMon A -> SPStMon B :=
    fun m => bind m (fun a => ret (f a)).

  Lemma map_alt {A B} (f : A -> B) m pre r :
    proj1_sig (map f m) pre r <-> forall a, fst r = f a -> proj1_sig m pre (a, snd r).
  Proof.
    split; cbn.
    - intros h??; apply h; eauto.
    - intros h ?? hs.
      unshelve epose (hs' := hs (fun s => fst r = f a /\ s = snd r) _).
      2: cbn in hs'; destruct hs' ; subst; eauto.
      cbn; eauto.
  Qed.

  Lemma map_id {A} (m : SPStMon A) : map (fun x => x) m ≈ m.
  Proof.
    split.
    (* Holds for any right-skew monoidale *)
    - apply runit.
    - intros ?? ?; apply map_alt; intros ? <-; now rewrite <-surjective_pairing.
  Qed.

  Lemma map_comp {A B C} (f : A -> B) (g : B -> C) m :
    map g (map f m) ≈ map (fun a => g (f a)) m.
  Proof.
    split.
    - intros ?? h; apply map_alt; intros ??.
      eapply map_alt in h; [|eassumption].
      eapply map_alt in h; [|reflexivity].
      assumption.
    (* Holds for any right-skew monad *)
    - unfold map.
      transitivity (bind m (fun a => bind (ret (f a)) (fun b => ret (g b)))).
      2: apply assoc.
      apply bind_monotone ; [reflexivity|].
      intros; apply (lunit (f a) (fun b => ret (g b))).
  Qed.

  Import PredSt.

  #[program]
  Definition fromPred {A} (p : PredSt S A) : SPStMon A :=
    fun pre r => forall s0, runStateT p s0 r -> pre s0.
  Next Obligation.
    red; intros **; eauto.
  Qed.

  Lemma fromPred_antitone {A} {p p' : PredSt S A} :
    ordPredSt p p' -> fromPred p' ≦ fromPred p.
  Proof.
    intros hp ???? ?%hp; eauto.
  Qed.

  #[program]
  Definition toPred {A} (sp : SPStMon A) : PredSt S A :=
    {| runStateT s0 := fun r => forall pre, sp pre r -> pre s0 |}.

  Lemma fromPred_toPred_adj {A} (sp : SPStMon A) (p : PredSt S A) :
    sp ≦ fromPred p <-> ordPredSt p (toPred sp).
  Proof.
    split; intros h ?????; eapply h; eassumption.
  Qed.

  Lemma fPtP_unit {A} {sp : SPStMon A} : sp ≦ fromPred (toPred sp).
  Proof.
    (* intros ?? h ? hfp; cbn; apply hfp, h. *)
    apply fromPred_toPred_adj; now intros ???. (* reflexivity *)
  Qed.

  Lemma tPfP_unit {A} (p : PredSt S A) : ordPredSt p (toPred (fromPred p)).
  Proof.
    apply fromPred_toPred_adj; now intros ???. (* reflexivity *)
  Qed.

  Lemma tPfP_unit_inv {A} (p : PredSt S A) : ordPredSt (toPred (fromPred p)) p.
  Proof.
    intros ?? h; pattern s; apply h; cbn; now intros ??.
  Qed.

  Definition sp_conj_term {A} (sp : SPStMon A)  := forall I (pre : I -> S -> Prop),
    forall r, proj1_sig sp (fun s=> forall i, pre i s) r <-> forall i, proj1_sig sp (pre i) r.

  Lemma fPtP_unit_inv {A} {sp : SPStMon A} :
    sp_conj_term sp -> fromPred (toPred sp) ≦ sp.
  Proof.
    intros ctsp ?? h; cbn in *.
    assert (proj1_sig sp (fun s0 => forall (pre : { pre | proj1_sig sp pre r}), proj1_sig pre s0) r).
    - apply ctsp. intros []; now cbn.
    - revert H; apply (proj2_sig sp).
      intros ? H; eapply h; intros pre' hpre'; apply (H (exist _ pre' hpre')).
  Qed.

  Lemma fromPred_ret {A} (a : A) : fromPred (ret a) ≈ ret a.
  Proof.
    split; unfold fromPred.
    - intros ?? H ?; subst; apply H. now rewrite surjective_pairing.
    - intros ? [] ?? [=]; subst; eauto.
  Qed.

  Lemma fromPred_bind {A B} (m : PredSt S A) (f : A -> PredSt S B) :
    fromPred (bind m f) ≈ bind (fromPred m) (fun a => fromPred (f a)).
  Proof.
    split; intros ??; unfold fromPred; cbn; unfold PredM.bindPred.
    - intros H ?? H' **. eapply H. eexists (_,_); split; eauto.
      pattern si; apply H'; eauto.
    - intros H ? ([]&?&?). eapply H; eauto.
  Qed.

  (* Radj is *not* monotone in any of its arguments *)
  #[program]
  Definition Radj {A} (sp : SPStMon A) (w : WSt S A) :=
    forall pre post, (forall s0, runStateT w s0 post -> pre s0) <-> (forall r, post r -> sp pre r).

  #[local] Notation "m ≈WSt m'" := (ordWSt m m' /\ ordWSt m' m) (at level 70).

  Definition Radj_equiv {A} {sp sp' : SPStMon A} {w w' : WSt S A} :
    sp ≈ sp' -> w ≈WSt w' -> Radj sp' w' -> Radj sp w.
  Proof.
    intros eqvsp eqvw hadj;  intros ??; split; intros h.
    - intros s hpre. eapply eqvsp. revert s hpre. eapply (proj1 (hadj _ _)).
      intros ? ?%eqvw; eauto.
    - intros r hpre%eqvw; revert r hpre; eapply hadj.
      intros ??; eapply eqvsp; eauto.
  Qed.

  (* right adjoints elements are conjunctive and terminating *)
  Lemma Radj_lim {A} (sp : SPStMon A) (w : WSt S A) : Radj sp w -> sp_conj_term sp.
  Proof.
    intros hadj I pre r; split.
    - intros hsp i; revert hsp; eapply (proj2_sig sp); eauto.
    - eapply (proj1 (hadj _ (fun r => forall i, proj1_sig sp (pre i) r))).
      intros ? hw i; revert hw; apply hadj; eauto.
  Qed.

  Lemma Radj_colim {A} (sp : SPStMon A) (w : WSt S A) : Radj sp w -> forall I (post : I -> A * S -> Prop),
    forall s, runStateT w s (fun r => exists i, post i r) <-> exists i, runStateT w s(post i).
  Proof.
    intros hadj I post s; split.
    - intros hw; pattern s; revert hw; apply hadj.
      intros ? [i hpost]; revert hpost; apply hadj.
      intros; eexists; eassumption.
    - intros [i hw]; revert hw; eapply (getWPure_mono (runStateT w _)).
      intros; eexists; eassumption.
  Qed.


  Lemma Radj_ret {A} (a : A) : Radj (ret a) (ret a).
  Proof.
    intros ??; split; cbn.
    - intros h???; apply h; subst; now rewrite <-surjective_pairing.
    - intros h ??%h; eauto.
  Qed.

  (* There should be a direct way to prove that Radj is compatible with bind
    but it looks painful, see below for an alternative proof *)
  (* Lemma Radj_bind {A B} (spm : SPStMon A) (wm : WSt S A) (spf : A -> SPStMon B) (wf : A -> WSt S B) :
    Radj spm wm -> (forall a, Radj (spf a) (wf a)) -> Radj (bind spm spf) (bind wm wf).
  Proof.
    intros hm hf ??; split; cbn.
    - intros h **. eapply (proj1 (hm _ _)); eauto; cbn.
      pattern si; apply H0; cbn; eapply (proj1 (hf a _ _)); eauto.
    - intros h ?; eapply hm; intros [a s1] hwf.
      assert (exists r, post r /\ (forall prei, proj1_sig (spf a) prei r -> prei s1)).
      + pattern s1; revert hwf. eapply (proj2 (hf a _ _)).
        intros ??. admit.
      + destruct H as [r []]; eauto.
      intros; eapply h. eauto.

      epose (r := proj2 (hf a _ _)); unfold Radj in r.
      eapply r.
     ?; eapply h.
      1: apply H.
     eapply (hf a).
      eapply
  Qed. *)

  #[program]
  Definition pred2WSt {A} (p : PredSt S A) : WSt S A :=
    {| runStateT s0 := fun post => exists r, runStateT p s0 r /\ post r |}.
  Next Obligation.
    intros ??? (?&?&?); eexists; eauto.
  Qed.

  Lemma pred2WSt_ret {A} (a : A): pred2WSt (ret a) ≈WSt ret a.
  Proof.
    split; intros ??; cbn.
    - intros; eexists; split; eauto; reflexivity.
    - now intros (?&<-&?).
  Qed.

  Lemma pred2WSt_bind {A B} (p : PredSt S A) (f : A -> PredSt S B) :
      pred2WSt (bind p f) ≈WSt bind (pred2WSt p) (fun a => pred2WSt (f a)).
  Proof.
    split; intros ??; cbn.
    - intros ([]&?&?&?&?). eexists; split; eauto; eexists; split; eauto.
    - intros (?&([]&?&?)&?); eexists; split; eauto. eexists; split; eauto.
  Qed.

  Lemma Radj_fromPred {A} (p : PredSt S A) : Radj (fromPred p) (pred2WSt p).
  Proof.
    intros ??; cbn; split.
    - intros h **; apply h; eauto.
    - intros ?? (?&?&?); eauto.
  Qed.

  Lemma Radj_toPred {A} (sp : SPStMon A) (w : WSt S A) :
    Radj sp w <-> sp ≈ fromPred (toPred sp) /\ w ≈WSt pred2WSt (toPred sp).
  Proof.
    split.
    - intros hadj; split; split.
      + apply fPtP_unit.
      + eapply fPtP_unit_inv, Radj_lim; eassumption.
      + intros ?? (?&?&?); cbn in *.
        unfold Radj in hadj.
        pattern s; apply H.
        revert H0; eapply (proj1 (hadj _ _)); now intros ??.
      + intros ?? hw; pattern s; revert hw. eapply (proj2 (hadj _ _)).
        intros ??; cbn.
        assert (h' : proj1_sig sp (fun s0 => forall (pre : {pre | proj1_sig sp pre r}), proj1_sig pre s0) r).
        * eapply Radj_lim. 1: eassumption.
          intros (?&?); now cbn.
        * revert h'; eapply (proj2_sig sp).
          intros ? h'; eexists; split ; [|eassumption].
          intros pre hpre; exact (h' (exist _ pre hpre)).
    - intros [??]; eapply Radj_equiv; try eassumption; apply Radj_fromPred.
  Qed.

  Lemma Radj_pred {A} (sp : SPStMon A) (w : WSt S A) :
    Radj sp w <-> exists p, sp ≈ fromPred p /\ w ≈WSt pred2WSt p.
  Proof.
    split.
    - intros hadj. exists (toPred sp); now apply Radj_toPred.
    - intros (?&?&?); eapply Radj_equiv; try eassumption; apply Radj_fromPred.
  Qed.

  Lemma Radj_bind {A B} (spm : SPStMon A) (wm : WSt S A) (spf : A -> SPStMon B) (wf : A -> WSt S B) :
    Radj spm wm -> (forall a, Radj (spf a) (wf a)) -> Radj (bind spm spf) (bind wm wf).
  Proof.
    intros [??]%Radj_toPred hf.
    assert (forall a, spf a ≈ fromPred (toPred (spf a))).
    1: intros a; specialize (hf a); apply Radj_toPred in hf; now destruct hf.
    assert (forall a, wf a ≈WSt pred2WSt (toPred (spf a))).
    1: intros a; specialize (hf a); apply Radj_toPred in hf; now destruct hf.
    apply Radj_toPred;split.
    (* Setoid rewrite material...
    *)
  Admitted.

End DemonicMonotone. End DemonicMonotone.
End SPStMonotone.





