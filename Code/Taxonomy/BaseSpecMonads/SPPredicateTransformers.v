From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
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

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

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
  Definition ret {A} (a : A) : SPStMon A := fun pre r => pre (snd r) /\ fst r = a.
  Next Obligation. red. intuition. Qed.

  #[program]
  Definition bind {A B} (m : SPStMon A) (f : A -> SPStMon B) : SPStMon B :=
    fun pre r => exists a si, m pre (a, si) /\ f a (fun s' => s' = si) r.
  Next Obligation.
    red. intros * ? (? & ? & ? & ?); eexists _, _; intuition eauto.
    eapply (proj2_sig m); eassumption.
  Qed.

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

End AngelicMonotone. End AngelicMonotone.

Module DemonicMonotone. Section DemonicMonotone.
  Context {S : Type}.
  Let SPStMon A := SPStMon S A.

  #[program]
  Definition ret {A} (a : A) : SPStMon A :=
    fun pre r => fst r = a -> pre (snd r).
  Next Obligation. red; intros **; eauto. Qed.

  #[program]
  Definition bind {A B} (m : SPStMon A) (f : A -> SPStMon B) : SPStMon B :=
    fun pre r => forall a si, (forall prei, f a prei r -> prei si) -> m pre (a,si).
  Next Obligation.
    red; intros **; eapply (proj2_sig m); eauto.
  Qed.

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

End DemonicMonotone. End DemonicMonotone.
End SPStMonotone.
