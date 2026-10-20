(** * Which orders on SP readings can make [bind] monotone.

    An SP reading judges a program outcome by outcome: at each terminating
    outcome [r] it looks at the set of start states that reach [r] (the
    predecessor set [R⁻¹ r]).  Its refinement order is therefore OUTCOME-LOCAL:
    one preorder [sq] on sets of start states, lifted pointwise over outcomes,

      [leRel sq R R'  :=  forall r, sq (R⁻¹ r) (R'⁻¹ r)].

    A reading [Φ : (S -> Prop) -> (S -> Prop) -> Prop] (predecessor set,
    precondition) induces [readOrder Φ X Y := forall P, Φ X P -> Φ Y P].
    ASP is [Φ X P = X ∩ P ≠ ∅], DSLP is [X ⊆ P], DSP their conjunction and
    ASLP their disjunction.

    [classification]: if [leRel sq] makes relational [bind] monotone in its
    CONTINUATION, then [sq] is equality, [⊆], [⊇], or total.  No other
    outcome-local order is a congruence.  [classification_prog] is the same
    statement for the order a specification monad induces on [stdivnd]
    programs through any effect observation, for ANY target monad [W].

    The proof uses two contexts:
    - a prefix [G] turns [sq X Y] into [sq (G⁻¹ X) (G⁻¹ Y)] ([sq_preimage]);
    - a nondeterministic boolean prefix turns two comparisons into one on
      their unions ([sq_union]).
    A prefix that sends every state of [U] to a point [x ∈ X \ Y] then gives
    [sq U ∅] for EVERY [U] ([sq_drop]); dually [sq ∅ U] ([sq_add]).

    Instances.  ASP induces [⊆] and DSLP [⊇] ([readOrder_ASP_is_incl],
    [readOrder_DSLP_is_rev_incl]).  DSP and ASLP are refuted directly by
    [sq_drop] / [sq_add], without the classical case split
    ([DSP_order_not_bind_mono], [ASLP_order_not_bind_mono]); lifted to any
    specification monad in [no_spec_monad_with_DSP_order] /
    [no_spec_monad_with_ASLP_order]:
    - DSP has [{0,1} ⊑ {0}] (dropping a start state is allowed) but not
      [{0} ⊑ ∅];
    - ASLP has [{0} ⊑ {0,1}] (adding one is allowed) but not [∅ ⊑ {0}].

    Mixed-ness alone is not the criterion.  The reading "the predecessor set
    is exactly [P]" is neither monotone nor antitone, yet it induces equality,
    which is a congruence ([readOrder_exact_is_eq]).  The classification is
    the precise statement. *)

From Coq Require Import Classical PeanoNat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivNonDet_SPSt_Arrow.
From Incorrectness.Taxonomy.DijkstraMonads Require Import ASPUnderObstructions.

Import MonadNotation.
Open Scope monad_scope.

Definition bindRel {S A B} (R : S -> A * S -> Prop) (K : A -> S -> B * S -> Prop)
  : S -> B * S -> Prop :=
  fun s r => exists a s', R s (a, s') /\ K a s' r.

Definition leRel {S B} (sq : (S -> Prop) -> (S -> Prop) -> Prop)
  (R R' : S -> B * S -> Prop) : Prop :=
  forall r, sq (fun s => R s r) (fun s => R' s r).

Definition readOrder {S} (Φ : (S -> Prop) -> (S -> Prop) -> Prop)
  (X Y : S -> Prop) : Prop :=
  forall P, Φ X P -> Φ Y P.

Definition sameSet {S} (X Y : S -> Prop) : Prop := forall s, X s <-> Y s.

Section Classification.
  Variable S : Type.
  Variable S_dec : forall x y : S, {x = y} + {x <> y}.
  Variable s0 : S.

  Variable sq : (S -> Prop) -> (S -> Prop) -> Prop.
  Hypothesis sq_refl : forall X, sq X X.
  Hypothesis sq_trans : forall X Y Z, sq X Y -> sq Y Z -> sq X Z.
  Hypothesis sq_ext : forall X X' Y Y',
      sameSet X X' -> sameSet Y Y' -> sq X Y -> sq X' Y'.

  (** Monotonicity of relational [bind] in its continuation, at result
      type [unit]. *)
  Hypothesis bind_mono_k :
    forall A (g : S -> A * S -> Prop) (k k' : A -> S -> unit * S -> Prop),
      (forall a, leRel sq (k a) (k' a)) -> leRel sq (bindRel g k) (bindRel g k').

  (** [relOf X] reaches the single outcome [(tt, s0)] from exactly [X]. *)
  Let relOf (X : S -> Prop) : S -> unit * S -> Prop :=
    fun s r => X s /\ snd r = s0.

  Let leRel_relOf X Y : sq X Y -> leRel sq (relOf X) (relOf Y).
  Proof.
    intros H [[] t]. unfold relOf; cbn.
    destruct (S_dec t s0) as [-> | Hne].
    - apply (sq_ext X _ Y); [ intro s; tauto | intro s; tauto | exact H ].
    - apply (sq_ext (fun _ => False) _ (fun _ => False));
        [ intro s; tauto | intro s; tauto | apply sq_refl ].
  Qed.

  Lemma sq_preimage (G : S -> S -> Prop) X Y :
    sq X Y ->
    sq (fun s => exists s', G s s' /\ X s') (fun s => exists s', G s s' /\ Y s').
  Proof.
    intro H.
    pose proof (bind_mono_k unit (fun s r => G s (snd r))
                  (fun _ => relOf X) (fun _ => relOf Y)
                  (fun _ => leRel_relOf X Y H) (tt, s0)) as Hb.
    unfold bindRel, relOf in Hb; cbn in Hb.
    refine (sq_ext _ _ _ _ _ _ Hb); intro s; split.
    - intros [[] [s' [HG [HX _]]]]. exists s'. exact (conj HG HX).
    - intros [s' [HG HX]]. exists tt, s'. exact (conj HG (conj HX eq_refl)).
    - intros [[] [s' [HG [HY _]]]]. exists s'. exact (conj HG HY).
    - intros [s' [HG HY]]. exists tt, s'. exact (conj HG (conj HY eq_refl)).
  Qed.

  Lemma sq_union X1 X2 Y1 Y2 :
    sq X1 Y1 -> sq X2 Y2 ->
    sq (fun s => X1 s \/ X2 s) (fun s => Y1 s \/ Y2 s).
  Proof.
    intros H1 H2.
    pose proof (bind_mono_k bool (fun s r => snd r = s)
                  (fun b => relOf (if b then X1 else X2))
                  (fun b => relOf (if b then Y1 else Y2))
                  (fun b => leRel_relOf _ _ (if b as b0 return
                             sq (if b0 then X1 else X2) (if b0 then Y1 else Y2)
                           then H1 else H2))
                  (tt, s0)) as Hb.
    unfold bindRel, relOf in Hb; cbn in Hb.
    refine (sq_ext _ _ _ _ _ _ Hb); intro s; split.
    - intros [[] [s' [Heq [H _]]]]; cbn in Heq; subst s'; tauto.
    - intros [H | H]; [ exists true | exists false ]; exists s; cbn; tauto.
    - intros [[] [s' [Heq [H _]]]]; cbn in Heq; subst s'; tauto.
    - intros [H | H]; [ exists true | exists false ]; exists s; cbn; tauto.
  Qed.

  (** A start state that [X] has and [Y] lacks: everything is below [∅]. *)
  Lemma sq_drop X Y x : sq X Y -> X x -> ~ Y x -> forall U, sq U (fun _ => False).
  Proof.
    intros H Hx Hy U.
    refine (sq_ext _ _ _ _ _ _ (sq_preimage (fun s s' => U s /\ s' = x) X Y H));
      intro s; split.
    - intros [s' [[HU ->] _]]. exact HU.
    - intro HU. exists x. exact (conj (conj HU eq_refl) Hx).
    - intros [s' [[_ ->] HY]]. exact (Hy HY).
    - intros [].
  Qed.

  (** A start state that [Y] has and [X] lacks: [∅] is below everything. *)
  Lemma sq_add X Y y : sq X Y -> ~ X y -> Y y -> forall U, sq (fun _ => False) U.
  Proof.
    intros H Hx Hy U.
    refine (sq_ext _ _ _ _ _ _ (sq_preimage (fun s s' => U s /\ s' = y) X Y H));
      intro s; split.
    - intros [s' [[_ ->] HX]]. exact (Hx HX).
    - intros [].
    - intros [s' [[HU ->] _]]. exact HU.
    - intro HU. exists y. exact (conj (conj HU eq_refl) Hy).
  Qed.

  Lemma sq_all_down (Hd : forall U, sq U (fun _ => False)) X Y :
    (forall s, Y s -> X s) -> sq X Y.
  Proof.
    intro Hsub.
    refine (sq_ext _ _ _ _ _ _ (sq_union X Y (fun _ => False) Y (Hd X) (sq_refl Y)));
      intro s; split; intro H; try tauto.
    destruct H; auto.
  Qed.

  Lemma sq_all_up (Hu : forall U, sq (fun _ => False) U) X Y :
    (forall s, X s -> Y s) -> sq X Y.
  Proof.
    intro Hsub.
    refine (sq_ext _ _ _ _ _ _ (sq_union (fun _ => False) X Y X (Hu Y) (sq_refl X)));
      intro s; split; intro H; try tauto.
    destruct H; auto.
  Qed.

  Theorem classification :
    (forall X Y, sq X Y <-> sameSet X Y)
    \/ (forall X Y, sq X Y <-> (forall s, X s -> Y s))
    \/ (forall X Y, sq X Y <-> (forall s, Y s -> X s))
    \/ (forall X Y, sq X Y).
  Proof.
    destruct (classic (exists X Y x, sq X Y /\ X x /\ ~ Y x))
      as [[X1 [Y1 [x [H1 [Hx Hnx]]]]] | Hnd];
    destruct (classic (exists X Y y, sq X Y /\ ~ X y /\ Y y))
      as [[X2 [Y2 [y [H2 [Hny Hy]]]]] | Hnu].
    - (* both: total *)
      right; right; right. intros X Y.
      exact (sq_trans _ _ _ (sq_drop _ _ _ H1 Hx Hnx X) (sq_add _ _ _ H2 Hny Hy Y)).
    - (* only drops: reverse inclusion *)
      right; right; left. intros X Y. split.
      + intros H s HY. apply NNPP. intro HX. apply Hnu. exists X, Y, s. auto.
      + apply sq_all_down. exact (sq_drop _ _ _ H1 Hx Hnx).
    - (* only additions: inclusion *)
      right; left. intros X Y. split.
      + intros H s HX. apply NNPP. intro HY. apply Hnd. exists X, Y, s. auto.
      + apply sq_all_up. exact (sq_add _ _ _ H2 Hny Hy).
    - (* neither: equality *)
      left. intros X Y. split.
      + intros H s. split; intro Hs; apply NNPP; intro Hn.
        * apply Hnd. exists X, Y, s. auto.
        * apply Hnu. exists X, Y, s. auto.
      + intro Heq. apply (sq_ext X X X Y); [ intro; tauto | exact Heq | apply sq_refl ].
  Qed.

End Classification.

(* ==================================================================== *)
(** * From any specification monad to relational [bind]                   *)
(* ==================================================================== *)

Definition outcomes {S A} (m : stdivnd S A) (s : S) (r : A * S) : Prop :=
  unOptionT (runStateT m s) (Some r).

Definition leProg {S A} (sq : (S -> Prop) -> (S -> Prop) -> Prop)
  (m m' : stdivnd S A) : Prop :=
  forall r, sq (fun s => outcomes m s r) (fun s => outcomes m' s r).

Section Programs.
  Variable S : Type.
  Variable sq : (S -> Prop) -> (S -> Prop) -> Prop.
  Hypothesis sq_ext : forall X X' Y Y',
      sameSet X X' -> sameSet Y Y' -> sq X Y -> sq X' Y'.

  (** Every relation is realised by [progOfSt], and [bind] of programs
      denotes [bindRel], so continuation-monotonicity on programs is
      continuation-monotonicity on relations. *)
  Lemma bind_mono_k_of_prog
    (Hk : forall A (g : stdivnd S A) (k k' : A -> stdivnd S unit),
        (forall a, leProg sq (k a) (k' a)) -> leProg sq (g >>= k) (g >>= k')) :
    forall A (g : S -> A * S -> Prop) (k k' : A -> S -> unit * S -> Prop),
      (forall a, leRel sq (k a) (k' a)) -> leRel sq (bindRel g k) (bindRel g k').
  Proof.
    intros A g k k' Hkk r.
    assert (Hp : forall a, leProg sq (progOfSt (k a)) (progOfSt (k' a))).
    { intros a r'. refine (sq_ext _ _ _ _ _ _ (Hkk a r'));
        intro s; unfold outcomes; rewrite progOfSt_outcomes; reflexivity. }
    pose proof (Hk A (progOfSt g) _ _ Hp r) as Hb.
    assert (Hden : forall (K : A -> S -> unit * S -> Prop) s,
               outcomes (progOfSt g >>= fun a => progOfSt (K a)) s r
               <-> bindRel g K s r).
    { intros K s. unfold outcomes, bindRel. rewrite (outcomes_bind S).
      setoid_rewrite progOfSt_outcomes. reflexivity. }
    refine (sq_ext _ _ _ _ _ _ Hb); intro s; apply Hden.
  Qed.

  (** A specification monad [W] whose order, read back on observed programs,
      is outcome-local with set-order [sq]. *)
  Variable W : Type -> Type.
  Variable bndW : forall A B, W A -> (A -> W B) -> W B.
  Variable obs : forall A, stdivnd S A -> W A.
  Variable eqW : forall A, W A -> W A -> Prop.
  Variable ordW : forall A, W A -> W A -> Prop.
  Arguments bndW {A B}. Arguments obs {A}. Arguments eqW {A}. Arguments ordW {A}.

  Hypothesis Hmorph : forall A B (x : stdivnd S A) (f : A -> stdivnd S B),
      eqW (obs (x >>= f)) (bndW (obs x) (fun a => obs (f a))).
  Hypothesis eqW_sym : forall A (x y : W A), eqW x y -> eqW y x.
  Hypothesis ordW_eq : forall A (x y : W A), eqW x y -> ordW x y.
  Hypothesis ordW_trans : forall A (x y z : W A), ordW x y -> ordW y z -> ordW x z.
  Hypothesis ordW_bind_k : forall A B (x : W A) (k k' : A -> W B),
      (forall a, ordW (k a) (k' a)) -> ordW (bndW x k) (bndW x k').
  Hypothesis Hread : forall A (m m' : stdivnd S A),
      ordW (obs m) (obs m') <-> leProg sq m m'.

  Lemma prog_bind_mono_k :
    forall A (g : stdivnd S A) (k k' : A -> stdivnd S unit),
      (forall a, leProg sq (k a) (k' a)) -> leProg sq (g >>= k) (g >>= k').
  Proof.
    intros A g k k' Hkk. apply Hread.
    apply (ordW_trans _ _ _ _ (ordW_eq _ _ _ (Hmorph _ _ g k))).
    apply (ordW_trans _ _ _ _ (ordW_bind_k _ _ (obs g) _ _
                                 (fun a => proj2 (Hread _ _ _) (Hkk a)))).
    apply ordW_eq. apply eqW_sym. apply Hmorph.
  Qed.

End Programs.

(** Part 3, "only if": the order any specification monad induces on observed
    programs, if outcome-local, is equality, inclusion, reverse inclusion, or
    total. *)
Theorem classification_prog (S : Type)
  (S_dec : forall x y : S, {x = y} + {x <> y}) (s0 : S)
  (sq : (S -> Prop) -> (S -> Prop) -> Prop)
  (sq_refl : forall X, sq X X)
  (sq_trans : forall X Y Z, sq X Y -> sq Y Z -> sq X Z)
  (sq_ext : forall X X' Y Y', sameSet X X' -> sameSet Y Y' -> sq X Y -> sq X' Y')
  (W : Type -> Type)
  (bndW : forall A B, W A -> (A -> W B) -> W B)
  (obs : forall A, stdivnd S A -> W A)
  (eqW ordW : forall A, W A -> W A -> Prop)
  (Hmorph : forall A B (x : stdivnd S A) (f : A -> stdivnd S B),
      eqW _ (obs _ (x >>= f)) (bndW _ _ (obs _ x) (fun a => obs _ (f a))))
  (eqW_sym : forall A (x y : W A), eqW _ x y -> eqW _ y x)
  (ordW_eq : forall A (x y : W A), eqW _ x y -> ordW _ x y)
  (ordW_trans : forall A (x y z : W A), ordW _ x y -> ordW _ y z -> ordW _ x z)
  (ordW_bind_k : forall A B (x : W A) (k k' : A -> W B),
      (forall a, ordW _ (k a) (k' a)) -> ordW _ (bndW _ _ x k) (bndW _ _ x k'))
  (Hread : forall A (m m' : stdivnd S A),
      ordW _ (obs _ m) (obs _ m') <-> leProg sq m m') :
  (forall X Y, sq X Y <-> sameSet X Y)
  \/ (forall X Y, sq X Y <-> (forall s, X s -> Y s))
  \/ (forall X Y, sq X Y <-> (forall s, Y s -> X s))
  \/ (forall X Y, sq X Y).
Proof.
  apply (classification S S_dec s0 sq sq_refl sq_trans sq_ext).
  apply (bind_mono_k_of_prog S sq sq_ext).
  exact (prog_bind_mono_k S sq W bndW obs eqW ordW Hmorph eqW_sym ordW_eq
           ordW_trans ordW_bind_k Hread).
Qed.

(* ==================================================================== *)
(** * The four readings                                                   *)
(* ==================================================================== *)

Definition PhiASP  {S} (X P : S -> Prop) : Prop := exists s, P s /\ X s.
Definition PhiDSLP {S} (X P : S -> Prop) : Prop := forall s, X s -> P s.
Definition PhiDSP  {S} (X P : S -> Prop) : Prop := PhiASP X P /\ PhiDSLP X P.
Definition PhiASLP {S} (X P : S -> Prop) : Prop := PhiASP X P \/ PhiDSLP X P.

(** The [Φ]s are exactly what the four observations compute per outcome. *)
Lemma obsDSP_is_PhiDSP {S A} (m : stdivnd S A) pre r :
  getDSPSt (obsDSP m) pre r <-> PhiDSP (fun s => outcomes m s r) pre.
Proof. rewrite getProgDSP_obsDSP. reflexivity. Qed.

Lemma obsASLP_is_PhiASLP {S A} (m : stdivnd S A) pre r :
  getASLPSt (obsASLP m) pre r <-> PhiASLP (fun s => outcomes m s r) pre.
Proof. rewrite getProgASLP_obsASLP. reflexivity. Qed.

Section ReadOrders.
  Variable S : Type.
  Variable Φ : (S -> Prop) -> (S -> Prop) -> Prop.
  Hypothesis Φ_ext : forall X X' P, sameSet X X' -> Φ X P -> Φ X' P.

  Lemma readOrder_refl X : readOrder Φ X X.
  Proof. intros P H. exact H. Qed.

  Lemma readOrder_trans X Y Z :
    readOrder Φ X Y -> readOrder Φ Y Z -> readOrder Φ X Z.
  Proof. intros H1 H2 P H. exact (H2 P (H1 P H)). Qed.

  Lemma readOrder_ext X X' Y Y' :
    sameSet X X' -> sameSet Y Y' -> readOrder Φ X Y -> readOrder Φ X' Y'.
  Proof.
    intros HX HY H P HP.
    apply (Φ_ext Y); [ exact HY |]. apply H.
    apply (Φ_ext X'); [ intro s; symmetry; apply HX | exact HP ].
  Qed.
End ReadOrders.

Lemma readOrder_ASP_is_incl {S} (X Y : S -> Prop) :
  readOrder PhiASP X Y <-> (forall s, X s -> Y s).
Proof.
  unfold readOrder, PhiASP. split.
  - intros H s Hx. destruct (H (fun t => t = s) (ex_intro _ s (conj eq_refl Hx)))
      as [t [-> Hy]]. exact Hy.
  - intros H P [s [Hp Hx]]. exists s. exact (conj Hp (H s Hx)).
Qed.

Lemma readOrder_DSLP_is_rev_incl {S} (X Y : S -> Prop) :
  readOrder PhiDSLP X Y <-> (forall s, Y s -> X s).
Proof.
  unfold readOrder, PhiDSLP. split.
  - intros H s Hy. exact (H X (fun t Ht => Ht) s Hy).
  - intros H P HX s Hy. exact (HX s (H s Hy)).
Qed.

(** Mixed-ness is not the criterion: "exactly [P]" is neither monotone nor
    antitone, yet it induces equality. *)
Definition PhiExact {S} (X P : S -> Prop) : Prop := sameSet X P.

Lemma readOrder_exact_is_eq {S} (X Y : S -> Prop) :
  readOrder PhiExact X Y <-> sameSet X Y.
Proof.
  unfold readOrder, PhiExact, sameSet. split.
  - intros H s. symmetry. exact (H X (fun t => conj (fun h => h) (fun h => h)) s).
  - intros H P HX s. rewrite <- HX. symmetry. apply H.
Qed.

(** DSP: dropping a start state is allowed ([{0,1} ⊑ {0}]), but [{0} ⋢ ∅],
    so [sq_drop] refutes continuation-monotonicity. *)
Theorem DSP_order_not_bind_mono :
  ~ (forall A (g : nat -> A * nat -> Prop) (k k' : A -> nat -> unit * nat -> Prop),
        (forall a, leRel (readOrder PhiDSP) (k a) (k' a)) ->
        leRel (readOrder PhiDSP) (bindRel g k) (bindRel g k')).
Proof.
  intro Hk.
  assert (Hext : forall (X X' P : nat -> Prop), sameSet X X' -> PhiDSP X P -> PhiDSP X' P).
  { intros X X' P HX [[s [Hp Hx]] Hall]. split.
    - exists s. split; [ exact Hp | apply HX; exact Hx ].
    - intros t Ht. apply Hall. apply HX. exact Ht. }
  assert (H01 : readOrder PhiDSP (fun s => s = 0 \/ s = 1) (fun s => s = 0)).
  { intros P [_ Hall]. split.
    - exists 0. split; [ apply Hall; left; reflexivity | reflexivity ].
    - intros t ->. apply Hall. left. reflexivity. }
  pose proof (sq_drop nat Nat.eq_dec 0 (readOrder PhiDSP)
                (readOrder_refl _ _)
                (readOrder_ext _ _ Hext) Hk _ _ 1 H01
                (or_intror eq_refl) ltac:(discriminate) (fun s => s = 0)) as Hbad.
  destruct (Hbad (fun s => s = 0)) as [[s [_ []]] _].
  split.
  - exists 0. split; reflexivity.
  - intros t Ht. exact Ht.
Qed.

(** ASLP: adding a start state is allowed ([{0} ⊑ {0,1}]), but [∅ ⋢ {0}],
    so [sq_add] refutes continuation-monotonicity. *)
Theorem ASLP_order_not_bind_mono :
  ~ (forall A (g : nat -> A * nat -> Prop) (k k' : A -> nat -> unit * nat -> Prop),
        (forall a, leRel (readOrder PhiASLP) (k a) (k' a)) ->
        leRel (readOrder PhiASLP) (bindRel g k) (bindRel g k')).
Proof.
  intro Hk.
  assert (Hext : forall (X X' P : nat -> Prop), sameSet X X' -> PhiASLP X P -> PhiASLP X' P).
  { intros X X' P HX [[s [Hp Hx]] | Hall].
    - left. exists s. split; [ exact Hp | apply HX; exact Hx ].
    - right. intros t Ht. apply Hall. apply HX. exact Ht. }
  assert (H01 : readOrder PhiASLP (fun s => s = 0) (fun s => s = 0 \/ s = 1)).
  { intros P H. left. exists 0. split; [| left; reflexivity ].
    destruct H as [[s [Hp ->]] | Hall]; [ exact Hp | apply Hall; reflexivity ]. }
  pose proof (sq_add nat Nat.eq_dec 0 (readOrder PhiASLP)
                (readOrder_refl _ _)
                (readOrder_ext _ _ Hext) Hk _ _ 1 H01
                ltac:(discriminate) (or_intror eq_refl) (fun s => s = 0)) as Hbad.
  destruct (Hbad (fun _ => False) (or_intror (fun _ (h : False) => h)))
    as [[s [[] _]] | Hall].
  exact (Hall 0 eq_refl).
Qed.

(** Hence no specification monad at all -- any [W], any [bind], any effect
    observation -- has DSP's (resp. ASLP's) refinement order on programs. *)
Corollary no_spec_monad_with_DSP_order
  (W : Type -> Type) (bndW : forall A B, W A -> (A -> W B) -> W B)
  (obs : forall A, stdivnd nat A -> W A) (eqW ordW : forall A, W A -> W A -> Prop)
  (Hmorph : forall A B (x : stdivnd nat A) (f : A -> stdivnd nat B),
      eqW _ (obs _ (x >>= f)) (bndW _ _ (obs _ x) (fun a => obs _ (f a))))
  (eqW_sym : forall A (x y : W A), eqW _ x y -> eqW _ y x)
  (ordW_eq : forall A (x y : W A), eqW _ x y -> ordW _ x y)
  (ordW_trans : forall A (x y z : W A), ordW _ x y -> ordW _ y z -> ordW _ x z)
  (ordW_bind_k : forall A B (x : W A) (k k' : A -> W B),
      (forall a, ordW _ (k a) (k' a)) -> ordW _ (bndW _ _ x k) (bndW _ _ x k')) :
  ~ (forall A (m m' : stdivnd nat A),
        ordW _ (obs _ m) (obs _ m')
        <-> (forall pre r, getDSPSt (obsDSP m) pre r -> getDSPSt (obsDSP m') pre r)).
Proof.
  intro Hread. apply DSP_order_not_bind_mono.
  assert (Hext : forall (X X' Y Y' : nat -> Prop), sameSet X X' -> sameSet Y Y' ->
             readOrder PhiDSP X Y -> readOrder PhiDSP X' Y').
  { apply readOrder_ext. intros X X' P HX [[s [Hp Hx]] Hall]. split.
    - exists s. split; [ exact Hp | apply HX; exact Hx ].
    - intros t Ht. apply Hall. apply HX. exact Ht. }
  apply (bind_mono_k_of_prog nat _ Hext).
  apply (prog_bind_mono_k nat _ W bndW obs eqW ordW Hmorph eqW_sym ordW_eq
           ordW_trans ordW_bind_k).
  intros A m m'. rewrite Hread. unfold leProg, readOrder. split.
  - intros H r P H1. apply (proj1 (obsDSP_is_PhiDSP m' P r)). apply H.
    exact (proj2 (obsDSP_is_PhiDSP m P r) H1).
  - intros H P r H1. apply (proj2 (obsDSP_is_PhiDSP m' P r)). apply H.
    exact (proj1 (obsDSP_is_PhiDSP m P r) H1).
Qed.

Corollary no_spec_monad_with_ASLP_order
  (W : Type -> Type) (bndW : forall A B, W A -> (A -> W B) -> W B)
  (obs : forall A, stdivnd nat A -> W A) (eqW ordW : forall A, W A -> W A -> Prop)
  (Hmorph : forall A B (x : stdivnd nat A) (f : A -> stdivnd nat B),
      eqW _ (obs _ (x >>= f)) (bndW _ _ (obs _ x) (fun a => obs _ (f a))))
  (eqW_sym : forall A (x y : W A), eqW _ x y -> eqW _ y x)
  (ordW_eq : forall A (x y : W A), eqW _ x y -> ordW _ x y)
  (ordW_trans : forall A (x y z : W A), ordW _ x y -> ordW _ y z -> ordW _ x z)
  (ordW_bind_k : forall A B (x : W A) (k k' : A -> W B),
      (forall a, ordW _ (k a) (k' a)) -> ordW _ (bndW _ _ x k) (bndW _ _ x k')) :
  ~ (forall A (m m' : stdivnd nat A),
        ordW _ (obs _ m) (obs _ m')
        <-> (forall pre r, getASLPSt (obsASLP m) pre r -> getASLPSt (obsASLP m') pre r)).
Proof.
  intro Hread. apply ASLP_order_not_bind_mono.
  assert (Hext : forall (X X' Y Y' : nat -> Prop), sameSet X X' -> sameSet Y Y' ->
             readOrder PhiASLP X Y -> readOrder PhiASLP X' Y').
  { apply readOrder_ext. intros X X' P HX [[s [Hp Hx]] | Hall].
    - left. exists s. split; [ exact Hp | apply HX; exact Hx ].
    - right. intros t Ht. apply Hall. apply HX. exact Ht. }
  apply (bind_mono_k_of_prog nat _ Hext).
  apply (prog_bind_mono_k nat _ W bndW obs eqW ordW Hmorph eqW_sym ordW_eq
           ordW_trans ordW_bind_k).
  intros A m m'. rewrite Hread. unfold leProg, readOrder. split.
  - intros H r P H1. apply (proj1 (obsASLP_is_PhiASLP m' P r)). apply H.
    exact (proj2 (obsASLP_is_PhiASLP m P r) H1).
  - intros H P r H1. apply (proj2 (obsASLP_is_PhiASLP m' P r)). apply H.
    exact (proj1 (obsASLP_is_PhiASLP m P r) H1).
Qed.
