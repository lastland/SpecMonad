(** * Classes separated by a context have no realised index.

    Carving out a class [T] of computations in DM fashion means finding an
    index [w] with [T m <-> w <= obs m].  In any ordered specification monad
    such a class is closed under CONTEXT TRANSFER: if [w] is realised by some
    [m_w] ([obs m_w ≡ w]) and [C] is a context [g ;; _ ;; h], then

      [T (C m_w) -> T y -> T (C y)]                    ([fibre_transfer]),

    because [obs m_w ≤ obs y] and the order is a congruence for [bind].

    [no_realised_index]: if every member [x] of [T] has a context [C] and a
    member [y] with [T (C x)] but not [T (C y)], no realised index carves out
    [T], in either direction ([no_realised_index_D]).  The theorem is generic
    in the computation monad, the specification monad, [bind] and the order.

    Existential triples.  O'Hearn's triple [[P] m [Q]],

      [forall r, Q r -> exists s, P s /\ m reaches r from s],

    is separated ([IL_separated]) whenever [Q] is inhabited and [P] has a
    state other than any given one.  The context is
    [assume s ;; _ ;; spread], where:
    - [assume s] keeps only the start state [s] from which [x] reaches [Q];
    - [spread] sends any [Q]-outcome to every [Q]-outcome.
    [x] survives the context and a member that reaches [Q] only from another
    [P]-state does not.  Every ASP index is realised ([obsASP_progOfASPSt]),
    so [no_asp_IL_index] rules out every index, for every [bind] making
    [obsASP] a morphism and every order compatible with it.  This generalises
    [no_ordered_asp_under_index_bnd] ([ASPUnderObstructions.v]) from one fixed
    triple to all of them.  That theorem needs only continuation
    monotonicity; the general [Q] needs both arguments, because [spread]
    follows the hole.

    Where the hypotheses are needed.
    - A singleton [P] is excluded: [[{p}] m [Q]] is [aspRel]-inclusion of
      [{p} × Q], a genuine ASP/[Over]-style fibre.
    - An empty [Q] makes the triple trivially true, so it is excluded too.
    - Realisation is needed: in a spec monad larger than the image of [obs],
      an unrealised index escapes the argument.  In ASP every index is
      realised. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Coq Require Import RelationClasses.
From Incorrectness.Classes Require Import OrderedMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPArrowCore ASPArrowRel ASPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import StDivNonDet_SPSt_Arrow.
From Incorrectness.Taxonomy.DijkstraMonads Require Import ASPUnderObstructions.

Import MonadNotation.
Open Scope monad_scope.

Section ContextTransfer.
  Context {M : Type -> Type} {HM : Monad M}.
  Variable W : Type -> Type.
  Variable bndW : forall A B, W A -> (A -> W B) -> W B.
  Variable obs : forall A, M A -> W A.
  Variable eqW : forall A, W A -> W A -> Prop.
  Variable ord : forall A, W A -> W A -> Prop.
  Arguments bndW {A B}. Arguments obs {A}. Arguments eqW {A}. Arguments ord {A}.

  Hypothesis Hmorph : forall A B (x : M A) (f : A -> M B),
      eqW (obs (bind x f)) (bndW (obs x) (fun a => obs (f a))).
  Hypothesis eqW_sym : forall A (x y : W A), eqW x y -> eqW y x.
  Hypothesis ord_eq : forall A (x y : W A), eqW x y -> ord x y.
  Hypothesis ord_trans : forall A (x y z : W A), ord x y -> ord y z -> ord x z.
  Hypothesis ord_bind_m : forall A B (x x' : W A) (k : A -> W B),
      ord x x' -> ord (bndW x k) (bndW x' k).
  Hypothesis ord_bind_k : forall A B (x : W A) (k k' : A -> W B),
      (forall a, ord (k a) (k' a)) -> ord (bndW x k) (bndW x k').

  Definition ctx {U A B} (g : M U) (h : A -> M B) (x : M A) : M B :=
    bind g (fun _ => bind x h).

  Lemma ctx_mono {U A B} (g : M U) (h : A -> M B) (x y : M A) :
    ord (obs x) (obs y) -> ord (obs (ctx g h x)) (obs (ctx g h y)).
  Proof.
    intro Hxy. unfold ctx.
    assert (Hk : ord (obs (bind x h)) (obs (bind y h))).
    { apply (ord_trans _ _ _ _ (ord_eq _ _ _ (Hmorph _ _ x h))).
      apply (ord_trans _ _ _ _ (ord_bind_m _ _ _ _ _ Hxy)).
      apply ord_eq, eqW_sym, Hmorph. }
    apply (ord_trans _ _ _ _ (ord_eq _ _ _ (Hmorph _ _ g _))).
    apply (ord_trans _ _ _ _ (ord_bind_k _ _ (obs g) _ (fun _ => obs (bind y h))
                                (fun _ => Hk))).
    apply ord_eq, eqW_sym, Hmorph.
  Qed.

  Lemma fibre_transfer {A B U} (T : M A -> Prop) (TB : M B -> Prop)
    (w : W A) (wB : W B)
    (Hfib : forall m, ord w (obs m) <-> T m)
    (HfibB : forall m, ord wB (obs m) <-> TB m)
    (mw : M A) (Hw : eqW (obs mw) w) (g : M U) (h : A -> M B) (y : M A) :
    TB (ctx g h mw) -> T y -> TB (ctx g h y).
  Proof.
    intros Hc Hy. apply HfibB.
    apply (ord_trans _ _ _ _ (proj2 (HfibB _) Hc)). apply ctx_mono.
    exact (ord_trans _ _ _ _ (ord_eq _ _ _ Hw) (proj2 (Hfib _) Hy)).
  Qed.

  Theorem no_realised_index {A} (T : M A -> Prop)
    (Hsep : forall x, T x -> exists U (g : M U) (h : A -> M A) (y : M A),
          T (ctx g h x) /\ T y /\ ~ T (ctx g h y)) :
    ~ exists (w : W A) (mw : M A),
        eqW (obs mw) w /\ forall m, ord w (obs m) <-> T m.
  Proof.
    intros [w [mw [Hw Hfib]]].
    assert (Hmw : T mw) by (apply Hfib, ord_eq, eqW_sym, Hw).
    destruct (Hsep mw Hmw) as [U [g [h [y [Hc [Hy Hn]]]]]].
    exact (Hn (fibre_transfer T T w w Hfib Hfib mw Hw g h y Hc Hy)).
  Qed.

End ContextTransfer.

(** The down-set direction is the same theorem for the opposite order. *)
Corollary no_realised_index_D {M} {HM : Monad M}
  (W : Type -> Type) (bndW : forall A B, W A -> (A -> W B) -> W B)
  (obs : forall A, M A -> W A) (eqW ord : forall A, W A -> W A -> Prop)
  (Hmorph : forall A B (x : M A) (f : A -> M B),
      eqW _ (obs _ (bind x f)) (bndW _ _ (obs _ x) (fun a => obs _ (f a))))
  (eqW_sym : forall A (x y : W A), eqW _ x y -> eqW _ y x)
  (ord_eq : forall A (x y : W A), eqW _ x y -> ord _ x y)
  (ord_trans : forall A (x y z : W A), ord _ x y -> ord _ y z -> ord _ x z)
  (ord_bind_m : forall A B (x x' : W A) (k : A -> W B),
      ord _ x x' -> ord _ (bndW _ _ x k) (bndW _ _ x' k))
  (ord_bind_k : forall A B (x : W A) (k k' : A -> W B),
      (forall a, ord _ (k a) (k' a)) -> ord _ (bndW _ _ x k) (bndW _ _ x k'))
  {A} (T : M A -> Prop)
  (Hsep : forall x, T x -> exists U (g : M U) (h : A -> M A) (y : M A),
        T (ctx g h x) /\ T y /\ ~ T (ctx g h y)) :
  ~ exists (w : W A) (mw : M A),
      eqW _ (obs _ mw) w /\ forall m, ord _ (obs _ m) w <-> T m.
Proof.
  apply (no_realised_index W bndW obs eqW (fun A x y => ord A y x) Hmorph eqW_sym).
  - intros B x y H. apply ord_eq, eqW_sym, H.
  - intros B x y z H1 H2. exact (ord_trans _ _ _ _ H2 H1).
  - intros B C x x' k H. exact (ord_bind_m _ _ _ _ k H).
  - intros B C x k k' H. exact (ord_bind_k _ _ x _ _ H).
  - exact Hsep.
Qed.

(* ==================================================================== *)
(** * Incorrectness triples are separated                                 *)
(* ==================================================================== *)

Section IL.
  Variable S : Type.

  Definition ILtriple {A} (P : S -> Prop) (Q : A * S -> Prop) (m : stdivnd S A) : Prop :=
    tripleASP m Under P Q.

  Lemma ILtriple_iff {A} P Q (m : stdivnd S A) :
    ILtriple P Q m
    <-> (forall r, Q r -> exists s, P s /\ unOptionT (runStateT m s) (Some r)).
  Proof.
    unfold ILtriple, tripleASP. split; intros H r Hq.
    - exact (proj1 (getProgASP_obsASP S m P r) (H r Hq)).
    - exact (proj2 (getProgASP_obsASP S m P r) (H r Hq)).
  Qed.

  (** [assumeSt s] continues only from [s], leaving the state unchanged. *)
  Definition assumeSt (s : S) : stdivnd S unit :=
    progOfSt (fun t r => t = s /\ r = (tt, t)).

  (** [spread Q] sends any [Q]-outcome to every [Q]-outcome. *)
  Definition spread {A} (Q : A * S -> Prop) (a : A) : stdivnd S A :=
    progOfSt (fun s r => Q (a, s) /\ Q r).

  Lemma ctx_outcomes {A} (s : S) (Q : A * S -> Prop) (x : stdivnd S A) p r :
    unOptionT (runStateT (ctx (assumeSt s) (spread Q) x) p) (Some r)
    <-> p = s /\ (exists q, Q q /\ unOptionT (runStateT x s) (Some q)) /\ Q r.
  Proof.
    unfold ctx. rewrite (outcomes_bind S). split.
    - intros [[] [p' [Ha Hk]]].
      apply progOfSt_outcomes in Ha. destruct Ha as [-> Heq].
      injection Heq as ->.
      apply (outcomes_bind S) in Hk. destruct Hk as [a [s' [Hx Hh]]].
      apply progOfSt_outcomes in Hh. destruct Hh as [Hq Hr].
      split; [ reflexivity | split; [ exists (a, s'); exact (conj Hq Hx) | exact Hr ] ].
    - intros [-> [[[a s'] [Hq Hx]] Hr]]. exists tt, s. split.
      + apply progOfSt_outcomes. split; reflexivity.
      + apply (outcomes_bind S). exists a, s'. split; [ exact Hx |].
        apply progOfSt_outcomes. exact (conj Hq Hr).
  Qed.

  Theorem IL_separated {A} (P : S -> Prop) (Q : A * S -> Prop)
    (HQ : exists q, Q q) (HP : forall s, exists s', P s' /\ s' <> s) :
    forall x, ILtriple P Q x ->
      exists U (g : stdivnd S U) (h : A -> stdivnd S A) (y : stdivnd S A),
        ILtriple P Q (ctx g h x) /\ ILtriple P Q y /\ ~ ILtriple P Q (ctx g h y).
  Proof.
    intros x Hx. destruct HQ as [q Hq].
    destruct (proj1 (ILtriple_iff P Q x) Hx q Hq) as [s [Hs Hxs]].
    destruct (HP s) as [s' [Hs' Hne]].
    set (y := progOfSt (fun t r => t = s' /\ Q r) : stdivnd S A).
    exists unit, (assumeSt s), (spread Q), y. split; [| split ].
    - apply ILtriple_iff. intros r Hr. exists s. split; [ exact Hs |].
      apply ctx_outcomes. split; [ reflexivity |].
      split; [ exists q; exact (conj Hq Hxs) | exact Hr ].
    - apply ILtriple_iff. intros r Hr. exists s'. split; [ exact Hs' |].
      apply progOfSt_outcomes. exact (conj eq_refl Hr).
    - intro Hc. destruct (proj1 (ILtriple_iff P Q _) Hc q Hq) as [p [_ Hp]].
      apply ctx_outcomes in Hp. destruct Hp as [_ [[q' [_ Hy]] _]].
      apply progOfSt_outcomes in Hy. destruct Hy as [Heq _].
      exact (Hne (eq_sym Heq)).
  Qed.

  (** Two distinct precondition states and decidable equality suffice. *)
  Lemma two_states_sep (S_dec : forall x y : S, x = y \/ x <> y)
    (P : S -> Prop) p1 p2 (H1 : P p1) (H2 : P p2) (Hne : p1 <> p2) :
    forall s, exists s', P s' /\ s' <> s.
  Proof.
    intro s. destruct (S_dec s p1) as [-> | Hs].
    - exists p2. split; [ exact H2 | intro H; exact (Hne (eq_sym H)) ].
    - exists p1. split; [ exact H1 | intro H; exact (Hs (eq_sym H)) ].
  Qed.

  (** Every element of [ASPSt S A] is the observation of a program. *)
  Definition progOfASPSt {A} (w : ASPSt S A) : stdivnd S A :=
    progOfSt (fun s r => aspRel w (tt, s) r).

  Lemma obsASP_progOfASPSt {A} (w : ASPSt S A) : eq1 (obsASP (progOfASPSt w)) w.
  Proof.
    apply (proj2 (eq1_ASPSt_get _ _ _)). intros pre r. split; intro H.
    - apply getProgASP_obsASP in H. destruct H as [s [Hp Hr]].
      apply progOfSt_outcomes in Hr.
      unfold getASPSt. apply get_aspRel. exists (tt, s). split; [ exact Hp | exact Hr ].
    - unfold getASPSt in H. apply get_aspRel in H. destruct H as [[[] s] [Hp Hr]].
      apply getProgASP_obsASP. exists s. split; [ exact Hp |].
      apply progOfSt_outcomes. exact Hr.
  Qed.

  Lemma eq1_ASPSt_symm {A} (x y : ASPSt S A) : eq1 x y -> eq1 y x.
  Proof.
    intro H. apply (proj2 (eq1_ASPSt_get _ _ _)). intros pre r.
    symmetry. exact (proj1 (eq1_ASPSt_get _ _ _) H pre r).
  Qed.

End IL.

(** No index carves out an incorrectness triple, in either direction, for
    ANY [bind] that makes [obsASP] a monad morphism and ANY order that
    contains [eq1] and makes that [bind] monotone. *)
Theorem no_asp_IL_index_bnd (S : Type)
  (bnd : forall A B, ASPSt S A -> (A -> ASPSt S B) -> ASPSt S B)
  (Hmorph : forall A B (x : stdivnd S A) (f : A -> stdivnd S B),
      eq1 (obsASP (bind x f)) (bnd _ _ (obsASP x) (fun a => obsASP (f a))))
  (ord : forall A, ASPSt S A -> ASPSt S A -> Prop)
  (ord_eq : forall A (x y : ASPSt S A), eq1 x y -> ord _ x y)
  (ord_trans : forall A (x y z : ASPSt S A), ord _ x y -> ord _ y z -> ord _ x z)
  (ord_bind_m : forall A B (x x' : ASPSt S A) (k : A -> ASPSt S B),
      ord _ x x' -> ord _ (bnd _ _ x k) (bnd _ _ x' k))
  (ord_bind_k : forall A B (x : ASPSt S A) (k k' : A -> ASPSt S B),
      (forall a, ord _ (k a) (k' a)) -> ord _ (bnd _ _ x k) (bnd _ _ x k'))
  {A} (P : S -> Prop) (Q : A * S -> Prop)
  (HQ : exists q, Q q) (HP : forall s, exists s', P s' /\ s' <> s) :
  (~ exists w, forall prog, ord _ w (obsASP prog) <-> tripleASP prog Under P Q)
  /\ (~ exists w, forall prog, ord _ (obsASP prog) w <-> tripleASP prog Under P Q).
Proof.
  split; intros [w Hfib].
  - apply (no_realised_index (ASPSt S) bnd (@obsASP S) (fun A => eq1) ord
             Hmorph (@eq1_ASPSt_symm S) ord_eq ord_trans ord_bind_m ord_bind_k
             (ILtriple S P Q) (IL_separated S P Q HQ HP)).
    exists w, (progOfASPSt S w). exact (conj (obsASP_progOfASPSt S w) Hfib).
  - apply (no_realised_index_D (ASPSt S) bnd (@obsASP S) (fun A => eq1) ord
             Hmorph (@eq1_ASPSt_symm S) ord_eq ord_trans ord_bind_m ord_bind_k
             (ILtriple S P Q) (IL_separated S P Q HQ HP)).
    exists w, (progOfASPSt S w). exact (conj (obsASP_progOfASPSt S w) Hfib).
Qed.

(** In particular, no specification-monad order on [ASPSt S] works. *)
Corollary no_asp_IL_index_any_order (S : Type)
  (le : forall A, ASPSt S A -> ASPSt S A -> Prop)
  (OM : OrderedMonad (ASPSt S) le)
  {A} (P : S -> Prop) (Q : A * S -> Prop)
  (HQ : exists q, Q q) (HP : forall s, exists s', P s' /\ s' <> s) :
  (~ exists w, forall prog, le _ w (obsASP prog) <-> tripleASP prog Under P Q)
  /\ (~ exists w, forall prog, le _ (obsASP prog) w <-> tripleASP prog Under P Q).
Proof.
  pose proof (fun B => @om_preorder _ _ _ le OM B) as HP'.
  apply (no_asp_IL_index_bnd S (fun _ _ => bind) (fun _ _ x f => obsASP_bind S x f) le).
  - exact (@om_eq1 _ _ _ le OM).
  - intros B x y z H1 H2. exact (@PreOrder_Transitive _ _ (HP' B) x y z H1 H2).
  - intros B C x x' k H.
    exact (@om_bind _ _ _ le OM B C x x' H k k (fun a => @PreOrder_Reflexive _ _ (HP' C) (k a))).
  - intros B C x k k' H.
    exact (@om_bind _ _ _ le OM B C x x (@PreOrder_Reflexive _ _ (HP' B) x) k k' H).
  - exact HQ.
  - exact HP.
Qed.
