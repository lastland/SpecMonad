(** * Triples as typings in the Dijkstra monads (paper, Section 6)

    The Dijkstra monads of [DijkstraMonads/DijkstraMonad.v] and the triples
    of [Triples/] are both read off the same monad morphisms; this file
    compares them.

    Triples are typings where the two say the same: a WP [Under] triple is
    a typing in [DM] and a WP [Over] triple one in [DMop], for all four WP
    readings, which is eight WP Dijkstra monads; ASP [Over] is a typing in
    [DM] and DSLP [Under] one in [DMop].

    The last part is about the two SP kinds that are left.  An ASP [Under]
    triple asks, for each result, for SOME start state that reaches it; a
    typing compares at every precondition, so it speaks of EVERY start
    state.  No index has the ASP [Under] triple as its typings
    ([no_asp_under_index]), nor the DSLP [Over] triple
    ([no_dslp_over_index]).  Without state there is one start point, the two
    readings agree, and the triple is a typing ([triple_under_aspPure]). *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow ArrowMonad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Verification.Computation Require Import
  DivNonDetNE.
From Incorrectness.Relational Require Import Rel.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Verification.Triples Require Import Triple.
From Incorrectness.Verification.MonadMorphisms Require Import MonadMorphisms.
From Incorrectness.Verification.DijkstraMonads Require Import DijkstraMonad.

(* ================================================================= *)
(** * Triples are typings                                             *)
(* ================================================================= *)

(** ** WP

    The index of a pre- and a postcondition, at the base and lifted start
    state by start state.  [wpUnder] is the least transformer that takes
    the postcondition into the precondition, [wpOver] the greatest one
    whose value at the postcondition is within the precondition. *)

Lemma wpUnder_mono {A} (pre : Prop) (post : A -> Prop) :
  wpure_mono (fun p : A -> Prop => pre /\ forall a, post a -> p a).
Proof.
  intros p q Hpq [Hpre Hsub]. split; [ exact Hpre |].
  intros a Ha. exact (Hpq a (Hsub a Ha)).
Qed.

Lemma wpOver_mono {A} (pre : Prop) (post : A -> Prop) :
  wpure_mono (fun p : A -> Prop => (forall a, p a -> post a) -> pre).
Proof.
  intros p q Hpq H Hsub. apply H. intros a Ha. exact (Hsub a (Hpq a Ha)).
Qed.

Definition wpUnderPure {A} (pre : Prop) (post : A -> Prop) : WPure A :=
  mkWPure _ (wpUnder_mono pre post).

Definition wpOverPure {A} (pre : Prop) (post : A -> Prop) : WPure A :=
  mkWPure _ (wpOver_mono pre post).

Definition wpUnderSt {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A := mkStateT (fun s => wpUnderPure (pre s) post).

Definition wpOverSt {S A} (pre : S -> Prop) (post : A * S -> Prop)
  : WSt S A := mkStateT (fun s => wpOverPure (pre s) post).

Definition wpUnderStExc {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : WStExc S A := mkStateT (fun s => mkOptionT (wpUnderPure (pre s) post)).

Definition wpOverStExc {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  : WStExc S A := mkStateT (fun s => mkOptionT (wpOverPure (pre s) post)).

Lemma le_wpUnderPure {A} (w : WPure A) (pre : Prop) (post : A -> Prop) :
  (pre -> getWPure w post) <-> WP_le w (wpUnderPure pre post).
Proof.
  split.
  - intros H k [Hpre Hsub]. exact (getWPure_mono w post k Hsub (H Hpre)).
  - intros H Hpre. exact (H post (conj Hpre (fun a Ha => Ha))).
Qed.

Lemma le_wpOverPure {A} (w : WPure A) (pre : Prop) (post : A -> Prop) :
  (getWPure w post -> pre) <-> WP_le (wpOverPure pre post) w.
Proof.
  split.
  - intros H k Hk Hsub. exact (H (getWPure_mono w k post Hsub Hk)).
  - intros H Hw. exact (H post Hw (fun a Ha => Ha)).
Qed.

(** For any morphism into the three WP monads, so for all four readings:
    an [Under] triple is a typing in [DM] at [wpUnder], an [Over] triple a
    typing in [DMop] at [wpOver]. *)
Section WPTypings.
  Context {M : Type -> Type}.

  Theorem triple_under_wpPure (θ : forall A, M A -> WPure A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Under pre post
    <-> WP_le (θ A m) (wpUnderPure (pre tt) post).
  Proof.
    etransitivity; [| exact (le_wpUnderPure (θ A m) (pre tt) post) ].
    split; [ intros H Hp; exact (H tt Hp) | intros H [] Hp; exact (H Hp) ].
  Qed.

  Theorem triple_over_wpPure (θ : forall A, M A -> WPure A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Over pre post
    <-> WP_le (wpOverPure (pre tt) post) (θ A m).
  Proof.
    etransitivity; [| exact (le_wpOverPure (θ A m) (pre tt) post) ].
    split; [ intros H Hw; exact (H tt Hw) | intros H [] Hw; exact (H Hw) ].
  Qed.

  Context {S : Type}.

  Theorem triple_under_wpSt (θ : forall A, M A -> WSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Under pre post <-> ordWSt (θ A m) (wpUnderSt pre post).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpUnderPure (runStateT (θ A m) s) (pre s) post) (H s)).
    - exact (proj2 (le_wpUnderPure (runStateT (θ A m) s) (pre s) post) (H s)).
  Qed.

  Theorem triple_over_wpSt (θ : forall A, M A -> WSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Over pre post <-> ordWSt (wpOverSt pre post) (θ A m).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpOverPure (runStateT (θ A m) s) (pre s) post) (H s)).
    - exact (proj2 (le_wpOverPure (runStateT (θ A m) s) (pre s) post) (H s)).
  Qed.

  Theorem triple_under_wpStExc (θ : forall A, M A -> WStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Under pre post <-> ordWStExc (θ A m) (wpUnderStExc pre post).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpUnderPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
    - exact (proj2 (le_wpUnderPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
  Qed.

  Theorem triple_over_wpStExc (θ : forall A, M A -> WStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Over pre post <-> ordWStExc (wpOverStExc pre post) (θ A m).
  Proof.
    split; intros H s.
    - exact (proj1 (le_wpOverPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
    - exact (proj2 (le_wpOverPure (unOptionT (runStateT (θ A m) s))
                      (pre s) post) (H s)).
  Qed.
End WPTypings.

(** ** SP

    The index of a pre- and a postcondition is the arrow of a relation, at
    any pair of indices: for ASP [Over], the relation that sends a start
    point in the precondition into the postcondition; for DSLP [Under], the
    one that sends into the postcondition only from the precondition.  The
    three levels are this one statement at three pairs of indices.

    The other SP kinds are not typings in these orders: an ASP [Under]
    triple asks for some start point per result, while the order compares
    at every precondition. *)

Definition aspOver {X Y} (P : X -> Prop) (Q : Y -> Prop) : ASPArr X Y :=
  relASP (fun x y => P x -> Q y).

Definition dslpUnder {X Y} (P : X -> Prop) (Q : Y -> Prop) : DSLPArr X Y :=
  relDSLP (fun x y => Q y -> P x).

Lemma le_aspOver {X Y} (w : ASPArr X Y) (P : X -> Prop) (Q : Y -> Prop) :
  (forall y, getASPArr w P y -> Q y)
  <-> (forall P' y, getASPArr w P' y -> getASPArr (aspOver P Q) P' y).
Proof.
  split.
  - intros H P' y Hw.
    destruct (proj1 (get_aspRel w P' y) Hw) as [x [Hx Hr]].
    exists x. split; [ exact Hx |]. intro HP. apply H.
    exact (proj2 (get_aspRel w P y) (ex_intro _ x (conj HP Hr))).
  - intros H y Hw. destruct (H P y Hw) as [x [HP HQ]]. exact (HQ HP).
Qed.

Lemma le_dslpUnder {X Y} (w : DSLPArr X Y) (P : X -> Prop) (Q : Y -> Prop) :
  (forall y, Q y -> getDSLPArr w P y)
  <-> (forall P' y, getDSLPArr (dslpUnder P Q) P' y -> getDSLPArr w P' y).
Proof.
  split.
  - intros H P' y Ht. apply (proj2 (get_dslpRel w P' y)). intros x Hr.
    refine (Ht x _). intro HQ.
    exact (proj1 (get_dslpRel w P y) (H y HQ) x Hr).
  - intros H y HQ. apply (H P y). intros x Hx. exact (Hx HQ).
Qed.

Section SPTypings.
  Context {M : Type -> Type}.

  Theorem triple_over_aspPure (θ : forall A, M A -> ASP A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Over pre post <-> ordASP (θ A m) (aspOver pre post).
  Proof. exact (le_aspOver (θ A m) pre post). Qed.

  Theorem triple_under_dslpPure (θ : forall A, M A -> DSLP A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : unit -> Prop) (post : A -> Prop) :
    triple θ m Under pre post <-> ordDSLP (dslpUnder pre post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) pre post). Qed.

  Context {S : Type}.

  Theorem triple_over_aspSt (θ : forall A, M A -> ASPSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Over pre post
    <-> ordASPSt (θ A m) (aspOver (fun p : unit * S => pre (snd p)) post).
  Proof. exact (le_aspOver (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_under_dslpSt (θ : forall A, M A -> DSLPSt S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : A * S -> Prop) :
    triple θ m Under pre post
    <-> ordDSLPSt (dslpUnder (fun p : unit * S => pre (snd p)) post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_over_aspStExc (θ : forall A, M A -> ASPStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Over pre post
    <-> ordASPStExc (θ A m)
          (aspOver (fun p : unit * S => pre (snd p)) post).
  Proof. exact (le_aspOver (θ A m) (fun p => pre (snd p)) post). Qed.

  Theorem triple_under_dslpStExc (θ : forall A, M A -> DSLPStExc S A)
    {Hθ : IsMonadMorphism θ} {A} (m : M A)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
    triple θ m Under pre post
    <-> ordDSLPStExc
          (dslpUnder (fun p : unit * S => pre (snd p)) post) (θ A m).
  Proof. exact (le_dslpUnder (θ A m) (fun p => pre (snd p)) post). Qed.
End SPTypings.

(* ================================================================= *)
(** * ASP [Under] and DSLP [Over] are not typings                     *)
(* ================================================================= *)

(** ** A typing is an inclusion of relations

    Whatever the index, a typing in [DMop] for ASP, and one in [DM] for
    DSLP, says that the relation the index denotes is included in the
    relation of the computation: the order leaves nothing else to look
    at. *)

Lemma le_relASP {X Y} (w : ASPArr X Y) (R : X -> Y -> Prop) :
  (forall P y, getASPArr w P y -> getASPArr (relASP R) P y)
  <-> (forall x y, aspRel w x y -> R x y).
Proof.
  split.
  - intros H x y Hw.
    destruct (H (fun z => z = x) y Hw) as [x' [E Hr]]. subst x'. exact Hr.
  - intros H P y Hw. destruct (proj1 (get_aspRel w P y) Hw) as [x [Hp Hr]].
    exists x. exact (conj Hp (H x y Hr)).
Qed.

Lemma relDSLP_le {X Y} (R : X -> Y -> Prop) (w : DSLPArr X Y) :
  (forall P y, getDSLPArr (relDSLP R) P y -> getDSLPArr w P y)
  <-> (forall x y, dslpRel w x y -> R x y).
Proof.
  split.
  - intros H x y Hw.
    exact (proj1 (get_dslpRel w (fun x' => R x' y) y)
             (H (fun x' => R x' y) y (fun a Ha => Ha)) x Hw).
  - intros H P y Ht. apply (proj2 (get_dslpRel w P y)).
    intros x Hr. exact (Ht x (H x y Hr)).
Qed.

(** ** The indices one would like to use

    For ASP [Under], the arrow of the relation between the precondition and
    the postcondition; for DSLP [Over], that between their complements. *)

Definition aspUnder {X Y} (P : X -> Prop) (Q : Y -> Prop) : ASPArr X Y :=
  relASP (fun x y => P x /\ Q y).

Definition dslpOver {X Y} (P : X -> Prop) (Q : Y -> Prop) : DSLPArr X Y :=
  relDSLP (fun x y => ~ P x /\ ~ Q y).

(** A typing at these indices says that EVERY start point in the
    precondition reaches EVERY result in the postcondition (for DSLP: every
    start point outside reaches every result outside). *)
Lemma le_aspUnder {X Y} (P : X -> Prop) (Q : Y -> Prop) (R : X -> Y -> Prop) :
  (forall P' y, getASPArr (aspUnder P Q) P' y -> getASPArr (relASP R) P' y)
  <-> (forall x y, P x -> Q y -> R x y).
Proof.
  etransitivity; [ exact (le_relASP (aspUnder P Q) R) |].
  split.
  - intros H x y HP HQ.
    exact (H x y (proj2 (aspRel_ofRel (fun x y => P x /\ Q y) x y)
                    (conj HP HQ))).
  - intros H x y Hw.
    destruct (proj1 (aspRel_ofRel (fun x y => P x /\ Q y) x y) Hw) as [HP HQ].
    exact (H x y HP HQ).
Qed.

Lemma dslpOver_le {X Y} (P : X -> Prop) (Q : Y -> Prop) (R : X -> Y -> Prop) :
  (forall P' y, getDSLPArr (relDSLP R) P' y -> getDSLPArr (dslpOver P Q) P' y)
  <-> (forall x y, ~ P x -> ~ Q y -> R x y).
Proof.
  etransitivity; [ exact (relDSLP_le R (dslpOver P Q)) |].
  split.
  - intros H x y HP HQ.
    exact (H x y (proj2 (dslpRel_ofRel (fun x y => ~ P x /\ ~ Q y) x y)
                    (conj HP HQ))).
  - intros H x y Hw.
    destruct (proj1 (dslpRel_ofRel (fun x y => ~ P x /\ ~ Q y) x y) Hw)
      as [HP HQ].
    exact (H x y HP HQ).
Qed.

(** That is stronger than the triple, which asks for SOME start point per
    result.  The typing gives the triple as soon as the precondition (for
    DSLP: its complement) is inhabited; the converse fails. *)
Lemma aspUnder_typing_triple {X Y} (P : X -> Prop) (Q : Y -> Prop)
  (R : X -> Y -> Prop) :
  (exists x, P x) -> (forall x y, P x -> Q y -> R x y) ->
  forall y, Q y -> getASPArr (relASP R) P y.
Proof. intros [x HP] H y HQ. exists x. exact (conj HP (H x y HP HQ)). Qed.

Lemma dslpOver_typing_triple {X Y} (P : X -> Prop) (Q : Y -> Prop)
  (R : X -> Y -> Prop) :
  (exists x, ~ P x) -> (forall x y, ~ P x -> ~ Q y -> R x y) ->
  forall y, getDSLPArr (relDSLP R) P y -> Q y.
Proof.
  intros [x HP] H y Hd. apply NNPP. intro HQ.
  exact (HP (Hd x (H x y HP HQ))).
Qed.

(** ** No index at all

    A computation with a prescribed relation between start states and
    results, which may also diverge. *)
Definition progOf {S A} (R : S -> A * S -> Prop) : stdivndNE S A :=
  mkStateT (fun s =>
    exist _
      (@mkOptionT SetM _
         (fun o : option (A * S) =>
            match o with Some r => R s r | None => True end))
      (ex_intro _ None I)).

Lemma progOf_out {S A} (R : S -> A * S -> Prop) (s : S) (r : A * S) :
  outSt (progOf R) s (Some r) <-> R s r.
Proof. reflexivity. Qed.

(** The typings with state, as inclusions into the outcomes. *)
Lemma aspSt_typing_op {S A} (w : ASPSt S A) (m : stdivndNE S A) :
  ordASPSt w (aspSt m)
  <-> (forall s r, aspRel w (tt, s) r -> outSt m s (Some r)).
Proof.
  etransitivity;
    [ exact (le_relASP w (fun us r => outSt m (snd us) (Some r))) |].
  split.
  - intros H s r Hw. exact (H (tt, s) r Hw).
  - intros H [[] s] r Hw. exact (H s r Hw).
Qed.

Lemma dslpSt_typing {S A} (m : stdivndNE S A) (w : DSLPSt S A) :
  ordDSLPSt (dslpSt m) w
  <-> (forall s r, dslpRel w (tt, s) r -> outSt m s (Some r)).
Proof.
  etransitivity;
    [ exact (relDSLP_le (fun us r => outSt m (snd us) (Some r)) w) |].
  split.
  - intros H s r Hw. exact (H (tt, s) r Hw).
  - intros H [[] s] r Hw. exact (H s r Hw).
Qed.

(** Three computations: the result [(tt, 0)] is reached from [0] by the
    first, from [1] by the second, and by the third from nowhere. *)
Definition reach0From0 : stdivndNE nat unit :=
  progOf (fun s (r : unit * nat) => s = 0 /\ r = (tt, 0)).
Definition reach0From1 : stdivndNE nat unit :=
  progOf (fun s (r : unit * nat) => s = 1 /\ r = (tt, 0)).
Definition reachNothing : stdivndNE nat unit :=
  progOf (fun (_ : nat) (_ : unit * nat) => False).

(** A typing is an inclusion of relations, so the computations typed by one
    index are closed under intersection of their relations.  The ASP
    [Under] triple is not: the first two computations satisfy it and the
    third, whose relation is their intersection, does not.  So no index has
    the triple as its typings.  This is a fact about the order of the ASP
    monad, not about the Dijkstra construction. *)
Theorem no_asp_under_index :
  ~ exists w : ASPSt nat unit,
      forall m : stdivndNE nat unit,
        ordASPSt w (aspSt m) <->
        triple (@aspSt nat) m Under
          (fun _ => True) (fun r : unit * nat => r = (tt, 0)).
Proof.
  intros [w Hiff].
  assert (H1 : ordASPSt w (aspSt reach0From0)).
  { apply (proj2 (Hiff reach0From0)). intros r Hr.
    exists (tt, 0). split; [ exact I | exact (conj eq_refl Hr) ]. }
  assert (H2 : ordASPSt w (aspSt reach0From1)).
  { apply (proj2 (Hiff reach0From1)). intros r Hr.
    exists (tt, 1). split; [ exact I | exact (conj eq_refl Hr) ]. }
  pose proof (proj1 (aspSt_typing_op w reach0From0) H1) as R1.
  pose proof (proj1 (aspSt_typing_op w reach0From1) H2) as R2.
  assert (H0 : ordASPSt w (aspSt reachNothing)).
  { apply (proj2 (aspSt_typing_op w reachNothing)). intros s r Hw.
    destruct (R1 s r Hw) as [E1 _]. destruct (R2 s r Hw) as [E2 _].
    subst s. discriminate E2. }
  destruct (proj1 (Hiff reachNothing) H0 (tt, 0) eq_refl) as [[[] s] [_ Hr]].
  exact Hr.
Qed.

(** The same for the DSLP [Over] triple, at the complements: the result
    [(tt, 0)] must be reached from somewhere. *)
Theorem no_dslp_over_index :
  ~ exists w : DSLPSt nat unit,
      forall m : stdivndNE nat unit,
        ordDSLPSt (dslpSt m) w <->
        triple (@dslpSt nat) m Over
          (fun _ => False) (fun r : unit * nat => r <> (tt, 0)).
Proof.
  intros [w Hiff].
  assert (H1 : ordDSLPSt (dslpSt reach0From0) w).
  { apply (proj2 (Hiff reach0From0)). intros r Hd E. subst r.
    exact (Hd (tt, 0) (conj eq_refl eq_refl)). }
  assert (H2 : ordDSLPSt (dslpSt reach0From1) w).
  { apply (proj2 (Hiff reach0From1)). intros r Hd E. subst r.
    exact (Hd (tt, 1) (conj eq_refl eq_refl)). }
  pose proof (proj1 (dslpSt_typing reach0From0 w) H1) as R1.
  pose proof (proj1 (dslpSt_typing reach0From1 w) H2) as R2.
  assert (H0 : ordDSLPSt (dslpSt reachNothing) w).
  { apply (proj2 (dslpSt_typing reachNothing w)). intros s r Hw.
    destruct (R1 s r Hw) as [E1 _]. destruct (R2 s r Hw) as [E2 _].
    subst s. discriminate E2. }
  exact (proj1 (Hiff reachNothing) H0 (tt, 0) (fun us Hr => Hr) eq_refl).
Qed.

(** ** Without state the ASP [Under] triple is a typing

    At the input [unit] there is one start point, so "some start point in
    the precondition" and "every start point in the precondition" say the
    same once the precondition holds.  This is all the statement uses: it
    is about any ASP element at unit input, and it is what fails with
    state. *)
Lemma le_aspUnder_unit {Y} (w : ASPArr unit Y)
  (P : unit -> Prop) (Q : Y -> Prop) :
  P tt ->
  ((forall y, Q y -> getASPArr w P y)
   <-> (forall P' y, getASPArr (aspUnder P Q) P' y -> getASPArr w P' y)).
Proof.
  intro Hp. split.
  - intros H P' y [[] [HP' [_ HQ]]].
    destruct (proj1 (get_aspRel w P y) (H y HQ)) as [[] [_ Hr]].
    exact (proj2 (get_aspRel w P' y) (ex_intro _ tt (conj HP' Hr))).
  - intros H y HQ. apply (H P y). exists tt. exact (conj Hp (conj Hp HQ)).
Qed.

Theorem triple_under_aspPure {M : Type -> Type} (θ : forall A, M A -> ASP A)
  {Hθ : IsMonadMorphism θ} {A} (m : M A)
  (pre : unit -> Prop) (post : A -> Prop) :
  pre tt ->
  (triple θ m Under pre post <-> ordASP (aspUnder pre post) (θ A m)).
Proof. exact (le_aspUnder_unit (θ A m) pre post). Qed.
