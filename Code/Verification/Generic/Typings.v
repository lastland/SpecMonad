(** * Triples as typings, for any morphism (paper, Section 6)

    The Dijkstra monads of [DijkstraMonad.v] and the triples of [Triple.v]
    are read off the same monad morphisms; this file compares them, for any
    morphism into a target and at arbitrary indices.  Triples are typings
    where the two say the same: a WP [Under] triple is a typing in [DM] and
    a WP [Over] triple one in [DMop]; ASP [Over] is a typing in [DM] and
    DSLP [Under] one in [DMop].  For ASP [Under] and DSLP [Over], a typing is
    an inclusion of relations, and the indices one would like to use give
    more than the triple.  The instances and the negative results are in
    [Base/TypingsPure.v], [State/TypingsSt.v] and [StateExc/TypingsStExc.v]. *)

From Coq Require Import Morphisms RelationClasses Relation_Definitions
  Classical_Prop.
From ExtLib Require Import Monad StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Arrow Require Import Arrow ArrowMonad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Lib.Monad Require Import
  TransformerLaws.
From Incorrectness.Relational Require Import Rel.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.WP Require Import
  WPure.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.Generic Require Import DijkstraMonad.


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
