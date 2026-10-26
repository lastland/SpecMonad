(** * Triples, for any monad morphism

    [triple θ m k P Q] is the triple of the computation [m] through the
    monad morphism [θ], for every kind of triple at once: the specification
    [θ m] is read as a predicate transformer, and [k] says on which side of
    it the precondition [P] and the postcondition [Q] lie.  A specification
    monad says how its elements are read ([SpecReading]): forward (SP) or
    backward (WP), and on which types its pre- and postconditions are
    predicates.  The readings of the specification monads at each setting
    are in [DivNonDet/Triples.v], [DivNonDetSt/Triples.v] and
    [DivNonDetStExc/Triples.v].

    The SP judgements [aspHolds], [dslpHolds], [dspHolds], [aslpHolds] are
    stated on a base arrow at arbitrary indices: the triple of an SP morphism
    at every setting is one of them, re-indexed.  Monad morphisms are in
    [Lib/Monad/OrderedMonad.v].

    The [Under] triple of each reading is a logic of Verscht and Kaminski's
    taxonomy (POPL 2025), and each setting's [Triples.v] names it:

      [TotalCorr]      total correctness              dwp    demonic, total
      [PartCorr]       partial correctness            dwlp   demonic, partial
      [LisbonLogic]    Lisbon logic                   awp    angelic, total
      [AngPartCorr]    angelic partial correctness    awlp   angelic, partial
      [IncorrLogic]    incorrectness logic            asp    angelic, total
      [PartIncorr]     partial incorrectness          dslp   demonic, partial
      [DemIncorr]      demonic incorrectness          dsp    demonic, total
      [AngPartIncorr]  angelic partial incorrectness  aslp   angelic, partial

    Correctness bounds the start states (pre included in wp post),
    incorrectness the final ones (post included in sp pre).  The [Over]
    triples are their contrapositives. *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.SP Require Import SPostArr DSPASLPArr.
From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Incorrectness.Lib.Monad Require Import
  OrderedMonad.

From Incorrectness.Relational Require Import
  Rel.

(* ================================================================= *)
(** * The general triple                                              *)
(* ================================================================= *)

(** A specification element is read as a predicate transformer between
    preconditions and postconditions: forward, from a precondition to the
    postcondition it establishes (SP), or backward, from a postcondition to
    the precondition it needs (WP).  A triple says that a pre- and a
    postcondition lie on one side of that transformer:

      [Under]   the transformer's value is in the conclusion
      [Over]    the transformer's value is in the premise

    so the four cases below are

      forward,  [Under]   post  is included in  sp pre
      forward,  [Over]    sp pre  is included in  post
      backward, [Under]   pre  is included in  wp post
      backward, [Over]    wp post  is included in  pre *)

Inductive approxKind : Type := Under | Over.

Inductive PTReading (X Y : Type) : Type :=
| Forward  (t : (X -> Prop) -> Y -> Prop)
| Backward (t : (Y -> Prop) -> X -> Prop).

Arguments Forward {X Y} t.
Arguments Backward {X Y} t.

Definition pt_holds {X Y : Type} (r : PTReading X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  match r, k with
  | Forward t,  Under => forall y, Q y -> t P y
  | Forward t,  Over  => forall y, t P y -> Q y
  | Backward t, Under => forall x, P x -> t Q x
  | Backward t, Over  => forall x, t Q x -> P x
  end.

(** How an element of a specification monad is read at result type [A]:
    its preconditions are predicates on [X], its postconditions on [Y].
    [X] and [Y] are determined by the monad and the result type. *)
Class SpecReading (W : Type -> Type) (A : Type) (X Y : Type) : Type := {
  spec_read : W A -> PTReading X Y
}.

#[global] Hint Mode SpecReading ! - - - : typeclass_instances.

(** The judgement on a specification element. *)
Definition spec_holds {W : Type -> Type} {A X Y : Type}
  {RW : SpecReading W A X Y}
  (w : W A) (k : approxKind) (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (spec_read w) k P Q.

(** The triple of a computation, through a monad morphism.  The types of
    [P] and [Q] are those of the morphism's target. *)
Definition triple {M W : Type -> Type}
  (θ : forall A, M A -> W A) {Hθ : IsMonadMorphism θ}
  {A X Y : Type} {RW : SpecReading W A X Y}
  (m : M A) (k : approxKind) (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  spec_holds (θ A m) k P Q.

Section PTHolds.
  Context {X Y : Type}.

  (** *** Consequence *)

  Lemma pt_holds_forward_under_conseq (t : (X -> Prop) -> Y -> Prop)
    (P P' : X -> Prop) (Q Q' : Y -> Prop) :
    (forall P1 P2 y, (forall x, P1 x -> P2 x) -> t P1 y -> t P2 y) ->
    (forall x, P x -> P' x) -> (forall y, Q' y -> Q y) ->
    pt_holds (Forward t) Under P Q -> pt_holds (Forward t) Under P' Q'.
  Proof. intros Hmono HP HQ H y Hy. exact (Hmono P P' y HP (H y (HQ y Hy))). Qed.

  Lemma pt_holds_forward_over_conseq (t : (X -> Prop) -> Y -> Prop)
    (P P' : X -> Prop) (Q Q' : Y -> Prop) :
    (forall P1 P2 y, (forall x, P1 x -> P2 x) -> t P1 y -> t P2 y) ->
    (forall x, P' x -> P x) -> (forall y, Q y -> Q' y) ->
    pt_holds (Forward t) Over P Q -> pt_holds (Forward t) Over P' Q'.
  Proof. intros Hmono HP HQ H y Hy. exact (HQ y (H y (Hmono P' P y HP Hy))). Qed.

  Lemma pt_holds_backward_under_conseq (t : (Y -> Prop) -> X -> Prop)
    (P P' : X -> Prop) (Q Q' : Y -> Prop) :
    (forall Q1 Q2 x, (forall y, Q1 y -> Q2 y) -> t Q1 x -> t Q2 x) ->
    (forall x, P' x -> P x) -> (forall y, Q y -> Q' y) ->
    pt_holds (Backward t) Under P Q -> pt_holds (Backward t) Under P' Q'.
  Proof. intros Hmono HP HQ H x Hx. exact (Hmono Q Q' x HQ (H x (HP x Hx))). Qed.

  Lemma pt_holds_backward_over_conseq (t : (Y -> Prop) -> X -> Prop)
    (P P' : X -> Prop) (Q Q' : Y -> Prop) :
    (forall Q1 Q2 x, (forall y, Q1 y -> Q2 y) -> t Q1 x -> t Q2 x) ->
    (forall x, P x -> P' x) -> (forall y, Q' y -> Q y) ->
    pt_holds (Backward t) Over P Q -> pt_holds (Backward t) Over P' Q'.
  Proof. intros Hmono HP HQ H x Hx. exact (HP x (H x (Hmono Q' Q x HQ Hx))). Qed.

  (** *** A backward reading indexed by a start state

      A triple against the family is the family of triples, one per start
      state, each with a precondition that no longer mentions the state. *)
  Lemma pt_holds_pointwise (t : (Y -> Prop) -> X -> Prop) (k : approxKind)
    (P : X -> Prop) (Q : Y -> Prop) :
    pt_holds (Backward t) k P Q
    <-> forall x, pt_holds (Backward (fun Q' (_ : unit) => t Q' x)) k
                    (fun _ => P x) Q.
  Proof.
    destruct k; cbn; split.
    - intros H x _ Hp. exact (H x Hp).
    - intros H x Hp. exact (H x tt Hp).
    - intros H x _ Ht. exact (H x Ht).
    - intros H x Ht. exact (H x tt Ht).
  Qed.

  (** *** Two readings of one direction *)

  (** Inclusion, pointwise. *)
  Definition pt_incl (r1 r2 : PTReading X Y) : Prop :=
    match r1, r2 with
    | Forward t1, Forward t2 => forall P y, t1 P y -> t2 P y
    | Backward t1, Backward t2 => forall Q x, t1 Q x -> t2 Q x
    | _, _ => False
    end.

  Lemma pt_holds_incl_under (r1 r2 : PTReading X Y) (P : X -> Prop) (Q : Y -> Prop) :
    pt_incl r1 r2 -> pt_holds r1 Under P Q -> pt_holds r2 Under P Q.
  Proof.
    destruct r1 as [t1|t1], r2 as [t2|t2]; cbn; try contradiction.
    - intros Hi H y Hq. exact (Hi P y (H y Hq)).
    - intros Hi H x Hp. exact (Hi Q x (H x Hp)).
  Qed.

  Lemma pt_holds_incl_over (r1 r2 : PTReading X Y) (P : X -> Prop) (Q : Y -> Prop) :
    pt_incl r1 r2 -> pt_holds r2 Over P Q -> pt_holds r1 Over P Q.
  Proof.
    destruct r1 as [t1|t1], r2 as [t2|t2]; cbn; try contradiction.
    - intros Hi H y Ht. exact (H y (Hi P y Ht)).
    - intros Hi H x Ht. exact (H x (Hi Q x Ht)).
  Qed.

  (** Two readings that include each other give the same triples. *)
  Lemma pt_holds_same (r1 r2 : PTReading X Y) (k : approxKind)
    (P : X -> Prop) (Q : Y -> Prop) :
    pt_incl r1 r2 -> pt_incl r2 r1 -> pt_holds r1 k P Q <-> pt_holds r2 k P Q.
  Proof.
    intros H12 H21. destruct k; split.
    - exact (pt_holds_incl_under r1 r2 P Q H12).
    - exact (pt_holds_incl_under r2 r1 P Q H21).
    - exact (pt_holds_incl_over r2 r1 P Q H21).
    - exact (pt_holds_incl_over r1 r2 P Q H12).
  Qed.

  (** The first is the contrapositive of the second. *)
  Definition pt_contra (r1 r2 : PTReading X Y) : Prop :=
    match r1, r2 with
    | Forward t1, Forward t2 => forall P y, t1 P y <-> ~ t2 (fun x => ~ P x) y
    | Backward t1, Backward t2 => forall Q x, t1 Q x <-> ~ t2 (fun y => ~ Q y) x
    | _, _ => False
    end.

  Lemma pt_holds_contra (r1 r2 : PTReading X Y) (P : X -> Prop) (Q : Y -> Prop) :
    pt_contra r1 r2 ->
    (pt_holds r1 Under P Q
     <-> pt_holds r2 Over (fun x => ~ P x) (fun y => ~ Q y)).
  Proof.
    destruct r1 as [t1|t1], r2 as [t2|t2]; cbn; try contradiction.
    - intro Hc. split.
      + intros H y Ht Hq. exact (proj1 (Hc P y) (H y Hq) Ht).
      + intros H y Hq. apply (proj2 (Hc P y)). intro Ht. exact (H y Ht Hq).
    - intro Hc. split.
      + intros H x Ht Hp. exact (proj1 (Hc Q x) (H x Hp) Ht).
      + intros H x Hp. apply (proj2 (Hc Q x)). intro Ht. exact (H x Ht Hp).
  Qed.
End PTHolds.

(* ================================================================= *)
(** * Sequencing                                                      *)
(* ================================================================= *)

(** Two triples compose into one for the sequenced computation, given an
    intermediate assertion.  A rule needs only two facts about the
    readings: the transformer of [bind] is built from the transformers of
    the parts, which is the monad morphism law ([Hbind] below), and
    transformers are monotone ([Hmono]).  Everything else is the shape of
    the triple, so one lemma covers both kinds at once: [Over] flips the
    three orderings and the side condition together.

    [Under] and [Over] disagree on which way the side condition points, and
    a backward reading disagrees with a forward one, so there are two
    definitions, each flipped by the kind. *)

(** The intermediate assertion of the first computation implies the
    precondition of the continuation. *)
Definition seq_side {Y : Type} (k : approxKind) (q0 pa : Y -> Prop) : Prop :=
  match k with
  | Under => forall y, q0 y -> pa y
  | Over  => forall y, pa y -> q0 y
  end.

Section SequencingBackward.
  Context {X Y Z : Type}.
  Variables (tm  : (Y -> Prop) -> X -> Prop)
            (tf  : Y -> (Z -> Prop) -> Prop)
            (tmf : (Z -> Prop) -> X -> Prop).

  Hypothesis Hmono :
    forall Q1 Q2 x, (forall y, Q1 y -> Q2 y) -> tm Q1 x -> tm Q2 x.
  Hypothesis Hbind : forall Q x, tmf Q x <-> tm (fun y => tf y Q) x.

  (** The continuation's triple is stated at the intermediate point, so its
      precondition no longer mentions it; this is the form
      [pt_holds_pointwise] produces, and the one a lifted [wp] morphism
      reads at ([spec_holds_wpSt]). *)
  Lemma pt_holds_backward_seq (k : approxKind)
    (p : X -> Prop) (q0 pa : Y -> Prop) (q : Z -> Prop) :
    pt_holds (Backward tm) k p q0 ->
    (forall y, pt_holds (Backward (fun Q (_ : unit) => tf y Q)) k
                 (fun _ => pa y) q) ->
    seq_side k q0 pa ->
    pt_holds (Backward tmf) k p q.
  Proof.
    destruct k; cbn; intros H1 H2 Hs x Hx.
    - apply Hbind. refine (Hmono q0 _ x _ (H1 x Hx)).
      intros y Hq0. exact (H2 y tt (Hs y Hq0)).
    - apply H1. refine (Hmono _ q0 x _ (proj1 (Hbind q x) Hx)).
      intros y Ht. exact (Hs y (H2 y tt Ht)).
  Qed.
End SequencingBackward.

(** A forward reading sequences the other way round: the continuation
    receives the postcondition the first computation produces, so it is the
    continuation that must be monotone, and the side condition points
    against the backward one.

    The intermediate point carries a returned value [i] and a state [x],
    which the first computation's postcondition sees together ([emb]) and
    the continuation sees apart: it is a different transformer per returned
    value.  So [bind] must aggregate over [i], and the two sp monads that
    have a monotone [bind] aggregate differently -- [ASPSt] by join,
    [DSLPSt] by meet -- which is the only place the two rules part. *)
Section SequencingForward.
  Context {I X Y Z : Type}.
  Variables (tm  : (X -> Prop) -> Y -> Prop)
            (emb : I -> X -> Y)
            (tf  : I -> (X -> Prop) -> Z -> Prop)
            (tmf : (X -> Prop) -> Z -> Prop).

  Hypothesis Hmono :
    forall i P1 P2 z, (forall x, P1 x -> P2 x) -> tf i P1 z -> tf i P2 z.

  Definition seq_side_fwd (k : approxKind)
    (q0 : Y -> Prop) (pa : I -> X -> Prop) : Prop :=
    match k with
    | Under => forall i x, pa i x -> q0 (emb i x)
    | Over  => forall i x, q0 (emb i x) -> pa i x
    end.

  (** A join-aggregated [bind], as [ASPSt] has.  The [Under] rule must
      produce a returned value out of premises that only quantify over
      them, so it needs [I] inhabited; with [I] empty the sequenced
      transformer is the join of nothing, every premise is vacuous, and the
      conclusion is arbitrary.  The [Over] rule -- Hoare logic -- is free
      of it. *)
  Section Join.
    Hypothesis Hbind :
      forall P z, tmf P z <-> exists i, tf i (fun x => tm P (emb i x)) z.

    Lemma pt_holds_forward_join_under_seq (Hinh : inhabited I)
      (p : X -> Prop) (q0 : Y -> Prop) (pa : I -> X -> Prop) (q : Z -> Prop) :
      pt_holds (Forward tm) Under p q0 ->
      (forall i, pt_holds (Forward (tf i)) Under (pa i) q) ->
      seq_side_fwd Under q0 pa ->
      pt_holds (Forward tmf) Under p q.
    Proof.
      intros H1 H2 Hs z Hq. destruct Hinh as [i].
      apply Hbind. exists i.
      refine (Hmono i (pa i) _ z _ (H2 i z Hq)).
      intros x Hpa. exact (H1 (emb i x) (Hs i x Hpa)).
    Qed.

    Lemma pt_holds_forward_join_over_seq
      (p : X -> Prop) (q0 : Y -> Prop) (pa : I -> X -> Prop) (q : Z -> Prop) :
      pt_holds (Forward tm) Over p q0 ->
      (forall i, pt_holds (Forward (tf i)) Over (pa i) q) ->
      seq_side_fwd Over q0 pa ->
      pt_holds (Forward tmf) Over p q.
    Proof.
      intros H1 H2 Hs z Hz.
      destruct (proj1 (Hbind p z) Hz) as [i Hi].
      apply (H2 i z). refine (Hmono i _ (pa i) z _ Hi).
      intros x Ht. exact (Hs i x (H1 (emb i x) Ht)).
    Qed.
  End Join.

  (** A meet-aggregated [bind], as [DSLPSt] has.  Here it is the [Over]
      rule that needs [I] inhabited, for the dual reason. *)
  Section Meet.
    Hypothesis Hbind :
      forall P z, tmf P z <-> forall i, tf i (fun x => tm P (emb i x)) z.

    Lemma pt_holds_forward_meet_under_seq
      (p : X -> Prop) (q0 : Y -> Prop) (pa : I -> X -> Prop) (q : Z -> Prop) :
      pt_holds (Forward tm) Under p q0 ->
      (forall i, pt_holds (Forward (tf i)) Under (pa i) q) ->
      seq_side_fwd Under q0 pa ->
      pt_holds (Forward tmf) Under p q.
    Proof.
      intros H1 H2 Hs z Hq. apply Hbind. intro i.
      refine (Hmono i (pa i) _ z _ (H2 i z Hq)).
      intros x Hpa. exact (H1 (emb i x) (Hs i x Hpa)).
    Qed.

    Lemma pt_holds_forward_meet_over_seq (Hinh : inhabited I)
      (p : X -> Prop) (q0 : Y -> Prop) (pa : I -> X -> Prop) (q : Z -> Prop) :
      pt_holds (Forward tm) Over p q0 ->
      (forall i, pt_holds (Forward (tf i)) Over (pa i) q) ->
      seq_side_fwd Over q0 pa ->
      pt_holds (Forward tmf) Over p q.
    Proof.
      intros H1 H2 Hs z Hz. destruct Hinh as [i]. apply (H2 i z).
      refine (Hmono i _ (pa i) z _ (proj1 (Hbind p z) Hz i)).
      intros x Ht. exact (Hs i x (H1 (emb i x) Ht)).
    Qed.
  End Meet.
End SequencingForward.

(** The inhabitation condition of the two rules above is necessary, not an
    artifact of their proofs.  At [I] empty the join is of nothing and the
    meet is of everything, so in each case every premise is vacuous while
    the conclusion is decided outright, the wrong way. *)

Theorem forward_join_under_seq_needs_inhabited :
  ~ (forall (I X Y Z : Type)
       (tm : (X -> Prop) -> Y -> Prop) (emb : I -> X -> Y)
       (tf : I -> (X -> Prop) -> Z -> Prop) (tmf : (X -> Prop) -> Z -> Prop),
       (forall i P1 P2 z, (forall x, P1 x -> P2 x) -> tf i P1 z -> tf i P2 z) ->
       (forall P z, tmf P z <-> exists i, tf i (fun x => tm P (emb i x)) z) ->
       forall (p : X -> Prop) (q0 : Y -> Prop) (pa : I -> X -> Prop)
         (q : Z -> Prop),
         pt_holds (Forward tm) Under p q0 ->
         (forall i, pt_holds (Forward (tf i)) Under (pa i) q) ->
         seq_side_fwd emb Under q0 pa ->
         pt_holds (Forward tmf) Under p q).
Proof.
  intro H.
  refine (H Empty_set unit unit unit (fun _ _ => True)
            (fun i (_ : unit) => Empty_set_rect (fun _ => unit) i)
            (fun i => Empty_set_rect (fun _ => (unit -> Prop) -> unit -> Prop) i)
            (fun _ _ => False) _ _
            (fun _ => True) (fun _ => True)
            (fun i => Empty_set_rect (fun _ => unit -> Prop) i)
            (fun _ => True) _ _ _ tt I).
  - intros [].
  - intros P z. split; [ contradiction | intros [[] _] ].
  - intros y _. exact I.
  - intros [].
  - intros [].
Qed.

Theorem forward_meet_over_seq_needs_inhabited :
  ~ (forall (I X Y Z : Type)
       (tm : (X -> Prop) -> Y -> Prop) (emb : I -> X -> Y)
       (tf : I -> (X -> Prop) -> Z -> Prop) (tmf : (X -> Prop) -> Z -> Prop),
       (forall i P1 P2 z, (forall x, P1 x -> P2 x) -> tf i P1 z -> tf i P2 z) ->
       (forall P z, tmf P z <-> forall i, tf i (fun x => tm P (emb i x)) z) ->
       forall (p : X -> Prop) (q0 : Y -> Prop) (pa : I -> X -> Prop)
         (q : Z -> Prop),
         pt_holds (Forward tm) Over p q0 ->
         (forall i, pt_holds (Forward (tf i)) Over (pa i) q) ->
         seq_side_fwd emb Over q0 pa ->
         pt_holds (Forward tmf) Over p q).
Proof.
  intro H.
  refine (H Empty_set unit unit unit (fun _ _ => True)
            (fun i (_ : unit) => Empty_set_rect (fun _ => unit) i)
            (fun i => Empty_set_rect (fun _ => (unit -> Prop) -> unit -> Prop) i)
            (fun _ _ => True) _ _
            (fun _ => True) (fun _ => True)
            (fun i => Empty_set_rect (fun _ => unit -> Prop) i)
            (fun _ => False) _ _ _ tt I).
  - intros [].
  - intros P z. split; [ intros _ [] | intros _; exact I ].
  - intros y _. exact I.
  - intros [].
  - intros [].
Qed.

(** The judgement on a base arrow, at arbitrary indices: [X] is what a
    precondition is a predicate on, [Y] what a postcondition is. *)

Definition aspHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getASPArr (@relASP X Y R))) k P Q.

Definition dslpHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getDSLPArr (@relDSLP X Y R))) k P Q.

Definition dspHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getDSP (@dspOfRelArr X Y R))) k P Q.

Definition aslpHolds {X Y : Type} (R : Rel X Y) (k : approxKind)
  (P : X -> Prop) (Q : Y -> Prop) : Prop :=
  pt_holds (Forward (getASLP (@aslpOfRelArr X Y R))) k P Q.

(** Each reading of a relation, spelled out. *)
Lemma aspHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getASPArr (relASP R) P y <-> exists x, P x /\ R x y.
Proof. reflexivity. Qed.

Lemma dslpHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getDSLPArr (relDSLP R) P y <-> forall x, R x y -> P x.
Proof. reflexivity. Qed.

Lemma dspHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getDSP (dspOfRelArr R) P y
  <-> (exists x, P x /\ R x y) /\ (forall x, R x y -> P x).
Proof. reflexivity. Qed.

Lemma aslpHolds_read {X Y : Type} (R : Rel X Y) (P : X -> Prop) (y : Y) :
  getASLP (aslpOfRelArr R) P y
  <-> (exists x, P x /\ R x y) \/ (forall x, R x y -> P x).
Proof. reflexivity. Qed.
