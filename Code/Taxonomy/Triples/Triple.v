(** * Triples

    [triple θ m k P Q] is the triple of the computation [m] through the
    monad morphism [θ], for every kind of triple at once: the specification
    [θ m] is read as a predicate transformer, and [k] says on which side of
    it the precondition [P] and the postcondition [Q] lie.

    The first part of the file is general.  A specification monad says how
    its elements are read ([SpecReading]): forward (SP) or backward (WP),
    and on which types its pre- and postconditions are predicates.  The
    second part gives that reading for each specification monad of
    [BaseSpecMonads/].

    Monad morphisms are in [Classes/OrderedMonad.v]; the morphisms of this
    development are in [MonadMorphisms.v]. *)

From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Lib.Monad Require Import OrderedMonad.

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
(** * How each specification monad is read                            *)
(* ================================================================= *)

From ExtLib Require Import StateMonad OptionMonad.
From Incorrectness.WP Require Import
  WPureMonad.
From Incorrectness.SP Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad.

(** A WP element is read backward, from a postcondition to the precondition
    it needs.  Preconditions are on [unit], or on the start state;
    postconditions on the result, on result and final state, or on the
    outcome of a computation that may raise. *)

#[global] Instance SpecReading_WPure (A : Type) :
  SpecReading WPure A unit A := {|
  spec_read := fun w : WPure A => Backward (fun Q (_ : unit) => getWPure w Q)
|}.

#[global] Instance SpecReading_WSt (S A : Type) :
  SpecReading (WSt S) A S (A * S)%type := {|
  spec_read := fun w : WSt S A =>
    Backward (fun Q s => getWPure (runStateT w s) Q)
|}.

#[global] Instance SpecReading_WStExc (S A : Type) :
  SpecReading (WStExc S) A S (option (A * S)) := {|
  spec_read := fun w : WStExc S A =>
    Backward (fun Q s => getWPure (unOptionT (runStateT w s)) Q)
|}.

(** An SP element is read forward, from a precondition to the postcondition
    it establishes.  The monads fix the input [unit], so a precondition is
    on [unit], or on the start state. *)

#[global] Instance SpecReading_ASP (A : Type) :
  SpecReading ASP A unit A := {|
  spec_read := fun w : ASP A => Forward (getASPArr w)
|}.

#[global] Instance SpecReading_ASPSt (S A : Type) :
  SpecReading (ASPSt S) A S (A * S)%type := {|
  spec_read := fun w : ASPSt S A => Forward (getASPSt w)
|}.

#[global] Instance SpecReading_ASPStExc (S A : Type) :
  SpecReading (ASPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : ASPStExc S A => Forward (getASPStExc w)
|}.

#[global] Instance SpecReading_DSLP (A : Type) :
  SpecReading DSLP A unit A := {|
  spec_read := fun w : DSLP A => Forward (getDSLPArr w)
|}.

#[global] Instance SpecReading_DSLPSt (S A : Type) :
  SpecReading (DSLPSt S) A S (A * S)%type := {|
  spec_read := fun w : DSLPSt S A => Forward (getDSLPSt w)
|}.

#[global] Instance SpecReading_DSLPStExc (S A : Type) :
  SpecReading (DSLPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : DSLPStExc S A => Forward (getDSLPStExc w)
|}.

#[global] Instance SpecReading_DSP (A : Type) :
  SpecReading DSP A unit A := {|
  spec_read := fun w : DSP A => Forward (getDSP w)
|}.

#[global] Instance SpecReading_DSPSt (S A : Type) :
  SpecReading (DSPSt S) A S (A * S)%type := {|
  spec_read := fun w : DSPSt S A => Forward (getDSPSt w)
|}.

#[global] Instance SpecReading_DSPStExc (S A : Type) :
  SpecReading (DSPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : DSPStExc S A => Forward (getDSPStExc w)
|}.

#[global] Instance SpecReading_ASLP (A : Type) :
  SpecReading ASLP A unit A := {|
  spec_read := fun w : ASLP A => Forward (getASLP w)
|}.

#[global] Instance SpecReading_ASLPSt (S A : Type) :
  SpecReading (ASLPSt S) A S (A * S)%type := {|
  spec_read := fun w : ASLPSt S A => Forward (getASLPSt w)
|}.

#[global] Instance SpecReading_ASLPStExc (S A : Type) :
  SpecReading (ASLPStExc S) A S (option (A * S)) := {|
  spec_read := fun w : ASLPStExc S A => Forward (getASLPStExc w)
|}.
