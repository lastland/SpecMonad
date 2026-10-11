(** * [RelPrePost]: the monotone-relations specification monad

        [Assuming p    := { q : Prop | q <-> (p -> q) }]
        [RelPrePost X  := { r : forall p:Prop, (X -> Assuming p) -> Assuming p
                          | monotone in the Hoare order }]

        [ret a    := fun p post => (p -> post a)]
        [bind m f := fun p post => m p (fun a => f a p post)]

    A [RelPrePost] validates Hoare specifications: given a
    precondition and a postcondition it says whether the pair is admissible.
    Monotonicity is the Hoare order — strengthening the precondition and
    weakening the postcondition preserves validity.

    This is DM4all's [MRSpec] ([sprop/SpecificationMonads.v],
    [Section MonotonicRelations]), transcribed from [SProp] to [Prop].
    Bind passes each continuation's [Assuming p] result directly to [m].
    [Eq1] compares the underlying verdicts by logical equivalence rather
    than by equality of bundled values.  The formulas above omit the
    [runRPP] and [ab] projections used in the definitions.

    [Assuming p] is the subtype of propositions [q] with [(p -> q) -> q] —
    "knowing [q] under [p] already gives [q]".  It is exactly what makes
    [bind_ret_l] go through, and it is the dual of [SPostMonad.v]'s [Over p].

    The unary carrier is [RPPM.RelPrePost].  The separate binary carrier
    [RelPrePostArr] in [Arrows/RelPrePostArr.v] validates input-indexed
    post-relations and uses projection-induced arrow equality. *)

From ITree Require Import Basics.Monad.

Module RPPM.

  (* ================================================================= *)
  (** ** [Assuming p]: propositions closed under assuming [p]          *)
  (* ================================================================= *)

  Definition Assuming (p : Prop) : Type := { q : Prop | q <-> (p -> q) }.

  Definition ab {p} (q : Assuming p) : Prop := proj1_sig q.

  (** The characteristic property: discharge an assumption of [p]. *)
  Lemma ab_close {p} (q : Assuming p) : (p -> ab q) -> ab q.
  Proof. exact (proj2 (proj2_sig q)). Qed.

  (* ================================================================= *)
  (** ** The carrier                                                   *)
  (* ================================================================= *)

  Definition RPPT (X : Type) : Type :=
    forall (p : Prop), (X -> Assuming p) -> Assuming p.

  (** The Hoare order: strengthen the pre, weaken the post. *)
  Definition rpp_mono {X} (r : RPPT X) : Prop :=
    forall (p1 p2 : Prop) (post1 : X -> Assuming p1) (post2 : X -> Assuming p2),
      (p1 -> p2) ->
      (forall x, ab (post2 x) -> ab (post1 x)) ->
      ab (r p2 post2) -> ab (r p1 post1).

  Definition RelPrePost (X : Type) : Type := { r : RPPT X | rpp_mono r }.

  Definition runRPP {X} (r : RelPrePost X) : RPPT X := proj1_sig r.

  Lemma runRPP_mono {X} (r : RelPrePost X)
    (p1 p2 : Prop) (post1 : X -> Assuming p1) (post2 : X -> Assuming p2) :
    (p1 -> p2) -> (forall x, ab (post2 x) -> ab (post1 x)) ->
    ab (runRPP r p2 post2) -> ab (runRPP r p1 post1).
  Proof. exact (proj2_sig r p1 p2 post1 post2). Qed.

  (* ================================================================= *)
  (** ** [ret] and [bind]                                              *)
  (* ================================================================= *)

  Definition retAssuming {X} (a : X) (p : Prop) (post : X -> Assuming p)
    : Assuming p :=
    exist _ (p -> ab (post a))
            (conj (fun H _ => H) (fun H hp => H hp hp)).

  Definition retRPPT {X} (a : X) : RPPT X := fun p post => retAssuming a p post.

  Lemma retRPP_mono {X} (a : X) : rpp_mono (retRPPT a).
  Proof.
    intros p1 p2 post1 post2 Hpre Hpost H hp1.
    exact (Hpost a (H (Hpre hp1))).
  Qed.

  Definition retRPP {X} (a : X) : RelPrePost X :=
    exist _ (retRPPT a) (retRPP_mono a).

  (** [bind] passes the continuation's verdict straight through — it already
      lives in [Assuming p], so no re-wrapping is needed. *)
  Definition bindRPPT {X Y} (m : RelPrePost X) (f : X -> RelPrePost Y)
    : RPPT Y :=
    fun p post => runRPP m p (fun a => runRPP (f a) p post).

  Lemma bindRPP_mono {X Y} (m : RelPrePost X) (f : X -> RelPrePost Y) :
    rpp_mono (bindRPPT m f).
  Proof.
    intros p1 p2 post1 post2 Hpre Hpost H.
    apply (runRPP_mono m p1 p2
             (fun a => runRPP (f a) p1 post1)
             (fun a => runRPP (f a) p2 post2) Hpre); [| exact H ].
    intro a. exact (runRPP_mono (f a) p1 p2 post1 post2 Hpre Hpost).
  Qed.

  Definition bindRPP {X Y} (m : RelPrePost X) (f : X -> RelPrePost Y)
    : RelPrePost Y :=
    exist _ (bindRPPT m f) (bindRPP_mono m f).

  #[global]
  Instance Monad_RelPrePost : Monad RelPrePost := {
    ret  := @retRPP ;
    bind := @bindRPP
  }.

  (** Pointwise equivalence of the verdicts. *)
  #[global]
  Instance Eq1_RelPrePost : Eq1 RelPrePost :=
    fun X m1 m2 => forall p post, ab (runRPP m1 p post) <-> ab (runRPP m2 p post).

End RPPM.

(* ================================================================= *)
(** ** Monad laws                                                    *)
(* ================================================================= *)

Module RPPMFacts.
  Import RPPM.

  #[global]
  Instance Eq1Equivalence_RelPrePost
    : @Eq1Equivalence RelPrePost _ Eq1_RelPrePost.
  Proof.
    constructor; repeat intro; unfold eq1, Eq1_RelPrePost in *.
    - reflexivity.
    - symmetry. apply H.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  #[global]
  Instance MonadLawsE_RelPrePost
    : @MonadLawsE RelPrePost Eq1_RelPrePost _.
  Proof.
    constructor.
    - (* bind_ret_l -- [Assuming] is exactly what discharges the [p ->] *)
      intros X Y f x p post. cbn. split.
      + intro H. exact (ab_close (runRPP (f x) p post) H).
      + intros H _. exact H.
    - (* bind_ret_r -- the two continuations agree pointwise *)
      intros X m p post. cbn. unfold bindRPPT. split.
      + intro H.
        apply (runRPP_mono m p p post
                 (fun a => runRPP (retRPP a) p post) (fun h => h)); [| exact H ].
        intros a Ha. exact (ab_close (post a) Ha).
      + intro H.
        apply (runRPP_mono m p p
                 (fun a => runRPP (retRPP a) p post) post (fun h => h)); [| exact H ].
        intros a Ha hp. exact Ha.
    - (* bind_bind -- definitional *)
      intros X Y Z m f g p post. cbn. split; intro H; exact H.
    - (* Proper_bind *)
      intros X Y m1 m2 Hm f g Hf p post. cbn.
      unfold eq1, Eq1_RelPrePost in Hm, Hf.
      unfold bindRPPT. split.
      + intro H. apply (proj1 (Hm p (fun a => runRPP (g a) p post))).
        apply (runRPP_mono m1 p p
                 (fun a => runRPP (g a) p post)
                 (fun a => runRPP (f a) p post) (fun h => h)); [| exact H ].
        intro a. exact (proj1 (Hf a p post)).
      + intro H. apply (proj2 (Hm p (fun a => runRPP (f a) p post))).
        apply (runRPP_mono m2 p p
                 (fun a => runRPP (f a) p post)
                 (fun a => runRPP (g a) p post) (fun h => h)); [| exact H ].
        intro a. exact (proj2 (Hf a p post)).
  Qed.

End RPPMFacts.

(* ================================================================= *)
(** * Refinement order: [RelPrePost] is a specification monad        *)
(* ================================================================= *)

(** Reverse implication on validator verdicts: a validator that accepts
    less is higher. *)

From Coq Require Import RelationClasses.
From Incorrectness.Lib.Monad Require Import OrderedMonad.

Definition MR_le {A} (r1 r2 : RPPM.RelPrePost A) : Prop :=
  forall p post, RPPM.ab (RPPM.runRPP r2 p post)
              -> RPPM.ab (RPPM.runRPP r1 p post).

#[global] Instance MR_le_PreOrder {A} : PreOrder (@MR_le A).
Proof.
  constructor; unfold MR_le.
  - intros x p post H. exact H.
  - intros x y z H1 H2 p post H. exact (H1 p post (H2 p post H)).
Qed.

#[global] Instance OrderedMonad_RelPrePost
  : OrderedMonad RPPM.RelPrePost (@MR_le).
Proof.
  constructor.
  - intro A. exact MR_le_PreOrder.
  - intros A x y H p post Hy. exact (proj2 (H p post) Hy).
  - intros A B m1 m2 Hm f1 f2 Hf p post H.
    apply (RPPM.runRPP_mono m1 p p
             (fun a => RPPM.runRPP (f1 a) p post)
             (fun a => RPPM.runRPP (f2 a) p post) (fun h => h)).
    + intros a Ha. exact (Hf a p post Ha).
    + exact (Hm p _ H).
Qed.
