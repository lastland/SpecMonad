(** * The stateful PrePost specification monad

    The exact ExtLib record transformer [stateT S PPM.PrePost] — the
    specification-side twin of the stateful DSP/ASLP monads — ordered
    pointwise in the initial state by the existing UNCONDITIONAL Hoare
    order [PP_le] ([BaseGaloisConnections]):

        [PPSt_le p q  :=  forall s, PP_le (runStateT p s) (runStateT q s)]

    No new carrier and no guarded order: [PPSt_le] IS the generic
    explicit-parameter lift [ord_stateT] from [TransformerLaws]
    instantiated at [PP_le], and every dictionary below is the existing
    [Monad_stateT] / [Eq1_stateT] / [MonadLawsE_stateT] machinery with
    all base arguments explicit.  Nothing recursive is registered: the
    only global instances are on the concrete leaf [stateT S PPM.PrePost]. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad StateMonad.
From ITree Require Import Basics.Monad Extra.Dijkstra.DijkstraMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  PrePostMonad BaseGaloisConnections.

(* ================================================================= *)
(** ** Explicit dictionaries                                          *)
(* ================================================================= *)

(** [Monad_stateT] is deliberately not a global instance (ExtLib warns of
    infinite search), so the composed monad dictionary is named. *)
Definition Monad__PPSt (S : Type) : Monad (stateT S PPM.PrePost) :=
  @Monad_stateT S PPM.PrePost PPM.Monad_PrePost.

(** The equality and monad-law dictionaries from [TransformerLaws],
    every base dictionary passed explicitly. *)
Definition Eq1__PPSt (S : Type) : Eq1 (stateT S PPM.PrePost) :=
  @Eq1_stateT S PPM.PrePost PPM.Eq1_PrePost.

Definition Eq1Equivalence__PPSt (S : Type) :
  @Eq1Equivalence (stateT S PPM.PrePost) (Monad__PPSt S) (Eq1__PPSt S) :=
  @Eq1Equivalence_stateT S PPM.PrePost PPM.Monad_PrePost PPM.Eq1_PrePost
    PPMFacts.Eq1Equivalence_PrePost.

Definition MonadLawsE__PPSt (S : Type) :
  @MonadLawsE (stateT S PPM.PrePost) (Eq1__PPSt S) (Monad__PPSt S) :=
  @MonadLawsE_stateT S PPM.PrePost PPM.Monad_PrePost PPM.Eq1_PrePost
    PPMFacts.Eq1Equivalence_PrePost PPMFacts.MonadLawsE_PrePost.

#[local] Existing Instance Monad__PPSt.

(* ================================================================= *)
(** ** The stateful Hoare order                                       *)
(* ================================================================= *)

Definition PPSt_le {S A} (p q : stateT S PPM.PrePost A) : Prop :=
  forall s, PP_le (runStateT p s) (runStateT q s).

(** [PPSt_le] is literally the generic lift [ord_stateT] at the base
    order [PP_le]; stated as an equation for downstream conversion. *)
Lemma PPSt_le_ord_stateT {S A} (p q : stateT S PPM.PrePost A) :
  PPSt_le p q = @ord_stateT S PPM.PrePost (fun B => @PP_le B) A p q.
Proof. reflexivity. Qed.

(** All order laws lift through the generic section lemmas, with the
    base preorder/joint-monotonicity arguments [PP_le_refl],
    [PP_le_trans] and [bindPP_mono] supplied explicitly. *)
Lemma PPSt_le_refl {S A} (p : stateT S PPM.PrePost A) : PPSt_le p p.
Proof.
  exact (ord_stateT_refl S PPM.PrePost (fun B => @PP_le B) (@PP_le_refl) p).
Qed.

Lemma PPSt_le_trans {S A} (m n o : stateT S PPM.PrePost A) :
  PPSt_le m n -> PPSt_le n o -> PPSt_le m o.
Proof.
  exact (ord_stateT_trans S PPM.PrePost (fun B => @PP_le B) (@PP_le_trans)
           m n o).
Qed.

Theorem bindPPSt_mono {S A B} (m n : stateT S PPM.PrePost A)
    (f g : A -> stateT S PPM.PrePost B) :
  PPSt_le m n -> (forall a, PPSt_le (f a) (g a)) ->
  PPSt_le (bind m f) (bind n g).
Proof.
  exact (@bind_stateT_mono S PPM.PrePost PPM.Monad_PrePost
           (fun B => @PP_le B) (@bindPP_mono) A B m n f g).
Qed.

#[global] Instance PPSt_le_PreOrder {S A} : PreOrder (@PPSt_le S A).
Proof.
  constructor.
  - intro p. apply PPSt_le_refl.
  - intros p q r Hpq Hqr. exact (PPSt_le_trans p q r Hpq Hqr).
Qed.

(* ================================================================= *)
(** ** Compatibility with [Eq1]                                        *)
(* ================================================================= *)

(** [PPSt_le] transports along the existing [Eq1] on [stateT S
    PPM.PrePost], pointwise through the base [PP_le_Proper]. *)
Theorem PPSt_le_Proper {S A} :
  Proper (@eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A ==>
          @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A ==> iff) (@PPSt_le S A).
Proof.
  intros p1 p2 Hp q1 q2 Hq. split; intros Hle s.
  - exact (proj1 (@PP_le_Proper (A * S) (runStateT p1 s) (runStateT p2 s)
                    (Hp s) (runStateT q1 s) (runStateT q2 s) (Hq s))
             (Hle s)).
  - exact (proj2 (@PP_le_Proper (A * S) (runStateT p1 s) (runStateT p2 s)
                    (Hp s) (runStateT q1 s) (runStateT q2 s) (Hq s))
             (Hle s)).
Qed.

(** Mutual [PPSt_le] refinement is exactly the existing [Eq1]. *)
Theorem PPSt_le_eq1 {S A} (p q : stateT S PPM.PrePost A) :
  (PPSt_le p q /\ PPSt_le q p) <-> @eq1 (stateT S PPM.PrePost) (Eq1__PPSt S) A p q.
Proof.
  split.
  - intros [Hpq Hqp] s.
    apply (proj1 (PP_le_eq1 (runStateT p s) (runStateT q s))).
    split; [ exact (Hpq s) | exact (Hqp s) ].
  - intros H. split; intro s.
    + exact (proj1 (proj2 (PP_le_eq1 (runStateT p s) (runStateT q s)) (H s))).
    + exact (proj2 (proj2 (PP_le_eq1 (runStateT p s) (runStateT q s)) (H s))).
Qed.

(* ================================================================= *)
(** ** Concrete ordered-monad dictionaries                             *)
(* ================================================================= *)

(** Concrete ITree [OrderM] / [OrderedMonad] dictionaries for the exact
    [stateT S PPM.PrePost]: the only registered instances, no recursion
    through the transformer. *)
#[global] Instance OrderM__PPSt (S : Type) : OrderM (stateT S PPM.PrePost) :=
  @PPSt_le S.

#[global] Instance OrderedMonad__PPSt (S : Type) :
  @OrderedMonad (stateT S PPM.PrePost) (Monad__PPSt S) (OrderM__PPSt S).
Proof.
  constructor.
  - intros A p. apply PPSt_le_refl.
  - intros A p q r Hpq Hqr. exact (PPSt_le_trans p q r Hpq Hqr).
  - intros A B m n f g Hmn Hfg. exact (bindPPSt_mono m n f g Hmn Hfg).
Qed.
