(** * Galois connections among the Taxonomy spec types.

    Following Figure 1 of "Dijkstra Monads for All"
    (Maillard et al., ICFP 2019), adapted from unary specification
    monads to binary arrows.  Each connection is exposed as an
    explicit named [Galois] value, never as a global instance, because
    some endpoints admit several competing variants (notably the four
    [PrePost]/WP readings) that would otherwise be ambiguous under
    typeclass resolution.

    The connections form the following topology.  No commutativity is
    claimed: the [SPost]/[RelPrePost] edge is missing because the two
    natural binary lifts fail (see "Obstruction" at the end).

                 PureASPostArr / PureDSLPostArr
                /                                x
               /                                  x no established
             Rel                                WFRelPrePost
               \                                  /
                \                                /
                 PrePost <================> MonotoneWP

    Edge legend (alpha/gamma with the order on each side):

    - Rel <-> PureASPostArr  :  [Galois_Rel_ASPost]
        alpha = mkASP,        gamma = sp_rel
        ASP order: forward transformer implication (PureASPostArr_le)

    - Rel <-> PureDSLPostArr :  [Galois_Rel_DSLPost]
        alpha = mkDSLP,       gamma = sp_rel
        DSLP order: reverse transformer implication (PureDSLPostArr_le)

    - Rel <-> PrePost        :  [Galois_Rel_PrePost]
        alpha = rel_to_pp,    gamma = pp_to_rel
        Rel_le covariant; PrePost Hoare order

    - PrePost <-> MonotoneWP :  four variants (one carrier, two orders)
        DWP  uses [MonotoneWP_le] (reverse implication)
        DWLP uses [MonotoneWP_le]
        AWP  uses [MonotoneWP_ge] (forward implication)
        AWLP uses [MonotoneWP_ge], classical logic

        The shared [PrePost (P, R)] is read as a no-divergence
        condition [P] paired with a terminating-outcome relation [R]:

            DWP  (P,R) Q =  P /\ forall b, R b -> Q b
            DWLP (P,R) Q =       forall b, R b -> Q b
            AWP  (P,R) Q =       exists b, R b /\ Q b
            AWLP (P,R) Q = ~P \/ exists b, R b /\ Q b

    - MonotoneWP <-> WFRelPrePost :  [Galois_WP_RelPrePost]
        alpha = wp_to_rpp,    gamma = rpp_to_wp
        reverse-implication orders on both sides

    Two natural binary lifts of the DM4All [SPost]/[RelPrePost]
    adjunction fail and are documented with counterexamples at the end
    of the file. *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  RelationClasses Program.Tactics Classical_Prop.
From Incorrectness.Classes Require Import Galois.
From Incorrectness.Taxonomy Require Import
  Rel SPost SPostFacts PrePost WPArr RelPrePost.

(* ================================================================= *)
(** ** [Galois_Rel_ASPost]: angelic strongest postcondition           *)
(* ================================================================= *)

(** [alpha_asp] wraps a relation as the angelic strongest-postcondition
    arrow; [gamma_asp] forgets the transformer and keeps the stored
    relation.  Both round trips are raw subtype equalities because
    [PureASPostArr] carries an exact iff correspondence and
    [PureASPostArr_eq] promotes pointwise iff to subtype equality. *)

Definition alpha_asp {A B} (R : Rel A B) : PureASPostArr A B :=
  mkASP R.

Definition gamma_asp {A B} (f : PureASPostArr A B) : Rel A B :=
  sp_rel (proj1_sig f).

Lemma adjunction_ASP_Rel {A B}
  (R : Rel A B) (f : PureASPostArr A B) :
  PureASPostArr_le (alpha_asp R) f <-> Rel_le R (gamma_asp f).
Proof.
  unfold PureASPostArr_le, Rel_le, alpha_asp, gamma_asp. split.
  - intros Hord a b HR.
    rewrite <- (asp_singleton (sp_rel (proj1_sig f)) a b).
    apply (proj1 (proj2_sig f (fun a' => a = a') b)).
    apply Hord.
    rewrite (proj2_sig (mkASP R) (fun a' => a = a') b).
    unfold asp. exists a. split; [reflexivity | exact HR].
  - intros Hle pre b Hpt.
    apply (proj2 (proj2_sig f pre b)).
    unfold asp.
    destruct (proj1 (proj2_sig (mkASP R) pre b) Hpt) as [a [Hpre HR]].
    exists a. split; [exact Hpre | apply Hle; exact HR].
Qed.

Definition Galois_Rel_ASPost :=
  {| galois_alpha := @alpha_asp ;
     galois_gamma := @gamma_asp ;
     galois_adjunction := @adjunction_ASP_Rel |}
  : Galois PureASPostArr Rel (@PureASPostArr_le) (@Rel_le).

(** Round trips.  [gamma_asp (alpha_asp R) = R] is definitional.
    [alpha_asp (gamma_asp f) = f] holds by [PureASPostArr_eq]. *)
Lemma gamma_alpha_asp {A B} (R : Rel A B) :
  gamma_asp (alpha_asp R) = R.
Proof. reflexivity. Qed.

Lemma alpha_gamma_asp {A B} (f : PureASPostArr A B) :
  alpha_asp (gamma_asp f) = f.
Proof.
  apply PureASPostArr_eq. intros pre b.
  split.
  - intros H. apply (proj2 (proj2_sig f pre b)).
    apply (proj1 (proj2_sig (alpha_asp (gamma_asp f)) pre b)). exact H.
  - intros H. apply (proj1 (proj2_sig (alpha_asp (gamma_asp f)) pre b)).
    apply (proj1 (proj2_sig f pre b)). exact H.
Qed.

(* ================================================================= *)
(** ** [Galois_Rel_DSLPost]: demonic strongest liberal postcondition  *)
(* ================================================================= *)

(** Symmetric to the ASP connection but using the reverse DSLP order.
    Both round trips are again raw subtype equalities. *)

Definition alpha_dslp {A B} (R : Rel A B) : PureDSLPostArr A B :=
  mkDSLP R.

Definition gamma_dslp {A B} (f : PureDSLPostArr A B) : Rel A B :=
  sp_rel (proj1_sig f).

Lemma adjunction_DSLP_Rel {A B}
  (R : Rel A B) (f : PureDSLPostArr A B) :
  PureDSLPostArr_le (alpha_dslp R) f <-> Rel_le R (gamma_dslp f).
Proof.
  apply PureDSLPostArr_le_iff.
Qed.

Definition Galois_Rel_DSLPost :=
  {| galois_alpha := @alpha_dslp ;
     galois_gamma := @gamma_dslp ;
     galois_adjunction := @adjunction_DSLP_Rel |}
  : Galois PureDSLPostArr Rel (@PureDSLPostArr_le) (@Rel_le).

Lemma gamma_alpha_dslp {A B} (R : Rel A B) :
  gamma_dslp (alpha_dslp R) = R.
Proof. reflexivity. Qed.

Lemma alpha_gamma_dslp {A B} (f : PureDSLPostArr A B) :
  alpha_dslp (gamma_dslp f) = f.
Proof.
  apply PureDSLPostArr_eq. intros pre b.
  split.
  - intros H. apply (proj2 (proj2_sig f pre b)).
    apply (proj1 (proj2_sig (alpha_dslp (gamma_dslp f)) pre b)). exact H.
  - intros H. apply (proj1 (proj2_sig (alpha_dslp (gamma_dslp f)) pre b)).
    apply (proj1 (proj2_sig f pre b)). exact H.
Qed.

(* ================================================================= *)
(** ** [Galois_Rel_PrePost]: relation embedding into Hoare specs      *)
(* ================================================================= *)

(** [alpha] equips a relation with the trivially-true precondition;
    [gamma] forgets the precondition and keeps only the post-relation.

    Under the Hoare order on [PrePost], [True] is the top of [fst]:
    [fst pq ⊆ True] holds for every [pq], so the pre check dissolves
    and the adjunction reduces to [R ⊆ snd pq]. *)
Definition rel_to_pp {A B} (R : Rel A B) : PrePost A B :=
  (fun _ => True, R).

Definition pp_to_rel {A B} (pq : PrePost A B) : Rel A B := snd pq.

Lemma adjunction_Rel_PrePost {A B}
  (R : Rel A B) (pq : PrePost A B) :
  PrePost_le (rel_to_pp R) pq <-> Rel_le R (pp_to_rel pq).
Proof.
  destruct pq as [P R'].
  unfold PrePost_le, Rel_le, rel_to_pp, pp_to_rel; cbn.
  split.
  - intros [_ HR]. exact HR.
  - intros HR. split; [intros _ _; exact I | exact HR].
Qed.

Definition Galois_Rel_PrePost :=
  {| galois_alpha := @rel_to_pp ;
     galois_gamma := @pp_to_rel ;
     galois_adjunction := @adjunction_Rel_PrePost |}
  : Galois PrePost Rel (@PrePost_le) (@Rel_le).

(** Round trips.  [pp_to_rel (rel_to_pp R) = R] is definitional.
    The reverse trip replaces the precondition with [True]; only one
    [PrePost_le] direction holds in general. *)
Lemma pp_to_rel_rel_to_pp {A B} (R : Rel A B) :
  pp_to_rel (rel_to_pp R) = R.
Proof. reflexivity. Qed.

Lemma rel_to_pp_pp_to_rel_deflation {A B} (pq : PrePost A B) :
  PrePost_le (rel_to_pp (pp_to_rel pq)) pq.
Proof.
  destruct pq as [P R].
  unfold rel_to_pp, pp_to_rel, PrePost_le; cbn.
  split; [intros _ _; exact I | intros; assumption].
Qed.

(** [PrePost_eq] round trip holds exactly when the precondition is
    universally true. *)
Lemma rel_to_pp_pp_to_rel_eq_iff {A B} (pq : PrePost A B) :
  PrePost_eq (rel_to_pp (pp_to_rel pq)) pq <->
  forall a, fst pq a.
Proof.
  destruct pq as [P R].
  unfold rel_to_pp, pp_to_rel, PrePost_eq; cbn.
  split.
  - intros [HP _] a. apply HP. exact I.
  - intros HP. split.
    + intros a. split; [intros _; exact (HP a) | intros _; exact I].
    + intros a b. reflexivity.
Qed.

(* ================================================================= *)
(** ** PrePost <-> MonotoneWP: four variants                          *)
(* ================================================================= *)

(** The shared [PrePost (P, R)] carrier is read in this section as a
    no-divergence condition [P] paired with a terminating-outcome
    relation [R].  The four readings differ in how they treat
    totality ([P]) and quantifier direction:

        DWP  (P,R) Q =  P /\ forall b, R b -> Q b    demonic total
        DWLP (P,R) Q =       forall b, R b -> Q b    demonic liberal
        AWP  (P,R) Q =       exists b, R b /\ Q b    angelic total
        AWLP (P,R) Q = ~P \/ exists b, R b /\ Q b    angelic liberal

    DWP and DWLP use the reverse Dijkstra WP order ([MonotoneWP_le]);
    AWP and AWLP use forward implication ([MonotoneWP_ge]).  AWLP
    additionally uses classical logic. *)

(* ----------------------------------------------------------------- *)
(** *** Maps                                                          *)
(* ----------------------------------------------------------------- *)

#[program] Definition alpha_DWP {A B} (pq : PrePost A B) : MonotoneWP A B :=
  fun a Q => fst pq a /\ forall b, snd pq a b -> Q b.
Next Obligation.
  unfold wp_monotone. intros a Q1 Q2 HQ [HP HR].
  split. exact HP. intros b HRb. apply HQ. apply HR. exact HRb.
Qed.

Definition gamma_DWP {A B} (w : MonotoneWP A B) : PrePost A B :=
  ( fun a => proj1_sig w a (fun _ => True)
  , fun a b => forall Q, proj1_sig w a Q -> Q b ).

#[program] Definition alpha_DWLP {A B} (pq : PrePost A B) : MonotoneWP A B :=
  fun a Q => forall b, snd pq a b -> Q b.
Next Obligation.
  unfold wp_monotone. intros a Q1 Q2 HQ HR b HRb. apply HQ. apply HR. exact HRb.
Qed.

Definition gamma_DWLP {A B} (w : MonotoneWP A B) : PrePost A B :=
  ( fun _ => False
  , fun a b => forall Q, proj1_sig w a Q -> Q b ).

#[program] Definition alpha_AWP {A B} (pq : PrePost A B) : MonotoneWP A B :=
  fun a Q => exists b, snd pq a b /\ Q b.
Next Obligation.
  unfold wp_monotone. intros a Q1 Q2 HQ [b [HR HQb]]. exists b.
  split. exact HR. apply HQ. exact HQb.
Qed.

Definition gamma_AWP {A B} (w : MonotoneWP A B) : PrePost A B :=
  ( fun _ => False
  , fun a b => proj1_sig w a (fun b' => b' = b) ).

#[program] Definition alpha_AWLP {A B} (pq : PrePost A B) : MonotoneWP A B :=
  fun a Q => ~ fst pq a \/ exists b, snd pq a b /\ Q b.
Next Obligation.
  unfold wp_monotone. intros a Q1 Q2 HQ.
  intros [Hnp | [b [HR HQb]]].
  - left. exact Hnp.
  - right. exists b. split. exact HR. apply HQ. exact HQb.
Qed.

Definition gamma_AWLP {A B} (w : MonotoneWP A B) : PrePost A B :=
  ( fun a => ~ proj1_sig w a (fun _ => False)
  , fun a b => proj1_sig w a (fun b' => b' = b) ).

(* ----------------------------------------------------------------- *)
(** *** Adjunctions                                                   *)
(* ----------------------------------------------------------------- *)

Lemma adjunction_DWP {A B}
  (pq : PrePost A B) (w : MonotoneWP A B) :
  MonotoneWP_le (alpha_DWP pq) w <->
  PrePost_le pq (gamma_DWP w).
Proof.
  destruct pq as [P R].
  unfold MonotoneWP_le, alpha_DWP, gamma_DWP, WPArr_le, PrePost_le; cbn.
  split.
  - intros H. split.
    + intros a HwTrue. apply (proj1 (H a _ HwTrue)).
    + intros a b HRb Q HwQ. apply (proj2 (H a _ HwQ) b HRb).
  - intros [HP HR] a Q HwQ. split.
    + apply HP.
      apply (proj2_sig w a Q (fun _ => True) (fun b _ => I) HwQ).
    + intros b HRb. apply (HR a b HRb Q HwQ).
Qed.

Lemma adjunction_DWLP {A B}
  (pq : PrePost A B) (w : MonotoneWP A B) :
  MonotoneWP_le (alpha_DWLP pq) w <->
  PrePost_le pq (gamma_DWLP w).
Proof.
  destruct pq as [P R].
  unfold MonotoneWP_le, alpha_DWLP, gamma_DWLP, WPArr_le, PrePost_le; cbn.
  split.
  - intros H. split.
    + intros a Habs. destruct Habs.
    + intros a b HRb Q HwQ. apply (H a _ HwQ b HRb).
  - intros [_ HR] a Q HwQ b HRb. apply (HR a b HRb Q HwQ).
Qed.

Lemma adjunction_AWP {A B}
  (pq : PrePost A B) (w : MonotoneWP A B) :
  MonotoneWP_ge (alpha_AWP pq) w <->
  PrePost_le pq (gamma_AWP w).
Proof.
  destruct pq as [P R].
  unfold MonotoneWP_ge, alpha_AWP, gamma_AWP, WPArr_ge, PrePost_le; cbn.
  split.
  - intros H. split.
    + intros a Habs. exfalso. exact Habs.
    + intros a b HRb. apply H. exists b. split; [exact HRb | reflexivity].
  - intros [_ HR] a Q [b [HRb HQb]].
    assert (Hwb : proj1_sig w a (fun b' => b' = b)).
    { exact (HR a b HRb). }
    apply (proj2_sig w a (fun b' => b' = b) Q).
    + intros b' Heq. subst. exact HQb.
    + exact Hwb.
Qed.

Lemma adjunction_AWLP {A B}
  (pq : PrePost A B) (w : MonotoneWP A B) :
  MonotoneWP_ge (alpha_AWLP pq) w <->
  PrePost_le pq (gamma_AWLP w).
Proof.
  destruct pq as [P R].
  unfold MonotoneWP_ge, alpha_AWLP, gamma_AWLP, WPArr_ge, PrePost_le; cbn.
  split.
  - intros H. split.
    + intros a Hnp.
      apply NNPP. intros HnotP. apply Hnp.
      apply (H a (fun _ => False)). left. exact HnotP.
    + intros a b HRb. apply H. right. exists b.
      split; [exact HRb | reflexivity].
  - intros [HP HR] a Q [Hnp | [b [HRb HQb]]].
    + assert (HwFalse : proj1_sig w a (fun _ => False)).
      { apply NNPP. intros HnotW. apply Hnp. apply HP. exact HnotW. }
      apply (proj2_sig w a (fun _ => False) Q).
      * intros b0 Hfalse. contradiction.
      * exact HwFalse.
    + assert (Hwb : proj1_sig w a (fun b' => b' = b)).
      { exact (HR a b HRb). }
      apply (proj2_sig w a (fun b' => b' = b) Q).
      * intros b' Heq. subst. exact HQb.
      * exact Hwb.
Qed.

Definition Galois_DWP_PrePost :=
  {| galois_alpha := @alpha_DWP ;
     galois_gamma := @gamma_DWP ;
     galois_adjunction := @adjunction_DWP |}
  : Galois MonotoneWP PrePost (@MonotoneWP_le) (@PrePost_le).
Definition Galois_DWLP_PrePost :=
  {| galois_alpha := @alpha_DWLP ;
     galois_gamma := @gamma_DWLP ;
     galois_adjunction := @adjunction_DWLP |}
  : Galois MonotoneWP PrePost (@MonotoneWP_le) (@PrePost_le).
Definition Galois_AWP_PrePost :=
  {| galois_alpha := @alpha_AWP ;
     galois_gamma := @gamma_AWP ;
     galois_adjunction := @adjunction_AWP |}
  : Galois MonotoneWP PrePost (@MonotoneWP_ge) (@PrePost_le).
Definition Galois_AWLP_PrePost :=
  {| galois_alpha := @alpha_AWLP ;
     galois_gamma := @gamma_AWLP ;
     galois_adjunction := @adjunction_AWLP |}
  : Galois MonotoneWP PrePost (@MonotoneWP_ge) (@PrePost_le).

(* ----------------------------------------------------------------- *)
(** *** Round trips: gamma (alpha pq) normalizations                  *)
(* ----------------------------------------------------------------- *)

(** DWP normalization: outside the no-divergence region, the
    post-relation becomes vacuous. *)
Lemma gamma_alpha_DWP {A B} (pq : PrePost A B) :
  PrePost_eq (gamma_DWP (alpha_DWP pq))
             ( fst pq
             , fun a b => fst pq a -> snd pq a b ).
Proof.
  destruct pq as [P R].
  unfold gamma_DWP, alpha_DWP, PrePost_eq; cbn.
  split.
  - intros a. split.
    + intros [HP _]. exact HP.
    + intros HP. split; [exact HP |].
      intros b HR. exact I.
  - intros a b. split.
    + intros HQ HP. apply (HQ (R a)).
      split; [exact HP | intros b' HR; exact HR].
    + intros HR Q [HP HQ]. apply HQ. apply HR. exact HP.
Qed.

Lemma gamma_alpha_DWLP {A B} (pq : PrePost A B) :
  PrePost_eq (gamma_DWLP (alpha_DWLP pq))
             (fun _ => False, snd pq).
Proof.
  destruct pq as [P R].
  unfold gamma_DWLP, alpha_DWLP, PrePost_eq; cbn.
  split.
  - intros a. reflexivity.
  - intros a b. split.
    + intros HQ. apply (HQ (R a)). intros b' HR. exact HR.
    + intros HR Q HQ. apply HQ. exact HR.
Qed.

Lemma gamma_alpha_AWP {A B} (pq : PrePost A B) :
  PrePost_eq (gamma_AWP (alpha_AWP pq))
             (fun _ => False, snd pq).
Proof.
  destruct pq as [P R].
  unfold gamma_AWP, alpha_AWP, PrePost_eq; cbn.
  split.
  - intros a. reflexivity.
  - intros a b. split.
    + intros [b' [HR' Heq]]. subst. exact HR'.
    + intros HR. exists b. split; [exact HR | reflexivity].
Qed.

(** AWLP normalization constructively retains the double negation on
    the no-divergence component.  Classical logic simplifies it to
    the same normalized shape as DWP. *)
Lemma gamma_alpha_AWLP {A B} (pq : PrePost A B) :
  PrePost_eq (gamma_AWLP (alpha_AWLP pq))
             ( fun a => ~~ fst pq a
             , fun a b => ~ fst pq a \/ snd pq a b ).
Proof.
  destruct pq as [P R].
  unfold gamma_AWLP, alpha_AWLP, PrePost_eq; cbn.
  split.
  - intros a. split.
    + intros H HnotP. apply H. left. exact HnotP.
    + intros Hnn [HnotP | [b [_ Hfalse]]].
      * apply Hnn. exact HnotP.
      * exact Hfalse.
  - intros a b. split.
    + intros [HnotP | [b' [HR Heq]]].
      * left. exact HnotP.
      * subst. right. exact HR.
    + intros [Hnp | HR].
      * left. exact Hnp.
      * right. exists b. split; [exact HR | reflexivity].
Qed.

(* ----------------------------------------------------------------- *)
(** *** Representability: alpha (gamma w) fixed points                *)
(* ----------------------------------------------------------------- *)

(** A WP is DWP-representable iff it is completely characterized by
    its [True] acceptance and the postconditions implied by all its
    accepted posts. *)
Definition DWP_representable {A B} (w : MonotoneWP A B) : Prop :=
  forall a Q,
    proj1_sig w a Q <->
    proj1_sig w a (fun _ => True) /\
    (forall b, (forall Q0, proj1_sig w a Q0 -> Q0 b) -> Q b).

Definition DWLP_representable {A B} (w : MonotoneWP A B) : Prop :=
  forall a Q,
    proj1_sig w a Q <->
    forall b, (forall Q0, proj1_sig w a Q0 -> Q0 b) -> Q b.

Definition AWP_representable {A B} (w : MonotoneWP A B) : Prop :=
  forall a Q,
    proj1_sig w a Q <->
    exists b, proj1_sig w a (fun b' => b' = b) /\ Q b.

Definition AWLP_representable {A B} (w : MonotoneWP A B) : Prop :=
  forall a Q,
    proj1_sig w a Q <->
    proj1_sig w a (fun _ => False) \/
    exists b, proj1_sig w a (fun b' => b' = b) /\ Q b.

(** Each representability predicate is equivalent to the corresponding
    [alpha (gamma w)] fixed point. *)
Lemma DWP_representable_iff {A B} (w : MonotoneWP A B) :
  DWP_representable w <->
  (forall a Q,
    proj1_sig w a Q <->
    proj1_sig (alpha_DWP (gamma_DWP w)) a Q).
Proof.
  unfold DWP_representable.
  unfold gamma_DWP, alpha_DWP.
  destruct w as [w Hw]. cbn. split; intro H; intros a Q; [apply H | apply H].
Qed.

Lemma DWLP_representable_iff {A B} (w : MonotoneWP A B) :
  DWLP_representable w <->
  (forall a Q,
    proj1_sig w a Q <->
    proj1_sig (alpha_DWLP (gamma_DWLP w)) a Q).
Proof.
  unfold DWLP_representable.
  unfold gamma_DWLP, alpha_DWLP.
  destruct w as [w Hw]. cbn. split; intro H; intros a Q; [apply H | apply H].
Qed.

Lemma AWP_representable_iff {A B} (w : MonotoneWP A B) :
  AWP_representable w <->
  (forall a Q,
    proj1_sig w a Q <->
    proj1_sig (alpha_AWP (gamma_AWP w)) a Q).
Proof.
  unfold AWP_representable.
  unfold gamma_AWP, alpha_AWP.
  destruct w as [w Hw]. cbn. split; intro H; intros a Q; [apply H | apply H].
Qed.

Lemma AWLP_representable_iff {A B} (w : MonotoneWP A B) :
  AWLP_representable w <->
  (forall a Q,
    proj1_sig w a Q <->
    proj1_sig (alpha_AWLP (gamma_AWLP w)) a Q).
Proof.
  unfold AWLP_representable.
  unfold gamma_AWLP, alpha_AWLP.
  destruct w as [w Hw]. cbn. split; intros H a Q; specialize (H a Q).
  - split.
    + intros HwQ. apply (proj1 H) in HwQ. destruct HwQ as [HwFalse | Hatom].
      * left. intros HnotW. apply HnotW. exact HwFalse.
      * right. exact Hatom.
    + intros [Hnn | Hatom].
      * apply (proj2 H). left. apply NNPP. exact Hnn.
      * apply (proj2 H). right. exact Hatom.
  - split.
    + intros HwQ. apply (proj1 H) in HwQ. destruct HwQ as [Hnn | Hatom].
      * left. apply NNPP. exact Hnn.
      * right. exact Hatom.
    + intros [HwFalse | Hatom].
      * apply (proj2 H). left. intros HnotW. apply HnotW. exact HwFalse.
      * apply (proj2 H). right. exact Hatom.
Qed.

(** Each alpha map lands in its named representable fragment. *)
Lemma alpha_DWP_representable {A B} (pq : PrePost A B) :
  DWP_representable (alpha_DWP pq).
Proof.
  destruct pq as [P R]. unfold DWP_representable, alpha_DWP; cbn.
  intros a Q. split.
  - intros [HP HQ]. split.
    + split; [exact HP | intros b HR; exact I].
    + intros b Hmeet. apply HQ. apply (Hmeet (R a)).
      split; [exact HP | intros b' HR; exact HR].
  - intros [[HP _] Hmeet]. split; [exact HP |].
    intros b HR. apply Hmeet. intros Q0 [_ HQ]. apply HQ. exact HR.
Qed.

Lemma alpha_DWLP_representable {A B} (pq : PrePost A B) :
  DWLP_representable (alpha_DWLP pq).
Proof.
  destruct pq as [P R]. unfold DWLP_representable, alpha_DWLP; cbn.
  intros a Q. split.
  - intros HQ b Hmeet. apply HQ. apply (Hmeet (R a)).
    intros b' HR. exact HR.
  - intros Hmeet b HR. apply Hmeet. intros Q0 HQ. apply HQ. exact HR.
Qed.

Lemma alpha_AWP_representable {A B} (pq : PrePost A B) :
  AWP_representable (alpha_AWP pq).
Proof.
  destruct pq as [P R]. unfold AWP_representable, alpha_AWP; cbn.
  intros a Q. split.
  - intros [b [HR HQ]]. exists b. split; [|exact HQ].
    exists b. split; [exact HR | reflexivity].
  - intros [b [[b' [HR Heq]] HQ]]. subst.
    exists b. split; assumption.
Qed.

Lemma alpha_AWLP_representable {A B} (pq : PrePost A B) :
  AWLP_representable (alpha_AWLP pq).
Proof.
  destruct pq as [P R]. unfold AWLP_representable, alpha_AWLP; cbn.
  intros a Q. split.
  - intros [HnotP | [b [HR HQ]]].
    + left. left. exact HnotP.
    + right. exists b. split; [|exact HQ].
      right. exists b. split; [exact HR | reflexivity].
  - intros [[HnotP | [b [_ Hfalse]]] | [b [[HnotP | [b' [HR Heq]]] HQ]]].
    + left. exact HnotP.
    + contradiction.
    + left. exact HnotP.
    + subst. right. exists b. split; assumption.
Qed.

(** The representability predicates are exactly the pointwise images
    of their corresponding [PrePost] alpha maps. *)
Lemma DWP_representable_exists_iff {A B} (w : MonotoneWP A B) :
  DWP_representable w <->
  exists pq, forall a Q,
    proj1_sig w a Q <-> proj1_sig (alpha_DWP pq) a Q.
Proof.
  split.
  - intros H. exists (gamma_DWP w). apply DWP_representable_iff. exact H.
  - intros [pq H].
    assert (Heq : proj1_sig w = proj1_sig (alpha_DWP pq)).
    { extensionality a. extensionality Q.
      apply propositional_extensionality. apply H. }
    unfold DWP_representable. rewrite Heq.
    exact (alpha_DWP_representable pq).
Qed.

Lemma DWLP_representable_exists_iff {A B} (w : MonotoneWP A B) :
  DWLP_representable w <->
  exists pq, forall a Q,
    proj1_sig w a Q <-> proj1_sig (alpha_DWLP pq) a Q.
Proof.
  split.
  - intros H. exists (gamma_DWLP w). apply DWLP_representable_iff. exact H.
  - intros [pq H].
    assert (Heq : proj1_sig w = proj1_sig (alpha_DWLP pq)).
    { extensionality a. extensionality Q.
      apply propositional_extensionality. apply H. }
    unfold DWLP_representable. rewrite Heq.
    exact (alpha_DWLP_representable pq).
Qed.

Lemma AWP_representable_exists_iff {A B} (w : MonotoneWP A B) :
  AWP_representable w <->
  exists pq, forall a Q,
    proj1_sig w a Q <-> proj1_sig (alpha_AWP pq) a Q.
Proof.
  split.
  - intros H. exists (gamma_AWP w). apply AWP_representable_iff. exact H.
  - intros [pq H].
    assert (Heq : proj1_sig w = proj1_sig (alpha_AWP pq)).
    { extensionality a. extensionality Q.
      apply propositional_extensionality. apply H. }
    unfold AWP_representable. rewrite Heq.
    exact (alpha_AWP_representable pq).
Qed.

Lemma AWLP_representable_exists_iff {A B} (w : MonotoneWP A B) :
  AWLP_representable w <->
  exists pq, forall a Q,
    proj1_sig w a Q <-> proj1_sig (alpha_AWLP pq) a Q.
Proof.
  split.
  - intros H. exists (gamma_AWLP w). apply AWLP_representable_iff. exact H.
  - intros [pq H].
    assert (Heq : proj1_sig w = proj1_sig (alpha_AWLP pq)).
    { extensionality a. extensionality Q.
      apply propositional_extensionality. apply H. }
    unfold AWLP_representable. rewrite Heq.
    exact (alpha_AWLP_representable pq).
Qed.

(* ================================================================= *)
(** ** [Galois_WP_RelPrePost]: RelPrePost embedding of WP             *)
(* ================================================================= *)

(** [alpha] sends a WP [w] to the validator
    [fun P R => forall a, P a -> w a (R a)].  [gamma] sends a
    validator [r] to the WP [fun a Q => project_wp r a Q].

    The adjunction holds for arbitrary well-formed [r] and monotone
    [w].  The WP round trip is pointwise iff; the reverse trip
    identifies a validator with its projection closure under
    [RelPrePost_arrow_eq]. *)

#[program] Definition alpha_wp_rpp {A B} (w : MonotoneWP A B) : WFRelPrePost A B :=
  fun P R => forall a, P a -> proj1_sig w a (R a).
Next Obligation.
  unfold RelPrePost_wf, project_wp.
  intros a Q1 Q2 HQ [P [R [HE [HPa HRiff]]]].
  exists P, (fun a' b => R a' b \/ (a' = a /\ Q2 b)).
  split; [|split].
  - intros a' HPa'.
    assert (HRw : proj1_sig w a' (R a')).
    { apply HE. exact HPa'. }
    apply (proj2_sig w a' (R a') (fun b0 => R a' b0 \/ (a' = a /\ Q2 b0))).
    + intros b0 HRb. left. exact HRb.
    + exact HRw.
  - exact HPa.
  - intros b0. split.
    + intros [HRb | [Heq HQ2b]].
      * apply HQ. apply HRiff. exact HRb.
      * exact HQ2b.
    + intros HQ2b. right. split; [reflexivity | exact HQ2b].
Qed.

#[program] Definition gamma_rpp_wp {A B} (r : WFRelPrePost A B) : MonotoneWP A B :=
  fun a Q => project_wp (proj1_sig r) a Q.
Next Obligation.
  exact (proj2_sig r).
Qed.

Lemma adjunction_WP_RPP {A B}
  (w : MonotoneWP A B) (r : WFRelPrePost A B) :
  WFRelPrePost_le (alpha_wp_rpp w) r <->
  MonotoneWP_le w (gamma_rpp_wp r).
Proof.
  unfold WFRelPrePost_le, alpha_wp_rpp, gamma_rpp_wp,
         RelPrePost_le, MonotoneWP_le, WPArr_le; cbn.
  split.
  - intros H a Q [P [R [Hr [HPa Hiff]]]].
    specialize (H P R Hr a HPa).
    replace Q with (R a); [exact H|].
    extensionality b. apply propositional_extensionality. apply Hiff.
  - intros H P R Hr a HPa.
    apply H. exists P, R. split; [exact Hr | split; [exact HPa | reflexivity]].
Qed.

Definition Galois_WP_RelPrePost :=
  {| galois_alpha := @alpha_wp_rpp ;
     galois_gamma := @gamma_rpp_wp ;
     galois_adjunction := @adjunction_WP_RPP |}
  : Galois WFRelPrePost MonotoneWP (@WFRelPrePost_le) (@MonotoneWP_le).

(** Round trips.  WP-side: [gamma (alpha w)] agrees pointwise with [w].
    RPP-side: the closure [alpha (gamma r)] is
    [RelPrePost_arrow_eq]-equivalent to [r] and below it in the order. *)
Lemma gamma_alpha_wp_rpp_iff {A B} (w : MonotoneWP A B) :
  forall a Q,
    project_wp (proj1_sig (alpha_wp_rpp w)) a Q <->
    proj1_sig w a Q.
Proof.
  intros a Q. split.
  - intros [P [R [Hr [HPa Hiff]]]].
    apply (proj2_sig w a (R a) Q).
    + intros b HR. apply (proj1 (Hiff b)). exact HR.
    + exact (Hr a HPa).
  - intros HwQ.
    exists (fun a' => a = a'), (fun _ b => Q b).
    split; [|split].
    + intros a' ->. exact HwQ.
    + reflexivity.
    + intros b. reflexivity.
Qed.

Lemma alpha_gamma_rpp_rpp_arrow_eq {A B} (r : WFRelPrePost A B) :
  forall a Q,
    project_wp (proj1_sig (alpha_wp_rpp (gamma_rpp_wp r))) a Q <->
    project_wp (proj1_sig r) a Q.
Proof.
  intros a Q. change
    (project_wp (proj1_sig (alpha_wp_rpp (gamma_rpp_wp r))) a Q <->
     proj1_sig (gamma_rpp_wp r) a Q).
  apply gamma_alpha_wp_rpp_iff.
Qed.

Lemma alpha_gamma_rpp_deflation {A B} (r : WFRelPrePost A B) :
  WFRelPrePost_le (alpha_wp_rpp (gamma_rpp_wp r)) r.
Proof.
  unfold WFRelPrePost_le, RelPrePost_le, alpha_wp_rpp, gamma_rpp_wp; cbn.
  intros P R Hr a HPa.
  exists P, R. split; [exact Hr |].
  split; [exact HPa | reflexivity].
Qed.

(* ================================================================= *)
(** ** Obstruction: SPost <-> RelPrePost in the binary setting        *)
(* ================================================================= *)

(** In DM4All (unary types), [SPost] embeds into [RelPrePost] via a
    Galois connection.  The two direct binary generalizations below
    fail for distinct reasons: the universal gamma violates SP
    monotonicity, while the existential maps require an invalid
    exchange of validator and witness quantifiers.

    Two natural binary lifts are proven to fail by counterexample
    below. *)

(* ----------------------------------------------------------------- *)
(** *** Universal variant: gamma is not monotone                      *)
(* ----------------------------------------------------------------- *)

(** Candidate maps:

    [alpha_uni sp P R := forall a b, P a -> sp P b -> R a b]
    [gamma_uni r  P b := forall R0, r P R0 -> forall a, P a -> R0 a b]

    The adjunction holds, but [gamma_uni] is not monotone in [P], so
    it does not land in the well-formed raw SP transformers. *)
Definition alpha_uni {A B} (sp : SPost_pt A B) : RelPrePost A B :=
  fun P R => forall a b, P a -> sp P b -> R a b.

Definition gamma_uni {A B} (r : RelPrePost A B)
  (P : A -> Prop) (b : B) : Prop :=
  forall R0, r P R0 -> forall a, P a -> R0 a b.

Definition r_all (A B : Type) : RelPrePost A B :=
  fun _ _ => True.

Lemma r_all_wf {A B} : RelPrePost_wf (r_all A B).
Proof.
  unfold RelPrePost_wf, project_wp, r_all.
  intros a Q1 Q2 HQ Hproject.
  exists (fun _ => True), (fun _ b => Q2 b).
  split; [exact I |]. split; [exact I | intros b; reflexivity].
Qed.

Lemma adjunction_uni {A B} (sp : SPost_pt A B) (r : RelPrePost A B) :
  RelPrePost_le (alpha_uni sp) r <-> SPost_le sp (gamma_uni r).
Proof.
  unfold RelPrePost_le, alpha_uni, SPost_le, gamma_uni. split.
  - intros H P b Hsp R0 Hr a HPa.
    exact (H P R0 Hr a b HPa Hsp).
  - intros H P R Hr a b HPa Hsp.
    exact (H P b Hsp R Hr a HPa).
Qed.

Lemma gamma_uni_not_monotone :
  ~ sp_monotone (gamma_uni (r_all unit bool)).
Proof.
  unfold sp_monotone, gamma_uni, r_all. intros Hmon.
  assert (Hincl : forall a : unit, (fun _ => False) a -> (fun _ => True) a).
  { intros a _. exact I. }
  assert (Hbot : forall (R0 : Rel unit bool) (_ : True) (a : unit),
                   (fun _ => False) a -> R0 a false).
  { intros R0 _ a Habs. destruct Habs. }
  assert (Htop := Hmon (fun _ => False) (fun _ => True) Hincl false Hbot).
  exact (Htop (fun _ _ => False) I tt I).
Qed.

(* ----------------------------------------------------------------- *)
(** *** Existential variant: adjunction fails                        *)
(* ----------------------------------------------------------------- *)

(** Candidate maps:

    [alpha_ex sp P R := forall b, sp P b -> exists a, P a /\ R a b]
    [gamma_ex  r P b := exists a, P a /\ forall R0, r P R0 -> R0 a b]

    The adjunction fails: the left side permits a witness [a] that
    depends on [R0], while the right side requires a single uniform
    [a] for every validated [R0].  For the concrete [r_two] below,
    [gamma_ex r_two] is monotone, so that failure is not caused by the
    raw SP well-formedness boundary.

    Concrete failure: take [A = bool], [B = unit], and an [sp] that
    requires both inputs to satisfy the precondition:

        sp_both P tt := P false /\ P true

    Let [r_two] accept a relation iff at least one input relates to
    [tt]:

        r_two P R := R false tt \/ R true tt

    Then [r_two] accepts both [R_false] (true only at [false]) and
    [R_true] (true only at [true]) for every [P].  The left adjunction
    side [RelPrePost_le (alpha_ex sp_both) r_two] holds because for
    each accepted [R] a witness exists.  The right side
    [SPost_le sp_both (gamma_ex r_two)] fails because no single [a]
    works for both [R_false] and [R_true]. *)

Definition alpha_ex {A B} (sp : SPost_pt A B) : RelPrePost A B :=
  fun P R => forall b, sp P b -> exists a, P a /\ R a b.

Definition gamma_ex {A B} (r : RelPrePost A B) : SPost_pt A B :=
  fun P b => exists a, P a /\ forall R0, r P R0 -> R0 a b.

Lemma alpha_ex_wf {A B} (sp : SPost_pt A B) :
  RelPrePost_wf (alpha_ex sp).
Proof.
  unfold RelPrePost_wf, project_wp, alpha_ex.
  intros a Q1 Q2 HQ [P [R [Halpha [HPa Hiff]]]].
  exists P, (fun a' b => R a' b \/ (a' = a /\ Q2 b)).
  split; [|split].
  - intros b Hsp. destruct (Halpha b Hsp) as [a' [HP HR]].
    exists a'. split; [exact HP | left; exact HR].
  - exact HPa.
  - intros b. split.
    + intros [HR | [_ HQ2]].
      * apply HQ. apply Hiff. exact HR.
      * exact HQ2.
    + intros HQ2. right. split; [reflexivity | exact HQ2].
Qed.

Definition sp_both : SPost_pt bool unit :=
  fun P _ => P false /\ P true.

Definition r_two : RelPrePost bool unit :=
  fun _ R => R false tt \/ R true tt.

Definition R_false : Rel bool unit :=
  fun a _ => match a with false => True | true => False end.

Definition R_true : Rel bool unit :=
  fun a _ => match a with false => False | true => True end.

Lemma r_two_R_false : forall P, r_two P R_false.
Proof. intros P. left. exact I. Qed.

Lemma r_two_R_true : forall P, r_two P R_true.
Proof. intros P. right. exact I. Qed.

Lemma sp_both_monotone : sp_monotone sp_both.
Proof.
  unfold sp_monotone, sp_both. intros P1 P2 Hsub b [HPfalse HPtrue].
  split; apply Hsub; assumption.
Qed.

Lemma r_two_wf : RelPrePost_wf r_two.
Proof.
  unfold RelPrePost_wf, project_wp, r_two.
  intros a Q1 Q2 HQ [P [R [Hr [HPa Hiff]]]]. destruct a.
  - exists P, (fun (a' : bool) (_ : unit) => if a' then Q2 tt else True).
    split; [left; exact I |].
    split; [exact HPa | intros []; reflexivity].
  - exists P, (fun (a' : bool) (_ : unit) => if a' then True else Q2 tt).
    split; [right; exact I |].
    split; [exact HPa | intros []; reflexivity].
Qed.

Lemma alpha_ex_sp_both_le_r_two :
  RelPrePost_le (alpha_ex sp_both) r_two.
Proof.
  unfold RelPrePost_le, alpha_ex, sp_both, r_two.
  intros P R HR b [HPfalse HPtrue]. destruct b.
  destruct HR as [HRfalse | HRtrue].
  - exists false. split; assumption.
  - exists true. split; assumption.
Qed.

(** This counterexample does not rely on a monotonicity failure:
    [gamma_ex r_two] is empty and therefore monotone. *)
Lemma gamma_ex_r_two_monotone : sp_monotone (gamma_ex r_two).
Proof.
  unfold sp_monotone, gamma_ex. intros P1 P2 Hsub b [a [HP Hall]].
  destruct b, a.
  - exfalso. exact (Hall R_false (r_two_R_false P1)).
  - exfalso. exact (Hall R_true (r_two_R_true P1)).
Qed.

(** The existential gamma at [Ptop] is false because no [a] works for
    both accepted relations. *)
Lemma gamma_ex_r_two_false :
  ~ gamma_ex r_two (fun _ : bool => True) tt.
Proof.
  unfold gamma_ex.
  intros [a [_ Hall]]. destruct a.
  - exact (Hall R_false (r_two_R_false (fun _ => True))).
  - exact (Hall R_true (r_two_R_true (fun _ => True))).
Qed.

Lemma not_sp_both_le_gamma_ex_r_two :
  ~ SPost_le sp_both (gamma_ex r_two).
Proof.
  intros H. apply gamma_ex_r_two_false. apply H. split; exact I.
Qed.

Lemma existential_adjunction_fails :
  RelPrePost_le (alpha_ex sp_both) r_two /\
  ~ SPost_le sp_both (gamma_ex r_two).
Proof.
  split.
  - apply alpha_ex_sp_both_le_r_two.
  - apply not_sp_both_le_gamma_ex_r_two.
Qed.

Lemma existential_counterexample_well_formed :
  sp_monotone sp_both /\
  RelPrePost_wf r_two /\
  RelPrePost_wf (alpha_ex sp_both).
Proof.
  split; [apply sp_both_monotone |].
  split; [apply r_two_wf | apply alpha_ex_wf].
Qed.

(** These results reject only the two candidate lifts above, not every
    possible connection between the binary carriers.  The existential
    failure is exactly the invalid exchange
    [forall R0, exists a] to [exists a, forall R0]. *)
