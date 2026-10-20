(** * The Galois transpose between [ASPArr] and [DWLPArr]

    For one program, the angelic strongest postcondition and the demonic
    weakest liberal precondition form a Galois connection,
    [asp P ⊆ Q <-> P ⊆ dwlp Q].  [GaloisRel] states it for a raw SP and a
    raw WP transformer between the same types.  Read as a relation between
    the two arrows:

    - it is closed under [arr_pure], [arr_comp] and [arr_first]
      ([galois_pure], [galois_comp], [galois_first]);
    - it relates only join-preserving SP transformers to meet-preserving WP
      transformers ([galois_left_join], [galois_right_meet]);
    - adjoints are unique ([galois_unique_sp], [galois_unique_wp]).

    So it is the graph of an isomorphism: [dwlpOfASP] sends an [ASPArr] to
    its right adjoint, [aspOfDWLP] a [DWLPArr] to its left adjoint
    ([galois_iff_dwlpOfASP], [galois_iff_aspOfDWLP]).  Both maps are arrow
    morphisms, [arr_app] included, and so preserve [ret_arrow] and
    [bind_arrow] at every input.

    On relations the transpose takes the ASP of a relation to its DWLP
    ([dwlpOfASP_ofRel]): that is the Galois connection of each program.  The
    other Galois connection, awp ⊣ dslp, is [GaloisRel] with the two types
    exchanged, between the ASP and the DWLP of the converse relation
    ([galois_awp_dslp]). *)

From Coq Require Import Morphisms RelationClasses Setoid.
From Incorrectness.Classes Require Import Arrow ArrowMorphism.
From Incorrectness.Taxonomy.Arrows Require Import SPostArr SPArr WPArr.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPArrowCore DWLPArrowCore.

(* ================================================================= *)
(** ** The relation                                                  *)
(* ================================================================= *)

Definition GaloisRel {A B} (s : SPArrT A B) (w : WPArr A B) : Prop :=
  forall (P : A -> Prop) (Q : B -> Prop),
    (forall b, s P b -> Q b) <-> (forall a, P a -> w a Q).

Section Closure.

  Lemma galois_pure {A B} (h : A -> B) :
    GaloisRel (fun P b => exists a, P a /\ h a = b) (fun a Q => Q (h a)).
  Proof.
    intros P Q. split.
    - intros H a Ha. apply H. exists a. auto.
    - intros H b [a [Ha <-]]. exact (H a Ha).
  Qed.

  Lemma galois_comp {A B C} (s1 : SPArrT A B) (w1 : WPArr A B)
        (s2 : SPArrT B C) (w2 : WPArr B C) :
    GaloisRel s1 w1 -> GaloisRel s2 w2 ->
    GaloisRel (fun P c => s2 (s1 P) c) (fun a Q => w1 a (fun b => w2 b Q)).
  Proof. intros H1 H2 P Q. rewrite (H2 (s1 P) Q). apply H1. Qed.

  Lemma galois_first {A B C} (s : SPArrT A B) (w : WPArr A B) :
    GaloisRel s w ->
    GaloisRel (fun (P : A * C -> Prop) bc => s (fun a => P (a, snd bc)) (fst bc))
              (fun ac Q => w (fst ac) (fun b => Q (b, snd ac))).
  Proof.
    intros H P Q. split.
    - intros Hs [a c] Ha. cbn [fst snd].
      apply (proj1 (H (fun a => P (a, c)) (fun b => Q (b, c)))); [| exact Ha ].
      intros b Hb. exact (Hs (b, c) Hb).
    - intros Hw [b c] Hb. cbn [fst snd] in Hb.
      apply (proj2 (H (fun a => P (a, c)) (fun b => Q (b, c)))); [| exact Hb ].
      intros a Ha. exact (Hw (a, c) Ha).
  Qed.

  Lemma galois_unique_sp {A B} (s1 s2 : SPArrT A B) (w : WPArr A B) :
    GaloisRel s1 w -> GaloisRel s2 w -> forall P b, s1 P b <-> s2 P b.
  Proof.
    intros H1 H2 P b. split; intro Hs.
    - exact (proj2 (H1 P (s2 P)) (proj1 (H2 P (s2 P)) (fun _ H => H)) b Hs).
    - exact (proj2 (H2 P (s1 P)) (proj1 (H1 P (s1 P)) (fun _ H => H)) b Hs).
  Qed.

  Lemma galois_unique_wp {A B} (s : SPArrT A B) (w1 w2 : WPArr A B) :
    GaloisRel s w1 -> GaloisRel s w2 -> forall a Q, w1 a Q <-> w2 a Q.
  Proof.
    intros H1 H2 a Q.
    transitivity (forall b, s (fun x => x = a) b -> Q b).
    - rewrite (H1 (fun x => x = a) Q).
      split; [ intros H x ->; exact H | intro H; exact (H a eq_refl) ].
    - rewrite (H2 (fun x => x = a) Q).
      split; [ intro H; exact (H a eq_refl) | intros H x ->; exact H ].
  Qed.

  (** A left adjoint preserves joins, so it is an [ASPArr]. *)
  Lemma galois_left_join {A B} (s : SPArrT A B) (w : WPArr A B) :
    GaloisRel s w -> asp_join s.
  Proof.
    intros H P b. split.
    - intro Hs.
      apply (proj2 (H P (fun b => exists a, P a /\ s (fun x => x = a) b))); [| exact Hs ].
      intros a Ha.
      apply (proj1 (H (fun x => x = a) (fun b => exists a, P a /\ s (fun x => x = a) b)));
        [| reflexivity ].
      intros b' Hb'. exists a. exact (conj Ha Hb').
    - intros [a [Ha Hs]].
      refine (proj2 (H (fun x => x = a) (s P)) _ b Hs).
      intros x ->. exact (proj1 (H P (s P)) (fun _ h => h) a Ha).
  Qed.

  (** A right adjoint preserves meets, so it is a [DWLPArr]. *)
  Lemma galois_right_meet {A B} (s : SPArrT A B) (w : WPArr A B) :
    GaloisRel s w -> dwlp_meet w.
  Proof.
    intros H a Q. split.
    - intros Hw b Hr. exact (Hr Q Hw).
    - intro Hall.
      apply (proj1 (H (fun x => x = a) Q)); [| reflexivity ].
      intros b Hs. apply Hall. intros Q' HQ'.
      refine (proj2 (H (fun x => x = a) Q') _ b Hs).
      intros x ->. exact HQ'.
  Qed.

End Closure.

(* ================================================================= *)
(** ** The transpose and its inverse                                 *)
(* ================================================================= *)

Lemma galois_asp_raw {A B} (f : ASPArr A B) :
  GaloisRel (getASPArr f) (fun a Q => forall b, f (fun x => x = a) b -> Q b).
Proof.
  intros P Q. split.
  - intros H a Ha b Hf. apply H.
    refine (getASPArr_mono f (fun x => x = a) P b _ Hf).
    intros x ->. exact Ha.
  - intros H b Hf. apply getASPArr_join in Hf. destruct Hf as [a [Ha Hf]].
    exact (H a Ha b Hf).
Qed.

Lemma galois_dwlp_raw {A B} (w : DWLPArr A B) :
  GaloisRel (fun P b => exists a, P a /\ dwlpRelT (getDWLPArr w) a b) (getDWLPArr w).
Proof.
  intros P Q. split.
  - intros H a Ha. apply (getDWLPArr_meet w). intros b Hr. apply H. exists a. auto.
  - intros H b [a [Ha Hr]]. exact (Hr Q (H a Ha)).
Qed.

(** The right adjoint of an ASP transformer. *)
#[program] Definition dwlpOfASP {A B} (f : ASPArr A B) : DWLPArr A B :=
  fun a Q => forall b, f (fun x => x = a) b -> Q b.
Next Obligation. exact (dwlp_meet_hom _ (galois_right_meet _ _ (galois_asp_raw f))). Qed.

(** The left adjoint of a DWLP transformer. *)
#[program] Definition aspOfDWLP {A B} (w : DWLPArr A B) : ASPArr A B :=
  fun P b => exists a, P a /\ dwlpRelT (getDWLPArr w) a b.
Next Obligation. exact (asp_join_hom _ (galois_left_join _ _ (galois_dwlp_raw w))). Qed.

Lemma galois_dwlpOfASP {A B} (f : ASPArr A B) :
  GaloisRel (getASPArr f) (getDWLPArr (dwlpOfASP f)).
Proof. exact (galois_asp_raw f). Qed.

Lemma galois_aspOfDWLP {A B} (w : DWLPArr A B) :
  GaloisRel (getASPArr (aspOfDWLP w)) (getDWLPArr w).
Proof. exact (galois_dwlp_raw w). Qed.

(** The relation is the graph of [dwlpOfASP], and of its inverse. *)
Theorem galois_iff_dwlpOfASP {A B} (f : ASPArr A B) (w : DWLPArr A B) :
  GaloisRel (getASPArr f) (getDWLPArr w) <-> arrow_eq (dwlpOfASP f) w.
Proof.
  cbn [arrow_eq ArrowEq_DWLPArr]. unfold DWLPArr_eq. split.
  - intros H a Q. exact (galois_unique_wp _ _ _ (galois_dwlpOfASP f) H a Q).
  - intros H P Q. rewrite (galois_dwlpOfASP f P Q).
    split; intros Hw a Ha; apply H; exact (Hw a Ha).
Qed.

Theorem galois_iff_aspOfDWLP {A B} (f : ASPArr A B) (w : DWLPArr A B) :
  GaloisRel (getASPArr f) (getDWLPArr w) <-> arrow_eq f (aspOfDWLP w).
Proof.
  cbn [arrow_eq ArrowEq_ASPArr]. unfold ASPArr_eq. split.
  - intros H P b. exact (galois_unique_sp _ _ _ H (galois_aspOfDWLP w) P b).
  - intros H P Q. rewrite <- (galois_aspOfDWLP w P Q).
    split; intros Hs b Hb; apply Hs; apply H; exact Hb.
Qed.

Lemma aspOfDWLP_dwlpOfASP {A B} (f : ASPArr A B) : arrow_eq (aspOfDWLP (dwlpOfASP f)) f.
Proof. symmetry. apply galois_iff_aspOfDWLP. apply galois_dwlpOfASP. Qed.

Lemma dwlpOfASP_aspOfDWLP {A B} (w : DWLPArr A B) : arrow_eq (dwlpOfASP (aspOfDWLP w)) w.
Proof. apply galois_iff_dwlpOfASP. apply galois_aspOfDWLP. Qed.

Lemma dwlpOfASP_proper {A B} : Proper (arrow_eq ==> arrow_eq) (@dwlpOfASP A B).
Proof.
  intros f f' Hf. cbn [arrow_eq ArrowEq_ASPArr ArrowEq_DWLPArr] in *.
  unfold ASPArr_eq in Hf. unfold DWLPArr_eq. intros a Q. cbn.
  split; intros H b Hb; apply H; apply Hf; exact Hb.
Qed.

Lemma aspOfDWLP_proper {A B} : Proper (arrow_eq ==> arrow_eq) (@aspOfDWLP A B).
Proof.
  intros w w' Hw. cbn [arrow_eq ArrowEq_ASPArr ArrowEq_DWLPArr] in *.
  unfold DWLPArr_eq in Hw. unfold ASPArr_eq. intros P b. cbn. unfold dwlpRelT.
  split; intros [a [Ha Hr]]; exists a; split; try exact Ha;
    intros Q HQ; apply Hr; apply Hw; exact HQ.
Qed.

(* ================================================================= *)
(** ** Both maps are arrow morphisms                                 *)
(* ================================================================= *)

(** [arr_app] of [ASPArr] is related to [arr_app] of [DWLPArr] after the
    arrow it carries is transposed, in either direction. *)
Lemma galois_app {A B} :
  GaloisRel (getASPArr (@appASP A B)) (fun fa Q => dwlpOfASP (fst fa) (snd fa) Q).
Proof.
  intros P Q. cbn. split.
  - intros H [f a] Ha b Hf. apply H. exists f, a. auto.
  - intros H b [f [a [Ha Hf]]]. exact (H (f, a) Ha b Hf).
Qed.

Lemma galois_app_inv {A B} :
  GaloisRel (getASPArr (arr_comp (arr_pure (fun fa : DWLPArr A B * A =>
                                                (aspOfDWLP (fst fa), snd fa)))
                                 arr_app))
            (getDWLPArr (@appDWLP A B)).
Proof.
  intros P Q. cbn. split.
  - intros H [w a] Ha. cbn. apply (getDWLPArr_meet w). intros b Hr. apply H.
    exists (aspOfDWLP w), a. split; [ exists (w, a); auto |].
    cbn. exists a. auto.
  - intros H b [f [a [[[w a'] [Hp Heq]] Hf]]]. cbn in Heq.
    injection Heq as <- <-. cbn in Hf. destruct Hf as [x [<- Hr]].
    exact (Hr Q (H (w, x) Hp)).
Qed.

#[global] Instance ArrowMorphism_dwlpOfASP :
  ArrowMorphism ASPArr DWLPArr (fun A B => @dwlpOfASP A B).
Proof.
  constructor; cbv beta.
  - intros A B. apply dwlpOfASP_proper.
  - intros A B h. apply galois_iff_dwlpOfASP. exact (galois_pure h).
  - intros A B C f g. apply galois_iff_dwlpOfASP.
    exact (galois_comp _ _ _ _ (galois_dwlpOfASP f) (galois_dwlpOfASP g)).
  - intros A B C f. apply galois_iff_dwlpOfASP. exact (galois_first _ _ (galois_dwlpOfASP f)).
Qed.

#[global] Instance ArrowApplyMorphism_dwlpOfASP :
  ArrowApplyMorphism ASPArr DWLPArr (fun A B => @dwlpOfASP A B).
Proof. constructor. intros A B. cbv beta. apply galois_iff_dwlpOfASP. exact galois_app. Qed.

#[global] Instance ArrowMorphism_aspOfDWLP :
  ArrowMorphism DWLPArr ASPArr (fun A B => @aspOfDWLP A B).
Proof.
  constructor; cbv beta.
  - intros A B. apply aspOfDWLP_proper.
  - intros A B h. symmetry. apply galois_iff_aspOfDWLP. exact (galois_pure h).
  - intros A B C f g. symmetry. apply galois_iff_aspOfDWLP.
    exact (galois_comp _ _ _ _ (galois_aspOfDWLP f) (galois_aspOfDWLP g)).
  - intros A B C f. symmetry. apply galois_iff_aspOfDWLP.
    exact (galois_first _ _ (galois_aspOfDWLP f)).
Qed.

#[global] Instance ArrowApplyMorphism_aspOfDWLP :
  ArrowApplyMorphism DWLPArr ASPArr (fun A B => @aspOfDWLP A B).
Proof.
  constructor. intros A B. cbv beta. symmetry. apply galois_iff_aspOfDWLP. exact galois_app_inv.
Qed.

(** Hence monad morphisms of [Monad_Arrow] at every input. *)
Corollary dwlpOfASP_ret {I A} (a : A) :
  arrow_eq (dwlpOfASP (ret_arrow ASPArr I a)) (ret_arrow DWLPArr I a).
Proof. exact (morph_ret_arrow ASPArr DWLPArr (fun A B => @dwlpOfASP A B) I a). Qed.

Corollary dwlpOfASP_bind {I A B} (m : ASPArr I A) (k : A -> ASPArr I B) :
  arrow_eq (dwlpOfASP (bind_arrow ASPArr I m k))
           (bind_arrow DWLPArr I (dwlpOfASP m) (fun a => dwlpOfASP (k a))).
Proof. exact (morph_bind_arrow ASPArr DWLPArr (fun A B => @dwlpOfASP A B) I m k). Qed.

(* ================================================================= *)
(** ** On relations: the two Galois connections of a program         *)
(* ================================================================= *)

Lemma dwlpOfASP_ofRel {A B} (R : A -> B -> Prop) :
  arrow_eq (dwlpOfASP (ofRelASPArr R)) (ofRelDWLPArr R).
Proof.
  cbn [arrow_eq ArrowEq_DWLPArr]. unfold DWLPArr_eq. intros a Q. cbn. split.
  - intros H b Hr. apply H. exists a. auto.
  - intros H b [x [-> Hr]]. exact (H b Hr).
Qed.

(** asp ⊣ dwlp. *)
Corollary galois_ofRel {A B} (R : A -> B -> Prop) :
  GaloisRel (getASPArr (ofRelASPArr R)) (getDWLPArr (ofRelDWLPArr R)).
Proof. apply galois_iff_dwlpOfASP. apply dwlpOfASP_ofRel. Qed.

(** awp ⊣ dslp: the angelic weakest precondition and the demonic strongest
    liberal postcondition of [R] are the ASP and the DWLP of its converse. *)
Corollary galois_awp_dslp {A B} (R : A -> B -> Prop) :
  GaloisRel (fun (Q : B -> Prop) a => exists b, Q b /\ R a b)
            (fun b (P : A -> Prop) => forall a, R a b -> P a).
Proof. exact (galois_ofRel (fun b a => R a b)). Qed.
