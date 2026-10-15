(** * Direct components of DSP and ASLP arrows (paper, Section 3.1 and
      Appendix D).

    [DSPASLPArr.v] splits a DSP or ASLP arrow into an ASP and a DSLP part
    through the relation it recovers ([aspPart], [dslpPart], [aspPartA],
    [dslpPartA]).  The paper computes the same components directly from the
    transformer, by evaluating it at [True], at [False], and at the
    complement of the precondition.  This file states those formulas, proves
    that a DSP arrow is the conjunction and an ASLP arrow the disjunction of
    them, types them as ASP and DSLP arrows, and shows that they agree with
    the relation-based parts.  At input [unit], with the precondition
    [fun _ => p], the formulas are the paper's.

    The DSP decomposition [dsp_split_direct] is constructive, and so are the
    monotonicity of all four components, the strictness of both ASP
    components, and the disjunctivity of [aspOfASLP].  The ASLP
    decomposition, the remaining healthiness conditions, and the agreement
    with the relation-based parts use excluded middle. *)

From Coq Require Import Classical_Prop.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Import PredicateTransformerProperties SPostArr DSPASLPArr.

Local Obligation Tactic := idtac.

(* ================================================================= *)
(** ** Components of a DSP arrow                                     *)
(* ================================================================= *)

Section DSPComponents.
  Context {X Y : Type}.

  (** [y] is produced, and not only from inputs outside [P]. *)
  Definition aspOfDSP (w : DSPArr X Y) : SPArrT X Y :=
    fun P y => getDSP w (fun _ => True) y /\ ~ getDSP w (fun x => ~ P x) y.

  (** [y] is produced only from inputs in [P], or not produced at all. *)
  Definition dslpOfDSP (w : DSPArr X Y) : SPArrT X Y :=
    fun P y => getDSP w P y \/ ~ getDSP w (fun _ => True) y.

  (** Constructive: it uses only monotonicity, strictness, and binary
      conjunctivity of [w]. *)
  Theorem dsp_split_direct (w : DSPArr X Y) P y :
    getDSP w P y <-> aspOfDSP w P y /\ dslpOfDSP w P y.
  Proof.
    destruct (proj2_sig w) as [Hm [Hs Hc]].
    unfold aspOfDSP, dslpOfDSP, getDSP. split.
    - intro Hw. split; [split | left; exact Hw].
      + exact (Hm P (fun _ => True) (fun _ _ => I) y Hw).
      + intro Hn. apply (Hs y).
        assert (Hboth : proj1_sig w (fun x => forall b : bool, if b then P x else ~ P x) y).
        { apply (proj2 (Hc bool (inhabits true) (fun b x => if b then P x else ~ P x) y)).
          intros [|]; [exact Hw | exact Hn]. }
        exact (Hm (fun x => forall b : bool, if b then P x else ~ P x) (fun _ => False)
                 (fun x H => H false (H true)) y Hboth).
    - intros [[Htop _] [Hw | Hn]]; [exact Hw | exact (False_ind _ (Hn Htop))].
  Qed.

  Lemma aspOfDSP_aspPart (w : DSPArr X Y) P y :
    aspOfDSP w P y <-> aspPart w P y.
  Proof.
    destruct (proj2_sig w) as [Hm _].
    unfold aspOfDSP, aspPart, aspPartArr, getASPArr, mkASPArr, aspOf, asp. cbn.
    split.
    - intros [Htop Hn]. apply NNPP. intro Hno. apply Hn.
      apply (proj2 (dspRel_spec w _ y)).
      destruct (proj1 (dspRel_spec w _ y) Htop) as [[x0 [_ Hx0]] _].
      assert (Hall : forall x, dspRel w x y -> ~ P x).
      { intros x Hx HP. apply Hno. exists x. split; [exact HP | exact Hx]. }
      split.
      + exists x0. split; [exact (Hall x0 Hx0) | exact Hx0].
      + exact Hall.
    - intros [x [HP [Htop Hnx]]]. split; [exact Htop |].
      intro Hn. apply Hnx.
      apply (Hm (fun z => ~ P z) (fun z => z <> x)); [| exact Hn].
      intros z Hz Heq. subst z. exact (Hz HP).
  Qed.

  Lemma dslpOfDSP_dslpPart (w : DSPArr X Y) P y :
    dslpOfDSP w P y <-> dslpPart w P y.
  Proof.
    unfold dslpOfDSP, dslpPart, dslpPartArr, getDSLPArr, mkDSLPArr, dslpOf, dslp. cbn.
    split.
    - intros [Hw | Hn] x Hx.
      + exact (proj2 (proj1 (dspRel_spec w P y) Hw) x Hx).
      + exact (False_ind _ (Hn (proj1 Hx))).
    - intro Hall. destruct (classic (getDSP w (fun _ => True) y)) as [Htop | Hn].
      + left. apply (proj2 (dspRel_spec w P y)).
        destruct (proj1 (dspRel_spec w _ y) Htop) as [[x0 [_ Hx0]] _].
        split; [exists x0; split; [exact (Hall x0 Hx0) | exact Hx0] | exact Hall].
      + right. exact Hn.
  Qed.

  (** [aspOf : DSP -> ASP] and [dslpOf : DSP -> DSLP]: the components
      satisfy the healthiness conditions of ASP and DSLP arrows. *)
  Lemma aspOfDSP_monotone (w : DSPArr X Y) : sp_monotone (aspOfDSP w).
  Proof.
    destruct (proj2_sig w) as [Hm _]. unfold aspOfDSP, getDSP.
    intros P Q HPQ y [Htop Hn]. split; [exact Htop |].
    intro HQ. apply Hn. apply (Hm (fun x => ~ Q x)); [| exact HQ].
    intros x HnQ HP. exact (HnQ (HPQ x HP)).
  Qed.

  Lemma aspOfDSP_strict (w : DSPArr X Y) : sp_strict (aspOfDSP w).
  Proof.
    destruct (proj2_sig w) as [Hm _]. unfold aspOfDSP, getDSP.
    intros y [Htop Hn]. apply Hn.
    exact (Hm (fun _ => True) (fun _ => ~ False) (fun _ _ f => f) y Htop).
  Qed.

  Lemma aspOfDSP_disjunctive (w : DSPArr X Y) : sp_disjunctive (aspOfDSP w).
  Proof.
    destruct (proj2_sig w) as [Hm [_ Hc]]. unfold aspOfDSP, getDSP.
    intros I HI p y. split.
    - intros [Htop Hn]. apply NNPP. intro Hno. apply Hn.
      apply (Hm (fun x => forall i, ~ p i x)).
      + intros x Hx [i Hi]. exact (Hx i Hi).
      + apply (proj2 (Hc I HI (fun i x => ~ p i x) y)). intro i.
        apply NNPP. intro Hni. apply Hno. exists i. split; [exact Htop | exact Hni].
    - intros [i [Htop Hn]]. split; [exact Htop |].
      intro Hall. apply Hn. apply (Hm (fun x => ~ exists i, p i x)); [| exact Hall].
      intros x Hx Hi. exact (Hx (ex_intro _ i Hi)).
  Qed.

  Lemma dslpOfDSP_monotone (w : DSPArr X Y) : sp_monotone (dslpOfDSP w).
  Proof.
    destruct (proj2_sig w) as [Hm _]. unfold dslpOfDSP, getDSP.
    intros P Q HPQ y [Hw | Hn]; [left; exact (Hm P Q HPQ y Hw) | right; exact Hn].
  Qed.

  Lemma dslpOfDSP_terminating (w : DSPArr X Y) : sp_terminating (dslpOfDSP w).
  Proof. unfold dslpOfDSP, getDSP. intro y. exact (classic _). Qed.

  Lemma dslpOfDSP_conjunctive (w : DSPArr X Y) : sp_conjunctive (dslpOfDSP w).
  Proof.
    destruct (proj2_sig w) as [Hm [_ Hc]]. unfold dslpOfDSP, getDSP.
    intros I HI p y. split.
    - intros [Hw | Hn] i; [left | right; exact Hn].
      apply (Hm (fun x => forall i, p i x)); [intros x Hx; exact (Hx i) | exact Hw].
    - intro Hall. destruct (classic (proj1_sig w (fun _ => True) y)) as [Htop | Hn].
      + left. apply (proj2 (Hc I HI p y)). intro i.
        destruct (Hall i) as [Hi | Hn]; [exact Hi | exact (False_ind _ (Hn Htop))].
      + right. exact Hn.
  Qed.

  #[program] Definition aspOfDSPArr (w : DSPArr X Y) : ASPArr X Y := aspOfDSP w.
  Next Obligation.
    intros w.
    exact (conj (aspOfDSP_monotone w) (conj (aspOfDSP_strict w) (aspOfDSP_disjunctive w))).
  Qed.

  #[program] Definition dslpOfDSPArr (w : DSPArr X Y) : DSLPArr X Y := dslpOfDSP w.
  Next Obligation.
    intros w.
    exact (conj (dslpOfDSP_monotone w)
             (conj (dslpOfDSP_terminating w) (dslpOfDSP_conjunctive w))).
  Qed.
End DSPComponents.

(* ================================================================= *)
(** ** Components of an ASLP arrow                                   *)
(* ================================================================= *)

Section ASLPComponents.
  Context {X Y : Type}.

  (** [y] is admitted, and produced: under [False], an ASLP arrow admits
      exactly the outputs that are not produced. *)
  Definition aspOfASLP (w : ASLPArr X Y) : SPArrT X Y :=
    fun P y => getASLP w P y /\ ~ getASLP w (fun _ => False) y.

  (** [y] is not admitted under the complement of [P], or not produced. *)
  Definition dslpOfASLP (w : ASLPArr X Y) : SPArrT X Y :=
    fun P y => ~ getASLP w (fun x => ~ P x) y \/ getASLP w (fun _ => False) y.

  Theorem aslp_split_direct (w : ASLPArr X Y) P y :
    getASLP w P y <-> aspOfASLP w P y \/ dslpOfASLP w P y.
  Proof.
    destruct (proj2_sig w) as [Hm [Ht Hd]].
    unfold aspOfASLP, dslpOfASLP, getASLP. split.
    - intro Hw. destruct (classic (proj1_sig w (fun _ => False) y)) as [Hbot | Hnbot].
      + right. right. exact Hbot.
      + left. split; [exact Hw | exact Hnbot].
    - intros [[Hw _] | [Hn | Hbot]].
      + exact Hw.
      + assert (Hor : proj1_sig w (fun x => exists b : bool, if b then P x else ~ P x) y).
        { apply (Hm (fun _ => True)); [| exact (Ht y)].
          intros x _. destruct (classic (P x)) as [Hp | Hnp];
            [exists true; exact Hp | exists false; exact Hnp]. }
        destruct (proj1 (Hd bool (inhabits true) (fun b x => if b then P x else ~ P x) y) Hor)
          as [[|] Hb]; [exact Hb | exact (False_ind _ (Hn Hb))].
      + exact (Hm (fun _ => False) P (fun _ f => match f with end) y Hbot).
  Qed.

  Lemma aspOfASLP_aspPartA (w : ASLPArr X Y) P y :
    aspOfASLP w P y <-> aspPartA w P y.
  Proof.
    destruct (proj2_sig w) as [Hm _].
    unfold aspOfASLP, aspPartA, aspPartAArr, getASPArr, mkASPArr, aspOf, asp. cbn.
    split.
    - intros [Hw Hnbot].
      destruct (proj1 (aslpRel_spec w P y) Hw) as [Ha | Hdl]; [exact Ha |].
      apply NNPP. intro Hno. apply Hnbot.
      apply (proj2 (aslpRel_spec w _ y)). right. intros x Hx.
      apply Hno. exists x. split; [exact (Hdl x Hx) | exact Hx].
    - intros [x [HP [Hnbot Hx]]]. split; [| exact Hnbot].
      apply (Hm (fun z => z = x) P); [| exact Hx].
      intros z Hz. subst z. exact HP.
  Qed.

  Lemma dslpOfASLP_dslpPartA (w : ASLPArr X Y) P y :
    dslpOfASLP w P y <-> dslpPartA w P y.
  Proof.
    destruct (proj2_sig w) as [Hm _].
    unfold dslpOfASLP, dslpPartA, dslpPartAArr, getDSLPArr, mkDSLPArr, dslpOf, dslp. cbn.
    split.
    - intros [Hn | Hbot] x [Hnbot Hx].
      + apply NNPP. intro HnP. apply Hn.
        apply (Hm (fun z => z = x) (fun z => ~ P z)); [| exact Hx].
        intros z Hz. subst z. exact HnP.
      + exact (False_ind _ (Hnbot Hbot)).
    - intro Hall. destruct (classic (getASLP w (fun _ => False) y)) as [Hbot | Hnbot].
      + right. exact Hbot.
      + left. intro Hn.
        destruct (proj1 (aslpRel_spec w _ y) Hn) as [[x [HnP Hx]] | Hdl].
        * exact (HnP (Hall x Hx)).
        * apply Hnbot. apply (proj2 (aslpRel_spec w _ y)). right.
          intros x Hx. exact (Hdl x Hx (Hall x Hx)).
  Qed.

  (** [aspOf : ASLP -> ASP] and [dslpOf : ASLP -> DSLP]. *)
  Lemma aspOfASLP_monotone (w : ASLPArr X Y) : sp_monotone (aspOfASLP w).
  Proof.
    destruct (proj2_sig w) as [Hm _]. unfold aspOfASLP, getASLP.
    intros P Q HPQ y [Hw Hnbot]. exact (conj (Hm P Q HPQ y Hw) Hnbot).
  Qed.

  Lemma aspOfASLP_strict (w : ASLPArr X Y) : sp_strict (aspOfASLP w).
  Proof. unfold aspOfASLP, getASLP. intros y [Hbot Hnbot]. exact (Hnbot Hbot). Qed.

  Lemma aspOfASLP_disjunctive (w : ASLPArr X Y) : sp_disjunctive (aspOfASLP w).
  Proof.
    destruct (proj2_sig w) as [_ [_ Hd]]. unfold aspOfASLP, getASLP.
    intros I HI p y. split.
    - intros [Hw Hnbot]. destruct (proj1 (Hd I HI p y) Hw) as [i Hi].
      exists i. exact (conj Hi Hnbot).
    - intros [i [Hi Hnbot]]. exact (conj (proj2 (Hd I HI p y) (ex_intro _ i Hi)) Hnbot).
  Qed.

  Lemma dslpOfASLP_monotone (w : ASLPArr X Y) : sp_monotone (dslpOfASLP w).
  Proof.
    destruct (proj2_sig w) as [Hm _]. unfold dslpOfASLP, getASLP.
    intros P Q HPQ y [Hn | Hbot]; [left | right; exact Hbot].
    intro HnQ. apply Hn. apply (Hm (fun x => ~ Q x)); [| exact HnQ].
    intros x Hx HP. exact (Hx (HPQ x HP)).
  Qed.

  Lemma dslpOfASLP_terminating (w : ASLPArr X Y) : sp_terminating (dslpOfASLP w).
  Proof.
    destruct (proj2_sig w) as [Hm _]. unfold dslpOfASLP, getASLP.
    intro y. destruct (classic (proj1_sig w (fun _ => False) y)) as [Hbot | Hnbot].
    - right. exact Hbot.
    - left. intro Hn. apply Hnbot.
      exact (Hm (fun _ => ~ True) (fun _ => False) (fun _ f => f I) y Hn).
  Qed.

  Lemma dslpOfASLP_conjunctive (w : ASLPArr X Y) : sp_conjunctive (dslpOfASLP w).
  Proof.
    destruct (proj2_sig w) as [Hm [_ Hd]]. unfold dslpOfASLP, getASLP.
    intros I HI p y. split.
    - intros [Hn | Hbot] i; [left | right; exact Hbot].
      intro Hi. apply Hn. apply (Hm (fun x => ~ p i x)); [| exact Hi].
      intros x Hx Hall. exact (Hx (Hall i)).
    - intro Hall. destruct (classic (proj1_sig w (fun _ => False) y)) as [Hbot | Hnbot].
      + right. exact Hbot.
      + left. intro Hn.
        assert (Hex : proj1_sig w (fun x => exists i, ~ p i x) y).
        { apply (Hm (fun x => ~ forall i, p i x)); [| exact Hn].
          intros x Hx. apply NNPP. intro Hno. apply Hx. intro i.
          apply NNPP. intro Hni. apply Hno. exists i. exact Hni. }
        destruct (proj1 (Hd I HI (fun i x => ~ p i x) y) Hex) as [i Hi].
        destruct (Hall i) as [Hni | Hbot]; [exact (Hni Hi) | exact (Hnbot Hbot)].
  Qed.

  #[program] Definition aspOfASLPArr (w : ASLPArr X Y) : ASPArr X Y := aspOfASLP w.
  Next Obligation.
    intros w.
    exact (conj (aspOfASLP_monotone w) (conj (aspOfASLP_strict w) (aspOfASLP_disjunctive w))).
  Qed.

  #[program] Definition dslpOfASLPArr (w : ASLPArr X Y) : DSLPArr X Y := dslpOfASLP w.
  Next Obligation.
    intros w.
    exact (conj (dslpOfASLP_monotone w)
             (conj (dslpOfASLP_terminating w) (dslpOfASLP_conjunctive w))).
  Qed.
End ASLPComponents.
