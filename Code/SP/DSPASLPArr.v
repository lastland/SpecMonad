(** * Property-only strongest-postcondition arrows: DSP and ASLP.

    DSP/ASLP recover relations classically and split operations into their
    ASP and DSLP readings, which they combine by conjunction / disjunction.
    The file ends with the separation of the four healthiness classes. *)

From Coq Require Import FunctionalExtensionality PropExtensionality RelationClasses
  Morphisms Setoid Classical_Prop.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Arrow Require Export ArrowMonad.
From Incorrectness.Lib.Arrow Require Import Arrow OptionArrowT StateArrowT
  ArrowMorphism RelArrowCoherence.
From Incorrectness.Relational Require Import Rel RelSPostArr.
From Incorrectness.SP Require Export PredicateTransformerProperties.
From Incorrectness.SP Require Import SPostArr.

Local Obligation Tactic := idtac.

(** ** Canonical DSP arrows
    Composition splits into ASP and DSLP, operates on each part, and conjoins.
    Composing the conjoined transformers directly would be strictly stronger
    than the relational reading. Relation recovery uses excluded middle. *)

Section DSPImplementation.

  (** *** Normal form: [dspOf] presentations *)

  Definition DSPhealthy {X Y} (w : SPArrT X Y) : Prop :=
    exists R : SPureArr X Y, forall P y, w P y <-> dspOf R P y.

  Lemma dsp_healthy_hom {X Y} (w : SPArrT X Y) :
    DSPhealthy w -> sp_monotone w /\ sp_strict w /\ sp_conjunctive w.
  Proof.
    intros [R HR]. split; [|split].
    - intros P Q HPQ y Hw. apply HR in Hw. apply HR. destruct Hw as [[x [Hx HRx]] Hd]. split.
      + exists x. split; [exact (HPQ x Hx) | exact HRx].
      + intros x' Hx'. exact (HPQ x' (Hd x' Hx')).
    - intros y Hw. apply HR in Hw. destruct Hw as [[x [[] _]] _].
    - intros I [i0] P y. rewrite (HR _ y). split.
      + intros [[x [Hx HRx]] Hd] i. apply (HR _ y). split.
        * exists x. split; [exact (Hx i) | exact HRx].
        * intros x' Hx'. exact (Hd x' Hx' i).
      + intro Hall. split.
        * destruct (proj1 (HR _ y) (Hall i0)) as [[x [_ HRx]] _].
          exists x. split; [|exact HRx].
          intro i. exact (proj2 (proj1 (HR _ y) (Hall i)) x HRx).
        * intros x HRx i. exact (proj2 (proj1 (HR _ y) (Hall i)) x HRx).
  Qed.

  Lemma dsp_hom_healthy {X Y} (w : SPArrT X Y) :
    sp_monotone w /\ sp_strict w /\ sp_conjunctive w -> DSPhealthy w.
  Proof.
    intros [Hm [Hs Hc]].
    exists (fun x y => w (fun _ => True) y /\ forall i : { Q : X -> Prop | w Q y }, proj1_sig i x).
    intros P y. unfold dspOf, aspOf, dslpOf. split.
    - intro Hw.
      assert (Htop : w (fun _ => True) y).
      { apply (Hm P); [intros; exact I | exact Hw]. }
      assert (Hleast : w (fun x => forall i : { Q : X -> Prop | w Q y }, proj1_sig i x) y).
      { exact (proj2 (Hc _ (inhabits (exist (fun Q => w Q y) P Hw)) (fun i => proj1_sig i) y)
                     (fun i => proj2_sig i)). }
      split.
      + apply NNPP. intro Hno. apply (Hs y).
        apply (Hm (fun x => forall i : { Q : X -> Prop | w Q y }, proj1_sig i x)); [|exact Hleast].
        intros x Hx. apply Hno. exists x.
        split; [exact (Hx (exist _ P Hw)) | split; [exact Htop | exact Hx]].
      + intros x [_ Hx]. exact (Hx (exist _ P Hw)).
    - intros [[x0 [_ [Htop _]]] Hall].
      apply (Hm (fun x => forall i : { Q : X -> Prop | w Q y }, proj1_sig i x)).
      + intros x Hx. exact (Hall x (conj Htop Hx)).
      + exact (proj2 (Hc _ (inhabits (exist (fun Q => w Q y) (fun _ => True) Htop))
                        (fun i => proj1_sig i) y) (fun i => proj2_sig i)).
  Qed.

  Theorem dsp_hom_iff {X Y} (w : SPArrT X Y) :
    DSPhealthy w <-> sp_monotone w /\ sp_strict w /\ sp_conjunctive w.
  Proof. split; [apply dsp_healthy_hom | apply dsp_hom_healthy]. Qed.

  (** *** Carrier, equality, and recovered relation *)

  Definition DSPArr (X Y : Type) : Type :=
    { w : SPArrT X Y | sp_monotone w /\ sp_strict w /\ sp_conjunctive w }.

  Definition getDSP {X Y} (w : DSPArr X Y) : (X -> Prop) -> Y -> Prop := proj1_sig w.

  Definition DSPArr_eq {X Y} (w v : DSPArr X Y) : Prop :=
    forall P y, getDSP w P y <-> getDSP v P y.

  Definition dspRel {X Y} (w : DSPArr X Y) : SPureArr X Y :=
    fun x y => getDSP w (fun _ => True) y /\ ~ getDSP w (fun z => z <> x) y.

  Lemma dspRel_of {X Y} (R : SPureArr X Y) (w : DSPArr X Y) :
    (forall P y, getDSP w P y <-> dspOf R P y) -> Rel_eq (dspRel w) R.
  Proof. intros Hw x y. unfold dspRel. rewrite !Hw. symmetry. apply dspOf_rel. Qed.

  Lemma dspRel_spec {X Y} (w : DSPArr X Y) P y :
    getDSP w P y <-> dspOf (dspRel w) P y.
  Proof.
    destruct (dsp_hom_healthy _ (proj2_sig w)) as [R HR].
    assert (Hrel : Rel_eq (dspRel w) R) by (apply dspRel_of; exact HR).
    unfold getDSP. rewrite HR. unfold dspOf, aspOf, dslpOf.
    split; intros [Ha Hd]; split.
    - destruct Ha as [x [HP Hx]]. exists x. split; [exact HP | apply Hrel; exact Hx].
    - intros x Hx. apply Hd. apply Hrel. exact Hx.
    - destruct Ha as [x [HP Hx]]. exists x. split; [exact HP | apply Hrel; exact Hx].
    - intros x Hx. apply Hd. apply Hrel. exact Hx.
  Qed.

  (** *** ASP and DSLP parts
      Both parts are canonical property-only arrows. *)

  Definition aspPartArr {X Y} (w : DSPArr X Y) : ASPArr X Y :=
    mkASPArr (aspOf (dspRel w)) (fun P b => aspOf_join (dspRel w) P b).

  Definition dslpPartArr {X Y} (w : DSPArr X Y) : DSLPArr X Y :=
    mkDSLPArr (dslpOf (dspRel w)) (fun P b => dslpOf_meet (dspRel w) P b).

  Definition aspPart {X Y} (w : DSPArr X Y) : (X -> Prop) -> Y -> Prop :=
    getASPArr (aspPartArr w).

  Definition dslpPart {X Y} (w : DSPArr X Y) : (X -> Prop) -> Y -> Prop :=
    getDSLPArr (dslpPartArr w).

  Theorem dsp_split {X Y} (w : DSPArr X Y) P y :
    getDSP w P y <-> (aspPart w P y /\ dslpPart w P y).
  Proof. exact (dspRel_spec w P y). Qed.

  (** The parts above are built from the relation an element denotes.  They
      agree with the direct formulas on the element itself: the ASP part
      admits [y] when the element admits it at [True] and not at the
      complement of [P]; the DSLP part when the element admits it at [P],
      or not at [True].  Both directions of the first and the forward
      direction of the second are classical. *)

  Theorem aspPart_formula {X Y} (w : DSPArr X Y) (P : X -> Prop) y :
    aspPart w P y
    <-> getDSP w (fun _ => True) y /\ ~ getDSP w (fun x => ~ P x) y.
  Proof.
    unfold aspPart, aspPartArr. cbn.
    rewrite (dspRel_spec w (fun _ => True) y), (dspRel_spec w (fun x => ~ P x) y).
    unfold dspOf, aspOf, dslpOf, asp, dslp. split.
    - intros [x [HP Hx]]. split.
      + split; [ exists x; split; [ exact I | exact Hx ] | intros ? ?; exact I ].
      + intros [_ Hall]. exact (Hall x Hx HP).
    - intros [[[x1 [_ Hx1]] _] Hn].
      destruct (classic (forall x, dspRel w x y -> ~ P x)) as [Hb | Hb].
      + exfalso. apply Hn. split; [| exact Hb ].
        exists x1. split; [ exact (Hb x1 Hx1) | exact Hx1 ].
      + apply NNPP. intro Hno. apply Hb. intros x Hx HP.
        exact (Hno (ex_intro _ x (conj HP Hx))).
  Qed.

  Theorem dslpPart_formula {X Y} (w : DSPArr X Y) (P : X -> Prop) y :
    dslpPart w P y
    <-> getDSP w P y \/ ~ getDSP w (fun _ => True) y.
  Proof.
    unfold dslpPart, dslpPartArr. cbn.
    rewrite (dspRel_spec w P y), (dspRel_spec w (fun _ => True) y).
    unfold dspOf, aspOf, dslpOf, asp, dslp. split.
    - intro Hall. destruct (classic (exists x, dspRel w x y)) as [[x0 Hx0] | Hno].
      + left. split; [ exists x0; split; [ exact (Hall x0 Hx0) | exact Hx0 ] | exact Hall ].
      + right. intros [[x [_ Hx]] _]. exact (Hno (ex_intro _ x Hx)).
    - intros [[_ Hall] | Hn]; [ exact Hall |].
      intros x Hx. exfalso. apply Hn.
      split; [ exists x; split; [ exact I | exact Hx ] | intros ? ?; exact I ].
  Qed.

  Theorem dspRel_faithful {X Y} (w v : DSPArr X Y) :
    Rel_eq (dspRel w) (dspRel v) -> DSPArr_eq w v.
  Proof.
    intros H P y. rewrite (dspRel_spec w P y), (dspRel_spec v P y).
    exact (dspOf_cong _ _ H P y).
  Qed.

  Theorem dspRel_faithful_conv {X Y} (w v : DSPArr X Y) :
    DSPArr_eq w v -> Rel_eq (dspRel w) (dspRel v).
  Proof.
    intros H x y. unfold dspRel. split.
    - intros [Ht Hn]. split; [apply H; exact Ht |].
      intro Hc. apply Hn. apply H. exact Hc.
    - intros [Ht Hn]. split; [apply H; exact Ht |].
      intro Hc. apply Hn. apply H. exact Hc.
  Qed.

  (** *** Operations and instances *)

  #[local] Obligation Tactic := idtac.

  #[program] Definition pure_DSP {X Y} (h : X -> Y) : DSPArr X Y :=
    fun P y => pureASP h P y /\ pureDSLP h P y.
  Next Obligation.
    intros X Y h. apply dsp_healthy_hom. exists (arr_pure h). intros P y. reflexivity.
  Qed.

  #[program] Definition comp_DSP {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z) : DSPArr X Z :=
    fun P z => compASP (aspPartArr w) (aspPartArr v) P z
               /\ compDSLP (dslpPartArr w) (dslpPartArr v) P z.
  Next Obligation.
    intros X Y Z w v. apply dsp_healthy_hom. exists (arr_comp (dspRel w) (dspRel v)). intros P z.
    unfold aspPart, dslpPart, dspOf.
    rewrite (aspOf_comp (dspRel w) (dspRel v)), (dslpOf_comp (dspRel w) (dspRel v)).
    reflexivity.
  Qed.

  #[program] Definition first_DSP {X Y C} (w : DSPArr X Y) : DSPArr (X * C) (Y * C) :=
    fun P q => @firstASP _ _ C (aspPartArr w) P q /\ @firstDSLP _ _ C (dslpPartArr w) P q.
  Next Obligation.
    intros X Y C w. apply dsp_healthy_hom. exists (arr_first (dspRel w)). intros P q.
    unfold aspPart, dslpPart, dspOf.
    rewrite (aspOf_first (dspRel w)), (dslpOf_first (dspRel w)). reflexivity.
  Qed.

  #[global] Instance Arrow_DSPArr : Arrow DSPArr := {
    arr_pure := @pure_DSP; arr_comp := @comp_DSP; arr_first := @first_DSP
  }.

  #[global] Instance DSPArr_eq_Equivalence {X Y} : Equivalence (@DSPArr_eq X Y).
  Proof.
    constructor.
    - intros w P y. reflexivity.
    - intros w v H P y. symmetry. exact (H P y).
    - intros u w v H1 H2 P y. exact (iff_trans (H1 P y) (H2 P y)).
  Qed.

  #[global] Instance ArrowEq_DSPArr : ArrowEq DSPArr := {
    arrow_eq := @DSPArr_eq; arrow_eq_equiv := @DSPArr_eq_Equivalence
  }.

  #[program] Definition left_DSP {X Y C} (w : DSPArr X Y) : DSPArr (X + C) (Y + C) :=
    fun P y => @leftASP _ _ C (aspPartArr w) P y /\ @leftDSLP _ _ C (dslpPartArr w) P y.
  Next Obligation.
    intros X Y C w. apply dsp_healthy_hom. exists (arr_left (dspRel w)).
    intros P [b | c]; unfold dspOf.
    - unfold aspPart, dslpPart.
      rewrite (aspOf_left_inl (dspRel w)), (dslpOf_left_inl (dspRel w)). reflexivity.
    - rewrite (aspOf_left_inr (dspRel w)), (dslpOf_left_inr (dspRel w)). tauto.
  Qed.

  #[global] Instance ArrowChoice_DSPArr : ArrowChoice DSPArr := { arr_left := @left_DSP }.

  (** Application reads the stored DSP arrow itself, so its domain is DSP-specific. *)
  Definition appRel {A B} : SPureArr (DSPArr A B * A) B :=
    fun p b => dspRel (fst p) (snd p) b.

  #[program] Definition app_DSP {A B} : DSPArr (DSPArr A B * A) B :=
    fun P b => aspOf appRel P b /\ dslpOf appRel P b.
  Next Obligation.
    intros A B. apply dsp_healthy_hom. exists appRel. intros P b. reflexivity.
  Qed.

  #[global] Instance ArrowApply_DSPArr : ArrowApply DSPArr := { arr_app := @app_DSP }.

End DSPImplementation.

(** ** DSP relation contracts and selected-equality laws *)

Section DSPRelation.

  (** *** Operation contracts *)

  Lemma dspRel_pure {X Y} (h : X -> Y) : Rel_eq (dspRel (pure_DSP h)) (arr_pure h).
  Proof. apply dspRel_of. intros P y. reflexivity. Qed.

  Lemma dspRel_comp {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z) :
    Rel_eq (dspRel (comp_DSP w v)) (arr_comp (dspRel w) (dspRel v)).
  Proof.
    apply dspRel_of. intros P z. unfold comp_DSP, getDSP. cbn [proj1_sig].
    unfold aspPart, dslpPart, dspOf.
    rewrite (aspOf_comp (dspRel w) (dspRel v)), (dslpOf_comp (dspRel w) (dspRel v)). reflexivity.
  Qed.

  Lemma dspRel_first {X Y C} (w : DSPArr X Y) :
    Rel_eq (dspRel (@first_DSP X Y C w)) (arr_first (dspRel w)).
  Proof.
    apply dspRel_of. intros P q. unfold first_DSP, getDSP. cbn [proj1_sig].
    unfold aspPart, dslpPart, dspOf.
    rewrite (aspOf_first (dspRel w)), (dslpOf_first (dspRel w)). reflexivity.
  Qed.

  Lemma dspRel_left {X Y C} (w : DSPArr X Y) :
    Rel_eq (dspRel (@left_DSP X Y C w)) (arr_left (dspRel w)).
  Proof.
    apply dspRel_of. intros P [b | c]; unfold left_DSP, getDSP; cbn [proj1_sig]; unfold dspOf.
    - unfold aspPart, dslpPart.
      rewrite (aspOf_left_inl (dspRel w)), (dslpOf_left_inl (dspRel w)). reflexivity.
    - rewrite (aspOf_left_inr (dspRel w)), (dslpOf_left_inr (dspRel w)). tauto.
  Qed.

  Lemma dspRel_app {A B} : Rel_eq (dspRel (@app_DSP A B)) appRel.
  Proof. apply dspRel_of. intros P b. reflexivity. Qed.

  Lemma dspRel_second {X Y C} (w : DSPArr X Y) :
    Rel_eq (dspRel (@arr_second DSPArr Arrow_DSPArr X Y C w))
      (@arr_second Rel Arrow_Rel X Y C (dspRel w)).
  Proof.
    unfold arr_second. cbn [arr_comp arr_pure arr_first Arrow_DSPArr].
    repeat first [setoid_rewrite dspRel_comp | setoid_rewrite dspRel_pure
      | setoid_rewrite dspRel_first].
    reflexivity.
  Qed.

  (** *** Symmetric and combined variants *)

  Lemma dspRel_pure_sym {X Y} (h : X -> Y) : Rel_eq (arr_pure h) (dspRel (pure_DSP h)).
  Proof. intros x y. symmetry. apply dspRel_pure. Qed.

  Lemma dspRel_comp_sym {X Y Z} (w : DSPArr X Y) (v : DSPArr Y Z) :
    Rel_eq (arr_comp (dspRel w) (dspRel v)) (dspRel (comp_DSP w v)).
  Proof. intros x z. symmetry. apply dspRel_comp. Qed.

  Lemma dspRel_first_sym {X Y C} (w : DSPArr X Y) :
    Rel_eq (arr_first (dspRel w)) (dspRel (@first_DSP X Y C w)).
  Proof. intros p q. symmetry. apply dspRel_first. Qed.

  Lemma dspRel_left2 {A B C D} (f : DSPArr A B) :
    Rel_eq (dspRel (@left_DSP _ _ D (@left_DSP A B C f))) (arr_left (arr_left (dspRel f))).
  Proof. etransitivity; [apply dspRel_left | apply Rel_left_cong; apply dspRel_left]. Qed.

  Lemma dspRel_first_left {A B C D} (f : DSPArr A B) :
    Rel_eq (dspRel (@first_DSP _ _ D (@left_DSP A B C f))) (arr_first (arr_left (dspRel f))).
  Proof. etransitivity; [apply dspRel_first | apply Rel_first_cong; apply dspRel_left]. Qed.

  Lemma dspRel_left_first {A B C D} (f : DSPArr A B) :
    Rel_eq (dspRel (@left_DSP _ _ (C * D)%type (@first_DSP A B D f)))
      (arr_left (arr_first (dspRel f))).
  Proof. etransitivity; [apply dspRel_left | apply Rel_left_cong; apply dspRel_first]. Qed.

  (** *** Semantic contracts and law packages *)

  #[global] Instance RelArrow_DSPArr : RelArrow DSPArr := {|
    rel_reading := @dspRel; rel_pure := @dspRel_pure; rel_comp := @dspRel_comp;
    rel_first := fun A B C f a c b d => dspRel_first f (a, c) (b, d)
  |}.

  #[global] Instance RelArrowChoice_DSPArr : RelArrowChoice DSPArr :=
    {| rel_left := @dspRel_left |}.

  #[global] Instance RelArrowApply_DSPArr : RelArrowApply DSPArr := {|
    rel_app := fun A B f a b => dspRel_app (f, a) b
  |}.

  #[global] Instance RelArrowEq_DSPArr : RelArrowEq DSPArr := {|
    rel_arrow_eq := fun A B f g => conj (dspRel_faithful_conv f g) (dspRel_faithful f g)
  |}.

  #[global] Instance ArrowLaws_DSPArr : ArrowLaws DSPArr :=
    @rel_arrow_laws DSPArr Arrow_DSPArr ArrowEq_DSPArr RelArrow_DSPArr RelArrowEq_DSPArr.

  #[global] Instance ArrowChoiceLaws_DSPArr : ArrowChoiceLaws DSPArr :=
    @rel_arrow_choice_laws DSPArr Arrow_DSPArr ArrowEq_DSPArr RelArrow_DSPArr
      RelArrowEq_DSPArr ArrowChoice_DSPArr RelArrowChoice_DSPArr.

  #[global] Instance ArrowApplyLaws_DSPArr : ArrowApplyLaws DSPArr :=
    @rel_arrow_apply_laws DSPArr Arrow_DSPArr ArrowEq_DSPArr RelArrow_DSPArr
      RelArrowEq_DSPArr ArrowApply_DSPArr RelArrowApply_DSPArr.

End DSPRelation.

(** ** Canonical ASLP arrows
    The dual split recipe disjoins ASP and DSLP operation results. The relation
    probe rejects the empty precondition and accepts the singleton. *)

Section ASLPImplementation.

  (** *** Normal form: [aslpOf] presentations *)

  Definition ASLPhealthy {X Y} (w : SPArrT X Y) : Prop :=
    exists R : SPureArr X Y, forall P y, w P y <-> aslpOf R P y.

  Lemma aslp_healthy_hom {X Y} (w : SPArrT X Y) :
    ASLPhealthy w -> sp_monotone w /\ sp_terminating w /\ sp_disjunctive w.
  Proof.
    intros [R HR]. split; [|split].
    - intros P Q HPQ y Hw. apply HR in Hw. apply HR. destruct Hw as [[x [Hx HRx]] | Hd].
      + left. exists x. split; [exact (HPQ x Hx) | exact HRx].
      + right. intros x Hx. exact (HPQ x (Hd x Hx)).
    - intro y. apply (HR _ y). right. intros x _. exact I.
    - intros I [i0] P y. rewrite (HR _ y). split.
      + intros [[x [[i Hi] HRx]] | Hd].
        * exists i. apply (HR _ y). left. exists x. split; assumption.
        * destruct (classic (exists x, R x y)) as [[x HRx] | Hno].
          -- destruct (Hd x HRx) as [i Hi]. exists i. apply (HR _ y).
             left. exists x. split; assumption.
          -- exists i0. apply (HR _ y). right. intros x HRx. destruct (Hno (ex_intro _ x HRx)).
      + intros [i Hw]. apply (HR _ y) in Hw. destruct Hw as [[x [Hx HRx]] | Hd].
        * left. exists x. split; [exists i; exact Hx | exact HRx].
        * right. intros x HRx. exists i. exact (Hd x HRx).
  Qed.

  Lemma aslp_hom_healthy {X Y} (w : SPArrT X Y) :
    sp_monotone w /\ sp_terminating w /\ sp_disjunctive w -> ASLPhealthy w.
  Proof.
    intros [Hm [Ht Hd]].
    assert (Hsplit : forall P y,
               w P y <-> w (fun _ => False) y \/ exists x, P x /\ w (fun z => z = x) y).
    { intros P y. split.
      - intro Hw.
        pose (F := fun (i : option { x : X | P x }) (z : X) =>
                     match i with Some x => z = proj1_sig x | None => False end).
        assert (HF : w (fun z => exists i, F i z) y).
        { apply (Hm P); [|exact Hw]. intros z Hz. exists (Some (exist _ z Hz)). reflexivity. }
        apply (Hd _ (inhabits None) F y) in HF.
        destruct HF as [[[x Hx] |] Hw'];
          [right; exists x; split; [exact Hx | exact Hw'] | left; exact Hw'].
      - intros [Hw | [x [Hx Hw]]].
        + apply (Hm (fun _ => False)); [intros z [] | exact Hw].
        + apply (Hm (fun z => z = x)); [intros z ->; exact Hx | exact Hw]. }
    exists (fun x y => ~ w (fun _ => False) y /\ w (fun z => z = x) y).
    intros P y. unfold aslpOf, aspOf, dslpOf.
    destruct (classic (w (fun _ => False) y)) as [Hbot | Hnbot].
    - split.
      + intros _. right. intros x [Hn _]. destruct (Hn Hbot).
      + intros _. apply (Hm (fun _ => False)); [intros x [] | exact Hbot].
    - rewrite (Hsplit P y). split.
      + intros [Hw | [x [Hx Hw]]]; [contradiction |].
        left. exists x. split; [exact Hx | split; assumption].
      + intros [[x [Hx [_ Hw]]] | Hall]; [right; exists x; split; assumption |].
        destruct (proj1 (Hsplit (fun _ => True) y) (Ht y)) as [Hw | [x0 [_ Hw0]]];
          [contradiction |].
        right. exists x0. split; [exact (Hall x0 (conj Hnbot Hw0)) | exact Hw0].
  Qed.

  Theorem aslp_hom_iff {X Y} (w : SPArrT X Y) :
    ASLPhealthy w <-> sp_monotone w /\ sp_terminating w /\ sp_disjunctive w.
  Proof. split; [apply aslp_healthy_hom | apply aslp_hom_healthy]. Qed.

  (** *** Carrier, equality, and recovered relation *)

  Definition ASLPArr (X Y : Type) : Type :=
    { w : SPArrT X Y | sp_monotone w /\ sp_terminating w /\ sp_disjunctive w }.

  Definition getASLP {X Y} (w : ASLPArr X Y) : (X -> Prop) -> Y -> Prop := proj1_sig w.

  Definition ASLPArr_eq {X Y} (w v : ASLPArr X Y) : Prop :=
    forall P y, getASLP w P y <-> getASLP v P y.

  Definition aslpRel {X Y} (w : ASLPArr X Y) : SPureArr X Y :=
    fun x y => ~ getASLP w (fun _ => False) y /\ getASLP w (fun z => z = x) y.

  Lemma aslpRel_of {X Y} (R : SPureArr X Y) (w : ASLPArr X Y) :
    (forall P y, getASLP w P y <-> aslpOf R P y) -> Rel_eq (aslpRel w) R.
  Proof. intros Hw x y. unfold aslpRel. rewrite !Hw. symmetry. apply aslpOf_rel. Qed.

  Lemma aslpRel_spec {X Y} (w : ASLPArr X Y) P y :
    getASLP w P y <-> aslpOf (aslpRel w) P y.
  Proof.
    destruct (aslp_hom_healthy _ (proj2_sig w)) as [R HR].
    assert (Hrel : Rel_eq (aslpRel w) R) by (apply aslpRel_of; exact HR).
    unfold getASLP. rewrite HR.
    exact (aslpOf_cong R (aslpRel w) (fun a b => iff_sym (Hrel a b)) P y).
  Qed.

  (** *** ASP and DSLP parts *)

  Definition aspPartAArr {X Y} (w : ASLPArr X Y) : ASPArr X Y :=
    mkASPArr (aspOf (aslpRel w)) (fun P b => aspOf_join (aslpRel w) P b).

  Definition dslpPartAArr {X Y} (w : ASLPArr X Y) : DSLPArr X Y :=
    mkDSLPArr (dslpOf (aslpRel w)) (fun P b => dslpOf_meet (aslpRel w) P b).

  Definition aspPartA {X Y} (w : ASLPArr X Y) : (X -> Prop) -> Y -> Prop :=
    getASPArr (aspPartAArr w).

  Definition dslpPartA {X Y} (w : ASLPArr X Y) : (X -> Prop) -> Y -> Prop :=
    getDSLPArr (dslpPartAArr w).

  Theorem aslp_split {X Y} (w : ASLPArr X Y) P y :
    getASLP w P y <-> (aspPartA w P y \/ dslpPartA w P y).
  Proof. exact (aslpRel_spec w P y). Qed.

  (** As for DSP, the parts agree with the direct formulas on the element:
      the ASP part admits [y] when the element admits it at [P] and not at
      [False]; the DSLP part when the element does not admit it at the
      complement of [P], or does at [False].  Classical in both
      directions. *)

  Theorem aspPartA_formula {X Y} (w : ASLPArr X Y) (P : X -> Prop) y :
    aspPartA w P y
    <-> getASLP w P y /\ ~ getASLP w (fun _ => False) y.
  Proof.
    unfold aspPartA, aspPartAArr. cbn.
    rewrite (aslpRel_spec w P y), (aslpRel_spec w (fun _ => False) y).
    unfold aslpOf, aspOf, dslpOf, asp, dslp. split.
    - intros [x [HP Hx]]. split.
      + left. exists x. split; [ exact HP | exact Hx ].
      + intros [[? [[] _]] | Hall]. exact (Hall x Hx).
    - intros [Hor Hn]. destruct Hor as [Ha | Hb]; [ exact Ha |].
      destruct (classic (exists x, aslpRel w x y)) as [[x0 Hx0] | Hno].
      + exists x0. split; [ exact (Hb x0 Hx0) | exact Hx0 ].
      + exfalso. apply Hn. right. intros x Hx. exact (Hno (ex_intro _ x Hx)).
  Qed.

  Theorem dslpPartA_formula {X Y} (w : ASLPArr X Y) (P : X -> Prop) y :
    dslpPartA w P y
    <-> ~ getASLP w (fun x => ~ P x) y \/ getASLP w (fun _ => False) y.
  Proof.
    unfold dslpPartA, dslpPartAArr. cbn.
    rewrite (aslpRel_spec w (fun x => ~ P x) y), (aslpRel_spec w (fun _ => False) y).
    unfold aslpOf, aspOf, dslpOf, asp, dslp. split.
    - intro Hall. destruct (classic (exists x, aslpRel w x y)) as [[x0 Hx0] | Hno].
      + left. intros [[x [HnP Hx]] | Hb].
        * exact (HnP (Hall x Hx)).
        * exact (Hb x0 Hx0 (Hall x0 Hx0)).
      + right. right. intros x Hx. exact (Hno (ex_intro _ x Hx)).
    - intros [Hn | Hbot] x Hx.
      + apply NNPP. intro HnP. apply Hn. left.
        exists x. split; [ exact HnP | exact Hx ].
      + exfalso. destruct Hbot as [[? [[] _]] | Hall]. exact (Hall x Hx).
  Qed.

  Theorem aslpRel_faithful {X Y} (w v : ASLPArr X Y) :
    Rel_eq (aslpRel w) (aslpRel v) -> ASLPArr_eq w v.
  Proof.
    intros H P y. rewrite (aslpRel_spec w P y), (aslpRel_spec v P y).
    exact (aslpOf_cong _ _ H P y).
  Qed.

  Theorem aslpRel_faithful_conv {X Y} (w v : ASLPArr X Y) :
    ASLPArr_eq w v -> Rel_eq (aslpRel w) (aslpRel v).
  Proof.
    intros H x y. unfold aslpRel. split.
    - intros [Hn Hs]. split; [|apply H; exact Hs].
      intro Hc. apply Hn. apply H. exact Hc.
    - intros [Hn Hs]. split; [|apply H; exact Hs].
      intro Hc. apply Hn. apply H. exact Hc.
  Qed.

  (** *** Operations and instances *)

  #[local] Obligation Tactic := idtac.

  #[program] Definition pure_ASLP {X Y} (h : X -> Y) : ASLPArr X Y :=
    fun P y => pureASP h P y \/ pureDSLP h P y.
  Next Obligation.
    intros X Y h. apply aslp_healthy_hom. exists (arr_pure h). intros P y. reflexivity.
  Qed.

  #[program] Definition comp_ASLP {X Y Z} (w : ASLPArr X Y) (v : ASLPArr Y Z) : ASLPArr X Z :=
    fun P z => compASP (aspPartAArr w) (aspPartAArr v) P z
               \/ compDSLP (dslpPartAArr w) (dslpPartAArr v) P z.
  Next Obligation.
    intros X Y Z w v. apply aslp_healthy_hom.
    exists (arr_comp (aslpRel w) (aslpRel v)). intros P z.
    unfold aspPartA, dslpPartA, aslpOf.
    rewrite (aspOf_comp (aslpRel w) (aslpRel v)),
      (dslpOf_comp (aslpRel w) (aslpRel v)). reflexivity.
  Qed.

  #[program] Definition first_ASLP {X Y C} (w : ASLPArr X Y) : ASLPArr (X * C) (Y * C) :=
    fun P q => @firstASP _ _ C (aspPartAArr w) P q \/ @firstDSLP _ _ C (dslpPartAArr w) P q.
  Next Obligation.
    intros X Y C w. apply aslp_healthy_hom. exists (arr_first (aslpRel w)). intros P q.
    unfold aspPartA, dslpPartA, aslpOf.
    rewrite (aspOf_first (aslpRel w)), (dslpOf_first (aslpRel w)). reflexivity.
  Qed.

  #[global] Instance Arrow_ASLPArr : Arrow ASLPArr := {
    arr_pure := @pure_ASLP; arr_comp := @comp_ASLP; arr_first := @first_ASLP
  }.

  #[global] Instance ASLPArr_eq_Equivalence {X Y} : Equivalence (@ASLPArr_eq X Y).
  Proof.
    constructor.
    - intros w P y. reflexivity.
    - intros w v H P y. symmetry. exact (H P y).
    - intros u w v H1 H2 P y. exact (iff_trans (H1 P y) (H2 P y)).
  Qed.

  #[global] Instance ArrowEq_ASLPArr : ArrowEq ASLPArr := {
    arrow_eq := @ASLPArr_eq; arrow_eq_equiv := @ASLPArr_eq_Equivalence
  }.

  Definition appRelA {A B} : SPureArr (ASLPArr A B * A) B :=
    fun p b => aslpRel (fst p) (snd p) b.

  #[program] Definition app_ASLP {A B} : ASLPArr (ASLPArr A B * A) B :=
    fun P b => aspOf appRelA P b \/ dslpOf appRelA P b.
  Next Obligation.
    intros A B. apply aslp_healthy_hom. exists appRelA. intros P b. reflexivity.
  Qed.

  #[global] Instance ArrowApply_ASLPArr : ArrowApply ASLPArr := { arr_app := @app_ASLP }.

  #[program] Definition left_ASLP {X Y C} (w : ASLPArr X Y) : ASLPArr (X + C) (Y + C) :=
    fun P y => @leftASP _ _ C (aspPartAArr w) P y \/ @leftDSLP _ _ C (dslpPartAArr w) P y.
  Next Obligation.
    intros X Y C w. apply aslp_healthy_hom. exists (arr_left (aslpRel w)).
    intros P [b | c]; unfold aslpOf.
    - unfold aspPartA, dslpPartA.
      rewrite (aspOf_left_inl (aslpRel w)), (dslpOf_left_inl (aslpRel w)). reflexivity.
    - rewrite (aspOf_left_inr (aslpRel w)), (dslpOf_left_inr (aslpRel w)). tauto.
  Qed.

  #[global] Instance ArrowChoice_ASLPArr : ArrowChoice ASLPArr := { arr_left := @left_ASLP }.

End ASLPImplementation.

(** ** ASLP relation contracts and selected-equality laws *)

Section ASLPRelation.

  (** *** Operation contracts *)

  Lemma aslpRel_pure {X Y} (h : X -> Y) : Rel_eq (aslpRel (pure_ASLP h)) (arr_pure h).
  Proof. apply aslpRel_of. intros P y. reflexivity. Qed.

  Lemma aslpRel_comp {X Y Z} (w : ASLPArr X Y) (v : ASLPArr Y Z) :
    Rel_eq (aslpRel (comp_ASLP w v)) (arr_comp (aslpRel w) (aslpRel v)).
  Proof.
    apply aslpRel_of. intros P z. unfold comp_ASLP, getASLP. cbn [proj1_sig].
    unfold aspPartA, dslpPartA, aslpOf.
    rewrite (aspOf_comp (aslpRel w) (aslpRel v)),
      (dslpOf_comp (aslpRel w) (aslpRel v)). reflexivity.
  Qed.

  Lemma aslpRel_first {X Y C} (w : ASLPArr X Y) :
    Rel_eq (aslpRel (@first_ASLP X Y C w)) (arr_first (aslpRel w)).
  Proof.
    apply aslpRel_of. intros P q. unfold first_ASLP, getASLP. cbn [proj1_sig].
    unfold aspPartA, dslpPartA, aslpOf.
    rewrite (aspOf_first (aslpRel w)), (dslpOf_first (aslpRel w)). reflexivity.
  Qed.

  Lemma aslpRel_left {X Y C} (w : ASLPArr X Y) :
    Rel_eq (aslpRel (@left_ASLP X Y C w)) (arr_left (aslpRel w)).
  Proof.
    apply aslpRel_of. intros P [b | c]; unfold left_ASLP, getASLP; cbn [proj1_sig]; unfold aslpOf.
    - unfold aspPartA, dslpPartA.
      rewrite (aspOf_left_inl (aslpRel w)), (dslpOf_left_inl (aslpRel w)). reflexivity.
    - rewrite (aspOf_left_inr (aslpRel w)), (dslpOf_left_inr (aslpRel w)). tauto.
  Qed.

  Lemma aslpRel_app {A B} : Rel_eq (aslpRel (@app_ASLP A B)) appRelA.
  Proof. apply aslpRel_of. intros P b. reflexivity. Qed.

  Lemma aslpRel_second {X Y C} (w : ASLPArr X Y) :
    Rel_eq (aslpRel (@arr_second ASLPArr Arrow_ASLPArr X Y C w))
      (@arr_second Rel Arrow_Rel X Y C (aslpRel w)).
  Proof.
    unfold arr_second. cbn [arr_comp arr_pure arr_first Arrow_ASLPArr].
    repeat first [setoid_rewrite aslpRel_comp | setoid_rewrite aslpRel_pure
      | setoid_rewrite aslpRel_first].
    reflexivity.
  Qed.

  (** *** Left/first combinations *)

  Lemma aslpRel_left2 {A B C D} (f : ASLPArr A B) :
    Rel_eq (aslpRel (@left_ASLP _ _ D (@left_ASLP A B C f))) (arr_left (arr_left (aslpRel f))).
  Proof. etransitivity; [apply aslpRel_left | apply Rel_left_cong; apply aslpRel_left]. Qed.

  Lemma aslpRel_first_left {A B C D} (f : ASLPArr A B) :
    Rel_eq (aslpRel (@first_ASLP _ _ D (@left_ASLP A B C f))) (arr_first (arr_left (aslpRel f))).
  Proof. etransitivity; [apply aslpRel_first | apply Rel_first_cong; apply aslpRel_left]. Qed.

  Lemma aslpRel_left_first {A B C D} (f : ASLPArr A B) :
    Rel_eq (aslpRel (@left_ASLP _ _ (C * D)%type (@first_ASLP A B D f)))
      (arr_left (arr_first (aslpRel f))).
  Proof. etransitivity; [apply aslpRel_left | apply Rel_left_cong; apply aslpRel_first]. Qed.

  (** *** Semantic contracts and law packages *)

  #[global] Instance RelArrow_ASLPArr : RelArrow ASLPArr := {|
    rel_reading := @aslpRel; rel_pure := @aslpRel_pure; rel_comp := @aslpRel_comp;
    rel_first := fun A B C f a c b d => aslpRel_first f (a, c) (b, d)
  |}.

  #[global] Instance RelArrowChoice_ASLPArr : RelArrowChoice ASLPArr :=
    {| rel_left := @aslpRel_left |}.

  #[global] Instance RelArrowApply_ASLPArr : RelArrowApply ASLPArr := {|
    rel_app := fun A B f a b => aslpRel_app (f, a) b
  |}.

  #[global] Instance RelArrowEq_ASLPArr : RelArrowEq ASLPArr := {|
    rel_arrow_eq := fun A B f g => conj (aslpRel_faithful_conv f g) (aslpRel_faithful f g)
  |}.

  #[global] Instance ArrowLaws_ASLPArr : ArrowLaws ASLPArr :=
    @rel_arrow_laws ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr RelArrow_ASLPArr RelArrowEq_ASLPArr.

  #[global] Instance ArrowChoiceLaws_ASLPArr : ArrowChoiceLaws ASLPArr :=
    @rel_arrow_choice_laws ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr RelArrow_ASLPArr
      RelArrowEq_ASLPArr ArrowChoice_ASLPArr RelArrowChoice_ASLPArr.

  #[global] Instance ArrowApplyLaws_ASLPArr : ArrowApplyLaws ASLPArr :=
    @rel_arrow_apply_laws ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr RelArrow_ASLPArr
      RelArrowEq_ASLPArr ArrowApply_ASLPArr RelArrowApply_ASLPArr.

End ASLPRelation.

(** ** DSP and ASLP binary transformer stacks
    Explicit dictionaries avoid recursive instance search. Unary monads and
    their runners fix the input in the specification-monad layer. *)

Section DSPStacks.

  (** *** State layer *)

  Definition DSPStArr (S : Type) := stateArrT S DSPArr.

  Definition ArrowEq_DSPStArr (S : Type) : ArrowEq (DSPStArr S) :=
    @ArrowEq_stateArrT S DSPArr ArrowEq_DSPArr.

  Definition ArrowLaws_DSPStArr (S : Type) : ArrowLaws (DSPStArr S) :=
    @ArrowLaws_stateArrT S DSPArr Arrow_DSPArr ArrowEq_DSPArr ArrowLaws_DSPArr.

  Definition ArrowApply_DSPStArr (S : Type) : ArrowApply (DSPStArr S) :=
    @ArrowApply_stateArrT S DSPArr Arrow_DSPArr ArrowApply_DSPArr.

  Definition ArrowApplyLaws_DSPStArr (S : Type) : ArrowApplyLaws (DSPStArr S) :=
    @ArrowApplyLaws_stateArrT S DSPArr Arrow_DSPArr ArrowApply_DSPArr
      ArrowEq_DSPArr ArrowLaws_DSPArr ArrowApplyLaws_DSPArr.

  (** *** Option layer *)

  Definition optDSP := optionArrT DSPArr.

  Definition Arrow_optDSP : Arrow optDSP :=
    @Arrow_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr.

  Definition ArrowEq_optDSP : ArrowEq optDSP :=
    @ArrowEq_optionArrT DSPArr ArrowEq_DSPArr.

  Definition ArrowLaws_optDSP : ArrowLaws optDSP :=
    @ArrowLaws_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr
      ArrowEq_DSPArr ArrowLaws_DSPArr ArrowChoiceLaws_DSPArr.

  Definition ArrowApply_optDSP : ArrowApply optDSP :=
    @ArrowApply_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr ArrowApply_DSPArr.

  Definition ArrowApplyLaws_optDSP : ArrowApplyLaws optDSP :=
    @ArrowApplyLaws_optionArrT DSPArr Arrow_DSPArr ArrowChoice_DSPArr
      ArrowApply_DSPArr ArrowEq_DSPArr ArrowLaws_DSPArr ArrowChoiceLaws_DSPArr
      ArrowApplyLaws_DSPArr.

  (** *** State-over-option layer *)

  Definition DSPStExcArr (S : Type) := stateArrT S optDSP.

  Definition ArrowEq_DSPStExcArr (S : Type) : ArrowEq (DSPStExcArr S) :=
    @ArrowEq_stateArrT S optDSP ArrowEq_optDSP.

  Definition ArrowLaws_DSPStExcArr (S : Type) : ArrowLaws (DSPStExcArr S) :=
    @ArrowLaws_stateArrT S optDSP Arrow_optDSP ArrowEq_optDSP ArrowLaws_optDSP.

  Definition ArrowApply_DSPStExcArr (S : Type) : ArrowApply (DSPStExcArr S) :=
    @ArrowApply_stateArrT S optDSP Arrow_optDSP ArrowApply_optDSP.

  Definition ArrowApplyLaws_DSPStExcArr (S : Type) : ArrowApplyLaws (DSPStExcArr S) :=
    @ArrowApplyLaws_stateArrT S optDSP Arrow_optDSP ArrowApply_optDSP
      ArrowEq_optDSP ArrowLaws_optDSP ArrowApplyLaws_optDSP.

End DSPStacks.

Section ASLPStacks.

  (** *** State layer *)

  Definition ASLPStArr (S : Type) := stateArrT S ASLPArr.

  Definition ArrowEq_ASLPStArr (S : Type) : ArrowEq (ASLPStArr S) :=
    @ArrowEq_stateArrT S ASLPArr ArrowEq_ASLPArr.

  Definition ArrowLaws_ASLPStArr (S : Type) : ArrowLaws (ASLPStArr S) :=
    @ArrowLaws_stateArrT S ASLPArr Arrow_ASLPArr ArrowEq_ASLPArr ArrowLaws_ASLPArr.

  Definition ArrowApply_ASLPStArr (S : Type) : ArrowApply (ASLPStArr S) :=
    @ArrowApply_stateArrT S ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr.

  Definition ArrowApplyLaws_ASLPStArr (S : Type) : ArrowApplyLaws (ASLPStArr S) :=
    @ArrowApplyLaws_stateArrT S ASLPArr Arrow_ASLPArr ArrowApply_ASLPArr
      ArrowEq_ASLPArr ArrowLaws_ASLPArr ArrowApplyLaws_ASLPArr.

  (** *** Option layer *)

  Definition optASLP := optionArrT ASLPArr.

  Definition Arrow_optASLP : Arrow optASLP :=
    @Arrow_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr.

  Definition ArrowEq_optASLP : ArrowEq optASLP :=
    @ArrowEq_optionArrT ASLPArr ArrowEq_ASLPArr.

  Definition ArrowLaws_optASLP : ArrowLaws optASLP :=
    @ArrowLaws_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr
      ArrowEq_ASLPArr ArrowLaws_ASLPArr ArrowChoiceLaws_ASLPArr.

  Definition ArrowApply_optASLP : ArrowApply optASLP :=
    @ArrowApply_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr ArrowApply_ASLPArr.

  Definition ArrowApplyLaws_optASLP : ArrowApplyLaws optASLP :=
    @ArrowApplyLaws_optionArrT ASLPArr Arrow_ASLPArr ArrowChoice_ASLPArr
      ArrowApply_ASLPArr ArrowEq_ASLPArr ArrowLaws_ASLPArr
      ArrowChoiceLaws_ASLPArr ArrowApplyLaws_ASLPArr.

  (** *** State-over-option layer *)

  Definition ASLPStExcArr (S : Type) := stateArrT S optASLP.

  Definition ArrowEq_ASLPStExcArr (S : Type) : ArrowEq (ASLPStExcArr S) :=
    @ArrowEq_stateArrT S optASLP ArrowEq_optASLP.

  Definition ArrowLaws_ASLPStExcArr (S : Type) : ArrowLaws (ASLPStExcArr S) :=
    @ArrowLaws_stateArrT S optASLP Arrow_optASLP ArrowEq_optASLP ArrowLaws_optASLP.

  Definition ArrowApply_ASLPStExcArr (S : Type) : ArrowApply (ASLPStExcArr S) :=
    @ArrowApply_stateArrT S optASLP Arrow_optASLP ArrowApply_optASLP.

  Definition ArrowApplyLaws_ASLPStExcArr (S : Type) : ArrowApplyLaws (ASLPStExcArr S) :=
    @ArrowApplyLaws_stateArrT S optASLP Arrow_optASLP ArrowApply_optASLP
      ArrowEq_optASLP ArrowLaws_optASLP ArrowApplyLaws_optASLP.

End ASLPStacks.

(** ** DSP/ASLP relation constructors and predicate congruence *)

Definition dspOfRelArr {X Y} (R : SPureArr X Y) : DSPArr X Y :=
  exist _ (dspOf R) (dsp_healthy_hom _ (ex_intro _ R (fun P y => iff_refl _))).

Lemma dspRel_ofRelArr {X Y} (R : SPureArr X Y) x y : dspRel (dspOfRelArr R) x y <-> R x y.
Proof. exact (dspRel_of R (dspOfRelArr R) (fun P y => iff_refl _) x y). Qed.

Lemma getDSP_cong {X Y} (w : DSPArr X Y) (P Q : X -> Prop) y :
  (forall x, P x <-> Q x) -> (getDSP w P y <-> getDSP w Q y).
Proof.
  intro H. rewrite (dspRel_spec w P y), (dspRel_spec w Q y).
  unfold dspOf, aspOf, dslpOf. split; intros [[x [Hx Hr]] Hall]; split.
  - exists x. split; [apply H; exact Hx | exact Hr].
  - intros x' Hr'. apply H. exact (Hall x' Hr').
  - exists x. split; [apply H; exact Hx | exact Hr].
  - intros x' Hr'. apply H. exact (Hall x' Hr').
Qed.

Definition aslpOfRelArr {X Y} (R : SPureArr X Y) : ASLPArr X Y :=
  exist _ (aslpOf R) (aslp_healthy_hom _ (ex_intro _ R (fun P y => iff_refl _))).

Lemma aslpRel_ofRelArr {X Y} (R : SPureArr X Y) x y : aslpRel (aslpOfRelArr R) x y <-> R x y.
Proof. exact (aslpRel_of R (aslpOfRelArr R) (fun P y => iff_refl _) x y). Qed.

Lemma getASLP_cong {X Y} (w : ASLPArr X Y) (P Q : X -> Prop) y :
  (forall x, P x <-> Q x) -> (getASLP w P y <-> getASLP w Q y).
Proof.
  intro H. rewrite (aslpRel_spec w P y), (aslpRel_spec w Q y).
  unfold aslpOf, aspOf, dslpOf. split; intros [[x [Hx Hr]] | Hall].
  - left. exists x. split; [apply H; exact Hx | exact Hr].
  - right. intros x' Hr'. apply H. exact (Hall x' Hr').
  - left. exists x. split; [apply H; exact Hx | exact Hr].
  - right. intros x' Hr'. apply H. exact (Hall x' Hr').
Qed.

(** ** The four classes are distinct

    One relation on [bool] separates them: its output [true] is reached from
    both inputs, and its output [false] from none.  Its DSP reading is
    neither top-preserving nor disjunctive, so it is the transformer of no
    DSLP arrow and of no ASP arrow.  Dually, its ASLP reading is neither
    strict nor conjunctive, so it is the transformer of no ASP arrow and of
    no DSLP arrow.  Its DSLP reading is not disjunctive, so no ASP arrow has
    it either.

    The failures at top and at the empty precondition use the unreachable
    output; the failures at joins and meets use the output with two
    predecessors.  DSP still preserves nonempty meets and ASLP nonempty
    joins: that is the healthiness of [DSPArr] and [ASLPArr]. *)

Definition trueFromBoth : SPureArr bool bool := fun _ y => y = true.

Theorem dspOf_not_terminating : ~ sp_terminating (dspOf trueFromBoth).
Proof.
  intro H. destruct (H false) as [[x [_ Hx]] _].
  change (false = true) in Hx. discriminate Hx.
Qed.

Theorem dspOf_not_disjunctive : ~ sp_disjunctive (dspOf trueFromBoth).
Proof.
  intro H.
  assert (Hj : dspOf trueFromBoth (fun x => exists i : bool, x = i) true).
  { split.
    - exists true. split; [ exists true; exact eq_refl | exact eq_refl ].
    - intros x _. exists x. exact eq_refl. }
  destruct (proj1 (H bool (inhabits true) (fun i x => x = i) true) Hj)
    as [i [_ Hi]].
  assert (Hn : negb i = i) by exact (Hi (negb i) eq_refl).
  destruct i; discriminate Hn.
Qed.

Theorem aslpOf_not_strict : ~ sp_strict (aslpOf trueFromBoth).
Proof.
  intro H. apply (H false). right. intros x Hx.
  change (false = true) in Hx. discriminate Hx.
Qed.

Theorem aslpOf_not_conjunctive : ~ sp_conjunctive (aslpOf trueFromBoth).
Proof.
  intro H.
  assert (Hm : forall i : bool, aslpOf trueFromBoth (fun x => x = i) true).
  { intro i. left. exists i. split; exact eq_refl. }
  destruct (proj2 (H bool (inhabits true) (fun i x => x = i) true) Hm)
    as [[x [Hx _]] | Hall].
  - assert (Ht : x = true) by exact (Hx true).
    assert (Hf : x = false) by exact (Hx false).
    rewrite Ht in Hf. discriminate Hf.
  - assert (Hf : true = false) by exact (Hall true eq_refl false).
    discriminate Hf.
Qed.

Theorem dslpOf_not_disjunctive : ~ sp_disjunctive (dslpOf trueFromBoth).
Proof.
  intro H.
  assert (Hj : dslpOf trueFromBoth (fun x => exists i : bool, x = i) true).
  { intros x _. exists x. exact eq_refl. }
  destruct (proj1 (H bool (inhabits true) (fun i x => x = i) true) Hj)
    as [i Hi].
  assert (Hn : negb i = i) by exact (Hi (negb i) eq_refl).
  destruct i; discriminate Hn.
Qed.

(** Healthiness is a property of the transformer up to pointwise
    equivalence. *)
Lemma sp_disjunctive_iff {A B} (f g : SPArrT A B) :
  (forall P b, f P b <-> g P b) -> sp_disjunctive f -> sp_disjunctive g.
Proof.
  intros E Hd I HI p b. split.
  - intro Hg. destruct (proj1 (Hd I HI p b) (proj2 (E _ b) Hg)) as [i Hi].
    exists i. exact (proj1 (E _ b) Hi).
  - intros [i Hi]. apply (proj1 (E _ b)). apply (proj2 (Hd I HI p b)).
    exists i. exact (proj2 (E _ b) Hi).
Qed.

Lemma sp_conjunctive_iff {A B} (f g : SPArrT A B) :
  (forall P b, f P b <-> g P b) -> sp_conjunctive f -> sp_conjunctive g.
Proof.
  intros E Hc I HI p b. split.
  - intros Hg i.
    exact (proj1 (E _ b) (proj1 (Hc I HI p b) (proj2 (E _ b) Hg) i)).
  - intro Hall. apply (proj1 (E _ b)). apply (proj2 (Hc I HI p b)).
    intro i. exact (proj2 (E _ b) (Hall i)).
Qed.

Corollary no_ASPArr_for_dsp :
  ~ exists w : ASPArr bool bool,
      forall P y, getASPArr w P y <-> dspOf trueFromBoth P y.
Proof.
  intros [w E]. apply dspOf_not_disjunctive.
  exact (sp_disjunctive_iff _ _ E (proj2 (proj2 (proj2_sig w)))).
Qed.

Corollary no_DSLPArr_for_dsp :
  ~ exists w : DSLPArr bool bool,
      forall P y, getDSLPArr w P y <-> dspOf trueFromBoth P y.
Proof.
  intros [w E]. apply dspOf_not_terminating.
  intro b. exact (proj1 (E _ b) (proj1 (proj2 (proj2_sig w)) b)).
Qed.

Corollary no_ASPArr_for_aslp :
  ~ exists w : ASPArr bool bool,
      forall P y, getASPArr w P y <-> aslpOf trueFromBoth P y.
Proof.
  intros [w E]. apply aslpOf_not_strict.
  intros b Hb. exact (proj1 (proj2 (proj2_sig w)) b (proj2 (E _ b) Hb)).
Qed.

Corollary no_DSLPArr_for_aslp :
  ~ exists w : DSLPArr bool bool,
      forall P y, getDSLPArr w P y <-> aslpOf trueFromBoth P y.
Proof.
  intros [w E]. apply aslpOf_not_conjunctive.
  exact (sp_conjunctive_iff _ _ E (proj2 (proj2 (proj2_sig w)))).
Qed.

Corollary no_ASPArr_for_dslp :
  ~ exists w : ASPArr bool bool,
      forall P y, getASPArr w P y <-> dslpOf trueFromBoth P y.
Proof.
  intros [w E]. apply dslpOf_not_disjunctive.
  exact (sp_disjunctive_iff _ _ E (proj2 (proj2 (proj2_sig w)))).
Qed.
