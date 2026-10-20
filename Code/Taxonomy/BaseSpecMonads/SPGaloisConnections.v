(** * Galois connections between the SP monads and the skew monad

    [SPStMon S A] ([SPPredicateTransformers.v]) is the lattice of monotone
    stateful strongest-postcondition transformers, ordered pointwise, with the
    angelic and demonic skew-monad structures of [SPStMonotone].  This file
    relates it to the SP monads and to pre/post pairs.

    - Evaluation at a precondition, [spAt P w = w P], has IL's index as left
      adjoint and Hoare's index as right adjoint ([il_spAt_adjunction],
      [spAt_hoare_adjunction]).
    - ASP, the transformers determined by singletons, is coreflective: its
      inclusion has the interior as right adjoint ([asp_coreflective]).
      DSLP, determined by co-singletons, is reflective, with the exterior as
      left adjoint ([dslp_reflective]).
    - So ASP keeps Hoare's adjoint and DSLP keeps IL's ([asp_hoare],
      [dslp_il]); they are [pp2asp_over] and [pp2dslp_under].  ASP loses IL's
      once [P] has two states, and DSLP loses Hoare's once the complement of
      [P] does ([asp_no_il_adjoint], [dslp_no_hoare_adjoint]).
    - The skew is exactly the interior (angelic) or the exterior (demonic):
      they are the left-unit defects ([skew_left_unit], [demonic_left_unit])
      and strict monad morphisms onto ASP and DSLP.  Discarding [get] yields
      them too ([skew_discard_get], [demonic_discard_get]), which is why IL
      and DSLP Over are exact here although no monad types them.
    - With relational postconditions the adjunction is global:
      [witRel ⊣ strongest ⊣ hoareRel] on programs ([wit_strongest],
      [strongest_hoare]). *)

From Coq Require Import RelationClasses Setoid Classical_Prop.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
Import SPStMonotone.

Section Lattice.
  Variables S A : Type.
  Local Notation T := (SPStMon S A).

  (** The strongest postcondition at [P]. *)
  Definition spAt (P : S -> Prop) (w : T) : A * S -> Prop := fun r => proj1_sig w P r.

  (** IL's index and Hoare's index. *)
  #[program] Definition ilIdx (P : S -> Prop) (Q : A * S -> Prop) : T :=
    fun p r => (forall s, P s -> p s) /\ Q r.
  Next Obligation.
    intros p p' r Hpp' [HP Hq]. split; [ intros s Hs; exact (Hpp' s (HP s Hs)) | exact Hq ].
  Qed.

  #[program] Definition hoareIdx (P : S -> Prop) (Q : A * S -> Prop) : T :=
    fun p r => (forall s, p s -> P s) -> Q r.
  Next Obligation.
    intros p p' r Hpp' H Hp'. apply H. intros s Hs. exact (Hp' s (Hpp' s Hs)).
  Qed.

  (* ================================================================= *)
  (** ** [ilIdx P ⊣ spAt P ⊣ hoareIdx P]                                *)
  (* ================================================================= *)

  Theorem il_spAt_adjunction P Q (w : T) : ilIdx P Q ≦ w <-> (forall r, Q r -> spAt P w r).
  Proof.
    split.
    - intros H r Hr. exact (H P r (conj (fun s Hs => Hs) Hr)).
    - intros H p r [HP Hr]. exact (proj2_sig w P p r HP (H r Hr)).
  Qed.

  Theorem spAt_hoare_adjunction P Q (w : T) : (forall r, spAt P w r -> Q r) <-> w ≦ hoareIdx P Q.
  Proof.
    split.
    - intros H p r Hw Hp. apply H. exact (proj2_sig w p P r Hp Hw).
    - intros H r Hw. exact (H P r Hw (fun s Hs => Hs)).
  Qed.

  (* ================================================================= *)
  (** ** ASP is coreflective, DSLP is reflective                        *)
  (* ================================================================= *)

  (** ASP: determined by singletons ([SingletonProg]). *)
  Definition Additive (w : T) : Prop :=
    forall p r, proj1_sig w p r <-> exists s, p s /\ proj1_sig w (fun t => t = s) r.

  #[program] Definition interior (w : T) : T :=
    fun p r => exists s, p s /\ proj1_sig w (fun t => t = s) r.
  Next Obligation.
    intros p p' r Hpp' [s [Hs Hw]]. exists s. split; [ exact (Hpp' s Hs) | exact Hw ].
  Qed.

  Lemma interior_additive w : Additive (interior w).
  Proof.
    intros p r. cbn. split.
    - intros [s [Hs Hw]]. exists s. split; [ exact Hs |]. exists s. split; [ reflexivity | exact Hw ].
    - intros [s [Hs [t [E Hw]]]]. rewrite E in Hw. exists s. split; assumption.
  Qed.

  Lemma interior_le w : interior w ≦ w.
  Proof.
    intros p r [s [Hs Hw]]. revert Hw. apply (proj2_sig w). intros t E. rewrite E. exact Hs.
  Qed.

  Theorem asp_coreflective (v w : T) : Additive v -> (v ≦ w <-> v ≦ interior w).
  Proof.
    intro Hv. split.
    - intros H p r Hvp. destruct (proj1 (Hv p r) Hvp) as [s [Hs Hs']].
      exists s. split; [ exact Hs | exact (H _ _ Hs') ].
    - intros H p r Hvp. exact (interior_le w p r (H p r Hvp)).
  Qed.

  (** DSLP: determined by co-singletons ([MSingletonProg]). *)
  Definition Coadditive (w : T) : Prop :=
    forall p r, proj1_sig w p r <-> forall s, ~ p s -> proj1_sig w (fun t => t <> s) r.

  #[program] Definition exterior (w : T) : T :=
    fun p r => forall s, ~ p s -> proj1_sig w (fun t => t <> s) r.
  Next Obligation. intros p p' r Hpp' H s Hs. apply H. intro Hp. exact (Hs (Hpp' s Hp)). Qed.

  Lemma le_exterior w : w ≦ exterior w.
  Proof.
    intros p r Hw s Hs. revert Hw. apply (proj2_sig w). intros t Ht E. rewrite E in Ht. exact (Hs Ht).
  Qed.

  Lemma exterior_coadditive w : Coadditive (exterior w).
  Proof.
    intros p r. cbn. split.
    - intros H s Hs t Ht. assert (E : t = s) by (apply NNPP; exact Ht). rewrite E. exact (H s Hs).
    - intros H s Hs. exact (H s Hs s (fun E => E eq_refl)).
  Qed.

  Lemma coadditive_fixed (v : T) : Coadditive v -> exterior v ≈ v.
  Proof.
    intro Hv. split; [| exact (le_exterior v) ].
    intros p r H. exact (proj2 (Hv p r) H).
  Qed.

  Theorem dslp_reflective (v w : T) : Coadditive v -> (exterior w ≦ v <-> w ≦ v).
  Proof.
    intro Hv. split.
    - intros H p r Hw. exact (H p r (le_exterior w p r Hw)).
    - intros H p r He. apply (proj2 (Hv p r)). intros s Hs. exact (H _ _ (He s Hs)).
  Qed.

  (* ================================================================= *)
  (** ** Each SP monad keeps one adjoint of [spAt P]                     *)
  (* ================================================================= *)

  (** ASP keeps Hoare's: [interior (hoareIdx P Q)], which is [pp2asp_over]. *)
  Corollary asp_hoare P Q (v : T) :
    Additive v -> ((forall r, spAt P v r -> Q r) <-> v ≦ interior (hoareIdx P Q)).
  Proof. intro Hv. rewrite (spAt_hoare_adjunction P Q v). exact (asp_coreflective v (hoareIdx P Q) Hv). Qed.

  Lemma interior_hoareIdx P Q p r :
    proj1_sig (interior (hoareIdx P Q)) p r <-> exists s, p s /\ (P s -> Q r).
  Proof.
    cbn. split.
    - intros [s [Hs H]]. exists s. split; [ exact Hs |]. intro HP. apply H. intros t E. rewrite E. exact HP.
    - intros [s [Hs H]]. exists s. split; [ exact Hs |]. intro Hsub. exact (H (Hsub s eq_refl)).
  Qed.

  (** DSLP keeps IL's: [exterior (ilIdx P Q)], which is [pp2dslp_under]. *)
  Corollary dslp_il P Q (v : T) :
    Coadditive v -> ((forall r, Q r -> spAt P v r) <-> exterior (ilIdx P Q) ≦ v).
  Proof.
    intro Hv. rewrite <- (il_spAt_adjunction P Q v). symmetry. exact (dslp_reflective v (ilIdx P Q) Hv).
  Qed.

  Lemma exterior_ilIdx P Q p r :
    proj1_sig (exterior (ilIdx P Q)) p r <-> (forall s, (Q r -> P s) -> p s).
  Proof.
    cbn. split.
    - intros H s Himp. apply NNPP. intro Hns. destruct (H s Hns) as [HP Hq].
      exact (HP s (Himp Hq) eq_refl).
    - intros H s Hns. split.
      + intros t Ht E. rewrite E in Ht. apply Hns, H. intros _. exact Ht.
      + apply NNPP. intro Hnq. apply Hns, H. intro Hq. contradiction.
  Qed.

  (** Reach [Q] from [s0], and nothing from elsewhere. *)
  #[program] Definition reachFrom (s0 : S) (Q : A * S -> Prop) : T := fun p r => p s0 /\ Q r.
  Next Obligation. intros p p' r Hpp' [Hs Hq]. split; [ exact (Hpp' s0 Hs) | exact Hq ]. Qed.

  Lemma reachFrom_additive s0 Q : Additive (reachFrom s0 Q).
  Proof.
    intros p r. cbn. split.
    - intros [Hs Hq]. exists s0. split; [ exact Hs | split; [ reflexivity | exact Hq ] ].
    - intros [s [Hs [E Hq]]]. rewrite E. split; assumption.
  Qed.

  (** ASP loses IL's adjoint once [P] has two states. *)
  Theorem asp_no_il_adjoint (p1 p2 : S) (r0 : A * S) :
    p1 <> p2 ->
    let P := fun s => s = p1 \/ s = p2 in
    let Q := fun r => r = r0 in
    ~ exists L : T, Additive L /\
        forall v : T, Additive v -> (L ≦ v <-> forall r, Q r -> spAt P v r).
  Proof.
    intros Hne P Q [L [HL Hadj]].
    assert (H1 : L ≦ reachFrom p1 Q).
    { apply (proj2 (Hadj _ (reachFrom_additive p1 Q))). intros r Hr. split; [ left; reflexivity | exact Hr ]. }
    assert (H2 : L ≦ reachFrom p2 Q).
    { apply (proj2 (Hadj _ (reachFrom_additive p2 Q))). intros r Hr. split; [ right; reflexivity | exact Hr ]. }
    assert (HP : spAt P L r0).
    { apply (proj1 (Hadj L HL) (fun p r H => H) r0). reflexivity. }
    destruct (proj1 (HL P r0) HP) as [s [[-> | ->] Hs]].
    - destruct (H2 _ _ Hs) as [E _]. exact (Hne (eq_sym E)).
    - destruct (H1 _ _ Hs) as [E _]. exact (Hne E).
  Qed.

  (** Reach [r0] only from [s0]; read demonically. *)
  #[program] Definition onlyFrom (s0 : S) (r0 : A * S) : T := fun p r => r = r0 -> p s0.
  Next Obligation. intros p p' r Hpp' H E. exact (Hpp' s0 (H E)). Qed.

  Lemma onlyFrom_coadditive s0 r0 : Coadditive (onlyFrom s0 r0).
  Proof.
    intros p r. cbn. split.
    - intros H s Hs E E'. rewrite E' in H. exact (Hs (H E)).
    - intros H E. apply NNPP. intro Hn. exact (H s0 Hn E eq_refl).
  Qed.

  (** DSLP loses Hoare's adjoint once the complement of [P] has two states. *)
  Theorem dslp_no_hoare_adjoint (q1 q2 : S) (r0 : A * S) :
    q1 <> q2 ->
    let P := fun s => s <> q1 /\ s <> q2 in
    let Q := fun r => r <> r0 in
    ~ exists U : T, Coadditive U /\
        forall v : T, Coadditive v -> (v ≦ U <-> forall r, spAt P v r -> Q r).
  Proof.
    intros Hne P Q [U [HU Hadj]].
    assert (H1 : onlyFrom q1 r0 ≦ U).
    { apply (proj2 (Hadj _ (onlyFrom_coadditive q1 r0))). intros r H E. destruct (H E) as [F _]. exact (F eq_refl). }
    assert (H2 : onlyFrom q2 r0 ≦ U).
    { apply (proj2 (Hadj _ (onlyFrom_coadditive q2 r0))). intros r H E. destruct (H E) as [_ F]. exact (F eq_refl). }
    apply (proj1 (Hadj U HU) (fun p r H => H) r0); [| reflexivity ].
    apply (proj2 (HU P r0)). intros s Hs.
    destruct (classic (s = q1)) as [-> | Hs1].
    - apply H2. intros _. exact (fun E => Hne (eq_sym E)).
    - assert (Hs2 : s = q2) by (apply NNPP; intro Hs2; exact (Hs (conj Hs1 Hs2))).
      rewrite Hs2. apply H1. intros _. exact Hne.
  Qed.

  (* ================================================================= *)
  (** ** Pointed preconditions repair only the nullary failure           *)
  (* ================================================================= *)

  Lemma ilIdx_one_additive (p : S) Q : Additive (ilIdx (fun s => s = p) Q).
  Proof.
    intros p' r. cbn. split.
    - intros [HP Hq]. exists p. split; [ exact (HP p eq_refl) | split; [ intros t E; exact E | exact Hq ] ].
    - intros [s [Hs [HP Hq]]]. split; [ intros t E; rewrite E, (HP p eq_refl); exact Hs | exact Hq ].
  Qed.

  Lemma ilIdx_empty_not_additive Q r0 : Q r0 -> ~ Additive (ilIdx (fun _ => False) Q).
  Proof.
    intros Hq Ha. destruct (proj1 (Ha (fun _ => False) r0) (conj (fun s F => F) Hq)) as [s [[] _]].
  Qed.

  Lemma ilIdx_two_not_additive (p1 p2 : S) r0 P Q :
    p1 <> p2 -> P p1 -> P p2 -> Q r0 -> ~ Additive (ilIdx P Q).
  Proof.
    intros Hne H1 H2 Hq Ha.
    destruct (proj1 (Ha P r0) (conj (fun s Hs => Hs) Hq)) as [s [_ [HP _]]].
    apply Hne. rewrite (HP p1 H1), (HP p2 H2). reflexivity.
  Qed.
End Lattice.

(* ================================================================= *)
(** ** The angelic skew monad: ASP is its coreflective submonad         *)
(* ================================================================= *)

Section AngelicSkew.
  Context {S : Type}.
  Local Notation retA := AngelicMonotone.ret.
  Local Notation bindA := AngelicMonotone.bind.

  (** The left-unit defect is exactly the interior. *)
  Theorem skew_left_unit {A B} (a : A) (f : A -> SPStMon S B) :
    bindA (retA a) f ≈ interior S B (f a).
  Proof.
    split; intros pre r; cbn.
    - intros [a' [si [[Hsi E] Hf]]]. subst a'. exists si. split; assumption.
    - intros [s [Hs Hf]]. exists a, s. split; [ split; [ exact Hs | reflexivity ] | exact Hf ].
  Qed.

  (** ASP is closed under [ret], and under [bind] with any continuation. *)
  Lemma ret_additive {A} (a : A) : Additive S A (retA a).
  Proof.
    intros p r. cbn. split.
    - intros [Hp E]. exists (snd r). split; [ exact Hp | split; [ reflexivity | exact E ] ].
    - intros [s [Hs [E1 E2]]]. rewrite E1. split; assumption.
  Qed.

  Lemma bind_additive {A B} (m : SPStMon S A) (f : A -> SPStMon S B) :
    Additive S A m -> Additive S B (bindA m f).
  Proof.
    intros Hm p r. cbn. split.
    - intros [a [si [Hma Hf]]]. destruct (proj1 (Hm p (a, si)) Hma) as [s [Hs Hms]].
      exists s. split; [ exact Hs |]. exists a, si. split; assumption.
    - intros [s [Hs [a [si [Hms Hf]]]]]. exists a, si. split; [| exact Hf ].
      revert Hms. apply (proj2_sig m). intros t E. rewrite E. exact Hs.
  Qed.

  (** The interior is a strict monad morphism. *)
  Theorem interior_ret {A} (a : A) : interior S A (retA a) ≈ retA a.
  Proof.
    split; intros pre r; cbn.
    - intros [s [Hs [E1 E2]]]. rewrite E1. split; assumption.
    - intros [Hp E]. exists (snd r). split; [ exact Hp | split; [ reflexivity | exact E ] ].
  Qed.

  Theorem interior_bind {A B} (m : SPStMon S A) (f : A -> SPStMon S B) :
    interior S B (bindA m f) ≈ bindA (interior S A m) (fun a => interior S B (f a)).
  Proof.
    split; intros pre r; cbn.
    - intros [s [Hs [a [si [Hm Hf]]]]]. exists a, si.
      split; [ exists s; split; assumption | exists si; split; [ reflexivity | exact Hf ] ].
    - intros [a [si [[s [Hs Hm]] [t [E Hf]]]]]. rewrite E in Hf.
      exists s. split; [ exact Hs |]. exists a, si. split; assumption.
  Qed.

  (** [get] read angelically; discarding it gives the interior. *)
  #[program] Definition getASP : SPStMon S S := fun p r => p (snd r) /\ fst r = snd r.
  Next Obligation. intros p p' r Hpp' [Hp E]. split; [ exact (Hpp' _ Hp) | exact E ]. Qed.

  Theorem skew_discard_get {B} (w : SPStMon S B) : bindA getASP (fun _ => w) ≈ interior S B w.
  Proof.
    split; intros pre r; cbn.
    - intros [a [si [[Hsi E] Hw]]]. exists si. split; assumption.
    - intros [s [Hs Hw]]. exists s, s. split; [ split; [ exact Hs | reflexivity ] | exact Hw ].
  Qed.

  (** A relation's angelic reading; IL and Hoare are exact typings here. *)
  #[program] Definition liftRel {A} (R : S -> A * S -> Prop) : SPStMon S A :=
    fun p r => exists s, p s /\ R s r.
  Next Obligation. intros p p' r Hpp' [s [Hs HR]]. exists s. split; [ exact (Hpp' s Hs) | exact HR ]. Qed.

  Corollary il_exact {A} (P : S -> Prop) (Q : A * S -> Prop) (R : S -> A * S -> Prop) :
    (forall r, Q r -> exists s, P s /\ R s r) <-> ilIdx S A P Q ≦ liftRel R.
  Proof. rewrite il_spAt_adjunction. reflexivity. Qed.

  Corollary hoare_exact {A} (P : S -> Prop) (Q : A * S -> Prop) (R : S -> A * S -> Prop) :
    (forall s r, P s -> R s r -> Q r) <-> liftRel R ≦ hoareIdx S A P Q.
  Proof.
    rewrite <- spAt_hoare_adjunction. cbn. split.
    - intros H r [s [Hs HR]]. exact (H s r Hs HR).
    - intros H s r Hs HR. exact (H r (ex_intro _ s (conj Hs HR))).
  Qed.
End AngelicSkew.

(* ================================================================= *)
(** ** The demonic skew monad: DSLP is its reflective submonad          *)
(* ================================================================= *)

Section DemonicSkew.
  Context {S : Type}.
  Local Notation retD := DemonicMonotone.ret.
  Local Notation bindD := DemonicMonotone.bind.

  (** The demonic bind reads its continuation at co-singletons only. *)
  Lemma guard_cosingleton {A B} (f : A -> SPStMon S B) a si r :
    (forall prei, proj1_sig (f a) prei r -> prei si) <-> ~ proj1_sig (f a) (fun t => t <> si) r.
  Proof.
    split.
    - intros H Hf. exact (H _ Hf eq_refl).
    - intros Hn prei Hf. apply NNPP. intro Hp. apply Hn. revert Hf. apply (proj2_sig (f a)).
      intros t Ht E. rewrite E in Ht. exact (Hp Ht).
  Qed.

  (** The left-unit defect is exactly the exterior. *)
  Theorem demonic_left_unit {A B} (a : A) (f : A -> SPStMon S B) :
    bindD (retD a) f ≈ exterior S B (f a).
  Proof.
    split; intros p r; cbn.
    - intros H s Hs. apply NNPP. intro Hn.
      exact (Hs (H a s (proj2 (guard_cosingleton f a s r) Hn) eq_refl)).
    - intros H a' si C E. subst a'. apply NNPP. intro Hn.
      exact (proj1 (guard_cosingleton f a si r) C (H si Hn)).
  Qed.

  (** The right unit and associativity hold exactly, strengthening
      [DemonicMonotone.runit] and [DemonicMonotone.assoc]. *)
  Theorem demonic_right_unit {A} (m : SPStMon S A) : bindD m retD ≈ m.
  Proof.
    split; intros p r; cbn.
    - intro H. rewrite (surjective_pairing r). apply H. intros prei Hp. exact (Hp eq_refl).
    - intros Hm a si C.
      destruct (C (fun t => fst r = a /\ t = snd r) (fun E => conj E eq_refl)) as [E1 E2].
      destruct r as [b t]. cbn in E1, E2. subst. exact Hm.
  Qed.

  Theorem demonic_assoc {A B C} (m : SPStMon S A) (f : A -> SPStMon S B) (g : B -> SPStMon S C) :
    bindD m (fun a => bindD (f a) g) ≈ bindD (bindD m f) g.
  Proof.
    split; [ exact (DemonicMonotone.assoc m f g) |].
    intros p r H a si Hc.
    apply (proj1 (guard_cosingleton (fun a => bindD (f a) g) a si r)) in Hc.
    apply NNPP. intro Hm. apply Hc. intros b ti Hg.
    apply NNPP. intro Hf. apply Hm.
    exact (H b ti Hg a si (proj2 (guard_cosingleton f a si (b, ti)) Hf)).
  Qed.

  (** DSLP is closed under [ret], and under [bind] with any continuation. *)
  Lemma retD_coadditive {A} (a : A) : Coadditive S A (retD a).
  Proof.
    intros p r. cbn. split.
    - intros H s Hs E E'. rewrite E' in H. exact (Hs (H E)).
    - intros H E. apply NNPP. intro Hn. exact (H (snd r) Hn E eq_refl).
  Qed.

  Lemma bindD_coadditive {A B} (m : SPStMon S A) (f : A -> SPStMon S B) :
    Coadditive S A m -> Coadditive S B (bindD m f).
  Proof.
    intros Hm p r. cbn. split.
    - intros H s Hs a si C. exact (proj1 (Hm p (a, si)) (H a si C) s Hs).
    - intros H a si C. apply (proj2 (Hm p (a, si))). intros s Hs. exact (H s Hs a si C).
  Qed.

  (** The exterior is a strict monad morphism. *)
  Theorem exterior_retD {A} (a : A) : exterior S A (retD a) ≈ retD a.
  Proof. exact (coadditive_fixed S A (retD a) (retD_coadditive a)). Qed.

  Theorem exterior_bindD {A B} (m : SPStMon S A) (f : A -> SPStMon S B) :
    exterior S B (bindD m f) ≈ bindD (exterior S A m) (fun a => exterior S B (f a)).
  Proof.
    split; intros p r; cbn.
    - intros H a si Cext s Hs. apply (H s Hs a si).
      apply (proj2 (guard_cosingleton f a si r)). intro Hf.
      apply (proj1 (guard_cosingleton (fun a => exterior S B (f a)) a si r) Cext).
      intros t Ht. assert (E : t = si) by (apply NNPP; exact Ht). rewrite E. exact Hf.
    - intros H s Hs a si Cf. apply (H a si); [| exact Hs ].
      apply (proj2 (guard_cosingleton (fun a => exterior S B (f a)) a si r)). intro He.
      exact (proj1 (guard_cosingleton f a si r) Cf (He si (fun E => E eq_refl))).
  Qed.

  (** [get] read demonically; discarding it gives the exterior. *)
  #[program] Definition getDSLP : SPStMon S S := fun p r => fst r = snd r -> p (snd r).
  Next Obligation. intros p p' r Hpp' H E. exact (Hpp' _ (H E)). Qed.

  Theorem demonic_discard_get {B} (w : SPStMon S B) : bindD getDSLP (fun _ => w) ≈ exterior S B w.
  Proof.
    split; intros p r; cbn.
    - intros H s Hs. apply NNPP. intro Hn.
      exact (Hs (H s s (proj2 (guard_cosingleton (fun _ : S => w) s s r) Hn) eq_refl)).
    - intros H a si C E. apply NNPP. intro Hn.
      exact (proj1 (guard_cosingleton (fun _ : S => w) a si r) C (H si Hn)).
  Qed.
End DemonicSkew.

(* ================================================================= *)
(** ** Relational postconditions: a global adjunction                   *)
(* ================================================================= *)

Section Relational.
  Variables S A : Type.
  Local Notation T := (SPStMon S A).

  (** A precondition on start states, and a postcondition relating each start
      state to outcomes. *)
  Definition RPP : Type := ((S -> Prop) * (S -> A * S -> Prop))%type.

  (** Hoare's (dependent) order, and the witness order. *)
  Definition leHoare (x y : RPP) : Prop :=
    forall s, fst y s -> fst x s /\ forall r, snd x s r -> snd y s r.
  Definition leWit (x y : RPP) : Prop :=
    forall s, fst x s -> fst y s /\ forall r, snd x s r -> snd y s r.

  (** What a transformer does from each single start state. *)
  Definition strongest (w : T) : RPP := (fun _ => True, fun s r => proj1_sig w (fun t => t = s) r).

  #[program] Definition hoareRel (x : RPP) : T := fun p r => exists s, p s /\ (fst x s -> snd x s r).
  Next Obligation. intros p p' r Hpp' [s [Hs H]]. exists s. split; [ exact (Hpp' s Hs) | exact H ]. Qed.

  #[program] Definition witRel (x : RPP) : T := fun p r => exists s, p s /\ fst x s /\ snd x s r.
  Next Obligation. intros p p' r Hpp' [s [Hs H]]. exists s. split; [ exact (Hpp' s Hs) | exact H ]. Qed.

  (** [witRel ⊣ strongest], on every monotone transformer. *)
  Theorem wit_strongest (x : RPP) (w : T) : witRel x ≦ w <-> leWit x (strongest w).
  Proof.
    split.
    - intros H s Hs. split; [ exact I |]. intros r Hq. apply H. exists s. split; [ reflexivity | split; assumption ].
    - intros H p r [s [Hs [HP Hq]]].
      apply (proj2_sig w (fun t => t = s) p r); [ intros t E; rewrite E; exact Hs |].
      exact (proj2 (H s HP) r Hq).
  Qed.

  (** [strongest ⊣ hoareRel], on programs. *)
  Theorem strongest_hoare (x : RPP) (w : T) :
    Additive S A w -> (leHoare (strongest w) x <-> w ≦ hoareRel x).
  Proof.
    intro Hw. split.
    - intros H p r Hwr. destruct (proj1 (Hw p r) Hwr) as [s [Hs Hs']].
      exists s. split; [ exact Hs |]. intro HP. exact (proj2 (H s HP) r Hs').
    - intros H s HP. split; [ exact I |]. intros r Hs'.
      destruct (H _ _ Hs') as [t [E Ht]]. cbn in E. rewrite E in Ht. exact (Ht HP).
  Qed.

  (** They are Hoare and the witnessed triple, with relational postconditions. *)
  Lemma leHoare_strongest_iff (x : RPP) (w : T) :
    leHoare (strongest w) x <->
    forall s, fst x s -> forall r, proj1_sig w (fun t => t = s) r -> snd x s r.
  Proof.
    split.
    - intros H s HP. exact (proj2 (H s HP)).
    - intros H s HP. split; [ exact I | exact (H s HP) ].
  Qed.

  Lemma leWit_strongest_iff (x : RPP) (w : T) :
    leWit x (strongest w) <->
    forall s, fst x s -> forall r, snd x s r -> proj1_sig w (fun t => t = s) r.
  Proof.
    split.
    - intros H s HP. exact (proj2 (H s HP)).
    - intros H s HP. split; [ exact I | exact (H s HP) ].
  Qed.
End Relational.

(** Off programs, [strongest ⊣ hoareRel] fails: a transformer that acts only
    on the two-state precondition has an empty strongest pair. *)
#[program] Definition bothStates : SPStMon bool unit :=
  fun p r => (p true /\ p false) /\ r = (tt, true).
Next Obligation.
  intros p p' r Hpp' [[Ht Hf] E]. split; [ split; [ exact (Hpp' _ Ht) | exact (Hpp' _ Hf) ] | exact E ].
Qed.

Theorem strongest_hoare_needs_additive :
  leHoare bool unit (strongest bool unit bothStates) (fun _ => True, fun _ _ => False)
  /\ ~ bothStates ≦ hoareRel bool unit (fun _ => True, fun _ _ => False).
Proof.
  split.
  - intros s _. split; [ exact I |]. intros r [[Ht Hf] _]. cbn in Ht, Hf. congruence.
  - intro H. destruct (H (fun _ => True) (tt, true) (conj (conj I I) eq_refl)) as [s [_ F]]. exact (F I).
Qed.
