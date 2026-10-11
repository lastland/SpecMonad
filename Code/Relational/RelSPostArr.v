(** * Strongest-postcondition readings of the relational arrow.

    An arrow is a [Rel A B] relation. Its predicate transformer is derived
    from that relation using four readings:

    [asp R pre b = exists a, pre a /\ R a b]   (angelic / existential)
    [dslp R pre b = forall a, R a b -> pre a]  (demonic liberal / universal)
    [dspOf R pre b = asp R pre b /\ dslp R pre b]  (demonic, total)
    [aslpOf R pre b = asp R pre b \/ dslp R pre b]  (angelic, liberal)

    The carrier, arrow operations, laws, and option/state stacks come from
    [Rel.v]. In particular, [optionRel] and [progRelArr] use the same
    relational operations for all four readings. At an unreachable output,
    [asp] is false and [dslp] is vacuously true.

    This file owns the arbitrary-input readings, their healthiness,
    recovery, inclusion, and operation facts. [aspOf] and [dslpOf] are
    transparent aliases of [asp] and [dslp]. Their recovery is constructive;
    [dspOf_rel] and [aslpOf_rel] use excluded middle. Unit-input monad
    interfaces and relational orders live in [RelMonads.v].

    [SPostArr.v] gives the property-only transformer presentation;
    [SPostArrEquiv.v] relates the ASP/DSLP arrows to [Rel], preserving their
    readings and arrow operations through the option and state transformers. *)

From Coq Require Import Classical_Prop.
From Incorrectness.Lib.Arrow Require Import Arrow.
From Incorrectness.Relational Require Export Rel.

(** ** Angelic strongest postcondition *)

Definition asp {A B} (R : Rel A B) (pre : A -> Prop) : B -> Prop :=
  fun b => exists a, pre a /\ R a b.

(** Evaluating singleton preconditions recovers the relation. The reverse
    round trip below applies to transformers in the image of [asp]. *)
Definition asp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : Rel A B :=
  fun a b => pt (fun a' => a = a') b.

Theorem asp_asp_inv : forall {A B} (R : Rel A B) a b,
    asp_inv (asp R) a b <-> R a b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? ?]]. subst. assumption.
  - intros. exists a. tauto.
Qed.

(** [asp] at the singleton precondition [eq a] recovers [R] at [a]. *)
Corollary asp_singleton : forall {A B} (R : Rel A B) (a : A) (b : B),
    asp R (eq a) b <-> R a b.
Proof.
  intros. unfold asp. split.
  - intros [a' [<- H]]. exact H.
  - intro H. exists a. auto.
Qed.

Theorem asp_inv_asp : forall {A B} (R : Rel A B) pre b,
    asp (asp_inv (asp R)) pre b <-> asp R pre b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? [? [? ?]]]]. subst.
    exists x0. tauto.
  - intros [? [? ?]].
    exists x. split; [assumption |].
    exists x. tauto.
Qed.

(** ** Demonic strongest liberal postcondition *)

Definition dslp {A B} (R : Rel A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

(** Intersecting all preconditions accepted at [b] recovers its
    predecessors. The reverse round trip applies to the image of [dslp]. *)
Definition dslp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : Rel A B :=
  fun a b => forall pre, pt pre b -> pre a.

Theorem dslp_dslp_inv : forall {A B} (R : Rel A B) a b,
    dslp_inv (dslp R) a b <-> R a b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros ?. apply H. auto.
  - intros. auto.
Qed.

Theorem dslp_inv_dslp : forall {A B} (R : Rel A B) pre b,
    dslp (dslp_inv (dslp R)) pre b <-> dslp R pre b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros. apply H; intros. auto.
  - intros. apply H0. apply H.
Qed.

(** ** Characterizations of DSP and ASLP

    Reference: Lena Verscht and Benjamin Lucien Kaminski,
    "A Taxonomy of Hoare-Like Logics: Towards a Holistic View using
    Predicate Transformers and Kleene Algebras with Top and Tests",
    POPL 2025, https://doi.org/10.1145/3704896.

    Their four SP readings use the same reachability relation:

    - [asp]: existential (angelic, total)
    - [dslp]: universal (demonic, liberal)
    - DSP: [asp /\ dslp] (demonic, total)
    - ASLP: [asp \/ dslp] (angelic, liberal)

    These characterizations match Verscht and Kaminski's Definitions 3.5
    and 3.6, which guard the quantifier by whether the inverse image is
    empty. Their §3.2.4 gives the conjunction/disjunction identities. *)

Section SPCharacterizations.

  Variables A B : Type.
  Variable R : Rel A B.

  Theorem dsp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, R a b) /\ forall a, R a b -> pre a) <->
    (asp R pre b /\ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [[a0 HRa0] Hall].
      split; [exists a0; auto | exact Hall].
    - intros [[a0 [Hpre HRa0]] Hall].
      split; [exists a0; exact HRa0 | exact Hall].
  Qed.

  Theorem aslp_asp_dslp (pre : A -> Prop) (b : B) :
    ((exists a, pre a /\ R a b) \/ ~ exists a, R a b) <->
    (asp R pre b \/ dslp R pre b).
  Proof.
    unfold asp, dslp. split.
    - intros [Hsp | Hunreach].
      + left. exact Hsp.
      + right. intros a HRab. exfalso. apply Hunreach. exists a. exact HRab.
    - intros [Hsp | Hdp].
      + left. exact Hsp.
      + destruct (classic (exists a, R a b)) as [[a0 HRa0] | Hunreach].
        * left. exists a0. split; [exact (Hdp a0 HRa0) | exact HRa0].
        * right. exact Hunreach.
  Qed.

End SPCharacterizations.

(* ================================================================= *)
(** ** The four arbitrary-input readings                             *)
(* ================================================================= *)

Section Readings.

  Context {X Y : Type}.

  (** Reuse the direct and universal images defined above. *)
  Definition aspOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    @asp X Y R.

  Definition dslpOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    @dslp X Y R.

  Definition dspOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    fun P y => aspOf R P y /\ dslpOf R P y.

  Definition aslpOf (R : SPureArr X Y) : (X -> Prop) -> Y -> Prop :=
    fun P y => aspOf R P y \/ dslpOf R P y.

  (** Equivalent relations have equivalent DSP/ASLP readings. *)
  Lemma dspOf_cong (R R' : SPureArr X Y) :
    Rel_eq R R' -> forall P y, dspOf R P y <-> dspOf R' P y.
  Proof.
    intros H P y. unfold dspOf, aspOf, dslpOf.
    split; intros [Ha Hd]; split.
    - destruct Ha as [x [HP Hx]]. exists x. split; [ exact HP | apply H; exact Hx ].
    - intros x Hx. apply Hd. apply H. exact Hx.
    - destruct Ha as [x [HP Hx]]. exists x. split; [ exact HP | apply H; exact Hx ].
    - intros x Hx. apply Hd. apply H. exact Hx.
  Qed.

  Lemma aslpOf_cong (R R' : SPureArr X Y) :
    Rel_eq R R' -> forall P y, aslpOf R P y <-> aslpOf R' P y.
  Proof.
    intros H P y. unfold aslpOf, aspOf, dslpOf.
    split; (intros [[x [HP Hx]] | Hd];
            [ left; exists x; split; [ exact HP | apply H; exact Hx ]
            | right; intros x Hx; apply Hd; apply H; exact Hx ]).
  Qed.

  (** *** Healthiness is automatic *)

  (** Every [aspOf] satisfies the singleton-join characterization. *)
  Theorem aspOf_join (R : SPureArr X Y) (P : X -> Prop) (y : Y) :
    aspOf R P y <-> exists x, P x /\ aspOf R (fun z => z = x) y.
  Proof.
    split.
    - intros [x [HP HR]]. exists x. split; [ exact HP |].
      exists x. split; [ reflexivity | exact HR ].
    - intros [x [HP [x' [Heq HR]]]]. subst x'. exists x. split; assumption.
  Qed.

  (** Every [dslpOf] satisfies the accepted-predicate meet characterization. *)
  Theorem dslpOf_meet (R : SPureArr X Y) (P : X -> Prop) (y : Y) :
    dslpOf R P y
    <-> forall x, (forall Q, dslpOf R Q y -> Q x) -> P x.
  Proof.
    split.
    - intros H x Hx. apply Hx. exact H.
    - intros H x HR. apply H. intros Q HQ. exact (HQ x HR).
  Qed.

  (** *** Faithfulness: the relation comes back *)

  (** ASP recovers it by probing at a singleton, DSLP by quantifying over
      accepted preconditions. Both are constructive; a complement probe
      gives a separate classical characterization of DSLP. *)

  Theorem aspOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    aspOf R (fun z => z = x) y <-> R x y.
  Proof.
    split.
    - intros [x' [Heq HR]]. subst x'. exact HR.
    - intro HR. exists x. split; [ reflexivity | exact HR ].
  Qed.

  Theorem dslpOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    (forall P, dslpOf R P y -> P x) <-> R x y.
  Proof.
    split.
    - intro H. exact (H (fun z => R z y) (fun z HR => HR)).
    - intros HR P HP. exact (HP x HR).
  Qed.

  Corollary aspOf_inj (R R' : SPureArr X Y) :
    (forall P y, aspOf R P y <-> aspOf R' P y) -> Rel_eq R R'.
  Proof.
    intros H x y. rewrite <- (aspOf_rel R), <- (aspOf_rel R'). apply H.
  Qed.

  Corollary dslpOf_inj (R R' : SPureArr X Y) :
    (forall P y, dslpOf R P y <-> dslpOf R' P y) -> Rel_eq R R'.
  Proof.
    intros H x y. rewrite <- (dslpOf_rel R), <- (dslpOf_rel R').
    split; intros HP Q HQ; apply HP; apply H; exact HQ.
  Qed.

  (** DSP and ASLP recover it too, but with excluded middle: each
      needs the value of the reading at two preconditions. *)

  Theorem dspOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    R x y <-> (dspOf R (fun _ => True) y /\ ~ dspOf R (fun z => z <> x) y).
  Proof.
    split.
    - intro HR. split.
      + split; [ exists x; split; [ exact I | exact HR ] | intros z _; exact I ].
      + intros [_ Hd]. exact (Hd x HR eq_refl).
    - intros [[[x0 [_ HR0]] _] Hno]. apply NNPP. intro Hnx.
      apply Hno. split.
      + exists x0. split; [| exact HR0 ].
        intro Heq. subst x0. exact (Hnx HR0).
      + intros z HR Heq. subst z. exact (Hnx HR).
  Qed.

  Theorem aslpOf_rel (R : SPureArr X Y) (x : X) (y : Y) :
    R x y <-> (~ aslpOf R (fun _ => False) y /\ aslpOf R (fun z => z = x) y).
  Proof.
    split.
    - intro HR. split.
      + intros [[z [Hf _]] | Hd]; [ exact Hf | exact (Hd x HR) ].
      + left. exists x. split; [ reflexivity | exact HR ].
    - intros [Hne [[z [Heq HR]] | Hd]].
      + subst z. exact HR.
      + apply NNPP. intro Hnx. apply Hne. right. intros z HR.
        rewrite (Hd z HR) in HR. exact (Hnx HR).
  Qed.

  (** *** The order correspondence *)

  (** Transformer inclusion is relation inclusion for ASP. *)
  Theorem aspOf_incl (R R' : SPureArr X Y) :
    (forall P y, aspOf R P y -> aspOf R' P y) <-> Rel_le R R'.
  Proof.
    split.
    - intros H x y HR. apply (aspOf_rel R' x y).
      apply H. apply aspOf_rel. exact HR.
    - intros H P y [x [HP HR]]. exists x. split; [ exact HP | exact (H x y HR) ].
  Qed.

  (** DSLP reverses relation inclusion. Note [R'] and [R] swap sides. *)
  Theorem dslpOf_incl (R R' : SPureArr X Y) :
    (forall P y, dslpOf R P y -> dslpOf R' P y) <-> Rel_le R' R.
  Proof.
    split.
    - intros H x y HR'. apply (proj1 (dslpOf_rel R x y)).
      intros P HP. exact (H P y HP x HR').
    - intros H P y HP x HR'. exact (HP x (H x y HR')).
  Qed.

End Readings.

Arguments aspOf {X Y}.
Arguments dslpOf {X Y}.
Arguments dspOf {X Y}.
Arguments aslpOf {X Y}.

(* ================================================================= *)
(** ** The readings preserve pure and composition                    *)
(* ================================================================= *)

(** These formulas derive the readings of [Rel]'s operations. Although
    [dslpOf] is antitone in the relation, it preserves the order of
    composition: the transposition happens twice. *)

Section Morphism.

  Context {X Y Z : Type}.

  Theorem aspOf_pure (h : X -> Y) (P : X -> Prop) (y : Y) :
    aspOf (arr_pure h) P y <-> exists x, P x /\ h x = y.
  Proof. reflexivity. Qed.

  Theorem dslpOf_pure (h : X -> Y) (P : X -> Prop) (y : Y) :
    dslpOf (arr_pure h) P y <-> forall x, h x = y -> P x.
  Proof. reflexivity. Qed.

  Theorem aspOf_comp (R : SPureArr X Y) (T : SPureArr Y Z)
    (P : X -> Prop) (z : Z) :
    aspOf (arr_comp R T) P z <-> aspOf T (aspOf R P) z.
  Proof.
    split.
    - intros [x [HP [y [HR HT]]]].
      exists y. split; [ exists x; split; assumption | exact HT ].
    - intros [y [[x [HP HR]] HT]].
      exists x. split; [ exact HP | exists y; split; assumption ].
  Qed.

  Theorem dslpOf_comp (R : SPureArr X Y) (T : SPureArr Y Z)
    (P : X -> Prop) (z : Z) :
    dslpOf (arr_comp R T) P z <-> dslpOf T (dslpOf R P) z.
  Proof.
    split.
    - intros H y HT x HR. apply H. exists y. split; assumption.
    - intros H x [y [HR HT]]. exact (H y HT x HR).
  Qed.

End Morphism.

(* ================================================================= *)
(** ** Structural operation readings                                *)
(* ================================================================= *)

(** These formulas preserve first and choice. DSP and ASLP arrows use
    them to split their readings, operate on each part, and recombine. *)

Section MorphismStruct.

  Context {X Y C : Type}.

  Theorem aspOf_first (R : SPureArr X Y) (P : X * C -> Prop) (q : Y * C) :
    aspOf (arr_first R) P q <-> aspOf R (fun x => P (x, snd q)) (fst q).
  Proof.
    destruct q as [b c']. cbn. split.
    - intros [[a c] [HP [HR Hc]]]. subst c. exists a. split; assumption.
    - intros [a [HP HR]]. exists (a, c').
      split; [ exact HP | split; [ exact HR | reflexivity ] ].
  Qed.

  Theorem dslpOf_first (R : SPureArr X Y) (P : X * C -> Prop) (q : Y * C) :
    dslpOf (arr_first R) P q <-> dslpOf R (fun x => P (x, snd q)) (fst q).
  Proof.
    destruct q as [b c']. cbn. split.
    - intros H a HR. exact (H (a, c') (conj HR eq_refl)).
    - intros H [a c] [HR Hc]. subst c. exact (H a HR).
  Qed.

  (** At [inl] the reading is the reading of [R]; at [inr] the value passes
      through, and both readings agree there. Their conjunction/disjunction
      therefore agrees with the same untouched branch of [arr_left R]. *)

  Theorem aspOf_left_inl (R : SPureArr X Y) (P : X + C -> Prop) (b : Y) :
    aspOf (arr_left R) P (inl b) <-> aspOf R (fun x => P (inl x)) b.
  Proof.
    cbn. split.
    - intros [[a|c] [HP HR]]; [ exists a; split; assumption | destruct HR ].
    - intros [a [HP HR]]. exists (inl a). split; assumption.
  Qed.

  Theorem aspOf_left_inr (R : SPureArr X Y) (P : X + C -> Prop) (c' : C) :
    aspOf (arr_left R) P (inr c') <-> P (inr c').
  Proof.
    cbn. split.
    - intros [[a|c] [HP HR]]; [ destruct HR | cbn in HR; subst c; exact HP ].
    - intro HP. exists (inr c'). split; [ exact HP | reflexivity ].
  Qed.

  Theorem dslpOf_left_inl (R : SPureArr X Y) (P : X + C -> Prop) (b : Y) :
    dslpOf (arr_left R) P (inl b) <-> dslpOf R (fun x => P (inl x)) b.
  Proof.
    cbn. split.
    - intros H a HR. exact (H (inl a) HR).
    - intros H [a|c] HR; [ exact (H a HR) | destruct HR ].
  Qed.

  Theorem dslpOf_left_inr (R : SPureArr X Y) (P : X + C -> Prop) (c' : C) :
    dslpOf (arr_left R) P (inr c') <-> P (inr c').
  Proof.
    cbn. split.
    - intro H. exact (H (inr c') eq_refl).
    - intros HP [a|c] HR; [ destruct HR | cbn in HR; subst c; exact HP ].
  Qed.

End MorphismStruct.
