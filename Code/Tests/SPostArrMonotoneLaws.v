(** * Arrow and application laws for monotone-only ASP and DSLP. *)

From Coq Require Import Morphisms RelationPairs.
From Incorrectness.Lib.Arrow Require Import Arrow.
From Incorrectness.SP Require Import SPostArr.
From Incorrectness.PTMonadTaxonomy Require Import TransformerRelations.

(** The two presentations have the same exhaustive classification:

    - Arrow fields that hold: [comp_id_l], [comp_id_r], [comp_assoc],
      [pure_comp], [first_pure], [first_comp], [first_assoc], [comp_proper],
      [first_proper], and [pure_proper].
    - Arrow fields that fail: [first_fst] and [first_natural].
    - Application fields that hold: [app_unit] and [app_ext].
    - Application fields that fail: [app_law], [app_precompose], and
      [app_postcompose].

    The carrier is the existing [MonoPT], not the production ASP/DSLP carrier:
    only monotonicity is required, without strictness, top preservation, or
    preservation of joins/meets. Pure lifts, composition, and [first] retain
    their production bodies; application retains the production singleton
    and recovered-relation bodies, not the healthiness-dependent equations
    [appASP_spec] and [appDSLP_spec].

    Each failed equation has explicit sides and acceptance/rejection proofs.
    Each surviving field has a generic proof. The conclusions concern exactly
    the plain operation dictionaries below, not every possible arrow structure
    on monotone transformers. No instances are registered here. *)
Module MonotoneLaws.
Local Obligation Tactic := idtac.

(** ** Operations and selected dictionaries. *)

(** Reuse the production pure lifts, retaining only their monotonicity proofs.
    Each following obligation checks closure in the monotone subset. *)
#[program] Definition pure_asp {A B} (h : A -> B) : MonoPT A B :=
  getASPArr (pureASP h).
Next Obligation.
  intros A B h.
  exact (proj1 (proj2_sig (pureASP h))).
Qed.

#[program] Definition pure_dslp {A B} (h : A -> B) : MonoPT A B :=
  getDSLPArr (pureDSLP h).
Next Obligation.
  intros A B h.
  exact (proj1 (proj2_sig (pureDSLP h))).
Qed.

(** Composition runs [f] first, then [g]. Transport predicate inclusion
    through [f], then through [g]; no stronger preservation law is needed. *)
#[program] Definition compose {A B C}
  (f : MonoPT A B) (g : MonoPT B C) : MonoPT A C :=
  fun P c => g (f P) c.
Next Obligation.
  intros A B C f g P Q HPQ c H.
  apply (getPT_mono g (f P) (f Q) c).
  - intros b Hfb.
    exact (getPT_mono f P Q b HPQ Hfb).
  - exact H.
Qed.

(** [first] freezes the second coordinate. Predicate inclusion restricts to
    that slice, so the monotonicity of [f] suffices. *)
#[program] Definition first {A B C}
  (f : MonoPT A B) : MonoPT (A * C) (B * C) :=
  fun P bc => f (fun a => P (a, snd bc)) (fst bc).
Next Obligation.
  intros A B C f P Q HPQ [b c] H.
  apply (getPT_mono f (fun a => P (a, c)) (fun a => Q (a, c)) b).
  - intro a.
    apply HPQ.
  - exact H.
Qed.

Definition asp_arrow : Arrow MonoPT := {|
  arr_pure := @pure_asp; arr_comp := @compose; arr_first := @first
|}.
Definition dslp_arrow : Arrow MonoPT := {|
  arr_pure := @pure_dslp; arr_comp := @compose; arr_first := @first
|}.
Definition equality : ArrowEq MonoPT := {|
  arrow_eq := @pt_eq;
  arrow_eq_equiv := fun A B => @pt_eq_Equivalence A B
|}.

(** Application retains the singleton probes of [appASP]. Predicate inclusion
    changes only the selected input pair, so monotonicity suffices for closure. *)
#[program] Definition app_asp {A B} : MonoPT (MonoPT A B * A) B :=
  fun P b => exists (f : MonoPT A B) a,
    P (f, a) /\ f (fun x => x = a) b.
Next Obligation.
  intros A B P Q HPQ b [f [a [HP Hf]]].
  exists f, a.
  exact (conj (HPQ (f, a) HP) Hf).
Qed.

(** Application retains the recovered relation used by [appDSLP]. The relation
    itself does not depend on the supplied pair predicate. *)
#[program] Definition app_dslp {A B} : MonoPT (MonoPT A B * A) B :=
  fun P b => forall (f : MonoPT A B) a,
    (forall Q, f Q b -> Q a) -> P (f, a).
Next Obligation.
  intros A B P Q HPQ b H f a Hr.
  exact (HPQ (f, a) (H f a Hr)).
Qed.

Definition asp_apply : @ArrowApply MonoPT asp_arrow :=
  {| arr_app := @app_asp |}.
Definition dslp_apply : @ArrowApply MonoPT dslp_arrow :=
  {| arr_app := @app_dslp |}.

Definition diagonal (p : bool * bool) : Prop := fst p = snd p.

(** ** Shared core proofs for the common composition and slicing bodies. *)
Lemma compose_assoc {A B C D}
  (f : MonoPT A B) (g : MonoPT B C) (h : MonoPT C D) :
  pt_eq (compose (compose f g) h) (compose f (compose g h)).
Proof. intros P d; reflexivity. Qed.

Lemma first_compose {A B C D} (f : MonoPT A B) (g : MonoPT B C) :
  pt_eq (@first A C D (compose f g)) (compose (first f) (first g)).
Proof. intros P [c d]; reflexivity. Qed.

Lemma compose_congr X Y Z :
  Proper (@pt_eq X Y ==> @pt_eq Y Z ==> @pt_eq X Z) (@compose X Y Z).
Proof.
  intros f f' Hf g g' Hg P z. cbn.
  transitivity (g (f' P) z).
  - apply getPT_ext; intro y; apply Hf.
  - apply Hg.
Qed.

Lemma first_congr X Y Z :
  Proper (@pt_eq X Y ==> @pt_eq (X * Z) (Y * Z)) (@first X Y Z).
Proof. intros f f' H P [y z]; apply H. Qed.

(** ** Direct application readings for pure pair builders. *)
(** These readings use the selected application bodies, not healthy normal
    forms or reflection of transformer equivalence into stored-arrow equality. *)
Lemma asp_dynamic {X A B} (u : X -> MonoPT A B * A) P b :
  compose (pure_asp u) app_asp P b <->
  exists x, P x /\ fst (u x) (fun y => y = snd (u x)) b.
Proof.
  change ((exists (f : MonoPT A B) a,
    (exists x, P x /\ u x = (f, a)) /\ f (fun y => y = a) b) <->
    exists x, P x /\ fst (u x) (fun y => y = snd (u x)) b).
  split.
  - intros [f [a [[x [HP E]] Hf]]].
    exists x; rewrite E; exact (conj HP Hf).
  - intros [x [HP Hf]].
    exists (fst (u x)), (snd (u x)); split.
    + exists x; split; [exact HP | destruct (u x); reflexivity].
    + exact Hf.
Qed.

Lemma dslp_dynamic {X A B} (u : X -> MonoPT A B * A) P b :
  compose (pure_dslp u) app_dslp P b <->
  forall x, (forall Q, fst (u x) Q b -> Q (snd (u x))) -> P x.
Proof.
  change ((forall (f : MonoPT A B) a,
    (forall Q, f Q b -> Q a) -> forall x, u x = (f, a) -> P x) <->
    forall x, (forall Q, fst (u x) Q b -> Q (snd (u x))) -> P x).
  split.
  - intros H x Hr; apply (H (fst (u x)) (snd (u x)) Hr x).
    destruct (u x); reflexivity.
  - intros H f a Hr x E; apply H; rewrite E; exact Hr.
Qed.

(** ** ASP: one shared choice versus two independent choices. *)
Module ASP.
Local Notation pure := (@arr_pure MonoPT asp_arrow _ _).
Local Notation comp := (@arr_comp MonoPT asp_arrow _ _ _).
Local Notation eqA := (@arrow_eq MonoPT equality _ _).

(** Both input Booleans must satisfy the supplied predicate. This witness
    preserves bottom and top; the counterexamples expose its failure to
    preserve joins. Only its monotonicity proof is stored in [MonoPT]. *)
#[program] Definition witness : MonoPT bool unit :=
  fun Q _ => Q true /\ Q false.
Next Obligation.
  intros P Q HPQ b [Ht Hf].
  split.
  - apply HPQ.
    exact Ht.
  - apply HPQ.
    exact Hf.
Qed.

(** *** Arrow law [comp_id_l]: holds. *)
Lemma comp_id_l_holds {A B} (f : MonoPT A B) :
  eqA (comp (@arr_id MonoPT asp_arrow A) f) f.
Proof.
  intros P b; cbn; apply getPT_ext; intro a; split.
  - intros [x [HP ->]]; exact HP.
  - intro HP; exists a; auto.
Qed.

(** *** Arrow law [comp_id_r]: holds. *)
Lemma comp_id_r_holds {A B} (f : MonoPT A B) :
  eqA (comp f (@arr_id MonoPT asp_arrow B)) f.
Proof.
  intros P b; cbn; split.
  - intros [x [HP ->]]; exact HP.
  - intro HP; exists b; auto.
Qed.

(** *** Arrow law [comp_assoc]: holds. *)
Lemma comp_assoc_holds {A B C D}
  (f : MonoPT A B) (g : MonoPT B C) (h : MonoPT C D) :
  eqA (comp (comp f g) h) (comp f (comp g h)).
Proof. exact (compose_assoc f g h). Qed.

(** *** Arrow law [pure_comp]: holds. *)
Lemma pure_comp_holds {A B C} (f : A -> B) (g : B -> C) :
  eqA (comp (pure f) (pure g)) (pure (fun a => g (f a))).
Proof.
  intros P c; cbn; split.
  - intros [b [[a [HP He]] H]]; subst b; exists a; auto.
  - intros [a [HP H]]; exists (f a); split.
    + exists a; auto.
    + exact H.
Qed.

(** *** Arrow law [first_pure]: holds. *)
Lemma first_pure_holds {A B C} (h : A -> B) :
  eqA (@arr_first MonoPT asp_arrow A B C (pure h))
    (pure (fun p : A * C => let '(a, c) := p in (h a, c))).
Proof.
  intros P [b c]; cbn; split.
  - intros [a [HP H]]; exists (a, c); cbn; split.
    + exact HP.
    + now rewrite H.
  - intros [[a c'] [HP H]]; cbn in H; inversion H; subst;
      exists a; auto.
Qed.

(** *** Arrow law [first_comp]: holds. *)
Lemma first_comp_holds {A B C D} (f : MonoPT A B) (g : MonoPT B C) :
  eqA (@arr_first MonoPT asp_arrow A C D (comp f g))
    (comp (@arr_first MonoPT asp_arrow A B D f)
      (@arr_first MonoPT asp_arrow B C D g)).
Proof. exact (first_compose f g). Qed.

(** *** Arrow law [first_fst]: fails. *)
(** Finite types A = bool, B = unit, C = bool; input [diagonal], output [tt].
    The left side requires one Boolean equal to both true and false; the
    right side chooses a separate diagonal pair for each conjunct. *)
(** These are the two sides of the actual [Arrow.first_fst] field, using
     explicit dictionaries to avoid any implicit choice of operations. *)
Definition first_then_fst : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_first MonoPT asp_arrow bool unit bool witness)
    (@arr_pure MonoPT asp_arrow _ _ (@fst unit bool)).
Definition fst_then_arrow : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_pure MonoPT asp_arrow _ _ (@fst bool bool)) witness.

Lemma first_then_fst_rejects : ~ first_then_fst diagonal tt.
Proof.
  (* One existential choice of [snd q] must equal both true and false.
     Inspect the goal after [change] before splitting on that choice. *)
  change (~ exists q : unit * bool,
    (true = snd q /\ false = snd q) /\ fst q = tt).
  intros [[[] c] [[Htrue Hfalse] _]].
  destruct c.
  - discriminate Hfalse.
  - discriminate Htrue.
Qed.

Lemma fst_then_arrow_accepts : fst_then_arrow diagonal tt.
Proof.
  (* The conjunction is now outside the existential choices. Each conjunct
     has its own diagonal pair, so the choices need not agree. *)
  change ((exists p : bool * bool, fst p = snd p /\ fst p = true) /\
          (exists p : bool * bool, fst p = snd p /\ fst p = false)).
  split.
  - exists (true, true).
    split.
    + reflexivity.
    + reflexivity.
  - exists (false, false).
    split.
    + reflexivity.
    + reflexivity.
Qed.

Theorem first_fst_fails :
  ~ @arrow_eq MonoPT equality _ _ first_then_fst fst_then_arrow.
Proof.
  intro H.
  (* Pointwise iff would transfer acceptance from right to left. *)
  apply first_then_fst_rejects.
  apply (proj2 (H diagonal tt)).
  exact fst_then_arrow_accepts.
Qed.

(** *** Arrow law [first_assoc]: holds. *)
Lemma first_assoc_holds {A B C D} (f : MonoPT A B) :
  eqA
    (comp (@arr_first MonoPT asp_arrow (A * C) (B * C) D
      (@arr_first MonoPT asp_arrow A B C f))
      (pure (@assoc_prod B C D)))
    (comp (pure (@assoc_prod A C D))
      (@arr_first MonoPT asp_arrow A B (C * D) f)).
Proof.
  intros P [b [c d]]; cbn; split.
  - intros [[[b' c'] d'] [Hf He]]; cbn in He; inversion He; subst.
    apply (getPT_mono f (fun a => P ((a, c), d)) _ b); [|exact Hf].
    intros a HP; exists ((a, c), d); auto.
  - intro Hf; exists ((b, c), d); cbn; split; [|reflexivity].
    apply (getPT_mono f
      (fun a => exists p, P p /\ assoc_prod p = (a, (c, d)))
      (fun a => P ((a, c), d)) b); [|exact Hf].
    intros a [[[a' c'] d'] [HP He]];
      cbn in He; inversion He; subst; exact HP.
Qed.

(** *** Arrow law [comp_proper]: holds. *)
Lemma comp_proper_holds X Y Z :
  Proper (@arrow_eq MonoPT equality X Y ==>
    @arrow_eq MonoPT equality Y Z ==> @arrow_eq MonoPT equality X Z)
    (@arr_comp MonoPT asp_arrow X Y Z).
Proof. exact (compose_congr X Y Z). Qed.

(** *** Arrow law [first_proper]: holds. *)
Lemma first_proper_holds X Y Z :
  Proper (@arrow_eq MonoPT equality X Y ==>
    @arrow_eq MonoPT equality (X * Z) (Y * Z))
    (@arr_first MonoPT asp_arrow X Y Z).
Proof. exact (first_congr X Y Z). Qed.

(** *** Arrow law [first_natural]: fails. *)
(** Finite types A = bool, B = unit, C = bool, D = unit; [g] is the constant
    [tt] map. Input [diagonal], output [(tt, tt)]. The left side reduces to
    [exists c : bool, true = c /\ false = c], which is false. The right side
    reduces to [(exists c : bool, true = c) /\ (exists c : bool, false = c)],
    which is true: the two conjuncts choose different diagonal pairs. *)
Definition first_then_collapse : MonoPT (bool * bool) (unit * unit) :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_first MonoPT asp_arrow bool unit bool witness)
    (@arr_pure MonoPT asp_arrow _ _
      (fun '(b, c) => (b, (fun _ : bool => tt) c))).

Definition collapse_then_first : MonoPT (bool * bool) (unit * unit) :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_pure MonoPT asp_arrow _ _
      (fun '(a, c) => (a, (fun _ : bool => tt) c)))
    (@arr_first MonoPT asp_arrow bool unit unit witness).

Lemma first_then_collapse_rejects :
  ~ first_then_collapse diagonal (tt, tt).
Proof.
  intros [[[] c] [[Ht Hf] _]];
    destruct c; [discriminate Hf | discriminate Ht].
Qed.

Lemma collapse_then_first_accepts : collapse_then_first diagonal (tt, tt).
Proof.
  split; [exists (true, true) | exists (false, false)]; split; reflexivity.
Qed.

Theorem first_natural_fails :
  ~ @arrow_eq MonoPT equality _ _ first_then_collapse collapse_then_first.
Proof.
  intro H; apply first_then_collapse_rejects.
  apply (proj2 (H diagonal (tt, tt))).
  exact collapse_then_first_accepts.
Qed.

(** *** Arrow law [pure_proper]: holds. *)
Lemma pure_proper_holds X Y :
  Proper (pointwise_relation X (@eq Y) ==> @arrow_eq MonoPT equality X Y)
    (@arr_pure MonoPT asp_arrow X Y).
Proof.
  intros f g H P y; cbn; split; intros [x [HP He]]; exists x; split.
  - exact HP.
  - rewrite <- H; exact He.
  - exact HP.
  - rewrite H; exact He.
Qed.

(** *** ArrowApply law [app_law]: fails. *)
(** Finite types A = bool, B = unit; input [fun _ => True], output [tt].
    The left side rejects because conjunction accepts no singleton. The
    right side is the original conjunction, which accepts the top predicate. *)
Definition static_application : MonoPT bool unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_pure MonoPT asp_arrow _ _ (fun a => (witness, a)))
    (@arr_app MonoPT asp_arrow asp_apply _ _).

Definition static_original : MonoPT bool unit := witness.

Lemma static_application_rejects : ~ static_application (fun _ => True) tt.
Proof.
  change (~ compose (pure_asp (fun a => (witness, a)))
    app_asp (fun _ => True) tt).
  rewrite asp_dynamic; intros [a [_ H]].
  change (true = a /\ false = a) in H.
  destruct H as [Ht Hf]; destruct a; discriminate.
Qed.

Lemma static_original_accepts : static_original (fun _ => True) tt.
Proof. split; exact I. Qed.

Theorem app_law_fails :
  ~ @arrow_eq MonoPT equality _ _ static_application static_original.
Proof.
  intro H; apply static_application_rejects.
  exact (proj2 (H (fun _ => True) tt) static_original_accepts).
Qed.

(** *** ArrowApply law [app_unit]: holds. *)
(** Pure pairing has exactly its graph, for arbitrary (also empty) types. *)
Lemma app_unit_holds (A B : Type) :
  @arrow_eq MonoPT equality _ _
    (@arr_comp MonoPT asp_arrow _ _ _
      (@arr_first MonoPT asp_arrow _ _ _
        (@arr_pure MonoPT asp_arrow _ _
          (fun x : A => pure_asp (fun y : B => (x, y)))))
      (@arr_app MonoPT asp_arrow asp_apply _ _))
    (@arr_id MonoPT asp_arrow (A * B)).
Proof.
  intros P [a b].
  change ((exists (f : MonoPT B (A * B)) y,
    (exists x : A, P (x, y) /\ pure_asp (fun z : B => (x, z)) = f) /\
    f (fun z => z = y) (a, b)) <->
    exists p : A * B, P p /\ p = (a, b)).
  split.
  - intros [f [y [[x [HP E]] Hf]]]; subst f.
    destruct Hf as [z [Ez Ep]]; subst z.
    exists (x, y); exact (conj HP Ep).
  - intros [p [HP E]]; subst p.
    exists (pure_asp (fun z : B => (a, z))), b; split.
    + exists a; split; [exact HP | reflexivity].
    + exists b; split; reflexivity.
Qed.

(** *** ArrowApply law [app_precompose]: fails. *)
(** Finite types A = bool, B = C = unit; [g] is [witness]. Input [pre_input]
    selects the stored unit identity; output [tt]. The left side is false:
    one singleton cannot satisfy both conjuncts. The right side is true:
    each conjunct chooses its own Boolean before the identity is applied.
    The selector uses ordinary stored-arrow equality; the law uses [pt_eq]. *)
Definition id_unit := @pure_asp unit unit (fun x => x).

Definition pre_input (p : MonoPT unit unit * bool) := fst p = id_unit.

Definition pre_left : MonoPT (MonoPT unit unit * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_first MonoPT asp_arrow _ _ _
      (@arr_pure MonoPT asp_arrow _ _
        (fun f : MonoPT unit unit => compose witness f)))
    (@arr_app MonoPT asp_arrow asp_apply _ _).

Definition pre_right : MonoPT (MonoPT unit unit * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_second MonoPT asp_arrow _ _ _ witness)
    (@arr_app MonoPT asp_arrow asp_apply _ _).

Lemma pre_left_rejects : ~ pre_left pre_input tt.
Proof.
  change (~ exists (k : MonoPT bool unit) a,
    (exists f : MonoPT unit unit, f = id_unit /\ compose witness f = k) /\
    k (fun x => x = a) tt).
  intros [k [a [[f [E K]] H]]]; subst f k.
  change (exists u : unit, (true = a /\ false = a) /\ u = tt) in H.
  destruct H as [[] [[Ht Hf] _]]; destruct a; discriminate.
Qed.

Lemma pre_right_accepts : pre_right pre_input tt.
Proof.
  exists id_unit, tt; split.
  - exists (tt, id_unit); split.
    + split; [exists (id_unit, true) | exists (id_unit, false)];
        split; reflexivity.
    + reflexivity.
  - exists tt; split; reflexivity.
Qed.

Theorem app_precompose_fails :
  ~ @arrow_eq MonoPT equality _ _ pre_left pre_right.
Proof.
  intro H; apply pre_left_rejects.
  exact (proj2 (H pre_input tt) pre_right_accepts).
Qed.

(** *** ArrowApply law [app_postcompose]: fails. *)
(** Finite types A = B = bool, C = unit; [h] is [witness]. Input [post_input]
    selects the stored Boolean identity; output [tt]. The left side is false:
    probing the composite with one singleton cannot satisfy conjunction.
    The right side is true: application chooses independent true/false
    arguments. The selector uses ordinary stored-arrow equality, not [pt_eq]. *)
Definition id_bool := @pure_asp bool bool (fun x => x).

Definition post_input (p : MonoPT bool bool * bool) := fst p = id_bool.

Definition post_left : MonoPT (MonoPT bool bool * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_first MonoPT asp_arrow _ _ _
      (@arr_pure MonoPT asp_arrow _ _
        (fun f : MonoPT bool bool => compose f witness)))
    (@arr_app MonoPT asp_arrow asp_apply _ _).

Definition post_right : MonoPT (MonoPT bool bool * bool) unit :=
  @arr_comp MonoPT asp_arrow _ _ _
    (@arr_app MonoPT asp_arrow asp_apply _ _) witness.

Lemma post_left_rejects : ~ post_left post_input tt.
Proof.
  change (~ exists (k : MonoPT bool unit) a,
    (exists f : MonoPT bool bool, f = id_bool /\ compose f witness = k) /\
    k (fun x => x = a) tt).
  intros [k [a [[f [E K]] H]]]; subst f k.
  change ((exists x : bool, x = a /\ x = true) /\
          (exists x : bool, x = a /\ x = false)) in H.
  destruct H as [[x [Ex Et]] [y [Ey Ef]]]; subst x y.
  destruct a; discriminate.
Qed.

Lemma post_right_accepts : post_right post_input tt.
Proof.
  split; [exists id_bool, true | exists id_bool, false]; split;
    [reflexivity | | reflexivity |].
  - exists true; split; reflexivity.
  - exists false; split; reflexivity.
Qed.

Theorem app_postcompose_fails :
  ~ @arrow_eq MonoPT equality _ _ post_left post_right.
Proof.
  intro H; apply post_left_rejects.
  exact (proj2 (H post_input tt) post_right_accepts).
Qed.

(** *** ArrowApply law [app_ext]: holds. *)
(** Transport singleton probes through [pt_eq]; do not equate stored arrows. *)
Lemma app_ext_holds {X A B} :
  Proper (pointwise_relation X
    (RelProd (@arrow_eq MonoPT equality A B) (@eq A)) ==>
    @arrow_eq MonoPT equality X B)
    (fun u : X -> MonoPT A B * A =>
      @arr_comp MonoPT asp_arrow _ _ _
        (@arr_pure MonoPT asp_arrow _ _ u)
        (@arr_app MonoPT asp_arrow asp_apply _ _)).
Proof.
  intros u v H P b.
  change (compose (pure_asp u) app_asp P b <->
    compose (pure_asp v) app_asp P b).
  rewrite !asp_dynamic; split.
  - intros [x [HP Hf]]; exists x; split; [exact HP |].
    destruct (H x) as [He Ha]; rewrite Ha in Hf.
    exact (proj1 (He _ b) Hf).
  - intros [x [HP Hf]]; exists x; split; [exact HP |].
    destruct (H x) as [He Ha]; rewrite Ha.
    exact (proj2 (He _ b) Hf).
Qed.

(** *** Package obstructions for the selected dictionaries. *)
Corollary no_arrow_laws : ~ @ArrowLaws MonoPT asp_arrow equality.
Proof.
  intro H.
  apply first_fst_fails.
  (* Extract the real field, specialized to our types and witness. *)
  exact (@first_fst MonoPT asp_arrow equality H bool unit bool witness).
Qed.

Corollary no_arrow_apply_laws :
  ~ @ArrowApplyLaws MonoPT asp_arrow asp_apply equality.
Proof.
  intro H; apply app_law_fails.
  exact (@app_law MonoPT asp_arrow asp_apply equality H bool unit witness).
Qed.
End ASP.

(** ** DSLP: a Boolean-dependent disjunct versus one fixed disjunct. *)
Module DSLP.
Local Notation pure := (@arr_pure MonoPT dslp_arrow _ _).
Local Notation comp := (@arr_comp MonoPT dslp_arrow _ _ _).
Local Notation eqA := (@arrow_eq MonoPT equality _ _).

(** At least one input Boolean must satisfy the supplied predicate. This
    witness preserves bottom and top; the counterexamples expose its failure
    to preserve meets. Only its monotonicity proof is stored in [MonoPT]. *)
#[program] Definition witness : MonoPT bool unit :=
  fun Q _ => Q true \/ Q false.
Next Obligation.
  intros P Q HPQ b [Ht | Hf].
  - left.
    apply HPQ.
    exact Ht.
  - right.
    apply HPQ.
    exact Hf.
Qed.

(** *** Arrow law [comp_id_l]: holds. *)
Lemma comp_id_l_holds {A B} (f : MonoPT A B) :
  eqA (comp (@arr_id MonoPT dslp_arrow A) f) f.
Proof.
  intros P b; cbn; apply getPT_ext; intro a; split.
  - intro H; apply H; reflexivity.
  - intros H x ->; exact H.
Qed.

(** *** Arrow law [comp_id_r]: holds. *)
Lemma comp_id_r_holds {A B} (f : MonoPT A B) :
  eqA (comp f (@arr_id MonoPT dslp_arrow B)) f.
Proof.
  intros P b; cbn; split.
  - intro H; apply H; reflexivity.
  - intros H x ->; exact H.
Qed.

(** *** Arrow law [comp_assoc]: holds. *)
Lemma comp_assoc_holds {A B C D}
  (f : MonoPT A B) (g : MonoPT B C) (h : MonoPT C D) :
  eqA (comp (comp f g) h) (comp f (comp g h)).
Proof. exact (compose_assoc f g h). Qed.

(** *** Arrow law [pure_comp]: holds. *)
Lemma pure_comp_holds {A B C} (f : A -> B) (g : B -> C) :
  eqA (comp (pure f) (pure g)) (pure (fun a => g (f a))).
Proof.
  intros P c; cbn; split.
  - intros H a Ha; apply (H (f a) Ha a eq_refl).
  - intros H b Hb a Ha; apply H; rewrite Ha; exact Hb.
Qed.

(** *** Arrow law [first_pure]: holds. *)
Lemma first_pure_holds {A B C} (h : A -> B) :
  eqA (@arr_first MonoPT dslp_arrow A B C (pure h))
    (pure (fun p : A * C => let '(a, c) := p in (h a, c))).
Proof.
  intros P [b c]; cbn; split.
  - intros H [a c'] He; cbn in He; inversion He; subst;
      apply H; reflexivity.
  - intros H a Ha; apply (H (a, c)); cbn; now rewrite Ha.
Qed.

(** *** Arrow law [first_comp]: holds. *)
Lemma first_comp_holds {A B C D} (f : MonoPT A B) (g : MonoPT B C) :
  eqA (@arr_first MonoPT dslp_arrow A C D (comp f g))
    (comp (@arr_first MonoPT dslp_arrow A B D f)
      (@arr_first MonoPT dslp_arrow B C D g)).
Proof. exact (first_compose f g). Qed.

(** *** Arrow law [first_fst]: fails. *)
(** Finite types A = bool, B = unit, C = bool; input [diagonal], output [tt].
    The left side chooses the matching disjunct separately for each Boolean;
    the right side requires one fixed disjunct over a fiber containing an
    off-diagonal pair. *)
Definition first_then_fst : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_first MonoPT dslp_arrow bool unit bool witness)
    (@arr_pure MonoPT dslp_arrow _ _ (@fst unit bool)).
Definition fst_then_arrow : MonoPT (bool * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_pure MonoPT dslp_arrow _ _ (@fst bool bool)) witness.

Lemma first_then_fst_accepts : first_then_fst diagonal tt.
Proof.
  (* The universal choice comes before the disjunction. Choose the matching
     disjunct separately for each Boolean [snd q]. *)
  change (forall q : unit * bool,
    fst q = tt -> true = snd q \/ false = snd q).
  intros [[] c] _.
  destruct c.
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

Lemma fst_then_arrow_rejects : ~ fst_then_arrow diagonal tt.
Proof.
  (* Now one disjunct must work for every pair in its projection fiber.
     Each fiber contains an off-diagonal pair, refuting that disjunct. *)
  change (~ ((forall p : bool * bool, fst p = true -> fst p = snd p) \/
             (forall p : bool * bool, fst p = false -> fst p = snd p))).
  intros [Htrue | Hfalse].
  - pose proof (Htrue (true, false) eq_refl) as H.
    discriminate H.
  - pose proof (Hfalse (false, true) eq_refl) as H.
    discriminate H.
Qed.

Theorem first_fst_fails :
  ~ @arrow_eq MonoPT equality _ _ first_then_fst fst_then_arrow.
Proof.
  intro H.
  (* Here the contradiction uses the other direction of pointwise iff. *)
  apply fst_then_arrow_rejects.
  apply (proj1 (H diagonal tt)).
  exact first_then_fst_accepts.
Qed.

(** *** Arrow law [first_assoc]: holds. *)
Lemma first_assoc_holds {A B C D} (f : MonoPT A B) :
  eqA
    (comp (@arr_first MonoPT dslp_arrow (A * C) (B * C) D
      (@arr_first MonoPT dslp_arrow A B C f))
      (pure (@assoc_prod B C D)))
    (comp (pure (@assoc_prod A C D))
      (@arr_first MonoPT dslp_arrow A B (C * D) f)).
Proof.
  intros P [b [c d]]; cbn; split.
  - intro H; specialize (H ((b, c), d) eq_refl); cbn in H.
    apply (getPT_mono f (fun a => P ((a, c), d)) _ b); [|exact H].
    intros a HP [[a' c'] d'] He;
      cbn in He; inversion He; subst; exact HP.
  - intros H [[b' c'] d'] He; cbn in He; inversion He; subst; cbn.
    apply (getPT_mono f
      (fun a => forall p, assoc_prod p = (a, (c, d)) -> P p)
      (fun a => P ((a, c), d)) b); [|exact H].
    intros a Ha; apply (Ha ((a, c), d) eq_refl).
Qed.

(** *** Arrow law [comp_proper]: holds. *)
Lemma comp_proper_holds X Y Z :
  Proper (@arrow_eq MonoPT equality X Y ==>
    @arrow_eq MonoPT equality Y Z ==> @arrow_eq MonoPT equality X Z)
    (@arr_comp MonoPT dslp_arrow X Y Z).
Proof. exact (compose_congr X Y Z). Qed.

(** *** Arrow law [first_proper]: holds. *)
Lemma first_proper_holds X Y Z :
  Proper (@arrow_eq MonoPT equality X Y ==>
    @arrow_eq MonoPT equality (X * Z) (Y * Z))
    (@arr_first MonoPT dslp_arrow X Y Z).
Proof. exact (first_congr X Y Z). Qed.

(** *** Arrow law [first_natural]: fails. *)
(** Finite types A = bool, B = unit, C = bool, D = unit; [g] is the constant
    [tt] map. Input [diagonal], output [(tt, tt)]. The left side reduces to
    [forall c : bool, true = c \/ false = c], which is true. The right side
    reduces to [(forall c : bool, true = c) \/ (forall c : bool, false = c)],
    which is false: each fixed disjunct has an off-diagonal counterexample. *)
Definition first_then_collapse : MonoPT (bool * bool) (unit * unit) :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_first MonoPT dslp_arrow bool unit bool witness)
    (@arr_pure MonoPT dslp_arrow _ _
      (fun '(b, c) => (b, (fun _ : bool => tt) c))).

Definition collapse_then_first : MonoPT (bool * bool) (unit * unit) :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_pure MonoPT dslp_arrow _ _
      (fun '(a, c) => (a, (fun _ : bool => tt) c)))
    (@arr_first MonoPT dslp_arrow bool unit unit witness).

Lemma first_then_collapse_accepts : first_then_collapse diagonal (tt, tt).
Proof.
  intros [[] c] _; destruct c; [left | right]; reflexivity.
Qed.

Lemma collapse_then_first_rejects : ~ collapse_then_first diagonal (tt, tt).
Proof.
  intros [Ht | Hf].
  - pose proof (Ht (true, false) eq_refl) as H; discriminate H.
  - pose proof (Hf (false, true) eq_refl) as H; discriminate H.
Qed.

Theorem first_natural_fails :
  ~ @arrow_eq MonoPT equality _ _ first_then_collapse collapse_then_first.
Proof.
  intro H; apply collapse_then_first_rejects.
  apply (proj1 (H diagonal (tt, tt))).
  exact first_then_collapse_accepts.
Qed.

(** *** Arrow law [pure_proper]: holds. *)
Lemma pure_proper_holds X Y :
  Proper (pointwise_relation X (@eq Y) ==> @arrow_eq MonoPT equality X Y)
    (@arr_pure MonoPT dslp_arrow X Y).
Proof.
  intros f g H P y; cbn; split; intros HP x He; apply HP;
    [rewrite H | rewrite <- H]; exact He.
Qed.

(** *** ArrowApply law [app_law]: fails. *)
(** Finite types A = bool, B = unit; input [fun _ => False], output [tt].
    The left side is true: disjunction has an empty recovered relation, so
    application accepts vacuously. The original disjunction on the right
    rejects the bottom predicate. *)
Definition static_application : MonoPT bool unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_pure MonoPT dslp_arrow _ _ (fun a => (witness, a)))
    (@arr_app MonoPT dslp_arrow dslp_apply _ _).

Definition static_original : MonoPT bool unit := witness.

Lemma static_application_accepts : static_application (fun _ => False) tt.
Proof.
  change (compose (pure_dslp (fun a => (witness, a)))
    app_dslp (fun _ => False) tt).
  rewrite dslp_dynamic; intros a Hr.
  assert (Hbad : a <> a).
  { apply (Hr (fun x : bool => x <> a)).
    change (true <> a \/ false <> a).
    destruct a; [right | left]; discriminate. }
  exact (Hbad eq_refl).
Qed.

Lemma static_original_rejects : ~ static_original (fun _ => False) tt.
Proof. intros [H | H]; exact H. Qed.

Theorem app_law_fails :
  ~ @arrow_eq MonoPT equality _ _ static_application static_original.
Proof.
  intro H; apply static_original_rejects.
  exact (proj1 (H (fun _ => False) tt) static_application_accepts).
Qed.

(** *** ArrowApply law [app_unit]: holds. *)
(** Keep the universal-image pure lift: its recovered relation is the
    pairing graph, even when either type is empty. *)
Lemma app_unit_holds (A B : Type) :
  @arrow_eq MonoPT equality _ _
    (@arr_comp MonoPT dslp_arrow _ _ _
      (@arr_first MonoPT dslp_arrow _ _ _
        (@arr_pure MonoPT dslp_arrow _ _
          (fun x : A => pure_dslp (fun y : B => (x, y)))))
      (@arr_app MonoPT dslp_arrow dslp_apply _ _))
    (@arr_id MonoPT dslp_arrow (A * B)).
Proof.
  intros P [a b].
  change ((forall (f : MonoPT B (A * B)) y,
    (forall Q, f Q (a, b) -> Q y) ->
    forall x : A, pure_dslp (fun z : B => (x, z)) = f -> P (x, y)) <->
    forall p : A * B, p = (a, b) -> P p).
  split.
  - intros H p E; subst p.
    apply (H (pure_dslp (fun z : B => (a, z))) b).
    + intros Q HQ; exact (HQ b eq_refl).
    + reflexivity.
  - intros H f y Hr x E; subst f.
    assert (Ep : (x, y) = (a, b)).
    { apply (Hr (fun z : B => (x, z) = (a, b))).
      intros z Hz; exact Hz. }
    exact (H (x, y) Ep).
Qed.

(** *** ArrowApply law [app_precompose]: fails. *)
(** Finite types A = bool, B = C = unit; [g] is [witness]. Input [pre_input]
    excludes the stored unit identity; output [tt]. The left side is true:
    composition gives that identity an empty recovered relation. The right
    side is false: applying the identity at tt forces an excluded input.
    The selector uses ordinary stored-arrow equality; the law uses [pt_eq]. *)
Definition id_unit := @pure_dslp unit unit (fun x => x).

Definition pre_input (p : MonoPT unit unit * bool) :=
  fst p = id_unit -> False.

Definition pre_left : MonoPT (MonoPT unit unit * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_first MonoPT dslp_arrow _ _ _
      (@arr_pure MonoPT dslp_arrow _ _
        (fun f : MonoPT unit unit => compose witness f)))
    (@arr_app MonoPT dslp_arrow dslp_apply _ _).

Definition pre_right : MonoPT (MonoPT unit unit * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_second MonoPT dslp_arrow _ _ _ witness)
    (@arr_app MonoPT dslp_arrow dslp_apply _ _).

Lemma pre_left_accepts : pre_left pre_input tt.
Proof.
  change (forall (k : MonoPT bool unit) a,
    (forall Q, k Q tt -> Q a) -> forall f : MonoPT unit unit,
    compose witness f = k -> (f = id_unit -> False)).
  intros k a Hr f Hk E; subst f k.
  assert (Hbad : a <> a).
  { apply (Hr (fun x : bool => x <> a)).
    change (forall u : unit, u = tt -> true <> a \/ false <> a).
    intros [] _; destruct a; [right | left]; discriminate. }
  exact (Hbad eq_refl).
Qed.

Lemma pre_right_rejects : ~ pre_right pre_input tt.
Proof.
  intro H.
  assert (Hr : forall Q : unit -> Prop, id_unit Q tt -> Q tt).
  { intros Q HQ; exact (HQ tt eq_refl). }
  destruct (H id_unit tt Hr (tt, id_unit) eq_refl) as [Ht | Hf].
  - exact (Ht (id_unit, true) eq_refl eq_refl).
  - exact (Hf (id_unit, false) eq_refl eq_refl).
Qed.

Theorem app_precompose_fails :
  ~ @arrow_eq MonoPT equality _ _ pre_left pre_right.
Proof.
  intro H; apply pre_right_rejects.
  exact (proj1 (H pre_input tt) pre_left_accepts).
Qed.

(** *** ArrowApply law [app_postcompose]: fails. *)
(** Finite types A = B = bool, C = unit; [h] is [witness]. Input [post_input]
    excludes the stored Boolean identity; output [tt]. The left side is true:
    the composite has an empty recovered relation. The right side is false:
    the identity's own graph forces rejection at both Boolean outputs before
    disjunction. The selector uses ordinary stored-arrow equality, not [pt_eq]. *)
Definition id_bool := @pure_dslp bool bool (fun x => x).

Definition post_input (p : MonoPT bool bool * bool) :=
  fst p = id_bool -> False.

Definition post_left : MonoPT (MonoPT bool bool * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_first MonoPT dslp_arrow _ _ _
      (@arr_pure MonoPT dslp_arrow _ _
        (fun f : MonoPT bool bool => compose f witness)))
    (@arr_app MonoPT dslp_arrow dslp_apply _ _).

Definition post_right : MonoPT (MonoPT bool bool * bool) unit :=
  @arr_comp MonoPT dslp_arrow _ _ _
    (@arr_app MonoPT dslp_arrow dslp_apply _ _) witness.

Lemma post_left_accepts : post_left post_input tt.
Proof.
  change (forall (k : MonoPT bool unit) a,
    (forall Q, k Q tt -> Q a) -> forall f : MonoPT bool bool,
    compose f witness = k -> (f = id_bool -> False)).
  intros k a Hr f Hk E; subst f k.
  assert (Hbad : a <> a).
  { apply (Hr (fun x : bool => x <> a)).
    change ((forall x : bool, x = true -> x <> a) \/
            (forall x : bool, x = false -> x <> a)).
    destruct a; [right | left]; intros x E; subst x; discriminate. }
  exact (Hbad eq_refl).
Qed.

Lemma post_right_rejects : ~ post_right post_input tt.
Proof.
  change (~ ((forall (f : MonoPT bool bool) a,
    (forall Q, f Q true -> Q a) -> f = id_bool -> False) \/
    (forall (f : MonoPT bool bool) a,
    (forall Q, f Q false -> Q a) -> f = id_bool -> False))).
  assert (Ht : forall Q : bool -> Prop, id_bool Q true -> Q true)
    by (intros Q H; exact (H true eq_refl)).
  assert (Hf : forall Q : bool -> Prop, id_bool Q false -> Q false)
    by (intros Q H; exact (H false eq_refl)).
  intros [H | H].
  - exact (H id_bool true Ht eq_refl).
  - exact (H id_bool false Hf eq_refl).
Qed.

Theorem app_postcompose_fails :
  ~ @arrow_eq MonoPT equality _ _ post_left post_right.
Proof.
  intro H; apply post_right_rejects.
  exact (proj1 (H post_input tt) post_left_accepts).
Qed.

(** *** ArrowApply law [app_ext]: holds. *)
(** Transport recovered-relation probes through [pt_eq], keeping the pure
    lift universal and avoiding equality reflection for stored arrows. *)
Lemma app_ext_holds {X A B} :
  Proper (pointwise_relation X
    (RelProd (@arrow_eq MonoPT equality A B) (@eq A)) ==>
    @arrow_eq MonoPT equality X B)
    (fun u : X -> MonoPT A B * A =>
      @arr_comp MonoPT dslp_arrow _ _ _
        (@arr_pure MonoPT dslp_arrow _ _ u)
        (@arr_app MonoPT dslp_arrow dslp_apply _ _)).
Proof.
  intros u v H P b.
  change (compose (pure_dslp u) app_dslp P b <->
    compose (pure_dslp v) app_dslp P b).
  rewrite !dslp_dynamic; split.
  - intros Hu x Hr; apply Hu; intros Q Hf.
    destruct (H x) as [He Ha]; rewrite Ha.
    apply Hr; exact (proj1 (He Q b) Hf).
  - intros Hv x Hr; apply Hv; intros Q Hf.
    destruct (H x) as [He Ha]; rewrite <- Ha.
    apply Hr; exact (proj2 (He Q b) Hf).
Qed.

(** *** Package obstructions for the selected dictionaries. *)
Corollary no_arrow_laws : ~ @ArrowLaws MonoPT dslp_arrow equality.
Proof.
  intro H.
  apply first_fst_fails.
  exact (@first_fst MonoPT dslp_arrow equality H bool unit bool witness).
Qed.

Corollary no_arrow_apply_laws :
  ~ @ArrowApplyLaws MonoPT dslp_arrow dslp_apply equality.
Proof.
  intro H; apply app_law_fails.
  exact (@app_law MonoPT dslp_arrow dslp_apply equality H bool unit witness).
Qed.
End DSLP.
End MonotoneLaws.
