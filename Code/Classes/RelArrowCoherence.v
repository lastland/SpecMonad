(** * Structural laws and application coherence for relationally presented arrows.

    The standard [Control.Arrow] equations (GHC 9.12.2), included in
    [ArrowApplyLaws], require application to respect pairing,
    precomposition, and postcomposition:

    [[
      first (pure (fun x => pure (fun y => (x, y)))) >>> app = id
      first (pure (fun f => g >>> f)) >>> app = second g >>> app
      first (pure (fun f => f >>> h)) >>> app = app >>> h
    ]]

    The core section below takes the relation reading [R] and its
    per-operation laws as explicit hypotheses; the structural and application
    equations additionally consume a faithful equality principle [rel_ext],
    which no relational statement uses.  [RelArrowPresentation] packages the
    same fields, and the closing wrappers keep its original theorem
    interfaces; both SP presentations reuse them in their base
    [ArrowApplyLaws] instances.

    The later sections describe relation semantics for option and
    state-over-option operations.  In particular,
    [rel_state_option_bind_fields] exposes the actual arrow-derived
    bind: it preserves the fixed input, threads the intermediate state,
    and propagates [None].  Concrete stacks instantiate it directly
    with their per-operation laws.  Application laws for these stacks
    come from the generic [OptionArrowT] and [StateArrowT] lifts, not
    from new concrete proofs here. *)

From Coq Require Import Classes.Morphisms_Prop.
From Incorrectness.Classes Require Import Arrow ArrowMonad OptionArrowT StateArrowT.

(** This ordinary record packages only the relation semantics needed by
    these proofs.  In particular, [present_app] evaluates the relation
    of the stored arrow itself, including when that arrow is a composite. *)
Record RelArrowPresentation (arr : Type -> Type -> Type)
  (HA : Arrow arr) (HC : @ArrowChoice arr HA) (HAA : @ArrowApply arr HA) := {
  present_rel : forall {A B}, arr A B -> A -> B -> Prop;
  present_ext : forall {A B} (f g : arr A B),
    (forall a b, present_rel f a b <-> present_rel g a b) -> f = g;
  present_pure : forall {A B} (f : A -> B) a b,
    present_rel (@arr_pure arr HA A B f) a b <-> f a = b;
  present_comp : forall {A B C} (f : arr A B) (g : arr B C) a c,
    present_rel (@arr_comp arr HA A B C f g) a c <->
    exists b, present_rel f a b /\ present_rel g b c;
  present_first : forall {A B C} (f : arr A B) a c b d,
    present_rel (@arr_first arr HA A B C f) (a, c) (b, d) <->
    present_rel f a b /\ c = d;
  present_left : forall {A B C} (f : arr A B) x y,
    present_rel (@arr_left arr HA HC A B C f) x y <->
    match x, y with
    | inl a, inl b => present_rel f a b
    | inr c, inr d => c = d
    | _, _ => False
    end;
  present_app : forall {A B} (f : arr A B) a b,
    present_rel (@arr_app arr HA HAA A B) (f, a) b <-> present_rel f a b
}.

Arguments present_rel {arr HA HC HAA} _ {A B} _ _ _.
Arguments present_ext {arr HA HC HAA} _ {A B} _ _ _.
Arguments present_pure {arr HA HC HAA} _ {A B} _ _ _.
Arguments present_comp {arr HA HC HAA} _ {A B C} _ _ _ _.
Arguments present_first {arr HA HC HAA} _ {A B C} _ _ _ _ _.
Arguments present_left {arr HA HC HAA} _ {A B C} _ _ _.
Arguments present_app {arr HA HC HAA} _ {A B} _ _ _.

Section RelationalCoherence.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HAA : @ArrowApply arr HA}.

  (** The relation reading of the base arrow and its per-operation
      laws, supplied as explicit hypotheses.  Concrete stacks pass the
      readings they already prove, without a bundled presentation, so
      relational results never inherit an equality principle. *)
  Variable R : forall {A B}, arr A B -> A -> B -> Prop.
  Variable rel_pure : forall {A B} (f : A -> B) a b,
    R (@arr_pure arr HA A B f) a b <-> f a = b.
  Variable rel_comp : forall {A B C} (f : arr A B) (g : arr B C) a c,
    R (@arr_comp arr HA A B C f g) a c <->
    exists b, R f a b /\ R g b c.
  Variable rel_first : forall {A B C} (f : arr A B) a c b d,
    R (@arr_first arr HA A B C f) (a, c) (b, d) <-> R f a b /\ c = d.
  Variable rel_left : forall {A B C} (f : arr A B) x y,
    R (@arr_left arr HA HC A B C f) x y <->
    match x, y with
    | inl a, inl b => R f a b
    | inr c, inr d => c = d
    | _, _ => False
    end.
  Variable rel_app : forall {A B} (f : arr A B) a b,
    R (@arr_app arr HA HAA A B) (f, a) b <-> R f a b.

  (** Faithful equality, consumed only by the arrow equalities
      below; section discharge keeps it out of every other statement. *)
  Variable rel_ext : forall {A B} (f g : arr A B),
    (forall a b, R f a b <-> R g a b) -> f = g.

  Local Notation pure := (@arr_pure arr HA).
  Local Notation comp := (@arr_comp arr HA).
  Local Notation first := (@arr_first arr HA).
  Local Notation second := (@arr_second arr HA).
  Local Notation app := (@arr_app arr HA HAA).

  Local Lemma rel_pure_comp {A B C} (f : A -> B) (g : arr B C) a c :
    R (comp (pure f) g) a c <-> R g (f a) c.
  Proof.
    rewrite rel_comp. split.
    - intros [b [Hb Hg]]. apply rel_pure in Hb. subst b. exact Hg.
    - intro Hg. exists (f a). split; [apply rel_pure; reflexivity | exact Hg].
  Qed.

  Local Lemma rel_comp_pure {A B C} (f : arr A B) (g : B -> C) a c :
    R (comp f (pure g)) a c <->
    exists b, R f a b /\ g b = c.
  Proof.
    rewrite rel_comp. split; intros [b [Hf Hg]]; exists b; split.
    - exact Hf.
    - apply rel_pure in Hg. exact Hg.
    - exact Hf.
    - apply rel_pure. exact Hg.
  Qed.

  Local Lemma rel_first_pure {A B C} (f : A -> B) (a : A) (c : C) q :
    R (first (pure f)) (a, c) q <-> (f a, c) = q.
  Proof.
    destruct q as [b d]. rewrite rel_first, rel_pure.
    split; [intros [-> ->]; reflexivity | intro H; injection H; auto].
  Qed.

  Local Lemma rel_second {A B C} (f : arr A B) (c : C) a d b :
    R (second f) (c, a) (d, b) <-> R f a b /\ c = d.
  Proof.
    unfold arr_second. rewrite rel_pure_comp. cbn [swap].
    rewrite rel_comp_pure. split.
    - intros [[b' d'] [Hf Heq]]. cbn [swap] in Heq.
      injection Heq as -> ->. apply rel_first in Hf. exact Hf.
    - intro Hf. exists (b, d). split; [apply rel_first; exact Hf | reflexivity].
  Qed.

  Local Lemma rel_first_pure_app {X A B} (k : X -> arr A B) x a b :
    R (comp (first (pure k)) app) (x, a) b <->
    R (k x) a b.
  Proof.
    rewrite rel_comp. split.
    - intros [fa [Hk Happ]]. apply rel_first_pure in Hk. subst fa.
      rewrite rel_app in Happ. exact Happ.
    - intro Hk. exists (k x, a). split.
      + apply rel_first_pure. reflexivity.
      + rewrite rel_app. exact Hk.
  Qed.

  Lemma rel_app_unit_fields (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y)))))
      app = @arr_id arr HA (A * B).
  Proof.
    apply rel_ext. intros [a b] q.
    rewrite rel_first_pure_app. unfold arr_id.
    rewrite ! rel_pure. reflexivity.
  Qed.

  Lemma rel_app_precompose_fields {A B C} (g : arr A B) :
    comp (first (pure (fun f : arr B C => comp g f)))
      app = comp (second g) app.
  Proof.
    apply rel_ext. intros [f a] c.
    rewrite rel_first_pure_app, ! rel_comp. split.
    - intros [b [Hg Hf]]. exists (f, b). split.
      + apply rel_second. auto.
      + rewrite rel_app. exact Hf.
    - intros [[f' b] [Hg Hf]]. apply rel_second in Hg.
      destruct Hg as [Hg <-]. exists b. split; [exact Hg |].
      rewrite rel_app in Hf. exact Hf.
  Qed.

  Lemma rel_app_postcompose_fields {A B C} (h : arr B C) :
    comp (first (pure (fun f : arr A B => comp f h)))
      app = comp app h.
  Proof.
    apply rel_ext. intros [f a] c.
    rewrite rel_first_pure_app, ! rel_comp.
    split; intros [b [Hf Hh]]; exists b; split.
    - rewrite rel_app. exact Hf.
    - exact Hh.
    - rewrite rel_app in Hf. exact Hf.
    - exact Hh.
  Qed.

  (** ** Structural law fields

      Each equation uses only its per-operation relational laws and
      faithfulness.  The core arrow equations require neither choice nor
      application; the choice equations require no application. *)

  Lemma rel_comp_id_l_fields {A B} (f : arr A B) :
    comp (@arr_id arr HA A) f = f.
  Proof.
    apply rel_ext. intros a b. unfold arr_id.
    rewrite rel_pure_comp. reflexivity.
  Qed.

  Lemma rel_comp_id_r_fields {A B} (f : arr A B) :
    comp f (@arr_id arr HA B) = f.
  Proof.
    apply rel_ext. intros a b. unfold arr_id.
    rewrite rel_comp_pure. split.
    - intros [b' [Hf ->]]. exact Hf.
    - intro Hf. exists b. auto.
  Qed.

  Lemma rel_comp_assoc_fields {A B C D}
      (f : arr A B) (g : arr B C) (h : arr C D) :
    comp (comp f g) h = comp f (comp g h).
  Proof.
    apply rel_ext. intros a d. rewrite !rel_comp. split.
    - intros [c [Hfg Hh]]. apply rel_comp in Hfg.
      destruct Hfg as [b [Hf Hg]]. exists b. split; [exact Hf |].
      apply rel_comp. exists c. auto.
    - intros [b [Hf Hgh]]. apply rel_comp in Hgh.
      destruct Hgh as [c [Hg Hh]]. exists c. split; [|exact Hh].
      apply rel_comp. exists b. auto.
  Qed.

  Lemma rel_pure_comp_fields {A B C} (f : A -> B) (g : B -> C) :
    comp (pure f) (pure g) = pure (fun a => g (f a)).
  Proof.
    apply rel_ext. intros a c. rewrite rel_pure_comp, !rel_pure. reflexivity.
  Qed.

  Lemma rel_first_pure_fields {A B C} (f : A -> B) :
    @arr_first arr HA A B C (pure f) =
    pure (fun '(a, c) => (f a, c)).
  Proof.
    apply rel_ext. intros [a c] q. rewrite rel_first_pure, rel_pure. reflexivity.
  Qed.

  Lemma rel_first_comp_fields {A B C D} (f : arr A B) (g : arr B C) :
    @arr_first arr HA A C D (comp f g) = comp (first f) (first g).
  Proof.
    apply rel_ext. intros [a d] [c d']. rewrite rel_first, !rel_comp. split.
    - intros [[b [Hf Hg]] <-]. exists (b, d). split;
        apply rel_first; auto.
    - intros [[b d0] [Hf Hg]]. apply rel_first in Hf, Hg.
      destruct Hf as [Hf <-], Hg as [Hg <-]. split; [|reflexivity].
      exists b. auto.
  Qed.

  Lemma rel_first_assoc_fields {A B C D} (f : arr A B) :
    comp (@arr_first arr HA _ _ D (@arr_first arr HA A B C f))
      (pure assoc_prod) =
    comp (pure assoc_prod) (@arr_first arr HA A B (C * D)%type f).
  Proof.
    apply rel_ext. intros [[a c] d] [b [c' d']].
    rewrite rel_comp_pure, rel_pure_comp. cbn [assoc_prod].
    rewrite rel_first. split.
    - intros [[[b0 c0] d0] [Hf Heq]].
      cbn [assoc_prod] in Heq. injection Heq as <- <- <-.
      apply rel_first in Hf. destruct Hf as [Hf Hd].
      apply rel_first in Hf. destruct Hf as [Hf Hc]. subst. auto.
    - intros [Hf Heq]. injection Heq as <- <-.
      exists ((b, c), d). split; [|reflexivity].
      apply rel_first. split; [apply rel_first; auto | reflexivity].
  Qed.

  Lemma rel_first_natural_fields {A B C D} (f : arr A B) (g : C -> D) :
    comp (first f) (pure (fun '(b, c) => (b, g c))) =
    comp (pure (fun '(a, c) => (a, g c))) (first f).
  Proof.
    apply rel_ext. intros [a c] [b d].
    rewrite rel_comp_pure, rel_pure_comp, rel_first. split.
    - intros [[b0 c0] [Hf Heq]]. apply rel_first in Hf.
      destruct Hf as [Hf <-]. injection Heq as <- <-. auto.
    - intros [Hf <-]. exists (b, c). split.
      + apply rel_first. auto.
      + reflexivity.
  Qed.

  Lemma rel_first_fst_fields {A B C} (f : arr A B) :
    comp (@arr_first arr HA A B C f) (pure fst) = comp (pure fst) f.
  Proof.
    apply rel_ext. intros [a c] b.
    rewrite rel_comp_pure, rel_pure_comp. cbn [fst]. split.
    - intros [[b0 c0] [Hf Heq]]. apply rel_first in Hf.
      cbn in Heq. subst b0. exact (proj1 Hf).
    - intro Hf. exists (b, c). split; [apply rel_first; auto | reflexivity].
  Qed.

  Lemma rel_left_pure_fields {A B C} (f : A -> B) :
    @arr_left arr HA HC A B C (pure f) =
    pure (fun x => sum_bimap f (fun c : C => c) x).
  Proof.
    apply rel_ext. intros x y.
    rewrite rel_left, rel_pure.
    destruct x as [a|c], y as [b|d]; cbn [sum_bimap].
    - rewrite rel_pure. split; intro H; [subst; reflexivity | injection H; auto].
    - split; intro H; [contradiction | discriminate].
    - split; intro H; [contradiction | discriminate].
    - split; intro H; [subst; reflexivity | injection H; auto].
  Qed.

  Lemma rel_left_comp_fields {A B C D} (f : arr A B) (g : arr B C) :
    @arr_left arr HA HC A C D (comp f g) =
    comp (@arr_left arr HA HC A B D f) (@arr_left arr HA HC B C D g).
  Proof.
    apply rel_ext. intros x y.
    rewrite !rel_comp, rel_left.
    destruct x as [a|d], y as [c|d']; cbn.
    - rewrite rel_comp. split.
      + intros [b [Hf Hg]]. exists (inl b). split; apply rel_left; auto.
      + intros [[b|d0] [Hf Hg]].
        * rewrite rel_left in Hf. rewrite rel_left in Hg. exists b. auto.
        * rewrite rel_left in Hf. contradiction.
    - split.
      + intros [].
      + intros [[b|d0] [Hf Hg]].
        * rewrite rel_left in Hg. contradiction.
        * rewrite rel_left in Hf. contradiction.
    - split.
      + intros [].
      + intros [[b|d0] [Hf Hg]].
        * rewrite rel_left in Hf. contradiction.
        * rewrite rel_left in Hg. contradiction.
    - split.
      + intros <-. exists (inr d). split; apply rel_left; auto.
      + intros [[b|d0] [Hf Hg]].
        * rewrite rel_left in Hf. contradiction.
        * rewrite rel_left in Hf. rewrite rel_left in Hg.
          exact (eq_trans Hf Hg).
  Qed.

  Lemma rel_left_inl_fields {A B C} (f : arr A B) :
    comp f (pure (@inl B C)) =
    comp (pure (@inl A C)) (@arr_left arr HA HC A B C f).
  Proof.
    apply rel_ext. intros a x.
    rewrite rel_comp_pure, rel_pure_comp, rel_left.
    destruct x as [b|d]; cbn; split; intro H.
    - destruct H as [b' [Hf Heq]]. injection Heq as Heq. subst b'. exact Hf.
    - exists b. split; [exact H | reflexivity].
    - destruct H as [b' [Hf Heq]]. discriminate Heq.
    - contradiction.
  Qed.

  Lemma rel_left_assoc_fields {A B C D} (f : arr A B) :
    comp (@arr_left arr HA HC _ _ D (@arr_left arr HA HC A B C f))
      (pure assoc_sum) =
    comp (pure assoc_sum) (@arr_left arr HA HC A B (C + D)%type f).
  Proof.
    apply rel_ext. intros x y.
    rewrite rel_comp_pure, rel_pure_comp.
    destruct x as [[a|c]|d], y as [b|[c'|d']];
      cbn [assoc_sum]; rewrite !rel_left;
      try solve [
        split; [
          intros [[[b0|c0]|d0] [Hf Heq]]; cbn [assoc_sum] in Heq;
          try discriminate;
          apply rel_left in Hf; try rewrite rel_left in Hf; contradiction
        | intro Heq; try discriminate Heq; contradiction
        ]
      ].
    - split.
      + intros [[[b0|c0]|d0] [Hf Heq]]; cbn [assoc_sum] in Heq;
          try discriminate.
        injection Heq as <-. apply rel_left in Hf.
        rewrite rel_left in Hf. exact Hf.
      + intro Hf. exists (inl (inl b)). split; [|reflexivity].
        apply rel_left. rewrite rel_left. exact Hf.
    - split.
      + intros [[[b0|c0]|d0] [Hf Heq]]; cbn [assoc_sum] in Heq;
          try discriminate.
        injection Heq as <-. apply rel_left in Hf.
        rewrite rel_left in Hf. subst c0. reflexivity.
      + intro Heq. injection Heq as <-. exists (inl (inr c)). split; [|reflexivity].
        apply rel_left. rewrite rel_left. reflexivity.
    - split.
      + intros [[[b0|c0]|d0] [Hf Heq]]; cbn [assoc_sum] in Heq;
          try discriminate.
        injection Heq as <-. apply rel_left in Hf. subst d0. reflexivity.
      + intro Heq. injection Heq as <-. exists (inr d). split; [|reflexivity].
        apply rel_left. reflexivity.
  Qed.

  Lemma rel_left_natural_fields {A B C D} (f : arr A B) (g : C -> D) :
    comp (@arr_left arr HA HC A B C f)
      (pure (fun x => sum_bimap (fun b : B => b) g x)) =
    comp (pure (fun x => sum_bimap (fun a : A => a) g x))
      (@arr_left arr HA HC A B D f).
  Proof.
    apply rel_ext. intros x y.
    rewrite rel_comp_pure, rel_pure_comp.
    destruct x as [a|c], y as [b|d]; cbn [sum_bimap]; rewrite !rel_left;
      try solve [
        split; [
          intros [[b0|c0] [Hf Heq]]; cbn [sum_bimap] in Heq; try discriminate;
          rewrite rel_left in Hf; contradiction
        | contradiction
        ]
      ].
    - split.
      + intros [[b0|c0] [Hf Heq]]; cbn [sum_bimap] in Heq; try discriminate.
        injection Heq as <-. rewrite rel_left in Hf. exact Hf.
      + intro Hf. exists (inl b). split; [rewrite rel_left; exact Hf | reflexivity].
    - split.
      + intros [[b0|c0] [Hf Heq]]; cbn [sum_bimap] in Heq; try discriminate.
        injection Heq as <-. rewrite rel_left in Hf. subst c0. reflexivity.
      + intros <-. exists (inr c). split; [rewrite rel_left; reflexivity | reflexivity].
  Qed.

  Lemma rel_left_inr_fields {A B C} (f : arr A B) :
    comp (pure (@inr A C)) (@arr_left arr HA HC A B C f) =
    pure (@inr B C).
  Proof.
    apply rel_ext; intros c y.
    rewrite rel_pure_comp, rel_left, rel_pure.
    destruct y as [b|d]; cbn; split; intro H.
    - contradiction.
    - discriminate H.
    - subst; reflexivity.
    - injection H; auto.
  Qed.

  Lemma rel_first_left_dist_fields {A B C D} (f : arr A B) :
    comp (@arr_first arr HA _ _ D (@arr_left arr HA HC A B C f))
      (pure sum_prod_dist) =
    comp (pure sum_prod_dist)
      (@arr_left arr HA HC _ _ (C * D)%type (first f)).
  Proof.
    apply rel_ext. intros [ac d] q.
    rewrite rel_comp_pure, rel_pure_comp.
    destruct ac as [a|c], q as [[b d']|[c' d']];
      cbn [sum_prod_dist]; rewrite rel_left;
      try solve [
        split; [
          intros [[[b0|c0] d0] [Hf Heq]]; cbn [sum_prod_dist] in Heq;
            try discriminate;
          apply rel_first in Hf; destruct Hf as [Hf _];
          rewrite rel_left in Hf; contradiction
        | contradiction
        ]
      ].
    - rewrite rel_first. split.
      + intros [[[b0|c0] d0] [Hf Heq]]; cbn [sum_prod_dist] in Heq;
          try discriminate.
        injection Heq as <- <-. apply rel_first in Hf.
        destruct Hf as [Hf Hd]. rewrite rel_left in Hf. auto.
      + intros [Hf <-]. exists (inl b, d). split; [|reflexivity].
        apply rel_first. split; [rewrite rel_left; exact Hf | reflexivity].
    - split.
      + intros [[[b0|c0] d0] [Hf Heq]]; cbn [sum_prod_dist] in Heq;
          try discriminate.
        injection Heq as <- <-. apply rel_first in Hf.
        destruct Hf as [Hf Hd]. rewrite rel_left in Hf. now subst.
      + intro Heq. injection Heq as <- <-. exists (inr c, d).
        split; [|reflexivity]. apply rel_first.
        split; [rewrite rel_left; reflexivity | reflexivity].
  Qed.

  (** ** Option operation semantics

      These facts evaluate the option transformer's operations on the
      base relation.  They support the state-over-option layer below;
      application coherence for the transformer itself is already the
      generic [OptionArrowT.ArrowApplyLaws] lift. *)

  Local Notation OA := (@Arrow_optionArrT arr HA HC).
  Local Notation opure := (@arr_pure (optionArrT arr) OA).
  Local Notation ocomp := (@arr_comp (optionArrT arr) OA).
  Local Notation ofirst := (@arr_first (optionArrT arr) OA).
  Local Notation oapp :=
    (@arr_app (optionArrT arr) OA (@ArrowApply_optionArrT arr HA HC HAA)).

  Local Lemma rel_option_pure {A B} (f : A -> B) a ob :
    R (opure f) a ob <-> Some (f a) = ob.
  Proof. exact (rel_pure (fun a => Some (f a)) a ob). Qed.

  Local Lemma rel_option_cont {B C} (g : optionArrT arr B C) ob oc :
    R (comp (pure to_sum)
      (comp (@arr_left arr HA HC _ _ unit g) (pure collapse))) ob oc <->
    match ob with Some b => R g b oc | None => None = oc end.
  Proof.
    rewrite rel_pure_comp, rel_comp_pure.
    destruct ob as [b|]; cbn [to_sum]; split.
    - intros [[oc'|[]] [Hg Heq]]; rewrite rel_left in Hg.
      + cbn [collapse] in Heq. subst oc'. exact Hg.
      + contradiction.
    - intro Hg. exists (inl oc). split; [rewrite rel_left; exact Hg | reflexivity].
    - intros [[oc'|[]] [Hg Heq]]; rewrite rel_left in Hg.
      + contradiction.
      + exact Heq.
    - intro Heq. exists (inr tt). split; [rewrite rel_left; reflexivity | exact Heq].
  Qed.

  Local Lemma rel_option_comp {A B C}
      (f : optionArrT arr A B) (g : optionArrT arr B C) a oc :
    R (ocomp f g) a oc <-> exists ob, R f a ob /\
      match ob with Some b => R g b oc | None => None = oc end.
  Proof.
    change (R (comp f (comp (pure to_sum)
      (comp (@arr_left arr HA HC _ _ unit g) (pure collapse)))) a oc <->
      exists ob, R f a ob /\
        match ob with Some b => R g b oc | None => None = oc end).
    rewrite rel_comp. setoid_rewrite rel_option_cont. reflexivity.
  Qed.

  Local Lemma rel_option_pure_comp {A B C}
      (f : A -> B) (g : optionArrT arr B C) a oc :
    R (ocomp (opure f) g) a oc <-> R g (f a) oc.
  Proof.
    rewrite rel_option_comp. split.
    - intros [ob [Hf Hg]]. apply rel_option_pure in Hf. subst ob. exact Hg.
    - intro Hg. exists (Some (f a)). split; [apply rel_option_pure; reflexivity | exact Hg].
  Qed.

  Local Lemma rel_option_comp_pure {A B C}
      (f : optionArrT arr A B) (g : B -> C) a oc :
    R (ocomp f (opure g)) a oc <->
    exists ob, R f a ob /\ option_map g ob = oc.
  Proof.
    rewrite rel_option_comp. split; intros [ob [Hf Hg]]; exists ob; split.
    - exact Hf.
    - destruct ob; [apply rel_option_pure in Hg |]; exact Hg.
    - exact Hf.
    - destruct ob; [apply rel_option_pure |]; exact Hg.
  Qed.

  Local Lemma rel_option_first {A B C} (f : optionArrT arr A B) a (c : C) q :
    R (ofirst f) (a, c) q <->
    exists ob, R f a ob /\ option_map (fun b => (b, c)) ob = q.
  Proof.
    change (R (comp (first f) (pure sequence_option)) (a, c) q <->
      exists ob, R f a ob /\ option_map (fun b => (b, c)) ob = q).
    rewrite rel_comp_pure. split.
    - intros [[ob d] [Hf Heq]]. apply rel_first in Hf.
      destruct Hf as [Hf <-]. exists ob. split; [exact Hf |].
      destruct ob; exact Heq.
    - intros [ob [Hf Heq]]. exists (ob, c). split.
      + apply rel_first. auto.
      + destruct ob; exact Heq.
  Qed.

  Local Lemma rel_option_app {A B} (f : optionArrT arr A B) a ob :
    R oapp (f, a) ob <-> R f a ob.
  Proof. exact (rel_app f a ob). Qed.

  (** ** State-over-option semantics

      Successful composition threads the intermediate state.  A [None]
      result propagates without inventing an output state. *)

  Section StateOptionCoherence.
    Variable S : Type.

    Local Notation SOA := (@Arrow_stateArrT S (optionArrT arr) OA).
    Local Notation sopure := (@arr_pure (stateArrT S (optionArrT arr)) SOA).
    Local Notation socomp := (@arr_comp (stateArrT S (optionArrT arr)) SOA).
    Local Notation sofirst := (@arr_first (stateArrT S (optionArrT arr)) SOA).
    Local Notation sosecond := (@arr_second (stateArrT S (optionArrT arr)) SOA).
    Local Notation soapp :=
      (@arr_app (stateArrT S (optionArrT arr)) SOA
        (@ArrowApply_stateArrT S (optionArrT arr) OA
          (@ArrowApply_optionArrT arr HA HC HAA))).

    (** [rel_state_option_pure_fields] and
        [rel_state_option_bind_fields] below are the public seams of
        this layer: concrete SP stacks instantiate them with their
        per-operation relational laws to read off [ret] and [bind]. *)

    Lemma rel_state_option_pure_fields {A B} (f : A -> B) a s q :
      R (sopure f) (a, s) q <-> Some (f a, s) = q.
    Proof. exact (rel_option_pure (fun '(a, s) => (f a, s)) (a, s) q). Qed.

    Local Lemma rel_state_option_comp {A B C}
      (f : stateArrT S (optionArrT arr) A B)
      (g : stateArrT S (optionArrT arr) B C) p q :
      R (socomp f g) p q <-> exists obs, R f p obs /\
        match obs with Some bs => R g bs q | None => None = q end.
    Proof. exact (rel_option_comp f g p q). Qed.

    Local Lemma rel_state_option_first {A B C}
      (f : stateArrT S (optionArrT arr) A B) a (c : C) s q :
      R (sofirst f) ((a, c), s) q <-> exists obs, R f (a, s) obs /\
        option_map (fun '(b, t) => ((b, c), t)) obs = q.
    Proof.
      change (R (ocomp (opure (@state_shuffle_in S A C))
        (ocomp (ofirst f) (opure (@state_shuffle_out S B C))))
        ((a, c), s) q <-> exists obs, R f (a, s) obs /\
          option_map (fun '(b, t) => ((b, c), t)) obs = q).
      rewrite rel_option_pure_comp, rel_option_comp_pure.
      cbn [state_shuffle_in]. split.
      - intros [qbsc [Hf Heq]]. apply rel_option_first in Hf.
        destruct Hf as [obs [Hf <-]]. exists obs. split; [exact Hf |].
        destruct obs as [[b t]|]; exact Heq.
      - intros [obs [Hf Heq]]. exists (option_map (fun bs => (bs, c)) obs). split.
        + apply rel_option_first. exists obs. auto.
        + destruct obs as [[b t]|]; exact Heq.
    Qed.

    Local Lemma rel_state_option_second {A B C}
      (f : stateArrT S (optionArrT arr) A B) (c : C) a s q :
      R (sosecond f) ((c, a), s) q <-> exists obs, R f (a, s) obs /\
        option_map (fun '(b, t) => ((c, b), t)) obs = q.
    Proof.
      change (R (ocomp (opure (fun '(p, s) => (swap p, s)))
        (ocomp (sofirst f) (opure (fun '(p, s) => (swap p, s)))))
        ((c, a), s) q <-> exists obs, R f (a, s) obs /\
          option_map (fun '(b, t) => ((c, b), t)) obs = q).
      rewrite rel_option_pure_comp, rel_option_comp_pure. cbn [swap]. split.
      - intros [qbc [Hf Heq]]. apply rel_state_option_first in Hf.
        destruct Hf as [obs [Hf <-]]. exists obs. split; [exact Hf |].
        destruct obs as [[b t]|]; exact Heq.
      - intros [obs [Hf Heq]].
        exists (option_map (fun '(b, t) => ((b, c), t)) obs). split.
        + apply rel_state_option_first. exists obs. auto.
        + destruct obs as [[b t]|]; exact Heq.
    Qed.

    Local Lemma rel_state_option_app {A B}
      (f : stateArrT S (optionArrT arr) A B) a s q :
      R soapp ((f, a), s) q <-> R f (a, s) q.
    Proof.
      change (R (ocomp (opure (fun '((f, a), s) => (f, (a, s)))) oapp)
        ((f, a), s) q <-> R f (a, s) q).
      rewrite rel_option_pure_comp. apply rel_option_app.
    Qed.

    Local Lemma rel_state_option_fanout_id {I A}
        (m : stateArrT S (optionArrT arr) I A) (i : I) (s : S) ox :
      R (@arr_fanout (stateArrT S (optionArrT arr)) SOA I A I m
           (@arr_id (stateArrT S (optionArrT arr)) SOA I)) (i, s) ox <->
      exists om, R m (i, s) om /\
        option_map (fun '(a, t) => ((a, i), t)) om = ox.
    Proof.
      unfold arr_fanout, arr_split.
      split.
      - intro Hf.
        rewrite rel_state_option_comp in Hf. destruct Hf as [od [Hop Hmid]].
        rewrite rel_state_option_pure_fields in Hop.
        destruct od as [[[i1 i2] s1]|]; [|discriminate Hop].
        injection Hop. intros; subst.
        rewrite rel_state_option_comp in Hmid. destruct Hmid as [oim [Hfirst Hsecond]].
        rewrite rel_state_option_first in Hfirst. destruct Hfirst as [om [Hm Hoim]].
        destruct om as [[a t]|].
        + exists (Some (a, t)). split; [exact Hm|].
          cbn [option_map] in Hoim. subst oim.
          cbn [option_map] in Hsecond |- *.
          rewrite rel_state_option_second in Hsecond.
          destruct Hsecond as [oidx [Hidx Hox2]].
          unfold arr_id in Hidx. rewrite rel_state_option_pure_fields in Hidx.
          cbn [option_map] in Hox2. cbn in Hidx. subst oidx. exact Hox2.
        + exists None. split; [exact Hm|].
          cbn [option_map] in Hoim. subst oim.
          cbn [option_map] in Hsecond |- *. exact Hsecond.
      - intros [om [Hm Hox]].
        rewrite rel_state_option_comp. exists (Some ((i, i), s)). split.
        + rewrite rel_state_option_pure_fields. reflexivity.
        + cbn [option_map].
          rewrite rel_state_option_comp.
          exists (option_map (fun '(a, t) => ((a, i), t)) om). split.
          * rewrite rel_state_option_first. exists om.
            split; [exact Hm | reflexivity].
          * destruct om as [[a t]|]; cbn [option_map].
            -- rewrite rel_state_option_second. exists (Some (i, t)). split.
               ++ unfold arr_id. rewrite rel_state_option_pure_fields. reflexivity.
               ++ exact Hox.
            -- exact Hox.
    Qed.

    Local Lemma rel_state_option_kapp {I A B}
        (k : A -> stateArrT S (optionArrT arr) I B) (a : A) (i : I) (t : S) r :
      R (socomp (sopure (fun '(a, i) => (k a, i))) soapp) ((a, i), t) r <->
      R (k a) (i, t) r.
    Proof.
      rewrite rel_state_option_comp. split.
      - intros [o [Hk Happ]].
        rewrite rel_state_option_pure_fields in Hk. subst o.
        exact (proj1 (rel_state_option_app (k a) i t r) Happ).
      - intro Hk. exists (Some ((k a, i), t)). split.
        + rewrite rel_state_option_pure_fields. reflexivity.
        + exact (proj2 (rel_state_option_app (k a) i t r) Hk).
    Qed.

    Theorem rel_state_option_bind_fields {I A B : Type}
        (m : stateArrT S (optionArrT arr) I A)
        (k : A -> stateArrT S (optionArrT arr) I B) (i : I) (s : S) r :
      R (@bind_arrow (stateArrT S (optionArrT arr)) SOA
           (@ArrowApply_stateArrT S (optionArrT arr) OA
              (@ArrowApply_optionArrT arr HA HC HAA)) I A B m k) (i, s) r <->
      exists om, R m (i, s) om /\
        match om with
        | Some (a, t) => R (k a) (i, t) r
        | None => r = None
        end.
    Proof.
      unfold bind_arrow. rewrite rel_state_option_comp. split.
      - intros [ofa [Hfan Hk]].
        rewrite rel_state_option_fanout_id in Hfan.
        destruct Hfan as [om [Hm Hofa]].
        destruct om as [[a t]|].
        + exists (Some (a, t)). split; [exact Hm|].
          subst ofa. cbn [option_map] in Hk.
          exact (proj1 (rel_state_option_kapp k a i t r) Hk).
        + exists None. split; [exact Hm|].
          subst ofa. cbn [option_map] in Hk.
          symmetry. exact Hk.
      - intros [om [Hm Hk]].
        exists (option_map (fun '(a, t) => ((a, i), t)) om). split.
        + rewrite rel_state_option_fanout_id.
          exists om. split; [exact Hm | reflexivity].
        + destruct om as [[a t]|].
          * cbn [option_map].
            exact (proj2 (rel_state_option_kapp k a i t r) Hk).
          * cbn [option_map]. symmetry. exact Hk.
    Qed.

  End StateOptionCoherence.

End RelationalCoherence.

(** ** Presentation wrappers

    These lemmas keep the original interfaces that consume a whole
    [RelArrowPresentation] record.  The [Let] adapters below expose all
    arguments of the record projections, and each wrapper delegates to the
    explicit-field core, so no proof body is duplicated. *)

Section PresentationCoherence.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HC : @ArrowChoice arr HA} {HAA : @ArrowApply arr HA}.
  Variable P : RelArrowPresentation arr HA HC HAA.

  Local Notation R := (present_rel P).
  Local Notation pure := (@arr_pure arr HA).
  Local Notation comp := (@arr_comp arr HA).
  Local Notation first := (@arr_first arr HA).
  Local Notation second := (@arr_second arr HA).
  Local Notation app := (@arr_app arr HA HAA).

  Let Rof := @present_rel arr HA HC HAA P.
  Let pure_law := @present_pure arr HA HC HAA P.
  Let comp_law := @present_comp arr HA HC HAA P.
  Let first_law := @present_first arr HA HC HAA P.
  Let left_law := @present_left arr HA HC HAA P.
  Let app_law := @present_app arr HA HC HAA P.
  Let ext_law := @present_ext arr HA HC HAA P.

  Lemma rel_app_unit (A B : Type) :
    comp (first (pure (fun x : A => pure (fun y : B => (x, y))))) app
      = @arr_id arr HA (A * B).
  Proof.
    exact (rel_app_unit_fields Rof pure_law comp_law first_law app_law ext_law A B).
  Qed.

  Lemma rel_app_precompose {A B C} (g : arr A B) :
    comp (first (pure (fun f : arr B C => comp g f))) app
      = comp (second g) app.
  Proof.
    exact (rel_app_precompose_fields Rof pure_law comp_law first_law app_law
      ext_law g).
  Qed.

  Lemma rel_app_postcompose {A B C} (h : arr B C) :
    comp (first (pure (fun f : arr A B => comp f h))) app
      = comp app h.
  Proof.
    exact (rel_app_postcompose_fields Rof pure_law comp_law first_law app_law
      ext_law h).
  Qed.

  Section StateOptionPresentation.
    Variable S : Type.

    Local Notation OA := (@Arrow_optionArrT arr HA HC).
    Local Notation SOA := (@Arrow_stateArrT S (optionArrT arr) OA).

    Lemma rel_state_option_pure {A B} (f : A -> B) a s q :
      R (@arr_pure (stateArrT S (optionArrT arr)) SOA A B f) (a, s) q <->
      Some (f a, s) = q.
    Proof.
      exact (rel_state_option_pure_fields Rof pure_law S f a s q).
    Qed.

    Lemma rel_state_option_bind {I A B : Type}
        (m : stateArrT S (optionArrT arr) I A)
        (k : A -> stateArrT S (optionArrT arr) I B) (i : I) (s : S) r :
      R (@bind_arrow (stateArrT S (optionArrT arr)) SOA
           (@ArrowApply_stateArrT S (optionArrT arr) OA
              (@ArrowApply_optionArrT arr HA HC HAA)) I A B m k) (i, s) r <->
        exists om, R m (i, s) om /\
          match om with
          | Some (a, t) => R (k a) (i, t) r
          | None => r = None
          end.
    Proof.
      exact (rel_state_option_bind_fields Rof pure_law comp_law first_law
        left_law app_law S m k i s r).
    Qed.

  End StateOptionPresentation.

End PresentationCoherence.
