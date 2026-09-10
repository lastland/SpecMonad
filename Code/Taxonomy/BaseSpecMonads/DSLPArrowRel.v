(** * The relation a [DSLPArr] denotes

    [dslpRel f a b]: every precondition [f] accepts for [b] contains [a].
    By [dslp_meet] this determines [f], so an arrow and the relation it
    denotes are interchangeable.  Note the direction: transformer
    inclusion is the CONVERSE of relational inclusion ([dslpRel_incl]),
    where [ASPArrowRel]'s [aspRel_incl] is covariant.

    Split out of [DSLPMonad.v] so that the arrow (in [DSLPArrowCore.v])
    and the specification monads (in [DSLPMonad.v]) are separable from the
    relational reasoning that connects them. *)

From Coq Require Import Morphisms RelationClasses Setoid Relation_Definitions.
From Coq Require Import Classical_Prop.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Classes Require Import ArrowMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSLPArrowCore.

(* ================================================================= *)
(** ** The relation an arrow denotes                                 *)
(* ================================================================= *)

(** [dslpRel f a b]: every precondition [f] accepts for [b] contains [a].
    By [dslp_meet] this determines [f]. *)

Section Relation.

  Definition dslpRel {A B} (f : DSLPArr A B) (a : A) (b : B) : Prop :=
    dslpRelT (getDSLPArr f) a b.

  Lemma get_dslpRel {A B} (f : DSLPArr A B) P b :
    f P b <-> forall a, dslpRel f a b -> P a.
  Proof. exact (getDSLPArr_meet f P b). Qed.

  (** The probe that computes it: [f] at the complement of [a]. *)
  Lemma dslpRel_probe {A B} (f : DSLPArr A B) a b :
    dslpRel f a b <-> ~ f (fun x => x <> a) b.
  Proof.
    split.
    - intros Hr Hf. exact (Hr (fun x => x <> a) Hf eq_refl).
    - intros Hf P HP.
      (* if [a] were missing from the relation, the complement would be accepted *)
      destruct (classic (dslpRel f a b)) as [Hin | Hout].
      + exact (proj1 (get_dslpRel f P b) HP a Hin).
      + exfalso. apply Hf.
        apply (proj2 (get_dslpRel f (fun x => x <> a) b)).
        intros a' Hr' Heq. subst a'. exact (Hout Hr').
  Qed.

  (** The arrow of a relation denotes that relation. *)
  Lemma dslpRel_ofRel {A B} (R : A -> B -> Prop) a b :
    dslpRel (ofRelDSLPArr R) a b <-> R a b.
  Proof.
    unfold dslpRel, dslpRelT, ofRelDSLPArr. cbn. split.
    - intro H. exact (H (fun x => R x b) (fun a' Hr => Hr)).
    - intros HR Q HQ. exact (HQ a HR).
  Qed.

  Lemma ofRel_dslpRel {A B} (f : DSLPArr A B) P b :
    ofRelDSLPArr (dslpRel f) P b <-> f P b.
  Proof.
    unfold dslpRel, dslpRelT, ofRelDSLPArr. cbn. split; apply getDSLPArr_meet.
  Qed.


  Lemma dslpRel_pure {A B} (h : A -> B) a b : dslpRel (arr_pure h) a b <-> h a = b.
  Proof.
    cbn. unfold dslpRel, dslpRelT. cbn. split.
    - intro H. exact (H (fun x => h x = b) (fun a' Hr => Hr)).
    - intros H Q HQ. exact (HQ a H).
  Qed.

  Lemma dslpRel_comp {A B C} (f : DSLPArr A B) (g : DSLPArr B C) a c :
    dslpRel (arr_comp f g) a c <-> exists b, dslpRel f a b /\ dslpRel g b c.
  Proof.
    split.
    - intro H.
      exact (H (fun x => exists b, dslpRel f x b /\ dslpRel g b c)
               (proj2 (get_dslpRel g _ c)
                  (fun b Hg => proj2 (get_dslpRel f _ b)
                                 (fun a' Hf => ex_intro _ b (conj Hf Hg))))).
    - intros [b [Hf Hg]] Q HQ. cbn in HQ.
      apply (proj1 (get_dslpRel f Q b)); [| exact Hf ].
      apply (proj1 (get_dslpRel g (f Q) c)); [ exact HQ | exact Hg ].
  Qed.

  Lemma dslpRel_first {A B C} (f : DSLPArr A B) (p : A * C) (q : B * C) :
    dslpRel (arr_first f) p q <-> dslpRel f (fst p) (fst q) /\ snd p = snd q.
  Proof.
    destruct p as [a c], q as [b c']. cbn [fst snd]. split.
    - intro H. split.
      + intros Q HQ. exact (H (fun p => Q (fst p)) HQ).
      + exact (H (fun p => snd p = c')
                 (proj2 (get_dslpRel f (fun x => c' = c') b) (fun a' _ => eq_refl))).
    - intros [Hf Hc]. cbn in Hc. subst c'. intros Q HQ.
      apply (proj1 (get_dslpRel f (fun a0 => Q (a0, c)) b)); [ exact HQ | exact Hf ].
  Qed.

  Lemma dslpRel_left {A B C} (f : DSLPArr A B) (x : A + C) (y : B + C) :
    dslpRel (arr_left f) x y <->
    match x, y with
    | inl a, inl b => dslpRel f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end.
  Proof.
    unfold dslpRel, dslpRelT. cbn [getDSLPArr arr_left ArrowChoice_DSLPArr].
    rewrite get_left. unfold leftDSLPT.
    destruct y as [b | c'].
    - destruct x as [a | c]; split.
      + intros H Q HQ.
        exact (H (fun z => match z with inl a0 => Q a0 | inr _ => True end) HQ).
      + intros Hr P HP. exact (proj1 (get_dslpRel f _ b) HP a Hr).
      + intro H.
        exact (H (fun z => match z with inl _ => True | inr _ => False end)
                 (proj2 (get_dslpRel f (fun _ => True) b) (fun _ _ => I))).
      + intros [].
    - destruct x as [a | c]; split.
      + intro H.
        exact (H (fun z => match z with inl _ => False | inr _ => True end) I).
      + intros [].
      + intro H. injection (H (fun z => z = inr c') eq_refl) as ->. reflexivity.
      + intros -> P HP. exact HP.
  Qed.

  Lemma dslpRel_app {A B} (p : DSLPArr A B * A) (b : B) :
    dslpRel arr_app p b <-> dslpRel (fst p) (snd p) b.
  Proof.
    destruct p as [f a]. cbn [fst snd]. split.
    - intro H.
      exact (H (fun q => dslpRel (fst q) (snd q) b) (fun f' a' Hr => Hr)).
    - intros Hr P HP. exact (HP f a Hr).
  Qed.

  (** Equality is relational; INCLUSION IS REVERSED, since [dslp] is
      antitone in its relation. *)
  Lemma dslpRel_eq {A B} (f g : DSLPArr A B) :
    DSLPArr_eq f g <-> (forall a b, dslpRel f a b <-> dslpRel g a b).
  Proof.
    split.
    - intros H a b. unfold dslpRel, dslpRelT. split; intros Hr P HP.
      + apply Hr, H, HP.
      + apply Hr, H, HP.
    - intros H P b. rewrite !get_dslpRel.
      split; intros HP a Hr; apply HP, H, Hr.
  Qed.

  Lemma dslpRel_incl {A B} (f g : DSLPArr A B) :
    (forall P b, f P b -> g P b) <-> (forall a b, dslpRel g a b -> dslpRel f a b).
  Proof.
    split.
    - intros H a b Hg P HP. exact (Hg P (H P b HP)).
    - intros H P b Hf. apply get_dslpRel. intros a Hg.
      exact (proj1 (get_dslpRel f P b) Hf a (H a b Hg)).
  Qed.

End Relation.

(* ================================================================= *)
(** ** Arrow laws                                                    *)
(* ================================================================= *)

(** Each law is an identity of relations, so every proof is the same one
    it would be for [ASPArr]: the arrows differ only in how a relation is
    read, not in which relation each operation denotes. *)

Local Ltac rel_eq :=
  apply dslpRel_eq; intros ?x ?y; unfold arr_id;
  repeat first [ setoid_rewrite dslpRel_comp | setoid_rewrite dslpRel_pure
               | setoid_rewrite dslpRel_first | setoid_rewrite dslpRel_app ];
  cbn [fst snd].

#[global] Instance ArrowLaws_DSLPArr : ArrowLaws DSLPArr.
Proof.
  constructor; intros.
  - (* comp_id_l *)
    rel_eq.
    split; [ intros [z [<- H]] | intro H; exists x ]; auto.
  - (* comp_id_r *)
    rel_eq.
    split; [ intros [z [H ->]] | intro H; exists y ]; auto.
  - (* comp_assoc *)
    rel_eq. firstorder.
  - (* pure_comp *)
    rel_eq. split; [ intros [z [<- H]] | intro H; eexists ]; auto.
  - (* first_pure *)
    rel_eq. destruct x as [a c], y as [b c']. cbn [fst snd]. split.
    + intros [H ->]. rewrite H. reflexivity.
    + intro H. injection H as <- <-. auto.
  - (* first_comp *)
    rel_eq. destruct x as [a c], y as [b c']. cbn [fst snd]. split.
    + intros [[z [H1 H2]] ->]. exists (z, c'). cbn. auto.
    + intros [[z c''] [[H1 ->] [H2 ->]]]. cbn in *. split; [ exists z |]; auto.
  - (* first_fst *)
    rel_eq. destruct x as [a c]. cbn [fst snd]. split.
    + intros [[b c'] [[H1 H2] H3]]. cbn in *. subst b. exists a. auto.
    + intros [z [Hz H]]. subst z. exists (y, c). cbn. auto.
  - (* first_assoc *)
    rel_eq. destruct x as [[a c] d], y as [b [c' d']].
    cbn [fst snd]. split.
    + intros [[[b0 c0] d0] [[[H1 H2] H3] Heq]]. cbn in *.
      injection Heq as Hb Hc Hd.
      exists (a, (c, d)). cbn. split; [ reflexivity | split ].
      * rewrite <- Hb. exact H1.
      * rewrite H2, Hc, H3, Hd. reflexivity.
    + intros [z [Heq [H1 H2]]]. subst z. cbn in *.
      injection H2 as Hc Hd.
      exists (b, c, d). cbn. rewrite Hc, Hd. auto.

  - (* comp_proper *)
    intros f f' Hf g g' Hg.
    pose proof (proj1 (dslpRel_eq f f') Hf) as Hf'.
    pose proof (proj1 (dslpRel_eq g g') Hg) as Hg'.
    rel_eq.
    split; intros [z [H1 H2]]; exists z; split;
      solve [ apply (proj1 (Hf' _ _)), H1 | apply (proj2 (Hf' _ _)), H1
            | apply (proj1 (Hg' _ _)), H2 | apply (proj2 (Hg' _ _)), H2 ].
  - (* first_proper *)
    intros f f' Hf.
    pose proof (proj1 (dslpRel_eq f f') Hf) as Hf'.
    rel_eq.
    split; intros [H Heq]; split;
      solve [ apply (proj1 (Hf' _ _)), H | apply (proj2 (Hf' _ _)), H | exact Heq ].
Qed.

(** Sum laws: split the input and output first, so that the [match] in
    [dslpRel_left] reduces and the inner relations become rewritable. *)
Local Ltac rel_sum :=
  apply dslpRel_eq; intros ?x ?y;
  unfold arr_id, sum_bimap, swap_sum, assoc_sum, sum_prod_dist;
  repeat match goal with z : (_ + _)%type |- _ => destruct z end;
  repeat match goal with z : (_ * _)%type |- _ => destruct z end;
  cbn [fst snd];
  repeat first [ setoid_rewrite dslpRel_comp | setoid_rewrite dslpRel_pure
               | setoid_rewrite dslpRel_first | setoid_rewrite dslpRel_left
               | setoid_rewrite dslpRel_app ];
  cbn [fst snd].

(** [sauto] closes the mixed cases; what is left are the goals whose
    witness is a sum injection, which [eauto] will not guess. *)
Local Ltac sum_step :=
  repeat match goal with
         | H : ex _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         | z : (_ + _)%type |- _ => destruct z
         | z : (_ * _)%type |- _ => destruct z
         end;
  rewrite ?dslpRel_left, ?dslpRel_first, ?dslpRel_pure in *;
  cbn in *;
  try contradiction;
  repeat match goal with
         | H : inl _ = inl _ |- _ => injection H as H
         | H : inr _ = inr _ |- _ => injection H as H
         | H : inl _ = inr _ |- _ => discriminate H
         | H : inr _ = inl _ |- _ => discriminate H
         | H : (_, _) = (_, _) |- _ => injection H as H
         end;
  subst.

Local Ltac sum_crush :=
  split; intro H; sum_step;
  solve [ eauto
        | eexists (inl _); sum_step; eauto
        | eexists (inr _); sum_step; eauto
        | eexists (inl (inl _)); sum_step; eauto
        | eexists (inl (inr _)); sum_step; eauto
        | eexists (inr (inl _)); sum_step; eauto
        | eexists (inr (inr _)); sum_step; eauto
        | eexists (inl _, _); sum_step; eauto
        | eexists (inr _, _); sum_step; eauto ].

#[global] Instance ArrowChoiceLaws_DSLPArr : ArrowChoiceLaws DSLPArr.
Proof.
  constructor; intros.
  - (* left_pure *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* left_comp *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* left_inl *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* left_assoc *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* left_inr *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* left_natural *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* first_left_dist *) rel_sum; try (sauto limit: 200); sum_crush.
  - (* left_proper *)
    intros f f' Hf.
    pose proof (proj1 (dslpRel_eq f f') Hf) as Hf'.
    rel_sum; solve [ apply Hf' | reflexivity | tauto ].
Qed.

#[global] Instance ArrowApplyLaws_DSLPArr : ArrowApplyLaws DSLPArr.
Proof.
  constructor.
  - (* app_law *)
    intros A B f. rel_eq. split.
    + intros [[g a] [Heq H]]. injection Heq as <- <-. exact H.
    + intro H. exists (f, x). cbn. auto.
  - (* app_pair *)
    intros A B. rel_eq. split.
    + intros [[k v] [[H1 H2] H3]]. cbn in *. subst k v.
      rewrite dslpRel_pure in H3. destruct x as [a b]. cbn in *. exact H3.
    + intro H. destruct x as [a b]. cbn in *.
      exists (pureDSLP (fun v : B => (a, v)), b). cbn.
      split; [ split; reflexivity |]. rewrite dslpRel_pure. exact H.
  - (* app_post *)
    intros A B C h. rel_eq. split.
    + intros [[k a] [[H1 H2] H3]]. cbn in *. subst k a.
      rewrite dslpRel_comp in H3. destruct x as [f a]. cbn in *. exact H3.
    + intros H. destruct x as [f a]. cbn in *.
      exists (compDSLP f h, a). cbn.
      split; [ split; reflexivity |]. rewrite dslpRel_comp. exact H.
  - (* app_ext *)
    intros X A B u v t Huv. rel_eq. split.
    + intros [[g a] [Heq H]]. injection Heq as <- <-.
      exists (v x, t x). cbn. split; [ reflexivity |].
      exact (proj1 (proj1 (dslpRel_eq (u x) (v x)) (Huv x) _ _) H).
    + intros [[g a] [Heq H]]. injection Heq as <- <-.
      exists (u x, t x). cbn. split; [ reflexivity |].
      exact (proj2 (proj1 (dslpRel_eq (u x) (v x)) (Huv x) _ _) H).
Qed.

Local Ltac flat :=
  repeat match goal with
  | H : exists _, _ |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | p : _ * _ |- _ => destruct p
  | H : (_, _) = (_, _) |- _ => inversion H; clear H
  | H : ?x = ?y |- _ => first [ subst x | subst y ]
  | _ => progress cbn in *
  end.

Local Ltac build :=
  repeat first [ progress cbn | eassumption | reflexivity | split
               | eexists (_, _) | eexists ].

Local Ltac rel_simpl :=
  repeat first [ setoid_rewrite dslpRel_comp | setoid_rewrite dslpRel_pure
               | setoid_rewrite dslpRel_first | setoid_rewrite dslpRel_app ].

(* ================================================================= *)
(** ** [bind] on relations, at a fixed input                        *)
(* ================================================================= *)

(** [ret_arrow a] ignores its input; [bind_arrow m k] runs [m] and then
    [k a] on the SAME input. *)

Section Mon.
  Lemma dslpRel_bind {I A B} (m : DSLPArr I A) (k : A -> DSLPArr I B) i b :
    dslpRel (@bind_arrow DSLPArr _ _ I A B m k) i b <-> exists a, dslpRel m i a /\ dslpRel (k a) i b.
  Proof.
    unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id. rel_simpl.
    split; [ intro H; flat; eauto | intros [a [Hm Hk]]; build ].
  Qed.
End Mon.


(* ================================================================= *)
(** ** [bind] on relations, under [stateArrT S]                     *)
(* ================================================================= *)

Section St.
  Variable S : Type.
  Lemma dslpRelS_ret {I A} (x : A) i s r :
    dslpRel (@ret_arrow (stateArrT S DSLPArr) _ I A x) (i, s) r <-> r = (x, s).
  Proof.
    unfold ret_arrow. cbn [arr_pure Arrow_stateArrT]. rewrite dslpRel_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma dslpRelS_bind {I A B} (m : stateArrT S DSLPArr I A)
    (k : A -> stateArrT S DSLPArr I B) i s r :
    dslpRel (@bind_arrow (stateArrT S DSLPArr) _ _ I A B m k) (i, s) r
    <-> exists a s', dslpRel m (i, s) (a, s') /\ dslpRel (k a) (i, s') r.
  Proof.
    unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id.
    cbn [arr_comp arr_pure arr_first arr_app Arrow_stateArrT ArrowApply_stateArrT].
    rel_simpl.
    split; [ intro H; flat; eauto | intros [a [s' [Hm Hk]]]; build ].
  Qed.
End St.



(* ================================================================= *)
(** ** [bind] on relations, under [stateArrT S (optionArrT _)]      *)
(* ================================================================= *)

(** First [optionArrT] alone, then the state layer on top. *)

Section Opt.
  Lemma dslpRelO_comp {X Y Z} (f : optionArrT DSLPArr X Y) (g : optionArrT DSLPArr Y Z) x o :
    dslpRel (@arr_comp (optionArrT DSLPArr) _ X Y Z f g) x o <->
    exists o1, dslpRel f x o1 /\ match o1 with Some y => dslpRel g y o | None => o = None end.
  Proof.
    cbn [arr_comp Arrow_optionArrT].
    repeat first [ setoid_rewrite dslpRel_comp | setoid_rewrite dslpRel_pure
                 | setoid_rewrite dslpRel_left ].
    split.
    - intros [b [Hf [c [Hc [d [Hd Ho]]]]]]. subst c o. exists b. split; [ exact Hf |].
      destruct b as [y|], d as [z|[]]; cbn in *; solve [ exact Hd | contradiction | reflexivity ].
    - intros [[y|] [Hf Hg]].
      + exists (Some y). split; [ exact Hf |]. exists (inl y). split; [ reflexivity |].
        exists (inl o). split; [ exact Hg | reflexivity ].
      + subst o. exists None. split; [ exact Hf |]. exists (inr tt). split; [ reflexivity |].
        exists (inr tt). split; reflexivity.
  Qed.

  Lemma dslpRelO_pure {X Y} (h : X -> Y) x o :
    dslpRel (@arr_pure (optionArrT DSLPArr) _ X Y h) x o <-> o = Some (h x).
  Proof.
    cbn [arr_pure Arrow_optionArrT]. rewrite dslpRel_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma dslpRelO_first {X Y C} (f : optionArrT DSLPArr X Y) x (c : C) o :
    dslpRel (@arr_first (optionArrT DSLPArr) _ X Y C f) (x, c) o <->
    exists o1, dslpRel f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    cbn [arr_first arr_comp Arrow_optionArrT].
    rewrite dslpRel_comp. setoid_rewrite dslpRel_first. setoid_rewrite dslpRel_pure.
    split.
    - intros [[o1 c'] [[Hf Hc] Ho]]. cbn in *. subst. exists o1. split; [ exact Hf |].
      destruct o1; reflexivity.
    - intros [o1 [Hf ->]]. exists (o1, c). cbn. split; [ exact (conj Hf eq_refl) |].
      destruct o1; reflexivity.
  Qed.
End Opt.

Local Ltac simp_in H := cbv beta iota delta [state_shuffle_in state_shuffle_out swap] in H.

Section StExc.
  Variable S : Type.
  Notation T := (stateArrT S (optionArrT DSLPArr)).

  Lemma dslpRelE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
    dslpRel (@arr_comp T _ X Y Z f g) p o <->
    exists o1, dslpRel f p o1 /\ match o1 with Some q => dslpRel g q o | None => o = None end.
  Proof. exact (dslpRelO_comp f g p o). Qed.

  Lemma dslpRelE_pure {X Y} (h : X -> Y) x s o :
    dslpRel (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
  Proof. exact (dslpRelO_pure _ (x, s) o). Qed.

  Lemma dslpRelE_first {X Y C} (f : T X Y) x (c : C) s o :
    dslpRel (@arr_first T _ X Y C f) ((x, c), s) o <->
    exists o1, dslpRel f (x, s) o1 /\
      o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
  Proof.
    unfold arr_first at 1; cbn [Arrow_stateArrT].
    rewrite dslpRelO_comp. split.
    - intros [o1 [H1 H2]]. apply dslpRelO_pure in H1. subst o1. simp_in H2.
      apply dslpRelO_comp in H2. destruct H2 as [o2 [H2 H3]].
      apply dslpRelO_first in H2. destruct H2 as [o3 [H3' ->]].
      exists o3. split; [ exact H3' |].
      destruct o3 as [[y s']|]; simp_in H3; [ apply dslpRelO_pure in H3 |]; exact H3.
    - intros [o1 [Hf ->]]. exists (Some ((x, s), c)). split; [ apply dslpRelO_pure; reflexivity |].
      apply dslpRelO_comp. exists (match o1 with Some y => Some (y, c) | None => None end).
      split; [ apply dslpRelO_first; exists o1; split; [ exact Hf | reflexivity ] |].
      destruct o1 as [[y s']|]; [ apply dslpRelO_pure |]; reflexivity.
  Qed.

  Lemma dslpRelE_app {X Y} (f : T X Y) x s o :
    dslpRel (@arr_app T _ _ X Y) ((f, x), s) o <-> dslpRel f (x, s) o.
  Proof.
    unfold arr_app at 1; cbn [ArrowApply_stateArrT].
    rewrite dslpRelO_comp. split.
    - intros [o1 [H1 H2]]. apply dslpRelO_pure in H1. subst o1. exact (proj1 (dslpRel_app (f, (x, s)) o) H2).
    - intro H. exists (Some (f, (x, s))). split; [ apply dslpRelO_pure; reflexivity |].
      exact (proj2 (dslpRel_app (f, (x, s)) o) H).
  Qed.

  Lemma dslpRelE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
    dslpRel (@bind_arrow T _ _ I A B m k) (i, s) o
    <-> exists o1, dslpRel m (i, s) o1 /\
          match o1 with Some (a, s') => dslpRel (k a) (i, s') o | None => o = None end.
  Proof.
    unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id.
    rewrite dslpRelE_comp. split.
    - intros [o1 [H1 H2]].
      apply dslpRelE_comp in H1. destruct H1 as [o2 [H1 H3]]. apply dslpRelE_pure in H1. subst o2.
      apply dslpRelE_comp in H3. destruct H3 as [o3 [H3 H4]].
      apply dslpRelE_first in H3. destruct H3 as [o4 [Hm ->]].
      exists o4. split; [ exact Hm |].
      destruct o4 as [[a s']|]; simp_in H4; [| subst o1; exact H2 ].
      apply dslpRelE_comp in H4. destruct H4 as [o5 [H4 H5]].
      apply dslpRelE_pure in H4. subst o5. simp_in H5.
      apply dslpRelE_comp in H5. destruct H5 as [o6 [H5 H6]].
      apply dslpRelE_first in H5. destruct H5 as [o7 [H5 ->]].
      apply dslpRelE_pure in H5. subst o7. simp_in H6.
      apply dslpRelE_pure in H6. subst o1. simp_in H2.
      apply dslpRelE_comp in H2. destruct H2 as [o8 [H7 H8]].
      apply dslpRelE_pure in H7. subst o8. simp_in H8.
      exact (proj1 (dslpRelE_app (k a) i s' o) H8).
    - intros [o1 [Hm Hk]].
      exists (match o1 with Some (a, s') => Some ((a, i), s') | None => None end).
      split.
      + apply dslpRelE_comp. exists (Some ((i, i), s)). split; [ apply dslpRelE_pure; reflexivity |].
        apply dslpRelE_comp.
        exists (match o1 with Some (a, s') => Some ((a, i), s') | None => None end).
        split; [ apply dslpRelE_first; exists o1; split; [ exact Hm | reflexivity ] |].
        destruct o1 as [[a s']|]; [| reflexivity ].
        apply dslpRelE_comp. exists (Some ((i, a), s')). split; [ apply dslpRelE_pure; reflexivity |].
        apply dslpRelE_comp. exists (Some ((i, a), s')).
        split; [ apply dslpRelE_first; exists (Some (i, s')); split; [ apply dslpRelE_pure | ]; reflexivity |].
        apply dslpRelE_pure. reflexivity.
      + destruct o1 as [[a s']|]; [| exact Hk ].
        apply dslpRelE_comp. exists (Some ((k a, i), s')). split; [ apply dslpRelE_pure; reflexivity |].
        exact (proj2 (dslpRelE_app (k a) i s' o) Hk).
  Qed.
End StExc.

Section StExcRet.
  Variable S : Type.
  Lemma dslpRelE_ret {I A} (a : A) i s o :
    dslpRel (@ret_arrow (stateArrT S (optionArrT DSLPArr)) _ I A a) (i, s) o <-> o = Some (a, s).
  Proof. unfold ret_arrow. cbn [arr_pure Arrow_stateArrT]. rewrite dslpRelO_pure. reflexivity. Qed.
End StExcRet.
