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
From Incorrectness.Classes Require Import ArrowMonad RelArrowCoherence.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import DSLPArrowCore SPure.

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

#[global] Instance RelArrow_DSLPArr : RelArrow DSLPArr := {|
  rel_reading := @dslpRel; rel_pure := @dslpRel_pure; rel_comp := @dslpRel_comp;
  rel_first := fun A B C f a c b d => dslpRel_first f (a, c) (b, d)
|}.
#[global] Instance RelArrowChoice_DSLPArr : RelArrowChoice DSLPArr := {|rel_left := @dslpRel_left|}.
#[global] Instance RelArrowApply_DSLPArr : RelArrowApply DSLPArr := {|
  rel_app := fun A B f a b => dslpRel_app (f, a) b
|}.
#[global] Instance RelArrowEq_DSLPArr : RelArrowEq DSLPArr := {|rel_arrow_eq := @dslpRel_eq|}.
#[global] Instance ArrowLaws_DSLPArr : ArrowLaws DSLPArr :=
  @rel_arrow_laws DSLPArr Arrow_DSLPArr ArrowEq_DSLPArr RelArrow_DSLPArr RelArrowEq_DSLPArr.
#[global] Instance ArrowChoiceLaws_DSLPArr : ArrowChoiceLaws DSLPArr :=
  @rel_arrow_choice_laws DSLPArr Arrow_DSLPArr ArrowEq_DSLPArr RelArrow_DSLPArr
    RelArrowEq_DSLPArr ArrowChoice_DSLPArr RelArrowChoice_DSLPArr.
#[global] Instance ArrowApplyLaws_DSLPArr : ArrowApplyLaws DSLPArr :=
  @rel_arrow_apply_laws DSLPArr Arrow_DSLPArr ArrowEq_DSLPArr RelArrow_DSLPArr
    RelArrowEq_DSLPArr ArrowApply_DSLPArr RelArrowApply_DSLPArr.

Local Definition dslpRelDenote :
  @RelDenote DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
    (@DSLPArrowRel.dslpRel) :=
  @Build_RelDenote DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
    (@DSLPArrowRel.dslpRel) (@dslpRel_pure) (@dslpRel_comp) (@dslpRel_first)
    (@dslpRel_left) (@dslpRel_app).

(* ================================================================= *)
(** ** [bind] on relations, at a fixed input                        *)
(* ================================================================= *)

(** [ret_arrow a] ignores its input; [bind_arrow m k] runs [m] and then
    [k a] on the SAME input. *)

Section Mon.
  Lemma dslpRel_bind {I A B} (m : DSLPArr I A) (k : A -> DSLPArr I B) i b :
    dslpRel (@bind_arrow DSLPArr _ _ I A B m k) i b <-> exists a, dslpRel m i a /\ dslpRel (k a) i b.
  Proof.
    exact (@SPure.rel_bind DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote I A B m k i b).
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
    exact (@SPure.relS_bind DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S I A B m k i s r).
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
    exact (@SPure.relO_comp DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote X Y Z f g x o).
  Qed.

  Lemma dslpRelO_pure {X Y} (h : X -> Y) x o :
    dslpRel (@arr_pure (optionArrT DSLPArr) _ X Y h) x o <-> o = Some (h x).
  Proof.
    exact (@SPure.relO_pure DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote X Y h x o).
  Qed.

  Lemma dslpRelO_first {X Y C} (f : optionArrT DSLPArr X Y) x (c : C) o :
    dslpRel (@arr_first (optionArrT DSLPArr) _ X Y C f) (x, c) o <->
    exists o1, dslpRel f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    exact (@SPure.relO_first DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote X Y C f x c o).
  Qed.
End Opt.

Section StExc.
  Variable S : Type.
  Notation T := (stateArrT S (optionArrT DSLPArr)).

  Lemma dslpRelE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
    dslpRel (@arr_comp T _ X Y Z f g) p o <->
    exists o1, dslpRel f p o1 /\ match o1 with Some q => dslpRel g q o | None => o = None end.
  Proof.
    exact (@SPure.relE_comp DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S X Y Z f g p o).
  Qed.

  Lemma dslpRelE_pure {X Y} (h : X -> Y) x s o :
    dslpRel (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
  Proof.
    exact (@SPure.relE_pure DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S X Y h x s o).
  Qed.

  Lemma dslpRelE_first {X Y C} (f : T X Y) x (c : C) s o :
    dslpRel (@arr_first T _ X Y C f) ((x, c), s) o <->
    exists o1, dslpRel f (x, s) o1 /\
      o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
  Proof.
    exact (@SPure.relE_first DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S X Y C f x c s o).
  Qed.

  Lemma dslpRelE_app {X Y} (f : T X Y) x s o :
    dslpRel (@arr_app T _ _ X Y) ((f, x), s) o <-> dslpRel f (x, s) o.
  Proof.
    exact (@SPure.relE_app DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S X Y f x s o).
  Qed.

  Lemma dslpRelE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
    dslpRel (@bind_arrow T _ _ I A B m k) (i, s) o
    <-> exists o1, dslpRel m (i, s) o1 /\
          match o1 with Some (a, s') => dslpRel (k a) (i, s') o | None => o = None end.
  Proof.
    exact (@SPure.relE_bind DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S I A B m k i s o).
  Qed.
End StExc.

Section StExcRet.
  Variable S : Type.
  Lemma dslpRelE_ret {I A} (a : A) i s o :
    dslpRel (@ret_arrow (stateArrT S (optionArrT DSLPArr)) _ I A a) (i, s) o <-> o = Some (a, s).
  Proof.
    exact (@SPure.relE_pure DSLPArr Arrow_DSLPArr ArrowChoice_DSLPArr ArrowApply_DSLPArr
      (@DSLPArrowRel.dslpRel) dslpRelDenote S I A (fun _ => a) i s o).
  Qed.
End StExcRet.
