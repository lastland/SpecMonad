(** * The relation an [ASPArr] denotes

    [aspRel f a b] is [f] at the singleton [a], reaching [b].  By
    [asp_join] this determines [f] ([get_aspRel]), so an arrow and the
    relation it denotes are interchangeable -- which is what every proof
    in [ASPMonad.v] uses: the arrow operations are read off as relational
    composition, and [bind] monotonicity comes from [aspRel_incl].

    Split out of [ASPMonad.v] so that the arrow (in [ASPArrowCore.v]) and
    the specification monads (in [ASPMonad.v]) are separable from the
    relational reasoning that connects them. *)

From Coq Require Import Morphisms RelationClasses Setoid.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT OrderedMonad.
From Incorrectness.Classes Require Import ArrowMonad RelArrowCoherence.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPArrowCore SPure.

(* ================================================================= *)
(** ** The relation an arrow denotes                                 *)
(* ================================================================= *)

(** [aspRel f a b]: [f] at the singleton [a] reaches [b].  By [asp_join]
    this determines [f]. *)

Section Relation.

  Definition aspRel {A B} (f : ASPArr A B) (a : A) (b : B) : Prop :=
    ASPArrowCore.aspRel f a b.

  Lemma get_aspRel {A B} (f : ASPArr A B) P b :
    f P b <-> exists a, P a /\ aspRel f a b.
  Proof. exact (getASPArr_join f P b). Qed.

  (** The arrow of a relation denotes that relation. *)
  Lemma aspRel_ofRel {A B} (R : A -> B -> Prop) a b :
    aspRel (ofRelASPArr R) a b <-> R a b.
  Proof.
    unfold aspRel, ofRelASPArr. cbn. split.
    - intros [x [Hx HR]]. subst x. exact HR.
    - intro HR. exists a. auto.
  Qed.

  Lemma ofRel_aspRel {A B} (f : ASPArr A B) P b :
    ofRelASPArr (aspRel f) P b <-> f P b.
  Proof.
    unfold aspRel, ofRelASPArr. cbn. split; apply getASPArr_join.
  Qed.

  Lemma aspRel_pure {A B} (h : A -> B) a b : aspRel (arr_pure h) a b <-> h a = b.
  Proof. exact (ASPArrowCore.aspRel_pure h a b). Qed.

  Lemma aspRel_comp {A B C} (f : ASPArr A B) (g : ASPArr B C) a c :
    aspRel (arr_comp f g) a c <-> exists b, aspRel f a b /\ aspRel g b c.
  Proof. exact (ASPArrowCore.aspRel_comp f g a c). Qed.

  Lemma aspRel_first {A B C} (f : ASPArr A B) (p : A * C) (q : B * C) :
    aspRel (arr_first f) p q <-> aspRel f (fst p) (fst q) /\ snd p = snd q.
  Proof. exact (ASPArrowCore.aspRel_first f p q). Qed.

  Lemma aspRel_left {A B C} (f : ASPArr A B) (x : A + C) (y : B + C) :
    aspRel (arr_left f) x y <->
    match x, y with
    | inl a, inl b => aspRel f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end.
  Proof. exact (ASPArrowCore.aspRel_left f x y). Qed.

  (** Equality and the refinement order are relational too. *)
  Lemma aspRel_eq {A B} (f g : ASPArr A B) :
    ASPArr_eq f g <-> (forall a b, aspRel f a b <-> aspRel g a b).
  Proof. exact (ASPArrowCore.aspRel_eq f g). Qed.

  Lemma aspRel_incl {A B} (f g : ASPArr A B) :
    (forall P b, f P b -> g P b) <-> (forall a b, aspRel f a b -> aspRel g a b).
  Proof.
    split.
    - intros H a b. apply H.
    - intros H P b Hf. apply get_aspRel in Hf. destruct Hf as [a [Hp Hr]].
      apply get_aspRel. exists a. split; [ exact Hp | apply H, Hr ].
  Qed.

  Lemma aspRel_app {A B} (p : ASPArr A B * A) (b : B) :
    aspRel arr_app p b <-> aspRel (fst p) (snd p) b.
  Proof. exact (ASPArrowCore.aspRel_app p b). Qed.

End Relation.

Local Definition aspRelDenote :
  @RelDenote ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
    (@ASPArrowRel.aspRel) :=
  @Build_RelDenote ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
    (@ASPArrowRel.aspRel) (@aspRel_pure) (@aspRel_comp) (@aspRel_first)
    (@aspRel_left) (@aspRel_app).

(* ================================================================= *)
(** ** [bind] on relations, at a fixed input                        *)
(* ================================================================= *)

(** [ret_arrow a] ignores its input; [bind_arrow m k] runs [m] and then
    [k a] on the SAME input. *)

Section Mon.
  Lemma aspRel_bind {I A B} (m : ASPArr I A) (k : A -> ASPArr I B) i b :
    aspRel (@bind_arrow ASPArr _ _ I A B m k) i b <-> exists a, aspRel m i a /\ aspRel (k a) i b.
  Proof.
    exact (@SPure.rel_bind ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote I A B m k i b).
  Qed.
End Mon.


(* ================================================================= *)
(** ** [bind] on relations, under [stateArrT S]                     *)
(* ================================================================= *)

Section St.
  Variable S : Type.
  Lemma aspRelS_ret {I A} (x : A) i s r :
    aspRel (@ret_arrow (stateArrT S ASPArr) _ I A x) (i, s) r <-> r = (x, s).
  Proof.
    unfold ret_arrow. cbn [arr_pure Arrow_stateArrT]. rewrite aspRel_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma aspRelS_bind {I A B} (m : stateArrT S ASPArr I A)
    (k : A -> stateArrT S ASPArr I B) i s r :
    aspRel (@bind_arrow (stateArrT S ASPArr) _ _ I A B m k) (i, s) r
    <-> exists a s', aspRel m (i, s) (a, s') /\ aspRel (k a) (i, s') r.
  Proof.
    exact (@SPure.relS_bind ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S I A B m k i s r).
  Qed.
End St.



(* ================================================================= *)
(** ** [bind] on relations, under [stateArrT S (optionArrT _)]      *)
(* ================================================================= *)

(** First [optionArrT] alone, then the state layer on top. *)

Section Opt.
  Lemma aspRelO_comp {X Y Z} (f : optionArrT ASPArr X Y) (g : optionArrT ASPArr Y Z) x o :
    aspRel (@arr_comp (optionArrT ASPArr) _ X Y Z f g) x o <->
    exists o1, aspRel f x o1 /\ match o1 with Some y => aspRel g y o | None => o = None end.
  Proof.
    exact (@SPure.relO_comp ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote X Y Z f g x o).
  Qed.

  Lemma aspRelO_pure {X Y} (h : X -> Y) x o :
    aspRel (@arr_pure (optionArrT ASPArr) _ X Y h) x o <-> o = Some (h x).
  Proof.
    exact (@SPure.relO_pure ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote X Y h x o).
  Qed.

  Lemma aspRelO_first {X Y C} (f : optionArrT ASPArr X Y) x (c : C) o :
    aspRel (@arr_first (optionArrT ASPArr) _ X Y C f) (x, c) o <->
    exists o1, aspRel f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    exact (@SPure.relO_first ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote X Y C f x c o).
  Qed.
End Opt.

Section StExc.
  Variable S : Type.
  Notation T := (stateArrT S (optionArrT ASPArr)).

  Lemma aspRelE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
    aspRel (@arr_comp T _ X Y Z f g) p o <->
    exists o1, aspRel f p o1 /\ match o1 with Some q => aspRel g q o | None => o = None end.
  Proof.
    exact (@SPure.relE_comp ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S X Y Z f g p o).
  Qed.

  Lemma aspRelE_pure {X Y} (h : X -> Y) x s o :
    aspRel (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
  Proof.
    exact (@SPure.relE_pure ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S X Y h x s o).
  Qed.

  Lemma aspRelE_first {X Y C} (f : T X Y) x (c : C) s o :
    aspRel (@arr_first T _ X Y C f) ((x, c), s) o <->
    exists o1, aspRel f (x, s) o1 /\
      o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
  Proof.
    exact (@SPure.relE_first ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S X Y C f x c s o).
  Qed.

  Lemma aspRelE_app {X Y} (f : T X Y) x s o :
    aspRel (@arr_app T _ _ X Y) ((f, x), s) o <-> aspRel f (x, s) o.
  Proof.
    exact (@SPure.relE_app ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S X Y f x s o).
  Qed.

  Lemma aspRelE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
    aspRel (@bind_arrow T _ _ I A B m k) (i, s) o
    <-> exists o1, aspRel m (i, s) o1 /\
          match o1 with Some (a, s') => aspRel (k a) (i, s') o | None => o = None end.
  Proof.
    exact (@SPure.relE_bind ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S I A B m k i s o).
  Qed.
End StExc.

Section StExcRet.
  Variable S : Type.
  Lemma aspRelE_ret {I A} (a : A) i s o :
    aspRel (@ret_arrow (stateArrT S (optionArrT ASPArr)) _ I A a) (i, s) o <-> o = Some (a, s).
  Proof.
    exact (@SPure.relE_pure ASPArr Arrow_ASPArr ArrowChoice_ASPArr ArrowApply_ASPArr
      (@ASPArrowRel.aspRel) aspRelDenote S I A (fun _ => a) i s o).
  Qed.
End StExcRet.
