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
From Incorrectness.Classes Require Import ArrowMonad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import ASPArrowCore.

(* ================================================================= *)
(** ** The relation an arrow denotes                                 *)
(* ================================================================= *)

(** [aspRel f a b]: [f] at the singleton [a] reaches [b].  By [asp_join]
    this determines [f]. *)

Section Relation.

  Definition aspRel {A B} (f : ASPArr A B) (a : A) (b : B) : Prop :=
    f (fun x => x = a) b.

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
  Proof.
    cbn. split; [ intros [x [-> H]]; exact H | intro H; exists a; auto ].
  Qed.

  Lemma aspRel_comp {A B C} (f : ASPArr A B) (g : ASPArr B C) a c :
    aspRel (arr_comp f g) a c <-> exists b, aspRel f a b /\ aspRel g b c.
  Proof. exact (get_aspRel g _ c). Qed.

  Lemma aspRel_first {A B C} (f : ASPArr A B) (p : A * C) (q : B * C) :
    aspRel (arr_first f) p q <-> aspRel f (fst p) (fst q) /\ snd p = snd q.
  Proof.
    destruct p as [a c], q as [b c']. cbn - [getASPArr].
    unfold aspRel. rewrite get_first. cbv beta. cbn [fst snd].
    rewrite (get_aspRel f). split.
    - intros [x [Hx H]]. inversion Hx; subst; auto.
    - intros [H ->]. exists a. auto.
  Qed.

  Lemma aspRel_left {A B C} (f : ASPArr A B) (x : A + C) (y : B + C) :
    aspRel (arr_left f) x y <->
    match x, y with
    | inl a, inl b => aspRel f a b
    | inr c, inr c' => c = c'
    | _, _ => False
    end.
  Proof.
    unfold aspRel. cbn - [getASPArr]. rewrite get_left. unfold leftASPT.
    destruct y as [b | c'].
    - rewrite (get_aspRel f). destruct x as [a | c]; split.
      + intros [x [Hx H]]. inversion Hx; subst; exact H.
      + intro H. exists a. auto.
      + intros [x [Hx _]]. discriminate Hx.
      + intros [].
    - destruct x as [a | c]; cbn; split; intro H.
      + discriminate H.
      + destruct H.
      + inversion H; subst; reflexivity.
      + subst. reflexivity.
  Qed.

  (** Equality and the refinement order are relational too. *)
  Lemma aspRel_eq {A B} (f g : ASPArr A B) :
    ASPArr_eq f g <-> (forall a b, aspRel f a b <-> aspRel g a b).
  Proof.
    split.
    - intros H a b. apply H.
    - intros H P b. rewrite !get_aspRel. split;
        intros [a [Hp Hr]]; exists a; split; solve [ exact Hp | apply H, Hr ].
  Qed.

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
  Proof.
    destruct p as [f a]. unfold aspRel. cbn - [getASPArr]. rewrite get_app. split.
    - intros [f' [a' [Heq H]]]. inversion Heq; subst; exact H.
    - intro H. exists f, a. auto.
  Qed.

End Relation.

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
  repeat first [ setoid_rewrite aspRel_comp | setoid_rewrite aspRel_pure
               | setoid_rewrite aspRel_first | setoid_rewrite aspRel_app ].

(* ================================================================= *)
(** ** [bind] on relations, at a fixed input                        *)
(* ================================================================= *)

(** [ret_arrow a] ignores its input; [bind_arrow m k] runs [m] and then
    [k a] on the SAME input. *)

Section Mon.
  Lemma aspRel_bind {I A B} (m : ASPArr I A) (k : A -> ASPArr I B) i b :
    aspRel (@bind_arrow ASPArr _ _ I A B m k) i b <-> exists a, aspRel m i a /\ aspRel (k a) i b.
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
  Lemma aspRelO_comp {X Y Z} (f : optionArrT ASPArr X Y) (g : optionArrT ASPArr Y Z) x o :
    aspRel (@arr_comp (optionArrT ASPArr) _ X Y Z f g) x o <->
    exists o1, aspRel f x o1 /\ match o1 with Some y => aspRel g y o | None => o = None end.
  Proof.
    cbn [arr_comp Arrow_optionArrT].
    repeat first [ setoid_rewrite aspRel_comp | setoid_rewrite aspRel_pure
                 | setoid_rewrite aspRel_left ].
    split.
    - intros [b [Hf [c [Hc [d [Hd Ho]]]]]]. subst c o. exists b. split; [ exact Hf |].
      destruct b as [y|], d as [z|[]]; cbn in *; solve [ exact Hd | contradiction | reflexivity ].
    - intros [[y|] [Hf Hg]].
      + exists (Some y). split; [ exact Hf |]. exists (inl y). split; [ reflexivity |].
        exists (inl o). split; [ exact Hg | reflexivity ].
      + subst o. exists None. split; [ exact Hf |]. exists (inr tt). split; [ reflexivity |].
        exists (inr tt). split; reflexivity.
  Qed.

  Lemma aspRelO_pure {X Y} (h : X -> Y) x o :
    aspRel (@arr_pure (optionArrT ASPArr) _ X Y h) x o <-> o = Some (h x).
  Proof.
    cbn [arr_pure Arrow_optionArrT]. rewrite aspRel_pure.
    split; intro H; symmetry; exact H.
  Qed.

  Lemma aspRelO_first {X Y C} (f : optionArrT ASPArr X Y) x (c : C) o :
    aspRel (@arr_first (optionArrT ASPArr) _ X Y C f) (x, c) o <->
    exists o1, aspRel f x o1 /\ o = match o1 with Some y => Some (y, c) | None => None end.
  Proof.
    cbn [arr_first arr_comp Arrow_optionArrT].
    rewrite aspRel_comp. setoid_rewrite aspRel_first. setoid_rewrite aspRel_pure.
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
  Notation T := (stateArrT S (optionArrT ASPArr)).

  Lemma aspRelE_comp {X Y Z} (f : T X Y) (g : T Y Z) p o :
    aspRel (@arr_comp T _ X Y Z f g) p o <->
    exists o1, aspRel f p o1 /\ match o1 with Some q => aspRel g q o | None => o = None end.
  Proof. exact (aspRelO_comp f g p o). Qed.

  Lemma aspRelE_pure {X Y} (h : X -> Y) x s o :
    aspRel (@arr_pure T _ X Y h) (x, s) o <-> o = Some (h x, s).
  Proof. exact (aspRelO_pure _ (x, s) o). Qed.

  Lemma aspRelE_first {X Y C} (f : T X Y) x (c : C) s o :
    aspRel (@arr_first T _ X Y C f) ((x, c), s) o <->
    exists o1, aspRel f (x, s) o1 /\
      o = match o1 with Some (y, s') => Some ((y, c), s') | None => None end.
  Proof.
    unfold arr_first at 1; cbn [Arrow_stateArrT].
    rewrite aspRelO_comp. split.
    - intros [o1 [H1 H2]]. apply aspRelO_pure in H1. subst o1. simp_in H2.
      apply aspRelO_comp in H2. destruct H2 as [o2 [H2 H3]].
      apply aspRelO_first in H2. destruct H2 as [o3 [H3' ->]].
      exists o3. split; [ exact H3' |].
      destruct o3 as [[y s']|]; simp_in H3; [ apply aspRelO_pure in H3 |]; exact H3.
    - intros [o1 [Hf ->]]. exists (Some ((x, s), c)). split; [ apply aspRelO_pure; reflexivity |].
      apply aspRelO_comp. exists (match o1 with Some y => Some (y, c) | None => None end).
      split; [ apply aspRelO_first; exists o1; split; [ exact Hf | reflexivity ] |].
      destruct o1 as [[y s']|]; [ apply aspRelO_pure |]; reflexivity.
  Qed.

  Lemma aspRelE_app {X Y} (f : T X Y) x s o :
    aspRel (@arr_app T _ _ X Y) ((f, x), s) o <-> aspRel f (x, s) o.
  Proof.
    unfold arr_app at 1; cbn [ArrowApply_stateArrT].
    rewrite aspRelO_comp. split.
    - intros [o1 [H1 H2]]. apply aspRelO_pure in H1. subst o1. exact (proj1 (aspRel_app (f, (x, s)) o) H2).
    - intro H. exists (Some (f, (x, s))). split; [ apply aspRelO_pure; reflexivity |].
      exact (proj2 (aspRel_app (f, (x, s)) o) H).
  Qed.

  Lemma aspRelE_bind {I A B} (m : T I A) (k : A -> T I B) i s o :
    aspRel (@bind_arrow T _ _ I A B m k) (i, s) o
    <-> exists o1, aspRel m (i, s) o1 /\
          match o1 with Some (a, s') => aspRel (k a) (i, s') o | None => o = None end.
  Proof.
    unfold bind_arrow, arr_fanout, arr_split, arr_second, arr_id.
    rewrite aspRelE_comp. split.
    - intros [o1 [H1 H2]].
      apply aspRelE_comp in H1. destruct H1 as [o2 [H1 H3]]. apply aspRelE_pure in H1. subst o2.
      apply aspRelE_comp in H3. destruct H3 as [o3 [H3 H4]].
      apply aspRelE_first in H3. destruct H3 as [o4 [Hm ->]].
      exists o4. split; [ exact Hm |].
      destruct o4 as [[a s']|]; simp_in H4; [| subst o1; exact H2 ].
      apply aspRelE_comp in H4. destruct H4 as [o5 [H4 H5]].
      apply aspRelE_pure in H4. subst o5. simp_in H5.
      apply aspRelE_comp in H5. destruct H5 as [o6 [H5 H6]].
      apply aspRelE_first in H5. destruct H5 as [o7 [H5 ->]].
      apply aspRelE_pure in H5. subst o7. simp_in H6.
      apply aspRelE_pure in H6. subst o1. simp_in H2.
      apply aspRelE_comp in H2. destruct H2 as [o8 [H7 H8]].
      apply aspRelE_pure in H7. subst o8. simp_in H8.
      exact (proj1 (aspRelE_app (k a) i s' o) H8).
    - intros [o1 [Hm Hk]].
      exists (match o1 with Some (a, s') => Some ((a, i), s') | None => None end).
      split.
      + apply aspRelE_comp. exists (Some ((i, i), s)). split; [ apply aspRelE_pure; reflexivity |].
        apply aspRelE_comp.
        exists (match o1 with Some (a, s') => Some ((a, i), s') | None => None end).
        split; [ apply aspRelE_first; exists o1; split; [ exact Hm | reflexivity ] |].
        destruct o1 as [[a s']|]; [| reflexivity ].
        apply aspRelE_comp. exists (Some ((i, a), s')). split; [ apply aspRelE_pure; reflexivity |].
        apply aspRelE_comp. exists (Some ((i, a), s')).
        split; [ apply aspRelE_first; exists (Some (i, s')); split; [ apply aspRelE_pure | ]; reflexivity |].
        apply aspRelE_pure. reflexivity.
      + destruct o1 as [[a s']|]; [| exact Hk ].
        apply aspRelE_comp. exists (Some ((k a, i), s')). split; [ apply aspRelE_pure; reflexivity |].
        exact (proj2 (aspRelE_app (k a) i s' o) Hk).
  Qed.
End StExc.

Section StExcRet.
  Variable S : Type.
  Lemma aspRelE_ret {I A} (a : A) i s o :
    aspRel (@ret_arrow (stateArrT S (optionArrT ASPArr)) _ I A a) (i, s) o <-> o = Some (a, s).
  Proof. unfold ret_arrow. cbn [arr_pure Arrow_stateArrT]. rewrite aspRelO_pure. reflexivity. Qed.
End StExcRet.
