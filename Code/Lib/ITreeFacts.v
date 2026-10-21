(** * Facts about the paths of interaction trees

    Complements to ITree's [Props.Leaf] and [Props.Infinite]: one-step
    inversions of [any_infinite] that need no dependent elimination
    axioms, the infinite paths of a [bind] ([any_infinite_bind_l],
    [any_infinite_bind_leaf], [any_infinite_bind_inv], the last by excluded
    middle), and, if every event has an answer, that every tree has a leaf
    or an infinite path ([leaf_or_infinite], by excluded middle).

    [any_infinite_bind_leaf] is the one result here that does rest on a
    dependent elimination axiom: [Print Assumptions] reports Coq's
    [Eqdep.Eq_rect_eq.eq_rect_eq] for it, introduced by applying [DivVis]
    in its [Vis] case, where the event type is existential.  It is the only
    use in the development, and it is not a further assumption:
    [eq_rect_eq_from_propext] below derives that statement from
    propositional extensionality, which the development already assumes.
    Coq's tactics still cite the standard-library axiom, so the report is
    unchanged. *)

From Coq Require Import Classical_Prop ClassicalFacts PropExtensionality.
From Paco Require Import paco.
From ITree Require Import Core.ITreeDefinition Eq.Eqit Eq.Shallow Props.Leaf
  Props.Infinite.

(** Inversions of one step of [any_infinite], without dependent
    elimination axioms. *)

Lemma any_infiniteF_ret_inv {E X} (P : itree E X -> Prop) (x : X) :
  ~ any_infiniteF P (RetF x).
Proof.
  intro H.
  exact (match H in any_infiniteF _ t
               return match t with RetF _ => False | _ => True end with
         | DivTau _ _ _ => I
         | DivVis _ _ _ _ _ => I
         end).
Qed.

Lemma any_infiniteF_tau_inv {E X} (P : itree E X -> Prop) (u : itree E X) :
  any_infiniteF P (TauF u) -> P u.
Proof.
  intro H.
  exact (match H in any_infiniteF _ t
               return match t with TauF u' => P u' | _ => True end with
         | DivTau _ _ Hu => Hu
         | DivVis _ _ _ _ _ => I
         end).
Qed.

Lemma any_infiniteF_vis_inv {E X Y} (P : itree E X -> Prop) (e : E Y)
  (k : Y -> itree E X) :
  any_infiniteF P (VisF e k) -> exists y, P (k y).
Proof.
  intro H.
  exact (match H in any_infiniteF _ t
               return match t with VisF _ k' => exists y, P (k' y) | _ => True end with
         | DivTau _ _ _ => I
         | DivVis _ _ _ a Ha => ex_intro _ a Ha
         end).
Qed.

Lemma any_infinite_ret {E X} (x : X) : ~ @any_infinite E X (Ret x).
Proof. intro H. punfold H. exact (any_infiniteF_ret_inv _ _ H). Qed.

(** A tree with no infinite path has a leaf: every event has an answer,
    so a tree with no leaf can be followed forever. *)
Lemma leaf_or_infinite {E A} (answer : forall X (e : E X), inhabited X)
  (t : itree E A) :
  (exists a, Leaf a t) \/ any_infinite t.
Proof.
  destruct (classic (exists a, Leaf a t)) as [H | H]; [ left; exact H | right ].
  revert t H. pcofix CIH. intros t H. pfold. red.
  destruct (observe t) as [a | u | Y e k] eqn:Ht.
  - exfalso. apply H. exists a. econstructor 1. exact Ht.
  - constructor. right. apply CIH. intros [a Ha]. apply H.
    exists a. econstructor 2; [ exact Ht | exact Ha ].
  - destruct (answer Y e) as [y0].
    apply (DivVis _ k e y0). right. apply CIH. intros [a Ha]. apply H.
    exists a. econstructor 3; [ exact Ht | exact Ha ].
Qed.

(** Infinite paths of a [bind]: an infinite path of the first tree, or a
    leaf of it followed by an infinite path of the continuation. *)

Lemma any_infinite_bind_l {E A B} (t : itree E A) (k : A -> itree E B) :
  any_infinite t -> any_infinite (ITree.bind t k).
Proof.
  revert t. pcofix CIH. intros t Ht. punfold Ht. red in Ht. pfold. red.
  rewrite observe_bind.
  destruct (observe t) as [a | u | Y e h].
  - destruct (any_infiniteF_ret_inv _ _ Ht).
  - cbn. constructor. right. apply CIH.
    pose proof (any_infiniteF_tau_inv _ _ Ht) as Hu. pclearbot. exact Hu.
  - cbn. destruct (any_infiniteF_vis_inv _ _ _ Ht) as [y Hy].
    apply (DivVis _ _ e y). right. apply CIH. pclearbot. exact Hy.
Qed.

(** The dependent elimination axiom that [any_infinite_bind_leaf] reports
    is derivable from propositional extensionality: that gives proof
    irrelevance, so a proof [h : p = p] equals [eq_refl], and
    [eq_rect p Q x p eq_refl] reduces to [x].  Recorded here so that the
    axiom [Print Assumptions] attributes to the lemma below is known to add
    no strength beyond the axioms the development already assumes. *)

Lemma eq_rect_eq_from_propext :
  forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h.
Proof.
  assert (pe : prop_extensionality)
    by (intros A B H; apply propositional_extensionality; exact H).
  pose proof (ext_prop_dep_proof_irrel_cic pe) as pi.
  intros U p Q x h. rewrite (pi _ h eq_refl). reflexivity.
Qed.

Lemma any_infinite_bind_leaf {E A B} (t : itree E A) (k : A -> itree E B) (a : A) :
  Leaf a t -> any_infinite (k a) -> any_infinite (ITree.bind t k).
Proof.
  intros Ha Hk. induction Ha as [t Ht | t u Ht _ IH | Y e t h y Ht _ IH].
  - rewrite (itree_eta t), Ht, Eqit.bind_ret_l. exact Hk.
  - rewrite (itree_eta t), Ht, Eqit.bind_tau, Eqit.tau_eutt. exact IH.
  - rewrite (itree_eta t), Ht, Eqit.bind_vis.
    pfold. red. cbn. apply (DivVis _ _ e y). left. exact IH.
Qed.

Lemma any_infinite_bind_inv {E A B} (t : itree E A) (k : A -> itree E B) :
  any_infinite (ITree.bind t k) ->
  any_infinite t \/ exists a, Leaf a t /\ any_infinite (k a).
Proof.
  intro H.
  destruct (classic (exists a, Leaf a t /\ any_infinite (k a))) as [Hl | Hn];
    [ right; exact Hl | left ].
  revert t H Hn. pcofix CIH. intros t H Hn. pfold. red.
  punfold H. red in H. rewrite observe_bind in H.
  destruct (observe t) as [a | u | Y e h] eqn:Ht.
  - exfalso. apply Hn. exists a. split; [ econstructor 1; exact Ht |].
    pfold. exact H.
  - cbn in H. apply any_infiniteF_tau_inv in H. pclearbot.
    constructor. right. apply CIH; [ exact H |].
    intros [a [Ha Hk]]. apply Hn. exists a.
    split; [ econstructor 2; [ exact Ht | exact Ha ] | exact Hk ].
  - cbn in H. destruct (any_infiniteF_vis_inv _ _ _ H) as [y Hy]. pclearbot.
    apply (DivVis _ _ e y). right. apply CIH; [ exact Hy |].
    intros [a [Ha Hk]]. apply Hn. exists a.
    split; [ econstructor 3; [ exact Ht | exact Ha ] | exact Hk ].
Qed.
