From Coq Require Import RelationClasses.
From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.


Section PP2SP.

  Variable A : Type.

  Definition SPost := forall (pre : Prop),
      A -> {p : Prop | p -> pre}.

  Definition mSPost :=
    { w : SPost | forall p q r,
        (p -> q) -> proj1_sig (w p r) -> proj1_sig (w q r)  }.

  Definition ordSPost (sp1 sp2:mSPost) : Prop := 
    forall pre r,
      proj1_sig (proj1_sig sp2 pre r) -> proj1_sig (proj1_sig sp1 pre r).

  Definition PrePost := prod Prop (A -> Prop).

  Definition ordPrePost (pp1 pp2:PrePost) : Prop :=
    (fst pp2 -> fst pp1) /\ (forall r, snd pp1 r -> snd pp2 r).

  Program Definition pp2sp (pp:PrePost) : mSPost :=
    fun q r =>
      q /\ (fst pp -> snd pp r).

  Definition sp2pp (sp:mSPost) : PrePost :=
    let post := fun x => forall (pre : Prop), proj1_sig (proj1_sig sp pre x) in
    let pre := exists pre, pre /\ (forall x, post x -> proj1_sig (proj1_sig sp pre x)) in
    (pre, post).

  Lemma loop1 (pp:PrePost):
    ordPrePost (sp2pp (pp2sp pp)) pp.
  Proof.    
    destruct pp as [P Q].
    unfold sp2pp. unfold pp2sp. unfold ordPrePost. simpl.
    split.
    + intros Hpre. exists P. split.
      ++ intros. apply Hpre. 
      ++ sfirstorder.
    + intros.
      specialize H with P.
      apply H.
      sfirstorder. 
  Qed.

  Lemma loop2 (sp:mSPost) :
    ordSPost (pp2sp (sp2pp sp)) sp.
  Proof.
    split. 
    + destruct sp. sfirstorder.
    + intros.
      destruct H0 as [pre' [Hpre' H0]].
      simpl.
      destruct sp.
  Abort.

End PP2SP.