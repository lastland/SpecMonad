From Coq Require Import RelationClasses.
From Hammer Require Import Hammer Tactics.

Set Implicit Arguments.

(** We want to transform PrePost-conditions to 
    the Forward Predicate Transformer (SPost) so that
    the transformation:
    * satisfies the laws of Hoare logic:
        {P}c{Q1} /\ {P}c{Q2} <-> {P}c{Q1 /\ Q2}
        {P1}c{Q} /\ (P2 -> P1) -> {P2}c{Q}
        {P}c{Q1} /\ (Q1 -> Q2) -> {P}c{Q2}
    * creates a Galois connection?
*)

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
    (** !!!! Contravariant *)  

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
    cbv.
    split.
    + exists P. split; sfirstorder.
    + intros r Hpre.
      specialize Hpre with P.
      apply Hpre.
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
      simpl in *.
  Abort.

  Theorem strengthen_pre (P1 P2:Prop) (Q:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P1, Q)) pre r) -> 
      (P2 -> P1) ->
      proj1_sig (proj1_sig (pp2sp (P2, Q)) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem weaken_post (P:Prop) (Q1 Q2:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P, Q1)) pre r) -> 
      (forall r, Q1 r -> Q2 r) ->
      proj1_sig (proj1_sig (pp2sp (P, Q2)) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_elim P Q1 Q2 :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P, (fun r => Q1 r /\ Q2 r))) pre r) ->
      proj1_sig (proj1_sig (pp2sp (P, Q1)) pre r) /\
      proj1_sig (proj1_sig (pp2sp (P, Q2)) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

  Theorem post_conj_intro (P:Prop) (Q1 Q2:A -> Prop) :
    forall pre r,
      proj1_sig (proj1_sig (pp2sp (P, Q1)) pre r) -> 
      proj1_sig (proj1_sig (pp2sp (P, Q2)) pre r) -> 
      proj1_sig (proj1_sig (pp2sp (P, (fun r => Q1 r /\ Q2 r))) pre r).
  Proof.
    cbv.
    sfirstorder.
  Qed.

End PP2SP.