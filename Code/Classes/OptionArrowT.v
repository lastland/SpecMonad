(** * Option arrow transformer for [SPArr].

    [optionArrT arr A B := arr A (option B)] lifts an arrow with
    option-aware composition (failure propagation).

    Instances are defined specifically for [SPArr] (relations). *)

From Coq Require Import
  FunctionalExtensionality PropExtensionality
  Morphisms RelationClasses.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow.

(* ================================================================= *)
(** ** Definition                                                      *)
(* ================================================================= *)

Definition optionArrT (arr : Type -> Type -> Type) A B := arr A (option B).

(* ================================================================= *)
(** ** Instances for [optionArrT SPArr]                                *)
(* ================================================================= *)

Section OptionSPArrInstances.

  Definition optionSPArr := optionArrT SPArr.

  Lemma optionSPArr_eq {A B} (f g : optionSPArr A B) :
    (forall a ob, f a ob <-> g a ob) -> f = g.
  Proof.
    intros H. extensionality a. extensionality ob.
    apply propositional_extensionality. apply H.
  Qed.

  #[global]
  Instance ArrowEq_optionSPArr : ArrowEq optionSPArr := {
    arrow_eq := fun A B => @eq (optionSPArr A B)
  }.

  #[global]
  Instance Arrow_optionSPArr : Arrow optionSPArr := {
    arr_pure := fun A B f a ob =>
      match ob with Some b => f a = b | None => False end ;
    arr_comp := fun A B C f g a oc =>
      match oc with
      | Some c => exists b, f a (Some b) /\ g b (Some c)
      | None => f a None \/ exists b, f a (Some b) /\ g b None
      end ;
    arr_first := fun A B C f p oq =>
      let '(a, c) := p in
      match oq with
      | Some (b, c') => f a (Some b) /\ c = c'
      | None => f a None
      end
  }.

  #[global]
  Instance ArrowChoice_optionSPArr : ArrowChoice optionSPArr := {
    arr_left := fun A B C f x oy =>
      match x, oy with
      | inl a, Some (inl b) => f a (Some b)
      | inl a, None => f a None
      | inr c, Some (inr c') => c = c'
      | _, _ => False
      end
  }.

  #[global]
  Instance ArrowApply_optionSPArr : ArrowApply optionSPArr := {
    arr_app := fun A B p ob =>
      let '(f, a) := p in f a ob
  }.

  #[global]
  Instance ArrowLoop_optionSPArr : ArrowLoop optionSPArr := {
    arr_loop := fun A B C f a ob =>
      match ob with
      | Some b => exists c, f (a, c) (Some (b, c))
      | None => exists c, f (a, c) None
      end
  }.

  (* -------------------------------------------------------------- *)
  (** *** Helper tactics                                               *)
  (* -------------------------------------------------------------- *)

  Local Ltac unfold_optionSPArr :=
    unfold optionSPArr, optionArrT, arr_id, arr_second,
           arr_comp, arr_first, arr_pure, arr_loop,
           arr_left, arr_app, Arrow_optionSPArr,
           swap; simpl.

  Local Ltac destruct_options :=
    repeat match goal with
    | [ob : option _ |- _] => destruct ob
    | [p : _ * _ |- _] => destruct p
    | [s : _ + _ |- _] => destruct s
    end; simpl in *.

  (* -------------------------------------------------------------- *)
  (** *** ArrowLaws                                                    *)
  (* -------------------------------------------------------------- *)

  #[global]
  Instance ArrowLaws_optionSPArr : ArrowLaws optionSPArr.
  Proof.
    constructor; intros.
    - (* comp_id_l *)
      apply optionSPArr_eq; intros a [c|]; unfold_optionSPArr.
      + split; [intros [b [Heq Hf]]; subst; exact Hf |
                intros Hf; exists a; eauto].
      + split; [intros [Habs | [b [Heq Hf]]]; [destruct Habs | subst; exact Hf] |
                intros Hf; right; exists a; eauto].
    - (* comp_id_r *)
      apply optionSPArr_eq; intros a [c|]; unfold_optionSPArr.
      + split; [intros [b [Hf Heq]]; subst; exact Hf |
                intros Hf; exists c; eauto].
      + split; [intros [H | [b [Hf Habs]]]; [exact H | destruct Habs] |
                intros Hf; left; exact Hf].
    - (* comp_assoc *)
      apply optionSPArr_eq; intros a [d|]; unfold_optionSPArr.
      + split.
        * intros [c [[b [Hf Hg]] Hh]]. exists b; split; [exact Hf|]. exists c; eauto.
        * intros [b [Hf [c [Hg Hh]]]]. exists c; split; [exists b|]; eauto.
      + split.
        * intros [[Hf | [b [Hf Hg]]] | [c [[b [Hf Hg]] Hh]]].
          -- left. exact Hf.
          -- right. exists b; split; [exact Hf | left; exact Hg].
          -- right. exists b; split; [exact Hf | right; exists c; eauto].
        * intros [Hf | [b [Hf [Hg | [c [Hg Hh]]]]]].
          -- left. left. exact Hf.
          -- left. right. exists b; eauto.
          -- right. exists c; split; [exists b; eauto | exact Hh].
    - (* pure_comp *)
      apply optionSPArr_eq; intros a [c|]; unfold_optionSPArr.
      + split; [intros [b [Heq1 Heq2]]; subst; reflexivity |
                intros Heq; exists (f a); eauto].
      + split; intros H; [destruct H as [|[? [_ ?]]] | destruct H]; contradiction.
    - (* first_pure *)
      apply optionSPArr_eq; intros [a c] [[b c']|]; unfold_optionSPArr.
      + split; [intros [Heq Hc]; subst; reflexivity |
                intro H; inversion H; eauto].
      + tauto.
    - (* first_comp *)
      apply optionSPArr_eq; intros [a d] [[c d']|]; unfold_optionSPArr.
      + split.
        * intros [[b [Hf Hg]] Heq]; subst d'.
          exists (b, d); simpl; eauto.
        * intros [[b0 d0] H]; simpl in H.
          destruct H as [[Hf Heq1] [Hg Heq2]]; subst.
          split; [exists b0; eauto | reflexivity].
      + split.
        * intros [Hf | [b [Hf Hg]]].
          -- left. exact Hf.
          -- right. exists (b, d); simpl; eauto.
        * intros [Hf | [[b d0] H]]; simpl in *.
          -- left. exact Hf.
          -- destruct H as [[Hf Heq] Hg]; subst.
             right. exists b; eauto.
    - (* first_fst *)
      apply optionSPArr_eq; intros [a c] [b|]; unfold_optionSPArr.
      + split.
        * intros [[b0 c0] H]; simpl in H.
          destruct H as [[Hf Hc] Heq]; subst. exists a; eauto.
        * intros [a0 [Heq Hf]]; subst.
          exists (b, c); simpl; eauto.
      + split.
        * intros [Hf | [[b0 c0] H]]; simpl in *.
          -- right. exists a; eauto.
          -- destruct H as [_ Habs]; destruct Habs.
        * intros [Habs | [a0 [Heq Hf]]].
          -- destruct Habs.
          -- subst. left. exact Hf.
    - (* first_assoc *)
      apply optionSPArr_eq; intros [[a c] d] [ob|]; unfold_optionSPArr.
      + destruct ob as [b [c' d']]. split.
        * intros [[[b0 c0] d0] H]; simpl in H.
          destruct H as [[[Hf Hc] Hd] Heq].
          subst c0 d0. inversion Heq; subst.
          exists (a, (c', d')); simpl; split; [reflexivity|].
          split; [exact Hf | reflexivity].
        * intros [[a0 [c0 d0]] H]; simpl in H.
          destruct H as [Hassoc Hrest].
          inversion Hassoc; subst.
          destruct Hrest as [Hf Heq_cd].
          inversion Heq_cd; subst.
          eexists (_, _, _); simpl; eauto.
      + split.
        * intros [Hf | [[[b0 c0] d0] H]]; simpl in *.
          -- right. exists (a, (c, d)); simpl; eauto.
          -- destruct H as [_ Habs]; destruct Habs.
        * intros [Habs | [[a0 [c0 d0]] H]]; [destruct Habs|].
          simpl in H. destruct H as [Hassoc Hf].
          inversion Hassoc; subst.
          left. exact Hf.
    - (* comp_proper *)
      unfold Proper, respectful, arrow_eq, ArrowEq_optionSPArr;
      intros; subst; reflexivity.
    - (* first_proper *)
      unfold Proper, respectful, arrow_eq, ArrowEq_optionSPArr;
      intros; subst; reflexivity.
  Qed.

End OptionSPArrInstances.
