(** * Public regressions for the arrow-derived monad. *)

From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow ArrowMonad.

(** Selecting the other position satisfies fixed-arrow application, but
    breaks the derived monad's right identity.  The full application
    contract must reject this implementation. *)
Module WrongIndex.
  Definition t (A B : Type) := (bool -> A) -> bool -> B.

  Definition arrow : Arrow t := {|
    arr_pure := fun A B f xs i => f (xs i);
    arr_comp := fun A B C f g xs => g (f xs);
    arr_first := fun A B C f xs i =>
      (f (fun j => fst (xs j)) i, snd (xs i))
  |}.

  Definition equality : ArrowEq t := {|
    arrow_eq := fun A B => @eq (t A B);
    arrow_eq_equiv := fun A B => eq_equivalence
  |}.

  Lemma arrow_laws : @ArrowLaws t arrow equality.
  Proof.
    constructor; cbn.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros A B C f. extensionality xs. extensionality i.
      destruct (xs i); reflexivity.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros A B C D f. extensionality xs. extensionality i.
      assert (E : (fun j => fst (fst (xs j))) =
                  (fun j => fst (assoc_prod (xs j)))).
      { extensionality j. destruct (xs j) as [[a c] d]; reflexivity. }
      rewrite E. destruct (xs i) as [[a c] d]; reflexivity.
    - intros X Y Z f g E h k F; subst; reflexivity.
    - intros X Y Z f g E; subst; reflexivity.
    - intros A B C D f g. extensionality xs. extensionality i.
      assert (E : (fun j => fst (xs j)) =
                  (fun j => fst (let '(a, c) := xs j in (a, g c)))).
      { extensionality j. destruct (xs j); reflexivity. }
      rewrite E. destruct (xs i); reflexivity.
  Qed.

  Definition application : @ArrowApply t arrow :=
    @Build_ArrowApply t arrow
      (fun (A B : Type) (p : bool -> t A B * A) i =>
        fst (p (negb i)) (fun j => snd (p j)) i).

  Lemma fixed_application {A B} (f : t A B) :
    @arrow_eq t equality A B
      (@arr_comp t arrow _ _ _
        (@arr_pure t arrow _ _ (fun a => (f, a)))
        (@arr_app t arrow application A B)) f.
  Proof. reflexivity. Qed.

  Definition position : t unit bool := fun _ i => i.

  Lemma right_identity_fails :
    @bind_arrow t arrow application unit bool bool position
      (@ret_arrow t arrow unit bool) <> position.
  Proof.
    intro H.
    pose proof (f_equal (fun f => f (fun _ => tt) false) H) as E.
    discriminate E.
  Qed.

  Lemma application_contract_rejects_wrong_index :
    ~ @ArrowApplyLaws t arrow application equality.
  Proof.
    intro H.
    pose proof (@app_unit t arrow application equality H bool unit) as E.
    apply (f_equal (fun f => fst (f (fun i => (i, tt)) false))) in E.
    discriminate E.
  Qed.
End WrongIndex.

(** This must certify the exact arrow-derived operations, for every
    fixed input type, using the arrow's own equivalence relation. *)
Section GenericResolution.
  Context {arr : Type -> Type -> Type}
    {HA : Arrow arr} {HAA : @ArrowApply arr HA} {HE : ArrowEq arr}
    {HL : @ArrowLaws arr HA HE} {HAL : @ArrowApplyLaws arr HA HAA HE}.

  Definition generic_monad_laws (I : Type) :
    @MonadLawsE (arr I) (@Eq1_Arrow arr HE I)
      (@Monad_Arrow arr HA HAA I) := _.

  Definition generic_equality_equivalence (I : Type) :
    @Eq1Equivalence (arr I) (@Monad_Arrow arr HA HAA I)
      (@Eq1_Arrow arr HE I) := _.
End GenericResolution.
