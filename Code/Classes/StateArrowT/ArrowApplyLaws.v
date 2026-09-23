From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.StateArrowT Require Import Core.

(* ================================================================= *)
(** ** ArrowApplyLaws for [stateArrT]                                 *)
(* ================================================================= *)

Section StateArrowTApplyLaws.

  Variable S : Type.
  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HAAL : @ArrowApplyLaws arr HA HAA HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl   := (@comp_id_l arr HA HE HL).
  Local Notation cidr   := (@comp_id_r arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation alaw   := (@app_law arr HA HAA HE HAAL).

  (** Base-arrow shorthands: every goal below is an equality of BASE
      arrows once the [stateArrT] operations are unfolded. *)
  Local Notation "f >>> g" := (@arr_comp arr HA _ _ _ f g)
    (at level 41, right associativity).
  Local Notation pur := (@arr_pure arr HA _ _).
  Local Notation app0 := (@arr_app arr HA HAA _ _).
  Local Notation "f == g" := (@arrow_eq arr HE _ _ f g) (at level 70).

  Local Lemma pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) -> pur f == pur g.
  Proof. apply arr_pure_ext. Qed.

  (** *** The two shapes a [stateArrT] law presents                    *)

  (** [T.pure (fun x => (u x, t x)) >>> T.app]: one [app] after one pure. *)
  Local Lemma app_state_pure {X A B}
    (u : X -> stateArrT S arr A B) (t : X -> A) :
    pur (fun '(x, s) => ((u x, t x), s))
      >>> (pur (fun '((f, a), s) => (f, (a, s))) >>> app0)
    == pur (fun p : X * S => (u (fst p), (t (fst p), snd p))) >>> app0.
  Proof.
    etransitivity; [ symmetry; apply cassoc |].
    apply cprop; [| reflexivity ].
    etransitivity; [ apply pcomp |].
    apply pure_ext. intros [x s]. reflexivity.
  Qed.

  (** [T.first (T.pure phi) >>> T.app]: the extra component supplies the
      argument, so again one [app] after one pure. *)
  Local Lemma app_state_first {X A B} (phi : X -> stateArrT S arr A B) :
    (pur (@state_shuffle_in S X A)
       >>> (@arr_first arr HA _ _ _ (pur (fun '(x, s) => (phi x, s)))
              >>> pur (@state_shuffle_out S (stateArrT S arr A B) A)))
      >>> (pur (fun '((f, a), s) => (f, (a, s))) >>> app0)
    == pur (fun p : (X * A) * S => (phi (fst (fst p)), (snd (fst p), snd p)))
         >>> app0.
  Proof.
    etransitivity.
    { apply cprop; [| reflexivity ].
      apply cprop; [ reflexivity |].
      apply cprop; [ apply first_pure | reflexivity ]. }
    (* all four leading arrows are pure: fuse them *)
    etransitivity.
    { apply cprop; [| reflexivity ].
      etransitivity; [ apply cprop; [ reflexivity | apply pcomp ] |].
      apply pcomp. }
    etransitivity; [ symmetry; apply cassoc |].
    apply cprop; [| reflexivity ].
    etransitivity; [ apply pcomp |].
    apply pure_ext. intros [[x a] s]. reflexivity.
  Qed.

  (** [T.second g] commutes with the [app] shuffle. *)
  Local Lemma second_state_shuffle {X A B} (g : stateArrT S arr A B) :
    (pur (fun '(p, s) => (@swap X A p, s))
       >>> ((pur (@state_shuffle_in S A X)
               >>> (@arr_first arr HA _ _ _ g >>> pur (@state_shuffle_out S B X)))
              >>> pur (fun '(p, s) => (@swap B X p, s))))
      >>> pur (fun '((f, a), s) => (f, (a, s)))
    == pur (fun '((f, a), s) => (f, (a, s))) >>> @arr_second arr HA _ _ _ g.
  Proof.
    unfold arr_second.
    rewrite !cassoc, !pcomp.      (* fuse the pures after [first g] *)
    rewrite <- !cassoc, !pcomp.   (* fuse the pures before it *)
    apply cprop; [ apply cprop |].
    - apply pure_ext. intros [[x a] s]. reflexivity.
    - reflexivity.
    - apply pure_ext. intros [[b s] x]. reflexivity.
  Qed.

  #[global]
  Instance ArrowApplyLaws_stateArrT : ArrowApplyLaws (stateArrT S arr).
  Proof.
    constructor; intros.
    all: unfold arr_id, arr_comp, arr_pure, arr_first, arr_app, arr_second,
                Arrow_stateArrT, ArrowApply_stateArrT,
                arrow_eq, ArrowEq_stateArrT;
         fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
              (@arr_app arr HA HAA) (@arrow_eq arr HE).
    - (* app_law *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply pure_ext. intros (a0, s0); reflexivity. }
      apply alaw.
    - (* app_pair *)
      etransitivity; [ apply app_state_first |].
      (* the arrow built is [pur (fun '(v,s) => ((a,v),s))]: split off
         the reassociation and use the base [app_pair_at]. *)
      etransitivity.
      { apply app_ext_at with
          (v := fun p : (A * B) * S =>
                  arr_comp (pur (fun q : B * S => (fst (fst p), q)))
                           (pur (@unassoc_prod A B S))).
        intro p. symmetry.
        etransitivity; [ apply pcomp |].
        apply pure_ext. intros [v s]. reflexivity. }
      etransitivity; [ apply app_post_at |].
      etransitivity.
      { apply cprop; [| reflexivity ]. apply app_pair_at. }
      etransitivity; [ apply pcomp |].
      symmetry. apply pure_ext. intros [[a b] s]. reflexivity.
    - (* app_post *)
      etransitivity; [ apply app_state_first |].
      etransitivity;
        [ apply (@app_post_at arr HA HAA HE HL HAAL _ _ _ _
                   (fun p : (stateArrT S arr A B * A) * S => fst (fst p))
                   (fun p : (stateArrT S arr A B * A) * S => (snd (fst p), snd p))
                   h) |].
      apply cprop; [| reflexivity ].
      apply cprop; [| reflexivity ].
      apply pure_ext. intros [[f a] s]. reflexivity.
    - (* app_ext *)
      etransitivity; [ apply app_state_pure |].
      etransitivity.
      { apply (@app_ext_at arr HA HAA HE HAAL (X * S)%type (A * S)%type
                 (B * S)%type (fun p => u (fst p)) (fun p => v (fst p))
                 (fun p : X * S => (t (fst p), snd p))).
        intro p. apply H. }
      symmetry. apply app_state_pure.
  Qed.

End StateArrowTApplyLaws.
