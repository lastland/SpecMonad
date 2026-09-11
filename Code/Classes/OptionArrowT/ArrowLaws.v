From Coq Require Import FunctionalExtensionality PropExtensionality Morphisms RelationClasses.
From Hammer Require Import Tactics.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.OptionArrowT Require Import Core.

(* ================================================================= *)
(** ** Generic [ArrowLaws] for [optionArrT]                           *)
(* ================================================================= *)

Section GenericOptionArrTLaws.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HCL : @ArrowChoiceLaws arr HA HC HE}.

  (* Use explicit law applications to avoid typeclass resolution picking
     the ArrowLaws_optionArrT instance being defined. *)
  Local Notation cassoc   := (@comp_assoc arr HA HE HL).
  Local Notation cidl     := (@comp_id_l arr HA HE HL).
  Local Notation cidr     := (@comp_id_r arr HA HE HL).
  Local Notation pcomp    := (@pure_comp arr HA HE HL).
  Local Notation cprop    := (@comp_proper arr HA HE HL).
  Local Notation fprop    := (@first_proper arr HA HE HL).
  Local Notation fpure    := (@first_pure arr HA HE HL).
  Local Notation fcomp    := (@first_comp arr HA HE HL).
  Local Notation ffst     := (@first_fst arr HA HE HL).
  Local Notation fassoc   := (@first_assoc arr HA HE HL).
  Local Notation fnat     := (@first_natural arr HA HE HL).
  Local Notation lpure    := (@left_pure arr HA HC HE HCL).
  Local Notation lcomp    := (@left_comp arr HA HC HE HCL).
  Local Notation linl     := (@left_inl arr HA HC HE HCL).
  Local Notation lassoc   := (@left_assoc arr HA HC HE HCL).
  Local Notation linr     := (@left_inr arr HA HC HE HCL).
  Local Notation lnat     := (@left_natural arr HA HC HE HCL).
  Local Notation lprop    := (@left_proper arr HA HC HE HCL).

  Local Lemma arr_pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro H. replace f with g by (extensionality x; symmetry; apply H). reflexivity.
  Qed.

  Create HintDb opt_ops.
  #[local] Hint Unfold arr_id arr_comp arr_pure arr_first Arrow_optionArrT
    arrow_eq arrow_eq_equiv ArrowEq_optionArrT : opt_ops.

  Local Ltac opt_unfold :=
    autounfold with opt_ops;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_left arr HA HC) (@arrow_eq arr HE) (@arrow_eq_equiv arr HE).

  (** Composition with a pure arrow reduces to ordinary base composition. *)
  Lemma optionArrT_comp_pure_l {A B C} (u : A -> B)
    (f : optionArrT arr B C) :
    @arrow_eq arr HE _ _
      (@arr_comp _ (@Arrow_optionArrT arr HA HC) _ _ _
        (@arr_pure _ (@Arrow_optionArrT arr HA HC) _ _ u) f)
      (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ u) f).
  Proof.
    opt_unfold.
    assert (Hhead : @arrow_eq arr HE _ _
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (fun a => Some (u a)))
        (@arr_pure arr HA _ _ (@to_sum B)))
      (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ u)
       (@arr_pure arr HA _ _ (@inl B unit)))).
    { etransitivity. { apply pcomp. }
      symmetry. etransitivity. { apply pcomp. }
      reflexivity. }
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. exact Hhead. }
    etransitivity. { apply cassoc. }
    apply cprop. 1: reflexivity.
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. symmetry. apply linl. }
    etransitivity. { apply cassoc. }
    etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
    apply cidr.
  Qed.

  Lemma optionArrT_comp_pure_r {A B C} (f : optionArrT arr A B)
    (u : B -> C) :
    @arrow_eq arr HE _ _
      (@arr_comp _ (@Arrow_optionArrT arr HA HC) _ _ _ f
        (@arr_pure _ (@Arrow_optionArrT arr HA HC) _ _ u))
      (@arr_comp arr HA _ _ _ f
        (@arr_pure arr HA _ _ (option_map u))).
  Proof.
    opt_unfold. apply cprop. 1: reflexivity.
    etransitivity.
    { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity. apply lpure. }
    etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
    etransitivity. { apply pcomp. }
    apply arr_pure_ext. intros [b|]; reflexivity.
  Qed.

  #[global]
  Instance ArrowLaws_optionArrT : ArrowLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros.
    - (* comp_id_l: [Some] >>> [ts] >>> L f >>> [c] = f *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
      (* [inl] >>> L f >>> [c] — now use left_inl to get f >>> [inl] >>> [c] *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity. symmetry. apply linl. }
      (* f >>> [inl] >>> [c] *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
      apply cidr.
    - (* comp_id_r: f >>> [ts] >>> L [Some] >>> [c] = f *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply lpure. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
      (* f >>> [collapse . sum_bimap Some id . to_sum] = f *)
      assert (Hid : @arrow_eq arr HE (option B) (option B)
        (@arr_pure arr HA _ _
          (fun x : option B =>
           collapse (sum_bimap (fun a : B => Some a) (fun c : unit => c) (to_sum x))))
        (@arr_pure arr HA _ _ (fun x => x))).
      { apply arr_pure_ext. intros [?|]; reflexivity. }
      etransitivity. { apply cprop. 1: reflexivity. exact Hid. }
      apply cidr.
    - (* comp_assoc *)
      (* LHS (unfolded): (f >>> [ts] >>> L g >>> [c]) >>> [ts] >>> L h >>> [c]
         RHS (unfolded): f >>> [ts] >>> L (g >>> [ts] >>> L h >>> [c]) >>> [c]

         Strategy:
         1. Rewrite [ts.c] = L[ts] >>> [assoc] >>> [sbm id (const tt)] (pure fun eq)
         2. Use lnat: [sbm id (const tt)] >>> Lh = L_{uu}h >>> [sbm id (const tt)]
         3. Use lassoc: L(Lh) >>> [assoc] = [assoc] >>> L_{uu}h
         4. [assoc] >>> [sbm id (const tt)] >>> [c] = L[c] >>> [c] (pure fun eq)
         5. Collapse with lcomp *)
      (* Core helper: [ts.c] >>> Lh >>> [c] = L([ts] >>> Lh >>> [c]) >>> [c]

         Chain (all fully right-associated):
         E0: [ts.c] >>> Lh >>> [c]
         E1: [sbm ts id] >>> [assoc] >>> [sbm id ctt] >>> Lh >>> [c]
         E2: [sbm ts id] >>> [assoc] >>> L_{uu}h >>> [sbm id ctt] >>> [c]
         E3: [sbm ts id] >>> L(Lh) >>> [assoc] >>> [sbm id ctt] >>> [c]
         E4: [sbm ts id] >>> L(Lh) >>> [sbm c id] >>> [c]
         E5: L[ts] >>> L(Lh) >>> L[c] >>> [c]
         E6: L([ts] >>> Lh >>> [c]) >>> [c]

         E0=E1: pure function equality (Hdecomp + cassoc)
         E1=E2: lnat (naturality)
         E2=E3: lassoc
         E3=E4: pure function equality (Htail)
         E4=E5: lpure (2x)
         E5=E6: lcomp (2x) *)

      (* We express each Ei as a single term and assert the chain.
         To avoid deep cprop navigation, we use cassoc to flatten,
         then apply one law at the boundary. *)

      (* All five-component right-associated compositions *)
      (* No local notations needed - work with explicit terms *)

      assert (Hcore : @arrow_eq arr HE (option C + unit) (option D)
        (@arr_comp arr HA _ _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (fun x : option C + unit => to_sum (collapse x)))
            (@arr_left arr HA HC _ _ _ h))
          (@arr_pure arr HA _ _ (@collapse D)))
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ _
            (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ (@to_sum C))
              (@arr_comp arr HA _ _ _ (@arr_left arr HA HC _ _ _ h)
                (@arr_pure arr HA _ _ (@collapse D)))))
          (@arr_pure arr HA _ _ (@collapse D)))).
      { (* Prove: ([ts.c] >>> Lh) >>> [c] = L([ts] >>> Lh >>> [c]) >>> [c]

           We go LHS -> RHS via the chain:
           E0: [ts.c] >>> Lh >>> [c]
           E1: [sbm ts id] >>> [assoc] >>> [sbm id ctt] >>> Lh >>> [c]
           E2: [sbm ts id] >>> [assoc] >>> L'h >>> [sbm id ctt] >>> [c]
           E3: [sbm ts id] >>> LLh >>> [assoc] >>> [sbm id ctt] >>> [c]
           E4: [sbm ts id] >>> LLh >>> [sbm c id] >>> [c]
           E5: L[ts] >>> LLh >>> L[c] >>> [c]
           E6: L([ts] >>> Lh >>> [c]) >>> [c]  *)

        set (Lh := @arr_left arr HA HC C (option D) unit h).
        set (LLh := @arr_left arr HA HC (C+unit) (option D+unit) unit Lh).
        set (L'h := @arr_left arr HA HC C (option D) (unit+unit) h).

        (* Assert each step as a standalone equality *)
        (* E01: [ts.c] = [sbm ts id] >>> [assoc] >>> [sbm id ctt] *)
        assert (E01 : @arrow_eq arr HE _ _
          (@arr_pure arr HA _ _ (fun x : option C + unit => to_sum (collapse x)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (sum_bimap (@to_sum C) (fun u : unit => u)))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (@assoc_sum C unit unit))
              (@arr_pure arr HA _ _ (sum_bimap (fun c0 : C => c0) (fun _ : unit + unit => tt)))))).
        { symmetry.
          etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
          etransitivity. { apply pcomp. }
          apply arr_pure_ext. intros [[c0|]|[]]; reflexivity. }

        (* E12: [sbm id ctt] >>> Lh = L'h >>> [sbm id ctt]   (from lnat symmetry) *)
        assert (E12 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (sum_bimap (fun c0 : C => c0) (fun _ : unit + unit => tt)))
            Lh)
          (@arr_comp arr HA _ _ _ L'h
            (@arr_pure arr HA _ _ (sum_bimap (fun d : option D => d) (fun _ : unit + unit => tt))))).
        { symmetry. apply lnat. }

        (* E23: [assoc] >>> L'h = LLh >>> [assoc]   (from lassoc symmetry) *)
        assert (E23 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@assoc_sum C unit unit))
            L'h)
          (@arr_comp arr HA _ _ _ LLh
            (@arr_pure arr HA _ _ (@assoc_sum (option D) unit unit)))).
        { symmetry. apply lassoc. }

        (* E34: [assoc] >>> [sbm id ctt] >>> [c] = [sbm c id] >>> [c] *)
        assert (E34 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@assoc_sum (option D) unit unit))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (sum_bimap (fun d : option D => d) (fun _ : unit + unit => tt)))
              (@arr_pure arr HA _ _ (@collapse D))))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (sum_bimap (@collapse D) (fun u : unit => u)))
            (@arr_pure arr HA _ _ (@collapse D)))).
        { etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
          etransitivity. { apply pcomp. }
          symmetry. etransitivity. { apply pcomp. }
          apply arr_pure_ext. intros [[od|]|[]]; reflexivity. }

        (* E45a: [sbm ts id] = L[ts] *)
        assert (E45a : @arrow_eq arr HE _ _
          (@arr_pure arr HA _ _ (sum_bimap (@to_sum C) (fun u : unit => u)))
          (@arr_left arr HA HC (option C) (C + unit) unit
            (@arr_pure arr HA _ _ (@to_sum C)))).
        { symmetry. apply lpure. }

        (* E45b: [sbm c id] = L[c] *)
        assert (E45b : @arrow_eq arr HE _ _
          (@arr_pure arr HA _ _ (sum_bimap (@collapse D) (fun u : unit => u)))
          (@arr_left arr HA HC (option D + unit) (option D) unit
            (@arr_pure arr HA _ _ (@collapse D)))).
        { symmetry. apply lpure. }

        (* E56: L([ts] >>> Lh >>> [c]) = L[ts] >>> LLh >>> L[c] *)
        assert (E56 : @arrow_eq arr HE (option C + unit) (option D + unit)
          (@arr_left arr HA HC (option C) (option D) unit
            (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ (@to_sum C))
              (@arr_comp arr HA _ _ _ Lh
                (@arr_pure arr HA _ _ (@collapse D)))))
          (@arr_comp arr HA _ _ _
            (@arr_left arr HA HC (option C) (C + unit) unit
              (@arr_pure arr HA _ _ (@to_sum C)))
            (@arr_comp arr HA _ _ _ LLh
              (@arr_left arr HA HC (option D + unit) (option D) unit
                (@arr_pure arr HA _ _ (@collapse D)))))).
        { etransitivity. { apply lcomp. }
          apply cprop. 1: reflexivity. apply lcomp. }

        (* LHS -> E0 *)
        etransitivity. { apply cassoc. }

        (* E0 -> E1: [ts.c] >>> (Lh >>> [c]) -> [sbm ts id] >>> [assoc] >>> [sbm id ctt] >>> (Lh >>> [c]) *)
        etransitivity.
        { apply cprop. 2: reflexivity. exact E01. }
        (* ([sbm ts id] >>> ([assoc] >>> [sbm id ctt])) >>> (Lh >>> [c]) *)
        etransitivity. { apply cassoc. }
        (* [sbm ts id] >>> (([assoc] >>> [sbm id ctt]) >>> (Lh >>> [c])) *)
        etransitivity.
        { apply cprop. 1: reflexivity. apply cassoc. }
        (* [sbm ts id] >>> ([assoc] >>> ([sbm id ctt] >>> (Lh >>> [c]))) *)

        (* E1->E4: [assoc] >>> [sbm id ctt] >>> Lh >>> [c]
                 = LLh >>> [sbm c id] >>> [c]
           via E12 (lnat), E23 (lassoc), E34 (pure fuse) *)
        assert (E14 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@assoc_sum C unit unit))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (sum_bimap (fun c0 : C => c0) (fun _ : unit + unit => tt)))
              (@arr_comp arr HA _ _ _ Lh
                (@arr_pure arr HA _ _ (@collapse D)))))
          (@arr_comp arr HA _ _ _ LLh
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (sum_bimap (@collapse D) (fun u : unit => u)))
              (@arr_pure arr HA _ _ (@collapse D))))).
        { (* [assoc] >>> [sbm id ctt] >>> Lh >>> [c]
             -> [assoc] >>> L'h >>> [sbm id ctt] >>> [c]  (by E12)
             -> LLh >>> [assoc] >>> [sbm id ctt] >>> [c]  (by E23)
             -> LLh >>> [sbm c id] >>> [c]  (by E34) *)

          (* Step a: use E12 to swap [sbm id ctt] >>> Lh *)
          assert (Ha : @arrow_eq arr HE _ _
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (sum_bimap (fun c0 : C => c0) (fun _ : unit + unit => tt)))
              (@arr_comp arr HA _ _ _ Lh
                (@arr_pure arr HA _ _ (@collapse D))))
            (@arr_comp arr HA _ _ _ L'h
              (@arr_comp arr HA _ _ _
                (@arr_pure arr HA _ _ (sum_bimap (fun d : option D => d) (fun _ : unit + unit => tt)))
                (@arr_pure arr HA _ _ (@collapse D))))).
          { etransitivity.
            { etransitivity. { symmetry. apply (cassoc
                (@arr_pure arr HA _ _ (sum_bimap (fun c0 : C => c0) (fun _ : unit + unit => tt)))
                Lh
                (@arr_pure arr HA _ _ (@collapse D))). }
              apply cprop. 2: reflexivity. exact E12. }
            apply (cassoc L'h
              (@arr_pure arr HA _ _ (sum_bimap (fun d : option D => d) (fun _ : unit + unit => tt)))
              (@arr_pure arr HA _ _ (@collapse D))). }

          (* Step b: use E23 to swap [assoc] >>> L'h *)
          assert (Hb : @arrow_eq arr HE _ _
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (@assoc_sum C unit unit))
              (@arr_comp arr HA _ _ _ L'h
                (@arr_comp arr HA _ _ _
                  (@arr_pure arr HA _ _ (sum_bimap (fun d : option D => d) (fun _ : unit + unit => tt)))
                  (@arr_pure arr HA _ _ (@collapse D)))))
            (@arr_comp arr HA _ _ _ LLh
              (@arr_comp arr HA _ _ _
                (@arr_pure arr HA _ _ (@assoc_sum (option D) unit unit))
                (@arr_comp arr HA _ _ _
                  (@arr_pure arr HA _ _ (sum_bimap (fun d : option D => d) (fun _ : unit + unit => tt)))
                  (@arr_pure arr HA _ _ (@collapse D)))))).
          { etransitivity.
            { etransitivity. { symmetry. apply (cassoc
                (@arr_pure arr HA _ _ (@assoc_sum C unit unit))
                L'h). }
              apply cprop. 2: reflexivity. exact E23. }
            apply cassoc. }

          (* Chain: E14 = Ha composed with Hb then E34 *)
          etransitivity.
          { apply cprop. 1: reflexivity. exact Ha. }
          etransitivity.
          { exact Hb. }
          apply cprop. 1: reflexivity. exact E34. }

        etransitivity.
        { apply cprop. 1: reflexivity. exact E14. }
        (* [sbm ts id] >>> (LLh >>> ([sbm c id] >>> [c])) *)

        (* E4 -> E6: directly assert and prove *)
        assert (E46 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (sum_bimap (@to_sum C) (fun u : unit => u)))
            (@arr_comp arr HA _ _ _ LLh
              (@arr_comp arr HA _ _ _
                (@arr_pure arr HA _ _ (sum_bimap (@collapse D) (fun u : unit => u)))
                (@arr_pure arr HA _ _ (@collapse D)))))
          (@arr_comp arr HA _ _ _
            (@arr_left arr HA HC (option C) (option D) unit
              (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ (@to_sum C))
                (@arr_comp arr HA _ _ _ Lh
                  (@arr_pure arr HA _ _ (@collapse D)))))
            (@arr_pure arr HA _ _ (@collapse D)))).
        { etransitivity.
          { apply cprop. 2: reflexivity. exact E45a. }
          (* L[ts] >>> (LLh >>> ([sbm c id] >>> [c])) *)
          etransitivity.
          { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
            apply cprop. 2: reflexivity. exact E45b. }
          (* L[ts] >>> (LLh >>> (L[c] >>> [c])) *)
          etransitivity.
          { apply cprop. 1: reflexivity. symmetry. apply cassoc. }
          (* L[ts] >>> ((LLh >>> L[c]) >>> [c]) *)
          etransitivity.
          { symmetry. apply cassoc. }
          (* (L[ts] >>> (LLh >>> L[c])) >>> [c] *)
          etransitivity.
          { apply cprop. 2: reflexivity. symmetry. apply cassoc. }
          (* ((L[ts] >>> LLh) >>> L[c]) >>> [c] *)
          etransitivity.
          { apply cprop. 2: reflexivity.
            etransitivity. { apply cprop. 2: reflexivity. symmetry. apply lcomp. }
            symmetry. apply lcomp. }
          (* L(([ts] >>> Lh) >>> [c]) >>> [c] -- inner is left-assoc *)
          (* Fix inner association: L(([ts]>>>Lh)>>>[c]) -> L([ts]>>>(Lh>>>[c])) *)
          apply cprop. 2: reflexivity.
          apply lprop.
          apply cassoc. }
        exact E46. }
      (* Now use Hcore to prove the main equation *)
      (* LHS = (f >>> [ts] >>> Lg >>> [c]) >>> [ts] >>> Lh >>> [c]
         RHS = f >>> [ts] >>> L(g >>> [ts] >>> Lh >>> [c]) >>> [c] *)
      (* Step 1: Right-assoc LHS *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cassoc. }
      (* f >>> [ts] >>> Lg >>> ([c] >>> ([ts] >>> Lh >>> [c])) *)
      (* Step 2: [c] >>> [ts] -> [ts.c] *)
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* f >>> [ts] >>> Lg >>> ([ts.c] >>> Lh >>> [c]) *)
      (* Step 3: Left-associate ([ts.c] >>> Lh) >>> [c] for Hcore *)
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. symmetry. apply cassoc. }
      (* f >>> [ts] >>> Lg >>> (([ts.c] >>> Lh) >>> [c]) *)
      (* Step 4: Apply Hcore *)
      etransitivity. { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. exact Hcore. }
      (* f >>> [ts] >>> Lg >>> (L([ts]>>>Lh>>>[c]) >>> [c]) *)
      (* Step 5: Left-associate Lg >>> L(...) and apply lcomp *)
      apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. symmetry. apply lcomp.
    - (* pure_comp *)
      (* LHS: [Some . f] >>> [ts] >>> L [Some . g] >>> [c]
         RHS: [Some . (g . f)] *)
      (* Pre-prove: [Some . f] >>> [ts] = [inl . f] *)
      assert (H1 : @arrow_eq arr HE A (B + unit)
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a => Some (f a)))
          (@arr_pure arr HA _ _ to_sum))
        (@arr_pure arr HA _ _ (fun a => inl (f a)))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros x. reflexivity. }
      (* Pre-prove: L [Some . g] = [sum_bimap (Some . g) id] *)
      assert (H2 : @arrow_eq arr HE (B + unit) (option C + unit)
        (@arr_left arr HA HC _ _ _ (@arr_pure arr HA _ _ (fun b => Some (g b))))
        (@arr_pure arr HA _ _ (sum_bimap (fun b => Some (g b)) (fun c : unit => c)))).
      { apply lpure. }
      (* Pre-prove: [inl . f] >>> [sum_bimap (Some . g) id] = [inl . Some . g . f] *)
      assert (H3 : @arrow_eq arr HE A (option C + unit)
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a => inl (f a)))
          (@arr_pure arr HA _ _ (sum_bimap (fun b => Some (g b)) (fun c : unit => c))))
        (@arr_pure arr HA _ _ (fun a => @inl (option C) unit (Some (g (f a)))))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros x. reflexivity. }
      (* Pre-prove: [inl . Some . g . f] >>> [c] = [Some . g . f] *)
      assert (H4 : @arrow_eq arr HE A (option C)
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun a => @inl (option C) unit (Some (g (f a)))))
          (@arr_pure arr HA _ _ collapse))
        (@arr_pure arr HA _ _ (fun a => Some (g (f a))))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros x. reflexivity. }
      (* Chain: LHS = [Some.f] >>> ([ts] >>> L [Some.g] >>> [c]) *)
      (* right-associate *)
      etransitivity. { symmetry. apply cassoc. }
      (* = ([Some.f] >>> [ts]) >>> L [Some.g] >>> [c] *)
      etransitivity. { apply cprop. 2: reflexivity. exact H1. }
      (* = [inl.f] >>> L [Some.g] >>> [c] *)
      etransitivity. { symmetry. apply cassoc. }
      (* = ([inl.f] >>> L [Some.g]) >>> [c] *)
      etransitivity. { apply cprop. 2: reflexivity.
        etransitivity. { apply cprop. 1: reflexivity. exact H2. }
        exact H3. }
      (* = [inl . Some . g . f] >>> [c] *)
      exact H4.
    - (* first_pure *)
      etransitivity. { apply cprop. 2: reflexivity. apply fpure. }
      etransitivity. { apply pcomp. }
      apply arr_pure_ext. intros [a c]. reflexivity.
    - (* first_comp *)
      (* Goal (base level):
           F(f >>> [ts] >>> Lg >>> [c]) >>> [seq]
         ≃ (Ff >>> [seq]) >>> [ts] >>> L(Fg >>> [seq]) >>> [c]

         Chain:
         (1) fcomp x3:   Ff >>> F[ts] >>> F(Lg) >>> F[c] >>> [seq]
         (2) fpure x2:   Ff >>> [Fts] >>> F(Lg) >>> [Fc] >>> [seq]
         (3) pcomp:      Ff >>> [Fts] >>> F(Lg) >>> [Fc_seq]
                          where Fc_seq = seq . (collapse * id)
         (4) factor:     Ff >>> [Fts] >>> F(Lg) >>> [spd] >>> [cseq]
                          where cseq (inl p) = seq p, cseq (inr _) = None
         (5) fldist:     Ff >>> [Fts] >>> [spd] >>> L(Fg) >>> [cseq]
         (6) L(Fg) >>> [cseq]
              = L(Fg) >>> L[seq] >>> [sbm id g] >>> [c]   (lpure + pcomp)
              = L(Fg>>>[seq]) >>> [sbm id g] >>> [c]      (lcomp)
         (7) lnat:       ... >>> [sbm id g] >>> L(Fg>>>[seq]) >>> [c]
         (8) pcomp:      [Fts] >>> [spd] >>> [sbm id g] = [seq >>> ts]
         Final:          Ff >>> [seq] >>> [ts] >>> L(Fg>>>[seq]) >>> [c] *)

      Local Notation fldist := (@first_left_dist arr HA HC HE HCL).

      opt_unfold.

      (* (1) fcomp x3: distribute F over the four-fold composition *)
      etransitivity.
      { apply cprop. 2: reflexivity. apply fcomp. }
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity. apply fcomp. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply fcomp. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply cassoc. }
      (* Ff >>> F[ts] >>> F(Lg) >>> F[c] >>> [seq] *)

      (* (2) fpure on F[ts] and F[c] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply fpure. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply fpure. }
      (* Ff >>> [Fts] >>> F(Lg) >>> [Fc] >>> [seq] *)

      (* From here the term is:
           Ff >>> [Fts] >>> F(Lg) >>> [Fc] >>> [seq]
         where Fts(ob,d) = (ts ob, d), Fc(x,d) = (collapse x, d).

         We need to reach:
           Ff >>> [seq] >>> [ts] >>> L(Fg >>> [seq]) >>> [c]

         The proof proceeds by asserting helper equalities and chaining. *)

      (* Helper: [Fc] >>> [seq] = [spd] >>> [cseq]
         where cseq (inl (oc,d)) = seq(oc,d), cseq (inr _) = None *)
      set (cseq := fun (x : (option C * D) + (unit * D)) =>
        match x with
        | inl p => @sequence_option C D p
        | inr _ => @None (C * D)
        end).
      assert (Hfactor : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun p : (option C + unit) * D =>
            let '(x, d) := p in (collapse x, d)))
          (@arr_pure arr HA _ _ (@sequence_option C D)))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@sum_prod_dist (option C) unit D))
          (@arr_pure arr HA _ _ cseq))).
      { etransitivity. { apply pcomp. }
        symmetry. etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros [[oc|[]] d]; reflexivity. }

      (* Helper: [cseq] = L[seq] >>> [sbm id (fun _ => tt)] >>> [c] *)
      assert (Hcseq : @arrow_eq arr HE _ _
        (@arr_pure arr HA _ _ cseq)
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ _ (@arr_pure arr HA _ _ (@sequence_option C D)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun x : option (C * D) + (unit * D) =>
                sum_bimap (fun a : option (C * D) => a) (fun _ : unit * D => tt) x))
            (@arr_pure arr HA _ _ (@collapse (C * D)))))).
      { symmetry.
        etransitivity.
        { apply cprop. 2: reflexivity. apply lpure. }
        (* [sbm seq id] >>> [sbm id g] >>> [c] *)
        etransitivity. { symmetry. apply cassoc. }
        etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
        etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros [[oc d]|[[] d]]; [destruct oc|]; reflexivity. }

      (* Prove the tail: [Fts] >>> F(Lg) >>> [Fc] >>> [seq]
                       ≃ [seq] >>> [ts] >>> L(Fg >>> [seq]) >>> [c]

         It suffices to show this since both sides are Ff >>> tail. *)
      assert (Htail : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun p : option B * D =>
            let '(ob, d) := p in (to_sum ob, d)))
          (@arr_comp arr HA _ _ _
            (@arr_first arr HA _ _ D
              (@arr_left arr HA HC _ _ unit g))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (fun p : (option C + unit) * D =>
                let '(x, d) := p in (collapse x, d)))
              (@arr_pure arr HA _ _ (@sequence_option C D)))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@sequence_option B D))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@to_sum (B * D)))
            (@arr_comp arr HA _ _ _
              (@arr_left arr HA HC _ _ unit
                (@arr_comp arr HA _ _ _
                  (@arr_first arr HA _ _ D g)
                  (@arr_pure arr HA _ _ (@sequence_option C D))))
              (@arr_pure arr HA _ _ (@collapse (C * D))))))).
      {
        (* Step 1: Merge [Fc] >>> [seq] via pcomp *)
        etransitivity.
        { apply cprop. 1: reflexivity.
          apply cprop. 1: reflexivity. apply pcomp. }
        (* [Fts] >>> F(Lg) >>> [Fc_seq] *)

        (* Step 2: Factor [Fc_seq] as [spd] >>> [cseq] *)
        etransitivity.
        { apply cprop. 1: reflexivity.
          apply cprop. 1: reflexivity.
          symmetry.
          etransitivity.
          { exact (@pcomp
              ((option C + unit) * D)%type
              ((option C * D) + (unit * D))%type
              (option (C * D))
              (@sum_prod_dist (option C) unit D)
              cseq). }
          apply arr_pure_ext. intros [[oc|[]] d]; reflexivity. }
        (* [Fts] >>> F(Lg) >>> [spd] >>> [cseq] *)

        (* Step 3: Left-assoc F(Lg)>>>[spd], apply fldist *)
        etransitivity.
        { apply cprop. 1: reflexivity.
          etransitivity. { symmetry. apply cassoc. }
          apply cprop. 2: reflexivity. apply fldist. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply cassoc. }
        (* [Fts] >>> [spd] >>> L(Fg) >>> [cseq] *)

        (* Step 4: Replace [cseq] with L[seq] >>> [sbm] >>> [c] *)
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
          apply cprop. 1: reflexivity. exact Hcseq. }
        (* [Fts] >>> [spd] >>> L(Fg) >>> L[seq] >>> [sbm] >>> [c] *)

        (* Step 5: lcomp: L(Fg) >>> L[seq] -> L(Fg>>>[seq]) *)
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
          etransitivity. { symmetry. apply cassoc. }
          etransitivity. { symmetry. apply cassoc. }
          apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
          symmetry. apply lcomp. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
          apply cassoc. }
        (* [Fts] >>> [spd] >>> L(Fg>>>[seq]) >>> ([sbm] >>> [c]) *)

        (* Step 6: lnat: L(Fg>>>[seq]) >>> [sbm] -> [sbm] >>> L(Fg>>>[seq]) *)
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
          etransitivity. { symmetry. apply cassoc. }
          apply cprop. 2: reflexivity. apply lnat. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply cassoc. }
        (* [Fts] >>> [spd] >>> [sbm] >>> L(Fg>>>[seq]) >>> [c] *)

        (* Step 7: Merge [Fts]>>>[spd]>>>[sbm] into one pure, then split as [seq]>>>[ts] *)
        (* Left-associate the three pures *)
        etransitivity.
        { etransitivity. { symmetry. apply cassoc. }
          etransitivity. { symmetry. apply cassoc. }
          apply cprop. 2: reflexivity.
          (* ([Fts] >>> [spd]) >>> [sbm] *)
          etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
          apply pcomp. }
        (* Now have [merged_3] >>> L(Fg>>>[seq]) >>> [c] *)
        (* Split [merged_3] as [seq] >>> [ts] *)
        etransitivity.
        { apply cprop. 2: reflexivity.
          symmetry.
          etransitivity.
          { exact (@pcomp
              (option B * D)%type
              (option (B * D))
              ((B * D) + unit)%type
              (@sequence_option B D)
              (@to_sum (B * D))). }
          apply arr_pure_ext. intros [[b|] d]; reflexivity. }
        apply cassoc. }

      (* Right-associate the RHS, then apply Htail under Ff *)
      symmetry.
      etransitivity. { apply cassoc. }
      symmetry.
      apply cprop. 1: reflexivity. exact Htail.
    - (* first_fst *)
      (* LHS (opt-level): arr_first_opt f >>> arr_pure_opt fst
         RHS (opt-level): arr_pure_opt fst >>> f
         LHS (base): (Ff >>> [seq]) >>> [Some . fst]
                     where [Some . fst] = arr_pure (fun '(a,c) => Some (fst (a,c)))
                                        = arr_pure (fun '(a,c) => Some a)  -- for B*C -> option B
         Wait, but at the opt level, arr_comp uses [ts] >>> L >>> [c].
         Let's unfold properly. *)

      (* Unfold optionArrT operations:
         LHS = (Ff >>> [seq]) >>> [ts] >>> L [fun p => Some (fst p)] >>> [c]
         RHS = [fun p => Some (fst p)] >>> [ts] >>> L f >>> [c]
         where fst : B*C -> B, so [fun p => Some (fst p)] : (B*C) -> option B *)

      opt_unfold.

      (* LHS tail: simplify [seq] >>> [ts] >>> L[Some.fst] >>> [c] to [fst]
         [seq] : optB * C -> opt(B*C)
         [ts] : opt(B*C) -> (B*C)+unit
         L[Some.fst] : (B*C)+unit -> optB+unit
         [c] : optB+unit -> optB
         Composed: optB*C -> optB = fst *)
      assert (Htail : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@sequence_option B C))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@to_sum (B * C)))
            (@arr_comp arr HA _ _ _
              (@arr_left arr HA HC _ _ _
                (@arr_pure arr HA _ _ (fun p : B * C => Some (fst p))))
              (@arr_pure arr HA _ _ (@collapse B)))))
        (@arr_pure arr HA _ _ (@fst (option B) C))).
      { etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
          apply cprop. 2: reflexivity. apply lpure. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity.
        { apply pcomp. }
        apply arr_pure_ext. intros [oa c0]; destruct oa; reflexivity. }

      (* Similarly, simplify RHS head:
         [Some.fst] >>> [ts] = [fun p => inl (fst p)]   by pcomp *)
      assert (Hhead : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun p : A * C => Some (fst p)))
          (@arr_pure arr HA _ _ (@to_sum A)))
        (@arr_pure arr HA _ _ (fun p : A * C => @inl A unit (fst p)))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros [a0 c0]; reflexivity. }

      (* [inl . fst] = [fst] >>> [inl] *)
      assert (Hfst_inl : @arrow_eq arr HE _ _
        (@arr_pure arr HA _ _ (fun p : A * C => @inl A unit (fst p)))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@fst A C))
          (@arr_pure arr HA _ _ (@inl A unit)))).
      { symmetry. etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros [a0 c0]; reflexivity. }

      (* [inl . fst] >>> Lf = [fst] >>> f >>> [inl] *)
      assert (Hmid : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun p : A * C => @inl A unit (fst p)))
          (@arr_left arr HA HC _ _ _ f))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@fst A C))
          (@arr_comp arr HA _ _ _ f
            (@arr_pure arr HA _ _ (@inl (option B) unit))))).
      { etransitivity.
        { apply cprop. 2: reflexivity. exact Hfst_inl. }
        (* ([fst] >>> [inl]) >>> Lf *)
        etransitivity. { apply cassoc. }
        apply cprop. 1: reflexivity.
        symmetry. apply linl. }

      (* [inl] >>> [c] = [id] *)
      assert (Htail2 : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@inl (option B) unit))
          (@arr_pure arr HA _ _ (@collapse B)))
        (@arr_pure arr HA _ _ (fun x : option B => x))).
      { etransitivity. { apply pcomp. }
        apply arr_pure_ext. intro; reflexivity. }

      (* Now chain for LHS:
         (Ff >>> [seq]) >>> [ts] >>> L[Some.fst] >>> [c]
         = Ff >>> [seq] >>> [ts] >>> L[Some.fst] >>> [c]    by cassoc
         = Ff >>> [fst]                                      by Htail
         = [fst] >>> f                                       by ffst *)
      etransitivity.
      { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. exact Htail. }
      etransitivity.
      { apply ffst. }

      (* Now chain for RHS:
         [Some.fst] >>> [ts] >>> Lf >>> [c]
         = ([Some.fst] >>> [ts]) >>> Lf >>> [c]   (left-assoc for Hhead)
         = [inl.fst] >>> Lf >>> [c]               by Hhead
         = [fst] >>> f >>> [inl] >>> [c]           by Hmid
         = [fst] >>> f >>> [id]                    by Htail2
         = [fst] >>> f                             by cidr *)
      symmetry.
      etransitivity.
      { etransitivity.
        { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. exact Hhead. }
      (* [inl.fst] >>> Lf >>> [c] *)
      etransitivity.
      { etransitivity.
        { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. exact Hmid. }
      (* ([fst] >>> f >>> [inl]) >>> [c] *)
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. exact Htail2. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cidr. }
      reflexivity.
    - (* first_assoc *)
      (* Both sides simplify to [assoc_prod] >>> Ff >>> [seq_{B,C*D}].

         LHS = F(Ff >>> [seq_{B,C}]) >>> [seq_{B*C,D}] >>> [ts] >>> L[Some.assoc] >>> [c]

         Step 1: fcomp => F(Ff) >>> F[seq] >>> [seq'] >>> ...
         Step 2: fpure => F(Ff) >>> [(fun '((ob,c),d) => (seq(ob,c),d))] >>> [seq'] >>> ...
         Step 3: pcomp => F(Ff) >>> [fun p => seq'(seq(fst (fst p), snd (fst p)), snd p)] >>> [ts] >>> L[Some.assoc] >>> [c]
         Steps 4-6: further pcomp + lpure fuse everything after F(Ff) into [assoc >>> seq]
         Step 7: fassoc => [assoc] >>> F_{C*D}(f) >>> [seq]

         RHS = [Some.assoc'] >>> [ts] >>> L(Ff >>> [seq_{B,C*D}]) >>> [c]
         = [assoc] >>> [Some] >>> [ts] >>> L(Ff >>> [seq]) >>> [c]
         = [assoc] >>> [inl] >>> L(Ff >>> [seq]) >>> [c]           (pcomp)
         = [assoc] >>> (Ff >>> [seq]) >>> [inl] >>> [c]            (linl sym)
         = [assoc] >>> Ff >>> [seq] >>> [id]                       (pcomp: [inl]>>>[c] = [id])
         = [assoc] >>> Ff >>> [seq]                                (cidr) *)

      opt_unfold.

      (* LHS tail: F[seq] >>> [seq'] >>> [ts] >>> L[Some.assoc] >>> [c]
         = [assoc] >>> [seq_{B,C*D}]
         i.e., the stuff after F(Ff) simplifies to [assoc_prod] >>> [sequence_option] *)
      assert (Htail_eq : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_first arr HA _ _ _ (@arr_pure arr HA _ _ (@sequence_option B C)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@sequence_option (B * C) D))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (@to_sum ((B * C) * D)))
              (@arr_comp arr HA _ _ _
                (@arr_left arr HA HC _ _ _
                  (@arr_pure arr HA _ _ (fun p : (B * C) * D => Some (assoc_prod p))))
                (@arr_pure arr HA _ _ (@collapse (B * (C * D))))))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@assoc_prod (option B) C D))
          (@arr_pure arr HA _ _ (@sequence_option B (C * D))))).
      { etransitivity.
        { apply cprop. 2: reflexivity. apply fpure. }
        etransitivity.
        { apply cprop. 1: reflexivity.
          apply cprop. 1: reflexivity.
          apply cprop. 1: reflexivity.
          apply cprop. 2: reflexivity. apply lpure. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
          apply pcomp. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity.
        { apply pcomp. }
        symmetry.
        etransitivity.
        { apply pcomp. }
        apply arr_pure_ext. intros [[ob c0] d0]. destruct ob; reflexivity. }

      (* RHS simplification: [Some.assoc] >>> [ts] >>> L(Ff >>> [seq]) >>> [c]
         = [assoc] >>> Ff >>> [seq] *)
      assert (Hrhs : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun p : (A * C) * D => Some (assoc_prod p)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@to_sum (A * (C * D))))
            (@arr_comp arr HA _ _ _
              (@arr_left arr HA HC _ _ _
                (@arr_comp arr HA _ _ _ (@arr_first arr HA _ _ _ f)
                  (@arr_pure arr HA _ _ (@sequence_option B (C * D)))))
              (@arr_pure arr HA _ _ (@collapse (B * (C * D)))))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@assoc_prod A C D))
          (@arr_comp arr HA _ _ _ (@arr_first arr HA _ _ _ f)
            (@arr_pure arr HA _ _ (@sequence_option B (C * D)))))).
      { (* [Some.assoc] >>> [ts] = [assoc] >>> [inl] *)
        assert (H1 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (fun p : (A * C) * D => Some (assoc_prod p)))
            (@arr_pure arr HA _ _ (@to_sum (A * (C * D)))))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@assoc_prod A C D))
            (@arr_pure arr HA _ _ (@inl (A * (C * D)) unit)))).
        { etransitivity. { apply pcomp. }
          symmetry. etransitivity. { apply pcomp. }
          apply arr_pure_ext. intros [[a0 c0] d0]; reflexivity. }
        (* [inl] >>> [c] = [id] *)
        assert (H2 : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@inl (option (B * (C * D))) unit))
            (@arr_pure arr HA _ _ (@collapse (B * (C * D)))))
          (@arr_pure arr HA _ _ (fun x => x))).
        { etransitivity. { apply pcomp. }
          apply arr_pure_ext. intro; reflexivity. }
        (* Left-assoc: ([Some.assoc] >>> [ts]) >>> (L(...) >>> [c]) *)
        etransitivity. { symmetry. apply cassoc. }
        (* Replace head *)
        etransitivity. { apply cprop. 2: reflexivity. exact H1. }
        (* ([assoc] >>> [inl]) >>> (L(Ff >>> [seq]) >>> [c]) *)
        etransitivity. { apply cassoc. }
        (* [assoc] >>> ([inl] >>> (L(Ff >>> [seq]) >>> [c])) *)
        etransitivity.
        { apply cprop. 1: reflexivity.
          (* [inl] >>> (L(Ff >>> [seq]) >>> [c]) *)
          etransitivity. { symmetry. apply cassoc. }
          (* ([inl] >>> L(Ff >>> [seq])) >>> [c] *)
          etransitivity. { apply cprop. 2: reflexivity. symmetry. apply linl. }
          (* ((Ff >>> [seq]) >>> [inl]) >>> [c] *)
          etransitivity. { apply cassoc. }
          (* (Ff >>> [seq]) >>> ([inl] >>> [c]) *)
          etransitivity. { apply cprop. 1: reflexivity. exact H2. }
          (* (Ff >>> [seq]) >>> [id] *)
          apply cidr. }
        (* [assoc] >>> Ff >>> [seq] *)
        reflexivity. }

      (* LHS chain *)
      (* First, right-associate the outer *)
      etransitivity. { apply cassoc. }
      (* F(Ff >>> [seq]) >>> (tail) *)

      (* Apply fcomp: F(Ff >>> [seq]) = F(Ff) >>> F[seq] *)
      assert (Hfcomp_eq : @arrow_eq arr HE _ _
        (@arr_first arr HA _ _ D
          (@arr_comp arr HA _ _ _ (@arr_first arr HA _ _ C f)
            (@arr_pure arr HA _ _ (@sequence_option B C))))
        (@arr_comp arr HA _ _ _
          (@arr_first arr HA _ _ D (@arr_first arr HA _ _ C f))
          (@arr_first arr HA _ _ D (@arr_pure arr HA _ _ (@sequence_option B C))))).
      { apply fcomp. }

      etransitivity.
      { apply cprop. 2: reflexivity. exact Hfcomp_eq. }
      (* (F(Ff) >>> F[seq]) >>> (tail) *)
      etransitivity. { apply cassoc. }
      (* F(Ff) >>> (F[seq] >>> tail) *)
      etransitivity.
      { apply cprop. 1: reflexivity. exact Htail_eq. }
      (* F(Ff) >>> [assoc] >>> [seq] *)

      (* Use fassoc: F(Ff) >>> [assoc] = [assoc] >>> Ff *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply fassoc. }
      etransitivity.
      { apply cassoc. }
      (* [assoc] >>> Ff >>> [seq] *)

      (* RHS chain *)
      symmetry. exact Hrhs.
    - (* comp_proper *)
      unfold Proper, respectful. intros f' g' Hfg h' k' Hhk.
      opt_unfold.
      apply cprop; [assumption |].
      apply cprop; [reflexivity |].
      apply cprop; [| reflexivity].
      apply lprop. assumption.
    - (* first_proper *)
      unfold Proper, respectful. intros f' g' Hfg.
      apply cprop; [| reflexivity].
      apply fprop. assumption.
    - (* first_natural: sequence_option commutes with mapping the context. *)
      etransitivity. { apply optionArrT_comp_pure_r. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry. opt_unfold.
      assert (Hsequence : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@sequence_option B C))
          (@arr_pure arr HA _ _
            (option_map (fun '(b, c) => (b, g c)))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun '(ob, c) => (ob, g c)))
          (@arr_pure arr HA _ _ (@sequence_option B D)))).
      { etransitivity. { apply pcomp. }
        symmetry. etransitivity. { apply pcomp. }
        apply arr_pure_ext. intros [[b|] c]; reflexivity. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. exact Hsequence. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply fnat. }
      apply cassoc.
  Qed.

End GenericOptionArrTLaws.
