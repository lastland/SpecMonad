From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.StateArrowT Require Import Core.

Arguments ArrowApply_stateArrT {_} {_} {_} {_}.

(* ================================================================= *)
(** ** ArrowChoiceLaws for [stateArrT]                                *)
(* ================================================================= *)

Section StateArrowTChoiceLaws.

  Variable S : Type.
  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HCL : @ArrowChoiceLaws arr HA HC HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl   := (@comp_id_l arr HA HE HL).
  Local Notation cidr   := (@comp_id_r arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation fprop  := (@first_proper arr HA HE HL).
  Local Notation fpure  := (@first_pure arr HA HE HL).
  Local Notation fcomp  := (@first_comp arr HA HE HL).
  Local Notation ffst   := (@first_fst arr HA HE HL).
  Local Notation fassoc := (@first_assoc arr HA HE HL).
  Local Notation lpure  := (@left_pure arr HA HC HE HCL).
  Local Notation lcomp  := (@left_comp arr HA HC HE HCL).
  Local Notation linl   := (@left_inl arr HA HC HE HCL).
  Local Notation lassoc := (@left_assoc arr HA HC HE HCL).
  Local Notation linr   := (@left_inr arr HA HC HE HCL).
  Local Notation lnat   := (@left_natural arr HA HC HE HCL).
  Local Notation fldist := (@first_left_dist arr HA HC HE HCL).
  Local Notation lprop  := (@left_proper arr HA HC HE HCL).

  Local Lemma arr_pure_ext' {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro Hext. replace g with f by (extensionality x; apply Hext).
    reflexivity.
  Qed.

  Local Ltac pure_ext :=
    apply arr_pure_ext'; intro;
    unfold sum_distribute, sum_undistribute,
           state_shuffle_in, state_shuffle_out, assoc_prod,
           sum_bimap, assoc_sum, sum_prod_dist;
    repeat match goal with
    | [p : _ * _ |- _] => destruct p
    | [s : _ + _ |- _] => destruct s
    end;
    simpl; reflexivity.

  (** Unfold the stateArrT operations to base-arrow terms. *)
  Local Ltac st_unfold :=
    unfold arr_id, arr_comp, arr_pure, arr_first, arr_left,
           Arrow_stateArrT, ArrowChoice_stateArrT,
           arrow_eq, ArrowEq_stateArrT;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_left arr HA HC) (@arrow_eq arr HE).

  (** The key identity: [sd] >>> left f >>> [su] distributes state
      across a left-mapped arrow. We prove many choice laws by
      reducing to the base arrow law plus shuffling [sd]/[su]. *)

  #[global]
  Instance ArrowChoiceLaws_stateArrT : ArrowChoiceLaws (stateArrT S arr).
  Proof.
    constructor; intros; st_unfold.
    - (* left_pure *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity.
        apply lpure. }
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      etransitivity. { apply pcomp. }
      pure_ext.
    - (* left_comp *)
      set (Lf := @arr_left arr HA HC (A*S) (B*S) (D*S) f).
      set (Lg := @arr_left arr HA HC (B*S) (C*S) (D*S) g).
      set (sd_A := @arr_pure arr HA _ _ (@sum_distribute A D S)).
      set (su_B := @arr_pure arr HA _ _ (@sum_undistribute B D S)).
      set (sd_B := @arr_pure arr HA _ _ (@sum_distribute B D S)).
      set (su_C := @arr_pure arr HA _ _ (@sum_undistribute C D S)).
      assert (Hlhs : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _ sd_A
          (@arr_comp arr HA _ _ _
            (@arr_left arr HA HC _ _ _ (@arr_comp arr HA _ _ _ f g))
            su_C))
        (@arr_comp arr HA _ _ _ sd_A
          (@arr_comp arr HA _ _ _ Lf
            (@arr_comp arr HA _ _ _ Lg su_C)))).
      { apply cprop. 1: reflexivity.
        etransitivity.
        { apply cprop. 2: reflexivity. apply lcomp. }
        apply cassoc. }
      assert (Hcancel : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _ su_B sd_B)
        (@arr_id arr HA _)).
      { etransitivity. {
          apply (@pure_comp arr HA HE HL _ _ _
            (@sum_undistribute B D S) (@sum_distribute B D S)). }
        apply arr_pure_ext'. intros [(b,s0)|(d,s0)]; reflexivity. }
      assert (Hrhs : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_comp arr HA _ _ _ sd_A
            (@arr_comp arr HA _ _ _ Lf su_B))
          (@arr_comp arr HA _ _ _ sd_B
            (@arr_comp arr HA _ _ _ Lg su_C)))
        (@arr_comp arr HA _ _ _ sd_A
          (@arr_comp arr HA _ _ _ Lf
            (@arr_comp arr HA _ _ _ Lg su_C)))).
      { etransitivity. { apply cassoc. }
        apply cprop. 1: reflexivity.
        etransitivity. { apply cassoc. }
        apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        etransitivity. { apply cprop. 2: reflexivity. exact Hcancel. }
        apply cidl. }
      etransitivity. { exact Hlhs. }
      symmetry. exact Hrhs.
    - (* left_inl *)
      symmetry.
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
        etransitivity. { apply pcomp. }
        apply arr_pure_ext'. intros (a0, s0); reflexivity. }
      etransitivity.
      { apply cprop. 2: reflexivity.
        symmetry. apply linl. }
      etransitivity. { apply cassoc. }
      apply cprop. 1: reflexivity.
      etransitivity. { apply pcomp. }
      pure_ext.
    - (* left_assoc *)
      set (Lf := @arr_left arr HA HC _ _ (C*S) f).
      set (LLf := @arr_left arr HA HC _ _ (D*S) Lf).
      set (Lf_CD := @arr_left arr HA HC _ _ ((C+D)*S) f).
      set (Lf_CsDs := @arr_left arr HA HC _ _ ((C*S+D*S)%type) f).
      set (sd_D := @arr_pure arr HA _ _ (@sum_distribute (A+C) D S)).
      set (su_D := @arr_pure arr HA _ _ (@sum_undistribute (B+C) D S)).
      set (su_CD := @arr_pure arr HA _ _ (@sum_undistribute B (C+D) S)).
      set (sd_CD := @arr_pure arr HA _ _ (@sum_distribute A (C+D) S)).
      set (assoc_s := @arr_pure arr HA _ _ (fun p : (((B + C) + D) * S)%type => let '(x, s0) := p in (assoc_sum x, s0))).
      set (assoc_s_in := @arr_pure arr HA _ _ (fun p : (((A + C) + D) * S)%type => let '(x, s0) := p in (assoc_sum x, s0))).
      set (sbm_sd := @arr_pure arr HA _ _
        (fun x : ((A+C)*S + D*S)%type =>
          @sum_bimap ((A+C)*S) (D*S) (A*S+C*S) (D*S)
            (@sum_distribute A C S) (fun d : D*S => d) x)).
      set (sbm_su := @arr_pure arr HA _ _
        (fun x : ((B*S+C*S) + D*S)%type =>
          @sum_bimap (B*S+C*S) (D*S) ((B+C)*S) (D*S)
            (@sum_undistribute B C S) (fun d : D*S => d) x)).
      set (assoc_base := @arr_pure arr HA _ _ (@assoc_sum (B*S) (C*S) (D*S))).
      set (sbm_su_inner := @arr_pure arr HA _ _
        (fun x : (B*S + (C*S + D*S))%type =>
          @sum_bimap (B*S) (C*S+D*S) (B*S) ((C+D)*S)
            (fun b : B*S => b) (@sum_undistribute C D S) x)).
      set (assoc_base_in := @arr_pure arr HA _ _ (@assoc_sum (A*S) (C*S) (D*S))).
      set (sbm_sd_inner := @arr_pure arr HA _ _
        (fun x : (A*S + (C*S + D*S))%type =>
          @sum_bimap (A*S) (C*S+D*S) (A*S) ((C+D)*S)
            (fun a : A*S => a) (@sum_undistribute C D S) x)).

      (* L(inner) = sbm_sd >>> LLf >>> sbm_su *)
      assert (H_expand :
        @arrow_eq arr HE _ _
          (@arr_left arr HA HC _ _ (D*S)
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (@sum_distribute A C S))
              (@arr_comp arr HA _ _ _ Lf
                (@arr_pure arr HA _ _ (@sum_undistribute B C S)))))
          (@arr_comp arr HA _ _ _ (@arr_comp arr HA _ _ _ sbm_sd LLf) sbm_su)).
      { etransitivity. { apply lprop. symmetry. apply cassoc. }
        etransitivity. { apply lcomp. }
        apply cprop.
        - etransitivity. { apply lcomp. }
          apply cprop. 2: reflexivity. subst sbm_sd. apply lpure.
        - subst sbm_su. apply lpure. }

      (* tail: sbm_su >>> su_D >>> assoc_s = assoc_base >>> sbm_su_inner >>> su_CD *)
      assert (H_tail :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _ sbm_su (@arr_comp arr HA _ _ _ su_D assoc_s))
          (@arr_comp arr HA _ _ _ assoc_base (@arr_comp arr HA _ _ _ sbm_su_inner su_CD))).
      { assert (Hlhs : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _ sbm_su (@arr_comp arr HA _ _ _ su_D assoc_s))
          (@arr_pure arr HA _ _
            (fun x : ((B*S+C*S)+D*S)%type =>
              match x with
              | inl (inl (b, s0)) => (inl b, s0) : ((B+(C+D))*S)%type
              | inl (inr (c, s0)) => (inr (inl c), s0) : ((B+(C+D))*S)%type
              | inr (d, s0) => (inr (inr d), s0) : ((B+(C+D))*S)%type
              end))).
        { subst sbm_su su_D assoc_s.
          etransitivity. { symmetry. apply cassoc. }
          etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
          etransitivity. { apply pcomp. }
          pure_ext. }
        assert (Hrhs : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _ assoc_base (@arr_comp arr HA _ _ _ sbm_su_inner su_CD))
          (@arr_pure arr HA _ _
            (fun x : ((B*S+C*S)+D*S)%type =>
              match x with
              | inl (inl (b, s0)) => (inl b, s0) : ((B+(C+D))*S)%type
              | inl (inr (c, s0)) => (inr (inl c), s0) : ((B+(C+D))*S)%type
              | inr (d, s0) => (inr (inr d), s0) : ((B+(C+D))*S)%type
              end))).
        { subst assoc_base sbm_su_inner su_CD.
          etransitivity. { symmetry. apply cassoc. }
          etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
          etransitivity. { apply pcomp. }
          pure_ext. }
        etransitivity. { exact Hlhs. }
        symmetry. exact Hrhs. }

      (* head: sd_D >>> sbm_sd >>> assoc_base_in >>> sbm_sd_inner = assoc_s_in >>> sd_CD *)
      assert (H_head :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _ sd_D
            (@arr_comp arr HA _ _ _ sbm_sd
              (@arr_comp arr HA _ _ _ assoc_base_in sbm_sd_inner)))
          (@arr_comp arr HA _ _ _ assoc_s_in sd_CD)).
      { assert (Hlhs : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _ sd_D
            (@arr_comp arr HA _ _ _ sbm_sd
              (@arr_comp arr HA _ _ _ assoc_base_in sbm_sd_inner)))
          (@arr_pure arr HA _ _
            (fun x : (((A+C)+D)*S)%type =>
              match x with
              | (inl (inl a), s0) => @inl (A*S) ((C+D)*S) (a, s0)
              | (inl (inr c), s0) => @inr (A*S) ((C+D)*S) (inl c, s0)
              | (inr d, s0) => @inr (A*S) ((C+D)*S) (inr d, s0)
              end))).
        { subst sd_D sbm_sd assoc_base_in sbm_sd_inner.
          etransitivity. { symmetry. apply cassoc. }
          etransitivity. { symmetry. apply cassoc. }
          etransitivity. { apply cprop. 2: reflexivity.
            etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
            apply pcomp. }
          etransitivity. { apply pcomp. }
          pure_ext. }
        assert (Hrhs : @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _ assoc_s_in sd_CD)
          (@arr_pure arr HA _ _
            (fun x : (((A+C)+D)*S)%type =>
              match x with
              | (inl (inl a), s0) => @inl (A*S) ((C+D)*S) (a, s0)
              | (inl (inr c), s0) => @inr (A*S) ((C+D)*S) (inl c, s0)
              | (inr d, s0) => @inr (A*S) ((C+D)*S) (inr d, s0)
              end))).
        { subst assoc_s_in sd_CD.
          etransitivity. { apply pcomp. }
          pure_ext. }
        etransitivity. { exact Hlhs. }
        symmetry. exact Hrhs. }

      (* Assemble *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity.
        exact H_expand. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. exact H_tail. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
        subst assoc_base LLf. apply lassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply cprop. 1: reflexivity.
        subst sbm_su_inner Lf_CsDs. apply lnat. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity. apply cassoc. }
      (* sd_D >>> sbm_sd >>> (assoc_base_in >>> (sbm_sd_inner >>> (Lf_CD >>> su_CD))) *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. symmetry. apply cassoc. }
      etransitivity.
      { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity. exact H_head. }
      subst Lf_CD assoc_s_in sd_CD su_CD.
      etransitivity. { apply cassoc. }
      apply cprop. 1: reflexivity. reflexivity.
    - (* left_inr *)
      (* [inr_s] >>> [sd] >>> Lf >>> [su] ≃ [inr_s] *)
      (* Right-associate then collapse [inr_s]>>>[sd] = [inr] *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply cprop. 2: reflexivity.
        apply pcomp. }
      (* [inr_combined] >>> Lf >>> [su] *)
      (* [inr_combined] = [inr] *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply cprop. 2: reflexivity.
        apply arr_pure_ext'. intros (c0, s0); reflexivity. }
      (* [inr] >>> Lf >>> [su] *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply linr. }
      (* [inr] >>> [su] *)
      etransitivity. { apply pcomp. }
      pure_ext.
    - (* left_natural *)
      (* LHS: ([sd] >>> Lf >>> [su]) >>> [ps (sbm id g)]
         RHS: [ps (sbm id g)] >>> ([sd'] >>> Lf' >>> [su']) *)
      (* Flatten and collapse pure parts, then use base lnat *)
      set (h := fun (p : C * S) => let '(c0, s0) := p in (g c0, s0)).

      (* LHS: flatten *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      (* [sd] >>> Lf >>> ([su] >>> [ps (sbm id g)]) *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply pcomp. }
      (* [sd] >>> Lf >>> [su >>> ps(sbm id g)] *)
      (* Factor tail: su >>> ps(sbm id g) = [sbm id h] >>> [su'] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        symmetry.
        etransitivity. {
          apply (@pure_comp arr HA HE HL _ _ _
            (fun x => @sum_bimap (B*S) (C*S) (B*S) (D*S) (fun b => b) h x)
            (@sum_undistribute B D S)). }
        apply arr_pure_ext'. intros [(b0,s0)|(c0,s0)]; reflexivity. }
      (* [sd] >>> Lf >>> [sbm id h] >>> [su'] *)

      (* Use lnat: Lf >>> [sbm id h] = [sbm id h] >>> Lf' *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply lnat. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      (* [sd] >>> [sbm id h] >>> Lf' >>> [su'] *)

      (* Collapse head: [sd] >>> [sbm id h] *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }

      (* RHS: flatten and collapse *)
      (* RHS is [ps_sbm] >>> ([sd'] >>> (Lf' >>> [su']))  *)
      symmetry.
      etransitivity. { symmetry. apply cassoc. }
      (* ([ps_sbm] >>> [sd']) >>> (Lf' >>> [su']) *)
      apply cprop. 2: reflexivity.
      etransitivity. { apply pcomp. }
      apply arr_pure_ext'. intro x; destruct x as [[a0|c0] s0]; reflexivity.

    - (* first_left_dist *)
      set (Lf := @arr_left arr HA HC (A*S) (B*S) (C*S) f).
      set (Ff := @arr_first arr HA (A*S) (B*S) D f).
      set (FLf := @arr_first arr HA _ _ D Lf).
      set (LFf := @arr_left arr HA HC _ _ ((C*D)*S) Ff).

      (* LHS head: si >>> F[sd] into single pure *)
      assert (H_lhs_head :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@state_shuffle_in S (A+C) D))
            (@arr_first arr HA _ _ _
              (@arr_pure arr HA _ _ (@sum_distribute A C S))))
          (@arr_pure arr HA _ _
            (fun x : (((A+C)*D)*S)%type =>
              match x with
              | ((inl a, d), s0) => ((inl (a, s0), d) : ((A*S + C*S) * D)%type)
              | ((inr c, d), s0) => ((inr (c, s0), d) : ((A*S + C*S) * D)%type)
              end))).
      { etransitivity. { apply cprop. 1: reflexivity. apply fpure. }
        etransitivity. { apply pcomp. }
        pure_ext. }

      (* LHS tail: F[su] >>> so >>> spd_s into single pure *)
      assert (H_lhs_tail :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_first arr HA _ _ _
              (@arr_pure arr HA _ _ (@sum_undistribute B C S)))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (@state_shuffle_out S (B+C) D))
              (@arr_pure arr HA _ _
                (fun p : (((B+C)*D)*S)%type => let '(x, s0) := p in (sum_prod_dist x, s0)))))
          (@arr_pure arr HA _ _
            (fun x : (((B*S+C*S)*D))%type =>
              match x with
              | (inl (b, s0), d) => ((inl (b, d), s0) : (((B*D)+(C*D))*S)%type)
              | (inr (c, s0), d) => ((inr (c, d), s0) : (((B*D)+(C*D))*S)%type)
              end))).
      { (* Fuse to intermediate pure, then prove via ext *)
        assert (Hfused :
          @arrow_eq arr HE _ _
            (@arr_comp arr HA _ _ _
              (@arr_first arr HA _ _ _
                (@arr_pure arr HA _ _ (@sum_undistribute B C S)))
              (@arr_comp arr HA _ _ _
                (@arr_pure arr HA _ _ (@state_shuffle_out S (B+C) D))
                (@arr_pure arr HA _ _
                  (fun p : (((B+C)*D)*S)%type => let '(x, s0) := p in (sum_prod_dist x, s0)))))
            (@arr_pure arr HA _ _
              (fun x : (((B*S+C*S)*D))%type =>
                match x with
                | (inl (b, s0), d) => ((inl (b, d), s0) : (((B*D)+(C*D))*S)%type)
                | (inr (c, s0), d) => ((inr (c, d), s0) : (((B*D)+(C*D))*S)%type)
                end))).
        { etransitivity. { symmetry. apply cassoc. }
          etransitivity.
          { apply cprop. 2: reflexivity. apply cprop. 2: reflexivity. apply fpure. }
          etransitivity.
          { apply cprop. 2: reflexivity. apply pcomp. }
          (* [f] >>> [spd_s] where spd_s has pattern match *)
          (* Rewrite spd_s to non-pattern form *)
          transitivity
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _
                (fun x : (((B*S+C*S))*D)%type =>
                  @state_shuffle_out S (B+C) D
                    (let '(a, c) := x in (@sum_undistribute B C S a, c))))
              (@arr_pure arr HA _ _
                (fun x : (((B+C)*D)*S)%type =>
                  (sum_prod_dist (fst x), snd x)))).
          { apply cprop. 1: reflexivity. apply arr_pure_ext'.
            intros ((bc, d), s0); reflexivity. }
          etransitivity. { apply pcomp. }
          pure_ext. }
        exact Hfused. }

      (* Factor LHS tail as [spd_base] >>> [t2] *)
      assert (H_lhs_tail_factor :
        @arrow_eq arr HE _ _
          (@arr_pure arr HA _ _
            (fun x : (((B*S+C*S)*D))%type =>
              match x with
              | (inl (b, s0), d) => ((inl (b, d), s0) : (((B*D)+(C*D))*S)%type)
              | (inr (c, s0), d) => ((inr (c, d), s0) : (((B*D)+(C*D))*S)%type)
              end))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@sum_prod_dist (B*S) (C*S) D))
            (@arr_pure arr HA _ _
              (fun x : ((B*S*D)+(C*S*D))%type =>
                match x with
                | inl ((b, s0), d) => ((inl (b, d), s0) : (((B*D)+(C*D))*S)%type)
                | inr ((c, s0), d) => ((inr (c, d), s0) : (((B*D)+(C*D))*S)%type)
                end)))).
      { symmetry.
        etransitivity. { apply pcomp. }
        pure_ext. }

      (* Fused LHS head with spd_base *)
      assert (H_lhs_fused_head :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun x : (((A+C)*D)*S)%type =>
                match x with
                | ((inl a, d), s0) => ((inl (a, s0), d) : ((A*S + C*S) * D)%type)
                | ((inr c, d), s0) => ((inr (c, s0), d) : ((A*S + C*S) * D)%type)
                end))
            (@arr_pure arr HA _ _ (@sum_prod_dist (A*S) (C*S) D)))
          (@arr_pure arr HA _ _
            (fun x : (((A+C)*D)*S)%type =>
              match x with
              | ((inl a, d), s0) => (inl ((a, s0), d) : ((A*S*D)+(C*S*D))%type)
              | ((inr c, d), s0) => (inr ((c, s0), d) : ((A*S*D)+(C*S*D))%type)
              end))).
      { etransitivity. { apply pcomp. }
        pure_ext. }

      (* RHS head: spd_s >>> sd' *)
      assert (H_rhs_head :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun p : (((A+C)*D)*S)%type => let '(x, s0) := p in (sum_prod_dist x, s0)))
            (@arr_pure arr HA _ _ (@sum_distribute (A*D) (C*D) S)))
          (@arr_pure arr HA _ _
            (fun x : (((A+C)*D)*S)%type =>
              match x with
              | ((inl a, d), s0) => ((inl ((a, d), s0)) : ((A*D)*S + (C*D)*S)%type)
              | ((inr c, d), s0) => ((inr ((c, d), s0)) : ((A*D)*S + (C*D)*S)%type)
              end))).
      { transitivity
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun p : (((A+C)*D)*S)%type => (sum_prod_dist (fst p), snd p)))
            (@arr_pure arr HA _ _ (@sum_distribute (A*D) (C*D) S))).
        { apply cprop. 2: reflexivity. apply arr_pure_ext'.
          intros ((ac, d), s0); reflexivity. }
        etransitivity. { apply pcomp. }
        pure_ext. }

      (* RHS expand + fuse: rhs_head >>> sbm(si', id) *)
      assert (H_rhs_fused_head :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun x : (((A+C)*D)*S)%type =>
                match x with
                | ((inl a, d), s0) => ((inl ((a, d), s0)) : ((A*D)*S + (C*D)*S)%type)
                | ((inr c, d), s0) => ((inr ((c, d), s0)) : ((A*D)*S + (C*D)*S)%type)
                end))
            (@arr_pure arr HA _ _
              (fun x : ((A*D)*S + (C*D)*S)%type =>
                @sum_bimap ((A*D)*S) ((C*D)*S) ((A*S)*D) ((C*D)*S)
                  (@state_shuffle_in S A D) (fun c0 : (C*D)*S => c0) x)))
          (@arr_pure arr HA _ _
            (fun x : (((A+C)*D)*S)%type =>
              match x with
              | ((inl a, d), s0) => (inl ((a, s0), d) : ((A*S*D)+((C*D)*S))%type)
              | ((inr c, d), s0) => (inr ((c, d), s0) : ((A*S*D)+((C*D)*S))%type)
              end))).
      { etransitivity. { apply pcomp. }
        pure_ext. }

      (* === Assemble LHS === *)
      (* Expand F(sd >>> Lf >>> su) using only fcomp (no fpure) *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity.
        etransitivity. { apply fprop. symmetry. apply cassoc. }
        etransitivity. { apply fcomp. }
        apply cprop. 2: reflexivity. apply fcomp. }
      (* si >>> ((F[sd] >>> FLf) >>> F[su]) >>> so) >>> spd_s *)
      (* Right-associate *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      (* si >>> F[sd] >>> (FLf >>> (F[su] >>> (so >>> spd_s))) *)
      (* Fuse head: si >>> F[sd] *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. exact H_lhs_head. }
      (* Fuse tail: FLf >>> (F[su] >>> (so >>> spd_s)) *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. exact H_lhs_tail. }
      (* Factor tail *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. exact H_lhs_tail_factor. }
      (* Apply fldist *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity.
        subst Lf FLf. apply fldist. }
      (* Fuse head with spd_base *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        etransitivity.
        { apply cprop. 2: reflexivity. symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
        exact H_lhs_fused_head. }
      (* [fused_lhs_head] >>> (LFf >>> [t2]) *)

      (* === Assemble RHS === *)
      symmetry.
      (* Expand L(si >>> Ff >>> so) *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity.
        etransitivity. { apply lprop. symmetry. apply cassoc. }
        etransitivity. { apply lcomp. }
        apply cprop.
        - etransitivity. { apply lcomp. }
          apply cprop. 2: reflexivity. apply lpure.
        - apply lpure. }
      (* Left-associate: spd_s >>> sd' >>> ((L[si'] >>> LFf) >>> L[so']) >>> su' *)
      etransitivity. { symmetry. apply cassoc. }
      (* (spd_s >>> sd') >>> (((L[si'] >>> LFf) >>> L[so']) >>> su') *)
      etransitivity. { symmetry. apply cassoc. }
      (* ((spd_s >>> sd') >>> ((L[si'] >>> LFf) >>> L[so'])) >>> su' *)
      etransitivity. { apply cprop. 2: reflexivity. symmetry. apply cassoc. }
      (* (((spd_s >>> sd') >>> (L[si'] >>> LFf)) >>> L[so']) >>> su' *)
      etransitivity. { apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
        symmetry. apply cassoc. }
      (* ((((spd_s >>> sd') >>> L[si']) >>> LFf) >>> L[so']) >>> su' *)

      (* Fuse head: spd_s >>> sd' >>> L[si'] into single pure *)
      assert (H_rhs_3fuse :
        @arrow_eq arr HE _ _
          (@arr_comp arr HA _ _ _
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _
                (fun p : (((A+C)*D)*S)%type => let '(x, s0) := p in (sum_prod_dist x, s0)))
              (@arr_pure arr HA _ _ (@sum_distribute (A*D) (C*D) S)))
            (@arr_pure arr HA _ _
              (fun x : ((A*D)*S + (C*D)*S)%type =>
                @sum_bimap ((A*D)*S) ((C*D)*S) ((A*S)*D) ((C*D)*S)
                  (@state_shuffle_in S A D) (fun c0 : (C*D)*S => c0) x)))
          (@arr_pure arr HA _ _
            (fun x : (((A+C)*D)*S)%type =>
              match x with
              | ((inl a, d), s0) => (inl ((a, s0), d) : ((A*S*D)+((C*D)*S))%type)
              | ((inr c, d), s0) => (inr ((c, d), s0) : ((A*S*D)+((C*D)*S))%type)
              end))).
      { etransitivity.
        { apply cprop. 2: reflexivity.
          transitivity
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _
                (fun p : (((A+C)*D)*S)%type => (sum_prod_dist (fst p), snd p)))
              (@arr_pure arr HA _ _ (@sum_distribute (A*D) (C*D) S))).
          { apply cprop. 2: reflexivity.
            apply arr_pure_ext'. intros ((ac, d), s0); reflexivity. }
          apply pcomp. }
        etransitivity. { apply pcomp. }
        pure_ext. }
      etransitivity.
      { apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
        apply cprop. 2: reflexivity. exact H_rhs_3fuse. }

      (* Right-associate *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cassoc. }
      (* [h] >>> (LFf_{CDS} >>> (L[so'] >>> su')) *)

      (* Fuse tail: L[so'] >>> su' into single pure [t_{CDS}] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
      (* [h] >>> (LFf_{CDS} >>> [t_{CDS}]) *)

      (* Factor [t_{CDS}] = [sbm id si] >>> [t_{CSD}] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        transitivity
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun x : ((B*S)*D + (C*D)*S)%type =>
                @sum_bimap ((B*S)*D) ((C*D)*S) ((B*S)*D) ((C*S)*D)
                  (fun b : (B*S)*D => b) (@state_shuffle_in S C D) x))
            (@arr_pure arr HA _ _
              (fun x : ((B*S)*D + (C*S)*D)%type =>
                match x with
                | inl ((b, s0), d) => ((inl (b, d), s0) : (((B*D)+(C*D))*S)%type)
                | inr ((c, s0), d) => ((inr (c, d), s0) : (((B*D)+(C*D))*S)%type)
                end))).
        { symmetry. etransitivity. { apply pcomp. } pure_ext. }
        reflexivity. }

      (* Reassociate: [h] >>> ((LFf_{CDS} >>> [sbm id si]) >>> [t_{CSD}]) *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity.
        (* Apply lnat: LFf >>> [sbm id si] = [sbm id si] >>> L(Ff)_{CSD} *)
        subst Ff LFf. apply lnat. }
      (* [h] >>> (([sbm id si] >>> L(Ff)_{CSD}) >>> [t_{CSD}]) *)

      (* Right-assoc inner, then left-assoc outer *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      (* [h] >>> ([sbm id si] >>> (L(Ff)_{CSD} >>> [t_{CSD}])) *)
      etransitivity. { symmetry. apply cassoc. }
      (* ([h] >>> [sbm id si]) >>> (L(Ff)_{CSD} >>> [t_{CSD}]) *)

      (* Fuse head: [h] >>> [sbm id si] *)
      etransitivity.
      { apply cprop. 2: reflexivity. apply pcomp. }
      (* [h'] >>> (L(Ff)_{CSD} >>> [t_{CSD}]) *)

      (* Left-associate to match target: ([h'] >>> L(Ff)_{CSD}) >>> [t_{CSD}] *)
      etransitivity. { symmetry. apply cassoc. }

      (* Now both sides: (_ >>> L(Ff)_{CSD}) >>> [t_{CSD}] *)
      apply cprop. 2: reflexivity. apply cprop. 2: reflexivity.
      pure_ext.
    - (* left_proper *)
      unfold Proper, respectful; intros.
      apply cprop. 1: reflexivity.
      apply cprop. 2: reflexivity.
      apply lprop. assumption.
  Qed.

End StateArrowTChoiceLaws.
