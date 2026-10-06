From Coq Require Import Morphisms.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.OptionArrowT Require Import Core ArrowLaws.

Section GenericOptionArrTChoiceLaws.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HC : @ArrowChoice arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
          `{HCL : @ArrowChoiceLaws arr HA HC HE}.

  Local Notation cassoc := (@comp_assoc arr HA HE HL).
  Local Notation cidl   := (@comp_id_l arr HA HE HL).
  Local Notation cidr   := (@comp_id_r arr HA HE HL).
  Local Notation pcomp  := (@pure_comp arr HA HE HL).
  Local Notation cprop  := (@comp_proper arr HA HE HL).
  Local Notation fpure  := (@first_pure arr HA HE HL).
  Local Notation fcomp  := (@first_comp arr HA HE HL).
  Local Notation fprop  := (@first_proper arr HA HE HL).
  Local Notation lpure  := (@left_pure arr HA HC HE HCL).
  Local Notation lcomp  := (@left_comp arr HA HC HE HCL).
  Local Notation linl   := (@left_inl arr HA HC HE HCL).
  Local Notation lassoc_law := (@left_assoc arr HA HC HE HCL).
  Local Notation linr   := (@left_inr arr HA HC HE HCL).
  Local Notation lnat   := (@left_natural arr HA HC HE HCL).
  Local Notation fldist := (@first_left_dist arr HA HC HE HCL).
  Local Notation lprop  := (@left_proper arr HA HC HE HCL).

  Definition rev_assoc {A B C} (x : A + (B + C)) : (A + B) + C :=
    match x with inl a => inl (inl a) | inr (inl b) => inl (inr b) | inr (inr c) => inr c end.

  Create HintDb opt_choice_ops.
  #[local] Hint Unfold sum_bimap to_sum opt_rearrange assoc_sum swap_sum
    collapse sequence_option sum_prod_dist rev_assoc : opt_choice_ops.

  Local Ltac solve_pure_eq :=
    apply (@Arrow.arr_pure_ext arr HA HE); intro x;
    repeat match goal with
    | [ x : (_ + _)%type |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x
    | [ x : unit |- _ ] => destruct x
    | [ x : (_ * _)%type |- _ ] => destruct x
    end;
    autounfold with opt_choice_ops;
    try reflexivity.

  (* Helper: decompose L_D(L_1(g)) via lassoc_law + lnat *)
  Local Lemma ll_decompose {B C D} (g : arr B (option C)) :
    @arrow_eq arr HE _ _
      (@arr_left arr HA HC _ _ D (@arr_left arr HA HC _ _ unit g))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@assoc_sum B unit D))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun x : B + (unit + D) =>
            sum_bimap (fun b : B => b)
              (fun y : unit + D => match y with inl u => @inr D unit u | inr d => @inl D unit d end) x))
          (@arr_comp arr HA _ _ _
            (@arr_left arr HA HC _ _ (D + unit) g)
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (fun x : option C + (D + unit) =>
                sum_bimap (fun c0 : option C => c0)
                  (fun y : D + unit => match y with inl d => @inr unit D d | inr u => @inl unit D u end) x))
              (@arr_pure arr HA _ _ (@rev_assoc (option C) unit D)))))).
  Proof.
    etransitivity. { symmetry. apply cidr. }
    etransitivity.
    { apply cprop. 1: reflexivity.
      symmetry. unfold arr_id.
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)
          ((option C + unit) + D)%type
          (option C + (unit + D))%type
          ((option C + unit) + D)%type
          (@assoc_sum (option C) unit D) (@rev_assoc (option C) unit D) _).
      intros [[?|[]]|?]; reflexivity. }
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. apply lassoc_law. }
    etransitivity. { apply cassoc. }
    etransitivity.
    { apply cprop. 1: reflexivity.
      etransitivity.
      { apply cprop. 2: reflexivity.
        etransitivity. { symmetry. apply cidr. }
        apply cprop. 1: reflexivity.
        symmetry. unfold arr_id.
        apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)
            (option C + (unit + D))%type
            (option C + (D + unit))%type
            (option C + (unit + D))%type
            (fun x : option C + (unit + D) =>
              sum_bimap (fun c0 : option C => c0)
                (fun y : unit + D => match y with inl u => @inr D unit u | inr d => @inl D unit d end) x)
            (fun x : option C + (D + unit) =>
              sum_bimap (fun c0 : option C => c0)
                (fun y : D + unit => match y with inl d => @inr unit D d | inr u => @inl unit D u end) x) _).
        intros [?|[[]|?]]; reflexivity. }
      etransitivity.
      { apply cprop. 2: reflexivity. symmetry. apply cassoc. }
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply (lnat g (fun x : unit + D => match x with inl u => @inr D unit u | inr d => @inl D unit d end)). }
      apply cassoc. }
    reflexivity.
  Qed.

  (* Similar decomposition for L_1(L_D(g)) *)
  Local Lemma ll_decompose2 {B C D} (g : arr B (option C)) :
    @arrow_eq arr HE _ _
      (@arr_left arr HA HC _ _ unit (@arr_left arr HA HC _ _ D g))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@assoc_sum B D unit))
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ (D + unit) g)
          (@arr_pure arr HA _ _ (@rev_assoc (option C) D unit)))).
  Proof.
    etransitivity. { symmetry. apply cidr. }
    etransitivity.
    { apply cprop. 1: reflexivity.
      symmetry. unfold arr_id.
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)
          ((option C + D) + unit)%type
          (option C + (D + unit))%type
          ((option C + D) + unit)%type
          (@assoc_sum (option C) D unit) (@rev_assoc (option C) D unit) _).
      intros [[?|?]|[]]; reflexivity. }
    etransitivity. { symmetry. apply cassoc. }
    etransitivity. { apply cprop. 2: reflexivity. apply lassoc_law. }
    apply cassoc.
  Qed.

  Local Lemma core_opt_left {B C D} (g : arr B (option C)) :
    @arrow_eq arr HE (option B + D) (option (C + D))
      (@arr_comp arr HA _ _ _
        (@arr_left arr HA HC _ _ D
          (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ (@to_sum B))
            (@arr_comp arr HA _ _ _
              (@arr_left arr HA HC _ _ unit g)
              (@arr_pure arr HA _ _ (@collapse C)))))
        (@arr_pure arr HA _ _ (@opt_rearrange C D)))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@opt_rearrange B D))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@to_sum (B + D)))
          (@arr_comp arr HA _ _ _
            (@arr_left arr HA HC _ _ unit
              (@arr_comp arr HA _ _ _
                (@arr_left arr HA HC _ _ D g)
                (@arr_pure arr HA _ _ (@opt_rearrange C D))))
            (@arr_pure arr HA _ _ (@collapse (C + D)))))).
  Proof.
    (* Both sides reduce to [p]>>>L_{D+1}(g)>>>[q] using lcomp, lpure,
       ll_decompose/ll_decompose2, and pcomp fusions. *)

    (* LHS: L_D([ts]>>>L_1(g)>>>[c]) >>> [rr] *)
    (* = [sbm ts id] >>> L_D(L_1 g) >>> [sbm c id] >>> [rr]  by lcomp+lpure *)

    (* Assert LHS = [head_L] >>> L_{D+1}(g) >>> [tail_L] *)
    assert (HLHS : @arrow_eq arr HE (option B + D) (option (C + D))
      (@arr_comp arr HA _ _ _
        (@arr_left arr HA HC _ _ D
          (@arr_comp arr HA _ _ _ (@arr_pure arr HA _ _ (@to_sum B))
            (@arr_comp arr HA _ _ _
              (@arr_left arr HA HC _ _ unit g)
              (@arr_pure arr HA _ _ (@collapse C)))))
        (@arr_pure arr HA _ _ (@opt_rearrange C D)))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (fun x : option B + D => sum_bimap (@to_sum B) (fun d : D => d) x))
        (@arr_comp arr HA _ _ _
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@assoc_sum B unit D))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (fun x : B + (unit + D) =>
                sum_bimap (fun b : B => b)
                  (fun y : unit + D => match y with inl u => @inr D unit u | inr d => @inl D unit d end) x))
              (@arr_comp arr HA _ _ _
                (@arr_left arr HA HC _ _ (D + unit) g)
                (@arr_comp arr HA _ _ _
                  (@arr_pure arr HA _ _ (fun x : option C + (D + unit) =>
                    sum_bimap (fun c0 : option C => c0)
                      (fun y : D + unit => match y with inl d => @inr unit D d | inr u => @inl unit D u end) x))
                  (@arr_pure arr HA _ _ (@rev_assoc (option C) unit D))))))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (fun x : (option C + unit) + D => sum_bimap (@collapse C) (fun d : D => d) x))
            (@arr_pure arr HA _ _ (@opt_rearrange C D)))))).
    { etransitivity.
      { apply cprop. 2: reflexivity.
        etransitivity. { apply lcomp. }
        etransitivity. { apply cprop. 2: reflexivity. apply lpure. }
        apply cprop. 1: reflexivity.
        etransitivity. { apply lcomp. }
        apply cprop. 1: reflexivity. apply lpure. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      apply cprop. 1: reflexivity.
      apply cprop. 2: reflexivity.
      apply (ll_decompose g). }

    (* Assert RHS = [head_R] >>> L_{D+1}(g) >>> [tail_R] *)
    assert (HRHS : @arrow_eq arr HE (option B + D) (option (C + D))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@opt_rearrange B D))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@to_sum (B + D)))
          (@arr_comp arr HA _ _ _
            (@arr_left arr HA HC _ _ unit
              (@arr_comp arr HA _ _ _
                (@arr_left arr HA HC _ _ D g)
                (@arr_pure arr HA _ _ (@opt_rearrange C D))))
            (@arr_pure arr HA _ _ (@collapse (C + D))))))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@opt_rearrange B D))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@to_sum (B + D)))
          (@arr_comp arr HA _ _ _
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (@assoc_sum B D unit))
              (@arr_comp arr HA _ _ _
                (@arr_left arr HA HC _ _ (D + unit) g)
                (@arr_pure arr HA _ _ (@rev_assoc (option C) D unit))))
            (@arr_comp arr HA _ _ _
              (@arr_pure arr HA _ _ (fun x : (option C + D) + unit =>
                sum_bimap (@opt_rearrange C D) (fun u : unit => u) x))
              (@arr_pure arr HA _ _ (@collapse (C + D)))))))).
    { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
      (* focus: L_1(L_D(g)>>>[rr]) >>> [c] *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        etransitivity. { apply lcomp. }
        apply cprop. 1: reflexivity. apply lpure. }
      (* (L_1(L_D(g)) >>> [sbm rr id]) >>> [c] *)
      etransitivity. { apply cassoc. }
      (* L_1(L_D(g)) >>> [sbm rr id] >>> [c] *)
      apply cprop. 2: reflexivity.
      apply (ll_decompose2 g). }

    etransitivity. { exact HLHS. }
    symmetry. etransitivity. { exact HRHS. } symmetry.

    (* LHS side: [sbm ts id] >>> ([assoc]>>>[swap]>>>L(g)>>>([swap']>>>[rev])) >>> ([sbm c id]>>>[rr])
       Fuse [sbm ts id] >>> [assoc] >>> [swap] into one pure *)
    etransitivity.
    { etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. apply pcomp. }
    etransitivity.
    { apply cprop. 2: reflexivity.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. apply pcomp. }
    etransitivity. { apply cassoc. }
    (* [head3] >>> L(g) >>> ([swap']>>>[rev]) >>> ([sbm c id]>>>[rr]) *)

    (* Fuse tail: ([swap']>>>[rev]) >>> ([sbm c id]>>>[rr]) -> one pure
       Structure: (A>>>B) >>> (C>>>D)
       Use: pcomp to fuse A>>>B, pcomp to fuse C>>>D, then pcomp to fuse results *)
    etransitivity.
    { apply cprop. 1: reflexivity.
      etransitivity. { apply cassoc. }
      apply cprop. 1: reflexivity.
      etransitivity.
      { apply cprop. 2: reflexivity. apply pcomp. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply pcomp. }
      apply pcomp. }

    symmetry.

    (* RHS side: [rr]>>>[ts] >>> ([assoc']>>>L(g)>>>[rev']) >>> ([sbm rr id]>>>[c])
       = (([rr]>>>[ts]) >>> ([assoc']>>>L(g)>>>[rev'])) >>> ([sbm rr id]>>>[c])
       Fuse head: [rr]>>>[ts]>>>[assoc'] and tail: [rev']>>>([sbm rr id]>>>[c]) *)

    (* Fuse head: [rr]>>>[ts] then [rr_ts]>>>[assoc'] *)
    etransitivity.
    { etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. apply pcomp. }
    (* [rr_ts] >>> (([assoc']>>>L(g)>>>[rev']) >>> ([sbm rr id]>>>[c])) *)
    etransitivity.
    { etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. apply pcomp. }
    (* (([head_R] >>> L(g)) >>> [rev']) >>> ([sbm rr id]>>>[c]) *)

    (* Right-associate *)
    etransitivity. { apply cassoc. }
    etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
    (* [head_R] >>> L(g) >>> [rev'] >>> ([sbm rr id]>>>[c]) *)

    (* Fuse tail: [rev'] >>> [sbm rr id] >>> [c] — 3 pures *)
    etransitivity.
    { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
      etransitivity.
      { apply cprop. 1: reflexivity. apply pcomp. }
      apply pcomp. }

    apply cprop.
    + solve_pure_eq.
    + apply cprop. 1: reflexivity. solve_pure_eq.
  Qed.

  #[global]
  Instance ArrowChoiceLaws_optionArrT : ArrowChoiceLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros;
      unfold arr_id, arr_comp, arr_pure, arr_first, arr_left,
             Arrow_optionArrT, ArrowChoice_optionArrT,
             arrow_eq, ArrowEq_optionArrT;
      fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
           (@arr_left arr HA HC) (@arrow_eq arr HE).
    all: try (unfold Proper, respectful; intros;
              apply cprop; [apply lprop; assumption | reflexivity]).

    - (* 1. left_pure *)
      setoid_rewrite lpure.
      apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
      intros [a|c]; reflexivity.

    - (* 2. left_comp *)
      etransitivity.
      { apply cprop. 2: reflexivity. apply lcomp. }
      etransitivity. { apply cassoc. }
      symmetry. etransitivity. { apply cassoc. } symmetry.
      apply cprop. 1: reflexivity. apply core_opt_left.

    - (* 3. left_inl *)
      (* Both opt-level compositions with a pure reduce to base
         compositions via optionArrT_comp_pure_r/l; then [inl] >>> [rr]
         collapses to [option_map inl] and the base left_inl applies. *)
      etransitivity. { apply optionArrT_comp_pure_r. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      assert (Hfused : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@inl (option B) C))
          (@arr_pure arr HA _ _ (@opt_rearrange B C)))
        (@arr_pure arr HA _ _ (option_map (@inl B C)))).
      { apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
        intros [?|]; reflexivity. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. symmetry. apply linl. }
      etransitivity. { apply cassoc. }
      apply cprop. 1: reflexivity. exact Hfused.

    - (* 4. left_assoc *)
      (* Both opt-level compositions with a pure reduce to base
         compositions via optionArrT_comp_pure_r/l.  The LHS tail
         L_D [rr] >>> [rr] >>> [option_map assoc] collapses to
         [assoc] >>> [rr], and the base left_assoc law applies. *)
      etransitivity. { apply optionArrT_comp_pure_r. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry.
      assert (Hfused : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ D (@arr_pure arr HA _ _ (@opt_rearrange B C)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@opt_rearrange (B + C) D))
            (@arr_pure arr HA _ _ (option_map (@assoc_sum B C D)))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@assoc_sum (option B) C D))
          (@arr_pure arr HA _ _ (@opt_rearrange B (C + D))))).
      { etransitivity.
        { apply cprop. 2: reflexivity. apply lpure. }
        etransitivity.
        { apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity.
        { apply pcomp. }
        symmetry.
        apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
        intros [[[?|]|?]|?]; reflexivity. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply lcomp. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. exact Hfused. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply lassoc_law. }
      apply cassoc.

    - (* 5. left_inr *)
      (* Reduce to base composition, then [inr] >>> L f >>> [rr]
         collapses via linr and pcomp. *)
      etransitivity. { apply optionArrT_comp_pure_l. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply linr. }
      exact (@pure_comp arr HA HE HL C ((option B + C)%type) (option (B + C))
               (@inr (option B) C) (@opt_rearrange B C)).

    - (* 6. left_natural *)
      (* Both opt-level compositions with a pure reduce to base
         compositions via optionArrT_comp_pure_r/l; the tail
         [rr] >>> [option_map (sbm id g)] fuses into [sbm id g] >>> [rr],
         and the base left_natural law applies. *)
      etransitivity. { apply optionArrT_comp_pure_r. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry.
      assert (Hfused : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@opt_rearrange B C))
          (@arr_pure arr HA _ _
            (option_map (fun x => sum_bimap (fun b : B => b) g x))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _
            (fun x => sum_bimap (fun ob : option B => ob) g x))
          (@arr_pure arr HA _ _ (@opt_rearrange B D)))).
      { etransitivity. { apply pcomp. }
        symmetry.
        apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
        intros [[?|]|?]; reflexivity. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. exact Hfused. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply lnat. }
      apply cassoc.

    - (* 7. first_left_dist *)
      (* Both opt-level compositions with a pure reduce to base
         compositions via optionArrT_comp_pure_r/l.  The LHS tail
         F_D [rr] >>> [seq] >>> [option_map spd] collapses to
         [spd] >>> [sbm seq id] >>> [rr]; then fcomp and the base
         first_left_dist law apply. *)
      etransitivity. { apply optionArrT_comp_pure_r. }
      symmetry. etransitivity. { apply optionArrT_comp_pure_l. }
      symmetry.
      assert (Hfused : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_first arr HA _ _ D (@arr_pure arr HA _ _ (@opt_rearrange B C)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ (@sequence_option (B + C) D))
            (@arr_pure arr HA _ _ (option_map (@sum_prod_dist B C D)))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@sum_prod_dist (option B) C D))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun x : ((option B * D + C * D)%type) =>
                 sum_bimap (@sequence_option B D) (fun cd : C * D => cd) x))
            (@arr_pure arr HA _ _ (@opt_rearrange (B * D) (C * D)))))).
      { etransitivity.
        { apply cprop. 2: reflexivity. apply fpure. }
        etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity. { apply pcomp. }
        symmetry.
        etransitivity. { apply cprop. 1: reflexivity. apply pcomp. }
        apply (@Arrow.pure_comp_ext arr HA HE HL (@Arrow.arr_pure_ext arr HA HE)).
        intros [[[?|]|?] ?]; reflexivity. }
      (* L(Ff >>> [seq]) = L(Ff) >>> [sbm seq id] *)
      assert (Hl : @arrow_eq arr HE _ _
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ ((C * D)%type)
            (@arr_first arr HA _ _ D f))
          (@arr_pure arr HA _ _
            (fun x : ((option B * D + C * D)%type) =>
               sum_bimap (@sequence_option B D) (fun cd : C * D => cd) x)))
        (@arr_left arr HA HC _ _ ((C * D)%type)
          (@arr_comp arr HA _ _ _
            (@arr_first arr HA _ _ D f)
            (@arr_pure arr HA _ _ (@sequence_option B D))))).
      { etransitivity.
        { apply cprop. 1: reflexivity. symmetry. apply lpure. }
        symmetry. apply lcomp. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply fcomp. }
      etransitivity. { apply cassoc. }
      etransitivity. { apply cprop. 1: reflexivity. exact Hfused. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply fldist. }
      etransitivity. { apply cassoc. }
      apply cprop. 1: reflexivity.
      etransitivity. { symmetry. apply cassoc. }
      apply cprop. 2: reflexivity. exact Hl.
  Qed.

End GenericOptionArrTChoiceLaws.
