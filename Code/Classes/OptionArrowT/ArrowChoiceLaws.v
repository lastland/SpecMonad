From Coq Require Import FunctionalExtensionality Morphisms.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Classes.OptionArrowT Require Import Core.

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

  Local Lemma pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro H. replace g with f by (extensionality x; apply H). reflexivity.
  Qed.

  Definition rev_assoc {A B C} (x : A + (B + C)) : (A + B) + C :=
    match x with inl a => inl (inl a) | inr (inl b) => inl (inr b) | inr (inr c) => inr c end.

  Create HintDb opt_choice_ops.
  #[local] Hint Unfold sum_bimap to_sum opt_rearrange assoc_sum swap_sum
    collapse sequence_option sum_prod_dist rev_assoc : opt_choice_ops.

  Local Ltac solve_pure_eq :=
    apply pure_ext; intro x;
    repeat match goal with
    | [ x : (_ + _)%type |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x
    | [ x : unit |- _ ] => destruct x
    | [ x : (_ * _)%type |- _ ] => destruct x
    end;
    autounfold with opt_choice_ops;
    try reflexivity.

  Local Lemma opt_tail_inl {B C} :
    @arrow_eq arr HE (option B) (option (B + C))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@to_sum B))
        (@arr_comp arr HA _ _ _
          (@arr_left arr HA HC _ _ _ (@arr_pure arr HA _ _ (fun b => @Some (B+C) (inl b))))
          (@arr_pure arr HA _ _ (@collapse (B+C)))))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@inl (option B) C))
        (@arr_pure arr HA _ _ (@opt_rearrange B C))).
  Proof.
    etransitivity.
    { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity. apply lpure. }
    etransitivity.
    { etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
      apply pcomp. }
    symmetry. etransitivity. { apply pcomp. }
    apply pure_ext. intros [?|]; reflexivity.
  Qed.

  Local Lemma opt_head_sinl {A C} :
    @arrow_eq arr HE A ((A+C)+unit)
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (fun a => @Some (A+C) (inl a)))
        (@arr_pure arr HA _ _ (@to_sum (A+C))))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@inl A C))
        (@arr_pure arr HA _ _ (@inl (A+C) unit))).
  Proof.
    etransitivity. { apply pcomp. }
    symmetry. etransitivity. { apply pcomp. } reflexivity.
  Qed.

  Local Lemma opt_head_sinr {A C} :
    @arrow_eq arr HE C ((A+C)+unit)
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (fun c0 : C => @Some (A+C) (inr c0)))
        (@arr_pure arr HA _ _ (@to_sum (A+C))))
      (@arr_comp arr HA _ _ _
        (@arr_pure arr HA _ _ (@inr A C))
        (@arr_pure arr HA _ _ (@inl (A+C) unit))).
  Proof.
    etransitivity. { apply pcomp. }
    symmetry. etransitivity. { apply pcomp. } reflexivity.
  Qed.

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
      etransitivity.
      { exact (@pcomp
          ((option C + unit) + D)%type
          (option C + (unit + D))%type
          ((option C + unit) + D)%type
          (@assoc_sum (option C) unit D) (@rev_assoc (option C) unit D)). }
      apply pure_ext. intros [[?|[]]|?]; reflexivity. }
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
        etransitivity.
        { exact (@pcomp
            (option C + (unit + D))%type
            (option C + (D + unit))%type
            (option C + (unit + D))%type
            (fun x : option C + (unit + D) =>
              sum_bimap (fun c0 : option C => c0)
                (fun y : unit + D => match y with inl u => @inr D unit u | inr d => @inl D unit d end) x)
            (fun x : option C + (D + unit) =>
              sum_bimap (fun c0 : option C => c0)
                (fun y : D + unit => match y with inl d => @inr unit D d | inr u => @inl unit D u end) x)). }
        apply pure_ext. intros [?|[[]|?]]; reflexivity. }
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
      etransitivity.
      { exact (@pcomp
          ((option C + D) + unit)%type
          (option C + (D + unit))%type
          ((option C + D) + unit)%type
          (@assoc_sum (option C) D unit) (@rev_assoc (option C) D unit)). }
      apply pure_ext. intros [[?|?]|[]]; reflexivity. }
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
      setoid_rewrite lpure. setoid_rewrite pcomp. solve_pure_eq.

    - (* 2. left_comp *)
      etransitivity.
      { apply cprop. 2: reflexivity. apply lcomp. }
      etransitivity. { apply cassoc. }
      symmetry. etransitivity. { apply cassoc. } symmetry.
      apply cprop. 1: reflexivity. apply core_opt_left.

    - (* 3. left_inl *)
      etransitivity. { apply cprop. 1: reflexivity. exact opt_tail_inl. }
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply linl. }
      etransitivity. { apply cassoc. }
      symmetry.
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. exact opt_head_sinl. }
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. symmetry. apply linl. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity.
        { apply cprop. 1: reflexivity. apply pure_ext. intro. reflexivity. }
        apply cidr. }
      reflexivity.

    - (* 4. left_assoc *)
      (* Both sides reduce to [assoc] >>> L_{C+D}(f) >>> [rr_{B(C+D)}].
         LHS: (L_D(L_C(f)>>>[rr])>>>[rr]) >>> [ts] >>> L_1([Some.assoc]) >>> [c]
         RHS: [Some.assoc] >>> [ts] >>> L_1(L_{C+D}(f)>>>[rr]) >>> [c] *)

      (* === LHS: decompose L_D(L_C(f)>>>[rr]) via lcomp+lpure === *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        apply cprop. 2: reflexivity.
        etransitivity. { apply lcomp. }
        apply cprop. 1: reflexivity. apply lpure. }
      (* (L_D(L_C f) >>> [sbm rr id] >>> [rr]) >>> [ts] >>> L_1([Some.assoc]) >>> [c] *)

      (* Simplify L_1([Some.assoc]) via lpure *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply lpure. }
      (* (L_D(L_C f) >>> [sbm rr id] >>> [rr]) >>> [ts] >>> [sbm(Some.assoc) id] >>> [c] *)

      (* Assert LHS = [assoc]>>>L_{C+D}(f)>>>[rr] *)
      (* Step 1: right-associate ((A>>>B)>>>C)>>>(D>>>(E>>>F)) to A>>>(B>>>C>>>D>>>E>>>F) *)
      etransitivity. { apply cassoc. }
      etransitivity. { apply cassoc. }
      (* L_D(L_C f) >>> ([sbm rr id] >>> [rr]) >>> [ts] >>> [sbm(...) id] >>> [c] *)
      (* Step 2: fuse [sbm rr id] >>> [rr] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* L_D(L_C f) >>> [rr.sbm] >>> [ts] >>> [sbm(...) id] >>> [c] *)
      (* Step 3: fuse [rr.sbm] >>> [ts] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* L_D(L_C f) >>> [ts.rr.sbm] >>> [sbm(...) id] >>> [c] *)
      (* Step 4: fuse [ts.rr.sbm] >>> [sbm(...) id] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* L_D(L_C f) >>> [fused4] >>> [c] *)
      (* Step 5: fuse [fused4] >>> [c] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply pcomp. }
      (* L_D(L_C f) >>> [fused5] *)

      (* Assert: fused5 = assoc >>> rr *)
      assert (Hpe_lhs : forall x : (option B + C) + D,
        (fun x0 : (option B + C) + D =>
          collapse
            (sum_bimap (fun a : (B + C) + D => Some (assoc_sum a))
               (fun c0 : unit => c0)
               (to_sum
                  (opt_rearrange
                     (sum_bimap (@opt_rearrange B C) (fun d : D => d) x0))))) x
        = (fun x0 : (option B + C) + D =>
            @opt_rearrange B (C + D) (@assoc_sum (option B) C D x0)) x).
      { intros [[[?|]|?]|?]; reflexivity. }

      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { apply pure_ext. exact Hpe_lhs. }
        symmetry. apply pcomp. }
      (* L_D(L_C f) >>> [assoc] >>> [rr_{B(C+D)}] *)

      (* Apply lassoc_law *)
      etransitivity.
      { symmetry. apply cassoc. }
      etransitivity.
      { apply cprop. 2: reflexivity. apply lassoc_law. }
      etransitivity. { apply cassoc. }
      (* LHS = [assoc] >>> L_{C+D}(f) >>> [rr_{B(C+D)}] *)

      (* === RHS === *)
      symmetry.
      (* [Some.assoc] >>> [ts] >>> L_1(L_{C+D}(f)>>>[rr]) >>> [c] *)

      (* Fuse [Some.assoc] >>> [ts] *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }

      (* Goal: [ts.Some.assoc] >>> L_1(h) >>> [c] = [assoc] >>> h
         where h = L_{C+D}(f) >>> [rr] *)

      (* Step 1: replace [ts.Some.assoc] with [assoc]>>>[inl] *)
      assert (Hpe_rhs_head : forall x : (A + C) + D,
        (fun x0 : (A + C) + D =>
          @to_sum (A + (C + D)) (Some (@assoc_sum A C D x0))) x
        = (fun x0 : (A + C) + D =>
            @inl (A + (C + D)) unit (@assoc_sum A C D x0)) x).
      { intros [[?|?]|?]; reflexivity. }

      etransitivity.
      { apply cprop. 2: reflexivity.
        etransitivity. { apply pure_ext. exact Hpe_rhs_head. }
        symmetry. apply pcomp. }
      (* [assoc] >>> [inl] >>> L_1(h) >>> [c] *)

      (* Step 2: use linl reversed: [inl]>>>L_1(h) = h>>>[inl] *)
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity.
        symmetry. apply linl. }
      (* [assoc] >>> h >>> [inl] >>> [c] *)

      (* [assoc] >>> (h>>>[inl]) >>> [c]  where h = L(f)>>>[rr] *)

      (* Step 3: right-associate: (h>>>[inl])>>>[c] -> h>>>([inl]>>>[c]) *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      (* [assoc] >>> h >>> ([inl]>>>[c]) *)

      (* Step 4: fuse [inl]>>>[c] into id *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
      (* [assoc] >>> h >>> [collapse.inl] = [assoc] >>> h >>> [id] *)

      (* Step 5: [collapse.inl] = id, so h >>> [id] = h *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity.
        { apply cprop. 1: reflexivity.
          apply pure_ext. intro x. reflexivity. }
        apply cidr. }
      (* [assoc] >>> h = [assoc] >>> L(f) >>> [rr] *)
      reflexivity.

    - (* 5. left_inr *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. exact opt_head_sinr. }
      etransitivity. { apply cassoc. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. symmetry. apply linl. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      (* [inr] >>> (Lf >>> [rr]) >>> [inl] >>> [c]
         = [inr] >>> Lf >>> [rr] >>> [inl] >>> [c] (right-assoc) *)
      (* Need to handle: [inr] >>> (Lf>>>[rr]) >>> ([inl]>>>[c])
         where [inl]>>>[c] is a sub-composition.
         First fuse [inl]>>>[c] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
      (* [inr] >>> (Lf>>>[rr]) >>> [c.inl] where c(inl x)=x *)
      (* Now [rr] >>> [c.inl] is Lf >>> [rr] >>> [c.inl] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { apply cassoc. }
        apply cprop. 1: reflexivity. apply pcomp. }
      (* [inr] >>> Lf >>> [rr . c.inl] *)
      (* linr: [inr] >>> Lf = [inr] *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply linr. }
      (* [inr] >>> [rr . c.inl] *)
      etransitivity. { apply pcomp. }
      solve_pure_eq.

    - (* 6. left_natural *)
      (* LHS: (Lf>>>[rr_BC]) >>> [ts_BC] >>> L[Some.sbm id g] >>> [c_BD] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply lpure. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
        apply pcomp. }
      (* (Lf>>>[rr_BC]) >>> [combined] *)
      etransitivity.
      { etransitivity. { apply cassoc. }
        apply cprop. 1: reflexivity. apply pcomp. }
      (* Lf >>> [combined2] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity.
        { assert (Hfeq : forall x : option B + C,
            (fun x0 => collapse (sum_bimap (fun a => Some (sum_bimap (fun b => b) g a)) (fun c0 : unit => c0) (to_sum (opt_rearrange x0)))) x
            = (fun x0 => opt_rearrange (sum_bimap (fun ob : option B => ob) g x0)) x).
          { intros [[?|]|?]; reflexivity. }
          replace (fun x : option B + C => collapse (sum_bimap (fun a => Some (sum_bimap (fun b => b) g a)) (fun c0 : unit => c0) (to_sum (opt_rearrange x)))) with (fun x => opt_rearrange (sum_bimap (fun ob : option B => ob) g x)).
          2: { extensionality x; symmetry; apply Hfeq. }
          reflexivity. }
        symmetry. apply pcomp. }
      (* Lf >>> ([sbm id g] >>> [rr_BD]) *)
      etransitivity. { symmetry. apply cassoc. }
      etransitivity. { apply cprop. 2: reflexivity. apply lnat. }
      etransitivity. { apply cassoc. }
      (* [sbm id g]_A >>> Lf_D >>> [rr_BD] *)

      (* RHS: [Some.sbm id g] >>> [ts_AD] >>> L(Lf>>>[rr_BD]) >>> [c] *)
      symmetry.
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* [inl . sbm id g] >>> L(Lf>>>[rr_BD]) >>> [c] *)
      etransitivity.
      { apply cprop. 2: reflexivity.
        symmetry. apply (pcomp (sum_bimap (fun a : A => a) g) (@inl (A+D) unit)). }
      (* ([sbm id g]_A >>> [inl]) >>> L(Lf>>>[rr_BD]) >>> [c] *)
      etransitivity. { apply cassoc. }
      (* [sbm id g]_A >>> [inl] >>> L(Lf>>>[rr_BD]) >>> [c] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. symmetry. apply linl. }
      etransitivity. { apply cprop. 1: reflexivity. apply cassoc. }
      (* [sbm id g]_A >>> (Lf>>>[rr_BD]) >>> [inl] >>> [c] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity.
        { apply cprop. 1: reflexivity. apply pure_ext. intro. reflexivity. }
        apply cidr. }
      reflexivity.

    - (* 7. first_left_dist *)
      (* F(Lf>>>[rr]) >>> [seq] >>> [ts] >>> L[Some.spd] >>> [c]
         = [Some.spd] >>> [ts] >>> L(Ff >>> [seq]) >>> [c]

         LHS: use fcomp to decompose F(Lf>>>[rr]) = F(Lf) >>> F[rr].
              Use fpure on F[rr].
              Use fldist on F(Lf) >>> [spd]... but [spd] is not adjacent to F(Lf) in LHS.
              The LHS is F(Lf>>>[rr]) >>> [seq] >>> ... which is opt_first applied to opt_left f.

         RHS: [Some.spd] >>> [ts] >>> L(Ff >>> [seq]) >>> [c].

         Strategy: both reduce to [spd] >>> L(Ff) >>> [seq_new] using fldist + pure fusions.
       *)
      (* LHS: F(Lf>>>[rr]) >>> [seq] >>> [ts] >>> L[Some.spd] >>> [c] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity.
        apply cprop. 2: reflexivity. apply lpure. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        etransitivity. { apply cprop. 2: reflexivity. apply pcomp. }
        apply pcomp. }
      (* Goal after previous lpure+pcomp fusions:
         (F(Lf>>>[rr])>>>[seq]) >>> [fused_tail] = [Some.spd]>>>[ts]>>>L(L(Ff>>>[seq])>>>[rr])>>>[c]
         where fused_tail = fun x => collapse(sbm(Some.spd)(id)(ts x)).

         Strategy: both sides reduce to [spd] >>> L(Ff) >>> [sbm seq id] >>> [rr].
         LHS: fcomp + fpure + pure fusions + fldist.
         RHS: pcomp fusions + linl + lcomp + lpure. *)

      (* === LHS: (F(Lf>>>[rr])>>>[seq]) >>> [fused_tail] === *)

      (* Assert: the 3-pure tail F[rr]>>>[seq]>>>[fused_tail] = [spd]>>>[sbm seq id]>>>[rr].
         After fpure, the structure is right-associated:
         [fun '(a,c)=>(rr a,c)] >>> ([seq] >>> [fused_tail]) *)
      assert (Hpure_chain : @arrow_eq arr HE
        ((option B + C) * D)%type (option (B * D + C * D))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (fun '(a, c) => (opt_rearrange a, c)))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _ sequence_option)
            (@arr_pure arr HA _ _
              (fun x : option ((B + C) * D) =>
                collapse
                  (sum_bimap (fun a : (B + C) * D => Some (sum_prod_dist a))
                     (fun c0 : unit => c0) (to_sum x))))))
        (@arr_comp arr HA _ _ _
          (@arr_pure arr HA _ _ (@sum_prod_dist (option B) C D))
          (@arr_comp arr HA _ _ _
            (@arr_pure arr HA _ _
              (fun x : (option B * D) + (C * D) =>
                sum_bimap sequence_option (fun cd : C * D => cd) x))
            (@arr_pure arr HA _ _ (@opt_rearrange (B * D) (C * D)))))).
      { (* Fuse LHS: [pair_rr]>>>([seq]>>>[fused_tail]) into single pure *)
        etransitivity.
        { apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity. { apply pcomp. }
        (* Fuse RHS: [spd]>>>([sbm seq id]>>>[rr]) into single pure *)
        symmetry.
        etransitivity.
        { apply cprop. 1: reflexivity. apply pcomp. }
        etransitivity. { apply pcomp. }
        apply pure_ext. intros [[[?|]|?] ?]; reflexivity. }

      (* Step 1: right-associate LHS *)
      etransitivity. { apply cassoc. }

      (* Step 2: fcomp *)
      etransitivity.
      { apply cprop. 2: reflexivity. apply fcomp. }

      (* Step 3: right-associate *)
      etransitivity. { apply cassoc. }

      (* Step 4: fpure on F[rr] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity. apply fpure. }

      (* Step 5: rewrite F[rr]>>>[seq]>>>[fused_tail] using Hpure_chain *)
      etransitivity.
      { apply cprop. 1: reflexivity. exact Hpure_chain. }
      (* F(Lf) >>> [spd] >>> [sbm seq id] >>> [rr] *)

      (* Step 6: left-associate to apply fldist *)
      etransitivity.
      { symmetry. apply cassoc. }
      (* (F(Lf) >>> [spd]) >>> ([sbm seq id] >>> [rr]) *)

      (* Step 7: fldist on (F(Lf) >>> [spd]) *)
      etransitivity.
      { apply cprop. 2: reflexivity. apply fldist. }
      (* ([spd] >>> L(Ff)) >>> ([sbm seq id] >>> [rr]) *)

      (* Step 8: right-associate *)
      etransitivity. { apply cassoc. }
      (* [spd] >>> L(Ff) >>> ([sbm seq id] >>> [rr]) *)

      (* === RHS: [Some.spd]>>>[ts]>>>L(L(Ff>>>[seq])>>>[rr])>>>[c] === *)
      symmetry.

      (* Step R1: fuse [Some.spd]>>>[ts] into [ts.Some.spd] *)
      etransitivity.
      { etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. apply pcomp. }
      (* [ts.Some.spd] >>> L(h) >>> [c] *)

      (* Step R1b: assert ts(Some(spd x)) = inl(spd x), then split as [spd]>>>[inl] *)
      assert (Hpe_rhs_head : forall x : (A + C) * D,
        (fun x0 : (A + C) * D =>
          @to_sum ((A * D) + (C * D)) (Some (@sum_prod_dist A C D x0))) x
        = (fun x0 : (A + C) * D =>
            @inl ((A * D) + (C * D)) unit (@sum_prod_dist A C D x0)) x).
      { intros [[?|?] ?]; reflexivity. }

      etransitivity.
      { apply cprop. 2: reflexivity.
        etransitivity. { apply pure_ext. exact Hpe_rhs_head. }
        symmetry. apply pcomp. }
      (* ([spd] >>> [inl]) >>> L(h) >>> [c] *)
      etransitivity. { apply cassoc. }
      (* [spd] >>> [inl] >>> L(h) >>> [c] where h = L(Ff>>>[seq])>>>[rr] *)

      (* Step R2: linl: [inl]>>>L(h) = h>>>[inl] *)
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity. { symmetry. apply cassoc. }
        apply cprop. 2: reflexivity. symmetry. apply linl. }
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      (* [spd] >>> h >>> [inl] >>> [c] *)

      (* Step R3: fuse [inl]>>>[c] into [id], then cidr *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 1: reflexivity. apply pcomp. }
      etransitivity.
      { apply cprop. 1: reflexivity.
        etransitivity.
        { apply cprop. 1: reflexivity.
          apply pure_ext. intro x. reflexivity. }
        apply cidr. }
      (* [spd] >>> h where h = L(Ff>>>[seq])>>>[rr] *)

      (* Step R4: lcomp on L(Ff>>>[seq]) *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity. apply lcomp. }

      (* Step R5: lpure on L[seq] *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cprop. 2: reflexivity.
        apply cprop. 1: reflexivity. apply lpure. }

      (* Step R6: right-associate *)
      etransitivity.
      { apply cprop. 1: reflexivity. apply cassoc. }
      (* [spd] >>> L(Ff) >>> [sbm seq id] >>> [rr] *)

      reflexivity.
  Qed.

End GenericOptionArrTChoiceLaws.
