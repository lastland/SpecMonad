From Coq Require Import FunctionalExtensionality Morphisms RelationClasses.
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

  Local Lemma pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) ->
    @arrow_eq arr HE A B (@arr_pure arr HA _ _ f) (@arr_pure arr HA _ _ g).
  Proof.
    intro H. replace g with f by (extensionality x; apply H). reflexivity.
  Qed.

  Local Ltac destruct_sums :=
    repeat match goal with
    | [ x : (_ + _)%type |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x
    | [ x : unit |- _ ] => destruct x
    | [ x : (_ * _)%type |- _ ] => destruct x
    end.

  Local Ltac solve_pure_eq :=
    apply pure_ext; intro x; destruct_sums;
    unfold sum_bimap, to_sum, opt_rearrange, assoc_sum, swap_sum,
           collapse, sequence_option, sum_prod_dist;
    try reflexivity.

  Local Ltac opt_unfold :=
    unfold arr_id, arr_comp, arr_pure, arr_first, arr_left,
           Arrow_optionArrT, ArrowChoice_optionArrT,
           arrow_eq, ArrowEq_optionArrT;
    fold (@arr_comp arr HA) (@arr_pure arr HA) (@arr_first arr HA)
         (@arr_left arr HA HC) (@arrow_eq arr HE).

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

  Definition rev_assoc {A B C} (x : A + (B + C)) : (A + B) + C :=
    match x with inl a => inl (inl a) | inr (inl b) => inl (inr b) | inr (inr c) => inr c end.

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
    admit.
  Admitted.

  #[global]
  Instance ArrowChoiceLaws_optionArrT : ArrowChoiceLaws (optionArrT arr).
  Proof.
    Local Transparent ArrowEq_optionArrT.
    constructor; intros; opt_unfold.
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
      (* Both sides reduce to [assoc] >>> L(Lf>>>[rr]) >>> [rr] using base lassoc + core *)
      admit.

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
      (* F(Lf>>>[rr]) >>> [combined_pure] *)
      (* combined = fun p => collapse(sbm(Some.spd)(id)(ts p))
         where p : option(B*D)... hmm, F(Lf>>>[rr]) maps (A+C)*D -> option(B+C)*D.
         Actually wait, F is arr_first. *)
      (* Actually after opt_unfold:
         arr_first_opt (arr_left_opt f) = F(Lf>>>[rr]) >>> [seq]
         where F = arr_first at base level, [seq] = [sequence_option].

         The full LHS is opt_comp (F_opt(L_opt f)) (opt_pure spd).
         F_opt g = F(g) >>> [seq].
         L_opt f = Lf >>> [rr].
         So F_opt(L_opt f) = F(Lf >>> [rr]) >>> [seq].

         opt_comp (F(Lf>>>[rr])>>>[seq]) ([Some.spd])
         = (F(Lf>>>[rr])>>>[seq]) >>> [ts] >>> L[Some.spd] >>> [c]

         This is right-associated: F(Lf>>>[rr]) >>> ([seq] >>> ([ts] >>> (L[Some.spd] >>> [c]))).

         After lpure and fusing pures, the tail [seq]>>>[ts]>>>L[Some.spd]>>>[c] becomes a combined pure.
         Let me compute this combined pure:

         seq : option(B+C) * D -> option((B+C)*D)
         ts : option((B+C)*D) -> (B+C)*D + unit
         L[Some.spd] via lpure = [sbm (Some.spd) id]
         c : option((B*D)+(C*D)) + unit -> option((B*D)+(C*D))

         For (Some(inl b), d):
           seq(Some(inl b), d) = Some(inl b, d)
           ts(Some(inl b, d)) = inl(inl b, d)
           sbm(Some.spd)(id)(inl(inl b, d)) = inl(Some(spd(inl b, d))) = inl(Some(inl(b,d)))
           c(inl(Some(inl(b,d)))) = Some(inl(b,d))

         For (Some(inr c0), d):
           seq = Some(inr c0, d), ts = inl(inr c0, d),
           sbm = inl(Some(spd(inr c0, d))) = inl(Some(inr(c0,d))),
           c = Some(inr(c0,d))

         For (None, d):
           seq = None, ts = inr tt, sbm = inr tt, c = None

         So combined: (optB+C)*D -> opt((B*D)+(C*D))
           (Some(inl b), d) -> Some(inl(b,d))
           (Some(inr c0), d) -> Some(inr(c0,d))
           (None, d) -> None

         This is [fun p => option_map spd (seq(fst p, snd p))]
         = [fun p => match fst p with Some x => Some(spd(x,snd p)) | None => None end]
         = [spd] >>> [seq] applied after some rearrangement.

         Hmm, this is getting complex. Let me try using fcomp and fldist directly.

         fcomp: F(f >>> g) = F(f) >>> F(g)
         fpure: F[f] = [fun (a,c) => (f a, c)]
         fldist: F(Lf) >>> [spd] = [spd] >>> L(Ff)

         So: F(Lf>>>[rr]) = F(Lf) >>> F[rr] = F(Lf) >>> [fun (p : (optB+C)*D) => (rr(fst p), snd p)]

         LHS = F(Lf) >>> F[rr] >>> [seq] >>> ... (tail pure)

         By fldist: F(Lf) >>> [spd] = [spd] >>> L(Ff).
         But F(Lf) is followed by F[rr], not [spd]. So I need to relate
         F[rr] >>> [seq] >>> tail to something involving [spd].
       *)
      admit.
  Admitted.

End GenericOptionArrTChoiceLaws.
