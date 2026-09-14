(** * Checked examples of SP arrows, transformer stacks, and equivalence. *)

From Coq Require Import Lia.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import
  SPostArr SPostArrEquiv.

(** A many-to-one pure arrow still has an angelic witness after conversion
    to the coupled presentation and back. *)
Example asp_roundtrip_many_to_one :
  getASP (asp_from_coupled (asp_to_coupled (arrASP (fun _ : bool => tt))))
    (eq true) tt.
Proof.
  rewrite asp_from_to. exists true. auto.
Qed.

(** The same well-formed pure arrow has a rejected demonic predecessor. *)
Example dslp_roundtrip_many_to_one :
  ~ getDSLP (dslp_from_coupled (dslp_to_coupled (arrDSLP (fun _ : bool => tt))))
      (eq true) tt.
Proof.
  rewrite dslp_from_to, arrDSLP_spec. intro H.
  specialize (H false eq_refl). discriminate.
Qed.

Example empty_domain :
  ~ getASP (arrASP (fun _ : Empty_set => tt)) (fun _ => False) tt /\
    getDSLP (arrDSLP (fun _ : Empty_set => tt)) (fun _ => False) tt.
Proof.
  split.
  - rewrite arrASP_spec. intros [[] _].
  - rewrite arrDSLP_spec. intros [].
Qed.

Example unreachable_output :
  ~ getASP (arrASP (fun _ : bool => true)) (eq true) false /\
    getDSLP (arrDSLP (fun _ : bool => true)) (eq true) false.
Proof.
  split.
  - rewrite arrASP_spec. intros [u [_ H]]. discriminate.
  - rewrite arrDSLP_spec. intros u H. discriminate.
Qed.

Example option_asp_failure (r : option nat) :
  getASP (@arr_comp optionASPArr Arrow_optionASPArr _ _ _
    (arrASP (fun _ : nat => @None nat))
    (@arr_pure optionASPArr Arrow_optionASPArr _ _ S)) (eq 3) r <-> r = None.
Proof.
  rewrite optionASP_comp_spec, optionASP_pure_spec. split.
  - intros [[_ Hr]|[b [[a [_ H]] _]]]; [exact Hr | discriminate].
  - intro Hr. left. split; [apply arrASP_spec; exists 3; auto | exact Hr].
Qed.

Example option_dslp_failure (r : option nat) :
  getDSLP (@arr_comp optionDSLPArr Arrow_optionDSLPArr _ _ _
    (arrDSLP (fun _ : unit => @None nat))
    (@arr_pure optionDSLPArr Arrow_optionDSLPArr _ _ S)) (fun _ => False) r
  <-> r <> None.
Proof.
  rewrite optionDSLP_comp_spec, optionDSLP_pure_spec. split.
  - intros [H _] ->. exact (H eq_refl tt eq_refl).
  - intro H. split; [exact (fun Heq => False_rect _ (H Heq)) |].
    intros b _ u Heq. discriminate.
Qed.

Example option_choice_bypasses_failure :
  getASP (@arr_left optionASPArr Arrow_optionASPArr ArrowChoice_optionASPArr
    unit nat nat (arrASP (fun _ : unit => @None nat)))
    (eq (inr 7)) (Some (inr 7)) /\
  getDSLP (@arr_left optionDSLPArr Arrow_optionDSLPArr ArrowChoice_optionDSLPArr
    unit nat nat (arrDSLP (fun _ : unit => @None nat)))
    (eq (inr 7)) (Some (inr 7)).
Proof.
  split; cbn.
  - exists (inr 7). auto.
  - intros [[n|]|n] H; inversion H; reflexivity.
Qed.

Local Definition increment : ASPostArr nat unit :=
  arrASP (fun '(u, s) => Some (u, S s)).
Local Definition checked_double : ASPostArr nat unit :=
  arrASP (fun '(u, s) => if Nat.eqb s 4 then Some (u, 2 * s) else None).
Local Definition increment_then_double : ASPostArr nat unit :=
  @arr_comp (stateArrT nat optionASPArr) (Arrow_stateOptASP nat) _ _ _
    increment checked_double.

Create HintDb sp_state_example_ops.
#[local] Hint Unfold increment checked_double : sp_state_example_ops.

Example state_roundtrip_threads_updates (r : option (unit * nat)) :
  getASP (state_option_asp_from_coupled
    (state_option_asp_to_coupled increment_then_double)) (eq (tt, 3)) r
  <-> r = Some (tt, 8).
Proof.
  rewrite state_option_asp_from_to. unfold increment_then_double.
  rewrite stateOptASP_comp_spec. autounfold with sp_state_example_ops.
  rewrite !arrASP_spec. split.
  - intros [[[[u s] [_ H]] _]|[[u s] [[[u0 s0] [Hp Hs]] Hr]]]; [discriminate |].
    inversion Hp; subst. inversion Hs; subst. now symmetry.
  - intros ->. right. exists (tt, 4). split; [exists (tt, 3); auto | reflexivity].
Qed.

Example state_updated_guard_fails (r : option (unit * nat)) :
  getASP increment_then_double (eq (tt, 2)) r <-> r = None.
Proof.
  unfold increment_then_double. rewrite stateOptASP_comp_spec.
  autounfold with sp_state_example_ops. rewrite !arrASP_spec. split.
  - intros [[_ Hr]|[[u s] [[[u0 s0] [Hp Hs]] Hr]]]; [exact Hr |].
    inversion Hp; subst. inversion Hs; subst. now symmetry.
  - intros ->. right. exists (tt, 3). split; [exists (tt, 2); auto | reflexivity].
Qed.

Local Notation coupled_state_arrow :=
  (@Arrow_stateArrT nat CoupledSP.optionASPArr
    (@Arrow_optionArrT CoupledSP.PureRelASPPairArr
      CoupledSP.Arrow_PureRelASPPairArr CoupledSP.ArrowChoice_PureRelASPPairArr)).

(** The coupled presentation registers no per-stack dictionaries; the
    application dictionary is the generic transformer instance applied
    to the coupled base arrows. *)
Local Notation coupled_state_apply :=
  (@ArrowApply_stateArrT nat CoupledSP.optionASPArr
     (@Arrow_optionArrT CoupledSP.PureRelASPPairArr
       CoupledSP.Arrow_PureRelASPPairArr CoupledSP.ArrowChoice_PureRelASPPairArr)
     (@ArrowApply_optionArrT CoupledSP.PureRelASPPairArr
       CoupledSP.Arrow_PureRelASPPairArr CoupledSP.ArrowChoice_PureRelASPPairArr
       CoupledSP.ArrowApply_PureRelASPPairArr)).

Example state_application_conversion :
  getASP (state_option_asp_from_coupled
    (@arr_comp _ coupled_state_arrow _ _ _
      (@arr_pure _ coupled_state_arrow _ _
        (fun '(f, a) => (state_option_asp_to_coupled f, a)))
      (@arr_app _ coupled_state_arrow coupled_state_apply
        unit unit))) (eq ((increment_then_double, tt), 3)) (Some (tt, 8)).
Proof.
  rewrite <- (morphism_app (state_option_asp_to_coupled_morphism nat)),
    state_option_asp_from_to.
  apply stateOptASP_app_spec. exists increment_then_double.
  pose proof (proj2 (state_roundtrip_threads_updates (Some (tt, 8))) eq_refl) as H.
  rewrite state_option_asp_from_to in H. eapply ASP_monotone; [|exact H].
  intros [u s] Heq. inversion Heq. reflexivity.
Qed.

Example asp_higher_order_precompose :
  getASP (compASP
    (firstASP (arrASP (fun f : PureASPostArr nat nat => compASP (arrASP S) f)))
    appASP) (eq (arrASP (fun n => 2 * n), 3)) 8.
Proof.
  rewrite (@app_precompose _ Arrow_PureASPostArr ArrowApply_PureASPostArr
    ArrowEq_PureASPostArr ArrowApplyLaws_PureASPostArr),
    compASP_spec, appASP_spec.
  exists (arrASP (fun n => 2 * n)). apply arrASP_spec.
  exists 4. split; [|reflexivity]. unfold arr_second. cbn.
  exists (4, arrASP (fun n => 2 * n)). split; [|reflexivity].
  exists 3. split; [|reflexivity].
  exists (arrASP (fun n => 2 * n), 3). auto.
Qed.

Example dslp_higher_order_postcompose :
  getDSLP (compDSLP (arrDSLP (fun n => (arrDSLP S, n)))
    (compDSLP (firstDSLP (arrDSLP (fun f : PureDSLPostArr nat nat =>
      compDSLP f (arrDSLP (fun n => 2 * n))))) appDSLP)) (eq 3) 8.
Proof.
  change (getDSLP (arr_comp (arr_pure (fun n => (arrDSLP S, n)))
    (arr_comp (arr_first (arr_pure (fun f : PureDSLPostArr nat nat =>
      arr_comp f (arrDSLP (fun n => 2 * n))))) arr_app)) (eq 3) 8).
  rewrite (@app_postcompose _ Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr
    ArrowEq_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr).
  rewrite <- (@comp_assoc _ Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr
    ArrowLaws_PureDSLPostArr).
  rewrite (@app_law _ Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr
    ArrowEq_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr).
  rewrite compDSLP_spec, arrDSLP_spec. intros n Hn.
  apply arrDSLP_spec. intros a Ha. lia.
Qed.

Example higher_order_captures_input :
  getASP (compASP (firstASP (arrASP
    (fun x : bool => arrASP (fun y : nat => (x, y))))) appASP)
    (eq (true, 3)) (true, 3) /\
  getDSLP (compDSLP (firstDSLP (arrDSLP
    (fun x : bool => arrDSLP (fun y : nat => (x, y))))) appDSLP)
    (eq (true, 3)) (true, 3).
Proof.
  rewrite (@app_unit _ Arrow_PureASPostArr ArrowApply_PureASPostArr
    ArrowEq_PureASPostArr ArrowApplyLaws_PureASPostArr),
    (@app_unit _ Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr
      ArrowEq_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr). split; cbn.
  - exists (true, 3). auto.
  - intros p ->. reflexivity.
Qed.

Example pure_choice_active_branch :
  getASP (@leftASP bool bool nat (arrASP negb)) (eq (inl true)) (inl false) /\
  getDSLP (@leftDSLP bool bool nat (arrDSLP negb)) (eq (inl true)) (inl false).
Proof.
  rewrite leftASP_spec, leftDSLP_spec, arrASP_spec, arrDSLP_spec. split.
  - exists true. auto.
  - intros [] H; [reflexivity | discriminate].
Qed.

Example converted_state_composition :
  getASP (state_option_asp_from_coupled
    (@arr_comp _ coupled_state_arrow _ _ _
      (state_option_asp_to_coupled increment)
      (state_option_asp_to_coupled checked_double))) (eq (tt, 3)) (Some (tt, 8)).
Proof.
  rewrite <- (morphism_comp (state_option_asp_to_coupled_morphism nat)).
  apply state_roundtrip_threads_updates. reflexivity.
Qed.

Example dslp_state_roundtrip_preserves_state :
  getDSLP (state_option_dslp_from_coupled (state_option_dslp_to_coupled
    (@arr_pure (stateArrT nat optionDSLPArr) (Arrow_stateOptDSLP nat) nat nat S)))
    (eq (3, 7)) (Some (4, 7)).
Proof.
  rewrite state_option_dslp_from_to, stateOptDSLP_pure_spec.
  intros a s H. inversion H. reflexivity.
Qed.
