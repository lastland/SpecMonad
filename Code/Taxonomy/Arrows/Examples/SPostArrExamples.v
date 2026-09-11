(** * Checked examples of SP arrows, transformer stacks, and equivalence. *)

From Coq Require Import Lia.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.
From Incorrectness.Taxonomy.Arrows Require Import
  SPostArr SPostArrEquiv SPostArrCoherence.

(** A many-to-one pure arrow still has an angelic witness after conversion
    to the coupled presentation and back. *)
Example asp_roundtrip_many_to_one :
  getASP (asp_from_coupled (asp_to_coupled (pureASP (fun _ : bool => tt))))
    (eq true) tt.
Proof.
  rewrite asp_from_to. exists true. auto.
Qed.

(** The same well-formed pure arrow has a rejected demonic predecessor. *)
Example dslp_roundtrip_many_to_one :
  ~ getDSLP (dslp_from_coupled (dslp_to_coupled (pureDSLP (fun _ : bool => tt))))
      (eq true) tt.
Proof.
  rewrite dslp_from_to, pureDSLP_spec. intro H.
  specialize (H false eq_refl). discriminate.
Qed.

Example empty_domain :
  ~ getASP (pureASP (fun _ : Empty_set => tt)) (fun _ => False) tt /\
    getDSLP (pureDSLP (fun _ : Empty_set => tt)) (fun _ => False) tt.
Proof.
  split.
  - rewrite pureASP_spec. intros [[] _].
  - rewrite pureDSLP_spec. intros [].
Qed.

Example unreachable_output :
  ~ getASP (pureASP (fun _ : bool => true)) (eq true) false /\
    getDSLP (pureDSLP (fun _ : bool => true)) (eq true) false.
Proof.
  split.
  - rewrite pureASP_spec. intros [u [_ H]]. discriminate.
  - rewrite pureDSLP_spec. intros u H. discriminate.
Qed.

Example option_asp_failure (r : option nat) :
  getASP (@arr_comp optionASPArr Arrow_optionASPArr _ _ _
    (pureASP (fun _ : nat => @None nat))
    (@arr_pure optionASPArr Arrow_optionASPArr _ _ S)) (eq 3) r <-> r = None.
Proof.
  rewrite optionASP_comp_spec, optionASP_pure_spec. split.
  - intros [[_ Hr]|[b [[a [_ H]] _]]]; [exact Hr | discriminate].
  - intro Hr. left. split; [apply pureASP_spec; exists 3; auto | exact Hr].
Qed.

Example option_dslp_failure (r : option nat) :
  getDSLP (@arr_comp optionDSLPArr Arrow_optionDSLPArr _ _ _
    (pureDSLP (fun _ : unit => @None nat))
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
    unit nat nat (pureASP (fun _ : unit => @None nat)))
    (eq (inr 7)) (Some (inr 7)) /\
  getDSLP (@arr_left optionDSLPArr Arrow_optionDSLPArr ArrowChoice_optionDSLPArr
    unit nat nat (pureDSLP (fun _ : unit => @None nat)))
    (eq (inr 7)) (Some (inr 7)).
Proof.
  split; cbn.
  - exists (inr 7). auto.
  - intros [[n|]|n] H; inversion H; reflexivity.
Qed.

Local Definition increment : ASPostArr nat unit :=
  pureASP (fun '(u, s) => Some (u, S s)).
Local Definition checked_double : ASPostArr nat unit :=
  pureASP (fun '(u, s) => if Nat.eqb s 4 then Some (u, 2 * s) else None).
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
  rewrite !pureASP_spec. split.
  - intros [[[[u s] [_ H]] _]|[[u s] [[[u0 s0] [Hp Hs]] Hr]]]; [discriminate |].
    inversion Hp; subst. inversion Hs; subst. now symmetry.
  - intros ->. right. exists (tt, 4). split; [exists (tt, 3); auto | reflexivity].
Qed.

Example state_updated_guard_fails (r : option (unit * nat)) :
  getASP increment_then_double (eq (tt, 2)) r <-> r = None.
Proof.
  unfold increment_then_double. rewrite stateOptASP_comp_spec.
  autounfold with sp_state_example_ops. rewrite !pureASP_spec. split.
  - intros [[_ Hr]|[[u s] [[[u0 s0] [Hp Hs]] Hr]]]; [exact Hr |].
    inversion Hp; subst. inversion Hs; subst. now symmetry.
  - intros ->. right. exists (tt, 3). split; [exists (tt, 2); auto | reflexivity].
Qed.

Local Notation coupled_state_arrow :=
  (@Arrow_stateArrT nat CoupledSP.optionASPArr
    (@Arrow_optionArrT CoupledSP.PureASPostArr
      CoupledSP.Arrow_PureASPostArr CoupledSP.ArrowChoice_PureASPostArr)).

Example state_application_conversion :
  getASP (state_option_asp_from_coupled
    (@arr_comp _ coupled_state_arrow _ _ _
      (@arr_pure _ coupled_state_arrow _ _
        (fun '(f, a) => (state_option_asp_to_coupled f, a)))
      (@arr_app _ coupled_state_arrow (CoupledSP.ArrowApply_stateOptASP nat)
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
    (firstASP (pureASP (fun f : PureASPostArr nat nat => compASP (pureASP S) f)))
    appASP) (eq (pureASP (fun n => 2 * n), 3)) 8.
Proof.
  rewrite ASP_app_precompose, compASP_spec, appASP_spec.
  exists (pureASP (fun n => 2 * n)). apply pureASP_spec.
  exists 4. split; [|reflexivity]. unfold arr_second. cbn.
  exists (4, pureASP (fun n => 2 * n)). split; [|reflexivity].
  exists 3. split; [|reflexivity].
  exists (pureASP (fun n => 2 * n), 3). auto.
Qed.

Example dslp_higher_order_postcompose :
  getDSLP (compDSLP (pureDSLP (fun n => (pureDSLP S, n)))
    (compDSLP (firstDSLP (pureDSLP (fun f : PureDSLPostArr nat nat =>
      compDSLP f (pureDSLP (fun n => 2 * n))))) appDSLP)) (eq 3) 8.
Proof.
  rewrite DSLP_app_postcompose.
  rewrite <- (@comp_assoc _ Arrow_PureDSLPostArr ArrowEq_PureDSLPostArr
    ArrowLaws_PureDSLPostArr).
  rewrite (@app_law _ Arrow_PureDSLPostArr ArrowApply_PureDSLPostArr
    ArrowEq_PureDSLPostArr ArrowApplyLaws_PureDSLPostArr).
  rewrite compDSLP_spec, pureDSLP_spec. intros n Hn.
  apply pureDSLP_spec. intros a Ha. lia.
Qed.

Example higher_order_captures_input :
  getASP (compASP (firstASP (pureASP
    (fun x : bool => pureASP (fun y : nat => (x, y))))) appASP)
    (eq (true, 3)) (true, 3) /\
  getDSLP (compDSLP (firstDSLP (pureDSLP
    (fun x : bool => pureDSLP (fun y : nat => (x, y))))) appDSLP)
    (eq (true, 3)) (true, 3).
Proof.
  rewrite ASP_app_unit, DSLP_app_unit. split; cbn.
  - exists (true, 3). auto.
  - intros p ->. reflexivity.
Qed.

Example pure_choice_active_branch :
  getASP (@leftASP bool bool nat (pureASP negb)) (eq (inl true)) (inl false) /\
  getDSLP (@leftDSLP bool bool nat (pureDSLP negb)) (eq (inl true)) (inl false).
Proof.
  rewrite leftASP_spec, leftDSLP_spec, pureASP_spec, pureDSLP_spec. split.
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

(** A second option layer also supports higher-order application and its
    static law.  These witnesses exercise the generic dictionaries. *)
Example nested_optionASP_apply_law {A B}
  (f : optionArrT optionASPArr A B) :
  @arr_comp (optionArrT optionASPArr)
    (@Arrow_optionArrT optionASPArr Arrow_optionASPArr ArrowChoice_optionASPArr)
    _ _ _
    (@arr_pure (optionArrT optionASPArr)
      (@Arrow_optionArrT optionASPArr Arrow_optionASPArr ArrowChoice_optionASPArr)
      _ _ (fun a => (f, a)))
    (@arr_app (optionArrT optionASPArr) _
      (@ArrowApply_optionArrT optionASPArr Arrow_optionASPArr
        ArrowChoice_optionASPArr ArrowApply_optionASPArr) _ _) = f.
Proof.
  exact (@app_law _ _ _ _
    (@ArrowApplyLaws_optionArrT optionASPArr Arrow_optionASPArr
      ArrowChoice_optionASPArr ArrowApply_optionASPArr ArrowEq_optionASPArr
      ArrowLaws_optionASPArr ArrowChoiceLaws_optionASPArr ArrowApplyLaws_optionASPArr)
    A B f).
Qed.

Example nested_optionDSLP_apply_law {A B}
  (f : optionArrT optionDSLPArr A B) :
  @arr_comp (optionArrT optionDSLPArr)
    (@Arrow_optionArrT optionDSLPArr Arrow_optionDSLPArr ArrowChoice_optionDSLPArr)
    _ _ _
    (@arr_pure (optionArrT optionDSLPArr)
      (@Arrow_optionArrT optionDSLPArr Arrow_optionDSLPArr ArrowChoice_optionDSLPArr)
      _ _ (fun a => (f, a)))
    (@arr_app (optionArrT optionDSLPArr) _
      (@ArrowApply_optionArrT optionDSLPArr Arrow_optionDSLPArr
        ArrowChoice_optionDSLPArr ArrowApply_optionDSLPArr) _ _) = f.
Proof.
  exact (@app_law _ _ _ _
    (@ArrowApplyLaws_optionArrT optionDSLPArr Arrow_optionDSLPArr
      ArrowChoice_optionDSLPArr ArrowApply_optionDSLPArr ArrowEq_optionDSLPArr
      ArrowLaws_optionDSLPArr ArrowChoiceLaws_optionDSLPArr ArrowApplyLaws_optionDSLPArr)
    A B f).
Qed.
