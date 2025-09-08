Definition example_3_1 '((x, y, z) : nat * nat * nat) : nat :=
  if Nat.even x then
    if negb (Nat.even y) then 42 else z
  else z.


Module ContextFree.
Definition SP {Γ A} (P : Γ -> Prop) (m : Γ -> A) : A -> Prop :=
  fun r => exists γ, m γ = r /\ P γ.

Definition Incorrect {Γ A} (presumes : Γ -> Prop) (m : Γ -> A) (achieves: A -> Prop)  : Prop :=
  forall r, achieves r -> SP presumes m r.

Lemma Incorect_weaken {Γ A} (pres1 pres2 : Γ -> Prop) (m : Γ -> A) (ach1 ach2 : A -> Prop) :
  (forall γ, pres1 γ -> pres2 γ) ->
  Incorrect pres1 m ach1 ->
  (forall γ, ach2 γ -> ach1 γ) ->
  Incorrect pres2 m ach2.
Proof.
  intros wk_pres inc wk_ach r [γ [? ?%wk_pres]]%wk_ach%inc.
  exists γ; split; assumption.
Qed.

Lemma Incorect_disj {Γ A} (pres : Γ -> Prop) (m : Γ -> A) (ach1 ach2 : A -> Prop) :
  Incorrect pres m ach1 ->
  Incorrect pres m ach2 ->
  Incorrect pres m (fun r => ach1 r \/ ach2 r).
Proof.
  now intros inc1 inc2 r [?%inc1 | ?%inc2].
Qed.

Definition Correct {Γ A} (precondition : Γ -> Prop) (m : Γ -> A) (postcondition : A -> Prop) : Prop :=
  forall r, SP precondition m r -> postcondition r.

Lemma Correct_alt {Γ A} (precondition : Γ -> Prop) (m : Γ -> A) (postcondition : A -> Prop) :
  Correct precondition m postcondition <-> (forall γ, precondition γ -> postcondition (m γ)).
Proof.
  split.
  - intros h γ hpre; apply h; exists γ; split; easy.
  - intros h r [γ [<- ?]]; now apply h.
Qed.

Lemma SP_monotone {Γ A} {P1 P2 : Γ -> Prop} {m : Γ -> A} :
  (forall γ, P1 γ -> P2 γ) ->
  forall r, SP P1 m r -> SP P2 m r.
Proof.
  intros wk r [γ []]; exists γ; split ; [assumption| now eapply wk].
Qed.

Lemma agreement {Γ A} (pres prec : Γ -> Prop) m (ach post : A -> Prop) :
  Incorrect pres m ach ->
  (forall γ, pres γ -> prec γ) ->
  Correct prec m post ->
  forall r, ach r -> post r.
Proof.
  intros inc wk_pre cor r ?.
  now apply cor, (SP_monotone wk_pre), inc.
Qed.

Example example_3_1_test1 :
  Incorrect
    (fun '(x,y,z) => z = 11)
    example_3_1
    (fun r => r = 42).
Proof.
  intros r ->; exists (0,1,11); repeat constructor.
Qed.

Example example_3_1_test2 :
  ~ Incorrect
      (fun '(x,y,z) => z = 11)
      example_3_1
      (fun r => r = 7).
Proof.
  intros h; pose proof (h 7 eq_refl) as [[[x y] z] []]; cbn in *; subst.
  destruct (Nat.even x); cbn in *; try discriminate.
  destruct (Nat.even y); cbn in *; discriminate.
Qed.

Example example_3_1_test3 :
  Incorrect
    (* (fun '(x,y,z) => z <> 42) *)
    (fun _ => True)
    example_3_1
    (fun r => r <> 42).
  Proof.
    intros r h.
    exists (0,0,r); repeat constructor.
  Qed.

End ContextFree.

Module ContextFull.

Definition SP {Γ A} (P : Γ -> Prop) (m : Γ -> A) : Γ -> A -> Prop :=
  fun γ r => m γ = r /\ P γ.

Definition Incorrect {Γ A} (presumes : Γ -> Prop) (m : Γ -> A) (achieves: Γ -> A -> Prop)  : Prop :=
  forall γ r, achieves γ r -> SP presumes m γ r.

Arguments SP {_ _} _ _ /.

Example example_3_1_test1 :
  ~ Incorrect
    (fun '(x,y,z) => z = 11)
    example_3_1
    (fun _ r => r = 42).
Proof.
  intros h; pose proof (h (1,0,42) 42 eq_refl) as [_ [=]].
Qed.

Example example_3_1_test2 :
  Incorrect
    (fun '(x,y,z) => z = 11)
    example_3_1
    (fun '(x,y,z) r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true /\ z = 11).
Proof.
  intros [[x y] z] r.
  intros [h0 [h1 [h2 h3]]]; cbn.
  rewrite !h0, !h1, !h2, !h3.
  repeat constructor.
Qed.

Example example_3_1_test3 :
  ~ Incorrect
    (fun '(x,y,z) => True)
    example_3_1
    (fun '(x,y,z) r => r = 42).
Proof.
  intros h; pose proof (h (1,0,0) 42 eq_refl) as [[=]].
Qed.

Example example_3_1_test4 :
  Incorrect
    (fun '(x,y,z) => True)
    example_3_1
    (fun '(x,y,z) r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  intros [[x y] z] r.
  intros [h0 [h1 h2]]; cbn.
  rewrite !h0, !h1, !h2.
  repeat constructor.
Qed.

Example example_3_1_test5 :
  Incorrect
    (fun '(x,y,z) => True)
    example_3_1
    (fun '(x,y,z) r => r = z /\ Nat.even x = false).
Proof.
  intros [[x y] z] r.
  intros [h0 h1]; cbn.
  rewrite !h0, !h1.
  repeat constructor.
Qed.

Example example_3_1_test6 :
  Incorrect
    (fun '(x,y,z) => True)
    example_3_1
    (fun '(x,y,z) r => r = z /\ Nat.even y = true).
Proof.
  intros [[x y] z] r.
  intros [h0 h1]; cbn.
  destruct (Nat.even x); rewrite ?h0, ?h1; repeat constructor.
Qed.

End ContextFull.


Module ContextImplicit.

Definition SP {A} (P : Prop) (m : A) : A -> Prop :=
  fun r => m = r /\ P.

Definition Incorrect {A} (presumes : Prop) (m : A) (achieves: A -> Prop)  : Prop :=
  forall r, achieves r -> SP presumes m r.

Arguments SP {_} _ _ /.

Lemma Incorect_weaken {A} (pres1 pres2 : Prop) (m : A) (ach1 ach2 : A -> Prop) :
  (pres1 -> pres2) ->
  Incorrect pres1 m ach1 ->
  (forall γ, ach2 γ -> ach1 γ) ->
  Incorrect pres2 m ach2.
Proof.
  intros wk_pres inc wk_ach r [? ?%wk_pres]%wk_ach%inc.
  split; assumption.
Qed.

Lemma Incorect_disj {A} (pres : Prop) (m : A) (ach1 ach2 : A -> Prop) :
  Incorrect pres m ach1 ->
  Incorrect pres m ach2 ->
  Incorrect pres m (fun r => ach1 r \/ ach2 r).
Proof.
  now intros inc1 inc2 r [?%inc1 | ?%inc2].
Qed.

Definition Correct {A} (precondition : Prop) (m : A) (postcondition: A -> Prop)  : Prop :=
  forall r, SP precondition m r -> postcondition r.

Lemma Correct_alt {A} (precondition : Prop) (m : A) (postcondition : A -> Prop) :
  Correct precondition m postcondition <-> (precondition -> postcondition m).
Proof.
  split.
  - intros h hpre; apply h; split; easy.
  - intros h r [<- ?]; now apply h.
Qed.

Lemma SP_monotone {A} {P1 P2 : Prop} {m : A} :
  (P1 -> P2) ->
  forall r, SP P1 m r -> SP P2 m r.
Proof.
  intros wk r []; split ; [assumption| now eapply wk].
Qed.

Lemma agreement {A} (pres prec : Prop) m (ach post : A -> Prop) :
  Incorrect pres m ach ->
  (pres -> prec) ->
  Correct prec m post ->
  forall r, ach r -> post r.
Proof.
  intros inc wk_pre cor r ?.
  now apply cor, (SP_monotone wk_pre), inc.
Qed.

Example example_3_1_test1 :
  ~ forall x y z,
    Incorrect
    (z = 11)
    (example_3_1 (x,y,z))
    (fun r => r = 42).
Proof.
  intros h; pose proof (h 1 0 42 42 eq_refl) as [_ [=]].
Qed.

Example example_3_1_test2 :
  forall x y z,
  Incorrect
    (z = 11)
    (example_3_1 (x,y,z))
    (fun r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true /\ z = 11).
Proof.
  intros x y z r.
  intros [h0 [h1 [h2 h3]]]; cbn.
  rewrite !h0, !h1, !h2, !h3.
  repeat constructor.
Qed.

Example example_3_1_test3 :
  ~ forall x y z,
    Incorrect
      True
      (example_3_1 (x,y,z))
      (fun r => r = 42).
Proof.
  intros h; pose proof (h 1 0 0 42 eq_refl) as [[=]].
Qed.

Example example_3_1_test4 :
  forall x y z,
  Incorrect
    True
    (example_3_1 (x,y,z))
    (fun r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  intros x y z r.
  intros [h0 [h1 h2]]; cbn.
  rewrite !h0, !h1, !h2.
  repeat constructor.
Qed.

Example example_3_1_test5 :
  forall x y z,
  Incorrect
    True
    (example_3_1 (x,y,z))
    (fun r => r = z /\ Nat.even x = false).
Proof.
  intros x y z r.
  intros [h0 h1]; cbn.
  rewrite !h0, !h1.
  repeat constructor.
Qed.

Example example_3_1_test6 :
  forall x y z,
  Incorrect
    True
    (example_3_1 (x,y,z))
    (fun r => r = z /\ Nat.even y = true).
Proof.
  intros x y z r.
  intros [h0 h1]; cbn.
  destruct (Nat.even x); rewrite ?h0, ?h1; repeat constructor.
Qed.

End ContextImplicit.