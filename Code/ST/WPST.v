From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.Examples ST.ST ST.WFST2.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition WPST0 :=
    (A -> S -> Prop) -> (S -> Prop).

  Definition wp_monotonicity (w:WPST0) : Prop := 
    forall p q,
      (forall r s1, p r s1 -> q r s1) -> 
        (forall s0, w p s0 -> w q s0).    

  Definition WPST :=
    { w : WPST0 | wp_monotonicity w }.

  Definition ordWPST (m1 m2 : WPST) : Prop :=
    forall p s0, proj1_sig m1 p s0 -> proj1_sig m2 p s0.

  Definition wp2pp (w : WPST) : (S -> Prop) * (S -> A -> S -> Prop) :=
    (proj1_sig w (fun _ _ => True), fun s0 a s1 => forall p, proj1_sig w p s0 -> p a s1).

  Program Definition wp2sp (w : WPST) : WFST S A :=
    let (pre, post) := wp2pp w in
    pp2sp0 pre post.

End Types.

Section WPST.

  Variable S : Type.

  Program Definition retWPST {A} (a : A) : WPST S A :=
    fun p s0 => p a s0.
  Next Obligation. sfirstorder. Qed.

  Program Definition bindWPST {A B}
    (m : WPST S A) (k : A -> WPST S B) : WPST S B :=
    fun p => m (fun a s1 => k a p s1).
  Next Obligation.
    destruct m as [m Hmm].
    (* destruct k as [k' Hkm]. *)
    unfold wp_monotonicity in *. simpl.
    intros.
    assert (forall a s1, proj1_sig (k a) p s1 -> proj1_sig (k a) q s1). {
      simpl. intros. destruct (k a) as [ka Hkm]. unfold wp_monotonicity in Hkm. 
      simpl.
      simpl in H1.
      specialize Hkm with p q s1. apply Hkm. sfirstorder. sfirstorder.
    }

    specialize Hmm with (fun a s1 => proj1_sig (k a) p s1) (fun a s1 => proj1_sig (k a) q s1) s0.
    apply Hmm. sfirstorder. sfirstorder.
  Qed.

  Program Definition getWPST : WPST S S :=
    fun p s0 => p s0 s0.
  Next Obligation. sfirstorder. Qed.

  Program Definition putWPST (s : S) : WPST S unit :=
    fun p s0 => p tt s.
  Next Obligation. sfirstorder. Qed.

  #[global] Instance Monad__WPST : Monad (WPST S) :=
    {| ret := fun _ => retWPST ;
       bind := fun _ _ => bindWPST |}.

  #[global] Instance MonadState__WPST : MonadState S (WPST S) :=
    {| get := getWPST ;
       put := putWPST |}.

End WPST.

Hint Unfold getWPST putWPST retWPST bindWPST ordWPST : mst.

Program Definition CorrectWP {R S}
  (pre : S -> Prop)
  (post: S -> R -> S -> Prop)
  (w : WPST S R) : Prop :=
  ordWPST (fun p s0 => pre s0 /\ (forall r s1, post s0 r s1 -> p r s1)) w.
Next Obligation. sfirstorder. Qed.

Program Definition IncorrectWP {R S}
  (presumes : S -> Prop)
  (achieves : R -> S -> Prop)
  (w : WPST S R) : Prop :=
  Incorrect presumes achieves (wp2sp w).

Hint Unfold CorrectWP IncorrectWP wp2sp : mst.

Lemma wp_ord_wp2sp {S R}  (m:WPST S R) P Q :
    CorrectWP P Q m ->
    Correct P Q (wp2sp m).
Proof.
  unfold CorrectWP.
  unfold Correct.
  unfold ordWPST.
  unfold ordWFST.
  unfold wp2sp. unfold pp2sp0.
  simpl.
  intros.
  split.
  + sfirstorder.
  + intros.
    destruct H0.
    specialize (H (Q s0) s0).
    (* specialize (H2 (Q s0) s0). *)
    assert (proj1_sig m (Q s0) s0). {
      apply H. sfirstorder. }
    apply H2 in H3.
    ++ assumption.
    ++ assert (wp_monotonicity (proj1_sig m)). { sfirstorder. }
       unfold wp_monotonicity in H4.
       assert (forall r s1, (Q s0) r s1 -> True). { sfirstorder. }
   
       eapply H4.
       apply H5.
       apply H3.
Qed.

Theorem agreement :
  forall {S R} (m : WPST S R) u u' o o',
    IncorrectWP u u' m ->
    (forall s0, u s0 -> o s0) ->
    CorrectWP o o' m ->
    (forall r s1, u' r s1 -> (exists s0, o' s0 r s1)).
Proof.
  intros.
  unfold IncorrectWP in H.
  apply wp_ord_wp2sp in H1.
  apply (ReasoningRulesAgreement.agreement H H0 H1).
  sfirstorder.
Qed.

Module Examples.

    Definition example_3_1_WPST : WPST (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else ret tt.

    Theorem example_3_1_incorrect :
      IncorrectWP
        (fun '(x, y, z) => z = 11)
        (fun _ '(x, y, z) => z = 42 /\
                            Nat.even x = true /\
                            negb (Nat.even y) = true)
        example_3_1_WPST.
    Proof.
      unfold IncorrectWP. unfold Incorrect'.
      autounfold with mst. cbn; intros.
      destruct r.
      destruct s as [[x y] z].
      destruct H as [Hz [Hx Hy]].
      autounfold with mst.
      exists (x, y, 11). 
      rewrite Hx. rewrite Hy. rewrite Hz.
      simpl.
      sfirstorder.
    Qed.

    Theorem example_3_1_incorrect' : (** should be unprovable *)
      IncorrectWP
        (fun '(x, y, z) => z = 11)
        (fun _ '(x, y, z) => z = 42)
        example_3_1_WPST.
    Proof.
      unfold IncorrectWP. unfold Incorrect'.
      autounfold with mst. cbn; intros.
      destruct r.
      destruct s as [[x y] z].
      (* destruct H as [Hz [Hx Hy]]. *)
      autounfold with mst.
      exists (x, y, 11). rewrite H.
      destruct (Nat.even x); destruct (Nat.even y); simpl; intros; split; split;
      auto.
      + intros. (** impossible to prove *)
    Abort.

End Examples.


Program Definition TestCorrectWP {R S}
  (pre : S -> Prop)
  (post: S -> R -> S -> Prop)
  (w : WPST S R) : Prop :=
  IncorrectWP pre (fun r s1 => exists s0, pre s0 /\ ~(post s0 r s1)) w.

Hint Unfold TestCorrectWP : mst.

Module TestExamples.

    Theorem example_3_1_correct :
      CorrectWP
        (fun '(x, y, z) => Nat.even x = true /\ negb (Nat.even y) = true)
        (fun _ _ '(x, y, z) => z = 42)
        Examples.example_3_1_WPST.
    Proof.
        unfold Examples.example_3_1_WPST.
        simpl.
        autounfold with mst. cbn; intros.
        destruct s0 as [[x y] z].
        destruct (Nat.even x); destruct (Nat.even y); simpl; intros;
        hauto lq: on drew: off.
    Qed.

End TestExamples.