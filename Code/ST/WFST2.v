From Coq Require Import RelationClasses.
From ExtLib Require Import Monad MonadState StateMonad MonadLaws.
From Hammer Require Import Hammer Tactics.
From Incorrectness Require Import ST.Examples ST.ST.

From Coq Require Import Nat Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition WFST :=
    { w : ST S A | forall s0 p q r s,
        (p -> q) -> proj1_sig (w s0 p r s) -> proj1_sig (w s0 q r s)  }.

End Types.

Section WFST.

  Variable S : Type.

  Program Definition retWFST {A} (a : A) : WFST S A :=
    retST a.

  Program Definition bindWFST {A B}
    (m : WFST S A) (k : A -> WFST S B) : WFST S B :=
    bindST m k.
  Next Obligation.
    destruct m as [m Hp]; cbn in *.
    exists H0. exists H1. destruct (k H0) as [ka Hkp] eqn:Hk.
    cbn in *. eapply Hkp; eauto.
  Qed.

  Program Definition getWFST : WFST S S :=
    @getST S.

  Program Definition putWFST (s : S) : WFST S unit :=
    putST s.

  #[global] Instance Monad__WFST : Monad (WFST S) :=
    {| ret := fun _ => retWFST ;
       bind := fun _ _ => bindWFST |}.

  #[global] Instance MonadState__WFST : MonadState S (WFST S) :=
    {| get := getWFST ;
       put := putWFST |}.

  (* Monad laws not proven. Not using [SProp]. *)

End WFST.

Program Definition obsWFST (S R : Type) (m : state S R) : WFST S R :=
  fun s0 pre r s => runState m s0 = (r, s) /\ pre.

Program Definition ordWFST {S R} (w w':WFST S R) : Prop :=
  forall s0 pre r s,
    proj1_sig (w' s0 pre r s) -> proj1_sig (w s0 pre r s).
    (* >= *)
    (** This definition should be like this, which
        is flipped compared to weakest-precondition because (Cezar's guess) these are post-conditions *)

    (* The fli was necessary to be able to prove the following law (Hoare Logic): {P}c{Q} /\ Q -> {Q'} -> {P}c{Q'} *)

Instance : forall {S R}, Transitive (@ordWFST S R).
Proof. now intros S R x y z hxy hyz ???? ?%hyz%hxy. Qed.

Program Definition VerifyWF {S R}
  (w : WFST S R) (m : state S R)
  (obs: forall {R}, state S R -> WFST S R) : Prop :=
  ordWFST w (obs m). 

#[local] Hint Unfold retWFST bindWFST getWFST putWFST VerifyWF ordWFST : mst.

Section Dijkstra.

  Variables S A R : Type.

  Theorem Verify_ret_WF : forall (r : R),
      @VerifyWF S _ (ret r) (ret r) (@obsWFST S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_bind_WF : forall m1 m2 k1 k2,
      @VerifyWF S A m1 m2 (@obsWFST S) ->
      (forall a, @VerifyWF S R (k1 a) (k2 a) (@obsWFST S)) ->
      @VerifyWF S R (m1 >>= k1) (m2 >>= k2) (@obsWFST S).
  Proof.
    autounfold with mst.
    sauto lq: on db: mst.
  Qed.

  Theorem Verify_get_WF :
    @VerifyWF S _ get get (@obsWFST S).
  Proof.
    autounfold with mst.
    hauto lq: on.
  Qed.

  Theorem Verify_put_WF : forall (s : S),
    VerifyWF (put s) (put s) (@obsWFST S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.

End Dijkstra.

#[export] Hint Resolve
  Verify_ret_WF Verify_bind_WF
  Verify_get_WF Verify_put_WF : mst.

Program Definition Incorrect {R S}
  (presumes : S -> Prop)
  (achieves: R -> S -> Prop) (* [achieves] works fine if does not talk about the initial state *)
  (w : WFST S R) : Prop :=
  forall r s,
    achieves r s ->
    exists s0, w s0 (presumes s0) r s /\ presumes s0.

Hint Unfold Incorrect : mst.

Module ReasoningRulesIncorrectness.
  Theorem weaken_pre :
    forall {S R} P P' Q (m : WFST S R),
      Incorrect P Q m ->
      (forall (s : S), P s -> P' s) ->
      Incorrect P' Q m.
  Proof.
    autounfold with mst. intros.
    sauto q: on.
  Qed.

  Theorem strengthen_post :
    forall {S R} P Q Q' (m : WFST S R),
      Incorrect P Q m ->
      (forall r (s : S), Q' r s -> Q r s) ->
      Incorrect P Q' m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.

  Theorem post_disj_intro :
    forall {S R} P Q1 Q2 (m : WFST S R),
    Incorrect P Q1 m ->
    Incorrect P Q2 m ->
    Incorrect P (fun r s => Q1 r s \/ Q2 r s) m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.

  Theorem post_disj_elim :
    forall {S R} P Q1 Q2 (m : WFST S R),
    Incorrect P (fun r s => Q1 r s \/ Q2 r s) m ->
    Incorrect P Q1 m /\
    Incorrect P Q2 m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.
End ReasoningRulesIncorrectness.

Program Definition pp2sp0 {S A}
  (pre : S -> Prop)
  (post : S -> A -> S -> Prop) : WFST S A :=
  fun s0 q r s1 =>
    q /\ (pre s0 -> post s0 r s1).

Definition ordPrePost {R S}
  (pre1 pre2 : S -> Prop) (post1 post2 : S -> R -> S -> Prop) : Prop :=
  (forall s, pre2 s -> pre1 s) /\ (forall s0 r s1, post1 s0 r s1 -> post2 s0 r s1).

Definition sp2pp {R S} (sp:WFST S R) : (S -> Prop) * (S -> R -> S -> Prop) :=
  let post := fun s0 x s1 => forall (pre : Prop), proj1_sig (proj1_sig sp s0 pre x s1) in
  let pre := fun s0 => exists pre, pre /\ (forall x s1, post s0 x s1 -> proj1_sig (proj1_sig sp s0 pre x s1)) in
  (pre, post).

Lemma test_pp2sp0' {S R} P (Q:S -> R -> S -> Prop) :
  let (P', Q') := sp2pp (pp2sp0 P Q) in
  ordPrePost P' P Q' Q.
Proof.
  split.
  + intros s0 Hpre. exists (P s0). split.
    ++ intros. apply Hpre. 
    ++ sfirstorder.
  + intros.
    unfold pp2sp0 in H. unfold sp2pp in H. simpl in H.
    specialize H with (P s0).
    apply H.
    sfirstorder. 
Qed.

Lemma test_pp2sp0_loop {S R} (sp:WFST S R) :
  (* let (P, Q) := sp2pp sp in *)
  ordWFST (pp2sp0 (fst (sp2pp sp)) (snd (sp2pp sp))) sp.
Proof.
  unfold ordWFST. 
  (* simpl. *)
  intros.
  simpl.
  split.
  + destruct sp. sfirstorder.
  + intros.
    destruct H0 as [pre' [Hpre' H0]].
    destruct sp.
 
(* Lemma test_pp2sp0 {S R} P (Q:S -> R -> S -> Prop) :
  let (P', Q') := sp2pp (pp2sp0 P Q) in
  ordPrePost P P' Q Q'.
Proof.
  unfold ordPrePost.
  split.
  + intros s0 Hpre. destruct Hpre as [P' [H HP']].
  unfold pp2sp0 in H. simpl in H.
  admit.
  + intros. unfold pp2sp0. simpl. sfirstorder.
Abort. *)
  

Program Definition Correct {R S}
  (pre : S -> Prop)
  (post: S -> R -> S -> Prop)
  (w : WFST S R) : Prop :=
  ordWFST (pp2sp0 pre post) w.

Hint Unfold Correct pp2sp0 : mst.

Module ReasoningRulesCorrectness.
  Theorem strengthen_pre :
    forall {S R} P P' Q (m : WFST S R),
      Correct P Q m ->
      (forall (s0 : S), P' s0 -> P s0) ->
      Correct P' Q m.
  Proof.
    autounfold with mst. intros.
    simpl in H. simpl in H1.
    simpl.
    specialize H with s0 pre r s.
    apply H in H1.
    sfirstorder.
  Qed.

  Theorem weaken_post :
    forall {S R} P Q Q' (m : WFST S R),
      Correct P Q m ->
      (forall s0 r s1, Q s0 r s1 -> Q' s0 r s1) ->
      Correct P Q' m.
  Proof.
    autounfold with mst. simpl. intros.
    specialize H with s0 pre r s.
    sfirstorder.
  Qed.

  Lemma pp2sp0_post_conj_intro {R S}
    (P : S -> Prop)
    (Q1 Q2 : S -> R -> S -> Prop) :
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp0 P Q1) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp0 P Q2) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp0 P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1)) s0 pre r s1).
    Proof.
      intros s0 pre r s1 H1 H2.
      simpl.
      intros.
      simpl in H1.
      simpl in H2.
      split.
      + sfirstorder.
      + sfirstorder.
    Qed.

  Theorem post_conj_intro :
    forall {S R} P Q1 Q2 (m : WFST S R),
    Correct P Q1 m ->
    Correct P Q2 m ->
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m.
  Proof.
    intros.
    unfold Correct in *.
    unfold ordWFST in *.
    intros s0 H_P.
    intros r s1 Hms0. 
    specialize (H s0 H_P r s1 Hms0).
    specialize (H0 s0 H_P r s1 Hms0).
    apply pp2sp0_post_conj_intro.
    sfirstorder.
    sfirstorder.
  Qed.

  Theorem post_conj_elim :
    forall {S R} P Q1 Q2 (m : WFST S R),
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m ->
    Correct P Q1 m /\
    Correct P Q2 m.
  Proof.
    autounfold with mst. simpl. intros. 
    split.
    - intros. specialize H with s0 pre r s. sfirstorder.
    - intros. specialize H with s0 pre r s. sfirstorder.
  Qed.
End ReasoningRulesCorrectness.

Module ReasoningRulesAgreement.
  Theorem agreement :
    forall {S R} (m : WFST S R) u u' o o',
      Incorrect u u' m ->
      (forall s0, u s0 -> o s0) ->
      Correct o o' m ->
      (forall r s1, u' r s1 -> (exists s0, o' s0 r s1)).
  Proof.
    autounfold with mst. simpl. intros.

    assert (Incorrect o u' m). {
      apply (ReasoningRulesIncorrectness.weaken_pre _ H H0).
    }
    clear H. clear H0.
    unfold Incorrect in H3.
    specialize H3 with r s1.
    apply H3 in H2. clear H3.
    destruct H2 as [s0 [Hpre H0]].
    exists s0.
    specialize H1 with s0 (o s0) r s1.
    sauto q: on.    
  Qed.

  Theorem denial :
    forall {S R} (m : WFST S R) u u' o o',
      (Incorrect u u' m /\
       (forall s0, u s0 -> o s0) /\
       ~(forall r s1, u' r s1 -> (exists s0, o' s0 r s1))) ->
      ~(Correct o o' m).
  Proof.
    (* autounfold with mst. *)
    unfold not.
    intros.
    destruct H as [H1 [H2 H3]].
    apply H3.
    apply (agreement H1 H2 H0).
  Qed.
End ReasoningRulesAgreement.

Module OHearnExample.

    Definition example_3_1_ST : WFST (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else ret tt.

    Definition example_3_1_state : state (nat * nat * nat) unit :=
      '(x, y, z) <- get ;;
        if Nat.even x then
          if negb (Nat.even y) then put (x, y, 42) else ret tt
        else ret tt.

    (* The new incorrectness reasoning that relates [presumes] and [achieves]
       with specification monad, but not effect observations yet! *)
    Theorem example_3_1_incorrect :
      Incorrect
        (fun '(x, y, z) => z = 11)
        (fun _ '(x, y, z) => z = 42 /\
                            Nat.even x = true /\
                            negb (Nat.even y) = true)
        example_3_1_ST.
    Proof.
      autounfold with mst. cbn; intros.
      (* This does not seem very automatic; can an SMT solver work here? *)
      destruct s as [[x y] z].
      exists (x, y, 11). split; auto; intros. exists (x, y, 11).
      destruct (Nat.even x); destruct (Nat.even y);
        hauto lq: on drew: off.
    Qed.

    Theorem example_3_1_correct :
      Correct
        (fun '(x, y, z) => Nat.even x = true /\ negb (Nat.even y) = true)
        (fun _ _ '(x, y, z) => z = 42)
        example_3_1_ST.
    Proof.
      autounfold with mst. cbn. intros.
      destruct s0 as [[x'' y''] z''].
      destruct s as [[x''' y'''] z'''].
      destruct H as [[[x y] z]]. destruct H as [[[x' y'] z']].
      destruct r.
      destruct (Nat.even x); destruct (Nat.even y); simpl in H.
      (** I think now this can be proved, but my Rocq skills are limited.
          I want to keep the hypothesis of the destruct here. *)
    Abort.

    (* This is the old thing with Dijkstra monads. *)
    Theorem example_3_1_dijkstra :
      VerifyWF example_3_1_ST example_3_1_state (@obsWFST _).
    Proof.
      unfold example_3_1_ST, example_3_1_state.
      apply Verify_bind_WF; [ apply Verify_get_WF | ].
      intros [[? ?] ?].
      destruct (Nat.even n) eqn:Hn.
      destruct (Nat.even n0) eqn:Hn0; cbn.
      - apply Verify_ret_WF.
      - apply Verify_put_WF.
      - apply Verify_ret_WF.
    Qed.

    (* This is the final theorem we want that relates [assumes] and [achieves]
       with effect observation. We only need to compose the above two proofs to
       obtain this. *)
    Theorem example_3_1_final :
      forall x' y' z',
        z' = 42 ->
        Nat.even x' = true ->
        negb (Nat.even y') = true ->
      exists x y z, runState example_3_1_state (x, y, z) = (tt, (x', y', z')) /\ z = 11.
    Proof.
      pose proof (example_3_1_incorrect) as HI.
      pose proof (example_3_1_dijkstra)  as HV.
      intros. specialize (HI tt (x', y', z') ltac:(hauto lq: on)).
      destruct HI as [[[x y] z] [HI ?]]. exists x, y, z.
      split.
      (* this is not provable anymore since the change in the definition of ord. *)
      + admit. (* eapply HV. apply HI. *)
      + assumption.
    Abort.

    (* incorrectness conditions -> effect observation *)
    (* incorrectness conditions -> spec monad -> effect observation *)
    (* Hoare logic? *)

End OHearnExample.

Module ReasoningRulesCorrectnessWithPP2SP.
  (** 
    pp2sp factors through the simpler pred specification monad that only captures the postcondition.
    Kenji proved that forward predicate transformers and predicate are in bijection.
  *)

  Program Definition pp2sp {S A}
    (pre : S -> Prop)
    (post : S -> A -> S -> Prop) : WFST S A :=
    fun s0 q r s1 =>
      forall (sp : WFST S A),
        (forall s0' q' r' s1', q' /\ post s0' r' s1' -> proj1_sig (proj1_sig sp s0' q' r' s1')) ->
          proj1_sig (proj1_sig sp s0 q r s1).
    Next Obligation.
      specialize H with (pp2sp0 pre post).
      cbv in H.
      apply H.
      sfirstorder.
    Qed.
    Next Obligation.
      specialize H0 with sp.
      assert (forall (s0 : S) (p q : Prop) (r : A) (s : S),
  (p -> q) -> proj1_sig (proj1_sig sp s0 p r s) -> proj1_sig (proj1_sig sp s0 q r s)). {
        destruct sp as [m mon].
        apply mon.
      }
      apply (H2 s0 p q r s);
      sfirstorder.
    Qed.

  (* Lemma pp2sp_monotone {R S}
    (pre1 pre2 : S -> Prop) (post1 post2 : S -> R -> S -> Prop) :
    ordPrePost pre1 pre2 post1 post2 ->
    ordWFST (pp2sp pre1 post1) (pp2sp pre2 post2).
  Proof.
    (* Surprisingly, hpre is never used *)
    intros [_ (* hpre *) hpost] s0 pre r s1 hwp1 sp hsp; apply hwp1.
    intros s0' pre' r' s1' [hpre' hpost1].
    apply hsp; split; [assumption| now apply hpost].
  Qed. *)

  Lemma helper_lemma1 A B C  :
    (A -> B) -> (C -> B) -> (A /\ C -> B).
  Proof. sfirstorder. Qed.

  Lemma helper_lemma2 {A B C D} (P1 P2:A -> B -> C -> D -> Prop) (Q:Prop):
    ((forall a b c d, P1 a b c d) /\ (forall a b c d, P2 a b c d) -> Q) ->
    ((forall a b c d, P1 a b c d /\ P2 a b c d) -> Q).
  Proof.
      intros.
      apply H.
      split.
      + intros. specialize H0 with a b c d. sfirstorder.
      + intros. specialize H0 with a b c d. sfirstorder.
  Qed.

  Lemma pp2sp0_post_conj_intro {R S}
    (P : S -> Prop)
    (Q1 Q2 : S -> R -> S -> Prop) 
    (m : state S R):
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp0 P Q1) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp0 P Q2) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp0 P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1)) s0 pre r s1).
    Proof.
      intros s0 pre r s1 H1 H2.
      simpl.
      intros.
      simpl in H1.
      simpl in H2.
      split.
      + sfirstorder.
      + sfirstorder.
    Qed.

  Lemma pp2sp_post_conj_intro {R S}
    (P : S -> Prop)
    (Q1 Q2 : S -> R -> S -> Prop) :
    forall s0 pre r s1,
      proj1_sig (proj1_sig (pp2sp P Q1) s0 pre r s1) /\ 
      proj1_sig (proj1_sig (pp2sp P Q2) s0 pre r s1) -> 
      proj1_sig (proj1_sig (pp2sp P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1)) s0 pre r s1).
    Proof.
      intros.
      destruct H as [H1 H2].
      simpl.
      intros.
      simpl in H1. specialize H1 with sp.
      simpl in H2. specialize H2 with sp.
      pose proof (helper_lemma1 H1 H2) as H3. clear H1 H2.
      apply helper_lemma2 in H3.
      + assumption.
      + clear H3. intros s0' q' r' s1'.
        specialize H with s0' q' r' s1'.
        (** impossible to prove. Something like this is needed:
          (A /\ C -> B) -> (A -> B) /\ (C -> B). *)
        (** Compared with pp2sp0_post_conj_intro, the pre-condition is missing. *)
    Admitted.

  Program Definition Correct {R S}
    (pre : S -> Prop)
    (post: S -> R -> S -> Prop)
    (w : WFST S R) : Prop :=
    ordWFST (pp2sp pre post) w.

  Hint Unfold Correct pp2sp : mst.

  Theorem strengthen_pre :
    forall {S R} P P' Q (m : WFST S R),
      Correct P Q m ->
      (forall (s0 : S), P' s0 -> P s0) ->
      Correct P' Q m.
  Proof.
    autounfold with mst. intros.
    simpl in H. simpl in H1.
    apply H.
    + sfirstorder.
    + sfirstorder.
  Qed.

  Theorem weaken_post :
    forall {S R} P Q Q' (m : WFST S R),
      Correct P Q m ->
      (forall s0 r s1, Q s0 r s1 -> Q' s0 r s1) ->
      Correct P Q' m.
  Proof.
    autounfold with mst. simpl. intros.
    apply H.
    sfirstorder.
    sfirstorder.
  Qed.

  Theorem post_conj_intro :
    forall {S R} P Q1 Q2 (m : WFST S R),
    Correct P Q1 m ->
    Correct P Q2 m ->
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m.
  Proof.
    intros.
    unfold Correct in *.
    unfold ordWFST in *.
    intros s0 H_P.
    intros r s1 Hms0. 
    specialize (H s0 H_P r s1 Hms0).
    specialize (H0 s0 H_P r s1 Hms0).
    apply pp2sp_post_conj_intro.
    sfirstorder.
  Qed.

  Theorem post_conj_elim :
    forall {S R} P Q1 Q2 (m : WFST S R),
    Correct P (fun s0 r s1 => Q1 s0 r s1 /\ Q2 s0 r s1) m ->
    Correct P Q1 m /\
    Correct P Q2 m.
  Proof.
    autounfold with mst. simpl. intros.
    split.
    - intros. apply H. sfirstorder. sfirstorder.
    - intros. apply H. sfirstorder. sfirstorder.
  Qed.

  Theorem agreement :
    forall {S R} (m : WFST S R) u u' o o',
      Incorrect u u' m ->
      (forall s0, u s0 -> o s0) ->
      Correct o o' m ->
      (forall r s1, u' r s1 -> (exists s0, o' s0 r s1)).
  Proof.
    autounfold with mst. simpl. intros.

    assert (Incorrect o u' m). {
      apply (ReasoningRulesIncorrectness.weaken_pre _ H H0).
    }
    clear H. clear H0.
    unfold Incorrect in H3.
    specialize H3 with r s1.
    apply H3 in H2. clear H3.
    destruct H2 as [s0 [Hpre H0]].
    exists s0.
    specialize H1 with s0 (o s0) r s1 (pp2sp0 o o').
    sauto q: on.    
  Qed.

  Theorem denial :
    forall {S R} (m : WFST S R) u u' o o',
      (Incorrect u u' m /\
       (forall s0, u s0 -> o s0) /\
       ~(forall r s1, u' r s1 -> (exists s0, o' s0 r s1))) ->
      ~(Correct o o' m).
  Proof.
    (* autounfold with mst. *)
    unfold not.
    intros.
    destruct H as [H1 [H2 H3]].
    apply H3.
    apply (agreement H1 H2 H0).
  Qed.
End ReasoningRulesCorrectnessWithPP2SP.

(* But we can prove the following if we use [WFST], which has an additional
   invariant. *)

Program Definition IncorrectWF {R S}
  (presumes : S -> Prop)
  (achieves: S -> R -> S -> Prop)
  (w : WFST S R) : Prop :=
  forall r s, exists s0,
    (presumes s0 -> achieves s0 r s ->
     proj1_sig (w s0 (presumes s0) r s)) /\
      presumes s0.


Hint Unfold IncorrectWF : mst.

(* If we have an [achieves] that talks about initial states, not all reasoning
   principles of incorrectness logic follow. *)
Module BadReasoningRules.

  Theorem weaken_pre :
    forall {S R} P P' Q (m : WFST S R),
      IncorrectWF P Q m ->
      (forall (s : S), P s -> P' s) ->
      IncorrectWF P' Q m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.

  Theorem strengthen_post :
    forall {S R} P Q Q' (m : WFST S R),
      IncorrectWF P Q m ->
      (forall r (s0 s : S), Q' s0 r s -> Q s0 r s) ->
      IncorrectWF P Q' m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.

  Theorem post_disj_intro :
    forall {S R} P Q1 Q2 (m : WFST S R),
    IncorrectWF P Q1 m ->
    IncorrectWF P Q2 m ->
    IncorrectWF P (fun s0 r s => Q1 s0 r s \/ Q2 s0 r s) m.
  Proof.
    autounfold with mst. intros.
    destruct m as [m Hm]; cbn in *.
    specialize (H r s). specialize (H0 r s).
    destruct H as [s1 [? ?]]. destruct H0 as [s2 [? ?]].
    (* This does not seem provable. *)
  Abort.

  Theorem post_disj_elim :
    forall {S R} P Q1 Q2 (m : WFST S R),
    IncorrectWF P (fun s0 r s => Q1 s0 r s \/ Q2 s0 r s) m ->
    IncorrectWF P Q1 m /\
    IncorrectWF P Q2 m.
  Proof.
    autounfold with mst. intros.
    sfirstorder.
  Qed.

  Theorem agreement :
    forall {S R} (m : WFST S R) u u' o o',
      IncorrectWF u u' m ->
      (forall s0, u s0 -> o s0) ->
      Correct o o' m ->
      (forall s0 r s, u' s0 r s -> o' s0 r s).
  Proof.
    autounfold with mst.
    intros.
    assert (IncorrectWF o u' m). {
      apply (weaken_pre _ H H0).
    }
    clear H. clear H0.
    autounfold with mst in H3.
    specialize H3 with r s.
    destruct H3 as [s0' [Hos0' H]].
    apply Hos0' in H. clear Hos0'.
    specialize H1 with s0' (o s0') r s.
    simpl in H1.
    (** unprovable *)
  Abort.

  Theorem denial :
    forall {S R} (m : WFST S R) u u' o o',
      (IncorrectWF u u' m /\
       (forall s0, u s0 -> o s0) /\
       ~(forall s0 r s, u' s0 r s -> o' s0 r s)) ->
      ~(Correct o o' m).
  Proof.
    (* autounfold with mst. *)
    unfold not.
    intros.
    destruct H as [H1 [H2 H3]].
    apply H3.
    (** This is agreement, but it is not provable. *)
  Abort.
End BadReasoningRules.