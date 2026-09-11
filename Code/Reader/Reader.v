From ExtLib Require Import Monad MonadReader ReaderMonad.
From Hammer Require Import Tactics.

From Coq Require Import Lia PeanoNat.
Opaque "<=?".

Set Implicit Arguments.

Import MonadNotation.
Open Scope monad_scope.
Open Scope nat_scope.

Section Types.

  Variable S A : Type.

  Definition Reader := forall (s0 : S) (pre : Prop),
      {p : A -> Prop | forall a, p a -> pre}.

  Definition WFReader :=
    { w : Reader | forall s0 p q r,
        (p -> q) -> proj1_sig (w s0 p) r -> proj1_sig (w s0 q) r }.

  Definition toReader (w : WFReader) : Reader := proj1_sig w.
End Types.

Coercion toReader : WFReader >-> Reader.

Section Reader.

  Variable S : Type.

  Program Definition retReader {A} (a : A) : Reader S A :=
    fun _ pre r => pre /\ r = a.

  Program Definition bindReader {A B}
    (m : Reader S A) (k : A -> Reader S B) : Reader S B :=
    fun s0 pre b => exists a, k a s0 (m s0 pre a) b.
  Next Obligation. sfirstorder. Qed.

  Program Definition askReader : Reader S S :=
    fun s0 pre r => pre /\ r = s0.

  Program Definition localReader {A}
    (f : S -> S) (m : Reader S A): Reader S A :=
    fun s0 => m (f s0).

  #[global] Instance Monad__Reader : Monad (Reader S) :=
    {| ret := fun _ => retReader ;
       bind := fun _ _ => bindReader |}.

  #[global] Instance MonadReader__Reader : MonadReader S (Reader S) :=
    {| ask   := askReader ;
       local := @localReader |}.

  (* Monad laws not proven. Not using [SProp]. *)

End Reader.

Program Definition obsReader (S R : Type) (m : reader S R) : Reader S R :=
  fun s0 pre r => runReader m s0 = r /\ pre.

Program Definition Verify {S R}
  (w : Reader S R) (m : reader S R)
  (obs: forall {R}, reader S R -> Reader S R) : Prop :=
  forall s0 pre r, w s0 pre r -> obs m s0 pre r.

#[local] Hint Unfold retReader bindReader localReader askReader Verify: mst.

Section Dijkstra.

  Variables S A R : Type.

  Theorem Verify_ret : forall (r : R),
      @Verify S _ (ret r) (ret r) (@obsReader S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_bind : forall m1 m2 k1 k2,
      @Verify S A m1 m2 (@obsReader S) ->
      (forall a, @Verify S R (k1 a) (k2 a) (@obsReader S)) ->
      @Verify S R (m1 >>= k1) (m2 >>= k2) (@obsReader S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.

  Theorem Verify_ask :
    @Verify S _ ask ask (@obsReader S).
  Proof.
    autounfold with mst.
    sfirstorder.
  Qed.

  Theorem Verify_local : forall (f : S -> S) (m1 : Reader S A) m2,
      Verify m1 m2 (@obsReader S) ->
      Verify (local f m1) (local f m2) (@obsReader S).
  Proof.
    autounfold with mst.
    sauto lq: on.
  Qed.

End Dijkstra.

#[export] Hint Resolve Verify_ret Verify_bind Verify_ask Verify_local : mst.

Module WithStateFreeAchieves.

(* KM: I don't think this definition of incorrectness follows the
  design of O'Hearn's paper *)
Program Definition Incorrect_ {R S}
  (presumes : S -> Prop)
  (w : Reader S R)
  (achieves: S -> R -> Prop) : Prop :=
  forall r, exists s0,
    (achieves s0 r ->
     w s0 (presumes s0) r) /\
      presumes s0.

(* Following O'Hearn's initial intuition:
  Given a predicate on initial state and a "computation" w
  (here really a specification standing in for a computation)
  produce the predicate on results induced by w.  *)
Program Definition SP {R S} (presumes : S -> Prop) (w : Reader S R) : R -> Prop :=
  fun r => exists s0, w s0 (presumes s0) r.

Program Definition Incorrect {R S}
  (presumes : S -> Prop)
  (w : Reader S R)
  (achieves: R -> Prop) : Prop :=
  forall r, achieves r -> SP presumes w r.

Hint Unfold Incorrect_ : mst.
Hint Unfold SP : mst.
Hint Unfold Incorrect : mst.

Lemma Incorect_weaken {S A}
  (pres1 pres2 : S -> Prop)
  (w : WFReader S A)  (* Need to assume monotonicity here *)
  (ach1 ach2 : A -> Prop) :
  (forall s0, pres1 s0 -> pres2 s0) ->
  Incorrect pres1 w ach1 ->
  (forall γ, ach2 γ -> ach1 γ) ->
  Incorrect pres2 w ach2.
Proof.
  intros wk_pres inc wk_ach r [s0 ?]%wk_ach%inc.
  exists s0; eapply (proj2_sig w);[ eapply wk_pres|]; eassumption.
Qed.

Lemma Incorect_disj {S A}
  (pres : S -> Prop)
  (w : Reader S A)
  (ach1 ach2 : A -> Prop) :
  Incorrect pres w ach1 ->
  Incorrect pres w ach2 ->
  Incorrect pres w (fun r => ach1 r \/ ach2 r).
Proof.
  now intros inc1 inc2 r [?%inc1 | ?%inc2].
Qed.

(* Dually to Incorrectness *)
Definition Correct {S A}
  (precondition : S -> Prop)
  (w : Reader S A)
  (postcondition : A -> Prop) : Prop :=
  forall r, SP precondition w r -> postcondition r.

Program Lemma Correct_alt {S A} (precondition : S -> Prop) (w : Reader S A) (postcondition : A -> Prop) :
  Correct precondition w postcondition <-> (forall s0 r, w s0 (precondition s0) r-> postcondition r).
Proof.
  split.
  - intros h s0 r hpre; apply h; exists s0; easy.
  - intros h r [s0 h']; eapply h, h'.
Qed.


Lemma SP_monotone {S A}
  {P1 P2 : S -> Prop}
  {w : WFReader S A} (* Need to assume monotonicity here *) :
  (forall s0, P1 s0 -> P2 s0) ->
  forall r, SP P1 w r -> SP P2 w r.
Proof.
  intros wk r [s0 h]; exists s0.
  eapply (proj2_sig w); [eapply wk|]; assumption.
Qed.

Lemma agreement {S A} (pres prec : S -> Prop) (w : WFReader S A) (ach post : A -> Prop) :
  Incorrect pres w ach ->
  (forall s0, pres s0 -> prec s0) ->
  Correct prec w post ->
  forall r, ach r -> post r.
Proof.
  intros inc wk_pre cor r ?.
  now apply cor, (SP_monotone wk_pre), inc.
Qed.

Definition example_3_1r : reader (nat * nat * nat) nat :=
  '(x, y, z) <- ask ;;
  if Nat.even x then
    if negb (Nat.even y) then ret 42 else ret z
  else ret z.

Definition example_3_1R : Reader (nat * nat * nat) nat :=
  '(x, y, z) <- ask ;;
  if Nat.even x then
    if negb (Nat.even y) then ret 42 else ret z
  else ret z.

Example example_3_1_test1 :
    Incorrect_
      (fun '(x, y, z) => z = 11)
      example_3_1R
      (fun '(x, y, z) r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  autounfold with mst. cbn; intros.
  exists (0, 1, 11). split; auto.
  cbn; intros. exists (0, 1, 11).
  hauto lq: on drew: off.
Qed.

Example example_3_1_test2 :
  Incorrect
    (fun '((x, y, z) as s0) => z = 11)
    example_3_1R
    (fun r => r = 42).
Proof.
  autounfold with mst.
  intros ? ->.
  pose (s := (0,1,11)); exists s, s; cbn.
  hauto.
Qed.

Theorem example_3_1_dijkstra :
  Verify example_3_1R example_3_1r (@obsReader (nat * nat * nat)%type).
Proof.
  unfold example_3_1R, example_3_1r.
  apply Verify_bind; [ apply Verify_ask | ].
  intros [[? ?] ?].
  destruct (Nat.even n) eqn:Hn; [ | apply Verify_ret ].
  destruct (Nat.even n0) eqn:Hn0; cbn; apply Verify_ret.
Qed.

Module Test2.

  Definition example_3_1R_ret_st : Reader (nat * nat * nat) (nat * nat * nat) :=
    '(x, y, z) <- ask ;;
    if Nat.even x then
      if negb (Nat.even y) then ret (x, y, 42) else ret (x, y, z)
    else ret (x, y, z).

  Example example_3_1_test1 :
    Incorrect_
      (fun '(x, y, z) => z = 11)
      example_3_1R_ret_st
      (fun _ '(x, y, z) =>
         z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
  Proof.
    autounfold with mst. cbn; intros.
    destruct r. destruct p.
    exists (n0, n1, 11). split; auto.
    cbn; intros. exists (n0, n1, 11).
    destruct H. destruct H0. simpl.
    hauto lq: on drew: off.
  Qed.

  Example example_3_1_test2 :
    Incorrect_
      (fun '(x, y, z) => z = 11)
      example_3_1R_ret_st
      (fun '(x0,y0,z0) '(x, y, z) => z = 42 /\ x0 = x /\ y0 = y).
  Proof.
    autounfold with mst. cbn; intros.
    exists (0, 1, 11). split; auto.
    cbn; intros. exists (0, 1, 11).
    hauto lq: on drew: off.
  Qed.

  Example example_3_1_test2':
    ~Incorrect
      (fun '(x, y, z) => z = 11)
      example_3_1R_ret_st
      (fun '(x, y, z) => z = 42).
  Proof.
    autounfold with mst.
    intros h; pose proof (h (0,0,42) eq_refl) as [[[x y] z] [[[x' y'] z'] ?]].
    destruct (Nat.even x'); cbn in *; [| hauto lq:on].
    destruct (Nat.even y') eqn:hy; cbn in *; [hauto lq: on|].
    hauto.
  Qed.

End Test2.

End WithStateFreeAchieves.



Module WithStateAwareAchieves.

(*  Trying to see what happens when the predicate on results
    has access to the reader state *)
(* After some tests, realizing that it is not so interesting:
  all the presumed assumptions on the input reader state needs to be implied by the
  achieved result since the reader state cannot change outside of the continuation.

  See example_3_1_test1 and example_3_1_test2 below.
*)

Program Definition SP {R S} (presumes : S -> Prop) (w : Reader S R) : S -> R -> Prop :=
  fun s0 r => w s0 (presumes s0) r.

Program Definition Incorrect {R S}
  (presumes : S -> Prop)
  (w : Reader S R)
  (achieves: S -> R -> Prop) : Prop :=
  forall s r, achieves s r -> SP presumes w s r.

Hint Unfold SP : mst.
Hint Unfold Incorrect : mst.

Lemma Incorect_weaken {S A}
  (pres1 pres2 : S -> Prop)
  (w : WFReader S A)  (* Need to assume monotonicity here *)
  (ach1 ach2 : S -> A -> Prop) :
  (forall s0, pres1 s0 -> pres2 s0) ->
  Incorrect pres1 w ach1 ->
  (forall s r, ach2 s r -> ach1 s r) ->
  Incorrect pres2 w ach2.
Proof.
  intros wk_pres inc wk_ach s r ?%wk_ach%inc.
  eapply (proj2_sig w);[ eapply wk_pres|]; eassumption.
Qed.

Lemma Incorect_disj {S A}
  (pres : S -> Prop)
  (w : Reader S A)
  (ach1 ach2 : S -> A -> Prop) :
  Incorrect pres w ach1 ->
  Incorrect pres w ach2 ->
  Incorrect pres w (fun s r => ach1 s r \/ ach2 s r).
Proof.
  now intros inc1 inc2 s r [?%inc1 | ?%inc2].
Qed.

(* Dually to Incorrectness *)
Definition Correct {S A}
  (precondition : S -> Prop)
  (w : Reader S A)
  (postcondition : S -> A -> Prop) : Prop :=
  forall s r, SP precondition w s r -> postcondition s r.

Program Lemma Correct_alt {S A} (precondition : S -> Prop) (w : Reader S A) (postcondition : S -> A -> Prop) :
  Correct precondition w postcondition <-> (forall s0 r, w s0 (precondition s0) r-> postcondition s0 r).
Proof.
  split.
  - intros h s0 r hpre; apply h; easy.
  - intros h s r h'. eapply h, h'.
Qed.


Lemma SP_monotone {S A}
  {P1 P2 : S -> Prop}
  {w : WFReader S A} (* Need to assume monotonicity here *) :
  (forall s0, P1 s0 -> P2 s0) ->
  forall s r, SP P1 w s r -> SP P2 w s r.
Proof.
  intros wk s r h.
  eapply (proj2_sig w); [eapply wk|]; assumption.
Qed.

Lemma agreement {S A} (pres prec : S -> Prop) (w : WFReader S A) (ach post : S -> A -> Prop) :
  Incorrect pres w ach ->
  (forall s0, pres s0 -> prec s0) ->
  Correct prec w post ->
  forall s r, ach s r -> post s r.
Proof.
  intros inc wk_pre cor s r ?.
  now apply cor, (SP_monotone wk_pre), inc.
Qed.

Definition example_3_1r : reader (nat * nat * nat) nat :=
  '(x, y, z) <- ask ;;
  if Nat.even x then
    if negb (Nat.even y) then ret 42 else ret z
  else ret z.

Definition example_3_1R : Reader (nat * nat * nat) nat :=
  '(x, y, z) <- ask ;;
  if Nat.even x then
    if negb (Nat.even y) then ret 42 else ret z
  else ret z.

Example example_3_1_test1 :
    Incorrect
      (fun '(x, y, z) => True)
      example_3_1R
      (fun '(x, y, z) r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true).
Proof.
  autounfold with mst. cbn; intros [[x y] z] r [-> [h1 h2]].
  exists (x,y,z); rewrite h1, h2; cbn.
  repeat constructor.
Qed.

Example example_3_1_test2 :
    Incorrect
      (fun '(x, y, z) => z = 11)
      example_3_1R
      (fun '(x, y, z) r => r = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true /\ z = 11).
Proof.
  autounfold with mst. cbn; intros [[x y] z] r [-> (h1&h2&->)].
  exists (x,y,11); rewrite h1, h2; cbn.
  repeat constructor.
Qed.

End WithStateAwareAchieves.


