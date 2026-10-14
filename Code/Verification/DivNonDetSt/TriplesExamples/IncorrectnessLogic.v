(** * O'Hearn's "Incorrectness Logic" (POPL 2020), as ITree programs

    The examples of the paper without concurrency: each triple it states is
    proved, or refuted where the paper calls it wrong.  A program is
    [prog S A = optionT (stateT S (itree ILE))]: an [error()] keeps its
    state, so [er:] assertions can talk about it; [assume false] diverges.
    Triples are the named logics of [Triples.v] on a program's denotation:
    [IncorrLogic] is O'Hearn's triple, [PartCorr] the Hoare triple, and
    [TotalCorr], [LisbonLogic] the [wp], [wpp] readings. *)

From Coq Require Import ZArith Lia Relations.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad MonadTrans.
From ITree Require Import ITree Eq Core.ITreeMonad.
From ITree Require Events.Nondeterminism.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.Verification.Generic Require Import Triple.
From Incorrectness.Verification.DivNonDet Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Computation.
From Incorrectness.Verification.DivNonDetSt Require Import Morphisms.
From Incorrectness.Verification.DivNonDetSt Require Import Triples.

Import MonadNotation.
Open Scope monad_scope.

(** * Programs *)

(** An arbitrary integer. *)
#[local] Unset Automatic Proposition Inductives.
Variant pickZE : Type -> Type :=
| PickZ : pickZE Z.

#[global] Instance HasAnswers_pickZE : HasAnswers pickZE.
Proof. intros X []. exact (inhabits 0%Z). Qed.

Definition ILE : Type -> Type := Nondeterminism.nondetE +' pickZE.

Notation prog S := (optionT (stateT S (itree ILE))).

Section Programs.
  Context {S : Type}.

  (** [error()]. *)
  Definition errorIL {A} : prog S A := mkOptionT (ret None).

  (** [C1 + C2]. *)
  Definition orIL {A} (C1 C2 : prog S A) : prog S A :=
    b <- lift (lift (ITree.trigger (inl1 Nondeterminism.Or))) ;;
    if b : bool then C1 else C2.

  (** [x = nondet()]: an arbitrary integer. *)
  Definition pickIL : prog S Z := lift (lift (ITree.trigger (inr1 PickZ))).

  (** [assume B]; [B] false diverges. *)
  Definition assumeIL (b : bool) : prog S unit :=
    if b then ret tt else lift (lift ITree.spin).

  Definition skipIL : prog S unit := ret tt.

  (** [while (true) {}]. *)
  Definition spinIL {A} : prog S A := lift (lift ITree.spin).

  (** [assert(B) = assume(B) + (assume(not B); error())]. *)
  Definition assertIL (b : bool) : prog S unit :=
    orIL (assumeIL b) (assumeIL (negb b) ;; errorIL).

  (** [C*]: zero or more iterations, [C* = skip + C; C*]. *)
  Definition starIL (C : prog S unit) : prog S unit :=
    Basics.iter (fun _ : unit => orIL (ret (inr tt)) (C ;; ret (inl tt))) tt.
End Programs.

(** * Triples *)

Definition denoteIL {S A} (C : prog S A) : stdivndNE S (option A) :=
  denoteSt S (option A) (unOptionT C).

(** The outcomes of [C] from [s]. *)
Definition outIL {S A} (C : prog S A) (s : S) (o : option (option A * S)) : Prop :=
  unOptionT (getNE (denote (runStateT (unOptionT C) s))) o.

(** [ok: q] and [er: q]. *)
Definition ok {S A} (q : S -> Prop) (r : option A * S) : Prop :=
  match fst r with Some _ => q (snd r) | None => False end.
Definition er {S A} (q : S -> Prop) (r : option A * S) : Prop :=
  match fst r with Some _ => False | None => q (snd r) end.

(** A program's triples are those of the named logics of [Triples.v] on its
    denotation: [IncorrLogic p (denoteIL C) q] is O'Hearn's [p]C[q]. *)

Section Readings.
  Context {S A : Type}.

  Lemma IncorrLogic_iff (p : S -> Prop) (C : prog S A) (q : option A * S -> Prop) :
    IncorrLogic p (denoteIL C) q <-> forall r, q r -> exists s, p s /\ outIL C s (Some r).
  Proof.
    split.
    - intros H r Hr. exact (proj1 (aspSt_read (denoteIL C) p r) (H r Hr)).
    - intros H r Hr. exact (proj2 (aspSt_read (denoteIL C) p r) (H r Hr)).
  Qed.

  Lemma PartCorr_iff (p : S -> Prop) (C : prog S A) (q : option A * S -> Prop) :
    PartCorr p (denoteIL C) q <-> forall s r, p s -> outIL C s (Some r) -> q r.
  Proof.
    split.
    - intros H s r Hs Ho. exact (proj1 (dwlpSt_read (denoteIL C) s q) (H s Hs) (Some r) Ho).
    - intros H s Hs. apply dwlpSt_read. intros [r|] Ho; [ exact (H s r Hs Ho) | exact I ].
  Qed.

  Lemma TotalCorr_iff (p : S -> Prop) (C : prog S A) (q : option A * S -> Prop) :
    TotalCorr p (denoteIL C) q <-> forall s, p s -> forall o, outIL C s o ->
                       match o with Some r => q r | None => False end.
  Proof.
    split; intros H s Hs.
    - exact (proj1 (dwpSt_read (denoteIL C) s q) (H s Hs)).
    - exact (proj2 (dwpSt_read (denoteIL C) s q) (H s Hs)).
  Qed.

  Lemma LisbonLogic_iff (p : S -> Prop) (C : prog S A) (q : option A * S -> Prop) :
    LisbonLogic p (denoteIL C) q <-> forall s, p s -> exists o, outIL C s o /\
                       match o with Some r => q r | None => False end.
  Proof.
    split; intros H s Hs.
    - exact (proj1 (awpSt_read (denoteIL C) s q) (H s Hs)).
    - exact (proj2 (awpSt_read (denoteIL C) s q) (H s Hs)).
  Qed.
End Readings.

(** * Outcomes, construct by construct *)

Section Outcomes.
  Context {S : Type}.

  (** Outcomes are invariant under [eutt]. *)
  Lemma outIL_eutt {A} (C : prog S A) (s : S) (t : itree ILE (option A * S)) o :
    eutt eq (runStateT (unOptionT C) s) t ->
    outIL C s o <-> unOptionT (getNE (denote t)) o.
  Proof. intro H. exact (eq1_outcomes _ _ (mm_proper denote_morphism _ _ H) o). Qed.

  Lemma outIL_ret {A} (a : A) (s : S) o :
    outIL (ret a : prog S A) s o <-> o = Some (Some a, s).
  Proof. unfold outIL. cbn. apply denote_ret. Qed.

  Lemma outIL_bind {A B} (C : prog S A) (k : A -> prog S B) (s : S) o :
    outIL (C >>= k) s o
    <-> exists o1, outIL C s o1 /\
          match o1 with
          | Some (Some a, s1) => outIL (k a) s1 o
          | Some (None, s1) => o = Some (None, s1)
          | None => o = None
          end.
  Proof.
    rewrite (outIL_eutt _ s
               (ITree.bind (runStateT (unOptionT C) s)
                  (fun vs => match vs with
                             | (Some a, s1) => runStateT (unOptionT (k a)) s1
                             | (None, s1) => Ret (None, s1)
                             end)) o).
    - rewrite denote_bind. split.
      + intros [[[[a|] s1]|] [H1 H2]];
          [ exists (Some (Some a, s1)) | exists (Some (None, s1)) | exists None ];
          (split; [ exact H1 |]); cbv beta iota in H2; try exact H2.
        apply denote_ret in H2. exact H2.
      + intros [[[[a|] s1]|] [H1 H2]];
          [ exists (Some (Some a, s1)) | exists (Some (None, s1)) | exists None ];
          (split; [ exact H1 |]); cbv beta iota; try exact H2.
        apply denote_ret. exact H2.
    - cbn. apply eutt_eq_bind. intros [[a|] s1]; reflexivity.
  Qed.

  Lemma outIL_error {A} (s : S) o :
    outIL (errorIL : prog S A) s o <-> o = Some (None, s).
  Proof. unfold outIL, errorIL. cbn. apply denote_ret. Qed.

  Lemma outIL_get (s : S) o : outIL (get : prog S S) s o <-> o = Some (Some s, s).
  Proof.
    rewrite (outIL_eutt _ s (Ret (Some s, s)) o).
    - apply denote_ret.
    - cbn. rewrite !Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma outIL_put (s' s : S) o : outIL (put s' : prog S unit) s o <-> o = Some (Some tt, s').
  Proof.
    rewrite (outIL_eutt _ s (Ret (Some tt, s')) o).
    - apply denote_ret.
    - cbn. rewrite !Eqit.bind_ret_l. reflexivity.
  Qed.

  (** A lifted tree keeps the state. *)
  (** A command with one [ok] outcome, followed by [k]. *)
  Lemma outIL_bind_det {A B} (C : prog S A) (k : A -> prog S B) (s : S) (a : A) (s1 : S) o :
    (forall o1, outIL C s o1 <-> o1 = Some (Some a, s1)) ->
    outIL (C >>= k) s o <-> outIL (k a) s1 o.
  Proof.
    intro HC. rewrite outIL_bind. split.
    - intros [o1 [H1 H2]]. apply HC in H1. subst o1. exact H2.
    - intro H. exists (Some (Some a, s1)). split; [ apply HC; reflexivity | exact H ].
  Qed.

  Lemma outIL_bind_assoc {A B C} (m : prog S A) (f : A -> prog S B) (g : B -> prog S C) s o :
    outIL ((m >>= f) >>= g) s o <-> outIL (m >>= fun a => f a >>= g) s o.
  Proof.
    rewrite !outIL_bind. split.
    - intros [o1 [H1 H2]]. apply outIL_bind in H1. destruct H1 as [o0 [H0 H01]].
      exists o0. split; [ exact H0 |]. destruct o0 as [[[a|] s0]|].
      + apply outIL_bind. exists o1. auto.
      + subst o1. exact H2.
      + subst o1. exact H2.
    - intros [o0 [H0 H]]. destruct o0 as [[[a|] s0]|].
      + apply outIL_bind in H. destruct H as [o1 [H1 H2]].
        exists o1. split; [ apply outIL_bind; exists (Some (Some a, s0)); auto | exact H2 ].
      + exists (Some (None, s0)). split; [ apply outIL_bind; exists (Some (None, s0)); auto | exact H ].
      + exists None. split; [ apply outIL_bind; exists None; auto | exact H ].
  Qed.

  (** [C; k] reaches what [k] reaches from an [ok] state of [C]. *)
  Lemma outIL_seq {A B} (C : prog S A) (k : A -> prog S B) s a s1 o :
    outIL C s (Some (Some a, s1)) -> outIL (k a) s1 o -> outIL (C >>= k) s o.
  Proof. intros H1 H2. apply outIL_bind. exists (Some (Some a, s1)). auto. Qed.

  Lemma outIL_if {A} (b : bool) (C1 C2 : prog S A) (s : S) o :
    outIL (if b then C1 else C2) s o
    <-> (b = true /\ outIL C1 s o) \/ (b = false /\ outIL C2 s o).
  Proof. destruct b; intuition discriminate. Qed.

  Lemma outIL_if_bind {A B} (b : bool) (C1 C2 : prog S A) (k : A -> prog S B) (s : S) o :
    outIL ((if b then C1 else C2) >>= k) s o
    <-> (b = true /\ outIL (C1 >>= k) s o) \/ (b = false /\ outIL (C2 >>= k) s o).
  Proof. destruct b; intuition discriminate. Qed.

  Lemma outIL_get_bind {A} (k : S -> prog S A) (s : S) o :
    outIL (get >>= k) s o <-> outIL (k s) s o.
  Proof. apply outIL_bind_det. intro. apply outIL_get. Qed.

  Lemma outIL_put_bind {A} (s' : S) (k : unit -> prog S A) (s : S) o :
    outIL (put s' >>= k) s o <-> outIL (k tt) s' o.
  Proof. apply outIL_bind_det. intro. apply outIL_put. Qed.

  Lemma outIL_ret_bind {A B} (a : A) (k : A -> prog S B) (s : S) o :
    outIL (ret a >>= k) s o <-> outIL (k a) s o.
  Proof. apply outIL_bind_det. intro. apply outIL_ret. Qed.

  Lemma outIL_error_bind {A B} (k : A -> prog S B) (s : S) o :
    outIL (errorIL >>= k) s o <-> o = Some (None, s).
  Proof.
    rewrite outIL_bind. split.
    - intros [o1 [H1 H2]]. apply outIL_error in H1. subst o1. exact H2.
    - intro H. exists (Some (None, s)). split; [ apply outIL_error; reflexivity | exact H ].
  Qed.

  Lemma outIL_lift {A} (t : itree ILE A) (s : S) o :
    outIL (lift (lift t) : prog S A) s o
    <-> match o with
        | Some (Some a, s') => s' = s /\ unOptionT (getNE (denote t)) (Some a)
        | Some (None, _) => False
        | None => unOptionT (getNE (denote t)) None
        end.
  Proof.
    rewrite (outIL_eutt _ s (ITree.bind t (fun a => Ret (Some a, s))) o).
    - rewrite denote_bind. destruct o as [[[a|] s']|]; split.
      + intros [[b|] [Ht Hr]]; [| discriminate Hr ].
        apply denote_ret in Hr. injection Hr as -> ->. split; [ reflexivity | exact Ht ].
      + intros [-> Ht]. exists (Some a). split; [ exact Ht | apply denote_ret; reflexivity ].
      + intros [[b|] [Ht Hr]]; [ apply denote_ret in Hr; discriminate | discriminate ].
      + intros [].
      + intros [[b|] [Ht Hr]]; [ apply denote_ret in Hr; discriminate | exact Ht ].
      + intro Ht. exists None. split; [ exact Ht | reflexivity ].
    - cbn. rewrite !Eqit.bind_bind.
      apply eutt_eq_bind. intro a. rewrite !Eqit.bind_ret_l. reflexivity.
  Qed.

  Lemma outIL_or {A} (C1 C2 : prog S A) (s : S) o :
    outIL (orIL C1 C2) s o <-> outIL C1 s o \/ outIL C2 s o.
  Proof.
    unfold orIL. rewrite outIL_bind. split.
    - intros [[[[b|] s1]|] [H1 H2]].
      + apply outIL_lift in H1. destruct H1 as [-> _]. destruct b; [ left | right ]; exact H2.
      + apply outIL_lift in H1. destruct H1.
      + apply outIL_lift in H1. unfold ITree.trigger in H1. apply denote_vis in H1.
        destruct H1 as [x Hx]. apply denote_ret in Hx. discriminate.
    - intros [H | H]; [ exists (Some (Some true, s)) | exists (Some (Some false, s)) ];
        (split; [| exact H ]); apply outIL_lift; (split; [ reflexivity |]);
        unfold ITree.trigger; apply denote_vis; eexists; apply denote_ret; reflexivity.
  Qed.

  Lemma outIL_pick (s : S) o : outIL (pickIL : prog S Z) s o <-> exists z, o = Some (Some z, s).
  Proof.
    unfold pickIL. rewrite outIL_lift. unfold ITree.trigger. destruct o as [[[z|] s']|]; split.
    - intros [-> _]. exists z. reflexivity.
    - intros [z' Hz]. injection Hz as -> ->. split; [ reflexivity |].
      apply denote_vis. eexists. apply denote_ret. reflexivity.
    - intros [].
    - intros [z Hz]. discriminate.
    - intro H. apply denote_vis in H. destruct H as [x Hx]. apply denote_ret in Hx. discriminate.
    - intros [z Hz]. discriminate.
  Qed.

  Lemma outIL_assume (b : bool) (s : S) o :
    outIL (assumeIL b : prog S unit) s o <-> (b = true /\ o = Some (Some tt, s)) \/ (b = false /\ o = None).
  Proof.
    unfold assumeIL. destruct b.
    - rewrite outIL_ret. split; [ intro H; left; exact (conj eq_refl H) | intros [[_ H] | [H _]]; [ exact H | discriminate ] ].
    - rewrite outIL_lift. destruct o as [[[[]|] s']|]; split.
      + intros [_ H]. apply denote_spin in H. discriminate.
      + intros [[H _] | [_ H]]; discriminate.
      + intros [].
      + intros [[H _] | [_ H]]; discriminate.
      + intros _. right. split; reflexivity.
      + intros _. apply denote_spin. reflexivity.
  Qed.

  Lemma outIL_spin {A} (s : S) o : outIL (spinIL : prog S A) s o <-> o = None.
  Proof.
    unfold spinIL. rewrite outIL_lift. destruct o as [[[a|] s']|]; split.
    - intros [_ H]. apply denote_spin in H. discriminate.
    - discriminate.
    - intros [].
    - discriminate.
    - intros _. reflexivity.
    - intros _. apply denote_spin. reflexivity.
  Qed.

  (** [assert] may also diverge, through the [assume] of the other branch. *)
  Lemma outIL_assert (b : bool) (s : S) o :
    outIL (assertIL b : prog S unit) s o
    <-> (b = true /\ o = Some (Some tt, s)) \/ (b = false /\ o = Some (None, s)) \/ o = None.
  Proof.
    unfold assertIL. rewrite outIL_or, outIL_bind, outIL_assume. split.
    - intros [[[-> ->] | [-> ->]] | [o1 [H1 H2]]].
      + left. split; reflexivity.
      + right; right. reflexivity.
      + apply outIL_assume in H1. destruct b; cbn in H1;
          destruct H1 as [[Hb ->] | [Hb ->]]; try discriminate.
        * right; right. exact H2.
        * apply outIL_error in H2. right; left. split; [ reflexivity | exact H2 ].
    - intros [[-> ->] | [[-> ->] | ->]].
      + left. left. split; reflexivity.
      + right. exists (Some (Some tt, s)). split; [ apply outIL_assume; left; split; reflexivity |].
        apply outIL_error. reflexivity.
      + destruct b.
        * right. exists None. split; [ apply outIL_assume; right; split; reflexivity | reflexivity ].
        * left. right. split; reflexivity.
  Qed.

  Lemma outIL_or_bind {A B} (C1 C2 : prog S A) (k : A -> prog S B) (s : S) o :
    outIL (orIL C1 C2 >>= k) s o <-> outIL (C1 >>= k) s o \/ outIL (C2 >>= k) s o.
  Proof.
    rewrite !outIL_bind. setoid_rewrite outIL_or. split.
    - intros [o1 [[H1 | H1] H2]]; [ left | right ]; exists o1; split; assumption.
    - intros [[o1 [H1 H2]] | [o1 [H1 H2]]]; exists o1; split; try assumption;
        [ left | right ]; assumption.
  Qed.

  Lemma outIL_pick_bind {B} (k : Z -> prog S B) (s : S) o :
    outIL (pickIL >>= k) s o <-> exists z, outIL (k z) s o.
  Proof.
    rewrite outIL_bind. setoid_rewrite outIL_pick. split.
    - intros [o1 [[z ->] H2]]. exists z. exact H2.
    - intros [z H]. exists (Some (Some z, s)). split; [ exists z; reflexivity | exact H ].
  Qed.

  Lemma outIL_assume_bind {B} (b : bool) (k : unit -> prog S B) (s : S) o :
    outIL (assumeIL b >>= k) s o <-> (b = true /\ outIL (k tt) s o) \/ (b = false /\ o = None).
  Proof.
    rewrite outIL_bind. setoid_rewrite outIL_assume. split.
    - intros [o1 [[[-> ->] | [-> ->]] H2]]; [ left | right ]; split; auto.
    - intros [[-> H] | [-> ->]];
        [ exists (Some (Some tt, s)) | exists None ]; split; auto.
  Qed.

  Lemma outIL_assert_bind {B} (b : bool) (k : unit -> prog S B) (s : S) o :
    outIL (assertIL b >>= k) s o
    <-> (b = true /\ outIL (k tt) s o) \/ (b = false /\ o = Some (None, s)) \/ o = None.
  Proof.
    rewrite outIL_bind. setoid_rewrite outIL_assert. split.
    - intros [o1 [[[-> ->] | [[-> ->] | ->]] H2]]; auto.
    - intros [[-> H] | [[-> ->] | ->]];
        [ exists (Some (Some tt, s)) | exists (Some (None, s)) | exists None ]; auto.
  Qed.

  Lemma outIL_spin_bind {A B} (k : A -> prog S B) (s : S) o :
    outIL (spinIL >>= k) s o <-> o = None.
  Proof.
    rewrite outIL_bind. setoid_rewrite outIL_spin. split.
    - intros [o1 [-> H2]]. exact H2.
    - intros ->. exists None. auto.
  Qed.

  (** A loop runs the base loop on the body's outcomes. *)
  Definition stepIL {I R} (body : I -> prog S (I + R)) (j : I * S)
    (o : option (I * S + (option R * S))) : Prop :=
    match o with
    | Some (inl (i', s')) => outIL (body (fst j)) (snd j) (Some (Some (inl i'), s'))
    | Some (inr (Some r, s')) => outIL (body (fst j)) (snd j) (Some (Some (inr r), s'))
    | Some (inr (None, s')) => outIL (body (fst j)) (snd j) (Some (None, s'))
    | None => outIL (body (fst j)) (snd j) None
    end.

  Lemma denote_eutt {A} (t u : itree ILE A) o :
    eutt eq t u -> unOptionT (getNE (denote t)) o <-> unOptionT (getNE (denote u)) o.
  Proof. intro H. exact (eq1_outcomes _ _ (mm_proper denote_morphism _ _ H) o). Qed.

  Lemma outIL_iter {I R} (body : I -> prog S (I + R)) (i : I) (s : S) o :
    outIL (Basics.iter body i) s o <-> iterOutcomes (stepIL body) (i, s) o.
  Proof.
    unfold outIL.
    cbv [Basics.iter MonadIter_stateT MonadIter_optionT MonadIter_itree]. cbn [runStateT unOptionT].
    rewrite denote_iter, outcomes_iter. apply iterOutcomes_ext. intros [i0 s0] o'.
    rewrite (denote_eutt _
               (ITree.bind (runStateT (unOptionT (body i0)) s0)
                  (fun vs : option (I + R) * S =>
                     match vs with
                     | (Some (inl i'), s') => Ret (inl (i', s'))
                     | (Some (inr r), s') => Ret (inr (Some r, s'))
                     | (None, s') => Ret (inr (None, s'))
                     end)) o').
    - rewrite denote_bind. unfold stepIL. cbn [fst snd]. split.
      + intros [[[[[i'|r]|] s1]|] [H1 H2]]; cbv beta iota in H2;
          try (apply denote_ret in H2); subst o'; exact H1.
      + destruct o' as [[[i' s'] | [[r|] s']]|]; intro H;
          [ exists (Some (Some (inl i'), s')) | exists (Some (Some (inr r), s'))
          | exists (Some (None, s')) | exists None ];
          (split; [ exact H |]); cbv beta iota; try (apply denote_ret); reflexivity.
    - cbn. rewrite !Eqit.bind_bind. apply eutt_eq_bind. intros [[[i'|r]|] s'];
        cbn; rewrite ?Eqit.bind_ret_l; reflexivity.
  Qed.
  (** One iteration of [C*]: exit, or run [C]. *)
  Lemma starIL_step (C : prog S unit) (s : S) o' :
    stepIL (fun _ : unit => orIL (ret (inr tt)) (C ;; ret (inl tt))) (tt, s) o'
    <-> match o' with
        | Some (inl (_, s')) => outIL C s (Some (Some tt, s'))
        | Some (inr (Some _, s')) => s' = s
        | Some (inr (None, s')) => outIL C s (Some (None, s'))
        | None => outIL C s None
        end.
  Proof.
    unfold stepIL. destruct o' as [[[[] s'] | [[[]|] s']]|]; cbn [fst snd];
      rewrite outIL_or, outIL_ret, outIL_bind; split.
    - intros [H | [[[[[]|] s1]|] [H1 H2]]]; try discriminate H; try discriminate H2.
      apply outIL_ret in H2. injection H2 as <-. exact H1.
    - intro H. right. exists (Some (Some tt, s')). split; [ exact H | apply outIL_ret; reflexivity ].
    - intros [H | [[[[[]|] s1]|] [H1 H2]]]; [ injection H as -> | | |];
        try reflexivity; try discriminate H2.
      apply outIL_ret in H2. discriminate.
    - intros ->. left. reflexivity.
    - intros [H | [[[[[]|] s1]|] [H1 H2]]]; try discriminate H; try discriminate H2.
      + apply outIL_ret in H2. discriminate.
      + injection H2 as <-. exact H1.
    - intro H. right. exists (Some (None, s')). split; [ exact H | reflexivity ].
    - intros [H | [[[[[]|] s1]|] [H1 H2]]]; try discriminate H; try discriminate H2.
      + apply outIL_ret in H2. discriminate.
      + exact H1.
    - intro H. right. exists None. split; [ exact H | reflexivity ].
  Qed.

  Lemma outIL_star (C : prog S unit) (s : S) o :
    outIL (starIL C) s o
    <-> iterOutcomes (stepIL (fun _ : unit => orIL (ret (inr tt)) (C ;; ret (inl tt)))) (tt, s) o.
  Proof. exact (outIL_iter _ tt s o). Qed.

  (** The rules Iterate zero and non-zero. *)
  Lemma starIL_ok (C : prog S unit) (s s' : S) :
    clos_refl_trans_1n S (fun s1 s2 => outIL C s1 (Some (Some tt, s2))) s s' ->
    outIL (starIL C) s (Some (Some tt, s')).
  Proof.
    intro Hr. apply outIL_star. induction Hr as [s | s s1 s' H1 _ IH];
      apply iterOutcomes_unfold.
    - exists (Some (inr (Some tt, s))). split; [ apply starIL_step; reflexivity | reflexivity ].
    - exists (Some (inl (tt, s1))). split; [ apply starIL_step; exact H1 | exact IH ].
  Qed.

  Lemma starIL_er (C : prog S unit) (s s1 s' : S) :
    clos_refl_trans_1n S (fun s1 s2 => outIL C s1 (Some (Some tt, s2))) s s1 ->
    outIL C s1 (Some (None, s')) ->
    outIL (starIL C) s (Some (None, s')).
  Proof.
    intros Hr Herr. apply outIL_star. induction Hr as [s | s s2 s1 H1 _ IH];
      apply iterOutcomes_unfold.
    - exists (Some (inr (None, s'))). split; [ apply starIL_step; exact Herr | reflexivity ].
    - exists (Some (inl (tt, s2))). split; [ apply starIL_step; exact H1 | exact (IH Herr) ].
  Qed.
End Outcomes.

(** Outcomes of straight-line code.  Lemmas are tried only where their
    command occurs: a failed unification unfolds both monad stacks. *)
Ltac il_simpl :=
  repeat match goal with
    | |- context [outIL (bind (bind _ _) _) _ _] => first [ rewrite outIL_bind_assoc | setoid_rewrite outIL_bind_assoc ]
    | |- context [outIL (bind get _) _ _] => first [ rewrite outIL_get_bind | setoid_rewrite outIL_get_bind ]
    | |- context [outIL (bind (put _) _) _ _] => first [ rewrite outIL_put_bind | setoid_rewrite outIL_put_bind ]
    | |- context [outIL (bind (ret _) _) _ _] => first [ rewrite outIL_ret_bind | setoid_rewrite outIL_ret_bind ]
    | |- context [outIL (bind errorIL _) _ _] => first [ rewrite outIL_error_bind | setoid_rewrite outIL_error_bind ]
    | |- context [outIL (bind pickIL _) _ _] => first [ rewrite outIL_pick_bind | setoid_rewrite outIL_pick_bind ]
    | |- context [outIL (bind (orIL _ _) _) _ _] => first [ rewrite outIL_or_bind | setoid_rewrite outIL_or_bind ]
    | |- context [outIL (bind (assumeIL _) _) _ _] => first [ rewrite outIL_assume_bind | setoid_rewrite outIL_assume_bind ]
    | |- context [outIL (bind (assertIL _) _) _ _] => first [ rewrite outIL_assert_bind | setoid_rewrite outIL_assert_bind ]
    | |- context [outIL (bind spinIL _) _ _] => first [ rewrite outIL_spin_bind | setoid_rewrite outIL_spin_bind ]
    | |- context [outIL get _ _] => first [ rewrite outIL_get | setoid_rewrite outIL_get ]
    | |- context [outIL (put _) _ _] => first [ rewrite outIL_put | setoid_rewrite outIL_put ]
    | |- context [outIL (ret _) _ _] => first [ rewrite outIL_ret | setoid_rewrite outIL_ret ]
    | |- context [outIL errorIL _ _] => first [ rewrite outIL_error | setoid_rewrite outIL_error ]
    | |- context [outIL (orIL _ _) _ _] => first [ rewrite outIL_or | setoid_rewrite outIL_or ]
    | |- context [outIL pickIL _ _] => first [ rewrite outIL_pick | setoid_rewrite outIL_pick ]
    | |- context [outIL (assumeIL _) _ _] => first [ rewrite outIL_assume | setoid_rewrite outIL_assume ]
    | |- context [outIL (assertIL _) _ _] => first [ rewrite outIL_assert | setoid_rewrite outIL_assert ]
    | |- context [outIL spinIL _ _] => first [ rewrite outIL_spin | setoid_rewrite outIL_spin ]
    | |- context [skipIL] => unfold skipIL
    | |- context [outIL (bind (if _ then _ else _) _) _ _] => first [ rewrite outIL_if_bind | setoid_rewrite outIL_if_bind ]
    | |- context [outIL (if _ then _ else _) _ _] => first [ rewrite outIL_if | setoid_rewrite outIL_if ]
    | |- _ => progress cbn [fst snd negb andb orb]
    end.

(** * The examples *)

Open Scope Z_scope.

(** ** Section 3: beginning examples *)

Module UnderApproximation.

(** *** Section 3.1 *)

Definition z42 : prog (Z * Z * Z) unit :=
  st <- get ;;
  let '(x, y, z) := st in
  if Z.even x then (if negb (Z.even y) then put (x, y, 42) else skipIL) else skipIL.

Lemma z42_out (x y z : Z) o :
  outIL z42 (x, y, z) o
  <-> o = Some (Some tt, if andb (Z.even x) (negb (Z.even y)) then (x, y, 42) else (x, y, z)).
Proof.
  unfold z42. rewrite outIL_bind. split.
  - intros [o1 [H1 H2]]. apply outIL_get in H1. subst o1. cbv beta iota in H2.
    destruct (Z.even x), (Z.even y); cbn [negb andb] in H2 |- *;
      first [ exact (proj1 (outIL_put _ _ _) H2) | exact (proj1 (outIL_ret _ _ _) H2) ].
  - intro H. exists (Some (Some (x, y, z), (x, y, z))).
    split; [ apply outIL_get; reflexivity |]. cbv beta iota.
    destruct (Z.even x), (Z.even y); cbn [negb andb] in H |- *;
      first [ exact (proj2 (outIL_put _ _ _) H) | exact (proj2 (outIL_ret _ _ _) H) ].
Qed.

(** [[z == 11] P [ok: z == 42]] is false. *)
Theorem z42_not_under :
  ~ IncorrLogic (fun '(_, _, z) => z = 11) (denoteIL z42) (ok (fun '(_, _, z) => z = 42)).
Proof.
  rewrite IncorrLogic_iff. intro H.
  destruct (H (Some tt, (1, 2, 42)) eq_refl) as [[[x y] z] [Hz Ho]].
  apply z42_out in Ho. cbn in Hz. injection Ho as Hst.
  destruct (Z.even x) eqn:Hx, (Z.even y); cbn [negb andb] in Hst; injection Hst; intros;
    subst; try discriminate Hx; lia.
Qed.

(** [[z == 11] P [ok: z == 42 && x is even && y is odd]]. *)
Theorem z42_under :
  IncorrLogic (fun '(_, _, z) => z = 11) (denoteIL z42)
     (ok (fun '(x, y, z) => z = 42 /\ Z.even x = true /\ Z.even y = false)).
Proof.
  rewrite IncorrLogic_iff. intros [[[] | ] [[x y] z]] Hq; [| destruct Hq ].
  cbn in Hq. destruct Hq as [-> [Hx Hy]].
  exists (x, y, 11). split; [ reflexivity |].
  apply z42_out. rewrite Hx, Hy. reflexivity.
Qed.

(** [[true] P [ok: z == 42]]. *)
Theorem z42_true_pre :
  IncorrLogic (fun _ => True) (denoteIL z42) (ok (fun '(_, _, z) => z = 42)).
Proof.
  rewrite IncorrLogic_iff. intros [[[] | ] [[x y] z]] Hq; [| destruct Hq ]. cbn in Hq. subst z.
  destruct (andb (Z.even x) (negb (Z.even y))) eqn:Hc.
  - exists (x, y, 11). split; [ exact I | apply z42_out; rewrite Hc; reflexivity ].
  - exists (x, y, 42). split; [ exact I | apply z42_out; rewrite Hc; reflexivity ].
Qed.

(** *** Section 3.2 *)

(** Copying [str] into a 16-byte buffer. *)
Definition foo : prog (list nat) unit :=
  str <- get ;;
  if Nat.ltb 16 (length str) then errorIL else skipIL.

Theorem foo_overflow (s : list nat) :
  IncorrLogic (fun str => str = s) (denoteIL foo) (er (fun str => str = s /\ (16 < length s)%nat)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] str] Hq; [ destruct Hq |]. cbn in Hq. destruct Hq as [-> Hlen].
  exists s. split; [ reflexivity |]. unfold foo. apply outIL_bind.
  exists (Some (Some s, s)). split; [ apply outIL_get; reflexivity |]. cbv beta iota.
  rewrite (proj2 (Nat.ltb_lt _ _) Hlen). apply outIL_error. reflexivity.
Qed.

(** *** Section 3.3 *)

Definition mkeven : prog Z unit := put 2.

Definition usemkeven : prog Z unit :=
  mkeven ;; x <- get ;; if x =? 4 then errorIL else skipIL.

Lemma usemkeven_out (s : Z) o : outIL usemkeven s o <-> o = Some (Some tt, 2).
Proof.
  unfold usemkeven, mkeven. rewrite outIL_bind. split.
  - intros [o1 [H1 H2]]. apply outIL_put in H1. subst o1.
    apply outIL_bind in H2. destruct H2 as [o2 [H2 H3]]. apply outIL_get in H2. subst o2.
    cbv beta iota in H3. exact (proj1 (outIL_ret _ _ _) H3).
  - intros ->. exists (Some (Some tt, 2)). split; [ apply outIL_put; reflexivity |].
    apply outIL_bind. exists (Some (Some 2, 2)). split; [ apply outIL_get; reflexivity |].
    cbv beta iota. apply outIL_ret. reflexivity.
Qed.

(** The wrong achieves [ok: x == 2 || x == 4]. *)
Theorem mkeven_not_under :
  ~ IncorrLogic (fun _ => True) (denoteIL mkeven) (ok (fun x => x = 2 \/ x = 4)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 4) (or_intror eq_refl)) as [s [_ Ho]].
  apply outIL_put in Ho. discriminate.
Qed.

Theorem mkeven_under : IncorrLogic (fun _ => True) (denoteIL mkeven) (ok (fun x => x = 2)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; [| destruct Hq ]. cbn in Hq. subst x.
  exists 0. split; [ exact I | apply outIL_put; reflexivity ].
Qed.

(** No run of [usemkeven] raises: every result is an [ok] exit ... *)
Theorem usemkeven_no_error : PartCorr (fun _ => True) (denoteIL usemkeven) (ok (fun _ => True)).
Proof.
  rewrite PartCorr_iff. intros s r _ Ho. apply usemkeven_out in Ho. injection Ho as ->. exact I.
Qed.

(** ... so the error the wrong achieves would predict is not reachable. *)
Theorem usemkeven_not_er : ~ IncorrLogic (fun _ => True) (denoteIL usemkeven) (er (fun x => x = 4)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (None, 4) eq_refl) as [s [_ Ho]].
  apply usemkeven_out in Ho. discriminate.
Qed.

(** [while(true){}; x = 2]. *)
Definition mkevenDiv : prog Z unit := (spinIL : prog Z unit) ;; put 2.

Definition usemkevenDiv : prog Z unit :=
  mkevenDiv ;; x <- get ;; if x =? 4 then errorIL else skipIL.

Lemma mkevenDiv_out (s : Z) o : outIL mkevenDiv s o <-> o = None.
Proof.
  unfold mkevenDiv. rewrite outIL_bind. split.
  - intros [o1 [H1 H2]]. apply outIL_spin in H1. subst o1. exact H2.
  - intros ->. exists None. split; [ apply outIL_spin; reflexivity | reflexivity ].
Qed.

(** [ok: x == 4] over-approximates its (no) results ... *)
Theorem mkevenDiv_over : PartCorr (fun _ => True) (denoteIL mkevenDiv) (ok (fun x => x = 4)).
Proof.
  rewrite PartCorr_iff. intros s r _ Ho. apply mkevenDiv_out in Ho. discriminate.
Qed.

(** ... but does not under-approximate them ... *)
Theorem mkevenDiv_not_under :
  ~ IncorrLogic (fun _ => True) (denoteIL mkevenDiv) (ok (fun x => x = 4)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 4) eq_refl) as [s [_ Ho]].
  apply mkevenDiv_out in Ho. discriminate.
Qed.

(** ... and the error in [usemkevenDiv] is not reachable. *)
Theorem usemkevenDiv_not_er :
  ~ IncorrLogic (fun _ => True) (denoteIL usemkevenDiv) (er (fun x => x = 4)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (None, 4) eq_refl) as [s [_ Ho]].
  unfold usemkevenDiv in Ho. apply outIL_bind in Ho. destruct Ho as [o1 [H1 H2]].
  apply mkevenDiv_out in H1. subst o1. discriminate.
Qed.

End UnderApproximation.

(** ** Sections 4 and 5: the examples around the proof rules *)

Module ProofRules.

(** *** Abnormal termination *)

Definition errSeq : prog Z unit := put 1 ;; (errorIL : prog Z unit) ;; put 42.

Lemma errSeq_out (s : Z) o : outIL errSeq s o <-> o = Some (None, 1).
Proof. unfold errSeq. il_simpl. reflexivity. Qed.

Theorem errSeq_er : IncorrLogic (fun _ => True) (denoteIL errSeq) (er (fun x => x = 1)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq |]. subst x.
  exists 0. split; [ exact I | apply errSeq_out; reflexivity ].
Qed.

Theorem errSeq_not_ok : ~ IncorrLogic (fun _ => True) (denoteIL errSeq) (ok (fun x => x = 42)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 42) eq_refl) as [s [_ Ho]].
  apply errSeq_out in Ho. discriminate.
Qed.

Theorem errSeq_hl : PartCorr (fun _ => True) (denoteIL errSeq) (er (fun x => x = 1)).
Proof.
  rewrite PartCorr_iff. intros s r _ Ho. apply errSeq_out in Ho. injection Ho as ->. reflexivity.
Qed.

(** *** Assignment *)

(** [x = 42], on the state [(x, y)]. *)
Definition assign42 : prog (Z * Z) unit := st <- get ;; put (42, snd st).

Lemma assign42_out (x y : Z) o : outIL assign42 (x, y) o <-> o = Some (Some tt, (42, y)).
Proof. unfold assign42. il_simpl. reflexivity. Qed.

Theorem hoare_assign_not_under :
  ~ IncorrLogic (fun '(_, y) => 42 = y) (denoteIL assign42) (ok (fun '(x, y) => x = y)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, (3, 3)) eq_refl) as [[x y] [_ Ho]].
  apply assign42_out in Ho. discriminate.
Qed.

Theorem hoare_assign_over :
  PartCorr (fun '(_, y) => 42 = y) (denoteIL assign42) (ok (fun '(x, y) => x = y)).
Proof.
  rewrite PartCorr_iff. intros [x y] r Hy Ho. apply assign42_out in Ho. injection Ho as ->. exact Hy.
Qed.

Theorem floyd_assign :
  IncorrLogic (fun '(_, y) => 42 = y) (denoteIL assign42) (ok (fun '(x, y) => x = 42 /\ y = 42)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] [x y]] Hq; cbn in Hq; [| destruct Hq ].
  destruct Hq as [-> ->]. exists (0, 42). split; [ reflexivity | apply assign42_out; reflexivity ].
Qed.

(** *** [assert] *)

Definition assertEven : prog Z unit := x <- get ;; assertIL (Z.even x).

Lemma assertEven_out (s : Z) r :
  outIL assertEven s (Some r)
  <-> (Z.even s = true /\ r = (Some tt, s)) \/ (Z.even s = false /\ r = (None, s)).
Proof.
  unfold assertEven. il_simpl. split.
  - intros [[He H] | [[He H] | H]]; [ left | right | discriminate ];
      injection H as <-; auto.
  - intros [[He ->] | [He ->]]; auto.
Qed.

(** The two quadruples of the rule for [+] ... *)
Theorem assert_even :
  IncorrLogic (fun x => Z.even x = true) (denoteIL assertEven) (ok (fun x => Z.even x = true))
  /\ IncorrLogic (fun x => Z.even x = true) (denoteIL assertEven) (er (fun _ => False)).
Proof.
  rewrite !IncorrLogic_iff. split; intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq | destruct Hq ..].
  exists x. split; [ exact Hq | apply assertEven_out; auto ].
Qed.

Theorem assert_odd :
  IncorrLogic (fun x => Z.even x = false) (denoteIL assertEven) (ok (fun _ => False))
  /\ IncorrLogic (fun x => Z.even x = false) (denoteIL assertEven) (er (fun x => Z.even x = false)).
Proof.
  rewrite !IncorrLogic_iff. split; intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq .. |].
  exists x. split; [ exact Hq | apply assertEven_out; auto ].
Qed.

(** ... and the one that postpones the test. *)
Theorem assert_true :
  IncorrLogic (fun _ => True) (denoteIL assertEven) (ok (fun x => Z.even x = true))
  /\ IncorrLogic (fun _ => True) (denoteIL assertEven) (er (fun x => Z.even x = false)).
Proof.
  rewrite !IncorrLogic_iff. split; intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq | destruct Hq |];
    exists x; (split; [ exact I | apply assertEven_out; auto ]).
Qed.

(** *** No conjunction rule *)

Definition choice88 : prog Z unit :=
  orIL (x <- get ;; assumeIL (x =? 1) ;; put 88)
       (x <- get ;; assumeIL (x =? 2) ;; put 88).

Lemma choice88_out (s : Z) r :
  outIL choice88 s (Some r) <-> (s = 1 \/ s = 2) /\ r = (Some tt, 88).
Proof.
  unfold choice88. il_simpl. rewrite !Z.eqb_eq. split.
  - intros [[[-> H] | [_ H]] | [[-> H] | [_ H]]];
      try discriminate H; injection H as <-; auto.
  - intros [[-> | ->] ->]; [ left | right ]; left; auto.
Qed.

Theorem choice88_one : IncorrLogic (fun x => x = 1) (denoteIL choice88) (ok (fun x => x = 88)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ]. subst x.
  exists 1. split; [ reflexivity | apply choice88_out; auto ].
Qed.

Theorem choice88_two : IncorrLogic (fun x => x = 2) (denoteIL choice88) (ok (fun x => x = 88)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ]. subst x.
  exists 2. split; [ reflexivity | apply choice88_out; auto ].
Qed.

Theorem choice88_not_conj :
  ~ IncorrLogic (fun x => x = 1 /\ x = 2) (denoteIL choice88) (ok (fun x => x = 88)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 88) eq_refl) as [s [[H1 H2] _]]. lia.
Qed.

(** *** Fact 9 *)

Theorem no_presumption (p : Z -> Prop) :
  ~ IncorrLogic p (denoteIL (put 41 : prog Z unit)) (ok (fun _ => True)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 0) I) as [s [_ Ho]].
  apply outIL_put in Ho. discriminate.
Qed.

End ProofRules.

(** ** Section 6.1, Figure 5: loops; the state is [x], presumptions default to [true] *)

Module Loops.

(** [if (x == v) { error(); }] *)
Definition errorIfX (v : Z) : prog Z unit :=
  x <- get ;; if x =? v then errorIL else skipIL.

Lemma errorIfX_out (v x : Z) o :
  outIL (errorIfX v) x o <-> o = Some (if x =? v then None else Some tt, x).
Proof. unfold errorIfX. il_simpl. destruct (x =? v); sauto limit: 200. Qed.

(** [x = x + 1] *)
Definition incX : prog Z unit := x <- get ;; put (x + 1).

Lemma incX_out (x : Z) o : outIL incX x o <-> o = Some (Some tt, x + 1).
Proof. unfold incX. il_simpl. reflexivity. Qed.

(** *** [loop0] and [client0] *)

Definition loop0Body (n : Z) : prog Z (Z + unit) :=
  if 0 <? n then (x <- get ;; put (x + n) ;; n' <- pickIL ;; ret (inl n'))
  else ret (inr tt).

Definition loop0 : prog Z unit :=
  n <- pickIL ;; put 0 ;; Basics.iter loop0Body n.

Lemma loop0_step (n x : Z) o :
  stepIL loop0Body (n, x) o
  <-> if 0 <? n then exists n', o = Some (inl (n', x + n)) else o = Some (inr (Some tt, x)).
Proof.
  unfold stepIL, loop0Body. cbn [fst snd].
  destruct (0 <? n); destruct o as [[[i' s'] | [[[]|] s']]|]; il_simpl; sauto limit: 200.
Qed.

(** One unrolling: pick [n = x], then exit with [n = 0]. *)
Lemma loop0_reach (s x : Z) : 0 <= x -> outIL loop0 s (Some (Some tt, x)).
Proof.
  intro Hx. unfold loop0. il_simpl. exists x. apply outIL_iter. left.
  destruct (Z.eq_dec x 0) as [-> | Hx0].
  - apply iterOut_exit. apply loop0_step. reflexivity.
  - apply (iterOut_next _ _ (0, x)).
    + apply loop0_step. rewrite (proj2 (Z.ltb_lt 0 x) ltac:(lia)). exists 0. reflexivity.
    + apply iterOut_exit. apply loop0_step. reflexivity.
Qed.

Theorem loop0_achieves : IncorrLogic (fun _ => True) (denoteIL loop0) (ok (fun x => 0 <= x)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  exists 0. split; [ exact I | apply loop0_reach; exact Hq ].
Qed.

Theorem loop0_hoare : PartCorr (fun _ => True) (denoteIL loop0) (ok (fun x => 0 <= x)).
Proof.
  rewrite PartCorr_iff. intros s r _. unfold loop0. il_simpl. intros [n Ho].
  apply outIL_iter in Ho. destruct Ho as [Ho | [Hc _]]; [| discriminate Hc ].
  refine (iterOut_invariant _ (fun '(_, x) => 0 <= x)
            (fun o => match o with Some r => ok (fun x => 0 <= x) r | None => True end)
            _ (n, 0) (Some r) (Z.le_refl 0) Ho).
  intros [n' x] o Hx Hs. apply loop0_step in Hs.
  destruct (Z.ltb_spec 0 n'); [ destruct Hs as [n'' ->] | subst o ]; cbn; lia.
Qed.

Definition client0 : prog Z unit := loop0 ;; errorIfX 2000000.

Theorem client0_achieves :
  IncorrLogic (fun _ => True) (denoteIL client0) (er (fun x => x = 2000000)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq |]. subst x.
  exists 0. split; [ exact I |].
  apply (outIL_seq _ _ _ tt 2000000); [ apply loop0_reach; lia |].
  apply errorIfX_out. reflexivity.
Qed.

(** *** [loop1] and [client1] *)

Definition loop1 : prog Z unit := put 0 ;; starIL incX.

(** [k] iterations of [x = x + 1]. *)
Lemma incX_steps (k : nat) (a : Z) :
  clos_refl_trans_1n Z (fun s1 s2 => outIL incX s1 (Some (Some tt, s2))) a (a + Z.of_nat k).
Proof.
  revert a. induction k as [| k IH]; intro a.
  - rewrite Z.add_0_r. apply rt1n_refl.
  - apply (Relation_Operators.rt1n_trans _ _ _ (a + 1)); [ apply incX_out; reflexivity |].
    replace (a + Z.of_nat (S k)) with (a + 1 + Z.of_nat k) by lia. apply IH.
Qed.

Lemma loop1_reach (s x : Z) : 0 <= x -> outIL loop1 s (Some (Some tt, x)).
Proof.
  intro Hx. unfold loop1. il_simpl. apply starIL_ok.
  replace x with (0 + Z.of_nat (Z.to_nat x)) by lia. apply incX_steps.
Qed.

Theorem loop1_achieves1 :
  IncorrLogic (fun _ => True) (denoteIL loop1) (ok (fun x => x = 0 \/ x = 1 \/ x = 2 \/ x = 3)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  exists 0. split; [ exact I | apply loop1_reach; lia ].
Qed.

Theorem loop1_achieves2 : IncorrLogic (fun _ => True) (denoteIL loop1) (ok (fun x => 0 <= x)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  exists 0. split; [ exact I | apply loop1_reach; exact Hq ].
Qed.

(** [achieves1] under-approximates: [x == 4] is reached too. *)
Theorem loop1_achieves1_not_hoare :
  ~ PartCorr (fun _ => True) (denoteIL loop1) (ok (fun x => x = 0 \/ x = 1 \/ x = 2 \/ x = 3)).
Proof.
  rewrite PartCorr_iff. intro H. specialize (H 0 (Some tt, 4) I (loop1_reach 0 4 ltac:(lia))).
  cbn in H. lia.
Qed.

(** Always choosing another iteration runs forever. *)
Theorem loop1_may_diverge (s : Z) : outIL loop1 s None.
Proof.
  unfold loop1. il_simpl. apply outIL_star. right. split; [ reflexivity |].
  apply (loopsForever_recurrence _ (fun _ => True)); [| exact I ].
  intros [[] x] _. exists (tt, x + 1). split; [| exact I ].
  apply starIL_step. apply incX_out. reflexivity.
Qed.

Definition client1 : prog Z unit := loop1 ;; errorIfX 2000000.

Theorem client1_achieves :
  IncorrLogic (fun _ => True) (denoteIL client1) (er (fun x => x = 2000000)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq |]. subst x.
  exists 0. split; [ exact I |].
  apply (outIL_seq _ _ _ tt 2000000); [ apply loop1_reach; lia |].
  apply errorIfX_out. reflexivity.
Qed.

(** *** [loop2] *)

Definition loop2Body : prog Z unit := errorIfX 2000000 ;; incX.

Definition loop2 : prog Z unit := put 0 ;; starIL loop2Body.

Lemma loop2Body_out (x : Z) o :
  outIL loop2Body x o
  <-> (x = 2000000 /\ o = Some (None, x)) \/ (x <> 2000000 /\ o = Some (Some tt, x + 1)).
Proof.
  unfold loop2Body. rewrite (outIL_bind (errorIfX 2000000)). setoid_rewrite errorIfX_out.
  destruct (Z.eqb_spec x 2000000) as [-> | Hx]; split.
  - intros [o1 [-> H]]. auto.
  - intros [[_ ->] | [Hx _]]; [| contradiction ]. eexists. split; reflexivity.
  - intros [o1 [-> H]]. right. split; [ exact Hx | exact (proj1 (incX_out _ _) H) ].
  - intros [[Hx' _] | [_ ->]]; [ contradiction |].
    eexists. split; [ reflexivity | apply incX_out; reflexivity ].
Qed.

(** The frontier: [x] counts up to [2,000,000]. *)
Lemma loop2Body_steps (k : nat) (a : Z) :
  a + Z.of_nat k <= 2000000 ->
  clos_refl_trans_1n Z (fun s1 s2 => outIL loop2Body s1 (Some (Some tt, s2))) a (a + Z.of_nat k).
Proof.
  revert a. induction k as [| k IH]; intros a Hk.
  - rewrite Z.add_0_r. apply rt1n_refl.
  - apply (Relation_Operators.rt1n_trans _ _ _ (a + 1)); [ apply loop2Body_out; right; split; [ lia | reflexivity ] |].
    replace (a + Z.of_nat (S k)) with (a + 1 + Z.of_nat k) by lia. apply IH. lia.
Qed.

Theorem loop2_frontier :
  IncorrLogic (fun x => x = 0) (denoteIL (starIL loop2Body)) (ok (fun x => 0 <= x <= 2000000)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  exists 0. split; [ reflexivity |]. apply starIL_ok.
  replace x with (0 + Z.of_nat (Z.to_nat x)) by lia. apply loop2Body_steps. lia.
Qed.

Theorem loop2_achieves : IncorrLogic (fun _ => True) (denoteIL loop2) (er (fun x => x = 2000000)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq |]. subst x.
  exists 0. split; [ exact I |]. unfold loop2. il_simpl.
  apply (starIL_er _ _ 2000000).
  - replace 2000000 with (0 + Z.of_nat (Z.to_nat 2000000)) by lia. apply loop2Body_steps. lia.
  - apply loop2Body_out. left. split; reflexivity.
Qed.

End Loops.

(** ** Section 6.2, Figures 6 and 7: conditionals *)

Module Conditionals.

(** *** Figure 6 *)

Definition difficult (z : Z) : Z := z * z.

Definition client : prog (Z * Z) unit :=
  z <- pickIL ;; st <- get ;;
  if snd st =? difficult z then put (1, snd st) else put (2, snd st).

Lemma client_out (x y : Z) r :
  outIL client (x, y) (Some r)
  <-> exists z, (y = difficult z /\ r = (Some tt, (1, y)))
                \/ (y <> difficult z /\ r = (Some tt, (2, y))).
Proof.
  unfold client. il_simpl. setoid_rewrite Z.eqb_eq. setoid_rewrite Z.eqb_neq.
  sauto limit: 200.
Qed.

Theorem client_achieves1 :
  IncorrLogic (fun _ => True) (denoteIL client) (ok (fun '(x, y) => y = 49 /\ x = 1)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] [x y]] Hq; cbn in Hq; [| destruct Hq ].
  destruct Hq as [-> ->]. exists (0, 49). split; [ exact I |].
  apply client_out. exists 7. left. split; reflexivity.
Qed.

Theorem client_achieves2 :
  IncorrLogic (fun _ => True) (denoteIL client)
     (ok (fun '(x, y) => exists z, (y = difficult z /\ x = 1) \/ (y <> difficult z /\ x = 2))).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] [x y]] Hq; cbn in Hq; [| destruct Hq ].
  exists (0, y). split; [ exact I |]. apply client_out.
  destruct Hq as [z [[Hy ->] | [Hy ->]]]; exists z; [ left | right ]; auto.
Qed.

(** [3] is not a square. *)
Lemma not_square_3 (z : Z) : 3 <> difficult z.
Proof.
  unfold difficult. intro H.
  destruct (Z.le_gt_cases z (-2)) as [Hz | Hz]; [ nia |].
  destruct (Z.le_gt_cases 2 z) as [Hz' | Hz']; [ nia |].
  assert (z = -1 \/ z = 0 \/ z = 1) as [-> | [-> | ->]] by lia; discriminate H.
Qed.

Theorem client_achieves3_not_under :
  ~ IncorrLogic (fun _ => True) (denoteIL client) (ok (fun '(x, _) => x = 1 \/ x = 2)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, (1, 3)) (or_introl eq_refl)) as [[x y] [_ Ho]].
  apply client_out in Ho. destruct Ho as [z [[Hy Hr] | [_ Hr]]]; [| discriminate Hr ].
  injection Hr as <-. exact (not_square_3 z Hy).
Qed.

Theorem client_achieves3_hoare :
  PartCorr (fun _ => True) (denoteIL client) (ok (fun '(x, _) => x = 1 \/ x = 2)).
Proof.
  rewrite PartCorr_iff. intros [x y] r _ Ho. apply client_out in Ho.
  destruct Ho as [z [[_ ->] | [_ ->]]]; cbn; auto.
Qed.

(** [if (x == 1 || x == 2) { error(); }] after [client]. *)
Definition test1 : prog (Z * Z) unit :=
  client ;; st <- get ;; if orb (fst st =? 1) (fst st =? 2) then errorIL else skipIL.

Lemma test1_out (x y : Z) r :
  outIL test1 (x, y) (Some r)
  <-> exists z, (y = difficult z /\ r = (None, (1, y)))
                \/ (y <> difficult z /\ r = (None, (2, y))).
Proof.
  unfold test1. rewrite outIL_bind. split.
  - intros [[[[[]|] [x1 y1]]|] [H1 H2]]; [| | discriminate H2 ];
      apply client_out in H1; destruct H1 as [z [[Hy Hr] | [Hy Hr]]]; try discriminate Hr;
      injection Hr as -> ->; revert H2; il_simpl; intro H2; exists z; sauto limit: 200.
  - intros [z [[Hy ->] | [Hy ->]]].
    + exists (Some (Some tt, (1, y))). split; [ apply client_out; eauto |]. il_simpl. auto.
    + exists (Some (Some tt, (2, y))). split; [ apply client_out; eauto |]. il_simpl. auto.
Qed.

Theorem test1_achieves2 :
  IncorrLogic (fun _ => True) (denoteIL test1)
     (er (fun '(x, y) => exists z, (y = difficult z /\ x = 1) \/ (y <> difficult z /\ x = 2))).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] [x y]] Hq; cbn in Hq; [ destruct Hq |].
  exists (0, y). split; [ exact I |]. apply test1_out.
  destruct Hq as [z [[Hy ->] | [Hy ->]]]; exists z; [ left | right ]; auto.
Qed.

(** [if (x == 2) { error(); }] after [client]. *)
Definition test2 : prog (Z * Z) unit :=
  client ;; st <- get ;; if fst st =? 2 then errorIL else skipIL.

Theorem test2_achieves : IncorrLogic (fun _ => True) (denoteIL test2) (er (fun '(x, _) => x = 2)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] [x y]] Hq; cbn in Hq; [ destruct Hq |]. subst x.
  exists (0, y). split; [ exact I |]. unfold test2.
  apply (outIL_seq _ _ _ tt (2, y)).
  - apply client_out. exists (if y =? 0 then 1 else 0). right. split; [| reflexivity ].
    unfold difficult. destruct (Z.eqb_spec y 0); lia.
  - il_simpl. auto.
Qed.

(** *** Figure 7 *)

(** [z = nondet(); if (z) { locked = 0 } else { locked = 1 }] *)
Definition maxing : prog Z unit :=
  z <- pickIL ;; if negb (z =? 0) then put 0 else put 1.

Lemma maxing_out (l : Z) r : outIL maxing l (Some r) <-> r = (Some tt, 0) \/ r = (Some tt, 1).
Proof.
  unfold maxing. il_simpl. split.
  - intros [z [[_ H] | [_ H]]]; injection H as <-; auto.
  - intros [-> | ->]; [ exists 1 | exists 0 ]; [ left | right ]; auto.
Qed.

Theorem maxing_achieves : IncorrLogic (fun _ => True) (denoteIL maxing) (ok (fun l => l = 1)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] l] Hq; cbn in Hq; [| destruct Hq ]. subst l.
  exists 0. split; [ exact I | apply maxing_out; auto ].
Qed.

Theorem maxing_achieves_both :
  IncorrLogic (fun _ => True) (denoteIL maxing) (ok (fun l => l = 0 \/ l = 1)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] l] Hq; cbn in Hq; [| destruct Hq ].
  exists 0. split; [ exact I | apply maxing_out; destruct Hq as [-> | ->]; auto ].
Qed.

(** [if (locked == 0) { error(); }] *)
Definition errorIfUnlocked : prog Z unit :=
  l <- get ;; if l =? 0 then errorIL else skipIL.

Lemma errorIfUnlocked_out (l : Z) o :
  outIL errorIfUnlocked l o <-> o = Some (if l =? 0 then None else Some tt, l).
Proof. unfold errorIfUnlocked. il_simpl. destruct (l =? 0); sauto limit: 200. Qed.

Definition false_negative : prog Z unit := maxing ;; errorIfUnlocked.

Theorem false_negative_achieves :
  IncorrLogic (fun _ => True) (denoteIL false_negative) (er (fun _ => False))
  /\ IncorrLogic (fun _ => True) (denoteIL false_negative) (ok (fun l => l = 1)).
Proof.
  rewrite !IncorrLogic_iff. split; intros [[[]|] l] Hq; cbn in Hq; [ destruct Hq | destruct Hq | | destruct Hq ]. subst l.
  exists 0. split; [ exact I |]. apply (outIL_seq _ _ _ tt 1); [ apply maxing_out; auto |].
  apply errorIfUnlocked_out. reflexivity.
Qed.

(** The error the summary of [maxing] misses. *)
Theorem false_negative_bug :
  IncorrLogic (fun _ => True) (denoteIL false_negative) (er (fun l => l = 0)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] l] Hq; cbn in Hq; [ destruct Hq |]. subst l.
  exists 0. split; [ exact I |]. apply (outIL_seq _ _ _ tt 0); [ apply maxing_out; auto |].
  apply errorIfUnlocked_out. reflexivity.
Qed.

(** [if (locked > 0) { locked = locked - 1 }; if (locked == 0) { error(); }] *)
Definition true_positive : prog Z unit :=
  maxing ;; (l <- get ;; if 0 <? l then put (l - 1) else skipIL) ;; errorIfUnlocked.

Theorem true_positive_achieves :
  IncorrLogic (fun _ => True) (denoteIL true_positive) (er (fun l => l = 0)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] l] Hq; cbn in Hq; [ destruct Hq |]. subst l.
  exists 0. split; [ exact I |]. apply (outIL_seq _ _ _ tt 1); [ apply maxing_out; auto |].
  apply (outIL_seq _ _ _ tt 0); [ il_simpl; auto |].
  apply errorIfUnlocked_out. reflexivity.
Qed.

End Conditionals.

(** ** Section 6.3, Figure 8: sturdy and flaky tests; the state is [x] *)

Module Flaky.

Definition foo : prog Z unit :=
  x <- get ;; if Z.even x then errorIL else orIL skipIL errorIL.

Lemma foo_out (x : Z) o :
  outIL foo x o
  <-> if Z.even x then o = Some (None, x) else o = Some (Some tt, x) \/ o = Some (None, x).
Proof. unfold foo. il_simpl. destruct (Z.even x); sauto limit: 200. Qed.

(** *** Specifications of [foo] *)

Theorem foo_sturdy :
  IncorrLogic (fun x => Z.even x = true) (denoteIL foo) (er (fun x => Z.even x = true))
  /\ IncorrLogic (fun x => Z.even x = true) (denoteIL foo) (ok (fun _ => False)).
Proof.
  rewrite !IncorrLogic_iff. split; intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq | | destruct Hq | destruct Hq ].
  exists x. split; [ exact Hq | apply foo_out; rewrite Hq; reflexivity ].
Qed.

Theorem foo_flaky :
  IncorrLogic (fun x => Z.even x = false) (denoteIL foo) (er (fun x => Z.even x = false))
  /\ IncorrLogic (fun x => Z.even x = false) (denoteIL foo) (ok (fun x => Z.even x = false)).
Proof.
  rewrite !IncorrLogic_iff. split; intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq | | | destruct Hq ];
    exists x; (split; [ exact Hq | apply foo_out; rewrite Hq; auto ]).
Qed.

Theorem foo_wp_error (p : Z -> Prop) :
  TotalCorr p (denoteIL foo) (er (fun _ => True)) <-> forall x, p x -> Z.even x = true.
Proof.
  rewrite TotalCorr_iff. split.
  - intros H x Hx. destruct (Z.even x) eqn:He; [ reflexivity |].
    specialize (H x Hx (Some (Some tt, x))). rewrite foo_out, He in H. cbn in H.
    destruct (H (or_introl eq_refl)).
  - intros H x Hx o Ho. rewrite foo_out, (H x Hx) in Ho. subst o. exact I.
Qed.

Theorem foo_wp_ok (p : Z -> Prop) (x : Z) :
  TotalCorr p (denoteIL foo) (ok (fun _ => True)) -> ~ p x.
Proof.
  rewrite TotalCorr_iff. intros H Hx. specialize (H x Hx (Some (None, x))).
  rewrite foo_out in H. destruct (Z.even x); cbn in H; auto.
Qed.

Theorem foo_wpp_ok (p : Z -> Prop) :
  LisbonLogic p (denoteIL foo) (ok (fun _ => True)) <-> forall x, p x -> Z.even x = false.
Proof.
  rewrite LisbonLogic_iff. split.
  - intros H x Hx. destruct (H x Hx) as [o [Ho Hq]]. rewrite foo_out in Ho.
    destruct (Z.even x); [| reflexivity ]. subst o. destruct Hq.
  - intros H x Hx. exists (Some (Some tt, x)). split; [| exact I ].
    rewrite foo_out, (H x Hx). auto.
Qed.

Theorem foo_true_not_under :
  ~ IncorrLogic (fun x => Z.even x = false) (denoteIL foo) (ok (fun _ => True)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 0) I) as [x [Hx Ho]].
  rewrite foo_out, Hx in Ho. destruct Ho as [Ho | Ho]; [ injection Ho as <-; discriminate Hx | discriminate Ho ].
Qed.

(** *** [flaky_client] *)

Definition flaky_client (v : Z) : prog Z unit :=
  put 3 ;; foo ;; x <- get ;; put (x + 2) ;; x <- get ;; assertIL (x =? v).

Lemma flaky_client_out (v s : Z) r :
  outIL (flaky_client v) s (Some r)
  <-> r = (None, 3) \/ (5 <> v /\ r = (None, 5)) \/ (5 = v /\ r = (Some tt, 5)).
Proof.
  unfold flaky_client, foo. il_simpl. change (3 + 2) with 5. change (Z.even 3) with false.
  destruct (Z.eqb_spec 5 v); sauto limit: 200.
Qed.

Theorem flaky_client_achieves :
  IncorrLogic (fun _ => True) (denoteIL (flaky_client 4)) (er (fun x => x = 3 \/ x = 5)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq |].
  exists 0. split; [ exact I |]. apply flaky_client_out.
  destruct Hq as [-> | ->]; [ left | right; left ]; auto with zarith.
Qed.

Theorem flaky_client5_not_er5 :
  ~ IncorrLogic (fun _ => True) (denoteIL (flaky_client 5)) (er (fun x => x = 5)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (None, 5) eq_refl) as [s [_ Ho]].
  apply flaky_client_out in Ho. sauto limit: 200.
Qed.

Theorem flaky_client5_er3 :
  IncorrLogic (fun _ => True) (denoteIL (flaky_client 5)) (er (fun x => x = 3)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [ destruct Hq |]. subst x.
  exists 0. split; [ exact I | apply flaky_client_out; auto ].
Qed.

End Flaky.

(** ** Section 6.4, Figure 9: composition; the state is [x] *)

Module Composition.

Definition inc : prog Z unit :=
  x <- get ;; assertIL (0 <=? x) ;; x <- get ;; put (x + 1).

Lemma inc_out (x : Z) o :
  outIL inc x o
  <-> (0 <= x /\ o = Some (Some tt, x + 1)) \/ (x < 0 /\ o = Some (None, x)) \/ o = None.
Proof. unfold inc. il_simpl. rewrite Z.leb_le, Z.leb_gt. reflexivity. Qed.

Theorem inc_spec1 : IncorrLogic (fun x => 0 <= x) (denoteIL inc) (ok (fun x => 0 < x)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  exists (x - 1). split; [ lia |]. apply inc_out. left. split; [ lia |].
  f_equal. f_equal. lia.
Qed.

Theorem inc_spec2 (m : Z) :
  IncorrLogic (fun x => x = m /\ 0 <= m) (denoteIL inc) (ok (fun x => x = m + 1 /\ 0 <= m)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  destruct Hq as [-> Hm]. exists m. split; [ auto |]. apply inc_out. auto.
Qed.

(** *** [client] *)

Definition client : prog Z unit := inc ;; inc.

Lemma client_out (x : Z) r :
  outIL client x (Some r)
  <-> (0 <= x /\ r = (Some tt, x + 2)) \/ (x < 0 /\ r = (None, x)).
Proof.
  unfold client. rewrite outIL_bind. split.
  - intros [o1 [H1 H2]]. apply inc_out in H1.
    destruct H1 as [[Hx ->] | [[Hx ->] | ->]]; cbv beta iota in H2.
    + apply inc_out in H2. destruct H2 as [[_ H] | [[? _] | H]]; [| lia | discriminate H ].
      injection H as ->. left. split; [ exact Hx | f_equal; lia ].
    + injection H2 as ->. right. auto.
    + discriminate H2.
  - intros [[Hx ->] | [Hx ->]].
    + exists (Some (Some tt, x + 1)). split; [ apply inc_out; auto |].
      apply inc_out. left. split; [ lia | do 2 f_equal; lia ].
    + exists (Some (None, x)). split; [ apply inc_out; auto | reflexivity ].
Qed.

Theorem client_wrong_achieves1 :
  ~ IncorrLogic (fun x => 0 <= x) (denoteIL client) (ok (fun x => 0 < x)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (Some tt, 1) ltac:(cbn; lia)) as [x [Hx Ho]].
  apply client_out in Ho. destruct Ho as [[_ Hr] | [? _]]; [| lia ].
  injection Hr as Hr. lia.
Qed.

Theorem client_hoare : PartCorr (fun x => 0 <= x) (denoteIL client) (ok (fun x => 0 < x)).
Proof.
  rewrite PartCorr_iff. intros x r Hx Ho. apply client_out in Ho.
  destruct Ho as [[_ ->] | [? _]]; [ cbn; lia | exfalso; lia ].
Qed.

Theorem client_achieves2 (m : Z) :
  IncorrLogic (fun x => x = m /\ 0 <= m) (denoteIL client) (ok (fun x => x = m + 2 /\ 0 <= m)).
Proof.
  rewrite IncorrLogic_iff. intros [[[]|] x] Hq; cbn in Hq; [| destruct Hq ].
  destruct Hq as [-> Hm]. exists m. split; [ auto |]. apply client_out. auto.
Qed.

(** *** [test] *)

Definition test : prog Z unit :=
  put 0 ;; client ;; x <- get ;; assertIL (2 <=? x).

Lemma test_out (s : Z) r : outIL test s (Some r) <-> r = (Some tt, 2).
Proof.
  unfold test. il_simpl. rewrite outIL_bind. split.
  - intros [[[[[]|] x]|] [H1 H2]]; [| | discriminate H2 ]; apply client_out in H1.
    + destruct H1 as [[_ H] | [_ H]]; [| discriminate H ]. injection H as ->.
      revert H2. il_simpl. intros [[_ H] | [[H _] | H]]; [ injection H as <-; reflexivity | discriminate H .. ].
    + destruct H1 as [[_ H] | [? _]]; [ discriminate H | exfalso; lia ].
  - intros ->. exists (Some (Some tt, 2)).
    split; [ apply client_out; left; split; [ lia | reflexivity ] |].
    il_simpl. auto.
Qed.

Theorem test_wrong_achieves1 : ~ IncorrLogic (fun _ => True) (denoteIL test) (er (fun x => x = 1)).
Proof.
  rewrite IncorrLogic_iff. intro H. destruct (H (None, 1) eq_refl) as [s [_ Ho]].
  apply test_out in Ho. discriminate.
Qed.

Theorem test_achieves2 : IncorrLogic (fun _ => True) (denoteIL test) (er (fun _ => False)).
Proof. rewrite IncorrLogic_iff. intros [[[]|] x] Hq; destruct Hq. Qed.

Theorem test_hoare : PartCorr (fun _ => True) (denoteIL test) (ok (fun x => x = 2)).
Proof.
  rewrite PartCorr_iff. intros s r _ Ho. apply test_out in Ho. subst r. reflexivity.
Qed.

End Composition.
