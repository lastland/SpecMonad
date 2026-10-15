(** * The stateful extension of [SPost] is not a monad (paper, Section 3.3).

    [SPostStExc] (over [option (A * S)]) and [St.SPostSt] (its
    terminating-slice twin over [A * S]) restrict stateful forward
    transformers by monotonicity and the codomain condition, the conditions
    under which [SPost] (Maillard et al., ICFP 2019) is a monad.  [FailingBind] and
    [St.FailingBind] build the transformers [m], [f], [g] of the
    paper and show that the proposed [bind] is not associative.  The paper
    phrases this for [stateArrT] over the angelic SP arrow at input [unit];
    these are hand-built carriers of the same shape. *)

From ITree Require Import Basics.Monad.
From Coq Require Import RelationClasses.
From Incorrectness.Lib.Monad Require Import OrderedMonad.
From Incorrectness.SP Require Import RawSP SPostMonad.

Section SPostStExc.
  Variable S : Type.
  
  Definition MonotoneS {A} (w : SPStExc A) : Prop :=
    forall (p q : S -> Prop) (r : option (A * S)), (forall (s : S), p s -> q s) -> w p r -> w q r.

  Definition CodomainS {A} (w : SPStExc A) : Prop :=
    forall (p : S -> Prop) (r : option (A * S)), w p r -> (exists s, p s).

  Definition SPostStExc (A : Type) : Type := { w : SPStExc A | MonotoneS w /\ CodomainS w }.

  Definition getSPostStExc {A} (w : SPostStExc A) : SPStExc A := proj1_sig w.

  #[program] Definition retSPostStExc {A} (v : A) : SPostStExc A :=
    fun pre r => exists s0, pre s0 /\ r = Some (v, s0).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s0 [Hp Heq]]. exists s0. split; [exact (Hpq s0 Hp) | exact Heq].
    - intros p r [s0 [Hp _]]. exists s0. exact Hp.
  Qed.

  #[program] Definition bindSPostStExc {A B} (m : SPostStExc A) (k : A -> SPostStExc B) : SPostStExc B :=
    fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [[a Ha] | [Hr Hn]].
      + left. exists a.
        apply (proj1 (proj2_sig (k a))
                 (fun s0 => proj1_sig m p (Some (a, s0)))
                 (fun s0 => proj1_sig m q (Some (a, s0))) r);
          [ intros s0 Hm; exact (proj1 (proj2_sig m) p q (Some (a, s0)) Hpq Hm)
          | exact Ha ].
      + right. split; [ exact Hr | exact (proj1 (proj2_sig m) p q None Hpq Hn) ].
    - intros p r [[a Ha] | [_ Hn]].
      + destruct (proj2 (proj2_sig (k a))
                    (fun s0 => proj1_sig m p (Some (a, s0))) r Ha) as [s0 Hm].
        exact (proj2 (proj2_sig m) p (Some (a, s0)) Hm).
      + exact (proj2 (proj2_sig m) p None Hn).
  Qed.

  (* ---- the two laws that do hold ---- *)

  Theorem SPostStExc_bind_ret_r {A} (m : SPostStExc A)
    (pre : S -> Prop) (r : option (A * S)) :
    getSPostStExc (bindSPostStExc m retSPostStExc) pre r <-> getSPostStExc m pre r.
  Proof.
    split.
    - intros [[a [s0 [Hm Heq]]] | [Hr Hn]]; subst r; assumption.
    - intro H. destruct r as [[a s0]|].
      + left. exists a, s0. split; [exact H | reflexivity].
      + right. split; [reflexivity | exact H].
  Qed.

  Theorem SPostStExc_bind_ret_l {A B} (v : A) (k : A -> SPostStExc B)
    (pre : S -> Prop) (r : option (B * S)) :
    getSPostStExc (bindSPostStExc (retSPostStExc v) k) pre r <-> getSPostStExc (k v) pre r.
  Proof.
    split.
    - intros [[a Ha] | [_ [s1 [_ Heq]]]]; [| discriminate Heq].
      (* [CodomainS] of [k a] produces a witness, which forces [a = v] *)
      destruct (proj2 (proj2_sig (k a))
                  (fun s0 => proj1_sig (retSPostStExc v) pre (Some (a, s0))) r Ha)
        as [s0 [s1 [Hp Heq]]].
      assert (Hav : a = v) by congruence. subst a.
      (* [MonotoneS] of [k v] then rewrites the precondition back to [pre] *)
      apply (proj1 (proj2_sig (k v))
               (fun s0 => proj1_sig (retSPostStExc v) pre (Some (v, s0))) pre r);
        [| exact Ha ].
      intros s [s' [Hp' Heq']]. assert (Hss : s = s') by congruence.
      subst s. exact Hp'.
    - intro H. left. exists v.
      apply (proj1 (proj2_sig (k v)) pre
               (fun s0 => proj1_sig (retSPostStExc v) pre (Some (v, s0))) r);
        [| exact H ].
      intros s Hs. exists s. split; [ exact Hs | reflexivity ].
  Qed.
End SPostStExc.


Module FailingBind.
  #[program] Definition m : SPostStExc bool bool :=
    fun pre r => exists s, pre s.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s Hs]. exists s. exact (Hpq s Hs).
    - intros p r [s Hs]. exists s. exact Hs.
  Qed.

  #[program] Definition k : bool -> SPostStExc bool unit :=
    fun a => fun pre r => (exists s, pre s) /\ r = Some (tt, a).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [[s Hs] Heq]. split; [ exists s; exact (Hpq s Hs) | exact Heq ].
    - intros p r [[s Hs] _]. exists s. exact Hs.
  Qed.

  #[program] Definition g : SPostStExc bool unit :=
    fun pre r => pre true /\ pre false.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [Ht Hf]. split; [ exact (Hpq true Ht) | exact (Hpq false Hf) ].
    - intros p r [Ht _]. exists true. exact Ht.
  Qed.

  Definition pre : bool -> Prop := fun _ => True.
  Definition r : option (unit * bool) := Some (tt, true).

  (** The two associations pass different preconditions to [g].

      On the left, sequencing [m] with [k] first makes both Boolean states
      available.  Thus [g] receives [fun _ => True] and accepts [r].

      On the right, [m] first chooses one [a : bool].  Sequencing [k a]
      with [g] then gives [g] only [fun s => s = a].  Since [g] requires
      both [true] and [false], it rejects that precondition for every [a].
      The exception branches cannot contribute because [r] is [Some _].

      [SPostStExc_bind_bind_fails] proves this distinction for the actual
      [bindSPostStExc] operations, without relying on schematic expansions. *)
  
  Theorem SPostStExc_bind_bind_fails :
    ~ (forall (A B C S : Type) (m : SPostStExc S A) (f : A -> SPostStExc S B)
              (g : B -> SPostStExc S C) (pre : S -> Prop) (r : option (C * S)),
         getSPostStExc S (bindSPostStExc S (bindSPostStExc S m f) g) pre r <->
           getSPostStExc S (bindSPostStExc S m (fun a => bindSPostStExc S (f a) g)) pre r).
  Proof.
    intro H.
    (* LHS holds: the precondition handed to [g] is constantly [True] *)
    assert (HL : getSPostStExc bool
                   (bindSPostStExc bool (bindSPostStExc bool m k) (fun _ : unit => g))
                   pre r).
    { left. exists tt. split.
      - left. exists true. split; [ exists true; exists true; exact I | reflexivity ].
      - left. exists false. split; [ exists true; exists true; exact I | reflexivity ]. }
    (* RHS does not: [g] is now handed the singleton [fun s1 => s1 = a] *)
    destruct (proj1 (H bool unit unit bool m k (fun _ : unit => g) pre r) HL)
      as [[a Ha] | [Hr _]]; [| discriminate Hr].
    destruct Ha as [[b Hb] | [Hr _]]; [| discriminate Hr].
    destruct Hb as [[_ Het] [_ Hef]].
    assert (Ha1 : a = true) by congruence.
    assert (Ha2 : a = false) by congruence.
    congruence.
  Qed.

(* This rejects the proposed bind on [SPostStExc], whose monotonicity and
   codomain conditions admit [g].  It does not reject the more constrained
   ASP carrier or the unary [SPM.SPost] monad above. *)

End FailingBind.

(* ================================================================= *)
(** * [SPostSt]: the terminating-slice twin of the above              *)
(* ================================================================= *)

Module St.
  Import StTrans.
Section SPostSt.
  Variable S : Type.

  Definition MonotoneS {A} (w : SPSt A) : Prop :=
    forall (p q : S -> Prop) (r : A * S), (forall (s : S), p s -> q s) -> w p r -> w q r.

  Definition CodomainS {A} (w : SPSt A) : Prop :=
    forall (p : S -> Prop) (r : A * S), w p r -> (exists s, p s).

  Definition SPostSt (A : Type) : Type :=
    { w : SPSt A | MonotoneS w /\ CodomainS w }.

  Definition getSPostSt {A} (w : SPostSt A) : SPSt A := proj1_sig w.

  #[program] Definition retSPostSt {A} (v : A) : SPostSt A :=
    fun pre r => exists s0, pre s0 /\ r = (v, s0).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s0 [Hp Heq]]. exists s0. split; [exact (Hpq s0 Hp) | exact Heq].
    - intros p r [s0 [Hp _]]. exists s0. exact Hp.
  Qed.

  #[program] Definition bindSPostSt {A B}
    (m : SPostSt A) (k : A -> SPostSt B) : SPostSt B :=
    fun pre r => exists a, k a (fun s0 => m pre (a, s0)) r.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [a Ha]. exists a.
      apply (proj1 (proj2_sig (k a))
               (fun s0 => proj1_sig m p (a, s0))
               (fun s0 => proj1_sig m q (a, s0)) r);
        [ intros s0 Hm; exact (proj1 (proj2_sig m) p q (a, s0) Hpq Hm) | exact Ha ].
    - intros p r [a Ha].
      destruct (proj2 (proj2_sig (k a))
                  (fun s0 => proj1_sig m p (a, s0)) r Ha) as [s0 Hm].
      exact (proj2 (proj2_sig m) p (a, s0) Hm).
  Qed.

  (** As in [SPSpecMonads], [SPostSt] is CLOSED under the operations but is
      not a lawful monad: [bind_ret_r] holds outright, [bind_ret_l] holds
      because [CodomainS] rules out the wrong-[a] branches and [MonotoneS]
      supplies congruence in the precondition, and [bind_bind] FAILS. *)

  Theorem SPostSt_bind_ret_r {A} (m : SPostSt A)
    (pre : S -> Prop) (r : A * S) :
    getSPostSt (bindSPostSt m retSPostSt) pre r <-> getSPostSt m pre r.
  Proof.
    split.
    - intros [a [s0 [Hm Heq]]]. subst r. exact Hm.
    - intro H. destruct r as [a s0]. exists a, s0.
      split; [ exact H | reflexivity ].
  Qed.

  Theorem SPostSt_bind_ret_l {A B} (v : A) (k : A -> SPostSt B)
    (pre : S -> Prop) (r : B * S) :
    getSPostSt (bindSPostSt (retSPostSt v) k) pre r
    <-> getSPostSt (k v) pre r.
  Proof.
    split.
    - intros [a Ha].
      (* [CodomainS] of [k a] produces a witness, which forces [a = v] *)
      destruct (proj2 (proj2_sig (k a))
                  (fun s0 => proj1_sig (retSPostSt v) pre (a, s0)) r Ha)
        as [s0 [s1 [Hp Heq]]].
      assert (Hav : a = v) by congruence. subst a.
      (* [MonotoneS] of [k v] then rewrites the precondition back to [pre] *)
      apply (proj1 (proj2_sig (k v))
               (fun s0 => proj1_sig (retSPostSt v) pre (v, s0)) pre r);
        [| exact Ha ].
      intros s [s' [Hp' Heq']]. assert (Hss : s = s') by congruence.
      subst s. exact Hp'.
    - intro H. exists v.
      apply (proj1 (proj2_sig (k v)) pre
               (fun s0 => proj1_sig (retSPostSt v) pre (v, s0)) r);
        [| exact H ].
      intros s Hs. exists s. split; [ exact Hs | reflexivity ].
  Qed.

End SPostSt.

(** Associativity fails, for the same reason as over [option (A * S)]: the
    precondition handed to [g] on the right is a singleton [fun s1 => s1 = a],
    and [g] can see the difference between one state and two. *)
Module FailingBind.

  #[program] Definition m : SPostSt bool bool :=
    fun pre r => exists s, pre s.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [s Hs]. exists s. exact (Hpq s Hs).
    - intros p r [s Hs]. exists s. exact Hs.
  Qed.

  #[program] Definition k : bool -> SPostSt bool unit :=
    fun a => fun pre r => (exists s, pre s) /\ r = (tt, a).
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [[s Hs] Heq]. split; [ exists s; exact (Hpq s Hs) | exact Heq ].
    - intros p r [[s Hs] _]. exists s. exact Hs.
  Qed.

  #[program] Definition g : SPostSt bool unit :=
    fun pre r => pre true /\ pre false.
  Next Obligation.
  Proof.
    split.
    - intros p q r Hpq [Ht Hf]. split; [ exact (Hpq true Ht) | exact (Hpq false Hf) ].
    - intros p r [Ht _]. exists true. exact Ht.
  Qed.

  Definition pre : bool -> Prop := fun _ => True.
  Definition r : unit * bool := (tt, true).

  Theorem SPostSt_bind_bind_fails :
    ~ (forall (A B C S : Type) (m : SPostSt S A) (f : A -> SPostSt S B)
              (g : B -> SPostSt S C) (pre : S -> Prop) (r : C * S),
         getSPostSt S (bindSPostSt S (bindSPostSt S m f) g) pre r <->
           getSPostSt S (bindSPostSt S m (fun a => bindSPostSt S (f a) g)) pre r).
  Proof.
    intro H.
    assert (HL : getSPostSt bool
                   (bindSPostSt bool (bindSPostSt bool m k) (fun _ : unit => g))
                   pre r).
    { exists tt. split.
      - exists true. split; [ exists true; exists true; exact I | reflexivity ].
      - exists false. split; [ exists true; exists true; exact I | reflexivity ]. }
    destruct (proj1 (H bool unit unit bool m k (fun _ : unit => g) pre r) HL)
      as [a Ha].
    destruct Ha as [b Hb].
    destruct Hb as [[_ Het] [_ Hef]].
    assert (Ha1 : a = true) by congruence.
    assert (Ha2 : a = false) by congruence.
    congruence.
  Qed.

End FailingBind.

End St.
