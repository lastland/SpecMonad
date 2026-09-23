(** * ASP-[Under] as a PARAMETERISED Dijkstra structure.

    [no_asp_under_index] shows the ASP [Under] triple has no index in the
    global order, and [ASPUnderObstructions.v] shows no other order on the
    ASP carrier repairs that.  The obstruction is specific to the
    ORDERED-MONAD presentation: [bind] there must be monotone, and the
    [Under] reading is existential in the start state while composition is
    universal in it.

    Moving the precondition out of the order and into the INDEX removes the
    obstruction.  What follows is an Atkey-style parameterised structure:

      [DUnder P Q]  =  the programs whose reachable set from [P] covers [Q]

    -- the [Under] triple as a TYPE.  [bind] never compares two
    specifications, so no [Pos]-enrichment is required; comparison happens
    only in [wknDU] / [wknPre], at a fixed index.

    This is incorrectness logic's proof system in monadic form: [wknPre] is
    covariant in the presumption and [wknDU] shrinks the result, which is
    O'Hearn's rule of consequence, and [bindDU]'s continuation is typed at
    the first stage's postcondition, which is his sequencing rule.

    What is NOT available is weakening the FIRST stage's postcondition:
    that retypes the continuation at a smaller precondition, and
    [DUnder_not_contravariant_in_pre] shows the needed contravariance is
    absent.  That is a property of the triple, not of this encoding.

    Open: the laws hold at two levels -- index EQUIVALENCE and program
    [eq1] -- rather than as equalities in one type, and whether
    [fun r => exists a, R a r] is the STRONGEST composite postcondition is
    unchecked.  Which other (reading, direction) pairs admit the same
    treatment is settled in [DSPASLPObstructions.v]: the closure that
    [bindDU] rests on ([tripleASP_under_seq]) holds for six of the eight
    pairs and fails for DSP/[Over] and ASLP/[Under]. *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import StExcNonDet DivNonDet StDivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  SPPredicateTransformers ASPMonad DSLPMonad DSPMonad ASLPMonad.
From Incorrectness.Taxonomy.EffectObservations.SP Require Import
  StDivNonDet_SPSt_Arrow.

Import MonadNotation.
Open Scope monad_scope.

#[local] Existing Instance Monad_optionT.
#[local] Existing Instance Monad_stateT.
#[local] Existing Instance Eq1__stdivnd.
#[local] Existing Instance MonadLawsE__stdivnd.

(** A program with prescribed terminating outcomes, always admitting
    divergence so the nonempty-outcomes condition is free. *)
Definition progOfSt {S A} (R : S -> A * S -> Prop) : stdivnd S A :=
  mkStateT (fun s => @mkOptionT SetM _
    (fun oa => match oa with Some r => R s r | None => True end)).

Lemma progOfSt_outcomes {S A} (R : S -> A * S -> Prop) s r :
  unOptionT (runStateT (progOfSt R) s) (Some r) <-> R s r.
Proof. cbn. split; intro H; exact H. Qed.

(** [mU] runs only from state 0 and leaves the state at 0. *)
Section Graded.
  #[local] Obligation Tactic := idtac.
  Variable S : Type.

  Notation rel m s r := (unOptionT (runStateT m s) (Some r)).

  (* ---- test 1: does the index composition associate? ---- *)

  Definition compIdx {A B} (Q : A * S -> Prop) (R : A -> S -> B * S -> Prop)
    : B * S -> Prop :=
    fun r => exists a s', Q (a, s') /\ R a s' r.

  Theorem compIdx_assoc {A B C}
    (Q : A * S -> Prop) (R : A -> S -> B * S -> Prop)
    (T : B -> S -> C * S -> Prop) (r : C * S) :
    compIdx (compIdx Q R) T r
    <-> compIdx Q (fun a s' => compIdx (R a s') T) r.
  Proof.
    unfold compIdx. split.
    - intros [b [s'' [[a [s' [HQ HR]]] HT]]].
      exists a, s'. split; [ exact HQ |]. exists b, s''. split; [ exact HR | exact HT ].
    - intros [a [s' [HQ [b [s'' [HR HT]]]]]].
      exists b, s''. split; [| exact HT ].
      exists a, s'. split; [ exact HQ | exact HR ].
  Qed.

  (* ---- test 2: is the Under triple CLOSED under bind? ---- *)

  (** The [Under] triple, as a TYPE: programs whose reachable set from [P]
      covers [Q].  The precondition sits in the INDEX, so a continuation is
      typed at the states the first stage actually produces. *)
  Definition DUnder {A} (P : S -> Prop) (Q : A * S -> Prop) : Type :=
    { m : stdivnd S A | forall r, Q r -> exists s, P s /\ rel m s r }.

  Definition duProg {A P Q} (d : @DUnder A P Q) : stdivnd S A := proj1_sig d.

  Definition retDU {A} (P : S -> Prop) (a : A)
    : DUnder P (fun r => exists s, P s /\ r = (a, s)).
  Proof.
    refine (exist _ (ret a : stdivnd S A) _).
    intros r [s [HP ->]]. exists s. split; [ exact HP |].
    apply (outcomes_ret S). reflexivity.
  Defined.

  Definition bindDU {A B} (P : S -> Prop) (Q : A * S -> Prop)
    (R : A -> B * S -> Prop)
    (m : DUnder P Q) (k : forall a, DUnder (fun s' => Q (a, s')) (R a))
    : DUnder P (fun r => exists a, R a r).
  Proof.
    refine (exist _ (bind (duProg m) (fun a => duProg (k a))) _).
    intros r [a HR].
    destruct (proj2_sig (k a) r HR) as [s' [HQ Hk]].
    destruct (proj2_sig m (a, s') HQ) as [s [HP Hm]].
    exists s. split; [ exact HP |].
    apply (outcomes_bind S). exists a, s'. split; [ exact Hm | exact Hk ].
  Defined.

  (** And weakening at a fixed index is the [At]-order -- which is all the
      [Under] characterisation ever needed. *)
  Definition wknDU {A} (P : S -> Prop) (Q Q' : A * S -> Prop)
    (H : forall r, Q' r -> Q r) (d : DUnder P Q) : DUnder P Q'.
  Proof.
    refine (exist _ (duProg d) _).
    intros r HQ'. exact (proj2_sig d r (H r HQ')).
  Defined.



  (* ---- test 3: does [wkn] commute with [bind]? ---- *)

  (** [DUnder] is COVARIANT in the precondition: more start states allowed
      is a weaker obligation. *)
  Definition wknPre {A} (P P' : S -> Prop) (Q : A * S -> Prop)
    (H : forall s, P s -> P' s) (d : DUnder P Q) : DUnder P' Q.
  Proof.
    refine (exist _ (duProg d) _).
    intros r HQ. destruct (proj2_sig d r HQ) as [s [HP Hr]].
    exists s. split; [ exact (H s HP) | exact Hr ].
  Defined.

  (** (a) Weakening the CONTINUATION commutes with [bind] -- the programs
      are equal, because [wkn] is the identity on the carrier. *)
  Theorem wkn_bind_cont {A B} (P : S -> Prop) (Q : A * S -> Prop)
    (R R' : A -> B * S -> Prop)
    (H2 : forall a r, R' a r -> R a r)
    (H : forall r, (exists a, R' a r) -> (exists a, R a r))
    (m : DUnder P Q) (k : forall a, DUnder (fun s' => Q (a, s')) (R a)) :
    duProg (wknDU P (fun r => exists a, R a r) (fun r => exists a, R' a r) H
              (bindDU P Q R m k))
    = duProg (bindDU P Q R' m (fun a => wknDU _ (R a) (R' a) (H2 a) (k a))).
  Proof. reflexivity. Qed.

  (** (b) Weakening the PRECONDITION commutes too. *)
  Theorem wkn_bind_pre {A B} (P P' : S -> Prop) (Q : A * S -> Prop)
    (R : A -> B * S -> Prop) (H : forall s, P s -> P' s)
    (m : DUnder P Q) (k : forall a, DUnder (fun s' => Q (a, s')) (R a)) :
    duProg (wknPre P P' (fun r => exists a, R a r) H (bindDU P Q R m k))
    = duProg (bindDU P' Q R (wknPre P P' Q H m) k).
  Proof. reflexivity. Qed.

  (* ---- test 4: the unit laws ---- *)

  (** LEFT UNIT.  The composite index [exists a', R a' r] collapses to
      [R a r] -- and it is DERIVABLE FROM THE TYPING: for [a' <> a] the
      continuation is typed at the empty precondition, which forces
      [R a'] empty. *)
  Theorem leftUnit_idx {A B} (P : S -> Prop) (a : A) (R : A -> B * S -> Prop)
    (k : forall a', DUnder (fun s' => exists s, P s /\ (a', s') = (a, s)) (R a'))
    (r : B * S) :
    (exists a', R a' r) <-> R a r.
  Proof.
    split.
    - intros [a' HR]. destruct (proj2_sig (k a') r HR) as [s [[s0 [_ Heq]] _]].
      injection Heq as Ha _. subst a'. exact HR.
    - intro HR. exists a. exact HR.
  Qed.

  Theorem leftUnit_prog {A B} (P : S -> Prop) (a : A) (R : A -> B * S -> Prop)
    (k : forall a', DUnder (fun s' => exists s, P s /\ (a', s') = (a, s)) (R a')) :
    eq1 (duProg (bindDU P _ R (retDU P a) k)) (duProg (k a)).
  Proof. exact (bind_ret_l _ _ (fun a2 => duProg (k a2)) a). Qed.

  (** RIGHT UNIT.  The composite index collapses to [Q], with no side
      condition at all. *)
  Theorem rightUnit_idx {A} (Q : A * S -> Prop) (r : A * S) :
    (exists a, exists s', Q (a, s') /\ r = (a, s')) <-> Q r.
  Proof.
    split.
    - intros [a [s' [HQ ->]]]. exact HQ.
    - intro HQ. destruct r as [a s']. exists a, s'. split; [ exact HQ | reflexivity ].
  Qed.

  Theorem rightUnit_prog {A} (P : S -> Prop) (Q : A * S -> Prop)
    (m : DUnder P Q) :
    eq1 (duProg (bindDU P Q _ m (fun a => retDU (fun s' => Q (a, s')) a)))
        (duProg m).
  Proof. exact (bind_ret_r _ (duProg m)). Qed.

End Graded.

(* ---- the one that does NOT typecheck, and why ---- *)

(** Weakening the FIRST stage's postcondition ([Q] to [Q' ⊆ Q]) retypes the
    continuation at the SMALLER precondition [fun s' => Q' (a,s')].  That
    needs [DUnder] to be CONTRAVARIANT in the precondition -- and it is not. *)
Definition mC : stdivnd nat unit :=
  progOfSt (fun s r => s = 1 /\ r = (tt, 9)).

(** [mC] reaches [(tt,9)] from state 1 only.  It inhabits [DUnder] at the
    LARGER precondition ... *)
Definition dC : DUnder nat (fun s => s = 0 \/ s = 1) (fun r => r = (tt, 9)).
Proof.
  refine (exist _ mC _). intros r ->. exists 1.
  split; [ right; reflexivity | apply progOfSt_outcomes; split; reflexivity ].
Defined.

(** ... but NOT at the smaller one.  So [DUnder] is covariant in the
    precondition and not contravariant -- which is exactly the retyping
    that weakening the first stage's postcondition would require. *)
Theorem DUnder_not_contravariant_in_pre :
  ~ (exists d : DUnder nat (fun s => s = 0) (fun r => r = (tt, 9)),
       proj1_sig d = mC).
Proof.
  intros [d Hd]. destruct (proj2_sig d (tt, 9) eq_refl) as [s [Hs Hr]].
  subst s. rewrite Hd in Hr.
  apply progOfSt_outcomes in Hr. destruct Hr as [Hn _]. discriminate Hn.
Qed.
