(** * The base computation monad: non-empty nondeterminism with divergence

    The base monad is built in three steps:

      [SetM A  = A -> Prop]          a set of outcomes
      [divnd A = optionT SetM A]     a set of outcomes, [None] being divergence
      [divndNE A]                    the elements of [divnd A] with an outcome

    The two other settings are monad transformers applied to it:
    [stdivndNE S = stateT S divndNE] ([DivNonDetSt/Computation.v]) and
    [stdivexcndNE S = stateT S (optionT divndNE)]
    ([DivNonDetStExc/Computation.v]). *)

From Coq Require Import Morphisms FunctionalExtensionality PropExtensionality
  Classical_Prop Wf_nat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Basics Basics.Monad.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import TransformerLaws.

(* ================================================================= *)
(** * Sets of outcomes: [SetM]                                        *)
(* ================================================================= *)

(** The powerset monad: return is a singleton, bind runs the continuation on
    every outcome of the prefix.  Its laws hold up to Leibniz equality, by
    functional and propositional extensionality. *)

Section SetM.

  Definition SetM A := A -> Prop.

  #[global]
    Instance Monad_SetM : Monad SetM :=
    {| ret := fun _ a => fun x => x = a ;
       bind := fun _ _ m k => fun b => exists a, m a /\ k a b |}.

  #[global]
  Instance Eq1_SetM : Eq1 SetM :=
    fun A => eq.

  #[global]
  Instance Eq1Equivalence_SetM
    : @Eq1Equivalence SetM _ Eq1_SetM.
  Proof.
    constructor; typeclasses eauto.
  Qed.

  #[global]
  Instance MonadLawsE_SetM
    : @MonadLawsE SetM Eq1_SetM _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto limit: 200.
    - (* bind_ret_r *)
      intros A x. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro b.
      apply propositional_extensionality. sauto limit: 200.
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1_SetM. cbn.
      apply functional_extensionality; intro c.
      apply propositional_extensionality. sauto limit: 200.
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1_SetM in *. subst.
      apply functional_extensionality; intro b.
      apply propositional_extensionality.
      split; intros [a [Ha Hk]]; exists a; split; try exact Ha;
        [rewrite <- (Hfg a) | rewrite (Hfg a)]; exact Hk.
  Qed.

End SetM.

(* ================================================================= *)
(** * Nondeterminism with divergence: [divnd]                         *)
(* ================================================================= *)

(** [divnd A = optionT SetM A], whose payload is [option A -> Prop] — a SET of
    outcomes, with the distinguished outcome [None] read as DIVERGENCE.

    Nothing in the type distinguishes divergence from a raised exception;
    what fixes the meaning is which operations are offered.
    So [divnd] deliberately has NO [MonadExc] instance — [catch] would
    be "recover from divergence", which is not an observable operation — and
    instead has [divergeD], the divergent program.

    [None] is absorbing under [bind], which is exactly the propagation rule
    divergence needs, so the monad structure is [optionT]'s unchanged. *)

Section DivNonDet.

  Definition divnd A := optionT SetM A.

  Definition retD {A} (a : A) : divnd A :=
    @ret (optionT SetM) _ _ a.

  Definition bindD {A B} (m : divnd A) (k : A -> divnd B) : divnd B :=
    @bind (optionT SetM) _ _ _ m k.

  #[global]
    Instance Monad__divnd : Monad divnd :=
    {| ret := fun _ => @retD _ ;
       bind := fun _ _ => @bindD _ _ |}.

  (** The divergent program: its only outcome is the divergence token. *)
  Definition divergeD {A} : divnd A :=
    @mkOptionT SetM _ (fun oa => oa = None).

  (** Nondeterministic choice: union of outcome sets. *)
  Definition orD {A} (m1 m2 : divnd A) : divnd A :=
    @mkOptionT SetM _ (fun oa => unOptionT m1 oa \/ unOptionT m2 oa).

  (** [m] may diverge. *)
  Definition mayDiverge {A} (m : divnd A) : Prop :=
    unOptionT m None.

  (** ** Divergence propagates

      Stated pointwise on outcomes rather than as an [eq1]: [Eq1_SetM] is
      Leibniz equality on [option A -> Prop], so the extensional form would
      need functional and propositional extensionality, while these are
      axiom-free and are the shape the monad morphisms consume. *)

  Lemma outcomes_bind {A B} (m : divnd A) (k : A -> divnd B) (ob : option B) :
    unOptionT (bindD m k) ob <->
    (exists oa, unOptionT m oa /\
       match oa with
       | Some a => unOptionT (k a) ob
       | None   => ob = None
       end).
  Proof.
    cbn. split; intros [oa [H1 H2]]; exists oa; split; try exact H1;
      destruct oa as [a|]; exact H2.
  Qed.

  (** [divergeD] is absorbing: nothing after it can run. *)
  Lemma diverge_absorbing {A B} (k : A -> divnd B) (ob : option B) :
    unOptionT (bindD (divergeD : divnd A) k) ob <-> ob = None.
  Proof.
    rewrite outcomes_bind. split.
    - intros [oa [Hd H]]. cbn in Hd. subst oa. exact H.
    - intro Hob. exists None. split; [ reflexivity | exact Hob ].
  Qed.

  (** A divergent prefix makes the whole computation divergent. *)
  Lemma mayDiverge_bind {A B} (m : divnd A) (k : A -> divnd B) :
    mayDiverge m -> mayDiverge (bindD m k).
  Proof.
    intro Hm. unfold mayDiverge. apply outcomes_bind.
    exists None. split; [ exact Hm | reflexivity ].
  Qed.

  (** ** Blocking versus the absorbing [None]

      An empty outcome set is BLOCKING — no bind outcome can be built from
      it — while a divergent prefix survives even an empty continuation,
      because [bind] absorbs [None] without running the continuation. *)

  Definition emptyD {A} : divnd A :=
    @mkOptionT SetM _ (fun _ => False).

  (** An empty prefix blocks: the bind has no outcome either. *)
  Lemma empty_prefix_blocks {A B} (k : A -> divnd B) (ob : option B) :
    ~ unOptionT (bindD (emptyD : divnd A) k) ob.
  Proof.
    intro Hout.
    destruct (proj1 (outcomes_bind emptyD k ob) Hout) as [oa [Hoa _]].
    exact Hoa.
  Qed.

  (** A divergent prefix survives an empty continuation. *)
  Lemma diverge_survives_empty {A B} :
    unOptionT (bindD (divergeD : divnd A) (fun _ => (emptyD : divnd B))) None.
  Proof. apply diverge_absorbing. reflexivity. Qed.

  (** ** Laws

      The generic [optionT] instances of [TransformerLaws.v], at [SetM]. *)

  Definition Eq1__divnd : Eq1 divnd :=
    Eq1_optionT SetM.

  Definition Eq1Equivalence__divnd
    : @Eq1Equivalence divnd _ Eq1__divnd :=
    Eq1Equivalence_optionT SetM.

  Definition MonadLawsE__divnd
    : @MonadLawsE divnd _ Monad__divnd :=
    MonadLawsE_optionT SetM.

End DivNonDet.

Arguments divnd _.
Arguments divergeD {_}.
Arguments orD {_}.
Arguments mayDiverge {_}.
Arguments emptyD {_}.

(* ================================================================= *)
(** * The base monad: [divndNE]                                       *)
(* ================================================================= *)

(** Nothing in [divnd] forces the outcome set to be inhabited: [emptyD] is a
    well-typed element with no outcomes at all — it neither terminates nor
    diverges.  Every program built from [retD], [bindD], [divergeD] and [orD]
    does have an outcome, so that is carved out here as a subset type: side
    conditions of the form [exists oa, unOptionT m oa] become part of the
    carrier instead of hypotheses on each theorem. *)

Definition nonEmptyOutcomes {A} (m : divnd A) : Prop :=
  exists oa, unOptionT m oa.

Definition divndNE (A : Type) : Type := { m : divnd A | nonEmptyOutcomes m }.

Definition getNE {A} (m : divndNE A) : divnd A := proj1_sig m.

Lemma getNE_nonEmpty {A} (m : divndNE A) : nonEmptyOutcomes (getNE m).
Proof. exact (proj2_sig m). Qed.

(** Closure of [nonEmptyOutcomes] under each operation. *)

Lemma nonEmpty_retD {A} (a : A) : nonEmptyOutcomes (retD a).
Proof. exists (Some a). cbn. reflexivity. Qed.

Lemma nonEmpty_divergeD {A} : nonEmptyOutcomes (divergeD : divnd A).
Proof. exists None. cbn. reflexivity. Qed.

Lemma nonEmpty_orD {A} (m1 m2 : divnd A) :
  nonEmptyOutcomes m1 -> nonEmptyOutcomes (orD m1 m2).
Proof. intros [oa Ho]. exists oa. cbn. left. exact Ho. Qed.

Lemma nonEmpty_bindD {A B} (m : divnd A) (k : A -> divnd B) :
  nonEmptyOutcomes m -> (forall a, nonEmptyOutcomes (k a)) ->
  nonEmptyOutcomes (bindD m k).
Proof.
  intros [[a|] Ho] Hk.
  - destruct (Hk a) as [ob Hob]. exists ob. cbn.
    exists (Some a). split; [ exact Ho | exact Hob ].
  - exists None. cbn. exists None. split; [ exact Ho | reflexivity ].
Qed.

(** The operations, lifted to the subset type. *)

Definition retNE {A} (a : A) : divndNE A :=
  exist _ (retD a) (nonEmpty_retD a).

Definition bindNE {A B} (m : divndNE A) (k : A -> divndNE B) : divndNE B :=
  exist _ (bindD (getNE m) (fun a => getNE (k a)))
          (nonEmpty_bindD (getNE m) (fun a => getNE (k a))
             (getNE_nonEmpty m) (fun a => getNE_nonEmpty (k a))).

#[global]
  Instance Monad__divndNE : Monad divndNE :=
  {| ret := fun _ => @retNE _ ;
     bind := fun _ _ => @bindNE _ _ |}.

Definition divergeNE {A} : divndNE A :=
  exist _ divergeD nonEmpty_divergeD.

Definition orNE {A} (m1 m2 : divndNE A) : divndNE A :=
  exist _ (orD (getNE m1) (getNE m2)) (nonEmpty_orD _ _ (getNE_nonEmpty m1)).

(** [m] may diverge, on the non-empty fragment. *)
Definition mayDivergeNE {A} (m : divndNE A) : Prop :=
  mayDiverge (getNE m).

Arguments divndNE _.
Arguments getNE {_}.
Arguments retNE {_}.
Arguments bindNE {_} {_}.
Arguments divergeNE {_}.
Arguments orNE {_}.
Arguments nonEmptyOutcomes {_}.
Arguments mayDivergeNE {_}.

(** [divndNE] carries the operations of [divnd] unchanged — [proj1_sig] of
    [retNE] / [bindNE] is [retD] / [bindD] definitionally — so every law is
    the corresponding law of [divnd], transported along [getNE]. *)

(** Equality on the subset type is equality of the underlying programs. *)

#[global]
  Instance Eq1__divndNE : Eq1 divndNE :=
  fun A m n => Eq1__divnd A (getNE m) (getNE n).

#[global]
  Instance Eq1Equivalence__divndNE
  : @Eq1Equivalence divndNE _ Eq1__divndNE.
Proof.
  intro A. destruct (Eq1Equivalence__divnd A) as [Erefl Esym Etrans].
  constructor.
  - intro x. exact (Erefl (getNE x)).
  - intros x y H. exact (Esym _ _ H).
  - intros x y z H1 H2. exact (Etrans _ _ _ H1 H2).
Qed.

#[global]
  Instance MonadLawsE__divndNE
  : @MonadLawsE divndNE Eq1__divndNE Monad__divndNE.
Proof.
  destruct MonadLawsE__divnd as [Lbrl Lbrr Lbb Lpb].
  constructor.
  - intros A B f x. exact (Lbrl A B (fun a => getNE (f a)) x).
  - intros A x. exact (Lbrr A (getNE x)).
  - intros A B C x f g.
    exact (Lbb A B C (getNE x) (fun a => getNE (f a)) (fun b => getNE (g b))).
  - intros A B x y Hxy f g Hfg.
    exact (Lpb A B (getNE x) (getNE y) Hxy
             (fun a => getNE (f a)) (fun a => getNE (g a)) Hfg).
Qed.

(** Equal computations of the base monad have the same outcomes. *)
Lemma eq1_outcomes {A} (x y : divndNE A) :
  eq1 x y -> forall oa, unOptionT (getNE x) oa <-> unOptionT (getNE y) oa.
Proof.
  intros H oa. change (unOptionT (getNE x) = unOptionT (getNE y)) in H.
  rewrite H. reflexivity.
Qed.

(* ================================================================= *)
(** * Iteration                                                       *)
(* ================================================================= *)

(** A loop runs a body [I -> M (I + R)] from an accumulator: [inl i']
    continues with [i'], [inr r] exits with [r].  Its outcomes are of two
    kinds:

      finite runs     [iterOut]: after finitely many iterations the body
                      exits, or the body itself diverges (inductive);
      infinite runs   [loopsForever]: the body continues forever
                      (coinductive), read as divergence.

    Both are stated on the body's outcome relation [step].  ITree's
    [iter_Prop] (the [MonadIter] of [_ -> Prop]) is the inductive part
    alone: an infinite loop would have no outcome, so it would leave
    [divndNE] and every demonic reading would accept it. *)

Section Iteration.
  Context {I R : Type} (step : I -> option (I + R) -> Prop).

  Inductive iterOut : I -> option R -> Prop :=
  | iterOut_exit i r : step i (Some (inr r)) -> iterOut i (Some r)
  | iterOut_div i : step i None -> iterOut i None
  | iterOut_next i i' o : step i (Some (inl i')) -> iterOut i' o -> iterOut i o.

  CoInductive loopsForever : I -> Prop :=
  | loopsForever_next i i' : step i (Some (inl i')) -> loopsForever i' -> loopsForever i.

  (** The outcomes of the loop from [i]. *)
  Definition iterOutcomes (i : I) (o : option R) : Prop :=
    iterOut i o \/ (o = None /\ loopsForever i).

  (** A loop whose body always has an outcome has one: if no finite run
      ends, every run continues, so one runs forever (excluded middle). *)
  Lemma iterOutcomes_nonEmpty :
    (forall i, exists o, step i o) -> forall i, exists o, iterOutcomes i o.
  Proof.
    intros Hstep i.
    destruct (classic (exists o, iterOut i o)) as [[o Ho] | Hnone].
    - exists o. left. exact Ho.
    - exists None. right. split; [ reflexivity |].
      revert i Hnone. cofix CIH. intros i Hnone.
      destruct (Hstep i) as [[[i'|r]|] Ho].
      + refine (loopsForever_next i i' Ho (CIH i' _)).
        intros [o Ho']. exact (Hnone (ex_intro _ o (iterOut_next i i' o Ho Ho'))).
      + exfalso. exact (Hnone (ex_intro _ _ (iterOut_exit i r Ho))).
      + exfalso. exact (Hnone (ex_intro _ _ (iterOut_div i Ho))).
  Qed.

  (** The loop is a fixed point: one run of the body, then the loop again
      or the exit. *)
  Lemma iterOutcomes_unfold (i : I) (o : option R) :
    iterOutcomes i o
    <-> exists o1, step i o1 /\
          match o1 with
          | Some (inl i') => iterOutcomes i' o
          | Some (inr r) => o = Some r
          | None => o = None
          end.
  Proof.
    split.
    - intros [Ho | [-> Hloop]].
      + destruct Ho as [i r Hs | i Hs | i i' o Hs Ho].
        * exists (Some (inr r)). split; [ exact Hs | reflexivity ].
        * exists None. split; [ exact Hs | reflexivity ].
        * exists (Some (inl i')). split; [ exact Hs | left; exact Ho ].
      + destruct Hloop as [i i' Hs Hloop].
        exists (Some (inl i')). split; [ exact Hs | right; split; [ reflexivity | exact Hloop ] ].
    - intros [[[i'|r]|] [Hs Ho]].
      + destruct Ho as [Ho | [-> Hloop]].
        * left. exact (iterOut_next i i' o Hs Ho).
        * right. split; [ reflexivity | exact (loopsForever_next i i' Hs Hloop) ].
      + subst o. left. exact (iterOut_exit i r Hs).
      + subst o. left. exact (iterOut_div i Hs).
  Qed.

  (** ** Loop rules, on the outcomes

      Each reading of a loop needs one of these:
        invariant   every finite run ends in [Q] (DWLP, ASP Over);
        variant     no run is infinite (DWP);
        reach       some finite run ends in [Q] (AWP, ASP Under);
        recurrence  some run is infinite (AWLP, and the [Over] triples). *)

  (** An invariant: every finite run from an [Inv] start ends in [Q]. *)
  Lemma iterOut_invariant (Inv : I -> Prop) (Q : option R -> Prop) :
    (forall i o, Inv i -> step i o ->
       match o with
       | Some (inl i') => Inv i'
       | Some (inr r) => Q (Some r)
       | None => Q None
       end) ->
    forall i o, Inv i -> iterOut i o -> Q o.
  Proof.
    intros Hstep i o Hi Ho.
    induction Ho as [i r Hs | i Hs | i i' o Hs _ IH].
    - exact (Hstep i _ Hi Hs).
    - exact (Hstep i _ Hi Hs).
    - exact (IH (Hstep i _ Hi Hs)).
  Qed.

  (** A variant: if every continuing step from an [Inv] start decreases [V]
      and keeps [Inv], no run from an [Inv] start is infinite. *)
  Lemma loopsForever_variant (Inv : I -> Prop) (V : I -> nat) :
    (forall i i', Inv i -> step i (Some (inl i')) -> Inv i' /\ V i' < V i) ->
    forall i, Inv i -> ~ loopsForever i.
  Proof.
    intros Hstep i. remember (V i) as n eqn:Hn. revert i Hn.
    induction n as [n IH] using lt_wf_ind. intros i Hn Hi Hloop.
    destruct Hloop as [i i' Hs Hloop].
    destruct (Hstep i i' Hi Hs) as [Hi' Hlt]. subst n.
    exact (IH (V i') Hlt i' eq_refl Hi' Hloop).
  Qed.

  (** Reaching: if from every [Inv] start some step exits in [Q], or
      continues to an [Inv] start with a smaller [V], then some finite run
      from an [Inv] start ends in [Q]. *)
  Lemma iterOut_reach (Inv : I -> Prop) (V : I -> nat) (Q : option R -> Prop) :
    (forall i, Inv i -> exists o, step i o /\
       match o with
       | Some (inl i') => Inv i' /\ V i' < V i
       | Some (inr r) => Q (Some r)
       | None => Q None
       end) ->
    forall i, Inv i -> exists o, Q o /\ iterOut i o.
  Proof.
    intros Hstep i. remember (V i) as n eqn:Hn. revert i Hn.
    induction n as [n IH] using lt_wf_ind. intros i Hn Hi.
    destruct (Hstep i Hi) as [[[i'|r]|] [Hs Ho]].
    - destruct Ho as [Hi' Hlt]. subst n.
      destruct (IH (V i') Hlt i' eq_refl Hi') as [o [Hq Ho]].
      exists o. split; [ exact Hq | exact (iterOut_next i i' o Hs Ho) ].
    - exists (Some r). split; [ exact Ho | exact (iterOut_exit i r Hs) ].
    - exists None. split; [ exact Ho | exact (iterOut_div i Hs) ].
  Qed.

  (** Recurrence: if from every [Inv] start some step continues to an
      [Inv] start, some run from an [Inv] start is infinite. *)
  Lemma loopsForever_recurrence (Inv : I -> Prop) :
    (forall i, Inv i -> exists i', step i (Some (inl i')) /\ Inv i') ->
    forall i, Inv i -> loopsForever i.
  Proof.
    intro Hstep. cofix CIH. intros i Hi.
    destruct (Hstep i Hi) as [i' [Hs Hi']].
    exact (loopsForever_next i i' Hs (CIH i' Hi')).
  Qed.
End Iteration.

(** The loop of the base monad, and its [MonadIter] instance. *)

Definition iterD {I R} (body : I -> divnd (I + R)) (i : I) : divnd R :=
  @mkOptionT SetM _ (iterOutcomes (fun j => unOptionT (body j)) i).

#[program] Definition iterNE {I R} (body : I -> divndNE (I + R)) (i : I) : divndNE R :=
  iterD (fun j => getNE (body j)) i.
Next Obligation.
  exact (iterOutcomes_nonEmpty _ (fun j => getNE_nonEmpty (body j)) i).
Qed.

#[global]
  Instance MonadIter__divndNE : MonadIter divndNE :=
  fun R I body i => iterNE body i.

Lemma outcomes_iter {I R} (body : I -> divndNE (I + R)) (i : I) (o : option R) :
  unOptionT (getNE (iter body i)) o
  <-> iterOutcomes (fun j => unOptionT (getNE (body j))) i o.
Proof. reflexivity. Qed.
