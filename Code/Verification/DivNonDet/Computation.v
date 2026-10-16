(** * The base computation monad: programs and their outcomes

    Programs are interaction trees [itree E A], over any events [E], read as
    nondeterministic: an event may get any of its answers.  What a program
    can do is a non-empty set of outcomes, built in three steps:

      [SetM A  = A -> Prop]          a set of outcomes
      [divnd A = optionT SetM A]     a set of outcomes, [None] being divergence
      [divndNE A]                    the elements of [divnd A] with an outcome

    and [denote : itree E A -> divndNE A] maps a program to its outcomes: the
    values it may return, and divergence if some path is infinite.  It needs
    every event to have an answer ([HasAnswers]), as ITree's
    nondeterministic choice [nondetE] has.  [denote] is a monad morphism up
    to [eutt] ([denote_morphism]) and maps [ITree.iter] to the loop of the
    outcome monad ([denote_iter]), whose loop rules ([iterOut_invariant]
    &c.) are stated on outcomes.

    The two other settings are monad transformers applied to [divndNE]:
    [stdivndNE S = stateT S divndNE] ([DivNonDetSt/Computation.v]) and
    [stdivexcndNE S = stateT S (optionT divndNE)]
    ([DivNonDetStExc/Computation.v]). *)

From Coq Require Import Morphisms FunctionalExtensionality PropExtensionality
  Classical_Prop Wf_nat.
From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From Paco Require Import paco.
From ITree Require Import Basics.Basics Basics.Monad Core.ITreeDefinition Core.ITreeMonad Core.Subevent
  Indexed.Sum Eq.Eqit Eq.Shallow Props.Leaf Props.Infinite.
From ITree Require Events.Nondeterminism.
From Hammer Require Import Tactics.
From Incorrectness.Lib.Monad Require Import TransformerLaws OrderedMonad.
From Incorrectness.Lib Require Import ITreeFacts.

(* ================================================================= *)
(** * Programs                                                        *)
(* ================================================================= *)

(** A program is an interaction tree [itree E A].  An event may get any of
    its answers; for every program to have an outcome, every event must have
    one ([HasAnswers]).  ITree's nondeterministic choice [nondetE] has: its
    one event [Or] answers a [bool]. *)

Class HasAnswers (E : Type -> Type) : Prop :=
  has_answer : forall X (e : E X), inhabited X.

#[global] Hint Mode HasAnswers ! : typeclass_instances.

#[global] Instance HasAnswers_nondetE : HasAnswers Nondeterminism.nondetE.
Proof. intros X []. exact (inhabits true). Qed.

#[global] Instance HasAnswers_sum {E F} `{HasAnswers E} `{HasAnswers F} :
  HasAnswers (E +' F).
Proof. intros X [e | f]; [ exact (has_answer X e) | exact (has_answer X f) ]. Qed.

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

(** Equivalent outcome relations give the same loop outcomes. *)
Lemma iterOutcomes_ext {I R} (step1 step2 : I -> option (I + R) -> Prop) :
  (forall i o, step1 i o <-> step2 i o) ->
  forall i o, iterOutcomes step1 i o <-> iterOutcomes step2 i o.
Proof.
  intro Heq.
  assert (Hout : forall s1 s2 : I -> option (I + R) -> Prop,
             (forall i o, s1 i o -> s2 i o) -> forall i o, iterOut s1 i o -> iterOut s2 i o).
  { intros s1 s2 H i o Ho. induction Ho as [i r Hs | i Hs | i i' o Hs _ IH].
    - exact (iterOut_exit s2 i r (H _ _ Hs)).
    - exact (iterOut_div s2 i (H _ _ Hs)).
    - exact (iterOut_next s2 i i' o (H _ _ Hs) IH). }
  assert (Hloop : forall s1 s2 : I -> option (I + R) -> Prop,
             (forall i o, s1 i o -> s2 i o) -> forall i, loopsForever s1 i -> loopsForever s2 i).
  { intros s1 s2 H. cofix CIH. intros i [i0 i' Hs Hl].
    exact (loopsForever_next s2 i0 i' (H _ _ Hs) (CIH i' Hl)). }
  intros i o. unfold iterOutcomes.
  split; intros [Ho | [Hn Hl]];
    [ left; exact (Hout step1 step2 (fun i o => proj1 (Heq i o)) i o Ho)
    | right; exact (conj Hn (Hloop step1 step2 (fun i o => proj1 (Heq i o)) i Hl))
    | left; exact (Hout step2 step1 (fun i o => proj2 (Heq i o)) i o Ho)
    | right; exact (conj Hn (Hloop step2 step1 (fun i o => proj2 (Heq i o)) i Hl)) ].
Qed.

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

(* ================================================================= *)
(** * [denote]                                                        *)
(* ================================================================= *)

Section Denote.
  Context {E : Type -> Type} `{HE : HasAnswers E}.

Definition denoteD {A} (t : itree E A) : divnd A :=
  @mkOptionT SetM _ (fun o => match o with
                              | Some a => Leaf a t
                              | None => any_infinite t
                              end).

#[program] Definition denote {A} (t : itree E A) : divndNE A := denoteD t.
Next Obligation.
  destruct (leaf_or_infinite has_answer t) as [[a Ha] | Hinf];
    [ exists (Some a); exact Ha | exists None; exact Hinf ].
Qed.

Lemma outcomes_denote {A} (t : itree E A) (o : option A) :
  unOptionT (getNE (denote t)) o
  <-> match o with Some a => Leaf a t | None => any_infinite t end.
Proof. reflexivity. Qed.

(** Two computations with the same outcomes are equal. *)
Lemma divndNE_eq1 {A} (x y : divndNE A) :
  (forall o, unOptionT (getNE x) o <-> unOptionT (getNE y) o) -> eq1 x y.
Proof.
  intro H. change (unOptionT (getNE x) = unOptionT (getNE y)).
  apply functional_extensionality. intro o.
  apply propositional_extensionality. exact (H o).
Qed.

Lemma denote_ret {A} (a : A) (o : option A) :
  unOptionT (getNE (denote (Ret a))) o <-> o = Some a.
Proof.
  rewrite outcomes_denote. destruct o as [b|]; split.
  - intro H. f_equal. exact (Leaf_Ret_inv _ _ _ _ H).
  - intro H. injection H as ->. apply Leaf_Ret.
  - intro H. destruct (any_infinite_ret a H).
  - discriminate.
Qed.

Lemma denote_bind {A B} (t : itree E A) (k : A -> itree E B) (o : option B) :
  unOptionT (getNE (denote (ITree.bind t k))) o
  <-> exists oa, unOptionT (getNE (denote t)) oa /\
        match oa with
        | Some a => unOptionT (getNE (denote (k a))) o
        | None => o = None
        end.
Proof.
  rewrite outcomes_denote. destruct o as [b|]; split.
  - intro H. destruct (Leaf_bind_inv _ _ _ H) as [a [Ha Hb]].
    exists (Some a). exact (conj Ha Hb).
  - intros [[a|] [Ha Hb]]; [ exact (Leaf_bind _ _ _ _ Ha Hb) | discriminate ].
  - intro H. destruct (any_infinite_bind_inv _ _ H) as [Hinf | [a [Ha Hinf]]].
    + exists None. exact (conj Hinf eq_refl).
    + exists (Some a). exact (conj Ha Hinf).
  - intros [[a|] [Ha Hb]].
    + exact (any_infinite_bind_leaf _ _ _ Ha Hb).
    + exact (any_infinite_bind_l _ k Ha).
Qed.

Theorem denote_morphism :
  @MonadMorphism (itree E) divndNE Monad_itree Monad__divndNE
    Eq1_ITree Eq1__divndNE (@denote).
Proof.
  constructor.
  - intros A x y Hxy. unfold eq1, Eq1_ITree in Hxy. apply divndNE_eq1.
    intros o. rewrite !outcomes_denote. destruct o as [a|].
    + rewrite Hxy. reflexivity.
    + rewrite Hxy. reflexivity.
  - intros A a. apply divndNE_eq1. intro o. exact (denote_ret a o).
  - intros A B x k. apply divndNE_eq1. intro o.
    etransitivity; [ exact (denote_bind x k o) |].
    symmetry. exact (outcomes_bind (getNE (denote x)) (fun a => getNE (denote (k a))) o).
Qed.

#[global] Instance IsMonadMorphism_denote : IsMonadMorphism (@denote) :=
  @Build_IsMonadMorphism _ _ _ _ _ _ _ denote_morphism.

(** The operations. *)

Lemma denote_vis {X A} (e : E X) (k : X -> itree E A) (o : option A) :
  unOptionT (getNE (denote (Vis e k))) o
  <-> exists x, unOptionT (getNE (denote (k x))) o.
Proof.
  rewrite outcomes_denote. destruct o as [a|]; split.
  - intro H. exact (Leaf_Vis_inv _ _ _ _ _ _ H).
  - intros [x Hx]. exact (Leaf_Vis _ _ _ e k a x Hx).
  - intro H. punfold H. red in H. cbn in H.
    destruct (any_infiniteF_vis_inv _ _ _ H) as [x Hx]. pclearbot. exists x. exact Hx.
  - intros [x Hx]. pfold. red. cbn. apply (DivVis _ _ e x). left. exact Hx.
Qed.

(** ITree's nondeterministic choice is the union of the outcomes. *)
Lemma denote_or `{Nondeterminism.nondetE -< E} {A} (t1 t2 : itree E A) (o : option A) :
  unOptionT (getNE (denote (Nondeterminism.or t1 t2))) o
  <-> unOptionT (getNE (denote t1)) o \/ unOptionT (getNE (denote t2)) o.
Proof.
  unfold Nondeterminism.or. rewrite denote_vis. split.
  - intros [[] Ho]; [ left | right ]; exact Ho.
  - intros [Ho | Ho]; [ exists true | exists false ]; exact Ho.
Qed.

Lemma denote_spin {A} (o : option A) :
  unOptionT (getNE (denote ITree.spin)) o <-> o = None.
Proof.
  rewrite outcomes_denote. destruct o as [a|]; split.
  - intro H. exfalso. remember ITree.spin as t eqn:Et.
    induction H as [t Ht | t u Ht _ IH | Y e t h y Ht _ IH];
      subst t; cbn in Ht; try discriminate.
    injection Ht as <-. exact (IH eq_refl).
  - discriminate.
  - intros _. reflexivity.
  - intros _. exact spin_infinite.
Qed.

(* ================================================================= *)
(** * [denote] and loops                                              *)
(* ================================================================= *)

Section Loops.
  Context {I R : Type} (body : I -> itree E (I + R)).

  (** The body's outcomes, from each accumulator. *)
  Let step (j : I) (o : option (I + R)) : Prop := unOptionT (getNE (denote (body j))) o.

  Let next (lr : I + R) : itree E R :=
    match lr with inl l => Tau (ITree.iter body l) | inr r => Ret r end.

  Lemma observe_iter (i : I) :
    observe (ITree.iter body i) = observe (ITree.bind (body i) next).
  Proof. reflexivity. Qed.

  (** A result of the tree is a result of a finite run. *)
  Lemma leaf_iter_iterOut (i : I) (r : R) :
    Leaf r (ITree.iter body i) -> iterOut step i (Some r).
  Proof.
    apply (Leaf_iter_inv body i (fun j => forall r, iterOut step j (Some r) -> iterOut step i (Some r))
             (fun r => iterOut step i (Some r))); [| intros r' H; exact H ].
    intros j [j'|r'] Hj Hx; cbn.
    - intros r' Hr. apply Hj. exact (iterOut_next step j j' _ Hx Hr).
    - apply Hj. exact (iterOut_exit step j r' Hx).
  Qed.

  (** A finite run is a result of the tree, or one of its infinite paths if
      the body diverges. *)
  Lemma iterOut_tree (i : I) (o : option R) :
    iterOut step i o ->
    match o with Some r => Leaf r (ITree.iter body i) | None => any_infinite (ITree.iter body i) end.
  Proof.
    intro H. induction H as [i r Hs | i Hs | i i' o Hs _ IH].
    - cbv beta iota. rewrite unfold_iter. exact (Leaf_bind _ _ _ _ Hs (Leaf_Ret _ _ r)).
    - cbv beta iota. rewrite unfold_iter. exact (any_infinite_bind_l _ _ Hs).
    - destruct o as [r|]; rewrite unfold_iter.
      + refine (Leaf_bind _ _ _ _ Hs _). econstructor 2; [ reflexivity | exact IH ].
      + refine (any_infinite_bind_leaf _ _ _ Hs _). pfold. red. cbn. constructor. left. exact IH.
  Qed.

  (** An infinite run gives an infinite path. *)
  Lemma loopsForever_infinite (i : I) :
    loopsForever step i -> any_infinite (ITree.iter body i).
  Proof.
    revert i. pcofix CIH. intros i Hl. pfold. red. rewrite observe_iter.
    destruct Hl as [i i' Hs Hl].
    assert (Hup : upaco1 any_infinite_ r (ITree.iter body i')) by (right; exact (CIH i' Hl)).
    clear Hl. change (Leaf (inl i') (body i)) in Hs.
    induction Hs as [u Hu | u u' Hu _ IH | Y e u h y Hu _ IH];
      rewrite observe_bind, Hu; cbn.
    - constructor. exact Hup.
    - constructor. left. pfold. exact IH.
    - apply (DivVis _ _ e y). left. pfold. exact IH.
  Qed.

  (** An infinite path is an infinite run, or a finite run on which the
      body diverges. *)
  Lemma infinite_iter_inv (i : I) :
    any_infinite (ITree.iter body i) -> iterOut step i None \/ loopsForever step i.
  Proof.
    intro H. destruct (classic (iterOut step i None)) as [Hd | Hn]; [ left; exact Hd | right ].
    revert i H Hn. cofix CIH. intros i H Hn.
    rewrite unfold_iter in H.
    destruct (any_infinite_bind_inv _ _ H) as [Hb | [[i'|r] [Hx Hk]]].
    - exfalso. exact (Hn (iterOut_div step i Hb)).
    - cbn in Hk. rewrite Eqit.tau_eutt in Hk.
      refine (loopsForever_next step i i' Hx (CIH i' Hk _)).
      intro Hd. exact (Hn (iterOut_next step i i' None Hx Hd)).
    - destruct (any_infinite_ret r Hk).
  Qed.
End Loops.

(** [denote] maps a loop of trees to the loop of their outcomes. *)
Theorem denote_iter {I R} (body : I -> itree E (I + R)) (i : I) (o : option R) :
  unOptionT (getNE (denote (ITree.iter body i))) o
  <-> unOptionT (getNE (Basics.iter (fun j => denote (body j)) i)) o.
Proof.
  rewrite outcomes_iter, outcomes_denote. unfold iterOutcomes. destruct o as [r|]; split.
  - intro H. left. exact (leaf_iter_iterOut body i r H).
  - intros [H | [H _]]; [ exact (iterOut_tree body i _ H) | discriminate ].
  - intro H. destruct (infinite_iter_inv body i H) as [Hd | Hl];
      [ left; exact Hd | right; exact (conj eq_refl Hl) ].
  - intros [H | [_ H]]; [ exact (iterOut_tree body i _ H) | exact (loopsForever_infinite body i H) ].
Qed.
End Denote.
