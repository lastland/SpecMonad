(** * SP judgments over observed specifications.

    Shared Over/Under triple judgments for computations that have already
    been observed into the specification monads of
    [BaseSpecMonads/SPostArrMonad]. [tripleASP] and [tripleDSL] run the
    observation at the intended precondition [pre]; [tripleASPspec] and
    [tripleDSLspec] run it at an arbitrary precondition [p] transferred to
    [pre] by [pp2_over] or
    [pp2_under].  The [DefEq] theorems bridge the two presentations for
    every specification arrow, by monotonicity alone — no hypothesis on
    [w] beyond its carrier. *)

From Incorrectness.Taxonomy.BaseSpecMonads Require Export SPostArrMonad.

(** ** Approximation direction *)

Inductive approxKind := Under | Over.

(** ** Precondition transfer

    [pp2_over pre post p r] requires [post r] whenever [p] implies [pre].
    [pp2_under pre post p r] requires both that [pre] implies [p] and
    that [post r] holds. *)

Definition pp2_over {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  (p : S -> Prop) (r : option (A * S)) : Prop :=
  (forall s, p s -> pre s) -> post r.

Definition pp2_under {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
  (p : S -> Prop) (r : option (A * S)) : Prop :=
  (forall s, pre s -> p s) /\ post r.

(** ** Angelic (ASP) triples *)

Definition tripleASP {S A} (w : ASPostArr S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  match kind with
  | Over => forall r, runASP w pre r -> post r
  | Under => forall r, post r -> runASP w pre r
  end.

Definition tripleASPspec {S A} (w : ASPostArr S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  match kind with
  | Over => forall p r, runASP w p r -> pp2_over pre post p r
  | Under => forall p r, pp2_under pre post p r -> runASP w p r
  end.

Theorem tripleASPDefEq {S A} (w : ASPostArr S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
  tripleASP w kind pre post <-> tripleASPspec w kind pre post.
Proof.
  unfold tripleASP, tripleASPspec, pp2_over, pp2_under.
  destruct kind; split.
  - (* Under: intended implies spec *)
    intros H p r [Hsub Hpost]. unfold runASP in *.
    exact (ASP_monotone w (fun us => pre (snd us)) (fun us => p (snd us)) r
      (fun us Hps => Hsub (snd us) Hps) (H r Hpost)).
  - (* Under: spec implies intended *)
    intros H r Hpost.
    exact (H pre r (conj (fun s Hs => Hs) Hpost)).
  - (* Over: intended implies spec *)
    intros H p r Hrun Hsub. apply (H r). unfold runASP in *.
    exact (ASP_monotone w (fun us => p (snd us)) (fun us => pre (snd us)) r
      (fun us Hps => Hsub (snd us) Hps) Hrun).
  - (* Over: spec implies intended *)
    intros H r Hrun.
    exact (H pre r Hrun (fun s Hs => Hs)).
Qed.

(** ** Demonic (DSLP) triples *)

Definition tripleDSL {S A} (w : DSLPostArr S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  match kind with
  | Over => forall r, runDSLP w pre r -> post r
  | Under => forall r, post r -> runDSLP w pre r
  end.

Definition tripleDSLspec {S A} (w : DSLPostArr S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  match kind with
  | Over => forall p r, runDSLP w p r -> pp2_over pre post p r
  | Under => forall p r, pp2_under pre post p r -> runDSLP w p r
  end.

Theorem tripleDSLDefEq {S A} (w : DSLPostArr S A) (kind : approxKind)
    (pre : S -> Prop) (post : option (A * S) -> Prop) :
  tripleDSL w kind pre post <-> tripleDSLspec w kind pre post.
Proof.
  unfold tripleDSL, tripleDSLspec, pp2_over, pp2_under.
  destruct kind; split.
  - (* Under: intended implies spec *)
    intros H p r [Hsub Hpost]. unfold runDSLP in *.
    exact (DSLP_monotone w (fun us => pre (snd us)) (fun us => p (snd us)) r
      (fun us Hps => Hsub (snd us) Hps) (H r Hpost)).
  - (* Under: spec implies intended *)
    intros H r Hpost.
    exact (H pre r (conj (fun s Hs => Hs) Hpost)).
  - (* Over: intended implies spec *)
    intros H p r Hrun Hsub. apply (H r). unfold runDSLP in *.
    exact (DSLP_monotone w (fun us => p (snd us)) (fun us => pre (snd us)) r
      (fun us Hps => Hsub (snd us) Hps) Hrun).
  - (* Over: spec implies intended *)
    intros H r Hrun.
    exact (H pre r Hrun (fun s Hs => Hs)).
Qed.
