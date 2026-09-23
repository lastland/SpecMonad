(** * The four WP observations of [(optionT SetM)] -- and the only algebras in the
      WP taxonomy.

    [(optionT SetM) A = optionT SetM A] is the base of every computation stack in
    [ComputationMonads/]:

      [rddivnd   R A] = [readerT R (optionT SetM) A]
      [stdivnd   S A] = [stateT S (optionT SetM) A]
      [stdivexcnd S A] = [stateT S (optionT (optionT SetM)) A]

    all by [eq_refl].  So the algebras below are the entire algebraic
    content of the WP side: every other observation in this directory is
    one of these four, carried through a LIFT ([MonadAlgebra.v]'s
    [MMor_readerT], [MMor_stateT], [MMor_optionT]) rather than re-derived.

    Two binary choices, four observations:

      - [SetM]              : demonic (meet) or angelic (join);
      - the divergence token: [False] (total) or [True] (liberal).

    A layer that is LIFTED offers no such choice, which is why the reader
    and state stacks have four observations apiece and not more. *)

From ExtLib Require Import Monad OptionMonad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.ComputationMonads Require Import
  TransformerLaws StExcNonDet DivNonDet.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad MonadAlgebra.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The two algebras of [SetM]                                     *)
(* ================================================================= *)

(** There is no canonical choice between them, so neither is an [Instance]:
    a nondeterministic set of assertions can be collapsed by meet or by
    join, and which one is meant is part of the specification. *)

Definition mu_SetM_demonic (P : SetM Prop) : Prop := forall p, P p -> p.
Definition mu_SetM_angelic (P : SetM Prop) : Prop := exists p, P p /\ p.

Definition MAlg_SetM_demonic : MAlg SetM Prop.
Proof.
  refine {| mu := mu_SetM_demonic |}.
  - (* proper *)
    (* [Eq1_SetM] is Leibniz equality, so this is immediate *)
    intros x y Hxy. unfold eq1, Eq1_SetM in Hxy. subst y. reflexivity.
  - (* ret *)
    intro p. unfold mu_SetM_demonic. cbn. split.
    + intro H. exact (H p eq_refl).
    + intros Hp q Heq. subst q. exact Hp.
  - (* bind *)
    intros A x f g Hfg H. unfold mu_SetM_demonic in *. cbn in *.
    intros p [a [Hx Hg]].
    apply (Hfg a); [| exact Hg ].
    intros q Hq. apply H. exists a. split; [ exact Hx | exact Hq ].
Defined.

Definition MAlg_SetM_angelic : MAlg SetM Prop.
Proof.
  refine {| mu := mu_SetM_angelic |}.
  - (* proper *)
    intros x y Hxy. unfold eq1, Eq1_SetM in Hxy. subst y. reflexivity.
  - (* ret *)
    intro p. unfold mu_SetM_angelic. cbn. split.
    + intros [q [Heq Hq]]. subst q. exact Hq.
    + intro Hp. exists p. split; [ reflexivity | exact Hp ].
  - (* bind *)
    intros A x f g Hfg H. unfold mu_SetM_angelic in *. cbn in *.
    destruct H as [p [[a [Hx Hf]] Hp]].
    destruct (Hfg a (ex_intro _ p (conj Hf Hp))) as [q [Hg Hq]].
    exists q. split; [ exists a; split; [ exact Hx | exact Hg ] | exact Hq ].
Defined.

(* ================================================================= *)
(** ** The four algebras of [(optionT SetM)]                                   *)
(* ================================================================= *)

(** [MAlg_optionT none] collapses the divergence token to [none]: [False]
    for the TOTAL readings, [True] for the LIBERAL ones. *)

Definition MAlg_DWP : MAlg (optionT SetM) Prop :=
  MAlg_optionT (AM := MAlg_SetM_demonic) False.
Definition MAlg_DWLP : MAlg (optionT SetM) Prop :=
  MAlg_optionT (AM := MAlg_SetM_demonic) True.
Definition MAlg_AWP : MAlg (optionT SetM) Prop :=
  MAlg_optionT (AM := MAlg_SetM_angelic) False.
Definition MAlg_AWLP : MAlg (optionT SetM) Prop :=
  MAlg_optionT (AM := MAlg_SetM_angelic) True.

(** The four core morphisms.  Everything else in this directory is one of
    these four under a lift. *)

Definition MMor_DWP  : MMor (optionT SetM) WPure := MMor_of_MAlg _ MAlg_DWP.
Definition MMor_DWLP : MMor (optionT SetM) WPure := MMor_of_MAlg _ MAlg_DWLP.
Definition MMor_AWP  : MMor (optionT SetM) WPure := MMor_of_MAlg _ MAlg_AWP.
Definition MMor_AWLP : MMor (optionT SetM) WPure := MMor_of_MAlg _ MAlg_AWLP.

(* ================================================================= *)
(** ** The observations                                               *)
(* ================================================================= *)

Definition obsDWPp  {A} (m : (optionT SetM) A) : WPure A := mmor MMor_DWP m.
Definition obsDWLPp {A} (m : (optionT SetM) A) : WPure A := mmor MMor_DWLP m.
Definition obsAWPp  {A} (m : (optionT SetM) A) : WPure A := mmor MMor_AWP m.
Definition obsAWLPp {A} (m : (optionT SetM) A) : WPure A := mmor MMor_AWLP m.

(** What each one says, in terms of the outcome set. *)

Lemma obsDWPp_get {A} (m : (optionT SetM) A) (post : A -> Prop) :
  getWPure (obsDWPp m) post
  <-> (forall oa, unOptionT m oa ->
                  match oa with Some a => post a | None => False end).
Proof.
  unfold obsDWPp, MMor_DWP, MAlg_DWP. cbn [mmor MMor_of_MAlg].
  rewrite obsA_get.
  cbn [mu MAlg_optionT mu_optionT MAlg_SetM_demonic bind ret
       Monad_optionT Monad_SetM unOptionT].
  unfold mu_SetM_demonic. split.
  - intros H oa Ho. destruct oa as [a|].
    + exact (H (post a) (ex_intro _ (Some (post a))
               (conj (ex_intro _ (Some a) (conj Ho eq_refl)) eq_refl))).
    + exact (H False (ex_intro _ None
               (conj (ex_intro _ None (conj Ho eq_refl)) eq_refl))).
  - intros H p [o [[oa [Ho Hoa]] Hp]].
    destruct oa as [a|]; cbn in Hoa; subst o; cbn in Hp; subst p.
    + exact (H (Some a) Ho).
    + exact (H None Ho).
Qed.

Lemma obsAWPp_get {A} (m : (optionT SetM) A) (post : A -> Prop) :
  getWPure (obsAWPp m) post <-> (exists a, unOptionT m (Some a) /\ post a).
Proof.
  unfold obsAWPp, MMor_AWP, MAlg_AWP. cbn [mmor MMor_of_MAlg].
  rewrite obsA_get.
  cbn [mu MAlg_optionT mu_optionT MAlg_SetM_angelic bind ret
       Monad_optionT Monad_SetM unOptionT].
  unfold mu_SetM_angelic. split.
  - intros [p [[o [[oa [Ho Hoa]] Hp]] Hq]].
    destruct oa as [a|]; cbn in Hoa; subst o; cbn in Hp; subst p.
    + exists a. split; [ exact Ho | exact Hq ].
    + destruct Hq.
  - intros [a [Ho Hp]]. exists (post a). split; [| exact Hp ].
    exists (Some (post a)). split; [| reflexivity ].
    exists (Some a). split; [ exact Ho | reflexivity ].
Qed.

Lemma obsDWLPp_get {A} (m : (optionT SetM) A) (post : A -> Prop) :
  getWPure (obsDWLPp m) post
  <-> (forall oa, unOptionT m oa ->
                  match oa with Some a => post a | None => True end).
Proof.
  unfold obsDWLPp, MMor_DWLP, MAlg_DWLP. cbn [mmor MMor_of_MAlg].
  rewrite obsA_get.
  cbn [mu MAlg_optionT mu_optionT MAlg_SetM_demonic bind ret
       Monad_optionT Monad_SetM unOptionT].
  unfold mu_SetM_demonic. split.
  - intros H oa Ho. destruct oa as [a|].
    + exact (H (post a) (ex_intro _ (Some (post a))
               (conj (ex_intro _ (Some a) (conj Ho eq_refl)) eq_refl))).
    + exact I.
  - intros H p [o [[oa [Ho Hoa]] Hp]].
    destruct oa as [a|]; cbn in Hoa; subst o; cbn in Hp; subst p.
    + exact (H (Some a) Ho).
    + exact I.
Qed.

Lemma obsAWLPp_get {A} (m : (optionT SetM) A) (post : A -> Prop) :
  getWPure (obsAWLPp m) post
  <-> ((exists a, unOptionT m (Some a) /\ post a) \/ unOptionT m None).
Proof.
  unfold obsAWLPp, MMor_AWLP, MAlg_AWLP. cbn [mmor MMor_of_MAlg].
  rewrite obsA_get.
  cbn [mu MAlg_optionT mu_optionT MAlg_SetM_angelic bind ret
       Monad_optionT Monad_SetM unOptionT].
  unfold mu_SetM_angelic. split.
  - intros [p [[o [[oa [Ho Hoa]] Hp]] Hq]].
    destruct oa as [a|]; cbn in Hoa; subst o; cbn in Hp; subst p.
    + left. exists a. split; [ exact Ho | exact Hq ].
    + right. exact Ho.
  - intros [[a [Ho Hp]] | Hn].
    + exists (post a). split; [| exact Hp ].
      exists (Some (post a)). split; [| reflexivity ].
      exists (Some a). split; [ exact Ho | reflexivity ].
    + exists True. split; [| exact I ].
      exists None. split; [| reflexivity ].
      exists None. split; [ exact Hn | reflexivity ].
Qed.

(* ================================================================= *)
(** ** The morphism laws, for free                                    *)
(* ================================================================= *)

Theorem obsDWPp_ret {A} (a : A) : eq1 (obsDWPp (ret a)) (ret a).
Proof. exact (mmor_ret (MMor := MMor_DWP) A a). Qed.
Theorem obsDWPp_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsDWPp (x >>= f)) (obsDWPp x >>= (fun a => obsDWPp (f a))).
Proof. exact (mmor_bind (MMor := MMor_DWP) A B x f). Qed.

Theorem obsDWLPp_ret {A} (a : A) : eq1 (obsDWLPp (ret a)) (ret a).
Proof. exact (mmor_ret (MMor := MMor_DWLP) A a). Qed.
Theorem obsDWLPp_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsDWLPp (x >>= f)) (obsDWLPp x >>= (fun a => obsDWLPp (f a))).
Proof. exact (mmor_bind (MMor := MMor_DWLP) A B x f). Qed.

Theorem obsAWPp_ret {A} (a : A) : eq1 (obsAWPp (ret a)) (ret a).
Proof. exact (mmor_ret (MMor := MMor_AWP) A a). Qed.
Theorem obsAWPp_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsAWPp (x >>= f)) (obsAWPp x >>= (fun a => obsAWPp (f a))).
Proof. exact (mmor_bind (MMor := MMor_AWP) A B x f). Qed.

Theorem obsAWLPp_ret {A} (a : A) : eq1 (obsAWLPp (ret a)) (ret a).
Proof. exact (mmor_ret (MMor := MMor_AWLP) A a). Qed.
Theorem obsAWLPp_bind {A B} (x : (optionT SetM) A) (f : A -> (optionT SetM) B) :
  eq1 (obsAWLPp (x >>= f)) (obsAWLPp x >>= (fun a => obsAWLPp (f a))).
Proof. exact (mmor_bind (MMor := MMor_AWLP) A B x f). Qed.

(** The divergent program separates the total readings from the liberal
    ones, which is the whole content of the [none] choice. *)

Theorem obsDWPp_divergeD {A} (post : A -> Prop) :
  getWPure (obsDWPp divergeD) post <-> False.
Proof.
  rewrite obsDWPp_get. split; [| destruct 1 ].
  intro H. exact (H None eq_refl).
Qed.

Theorem obsAWPp_divergeD {A} (post : A -> Prop) :
  getWPure (obsAWPp divergeD) post <-> False.
Proof.
  rewrite obsAWPp_get. split; [| destruct 1 ].
  intros [a [Ho _]]. discriminate Ho.
Qed.
