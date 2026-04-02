(** * Predicate transformers and bundled predicate transformer arrows.

    We define the two predicate transformers on [SPArr] relations:

    [asp R pre b = exists a, pre a /\ R a b]   (angelic / existential)
    [dslp R pre b = forall a, R a b -> pre a]  (demonic / universal)

    Both [PureASPostArr] and [PureDSLPostArr] are sigma types over
    [SPRecord], a record that bundles a predicate transformer with
    its underlying relation.  They differ only in the correctness
    condition:

    [PureASPostArr A B] requires [sp_pt d pre b <-> asp (sp_rel d) pre b]
    [PureDSLPostArr A B] requires [sp_pt d pre b <-> dslp (sp_rel d) pre b]

    Both use the same relational composition, so both satisfy
    the arrow laws (proved in [SPostArrFacts.v]).

    Composed types for specifications:

    [ASPostArr S A = stateArrT S (optionArrT PureASPostArr) unit A]
    [DSLPostArr S A = stateArrT S (optionArrT PureDSLPostArr) unit A]

    Both unfold to [Pure(A/DSL)PostArr (unit * S) (option (A * S))]. *)

From Coq Require Import Program.Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.

(* ================================================================= *)
(** ** Predicate transformers and shared record                         *)
(* ================================================================= *)

(** Predicate transformer view: strongest postcondition (angelic / existential).
  *)
Definition asp {A B} (R : SPArr A B) (pre : A -> Prop) : B -> Prop :=
  fun b => exists a, pre a /\ R a b.

(* [asp] goes from predicate arrow to strongest postcondition arrow; [asp_inv] is
   the inverse. Similar to the relation described in Kenji's Ph.D. thesis, we
   can show that predicate monads and strongest postcondition monads are
   equivalent, by showing [asp_asp_inv] and [asp_inv_asp] below.

   TODO: Is the definition [asp_inv] the most general form? [dslp_inv] seems to be
   more flexible with a [forall] on [pre].

   TODO: Show that lawful arrow transformers preserve this equivalence.
 *)
Definition asp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : SPArr A B :=
  fun a b => pt (fun a' => a = a') b.

Theorem asp_asp_inv : forall {A B} (R : SPArr A B) a b,
    asp_inv (asp R) a b <-> R a b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? ?]]. subst. assumption.
  - intros. exists a. tauto.
Qed.

(* Cannot prove this for arbitrary [(A -> Prop) -> B -> Prop]. *)
Theorem asp_inv_asp : forall {A B} (R : SPArr A B) pre b,
    asp (asp_inv (asp R)) pre b <-> asp R pre b.
Proof.
  intros. unfold asp_inv, asp. split.
  - intros [? [? [? [? ?]]]]. subst.
    exists x0. tauto.
  - intros [? [? ?]].
    exists x. split; [assumption |].
    exists x. tauto.
Qed.

(** Demonic predicate transformer: universal dual of [asp]. *)
Definition dslp {A B} (R : SPArr A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

(* This shows a different equivalence between predicate arrows and strongest
   postcondition arrows. We can figure this out by "reverse engineering"
   [dslp_dslp_inv], but why does this one make sense? *)
Definition dslp_inv {A B} (pt : (A -> Prop) -> B -> Prop) : SPArr A B :=
  fun a b => forall pre, pt pre b -> pre a.

Theorem dslp_dslp_inv : forall {A B} (R : SPArr A B) a b,
    dslp_inv (dslp R) a b <-> R a b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros ?. apply H. auto.
  - intros. auto.
Qed.

Theorem dslp_inv_dslp : forall {A B} (R : SPArr A B) pre b,
    dslp (dslp_inv (dslp R)) pre b <-> dslp R pre b.
Proof.
  intros. unfold dslp_inv, dslp. split.
  - intros. apply H; intros. auto.
  - intros. apply H0. apply H.
Qed.

(** Bundle a predicate transformer with its underlying relation.
    Using a record avoids universe issues that [prod] causes when
    combined with [Eq1] from ExtLib. *)
Record SPRecord (A B : Type) := mkSPRecord {
  sp_pt : (A -> Prop) -> B -> Prop ;
  sp_rel : SPArr A B
}.
Arguments mkSPRecord {A B}.
Arguments sp_pt {A B}.
Arguments sp_rel {A B}.

(* ================================================================= *)
(** ** Angelic: [PureASPostArr]                                       *)
(* ================================================================= *)

(** [PureASPostArr] does not strictly need [SPRecord] — it could remain
    as [{ f | IsASP f }] with a Prop-level existential (see
    [Taxonomy/deprecated/SPostArr.v]).  Using the shared record lets us
    reuse arrow operations, equality lemmas, and monad infrastructure
    between the angelic and demonic variants. *)
Definition PureASPostArr (A B : Type) : Type :=
  { d : SPRecord A B |
    forall pre b, sp_pt d pre b <-> asp (sp_rel d) pre b }.

(** Smart constructor: wrap a relation with [asp]. *)
#[program] Definition mkASP {A B} (R : SPArr A B) : PureASPostArr A B :=
  mkSPRecord (asp R) R.
Next Obligation. reflexivity. Qed.

Section PureASPostArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureASPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_ASP {A B} (f : A -> B) : PureASPostArr A B :=
    mkSPRecord (fun pre b => exists a, pre a /\ f a = b) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_ASP {A B C}
    (f : PureASPostArr A B) (g : PureASPostArr B C) : PureASPostArr A C :=
    mkSPRecord (fun pre c => sp_pt g (sp_pt f pre) c)
               (fun a c => exists b, sp_rel f a b /\ sp_rel g b c).
  Next Obligation.
    split.
    - intro H. unfold asp. apply (proj2_sig g) in H. unfold asp in H.
      destruct H as [b0 [Hfb Hrgbc]].
      apply (proj2_sig f) in Hfb. unfold asp in Hfb.
      destruct Hfb as [a0 [Hpre Hrfab]].
      exists a0. split; [exact Hpre | exists b0; auto].
    - intros [a0 [Hpre [b0 [Hrfab Hrgbc]]]].
      apply (proj2_sig g). unfold asp.
      exists b0. split.
      + apply (proj2_sig f). unfold asp. exists a0. auto.
      + exact Hrgbc.
  Qed.

  #[local]
  #[program] Definition arr_first_ASP {A B C}
    (f : PureASPostArr A B) : PureASPostArr (A * C)%type (B * C)%type :=
    mkSPRecord
      (fun pre '(b, d) => sp_pt f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => sp_rel f a b /\ d = d').
  Next Obligation.
    unfold asp. split.
    - intro H. apply (proj2_sig f) in H. unfold asp in H.
      destruct H as [a [Hpre Hrf]].
      exists (a, c). simpl. auto.
    - intros [[a d0] [Hpre [Hrf Heq]]]. simpl in *. subst d0.
      apply (proj2_sig f). unfold asp. exists a. auto.
  Qed.

  #[global]
  Instance Arrow_PureASPostArr : Arrow PureASPostArr := {
    arr_pure := @arr_pure_ASP ;
    arr_comp := @arr_comp_ASP ;
    arr_first := @arr_first_ASP
  }.

  #[local]
  #[program] Definition arr_app_ASP {A B}
    : PureASPostArr (PureASPostArr A B * A)%type B :=
    mkSPRecord
      (fun pre b => exists f a, pre (f, a) /\ sp_rel (proj1_sig f) a b)
      (fun fa b => sp_rel (proj1_sig (fst fa)) (snd fa) b).
  Next Obligation.
    unfold asp. split.
    - intros [f [a [Hpre Hfab]]].
      exists (f, a). auto.
    - intros [[f a] [Hpre Hfab]].
      exists f, a. auto.
  Qed.

  #[global]
  Instance ArrowApply_PureASPostArr : ArrowApply PureASPostArr := {
    arr_app := @arr_app_ASP
  }.

End PureASPostArr.

(* ================================================================= *)
(** ** Demonic: [PureDSLPostArr]                                       *)
(* ================================================================= *)

Definition PureDSLPostArr (A B : Type) : Type :=
  { d : SPRecord A B |
    forall pre b, sp_pt d pre b <-> dslp (sp_rel d) pre b }.

(** Smart constructor: wrap a relation with [dslp]. *)
#[program] Definition mkDSLP {A B} (R : SPArr A B) : PureDSLPostArr A B :=
  mkSPRecord (dslp R) R.
Next Obligation. reflexivity. Qed.

Section PureDSLPostArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureDSLPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_DSLP {A B} (f : A -> B) : PureDSLPostArr A B :=
    mkSPRecord (fun pre b => forall a, f a = b -> pre a) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_DSLP {A B C}
    (f : PureDSLPostArr A B) (g : PureDSLPostArr B C) : PureDSLPostArr A C :=
    mkSPRecord (fun pre c => sp_pt g (sp_pt f pre) c)
               (fun a c => exists b, sp_rel f a b /\ sp_rel g b c).
  Next Obligation.
    split.
    - intro H. unfold dslp. intros a [b0 [Hrf Hrg]].
      apply (proj2_sig g) in H. unfold dslp in H.
      apply H in Hrg. apply (proj2_sig f) in Hrg. unfold dslp in Hrg.
      exact (Hrg a Hrf).
    - intros Hall. apply (proj2_sig g). unfold dslp.
      intros b0 Hrg. apply (proj2_sig f). unfold dslp. intros a Hrf.
      exact (Hall a (ex_intro _ b0 (conj Hrf Hrg))).
  Qed.

  #[local]
  #[program] Definition arr_first_DSLP {A B C}
    (f : PureDSLPostArr A B) : PureDSLPostArr (A * C)%type (B * C)%type :=
    mkSPRecord
      (fun pre '(b, d) => sp_pt f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => sp_rel f a b /\ d = d').
  Next Obligation.
    unfold dslp. split.
    - intro H. apply (proj2_sig f) in H. unfold dslp in H.
      intros [a d0] [Hrf Heq]. simpl in *. subst d0.
      exact (H a Hrf).
    - intros Hall. apply (proj2_sig f). unfold dslp. intros a Hrf.
      exact (Hall (a, _) (conj Hrf eq_refl)).
  Qed.

  #[global]
  Instance Arrow_PureDSLPostArr : Arrow PureDSLPostArr := {
    arr_pure := @arr_pure_DSLP ;
    arr_comp := @arr_comp_DSLP ;
    arr_first := @arr_first_DSLP
  }.

  #[local]
  #[program] Definition arr_app_DSLP {A B}
    : PureDSLPostArr (PureDSLPostArr A B * A)%type B :=
    mkSPRecord
      (fun pre b => forall f a, sp_rel (proj1_sig f) a b -> pre (f, a))
      (fun '(f, a) b => sp_rel f a b).
  Next Obligation.
    unfold dslp. split.
    - intros H [f0 a] Hfab. exact (H f0 a Hfab).
    - intros H f0 a Hfab. exact (H (f0, a) Hfab).
  Qed.

  #[global]
  Instance ArrowApply_PureDSLPostArr : ArrowApply PureDSLPostArr := {
    arr_app := @arr_app_DSLP
  }.

End PureDSLPostArr.

(* ================================================================= *)
(** ** Angelic option transformer: [optionASPArr]                     *)
(* ================================================================= *)

Section OptionASPArr.

  Definition optionASPArr := optionArrT PureASPostArr.

  #[local]
  #[program] Definition arr_pure_optASP {A B}
    (f : A -> B) : optionASPArr A B :=
    mkSPRecord
      (fun pre ob => match ob with
        | Some b => exists a, pre a /\ f a = b
        | None => False
      end)
      (fun a ob => match ob with Some b => f a = b | None => False end).
  Next Obligation.
    destruct b as [b|]; unfold asp; split; firstorder.
  Qed.

  #[local]
  #[program] Definition arr_comp_optASP {A B C}
    (f : optionASPArr A B) (g : optionASPArr B C)
    : optionASPArr A C :=
    mkSPRecord
      (fun pre oc => match oc with
        | Some c => sp_pt g (fun b => sp_pt f pre (Some b)) (Some c)
        | None => sp_pt f pre None \/
                  sp_pt g (fun b => sp_pt f pre (Some b)) None
      end)
      (fun a oc => match oc with
        | Some c => exists b, sp_rel f a (Some b) /\ sp_rel g b (Some c)
        | None => sp_rel f a None \/ exists b, sp_rel f a (Some b) /\ sp_rel g b None
      end).
  Next Obligation.
    destruct b as [c|]; unfold asp.
    - (* Some c *)
      split.
      + intro H. apply (proj2_sig g) in H. unfold asp in H.
        destruct H as [b [Hfb Hrgbc]].
        apply (proj2_sig f) in Hfb. unfold asp in Hfb.
        destruct Hfb as [a [Hpre Hrfab]].
        exists a. split; [exact Hpre | exists b; auto].
      + intros [a [Hpre [b [Hrfab Hrgbc]]]].
        apply (proj2_sig g). unfold asp. exists b. split.
        * apply (proj2_sig f). unfold asp. exists a; auto.
        * exact Hrgbc.
    - (* None *)
      split.
      + intros [HfNone | HgNone].
        * apply (proj2_sig f) in HfNone. unfold asp in HfNone.
          destruct HfNone as [a [Hpre Hrf]].
          exists a. split; [exact Hpre | left; exact Hrf].
        * apply (proj2_sig g) in HgNone. unfold asp in HgNone.
          destruct HgNone as [b [Hfb Hrgb]].
          apply (proj2_sig f) in Hfb. unfold asp in Hfb.
          destruct Hfb as [a [Hpre Hrfab]].
          exists a. split; [exact Hpre | right; exists b; auto].
      + intros [a [Hpre [Hrf | [b [Hrfab Hrgb]]]]].
        * left. apply (proj2_sig f). unfold asp. exists a; auto.
        * right. apply (proj2_sig g). unfold asp. exists b. split.
          -- apply (proj2_sig f). unfold asp. exists a; auto.
          -- exact Hrgb.
  Qed.

  #[local]
  #[program] Definition arr_first_optASP {A B C}
    (f : optionASPArr A B) : optionASPArr (A * C)%type (B * C)%type :=
    mkSPRecord
      (fun pre obc => match obc with
        | Some bd => sp_pt f (fun a => pre (a, snd bd)) (Some (fst bd))
        | None => exists d, sp_pt f (fun a => pre (a, d)) None
      end)
      (fun ad obc => match obc with
        | Some bd => sp_rel (proj1_sig f) (fst ad) (Some (fst bd)) /\ snd ad = snd bd
        | None => sp_rel (proj1_sig f) (fst ad) None
      end).
  Next Obligation.
    destruct b as [[b0 d0] |]; unfold asp.
    - (* Some (b0, d0) *)
      split.
      + intro H. apply (proj2_sig f) in H. unfold asp in H.
        destruct H as [a [Hpre Hrf]].
        exists (a, d0). simpl. auto.
      + intros [[a d1] [Hpre [Hrf Heq]]]. simpl in *. subst d1.
        apply (proj2_sig f). unfold asp. exists a. auto.
    - (* None *)
      split.
      + intros [d Hfd].
        apply (proj2_sig f) in Hfd. unfold asp in Hfd.
        destruct Hfd as [a [Hpre Hrf]].
        exists (a, d). simpl. auto.
      + intros [[a d] [Hpre Hrf]]. simpl in *.
        exists d. apply (proj2_sig f). unfold asp. exists a. auto.
  Qed.

  #[global]
  Instance Arrow_optionASPArr : Arrow optionASPArr := {
    arr_pure := @arr_pure_optASP ;
    arr_comp := @arr_comp_optASP ;
    arr_first := @arr_first_optASP
  }.

End OptionASPArr.

(* ================================================================= *)
(** ** Demonic option transformer: [optionDSLPArr]                     *)
(* ================================================================= *)

Section OptionDSLPArr.

  Definition optionDSLPArr := optionArrT PureDSLPostArr.

  #[local]
  #[program] Definition arr_pure_optDSLP {A B}
    (f : A -> B) : optionDSLPArr A B :=
    mkSPRecord
      (fun pre ob => match ob with
        | Some b => forall a, f a = b -> pre a
        | None => True
      end)
      (fun a ob => match ob with Some b => f a = b | None => False end).
  Next Obligation.
    destruct b as [b|]; unfold dslp; split; firstorder; discriminate.
  Qed.

  #[local]
  #[program] Definition arr_comp_optDSLP {A B C}
    (f : optionDSLPArr A B) (g : optionDSLPArr B C)
    : optionDSLPArr A C :=
    mkSPRecord
      (fun pre oc => match oc with
        | Some c => sp_pt g (fun b => sp_pt f pre (Some b)) (Some c)
        | None => sp_pt f pre None /\
                  sp_pt g (fun b => sp_pt f pre (Some b)) None
      end)
      (fun a oc => match oc with
        | Some c => exists b, sp_rel f a (Some b) /\ sp_rel g b (Some c)
        | None => sp_rel f a None \/
                  exists b, sp_rel f a (Some b) /\ sp_rel g b None
      end).
  Next Obligation.
    destruct b as [c|]; unfold dslp.
    - (* Some c *)
      split.
      + intro H. intros a [b0 [Hrfab Hrgbc]].
        apply (proj2_sig g) in H. unfold dslp in H.
        apply H in Hrgbc. apply (proj2_sig f) in Hrgbc. unfold dslp in Hrgbc.
        exact (Hrgbc a Hrfab).
      + intros Hall. apply (proj2_sig g). unfold dslp.
        intros b0 Hrgbc. apply (proj2_sig f). unfold dslp. intros a Hrfab.
        exact (Hall a (ex_intro _ b0 (conj Hrfab Hrgbc))).
    - (* None *)
      split.
      + intros [HfNone HgNone] a [Hrf | [b0 [Hrfab Hrgb]]].
        * apply (proj2_sig f) in HfNone. unfold dslp in HfNone.
          exact (HfNone a Hrf).
        * apply (proj2_sig g) in HgNone. unfold dslp in HgNone.
          apply HgNone in Hrgb. apply (proj2_sig f) in Hrgb. unfold dslp in Hrgb.
          exact (Hrgb a Hrfab).
      + intros Hall. split.
        * apply (proj2_sig f). unfold dslp. intros a Hrf.
          exact (Hall a (or_introl Hrf)).
        * apply (proj2_sig g). unfold dslp. intros b0 Hrgb.
          apply (proj2_sig f). unfold dslp. intros a Hrfab.
          exact (Hall a (or_intror (ex_intro _ b0 (conj Hrfab Hrgb)))).
  Qed.

  #[local]
  #[program] Definition arr_first_optDSLP {A B C}
    (f : optionDSLPArr A B) : optionDSLPArr (A * C)%type (B * C)%type :=
    mkSPRecord
      (fun pre obc => match obc with
        | Some bd => sp_pt f (fun a => pre (a, snd bd)) (Some (fst bd))
        | None => forall d, sp_pt f (fun a => pre (a, d)) None
      end)
      (fun ad obc => match obc with
        | Some bd => sp_rel f (fst ad) (Some (fst bd)) /\ snd ad = snd bd
        | None => sp_rel f (fst ad) None
      end).
  Next Obligation.
    destruct b as [[b0 d0] |]; unfold dslp.
    - (* Some (b0, d0) *)
      split.
      + intro H. apply (proj2_sig f) in H. unfold dslp in H.
        intros [a d1] [Hrf Heq]. simpl in *. subst d1.
        exact (H a Hrf).
      + intros Hall. apply (proj2_sig f). unfold dslp. intros a Hrf.
        exact (Hall (a, d0) (conj Hrf eq_refl)).
    - (* None *)
      split.
      + intros H [a d] Hrf. simpl in *.
        specialize (H d). apply (proj2_sig f) in H. unfold dslp in H.
        exact (H a Hrf).
      + intros Hall d. apply (proj2_sig f). unfold dslp. intros a Hrf.
        exact (Hall (a, d) Hrf).
  Qed.

  #[global]
  Instance Arrow_optionDSLPArr : Arrow optionDSLPArr := {
    arr_pure := @arr_pure_optDSLP ;
    arr_comp := @arr_comp_optDSLP ;
    arr_first := @arr_first_optDSLP
  }.

End OptionDSLPArr.

(* ================================================================= *)
(** ** Composed types for specifications                              *)
(* ================================================================= *)

Section ComposedTypes.

  Variable S : Type.

  (** [ASPostArr S A] is the angelic strongest postcondition arrow.
      [ASPostArr S A = PureASPostArr (unit * S) (option (A * S))] *)
  Definition ASPostArr (A : Type) : Type :=
    stateArrT S optionASPArr unit A.

  (** [DSLPostArr S A] is the demonic strongest liberal postcondition arrow.
      [DSLPostArr S A = PureDSLPostArr (unit * S) (option (A * S))] *)
  Definition DSLPostArr (A : Type) : Type :=
    stateArrT S optionDSLPArr unit A.

End ComposedTypes.
