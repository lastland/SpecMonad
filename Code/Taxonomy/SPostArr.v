(** * Bundled predicate transformer arrows: angelic and demonic.

    Both [PureASPostArr] and [PureDSPostArr] are sigma types over
    [SPRecord], a record that bundles a predicate transformer with
    its underlying relation.  They differ only in the correctness
    condition:

    [PureASPostArr A B] requires [sp_pt d pre b <-> sp (sp_rel d) pre b]
    [PureDSPostArr A B] requires [sp_pt d pre b <-> dp (sp_rel d) pre b]

    [sp R pre b = exists a, pre a /\ R a b]   (angelic / existential)
    [dp R pre b = forall a, R a b -> pre a]    (demonic / universal)

    Both use the same relational composition, so both satisfy
    the arrow laws (proved in [SPostArrFacts.v]).

    Composed types for specifications:

    [ASPostArr S A = stateArrT S (optionArrT PureASPostArr) unit A]
    [DSPostArr S A = stateArrT S (optionArrT PureDSPostArr) unit A]

    Both unfold to [Pure(A/D)SPostArr (unit * S) (option (A * S))]. *)

From Coq Require Import Program.Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.

(* ================================================================= *)
(** ** Shared record and demonic PT                                    *)
(* ================================================================= *)

(** Demonic predicate transformer: universal dual of [sp].

    TODO: Investigate if there's another predicate monad that corresponds to
    this. *)
Definition dp {A B} (R : SPArr A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

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
    forall pre b, sp_pt d pre b <-> sp (sp_rel d) pre b }.

(** Smart constructor: wrap a relation with [sp]. *)
#[program] Definition mkASP {A B} (R : SPArr A B) : PureASPostArr A B :=
  mkSPRecord (sp R) R.
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
    - intro H. unfold sp. apply (proj2_sig g) in H. unfold sp in H.
      destruct H as [b0 [Hfb Hrgbc]].
      apply (proj2_sig f) in Hfb. unfold sp in Hfb.
      destruct Hfb as [a0 [Hpre Hrfab]].
      exists a0. split; [exact Hpre | exists b0; auto].
    - intros [a0 [Hpre [b0 [Hrfab Hrgbc]]]].
      apply (proj2_sig g). unfold sp.
      exists b0. split.
      + apply (proj2_sig f). unfold sp. exists a0. auto.
      + exact Hrgbc.
  Qed.

  #[local]
  #[program] Definition arr_first_ASP {A B C}
    (f : PureASPostArr A B) : PureASPostArr (A * C)%type (B * C)%type :=
    mkSPRecord
      (fun pre '(b, d) => sp_pt f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => sp_rel f a b /\ d = d').
  Next Obligation.
    unfold sp. split.
    - intro H. apply (proj2_sig f) in H. unfold sp in H.
      destruct H as [a [Hpre Hrf]].
      exists (a, c). simpl. auto.
    - intros [[a d0] [Hpre [Hrf Heq]]]. simpl in *. subst d0.
      apply (proj2_sig f). unfold sp. exists a. auto.
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
    unfold sp. split.
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
(** ** Demonic: [PureDSPostArr]                                       *)
(* ================================================================= *)

Definition PureDSPostArr (A B : Type) : Type :=
  { d : SPRecord A B |
    forall pre b, sp_pt d pre b <-> dp (sp_rel d) pre b }.

(** Smart constructor: wrap a relation with [dp]. *)
#[program] Definition mkDSP {A B} (R : SPArr A B) : PureDSPostArr A B :=
  mkSPRecord (dp R) R.
Next Obligation. reflexivity. Qed.

Section PureDSPostArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureDSPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_DSP {A B} (f : A -> B) : PureDSPostArr A B :=
    mkSPRecord (fun pre b => forall a, f a = b -> pre a) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_DSP {A B C}
    (f : PureDSPostArr A B) (g : PureDSPostArr B C) : PureDSPostArr A C :=
    mkSPRecord (fun pre c => sp_pt g (sp_pt f pre) c)
               (fun a c => exists b, sp_rel f a b /\ sp_rel g b c).
  Next Obligation.
    split.
    - intro H. unfold dp. intros a [b0 [Hrf Hrg]].
      apply (proj2_sig g) in H. unfold dp in H.
      apply H in Hrg. apply (proj2_sig f) in Hrg. unfold dp in Hrg.
      exact (Hrg a Hrf).
    - intros Hall. apply (proj2_sig g). unfold dp.
      intros b0 Hrg. apply (proj2_sig f). unfold dp. intros a Hrf.
      exact (Hall a (ex_intro _ b0 (conj Hrf Hrg))).
  Qed.

  #[local]
  #[program] Definition arr_first_DSP {A B C}
    (f : PureDSPostArr A B) : PureDSPostArr (A * C)%type (B * C)%type :=
    mkSPRecord
      (fun pre '(b, d) => sp_pt f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => sp_rel f a b /\ d = d').
  Next Obligation.
    unfold dp. split.
    - intro H. apply (proj2_sig f) in H. unfold dp in H.
      intros [a d0] [Hrf Heq]. simpl in *. subst d0.
      exact (H a Hrf).
    - intros Hall. apply (proj2_sig f). unfold dp. intros a Hrf.
      exact (Hall (a, _) (conj Hrf eq_refl)).
  Qed.

  #[global]
  Instance Arrow_PureDSPostArr : Arrow PureDSPostArr := {
    arr_pure := @arr_pure_DSP ;
    arr_comp := @arr_comp_DSP ;
    arr_first := @arr_first_DSP
  }.

  #[local]
  #[program] Definition arr_app_DSP {A B}
    : PureDSPostArr (PureDSPostArr A B * A)%type B :=
    mkSPRecord
      (fun pre b => forall f a, sp_rel (proj1_sig f) a b -> pre (f, a))
      (fun '(f, a) b => sp_rel f a b).
  Next Obligation.
    unfold dp. split.
    - intros H [f0 a] Hfab. exact (H f0 a Hfab).
    - intros H f0 a Hfab. exact (H (f0, a) Hfab).
  Qed.

  #[global]
  Instance ArrowApply_PureDSPostArr : ArrowApply PureDSPostArr := {
    arr_app := @arr_app_DSP
  }.

End PureDSPostArr.

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
    destruct b as [b|]; unfold sp; split; firstorder.
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
    destruct b as [c|]; unfold sp.
    - (* Some c *)
      split.
      + intro H. apply (proj2_sig g) in H. unfold sp in H.
        destruct H as [b [Hfb Hrgbc]].
        apply (proj2_sig f) in Hfb. unfold sp in Hfb.
        destruct Hfb as [a [Hpre Hrfab]].
        exists a. split; [exact Hpre | exists b; auto].
      + intros [a [Hpre [b [Hrfab Hrgbc]]]].
        apply (proj2_sig g). unfold sp. exists b. split.
        * apply (proj2_sig f). unfold sp. exists a; auto.
        * exact Hrgbc.
    - (* None *)
      split.
      + intros [HfNone | HgNone].
        * apply (proj2_sig f) in HfNone. unfold sp in HfNone.
          destruct HfNone as [a [Hpre Hrf]].
          exists a. split; [exact Hpre | left; exact Hrf].
        * apply (proj2_sig g) in HgNone. unfold sp in HgNone.
          destruct HgNone as [b [Hfb Hrgb]].
          apply (proj2_sig f) in Hfb. unfold sp in Hfb.
          destruct Hfb as [a [Hpre Hrfab]].
          exists a. split; [exact Hpre | right; exists b; auto].
      + intros [a [Hpre [Hrf | [b [Hrfab Hrgb]]]]].
        * left. apply (proj2_sig f). unfold sp. exists a; auto.
        * right. apply (proj2_sig g). unfold sp. exists b. split.
          -- apply (proj2_sig f). unfold sp. exists a; auto.
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
    destruct b as [[b0 d0] |]; unfold sp.
    - (* Some (b0, d0) *)
      split.
      + intro H. apply (proj2_sig f) in H. unfold sp in H.
        destruct H as [a [Hpre Hrf]].
        exists (a, d0). simpl. auto.
      + intros [[a d1] [Hpre [Hrf Heq]]]. simpl in *. subst d1.
        apply (proj2_sig f). unfold sp. exists a. auto.
    - (* None *)
      split.
      + intros [d Hfd].
        apply (proj2_sig f) in Hfd. unfold sp in Hfd.
        destruct Hfd as [a [Hpre Hrf]].
        exists (a, d). simpl. auto.
      + intros [[a d] [Hpre Hrf]]. simpl in *.
        exists d. apply (proj2_sig f). unfold sp. exists a. auto.
  Qed.

  #[global]
  Instance Arrow_optionASPArr : Arrow optionASPArr := {
    arr_pure := @arr_pure_optASP ;
    arr_comp := @arr_comp_optASP ;
    arr_first := @arr_first_optASP
  }.

End OptionASPArr.

(* ================================================================= *)
(** ** Demonic option transformer: [optionDSPArr]                     *)
(* ================================================================= *)

Section OptionDSPArr.

  Definition optionDSPArr := optionArrT PureDSPostArr.

  #[local]
  #[program] Definition arr_pure_optDSP {A B}
    (f : A -> B) : optionDSPArr A B :=
    mkSPRecord
      (fun pre ob => match ob with
        | Some b => forall a, f a = b -> pre a
        | None => True
      end)
      (fun a ob => match ob with Some b => f a = b | None => False end).
  Next Obligation.
    destruct b as [b|]; unfold dp; split; firstorder; discriminate.
  Qed.

  #[local]
  #[program] Definition arr_comp_optDSP {A B C}
    (f : optionDSPArr A B) (g : optionDSPArr B C)
    : optionDSPArr A C :=
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
    destruct b as [c|]; unfold dp.
    - (* Some c *)
      split.
      + intro H. intros a [b0 [Hrfab Hrgbc]].
        apply (proj2_sig g) in H. unfold dp in H.
        apply H in Hrgbc. apply (proj2_sig f) in Hrgbc. unfold dp in Hrgbc.
        exact (Hrgbc a Hrfab).
      + intros Hall. apply (proj2_sig g). unfold dp.
        intros b0 Hrgbc. apply (proj2_sig f). unfold dp. intros a Hrfab.
        exact (Hall a (ex_intro _ b0 (conj Hrfab Hrgbc))).
    - (* None *)
      split.
      + intros [HfNone HgNone] a [Hrf | [b0 [Hrfab Hrgb]]].
        * apply (proj2_sig f) in HfNone. unfold dp in HfNone.
          exact (HfNone a Hrf).
        * apply (proj2_sig g) in HgNone. unfold dp in HgNone.
          apply HgNone in Hrgb. apply (proj2_sig f) in Hrgb. unfold dp in Hrgb.
          exact (Hrgb a Hrfab).
      + intros Hall. split.
        * apply (proj2_sig f). unfold dp. intros a Hrf.
          exact (Hall a (or_introl Hrf)).
        * apply (proj2_sig g). unfold dp. intros b0 Hrgb.
          apply (proj2_sig f). unfold dp. intros a Hrfab.
          exact (Hall a (or_intror (ex_intro _ b0 (conj Hrfab Hrgb)))).
  Qed.

  #[local]
  #[program] Definition arr_first_optDSP {A B C}
    (f : optionDSPArr A B) : optionDSPArr (A * C)%type (B * C)%type :=
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
    destruct b as [[b0 d0] |]; unfold dp.
    - (* Some (b0, d0) *)
      split.
      + intro H. apply (proj2_sig f) in H. unfold dp in H.
        intros [a d1] [Hrf Heq]. simpl in *. subst d1.
        exact (H a Hrf).
      + intros Hall. apply (proj2_sig f). unfold dp. intros a Hrf.
        exact (Hall (a, d0) (conj Hrf eq_refl)).
    - (* None *)
      split.
      + intros H [a d] Hrf. simpl in *.
        specialize (H d). apply (proj2_sig f) in H. unfold dp in H.
        exact (H a Hrf).
      + intros Hall d. apply (proj2_sig f). unfold dp. intros a Hrf.
        exact (Hall (a, d) Hrf).
  Qed.

  #[global]
  Instance Arrow_optionDSPArr : Arrow optionDSPArr := {
    arr_pure := @arr_pure_optDSP ;
    arr_comp := @arr_comp_optDSP ;
    arr_first := @arr_first_optDSP
  }.

End OptionDSPArr.

(* ================================================================= *)
(** ** Composed types for specifications                              *)
(* ================================================================= *)

Section ComposedTypes.

  Variable S : Type.

  (** [ASPostArr S A] is the angelic strongest postcondition arrow.
      [ASPostArr S A = PureASPostArr (unit * S) (option (A * S))] *)
  Definition ASPostArr (A : Type) : Type :=
    stateArrT S optionASPArr unit A.

  (** [DSPostArr S A] is the demonic strongest liberal postcondition arrow.
      [DSPostArr S A = PureDSPostArr (unit * S) (option (A * S))] *)
  Definition DSPostArr (A : Type) : Type :=
    stateArrT S optionDSPArr unit A.

End ComposedTypes.
