(** * Bundled predicate transformer arrows: angelic and demonic.

    [PureASPostArr A B] (angelic) bundles [(A -> Prop) -> B -> Prop]
    with [IsASP], guaranteeing it equals [sp R] for some [R : SPArr A B].

    [PureDSPostArr A B] (demonic) bundles [(A -> Prop) -> B -> Prop]
    with [IsDSP], guaranteeing it equals [dp R] for some [R : SPArr A B].

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
(** ** Angelic: [PureASPostArr]                                       *)
(* ================================================================= *)

Section PureASPostArr.

  (** A predicate transformer is in the image of [sp] iff it equals
      [sp R] for some relation [R]. *)
  Definition IsASP {A B} (f : (A -> Prop) -> B -> Prop) : Prop :=
    exists R : SPArr A B, forall pre b, f pre b <-> sp R pre b.

  Definition PureASPostArr (A B : Type) : Type :=
    { f : (A -> Prop) -> B -> Prop | IsASP f }.

  (** Smart constructor: wrap a relation with [sp]. *)
  #[program] Definition mkASP {A B} (R : SPArr A B) : PureASPostArr A B :=
    sp R.
  Next Obligation.
    exists R. reflexivity.
  Defined.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureASPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_ASP {A B} (f : A -> B) : PureASPostArr A B :=
    fun pre b => exists a, pre a /\ f a = b.
  Next Obligation.
    exists (fun a b => f a = b). intros pre b. reflexivity.
  Qed.

  #[local]
  #[program] Definition arr_comp_ASP {A B C}
    (f : PureASPostArr A B) (g : PureASPostArr B C) : PureASPostArr A C :=
    fun pre c => proj1_sig g (proj1_sig f pre) c.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    destruct (proj2_sig g) as [Rg Hg].
    exists (fun a c => exists b, Rf a b /\ Rg b c).
    intros pre c. unfold sp.
    rewrite Hg. unfold sp.
    split.
    - intros [b [Hfb Hrgbc]].
      rewrite Hf in Hfb. destruct Hfb as [a [Hpre Hrfab]].
      exists a. split; [exact Hpre | exists b; split; assumption].
    - intros [a [Hpre [b [Hrfab Hrgbc]]]].
      exists b. split.
      + rewrite Hf. exists a. split; assumption.
      + exact Hrgbc.
  Qed.

  #[local]
  #[program] Definition arr_first_ASP {A B C}
    (f : PureASPostArr A B) : PureASPostArr (A * C)%type (B * C)%type :=
    fun pre '(b, d) => proj1_sig f (fun a => pre (a, d)) b.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    exists (fun '(a, d) '(b, d') => Rf a b /\ d = d').
    intros pre [b d']. unfold sp.
    split.
    - intro H. rewrite Hf in H. destruct H as [a [Hpre Hrf]].
      exists (a, d'). simpl. auto.
    - intros [[a d0] [Hpre [Hrf Heq]]]. simpl in *. subst d0.
      rewrite Hf. exists a. auto.
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
    fun pre b => exists f a, pre (f, a) /\ proj1_sig f (eq a) b.
  Next Obligation.
    exists (fun '(f, a) b => proj1_sig f (eq a) b).
    intros pre b. unfold sp. split.
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

Section PureDSPostArr.

  (** Demonic predicate transformer: universal dual of [sp]. *)
  Definition dp {A B} (R : SPArr A B) (pre : A -> Prop) : B -> Prop :=
    fun b => forall a, R a b -> pre a.

  (** A predicate transformer is in the image of [dp] iff it equals
      [dp R] for some relation [R]. *)
  Definition IsDSP {A B} (f : (A -> Prop) -> B -> Prop) : Prop :=
    exists R : SPArr A B, forall pre b, f pre b <-> dp R pre b.

  Definition PureDSPostArr (A B : Type) : Type :=
    { f : (A -> Prop) -> B -> Prop | IsDSP f }.

  (** Smart constructor: wrap a relation with [dp]. *)
  #[program] Definition mkDSP {A B} (R : SPArr A B) : PureDSPostArr A B :=
    dp R.
  Next Obligation.
    exists R. reflexivity.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureDSPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_DSP {A B} (f : A -> B) : PureDSPostArr A B :=
    fun pre b => forall a, f a = b -> pre a.
  Next Obligation.
    exists (fun a b => f a = b). intros pre b. reflexivity.
  Qed.

  #[local]
  #[program] Definition arr_comp_DSP {A B C}
    (f : PureDSPostArr A B) (g : PureDSPostArr B C) : PureDSPostArr A C :=
    fun pre c => proj1_sig g (proj1_sig f pre) c.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    destruct (proj2_sig g) as [Rg Hg].
    exists (fun a c => exists b, Rf a b /\ Rg b c).
    intros pre c. unfold dp.
    rewrite Hg. unfold dp.
    split.
    - intros Hgf a [b [Hrf Hrg]].
      apply Hgf in Hrg. rewrite Hf in Hrg. unfold dp in Hrg.
      exact (Hrg a Hrf).
    - intros Hall b Hrg.
      rewrite Hf. unfold dp. intros a Hrf.
      exact (Hall a (ex_intro _ b (conj Hrf Hrg))).
  Qed.

  #[local]
  #[program] Definition arr_first_DSP {A B C}
    (f : PureDSPostArr A B) : PureDSPostArr (A * C)%type (B * C)%type :=
    fun pre '(b, d) => proj1_sig f (fun a => pre (a, d)) b.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    exists (fun '(a, d) '(b, d') => Rf a b /\ d = d').
    intros pre [b d']. unfold dp.
    split.
    - intro H. rewrite Hf in H. unfold dp in H.
      intros [a d0] [Hrf Heq]. simpl in *. subst d0.
      exact (H a Hrf).
    - intros Hall.
      rewrite Hf. unfold dp. intros a Hrf.
      exact (Hall (a, d') (conj Hrf eq_refl)).
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
    fun pre b => forall f a,
      ~ proj1_sig f (fun a' => a' <> a) b -> pre (f, a).
  Next Obligation.
    exists (fun '(f, a) b => ~ proj1_sig f (fun a' => a' <> a) b).
    intros pre b. unfold dp. split.
    - intros H [f a] Hfab. exact (H f a Hfab).
    - intros H f a Hfab. exact (H (f, a) Hfab).
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
    fun pre ob => match ob with
      | Some b => exists a, pre a /\ f a = b
      | None => False
    end.
  Next Obligation.
    exists (fun a ob => match ob with Some b => f a = b | None => False end).
    intros pre [b|]; unfold sp; split; firstorder.
  Qed.

  #[local]
  #[program] Definition arr_comp_optASP {A B C}
    (f : optionASPArr A B) (g : optionASPArr B C)
    : optionASPArr A C :=
    fun pre oc => match oc with
      | Some c => proj1_sig g (fun b => proj1_sig f pre (Some b)) (Some c)
      | None => proj1_sig f pre None \/
                proj1_sig g (fun b => proj1_sig f pre (Some b)) None
    end.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    destruct (proj2_sig g) as [Rg Hg].
    exists (fun a oc => match oc with
      | Some c => exists b, Rf a (Some b) /\ Rg b (Some c)
      | None => Rf a None \/ exists b, Rf a (Some b) /\ Rg b None
    end).
    intros pre [c|]; unfold sp.
    - (* Some c *)
      rewrite Hg. unfold sp.
      split.
      + intros [b [Hfb Hrgbc]].
        rewrite Hf in Hfb. destruct Hfb as [a [Hpre Hrfab]].
        exists a. split; [exact Hpre | exists b; auto].
      + intros [a [Hpre [b [Hrfab Hrgbc]]]].
        exists b. split.
        * rewrite Hf. exists a; auto.
        * exact Hrgbc.
    - (* None *)
      split.
      + intros [HfNone | HgNone].
        * rewrite Hf in HfNone.
          destruct HfNone as [a [Hpre Hrf]].
          exists a. split; [exact Hpre | left; exact Hrf].
        * rewrite Hg in HgNone. unfold sp in HgNone.
          destruct HgNone as [b [Hfb Hrgb]].
          rewrite Hf in Hfb.
          destruct Hfb as [a [Hpre Hrfab]].
          exists a. split; [exact Hpre | right; exists b; auto].
      + intros [a [Hpre [Hrf | [b [Hrfab Hrgb]]]]].
        * left. rewrite Hf. exists a; auto.
        * right. rewrite Hg. unfold sp. exists b. split.
          -- rewrite Hf. exists a; auto.
          -- exact Hrgb.
  Qed.

  #[local]
  #[program] Definition arr_first_optASP {A B C}
    (f : optionASPArr A B) : optionASPArr (A * C)%type (B * C)%type :=
    fun pre obc => match obc with
      | Some (b, d) => proj1_sig f (fun a => pre (a, d)) (Some b)
      | None => exists d, proj1_sig f (fun a => pre (a, d)) None
    end.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    exists (fun '(a, d) obc => match obc with
      | Some (b, d') => Rf a (Some b) /\ d = d'
      | None => Rf a None
    end).
    intros pre [[b0 d0] |]; unfold sp.
    - (* Some (b0, d0) *)
      rewrite Hf. unfold sp.
      split.
      + intros [a [Hpre Hrf]].
        exists (a, d0). simpl. auto.
      + intros [[a d1] [Hpre [Hrf Heq]]]. simpl in *. subst d1.
        exists a. auto.
    - (* None *)
      split.
      + intros [d Hfd].
        rewrite Hf in Hfd. destruct Hfd as [a [Hpre Hrf]].
        exists (a, d). simpl. auto.
      + intros [[a d] [Hpre Hrf]]. simpl in *.
        exists d. rewrite Hf. exists a. auto.
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
    fun pre ob => match ob with
      | Some b => forall a, f a = b -> pre a
      | None => True
    end.
  Next Obligation.
    exists (fun a ob => match ob with Some b => f a = b | None => False end).
    intros pre [b|]; unfold dp; split; firstorder; discriminate.
  Qed.

  #[local]
  #[program] Definition arr_comp_optDSP {A B C}
    (f : optionDSPArr A B) (g : optionDSPArr B C)
    : optionDSPArr A C :=
    fun pre oc => match oc with
      | Some c => proj1_sig g (fun b => proj1_sig f pre (Some b)) (Some c)
      | None => proj1_sig f pre None /\
                proj1_sig g (fun b => proj1_sig f pre (Some b)) None
    end.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    destruct (proj2_sig g) as [Rg Hg].
    exists (fun a oc => match oc with
      | Some c => exists b, Rf a (Some b) /\ Rg b (Some c)
      | None => Rf a None \/ exists b, Rf a (Some b) /\ Rg b None
    end).
    intros pre [c|]; unfold dp.
    - (* Some c *)
      rewrite Hg. unfold dp.
      split.
      + intros Hgf a [b [Hrfab Hrgbc]].
        apply Hgf in Hrgbc. rewrite Hf in Hrgbc. unfold dp in Hrgbc.
        exact (Hrgbc a Hrfab).
      + intros Hall b Hrgbc.
        rewrite Hf. unfold dp. intros a Hrfab.
        exact (Hall a (ex_intro _ b (conj Hrfab Hrgbc))).
    - (* None *)
      split.
      + intros [HfNone HgNone] a [Hrf | [b [Hrfab Hrgb]]].
        * rewrite Hf in HfNone. unfold dp in HfNone.
          exact (HfNone a Hrf).
        * rewrite Hg in HgNone. unfold dp in HgNone.
          apply HgNone in Hrgb.
          rewrite Hf in Hrgb. unfold dp in Hrgb.
          exact (Hrgb a Hrfab).
      + intros Hall. split.
        * rewrite Hf. unfold dp. intros a Hrf.
          exact (Hall a (or_introl Hrf)).
        * rewrite Hg. unfold dp. intros b Hrgb.
          rewrite Hf. unfold dp. intros a Hrfab.
          exact (Hall a (or_intror (ex_intro _ b (conj Hrfab Hrgb)))).
  Qed.

  #[local]
  #[program] Definition arr_first_optDSP {A B C}
    (f : optionDSPArr A B) : optionDSPArr (A * C)%type (B * C)%type :=
    fun pre obc => match obc with
      | Some (b, d) => proj1_sig f (fun a => pre (a, d)) (Some b)
      | None => forall d, proj1_sig f (fun a => pre (a, d)) None
    end.
  Next Obligation.
    destruct (proj2_sig f) as [Rf Hf].
    exists (fun '(a, d) obc => match obc with
      | Some (b, d') => Rf a (Some b) /\ d = d'
      | None => Rf a None
    end).
    intros pre [[b0 d0] |]; unfold dp.
    - (* Some (b0, d0) *)
      rewrite Hf. unfold dp.
      split.
      + intros H [a d1] [Hrf Heq]. simpl in *. subst d1.
        exact (H a Hrf).
      + intros Hall a Hrf.
        exact (Hall (a, d0) (conj Hrf eq_refl)).
    - (* None *)
      split.
      + intros H [a d] Hrf. simpl in *.
        specialize (H d). rewrite Hf in H. unfold dp in H.
        exact (H a Hrf).
      + intros Hall d.
        rewrite Hf. unfold dp. intros a Hrf.
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
