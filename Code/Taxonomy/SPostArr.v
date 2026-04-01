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

  (** A predicate transformer is in the image of [sp] iff it equals [sp R] for
      some relation [R]. This seems to be consistent with what's in Kenji's
      Ph.D. thesis: predicate monads = strongest postcondition transformer
      monad, but we additionally consider the input due to being an arrow. *)
  Definition IsASP {A B} (f : (A -> Prop) -> B -> Prop) : Prop :=
    exists R : SPArr A B, forall pre b, f pre b <-> sp R pre b.

  Definition PureASPostArr (A B : Type) : Type :=
    { f : (A -> Prop) -> B -> Prop | IsASP f }.

  (** Smart constructor: wrap a relation with [sp]. *)
  #[program] Definition mkASP {A B} (R : SPArr A B) : PureASPostArr A B :=
    sp R.
  Next Obligation.
    exists R. reflexivity.
  Qed.

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
    fun pre c => g (f pre) c.
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
    fun pre '(b, d) => f (fun a => pre (a, d)) b.
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
    fun pre b => exists f a, pre (f, a) /\ f (eq a) b.
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

(** Demonic predicate transformer: universal dual of [sp]. This diverges from
    the strongest postcondition transformer in Kenji's Ph.D. thesis.

    TODO: Investigate if there's another predicate monad that corresponds to
    this. *)
Definition dp {A B} (R : SPArr A B) (pre : A -> Prop) : B -> Prop :=
  fun b => forall a, R a b -> pre a.

(** Bundle a predicate transformer with its underlying relation.
    Using a record avoids universe issues that [prod] causes when
    combined with [Eq1] from ExtLib. *)
Record DSPData (A B : Type) := mkDSPData {
  dsp_pt : (A -> Prop) -> B -> Prop ;
  dsp_rel : SPArr A B
}.
Arguments mkDSPData {A B}.
Arguments dsp_pt {A B}.
Arguments dsp_rel {A B}.

Definition PureDSPostArr (A B : Type) : Type :=
  { d : DSPData A B |
    forall pre b, dsp_pt d pre b <-> dp (dsp_rel d) pre b }.

(** Smart constructor: wrap a relation with [dp]. *)
#[program] Definition mkDSP {A B} (R : SPArr A B) : PureDSPostArr A B :=
  mkDSPData (dp R) R.
Next Obligation. reflexivity. Qed.

Section PureDSPostArr.

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureDSPostArr]                          *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_DSP {A B} (f : A -> B) : PureDSPostArr A B :=
    mkDSPData (fun pre b => forall a, f a = b -> pre a) (fun a b => f a = b).
  Next Obligation. reflexivity. Qed.

  #[local]
  #[program] Definition arr_comp_DSP {A B C}
    (f : PureDSPostArr A B) (g : PureDSPostArr B C) : PureDSPostArr A C :=
    mkDSPData (fun pre c => dsp_pt g (dsp_pt f pre) c)
                  (fun a c => exists b, dsp_rel f a b /\ dsp_rel g b c).
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
    mkDSPData
      (fun pre '(b, d) => dsp_pt f (fun a => pre (a, d)) b)
      (fun '(a, d) '(b, d') => dsp_rel f a b /\ d = d').
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
    mkDSPData
      (fun pre b => forall f a, dsp_rel (proj1_sig f) a b -> pre (f, a))
      (fun '(f, a) b => dsp_rel f a b).
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
      | Some c => g (fun b => f pre (Some b)) (Some c)
      | None => f pre None \/
                g (fun b => f pre (Some b)) None
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
      | Some (b, d) => f (fun a => pre (a, d)) (Some b)
      | None => exists d, f (fun a => pre (a, d)) None
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
    mkDSPData
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
    mkDSPData
      (fun pre oc => match oc with
        | Some c => dsp_pt g (fun b => dsp_pt f pre (Some b)) (Some c)
        | None => dsp_pt f pre None /\
                  dsp_pt g (fun b => dsp_pt f pre (Some b)) None
      end)
      (fun a oc => match oc with
        | Some c => exists b, dsp_rel f a (Some b) /\ dsp_rel g b (Some c)
        | None => dsp_rel f a None \/
                  exists b, dsp_rel f a (Some b) /\ dsp_rel g b None
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
    mkDSPData
      (fun pre obc => match obc with
        | Some bd => dsp_pt f (fun a => pre (a, snd bd)) (Some (fst bd))
        | None => forall d, dsp_pt f (fun a => pre (a, d)) None
      end)
      (fun ad obc => match obc with
        | Some bd => dsp_rel f (fst ad) (Some (fst bd)) /\ snd ad = snd bd
        | None => dsp_rel f (fst ad) None
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
