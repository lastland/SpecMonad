(** * PureSPostArr: bundled predicate transformer arrow.

    [PureSPostArr A B] is a predicate transformer [(A -> Prop) -> B -> Prop]
    bundled with an [IsSP] condition guaranteeing that it equals [sp R]
    for some relation [R : SPArr A B].

    This bundling is necessary for the [first_fst] arrow law, which
    requires additivity (distributes over existentials).

    [SPostArr S A = stateArrT S (optionArrT PureSPostArr) unit A]
    unfolds to [PureSPostArr (unit * S) (option (A * S))],
    giving a predicate transformer [(unit * S -> Prop) -> option (A * S) -> Prop]. *)

From Coq Require Import Program.Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.

(* ================================================================= *)
(** ** Core definitions                                               *)
(* ================================================================= *)

Section PureSPostArr.

  (** A predicate transformer is in the image of [sp] iff it equals
      [sp R] for some relation [R]. *)
  Definition IsSP {A B} (f : (A -> Prop) -> B -> Prop) : Prop :=
    exists R : SPArr A B, forall pre b, f pre b <-> sp R pre b.

  Definition PureSPostArr (A B : Type) : Type :=
    { f : (A -> Prop) -> B -> Prop | IsSP f }.

  (** Smart constructor: wrap a relation with [sp]. *)
  Definition mkPSA {A B} (R : SPArr A B) : PureSPostArr A B :=
    exist _ (sp R) (ex_intro _ R (fun pre b => iff_refl _)).

  (* -------------------------------------------------------------- *)
  (** *** Arrow instance for [PureSPostArr]                           *)
  (* -------------------------------------------------------------- *)

  #[local]
  #[program] Definition arr_pure_PSA {A B} (f : A -> B) : PureSPostArr A B :=
    fun pre b => exists a, pre a /\ f a = b.
  Next Obligation.
    exists (fun a b => f a = b). intros pre b. reflexivity.
  Qed.

  #[local]
  #[program] Definition arr_comp_PSA {A B C}
    (f : PureSPostArr A B) (g : PureSPostArr B C) : PureSPostArr A C :=
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
  #[program] Definition arr_first_PSA {A B C}
    (f : PureSPostArr A B) : PureSPostArr (A * C)%type (B * C)%type :=
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
  Instance Arrow_PureSPostArr : Arrow PureSPostArr := {
    arr_pure := @arr_pure_PSA ;
    arr_comp := @arr_comp_PSA ;
    arr_first := @arr_first_PSA
  }.

End PureSPostArr.

(* ================================================================= *)
(** ** Option arrow transformer on [PureSPostArr]                     *)
(* ================================================================= *)

Section OptionPSArr.

  Definition optionPSArr := optionArrT PureSPostArr.

  #[local]
  #[program] Definition arr_pure_optPSA {A B}
    (f : A -> B) : optionPSArr A B :=
    fun pre ob => match ob with
      | Some b => exists a, pre a /\ f a = b
      | None => False
    end.
  Next Obligation.
    exists (fun a ob => match ob with Some b => f a = b | None => False end).
    intros pre [b|]; unfold sp; split; firstorder.
  Qed.

  #[local]
  #[program] Definition arr_comp_optPSA {A B C}
    (f : optionPSArr A B) (g : optionPSArr B C)
    : optionPSArr A C :=
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
  #[program] Definition arr_first_optPSA {A B C}
    (f : optionPSArr A B) : optionPSArr (A * C)%type (B * C)%type :=
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
  Instance Arrow_optionPSArr : Arrow optionPSArr := {
    arr_pure := @arr_pure_optPSA ;
    arr_comp := @arr_comp_optPSA ;
    arr_first := @arr_first_optPSA
  }.

End OptionPSArr.

(* ================================================================= *)
(** ** Composed type for specifications                               *)
(* ================================================================= *)

Section SPostArr.

  Variable S : Type.

  (** [SPostArr S A] is the arrow-based strongest postcondition
      specification type.  It composes [stateArrT] over [optionArrT]
      over [PureSPostArr], giving:

      [SPostArr S A = PureSPostArr (unit * S) (option (A * S))]

      The [proj1_sig] projection yields the predicate transformer
      [(unit * S -> Prop) -> option (A * S) -> Prop]. *)

  Definition SPostArr (A : Type) : Type :=
    stateArrT S optionPSArr unit A.
  (** Unfolds to [PureSPostArr (unit * S) (option (A * S))]. *)

End SPostArr.
