(** * Original IsASP-based PureASPostArr (deprecated).

    This file preserves the original definition of [PureASPostArr]
    using a Prop-level existential ([IsASP]).  The main codebase now
    uses [SPRecord] instead, which bundles the PT with its relation
    directly, allowing shared infrastructure with [PureDSPostArr].

    This file is NOT imported by anything — it exists only as a
    reference. *)

From Coq Require Import Program.Tactics.
From Incorrectness.Classes Require Import Arrow OptionArrowT StateArrowT.

Section PureASPostArr.

  Definition IsASP {A B} (f : (A -> Prop) -> B -> Prop) : Prop :=
    exists R : SPArr A B, forall pre b, f pre b <-> sp R pre b.

  Definition PureASPostArr (A B : Type) : Type :=
    { f : (A -> Prop) -> B -> Prop | IsASP f }.

  #[program] Definition mkASP {A B} (R : SPArr A B) : PureASPostArr A B :=
    sp R.
  Next Obligation.
    exists R. reflexivity.
  Qed.

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
