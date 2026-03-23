From Coq Require Import
  FunctionalExtensionality
  PropExtensionality
  ProofIrrelevance.
From ExtLib Require Import
  Monad MonadLaws.
From ITree Require Import ITree Eq Props.Infinite.
From ITree.Extra.Dijkstra Require Import DelaySpecMonad PureITreeBasics.
From Paco Require Import paco.
From Incorrectness.Delay Require Import WP.

#[local] Open Scope delayspec_scope.

(** * Utility lemma: sigma-type equality from projection equality *)

Lemma sig_eq {A} {P : A -> Prop} (x y : sig P) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x, y; simpl; intros; subst.
  f_equal. apply proof_irrelevance.
Qed.

(** * Monad instances *)

#[global]
Instance Monad__DelayAWP : Monad DelayAWP :=
  {| ret := fun A => @ret_del A ;
     bind := fun A B => @bind_awp A B |}.

#[global]
Instance Monad__DelayDWP : Monad DelayDWP :=
  {| ret := fun A => @ret_del A ;
     bind := fun A B => @bind_dwp A B |}.

#[global]
Instance Monad__DelayAWLP : Monad DelayAWLP :=
  {| ret := fun A => @ret_del A ;
     bind := fun A B => @bind_awlp A B |}.

#[global]
Instance Monad__DelayDWLP : Monad DelayDWLP :=
  {| ret := fun A => @ret_del A ;
     bind := fun A B => @bind_dwlp A B |}.

(** * Left identity: bind (ret a) f = f a *)

Section BindOfReturn.

  Lemma bind_of_return_awp :
    forall (A B : Type) (a : A) (f : A -> DelayAWP B),
      bind_awp (ret_del a) f = f a.
  Proof.
    intros A B a f.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. split.
    - intros [a' [Hret Hfa']].
      apply eutt_inv_Ret in Hret. subst. exact Hfa'.
    - intro H. exists a. split; [reflexivity | exact H].
  Qed.

  Lemma bind_of_return_dwp :
    forall (A B : Type) (a : A) (f : A -> DelayDWP B),
      bind_dwp (ret_del a) f = f a.
  Proof.
    intros A B a f.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. split.
    - intro H. apply H. reflexivity.
    - intros H a' Hret. apply eutt_inv_Ret in Hret. subst. exact H.
  Qed.

  Lemma bind_of_return_awlp :
    forall (A B : Type) (a : A) (f : A -> DelayAWLP B),
      bind_awlp (ret_del a) f = f a.
  Proof.
    intros A B a f.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. split.
    - intros [[a' [Hret Hfa']] | Hinf].
      + apply eutt_inv_Ret in Hret. subst. exact Hfa'.
      + exfalso. pinversion Hinf.
    - intro H. left. exists a. split; [reflexivity | exact H].
  Qed.

  Lemma bind_of_return_dwlp :
    forall (A B : Type) (a : A) (f : A -> DelayDWLP B),
      bind_dwlp (ret_del a) f = f a.
  Proof.
    intros A B a f.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. split.
    - intros [H | Hinf].
      + apply H. reflexivity.
      + exfalso. pinversion Hinf.
    - intro H. left. intros a' Hret.
      apply eutt_inv_Ret in Hret. subst. exact H.
  Qed.

End BindOfReturn.

(** * Associativity: bind (bind m f) g = bind m (fun a => bind (f a) g) *)

Section BindAssociativity.

  Lemma bind_assoc_awp :
    forall (A B C : Type) (m : DelayAWP A) (f : A -> DelayAWP B) (g : B -> DelayAWP C),
      bind_awp (bind_awp m f) g = bind_awp m (fun a => bind_awp (f a) g).
  Proof.
    intros A B C m f g.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. simpl.
    destruct m as [mw Hm]; simpl.
    split; intro H;
    (eapply Hm; [|exact H]; simpl; intros t Ht;
     destruct Ht as [a [Ha Hfa]];
     exists a; split; [exact Ha|];
     destruct (f a) as [fw Hf]; simpl in *;
     eapply Hf; [|exact Hfa]; simpl; intros t' Ht';
     destruct Ht' as [b [Hb Hgb]];
     exists b; split; [exact Hb | exact Hgb]).
  Qed.

  Lemma bind_assoc_dwp :
    forall (A B C : Type) (m : DelayDWP A) (f : A -> DelayDWP B) (g : B -> DelayDWP C),
      bind_dwp (bind_dwp m f) g = bind_dwp m (fun a => bind_dwp (f a) g).
  Proof.
    intros A B C m f g.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. simpl.
    destruct m as [mw Hm]; simpl.
    split; intro H;
    (eapply Hm; [|exact H]; simpl; intros t Ht;
     intros a Hret; specialize (Ht a Hret);
     destruct (f a) as [fw Hf]; simpl in *;
     eapply Hf; [|exact Ht]; simpl; intros; auto).
  Qed.

  Lemma bind_assoc_awlp :
    forall (A B C : Type) (m : DelayAWLP A) (f : A -> DelayAWLP B) (g : B -> DelayAWLP C),
      bind_awlp (bind_awlp m f) g = bind_awlp m (fun a => bind_awlp (f a) g).
  Proof.
    intros A B C m f g.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. simpl.
    destruct m as [mw Hm]; simpl.
    split; intro H;
    (eapply Hm; [|exact H]; simpl; intros t Ht;
     destruct Ht as [[a [Ha Hfa]] | Hinf];
     [ left; exists a; split; [exact Ha|];
       destruct (f a) as [fw Hf]; simpl in *;
       eapply Hf; [|exact Hfa]; simpl; intros t' Ht';
       destruct Ht' as [[b [Hb Hgb]] | Hinf'];
       [left; exists b; split; [exact Hb | exact Hgb] | right; exact Hinf']
     | right; exact Hinf ]).
  Qed.

  Lemma bind_assoc_dwlp :
    forall (A B C : Type) (m : DelayDWLP A) (f : A -> DelayDWLP B) (g : B -> DelayDWLP C),
      bind_dwlp (bind_dwlp m f) g = bind_dwlp m (fun a => bind_dwlp (f a) g).
  Proof.
    intros A B C m f g.
    apply sig_eq. extensionality p.
    apply propositional_extensionality. simpl.
    destruct m as [mw Hm]; simpl.
    split; intro H;
    (eapply Hm; [|exact H]; simpl; intros t Ht;
     destruct Ht as [Ht | Hinf];
     [ left; intros a Hret; specialize (Ht a Hret);
       destruct (f a) as [fw Hf]; simpl in *;
       eapply Hf; [|exact Ht]; simpl; intros t' Ht';
       destruct Ht' as [Ht' | Hinf'];
       [left; intros; auto | right; exact Hinf']
     | right; exact Hinf ]).
  Qed.

End BindAssociativity.

(** * Counter-examples: return_of_bind fails for all four *)

Section ReturnOfBindCounter.

  (** A specification that evaluates any postcondition at [spin]. *)
  #[program] Definition spin_spec (A : Type) : DelaySpec A :=
    fun p => proj1_sig p ITree.spin.

  (** A postcondition that is universally true. *)
  #[program] Definition true_post (A : Type) : DelaySpecInput A :=
    fun _ => True.
  Next Obligation. intros t1 t2 _. tauto. Qed.

  (** A postcondition that is universally false. *)
  #[program] Definition false_post (A : Type) : DelaySpecInput A :=
    fun _ => False.
  Next Obligation. intros t1 t2 _. tauto. Qed.

  (** For AWP: [bind_awp m ret] at [true_post] requires a terminating [spin],
      but [m] at [true_post] holds trivially. *)
  Lemma return_of_bind_counter_awp :
    exists (A : Type) (m : DelayAWP A),
      bind_awp m (fun a => ret_del a) <> m.
  Proof.
    exists unit, (spin_spec unit).
    intro Heq.
    assert (Hm : proj1_sig (spin_spec unit) (true_post unit)).
    { simpl. exact I. }
    assert (Hbind : ~ proj1_sig (bind_awp (spin_spec unit) (fun a => ret_del a)) (true_post unit)).
    { simpl. intros [a [Hret _]].
      eapply not_ret_eutt_spin; eauto. }
    apply Hbind. change (proj1_sig (spin_spec unit) (true_post unit)) in Hm.
    rewrite <- Heq in Hm. exact Hm.
  Qed.

  (** For DWP: [bind_dwp m ret] at [false_post] holds vacuously,
      but [m] at [false_post] is [False]. *)
  Lemma return_of_bind_counter_dwp :
    exists (A : Type) (m : DelayDWP A),
      bind_dwp m (fun a => ret_del a) <> m.
  Proof.
    exists unit, (spin_spec unit).
    intro Heq.
    assert (Hbind : proj1_sig (bind_dwp (spin_spec unit) (fun a => ret_del a)) (false_post unit)).
    { simpl. intros a Hret.
      exfalso. eapply not_ret_eutt_spin; eauto. }
    assert (Hm : ~ proj1_sig (spin_spec unit) (false_post unit)).
    { simpl. auto. }
    apply Hm. rewrite <- Heq. exact Hbind.
  Qed.

  (** For AWLP: [bind_awlp m ret] at [false_post] holds via divergence,
      but [m] at [false_post] is [False]. *)
  Lemma return_of_bind_counter_awlp :
    exists (A : Type) (m : DelayAWLP A),
      bind_awlp m (fun a => ret_del a) <> m.
  Proof.
    exists unit, (spin_spec unit).
    intro Heq.
    assert (Hbind : proj1_sig (bind_awlp (spin_spec unit) (fun a => ret_del a)) (false_post unit)).
    { simpl. right. apply spin_infinite. }
    assert (Hm : ~ proj1_sig (spin_spec unit) (false_post unit)).
    { simpl. auto. }
    apply Hm. rewrite <- Heq. exact Hbind.
  Qed.

  (** For DWLP: [bind_dwlp m ret] at [false_post] holds via divergence,
      but [m] at [false_post] is [False]. *)
  Lemma return_of_bind_counter_dwlp :
    exists (A : Type) (m : DelayDWLP A),
      bind_dwlp m (fun a => ret_del a) <> m.
  Proof.
    exists unit, (spin_spec unit).
    intro Heq.
    assert (Hbind : proj1_sig (bind_dwlp (spin_spec unit) (fun a => ret_del a)) (false_post unit)).
    { simpl. right. apply spin_infinite. }
    assert (Hm : ~ proj1_sig (spin_spec unit) (false_post unit)).
    { simpl. auto. }
    apply Hm. rewrite <- Heq. exact Hbind.
  Qed.

End ReturnOfBindCounter.
