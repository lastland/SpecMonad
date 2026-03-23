From Coq Require Import
  FunctionalExtensionality
  PropExtensionality.
From ExtLib Require Import
  Monad MonadLaws
  StateMonad OptionMonad
  MonadState MonadExc.
From ITree Require Import ITree Eq.
From ITree.Extra.Dijkstra Require Import DelaySpecMonad.
From Incorrectness.Delay Require Import WP.

(** * Monad and state laws for [prog]

    We prove [bind_of_return], [bind_associativity], [put_get], [put_put],
    and [get_get].  We give counter-examples for [return_of_bind], [get_put],
    and [get_ignore]. *)

Section ProgLaws.

  Variable S : Type.

  (** ** Positive monad laws *)

  Lemma bind_of_return_prog (s0 : S) :
    forall (A B : Type) (a : A) (f : A -> prog S B),
      bind (ret a) f = f a.
  Proof.
    intros A B a f.
    apply functional_extensionality; intro b.
    apply propositional_extensionality; split.
    - intros [a' [Ha' Hk]].
      cbn in Ha'.
      specialize (Ha' s0). apply eutt_inv_Ret in Ha'.
      assert (a' = a) by congruence. subst. exact Hk.
    - intro Hfa. exists a. split; [|exact Hfa].
      cbn. intro s. reflexivity.
  Qed.

  Lemma bind_assoc_prog :
    forall (A B C : Type) (aM : prog S A) (f : A -> prog S B) (g : B -> prog S C),
      bind (bind aM f) g = bind aM (fun a => bind (f a) g).
  Proof.
    intros A B C aM f g.
    apply functional_extensionality; intro c.
    apply propositional_extensionality.
    simpl. split.
    - intros [b [[a [HaM Hfa]] Hgb]].
      exists a. split; [exact HaM|]. exists b. split; [exact Hfa|exact Hgb].
    - intros [a [HaM [b [Hfa Hgb]]]].
      exists b. split; [exists a; split; [exact HaM|exact Hfa]|exact Hgb].
  Qed.

  (** ** Positive state laws *)

  Lemma put_get_prog :
    forall (x : S),
      bind (put x) (fun _ => get) = bind (put x) (fun _ => ret x).
  Proof.
    intro x.
    apply functional_extensionality; intro p.
    apply propositional_extensionality; split.
    - intros [u [Hput Hget]].
      exists u. split; [exact Hput|].
      cbn in Hput. cbn in Hget. cbn.
      destruct p as [fp]. simpl in *.
      intro s.
      pose proof (Hput s) as Hps. apply eutt_inv_Ret in Hps.
      assert (s = x) by congruence. subst.
      exact (Hget x).
    - intros [u [Hput Hret]].
      exists u. split; [exact Hput|].
      cbn in Hput. cbn in Hret. cbn.
      destruct p as [fp]. simpl in *.
      intro s.
      pose proof (Hput s) as Hps. apply eutt_inv_Ret in Hps.
      assert (s = x) by congruence. subst.
      exact (Hret x).
  Qed.

  Lemma put_put_prog :
    forall (A : Type) (x y : S) (f : unit -> prog S A),
      bind (put x) (fun _ => bind (put y) f) = bind (put y) f.
  Proof.
    intros A x y f.
    apply functional_extensionality; intro p.
    apply propositional_extensionality; split.
    - intros [u1 [_ [u2 [Hput2 Hf]]]].
      exists u2. split; [exact Hput2|exact Hf].
    - intros [u2 [Hput2 Hf]].
      exists tt. split.
      + cbn. cbn in Hput2. intro s.
        pose proof (Hput2 s) as Hs. apply eutt_inv_Ret in Hs.
        pose proof (Hput2 x) as Hx. apply eutt_inv_Ret in Hx.
        assert (s = y) by congruence.
        assert (x = y) by congruence.
        subst. reflexivity.
      + exists u2. split; [exact Hput2|exact Hf].
  Qed.

  Lemma get_get_prog :
    forall (A : Type) (f : S -> S -> prog S A),
      bind get (fun s => bind get (f s)) = bind get (fun s => f s s).
  Proof.
    intros A f.
    apply functional_extensionality; intro p.
    apply propositional_extensionality; split.
    - intros [s [Hget1 [s' [Hget2 Hf]]]].
      exists s. split; [exact Hget1|].
      cbn in Hget2.
      assert (s' = s).
      { pose proof (Hget2 s) as H. apply eutt_inv_Ret in H. congruence. }
      subst. exact Hf.
    - intros [s [Hget Hf]].
      exists s. split; [exact Hget|].
      exists s. split; [exact Hget|exact Hf].
  Qed.

End ProgLaws.

(** ** Counter-examples *)

Section Counterexamples.

  (** [return_of_bind] fails for any inhabited state. *)
  Lemma return_of_bind_counter (S : Type) (s0 : S) :
    exists (aM : prog S unit), bind aM ret <> aM.
  Proof.
    exists (fun _ => True).
    intro Heq.
    set (w := @mkStateT S (optionT Delay) unit
                (fun _ : S => @mkOptionT Delay (unit * S)
                   ((Ret None) : itree void1 (option (unit * S))))).
    assert (Hrhs : (fun _ : stateT S (optionT Delay) unit => True) w) by exact I.
    assert (Hlhs : ~ @bind (prog S) _ unit unit (fun _ => True) ret w).
    { intros [a [_ Ha]].
      cbn in Ha. specialize (Ha s0).
      apply eutt_inv_Ret in Ha. discriminate. }
    apply Hlhs. rewrite Heq. exact Hrhs.
  Qed.

  (** [get_put] fails when S has more than one element. *)
  Lemma get_put_counter :
    @bind (prog bool) _ _ _ (@get _ (prog bool) _) (@put _ (prog bool) _)
    <> @ret (prog bool) _ _ tt.
  Proof.
    intro Heq.
    set (w := @mkStateT bool (optionT Delay) unit
                (fun s : bool => @mkOptionT Delay (unit * bool)
                   (Ret (Some (tt, s))))).
    assert (Hrhs : (@ret (prog bool) _ _ tt) w).
    { cbn. intro s. reflexivity. }
    assert (Hlhs : ~ (@bind (prog bool) _ _ _ (@get _ (prog bool) _) (@put _ (prog bool) _)) w).
    { intros [s [Hget _]].
      cbn in Hget.
      pose proof (Hget true) as Ht. apply eutt_inv_Ret in Ht.
      pose proof (Hget false) as Hf. apply eutt_inv_Ret in Hf.
      congruence. }
    apply Hlhs. rewrite Heq. exact Hrhs.
  Qed.

  (** [get_ignore] fails when S has more than one element. *)
  Lemma get_ignore_counter :
    @bind (prog bool) _ _ _ (@get _ (prog bool) _) (fun _ => @ret (prog bool) _ _ tt)
    <> @ret (prog bool) _ _ tt.
  Proof.
    intro Heq.
    set (w := @mkStateT bool (optionT Delay) unit
                (fun s : bool => @mkOptionT Delay (unit * bool)
                   (Ret (Some (tt, s))))).
    assert (Hrhs : (@ret (prog bool) _ _ tt) w).
    { cbn. intro s. reflexivity. }
    assert (Hlhs : ~ (@bind (prog bool) _ _ _ (@get _ (prog bool) _)
                        (fun _ => @ret (prog bool) _ _ tt)) w).
    { intros [s [Hget _]].
      cbn in Hget.
      pose proof (Hget true) as Ht. apply eutt_inv_Ret in Ht.
      pose proof (Hget false) as Hf. apply eutt_inv_Ret in Hf.
      congruence. }
    apply Hlhs. rewrite Heq. exact Hrhs.
  Qed.

End Counterexamples.
