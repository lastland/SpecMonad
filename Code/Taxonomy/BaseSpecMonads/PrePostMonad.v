(** * [PrePost]: the pre/postcondition specification monad

        [PrePost A := Prop * (A -> Prop)]

        [ret a    := (True, fun x => x = a)]
        [bind m k := ( fst m /\ (forall a, snd m a -> fst (k a))
                     , fun b => exists a, snd m a /\ snd (k a) b )]

    A specification is a precondition together with the set of results it
    admits.  Sequencing requires [m]'s precondition and requires every result
    admitted by [m] to satisfy the continuation's precondition.  The composite
    postcondition admits results connected through an intermediate value.

    This is DM4all's [PPSpecMonad] ([PP_ret] / [PP_bind] in
    [sprop/SpecificationMonads.v]), transcribed from [SProp] to [Prop].
    Here [Eq1] compares both components by pointwise logical equivalence;
    the monad laws do not require equality of predicate functions.

    The unary carrier is [PPM.PrePost].  Its binary counterpart is
    [PrePostArr] in [Arrows/PrePostArr.v], with a post-relation that also
    retains the input.  Qualify [PPM.pre] and [PPM.post] when importing their
    short names would shadow local binders. *)

From ITree Require Import Basics.Monad.

Module PPM.

  Definition PrePost (A : Type) : Type := (Prop * (A -> Prop))%type.

  Definition pre  {A} (m : PrePost A) : Prop        := fst m.
  Definition post {A} (m : PrePost A) : A -> Prop   := snd m.

  Definition retPP {A} (a : A) : PrePost A :=
    (True, fun x => x = a).

  Definition bindPP {A B} (m : PrePost A) (k : A -> PrePost B) : PrePost B :=
    ( pre m /\ (forall a, post m a -> pre (k a))
    , fun b => exists a, post m a /\ post (k a) b ).

  #[global]
  Instance Monad_PrePost : Monad PrePost := {
    ret  := @retPP ;
    bind := @bindPP
  }.

  (** Pointwise equivalence on both components. *)
  #[global]
  Instance Eq1_PrePost : Eq1 PrePost :=
    fun A m1 m2 => (pre m1 <-> pre m2) /\ (forall a, post m1 a <-> post m2 a).

End PPM.

(* ================================================================= *)
(** ** Monad laws                                                    *)
(* ================================================================= *)

Module PPMFacts.
  Import PPM.

  #[global]
  Instance Eq1Equivalence_PrePost : @Eq1Equivalence PrePost _ Eq1_PrePost.
  Proof.
    constructor; repeat intro; unfold eq1, Eq1_PrePost in *.
    - split; [ reflexivity | intro a; reflexivity ].
    - destruct H as [Hp Hq]. split; [ symmetry; exact Hp |].
      intro a. symmetry. exact (Hq a).
    - destruct H as [Hp1 Hq1]. destruct H0 as [Hp2 Hq2].
      split; [ etransitivity; [ exact Hp1 | exact Hp2 ] |].
      intro a. etransitivity; [ exact (Hq1 a) | exact (Hq2 a) ].
  Qed.

  #[global]
  Instance MonadLawsE_PrePost : @MonadLawsE PrePost Eq1_PrePost _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. cbn. unfold bindPP, retPP, pre, post; cbn. split.
      + split.
        * intros [_ H]. exact (H x eq_refl).
        * intro H. split; [ exact I |]. intros a Heq. subst a. exact H.
      + intro b. split.
        * intros [a [Heq H]]. subst a. exact H.
        * intro H. exists x. split; [ reflexivity | exact H ].
    - (* bind_ret_r *)
      intros A m. cbn. unfold bindPP, retPP, pre, post; cbn. split.
      + split.
        * intros [H _]. exact H.
        * intro H. split; [ exact H | intros a _; exact I ].
      + intro a. split.
        * intros [a' [H Heq]]. subst a'. exact H.
        * intro H. exists a. split; [ exact H | reflexivity ].
    - (* bind_bind *)
      intros A B C m f g. cbn. unfold bindPP, pre, post; cbn. split.
      + split.
        * intros [[Hm Hf] Hg]. split; [ exact Hm |].
          intros a Ha. split; [ exact (Hf a Ha) |].
          intros b Hb. apply Hg. exists a. split; [ exact Ha | exact Hb ].
        * intros [Hm H]. split.
          -- split; [ exact Hm | intros a Ha; exact (proj1 (H a Ha)) ].
          -- intros b [a [Ha Hb]]. exact (proj2 (H a Ha) b Hb).
      + intro c. split.
        * intros [b [[a [Ha Hb]] Hc]]. exists a. split; [ exact Ha |].
          exists b. split; [ exact Hb | exact Hc ].
        * intros [a [Ha [b [Hb Hc]]]]. exists b. split; [| exact Hc ].
          exists a. split; [ exact Ha | exact Hb ].
    - (* Proper_bind *)
      intros A B m1 m2 Hm k1 k2 Hk. cbn. unfold bindPP, pre, post; cbn.
      unfold eq1, Eq1_PrePost, pre, post in Hm.
      destruct Hm as [Hmp Hmq]. split.
      + split.
        * intros [H1 H2]. split; [ apply Hmp; exact H1 |].
          intros a Ha. apply (proj1 (proj1 (Hk a))).
          apply H2. apply Hmq. exact Ha.
        * intros [H1 H2]. split; [ apply Hmp; exact H1 |].
          intros a Ha. apply (proj2 (proj1 (Hk a))).
          apply H2. apply Hmq. exact Ha.
      + intro b. split.
        * intros [a [Ha Hb]]. exists a. split.
          -- apply Hmq. exact Ha.
          -- apply (proj2 (Hk a) b). exact Hb.
        * intros [a [Ha Hb]]. exists a. split.
          -- apply Hmq. exact Ha.
          -- apply (proj2 (Hk a) b). exact Hb.
  Qed.

End PPMFacts.
