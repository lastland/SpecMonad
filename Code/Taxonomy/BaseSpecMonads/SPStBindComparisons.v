(** State bind formulas and monotone SP transformer comparisons. *)

From ExtLib Require Import Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  ASPMonad DSLPMonad DSPMonad ASLPMonad SPure SPPredicateTransformers.

(** Reading an [ASPSt] arrow as a monotone stateful predicate transformer
    identifies its bind with the angelic bind of [SPStMonotone]. *)
Section ASPStMonotoneBind.
  Context {S : Type}.

  Definition asSPStMon {A} (m : ASPSt S A) : SPStMonotone.SPStMon S A.
  Proof.
    exists (getASPSt m).
    intros pre pre' r Hpre Hm.
    eapply getASPSt_mono; eassumption.
  Defined.

  Definition bindASPSt_angelic_formula {A B}
      (m : ASPSt S A) (k : A -> ASPSt S B) : @SPSt S B :=
    fun pre r =>
      exists a s',
        getASPSt m pre (a, s') /\
        getASPSt (k a) (fun s => s = s') r.

  Lemma bindASPSt_angelic_formula_spec {A B}
      (m : ASPSt S A) (k : A -> ASPSt S B) pre (r : B * S) :
    getASPSt (bindASPSt m k) pre r <->
    bindASPSt_angelic_formula m k pre r.
  Proof. apply getASPSt_bind. Qed.

  Lemma bindASPSt_angelic {A B}
      (m : ASPSt S A) (k : A -> ASPSt S B) pre (r : B * S) :
    getASPSt (bindASPSt m k) pre r <->
    proj1_sig (SPStMonotone.AngelicMonotone.bind
      (asSPStMon m) (fun a => asSPStMon (k a))) pre r.
  Proof.
    rewrite getASPSt_bind. cbn. reflexivity.
  Qed.
End ASPStMonotoneBind.

Section ASPStExcMonotoneBind.
  Context {S : Type}.

  Definition successASPStExc {A} (m : ASPStExc S A)
    : SPStMonotone.SPStMon S A.
  Proof.
    exists (fun pre r => getASPStExc m pre (Some r)).
    intros pre pre' r Hpre Hm.
    eapply getASPStExc_mono; eassumption.
  Defined.

  Lemma bindASPStExc_success_angelic {A B}
      (m : ASPStExc S A) (k : A -> ASPStExc S B) pre (r : B * S) :
    getASPStExc (bindASPStExc m k) pre (Some r) <->
    proj1_sig (SPStMonotone.AngelicMonotone.bind
      (successASPStExc m) (fun a => successASPStExc (k a))) pre r.
  Proof.
    rewrite getASPStExc_bind. cbn.
    split.
    - intros [[a [s' [Hm Hk]]] | [Hnone _]].
      + exists a, s'. auto.
      + discriminate Hnone.
    - intros [a [s' [Hm Hk]]]. left. exists a, s'. auto.
  Qed.

  Lemma bindASPStExc_failure {A B}
      (m : ASPStExc S A) (k : A -> ASPStExc S B) pre :
    getASPStExc (bindASPStExc m k) pre None <->
    (exists a s', getASPStExc m pre (Some (a, s')) /\
                  getASPStExc (k a) (fun t => t = s') None)
    \/ getASPStExc m pre None.
  Proof.
    rewrite getASPStExc_bind. tauto.
  Qed.
End ASPStExcMonotoneBind.

(** The universal [DSLPSt] reading gives the demonic monotone bind. *)
Section DSLPStMonotoneBind.
  Context {S : Type}.

  Definition asDSLPStMon {A} (m : DSLPSt S A)
    : SPStMonotone.SPStMon S A.
  Proof.
    exists (getDSLPSt m).
    intros pre pre' r Hpre Hm.
    eapply getDSLPSt_mono; eassumption.
  Defined.

  Definition bindDSLPSt_demonic_formula {A B}
      (m : DSLPSt S A) (k : A -> DSLPSt S B) : @SPSt S B :=
    fun pre r =>
      forall a s',
        (forall prei, getDSLPSt (k a) prei r -> prei s') ->
        getDSLPSt m pre (a, s').

  Lemma dslpRelSt_test {A} (m : DSLPSt S A) s r :
    dslpRelSt m s r <->
    forall prei, getDSLPSt m prei r -> prei s.
  Proof.
    split.
    - intros Hrel prei Hget.
      apply (proj1 (getDSLPSt_rel S m prei r) Hget s Hrel).
    - intro H. apply (H (fun t => dslpRelSt m t r)).
      apply getDSLPSt_rel. intros t Hrel. exact Hrel.
  Qed.

  Lemma bindDSLPSt_demonic_formula_spec {A B}
      (m : DSLPSt S A) (k : A -> DSLPSt S B) pre (r : B * S) :
    getDSLPSt (bindDSLPSt m k) pre r <->
    bindDSLPSt_demonic_formula m k pre r.
  Proof.
    rewrite getDSLPSt_bind.
    unfold bindDSLPSt_demonic_formula.
    setoid_rewrite dslpRelSt_test. reflexivity.
  Qed.

  Lemma bindDSLPSt_demonic {A B}
      (m : DSLPSt S A) (k : A -> DSLPSt S B) pre (r : B * S) :
    getDSLPSt (bindDSLPSt m k) pre r <->
    proj1_sig (SPStMonotone.DemonicMonotone.bind
      (asDSLPStMon m) (fun a => asDSLPStMon (k a))) pre r.
  Proof.
    rewrite bindDSLPSt_demonic_formula_spec.
    reflexivity.
  Qed.
End DSLPStMonotoneBind.

Section RelationReadings.
  Context {S : Type}.

  Definition compositeStRel {A B}
      (R : S -> A * S -> Prop) (K : A -> S -> B * S -> Prop)
      (s : S) (r : B * S) : Prop :=
    exists a s', R s (a, s') /\ K a s' r.

  Definition angelicRelSPSt {A} (R : S -> A * S -> Prop)
    : SPStMonotone.SPStMon S A.
  Proof.
    exists (fun pre r => exists s, pre s /\ R s r).
    intros pre pre' r Hpre [s [Hp Hr]].
    exists s. split; [ apply Hpre, Hp | exact Hr ].
  Defined.

  Definition demonicRelSPSt {A} (R : S -> A * S -> Prop)
    : SPStMonotone.SPStMon S A.
  Proof.
    exists (fun pre r => forall s, R s r -> pre s).
    intros pre pre' r Hpre Hm s Hr.
    apply Hpre, Hm, Hr.
  Defined.

  Lemma angelicRelSPSt_bind {A B}
      (R : S -> A * S -> Prop) (K : A -> S -> B * S -> Prop)
      pre (r : B * S) :
    proj1_sig (SPStMonotone.AngelicMonotone.bind
      (angelicRelSPSt R) (fun a => angelicRelSPSt (K a))) pre r <->
    exists s, pre s /\ compositeStRel R K s r.
  Proof.
    cbn. unfold compositeStRel. split.
    - intros [a [s' [[s [Hp HR]] [t [Ht HK]]]]].
      subst t. exists s. split; [ exact Hp |].
      exists a, s'. auto.
    - intros [s [Hp [a [s' [HR HK]]]]].
      exists a, s'. split.
      + exists s. auto.
      + exists s'. auto.
  Qed.

  Lemma demonicRelSPSt_test {A} (R : S -> A * S -> Prop) s r :
    R s r <->
    forall prei, proj1_sig (demonicRelSPSt R) prei r -> prei s.
  Proof.
    cbn. split.
    - intros HR prei Hprei. apply Hprei, HR.
    - intro H. apply (H (fun t => R t r)). intros t HR. exact HR.
  Qed.

  Lemma demonicRelSPSt_bind {A B}
      (R : S -> A * S -> Prop) (K : A -> S -> B * S -> Prop)
      pre (r : B * S) :
    proj1_sig (SPStMonotone.DemonicMonotone.bind
      (demonicRelSPSt R) (fun a => demonicRelSPSt (K a))) pre r <->
    forall s, compositeStRel R K s r -> pre s.
  Proof.
    cbn. unfold compositeStRel. split.
    - intros H s [a [s' [HR HK]]].
      apply (H a s'); [| exact HR ].
      apply (proj1 (demonicRelSPSt_test (K a) s' r) HK).
    - intros H a s' Htest s HR.
      apply H. exists a, s'. split; [ exact HR |].
      apply (proj2 (demonicRelSPSt_test (K a) s' r) Htest).
  Qed.
End RelationReadings.

Section DSPStBind.
  Context {S : Type}.

  Definition angelicDSPSt {A} (m : DSPSt S A)
    : SPStMonotone.SPStMon S A :=
    angelicRelSPSt (fun s r => dspRel m (tt, s) r).

  Definition demonicDSPSt {A} (m : DSPSt S A)
    : SPStMonotone.SPStMon S A :=
    demonicRelSPSt (fun s r => dspRel m (tt, s) r).

  Definition bindDSPSt_relation {A B}
      (m : DSPSt S A) (k : A -> DSPSt S B) (s : S) (r : B * S) : Prop :=
    exists a s', dspRel m (tt, s) (a, s') /\ dspRel (k a) (tt, s') r.

  Definition bindDSPSt_formula {A B}
      (m : DSPSt S A) (k : A -> DSPSt S B) : @SPSt S B :=
    fun pre r =>
      (exists s, pre s /\ bindDSPSt_relation m k s r) /\
      (forall s, bindDSPSt_relation m k s r -> pre s).

  Lemma bindDSPSt_formula_spec {A B}
      (m : DSPSt S A) (k : A -> DSPSt S B) pre (r : B * S) :
    getDSPSt (bind m k) pre r <-> bindDSPSt_formula m k pre r.
  Proof.
    rewrite getDSPSt_rel. unfold bindDSPSt_formula.
    unfold bindDSPSt_relation.
    setoid_rewrite (relS_bind (arr := DSPArr) (rel := @dspRel) S m k tt).
    reflexivity.
  Qed.

  Lemma bindDSPSt_SPStMonotone {A B}
      (m : DSPSt S A) (k : A -> DSPSt S B) pre (r : B * S) :
    getDSPSt (bind m k) pre r <->
    proj1_sig (SPStMonotone.AngelicMonotone.bind
      (angelicDSPSt m) (fun a => angelicDSPSt (k a))) pre r /\
    proj1_sig (SPStMonotone.DemonicMonotone.bind
      (demonicDSPSt m) (fun a => demonicDSPSt (k a))) pre r.
  Proof.
    rewrite bindDSPSt_formula_spec.
    unfold bindDSPSt_formula, angelicDSPSt, demonicDSPSt.
    rewrite angelicRelSPSt_bind, demonicRelSPSt_bind.
    reflexivity.
  Qed.
End DSPStBind.

Section ASLPStBind.
  Context {S : Type}.

  Definition angelicASLPSt {A} (m : ASLPSt S A)
    : SPStMonotone.SPStMon S A :=
    angelicRelSPSt (fun s r => aslpRel m (tt, s) r).

  Definition demonicASLPSt {A} (m : ASLPSt S A)
    : SPStMonotone.SPStMon S A :=
    demonicRelSPSt (fun s r => aslpRel m (tt, s) r).

  Definition bindASLPSt_relation {A B}
      (m : ASLPSt S A) (k : A -> ASLPSt S B) (s : S) (r : B * S) : Prop :=
    exists a s', aslpRel m (tt, s) (a, s') /\ aslpRel (k a) (tt, s') r.

  Definition bindASLPSt_formula {A B}
      (m : ASLPSt S A) (k : A -> ASLPSt S B) : @SPSt S B :=
    fun pre r =>
      (exists s, pre s /\ bindASLPSt_relation m k s r) \/
      (forall s, bindASLPSt_relation m k s r -> pre s).

  Lemma bindASLPSt_formula_spec {A B}
      (m : ASLPSt S A) (k : A -> ASLPSt S B) pre (r : B * S) :
    getASLPSt (bind m k) pre r <-> bindASLPSt_formula m k pre r.
  Proof.
    rewrite getASLPSt_rel. unfold bindASLPSt_formula.
    unfold bindASLPSt_relation.
    setoid_rewrite (relS_bind (arr := ASLPArr) (rel := @aslpRel) S m k tt).
    reflexivity.
  Qed.

  Lemma bindASLPSt_SPStMonotone {A B}
      (m : ASLPSt S A) (k : A -> ASLPSt S B) pre (r : B * S) :
    getASLPSt (bind m k) pre r <->
    proj1_sig (SPStMonotone.AngelicMonotone.bind
      (angelicASLPSt m) (fun a => angelicASLPSt (k a))) pre r \/
    proj1_sig (SPStMonotone.DemonicMonotone.bind
      (demonicASLPSt m) (fun a => demonicASLPSt (k a))) pre r.
  Proof.
    rewrite bindASLPSt_formula_spec.
    unfold bindASLPSt_formula, angelicASLPSt, demonicASLPSt.
    rewrite angelicRelSPSt_bind, demonicRelSPSt_bind.
    reflexivity.
  Qed.
End ASLPStBind.
