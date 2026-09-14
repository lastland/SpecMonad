From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad DSPMonad.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The pure variant                                              *)
(* ================================================================= *)

(** Dual to [PureDSPMonad] in [DSPMonad.v]: at [SPPure] the ASLP carrier
    condition [Terminating /\ Disjunctive] is EQUIVALENT to the DSLP one
    ([MSingleton]).  [Terminating] alone already forces [MSingleton]
    ([terminating_to_msingleton]), and [MSingleton] gives both connectives
    back ([msingleton_to_meet], [msingleton_to_disjunctive]).

    So [ASLPSP] is [DSLPSP] under a different presentation of the same subset
    of [SPPure], and its monad structure is transported rather than rebuilt. *)

Section PureASLPMonad.

  Definition TerminatingDisjunctive {A} (w : SPPure A) : Prop :=
    Terminating w /\ Disjunctive w.

  Definition ASLPSP (A : Type) : Type := { w : SPPure A | TerminatingDisjunctive w }.

  Definition getASLP {A} (w : ASLPSP A) : SPPure A := proj1_sig w.

  Theorem term_disj_iff_msingleton {A} (w : SPPure A) :
    TerminatingDisjunctive w <-> MSingleton w.
  Proof.
    split.
    - intros [HT _]. exact (terminating_to_msingleton w HT).
    - intro H. split;
        [ exact (proj1 (msingleton_to_meet w H))
        | exact (msingleton_to_disjunctive w H) ].
  Qed.

  Definition dslp_to_aslp {A} (w : DSLPSP A) : ASLPSP A :=
    exist _ (getDSLP w) (proj2 (term_disj_iff_msingleton (getDSLP w)) (proj2_sig w)).

  Definition aslp_to_dslp {A} (w : ASLPSP A) : DSLPSP A :=
    exist _ (getASLP w) (proj1 (term_disj_iff_msingleton (getASLP w)) (proj2_sig w)).

  Lemma getASLP_dslp_to_aslp {A} (w : DSLPSP A) p a :
    getASLP (dslp_to_aslp w) p a <-> getDSLP w p a.
  Proof. split; intro H; exact H. Qed.

  Lemma getDSLP_aslp_to_dslp {A} (w : ASLPSP A) p a :
    getDSLP (aslp_to_dslp w) p a <-> getASLP w p a.
  Proof. split; intro H; exact H. Qed.

  Definition retASLP {A} (v : A) : ASLPSP A := dslp_to_aslp (retDSLP v).

  Definition bindASLP {A B} (m : ASLPSP A) (k : A -> ASLPSP B) : ASLPSP B :=
    dslp_to_aslp (bindDSLP (aslp_to_dslp m) (fun a => aslp_to_dslp (k a))).

  #[global] Instance Monad_ASLPSP : Monad ASLPSP :=
    {| ret := fun _ => retASLP ;
      bind := fun _ _ => bindASLP |}.

  #[global] Instance Eq1_ASLPSP : Eq1 ASLPSP :=
    fun A m n => forall p a, getASLP m p a <-> getASLP n p a.

  #[global] Instance Eq1Equivalence_ASLPSP
    : @Eq1Equivalence ASLPSP _ Eq1_ASLPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a); specialize (H2 p a). tauto.
  Qed.

  #[global] Instance MonadLawsE_ASLPSP : @MonadLawsE ASLPSP Eq1_ASLPSP _.
  Proof.
    destruct (@MonadLawsE_DSLPSP) as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => aslp_to_dslp (f a)) x).
    - intros A x. exact (Lbrr A (aslp_to_dslp x)).
    - intros A B C x f g.
      exact (Lbb A B C (aslp_to_dslp x) (fun a => aslp_to_dslp (f a))
               (fun b => aslp_to_dslp (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (aslp_to_dslp x) (aslp_to_dslp y) Hxy
               (fun a => aslp_to_dslp (f a)) (fun a => aslp_to_dslp (g a)) Hfg).
  Qed.

  Definition ordASLPSP {A} (m1 m2 : ASLPSP A) : Prop :=
    forall p a, getASLP m1 p a -> getASLP m2 p a.
  Definition ordASLPSPAt {A} (pre : Prop) (m1 m2 : ASLPSP A) : Prop :=
    forall a, getASLP m1 pre a -> getASLP m2 pre a.

  Lemma ordASLPSP_refl A (m : ASLPSP A) : ordASLPSP m m.
  Proof. intros p a H. exact H. Qed.
  Lemma bindASLP_mono A B (m n : ASLPSP A) (f g : A -> ASLPSP B) :
    ordASLPSP m n -> (forall a, ordASLPSP (f a) (g a)) ->
    ordASLPSP (bindASLP m f) (bindASLP n g).
  Proof.
    intros Hmn Hfg p b Hb a. apply Hfg.
    apply (getMSP_mono (aslp_to_dslp (f a)) (getASLP m p a) (getASLP n p a) b).
    - exact (Hmn p a).
    - exact (Hb a).
  Qed.
End PureASLPMonad.

Local Lemma aslp_recov_gen (S O : Type) (R : S -> O -> Prop) (s : S) (r : O) :
  (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
   /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s))) <-> R s r.
Proof.
  split.
  - intros [Hne [[t [Heq Ht]] | Hall]]; [ subst t; exact Ht |].
    apply NNPP. intro Hns. apply Hne. right.
    intros t Ht. rewrite (Hall t Ht) in Ht. exact (Hns Ht).
  - intro Hs. split.
    + intros [[t [Hf _]] | Hall]; [ destruct Hf | exact (Hall s Hs) ].
    + left. exists s. split; [ reflexivity | exact Hs ].
Qed.
Local Lemma aslp_cong_gen (S O : Type) (R R' : S -> O -> Prop)
  (H : forall s r, R s r <-> R' s r) : forall (pre : S -> Prop) (r : O),
  ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s)) <->
  ((exists s, pre s /\ R' s r) \/ (forall s, R' s r -> pre s)).
Proof.
  intros pre r. split.
  - intros [[s [Hp Hs]] | Hall].
    + left. exists s. split; [ exact Hp | exact (proj1 (H s r) Hs) ].
    + right. intros s' Hs'. exact (Hall s' (proj2 (H s' r) Hs')).
  - intros [[s [Hp Hs]] | Hall].
    + left. exists s. split; [ exact Hp | exact (proj2 (H s r) Hs) ].
    + right. intros s' Hs'. exact (Hall s' (proj1 (H s' r) Hs')).
Qed.

Section ProgASLPMonad.
  Variable S : Type.

  Definition TerminatingPositivelyJoinPreserving {A} (w : SPStExc A) : Prop :=
    TerminatingProg S w /\ DisjunctiveProg S w.

  Definition ASLPStExc (A : Type) : Type :=
    { w : SPStExc A | TerminatingPositivelyJoinPreserving w }.

  Definition getASLPStExc {A} (w : ASLPStExc A) : SPStExc A := proj1_sig w.

  Lemma aslp_recov {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
    (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
     /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
    <-> R s r.
  Proof. exact (aslp_recov_gen S (option (A * S)) R s r). Qed.

  Lemma aslp_wf {A} (R : S -> option (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : option (A * S)),
      ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\
              (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
               /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s))))
           \/ (forall s,
                 (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
                  /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
                 -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj2 (aslp_recov R s r) Hs) ].
      + right. intros s H. exact (Hall s (proj1 (aslp_recov R s r) H)).
    - intros [[s [Hp H]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj1 (aslp_recov R s r) H) ].
      + right. intros s Hs. exact (Hall s (proj2 (aslp_recov R s r) Hs)).
  Qed.

  Lemma aslp_cong {A} (R R' : S -> option (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : option (A * S)),
      ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\ R' s r) \/ (forall s, R' s r -> pre s)).
  Proof. exact (aslp_cong_gen S (option (A * S)) R R' H). Qed.

  Lemma aslp_rec_ext {A} (w1 w2 : @SPStExc S A)
    (H : forall pre r, w1 pre r <-> w2 pre r) :
    forall (s : S) (r : option (A * S)),
      (~ w1 (fun _ => False) r /\ w1 (fun t => t = s) r)
      <-> (~ w2 (fun _ => False) r /\ w2 (fun t => t = s) r).
  Proof.
    intros s r. split.
    - intros [H1 H2]. split;
        [ intro Hc; exact (H1 (proj2 (H _ r) Hc)) | exact (proj1 (H _ r) H2) ].
    - intros [H1 H2]. split;
        [ intro Hc; exact (H1 (proj1 (H _ r) Hc)) | exact (proj2 (H _ r) H2) ].
  Qed.

  (** Dual of [dsp_carrier]: the carrier's well-formedness condition is
      equivalent to saying that [w] is the ASLP reading of its recovered
      relation. The proofs use this representation. *)
  Lemma aslp_carrier {A} (w : SPStExc A) :
    TerminatingPositivelyJoinPreserving w <->
      (forall (pre : S -> Prop) (r : option (A * S)), w pre r <->
      ((exists s, pre s /\ (~ w (fun _ => False) r /\ w (fun t => t = s) r)) \/
         (forall s, (~ w (fun _ => False) r /\ w (fun t => t = s) r) -> pre s))).
  Proof.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    split.
    - intros [HT HD] pre r.
      (* the join of the two-element family [{P, Q}] is [Q] when [P <= Q] *)
      assert (Hmono : forall (P Q : S -> Prop) y,
                 (forall s, P s -> Q s) -> w P y -> w Q y).
      { intros P Q y Hpq Hw.
        assert (Heq : Q = (fun s => exists b : bool, (if b then P else Q) s)).
        { apply Hext. intro s. split.
          - intro Hs. exists false. exact Hs.
          - intros [b Hb]. destruct b; [ exact (Hpq s Hb) | exact Hb ]. }
        rewrite Heq.
        apply (HD bool (inhabits true) (fun b => if b then P else Q) y).
        exists true. exact Hw. }
      destruct (classic (w (fun _ => False) r)) as [Hbot | Hnbot].
      + split.
        * intros _. right. intros s [Hn _]. destruct (Hn Hbot).
        * intros _. apply (Hmono (fun _ => False) pre r); [ intros s [] | exact Hbot ].
      + (* [S] is inhabited, else top and bottom coincide *)
        assert (Hinh : exists s0 : S, True).
        { apply NNPP. intro Hno. apply Hnbot.
          assert (Heq : (fun _ : S => True) = (fun _ : S => False)).
          { apply Hext. intro s. split;
              [ intros _; exact (Hno (ex_intro _ s I)) | intros [] ]. }
          pose proof (HT r) as Htop. rewrite Heq in Htop. exact Htop. }
        destruct Hinh as [sinh _].
        (* top-preservation makes some singleton already force [r] *)
        assert (Hex : exists s, w (fun t => t = s) r).
        { assert (Heq : (fun _ : S => True) = (fun s => exists s0 : S, s = s0)).
          { apply Hext. intro s. split;
              [ intros _; exists s; reflexivity | intros _; exact I ]. }
          pose proof (HT r) as Htop. rewrite Heq in Htop.
          exact (proj1 (HD S (inhabits sinh) (fun s0 s => s = s0) r) Htop). }
        (* the join of all preconditions that FAIL to force [r] *)
        pose (bad := fun s => exists i : { q : S -> Prop | ~ w q r }, proj1_sig i s).
        assert (Hbad : ~ w bad r).
        { unfold bad. intro Hc.
          destruct (proj1 (HD { q : S -> Prop | ~ w q r }
                             (inhabits (exist (fun q => ~ w q r) (fun _ : S => False) Hnbot))
                             (fun i s => proj1_sig i s) r) Hc) as [i Hi].
          exact (proj2_sig i Hi). }
        assert (Hub : forall q, ~ w q r -> forall s, q s -> bad s).
        { intros q Hq s Hs. unfold bad.
          exists (exist (fun q0 => ~ w q0 r) q Hq). exact Hs. }
        assert (Hrec : forall s, (~ w (fun _ => False) r /\ w (fun t => t = s) r)
                                 <-> ~ bad s).
        { intro s. split.
          - intros [_ Hw] Hb. unfold bad in Hb. destruct Hb as [i Hi].
            apply (proj2_sig i).
            apply (Hmono (fun t => t = s) (proj1_sig i) r);
              [ intros t Ht; rewrite Ht; exact Hi | exact Hw ].
          - intro Hnb. split; [ exact Hnbot |].
            apply NNPP. intro Hnw.
            exact (Hnb (Hub (fun t => t = s) Hnw s eq_refl)). }
        assert (Hmain : w pre r <-> exists s, pre s /\ ~ bad s).
        { split.
          - intro Hw. apply NNPP. intro Hno. apply Hbad.
            apply (Hmono pre bad r); [| exact Hw ].
            intros s Hs. apply NNPP. intro Hnb.
            exact (Hno (ex_intro _ s (conj Hs Hnb))).
          - intros [s [Hs Hnb]]. apply NNPP. intro Hnw.
            exact (Hnb (Hub pre Hnw s Hs)). }
        split.
        * intro Hw. left. destruct (proj1 Hmain Hw) as [s [Hs Hnb]].
          exists s. split; [ exact Hs | exact (proj2 (Hrec s) Hnb) ].
        * intros [[s [Hs Hr']] | Hall].
          -- apply Hmain. exists s.
             split; [ exact Hs | exact (proj1 (Hrec s) Hr') ].
          -- destruct Hex as [s0 Hs0]. apply Hmain. exists s0.
             split; [ exact (Hall s0 (conj Hnbot Hs0))
                    | exact (proj1 (Hrec s0) (conj Hnbot Hs0)) ].
    - intro HD. split.
      + intro r. apply (HD (fun _ => True) r). right. intros s _. exact I.
      + intros J Hi0 p r. destruct Hi0 as [i0]. split.
        * intro Hw. destruct (proj1 (HD (fun s => exists i : J, p i s) r) Hw)
            as [[s [[i Hpi] Hrec]] | Hall].
          -- exists i. apply (HD (fun s0 => p i s0) r). left.
             exists s. split; [ exact Hpi | exact Hrec ].
          -- destruct (classic (exists s, ~ w (fun _ => False) r
                                          /\ w (fun t => t = s) r)) as [[s0 Hs0] | Hno].
             ++ destruct (Hall s0 Hs0) as [i Hpi].
                exists i. apply (HD (fun s0' => p i s0') r). left.
                exists s0. split; [ exact Hpi | exact Hs0 ].
             ++ exists i0. apply (HD (fun s0 => p i0 s0) r). right.
                intros s Hrec. exfalso. exact (Hno (ex_intro _ s Hrec)).
        * intros [i Hw]. apply (HD (fun s => exists j : J, p j s) r).
          destruct (proj1 (HD (fun s0 => p i s0) r) Hw) as [[s [Hpi Hrec]] | Hall].
          -- left. exists s. split; [ exists i; exact Hpi | exact Hrec ].
          -- right. intros s Hrec. exists i. exact (Hall s Hrec).
  Qed.

  (** Everything of ASLP shape inhabits the carrier — this discharges each
      [#[program]] obligation below. *)
  Lemma aslp_shape_wf {A} (R : S -> option (A * S) -> Prop) :
    TerminatingPositivelyJoinPreserving
      (fun pre r => (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s)).
  Proof.
    split.
    - intros r. right. intros s _. exact I.
    - intros I [i0] p r. split.
      + intros [[s [[i Hi] Hs]] | Hall].
        * exists i. left. exists s. split; [ exact Hi | exact Hs ].
        * destruct (classic (exists s, R s r)) as [[s0 Hs0] | Hno].
          -- destruct (Hall s0 Hs0) as [i Hi]. exists i. left.
             exists s0. split; [ exact Hi | exact Hs0 ].
          -- exists i0. right. intros s Hs. exfalso.
             exact (Hno (ex_intro _ s Hs)).
      + intros [i [[s [Hp Hs]] | Hall]].
        * left. exists s. split; [ exists i; exact Hp | exact Hs ].
        * right. intros s Hs. exists i. exact (Hall s Hs).
  Qed.

  (** ... and every carrier element is the ASLP of its recovered relation. *)
  Lemma getProgASLP_carrier {A} (w : ASLPStExc A)
    (pre : S -> Prop) (r : option (A * S)) :
    getASLPStExc w pre r <->
      ((exists s, pre s /\ (~ getASLPStExc w (fun _ => False) r
                            /\ getASLPStExc w (fun t => t = s) r)) \/
         (forall s, (~ getASLPStExc w (fun _ => False) r
                     /\ getASLPStExc w (fun t => t = s) r) -> pre s)).
  Proof. exact (proj1 (aslp_carrier (getASLPStExc w)) (proj2_sig w) pre r). Qed.

  #[program] Definition retASLPStExc {A} (a : A) : ASLPStExc A :=
    fun pre r => (retASPStExc a pre r) \/ (retDSLPStExc a pre r).
  Next Obligation. exact (aslp_shape_wf (fun s r => r = Some (a, s))). Qed.

  (** The two probe forms are the ASP and the DSLP of the recovered relation. *)
  Lemma aspPartaslp_closed {A} (w : ASLPStExc A) pre r :
    (~ getASLPStExc w (fun _ => False) r /\ getASLPStExc w pre r)
    <-> (exists s, pre s /\ (~ getASLPStExc w (fun _ => False) r
                             /\ getASLPStExc w (fun t => t = s) r)).
  Proof.
    split.
    - intros [Hn Hw]. destruct (proj1 (getProgASLP_carrier w pre r) Hw) as [He | Hall];
        [ exact He |].
      apply NNPP. intro Hno. apply Hn. apply getProgASLP_carrier. right.
      intros s Hs. exfalso. exact (Hno (ex_intro _ s (conj (Hall s Hs) Hs))).
    - intros [s [Hp Hs]]. split.
      + intro Hc. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hc)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply getProgASLP_carrier. left. exists s. split; [ exact Hp | exact Hs ].
  Qed.

  Lemma dslpPartaslp_closed {A} (w : ASLPStExc A) pre r :
    (getASLPStExc w (fun _ => False) r \/ ~ getASLPStExc w (fun s => ~ pre s) r)
    <-> (forall s, (~ getASLPStExc w (fun _ => False) r
                    /\ getASLPStExc w (fun t => t = s) r) -> pre s).
  Proof.
    split.
    - intros [Hbot | Hn] s Hs.
      + exfalso. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hbot)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply NNPP. intro Hnp. apply Hn. apply getProgASLP_carrier. left.
        exists s. split; [ exact Hnp | exact Hs ].
    - intro Hall.
      destruct (classic (exists s, ~ getASLPStExc w (fun _ => False) r
                                   /\ getASLPStExc w (fun t => t = s) r)) as [[s0 Hs0] | Hno].
      + right. intro Hc.
        destruct (proj1 (getProgASLP_carrier w (fun t => ~ pre t) r) Hc)
          as [[s [Hnp Hs]] | Hev].
        * exact (Hnp (Hall s Hs)).
        * exact (Hev s0 Hs0 (Hall s0 Hs0)).
      + left. apply getProgASLP_carrier. right. intros s Hs.
        exfalso. exact (Hno (ex_intro _ s Hs)).
  Qed.

  Lemma singletonProg_ext' {A} (w1 w2 : @SPStExc S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
  Qed.

  Lemma aslp_healthy_ext {A} (w1 w2 : @SPStExc S A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    TerminatingPositivelyJoinPreserving w1 -> TerminatingPositivelyJoinPreserving w2.
  Proof.
    intros Hext [HT HD]. split.
    - intro r. apply Hext. exact (HT r).
    - intros I i0 p r. split.
      + intro Hw. destruct (proj1 (HD I i0 p r) (proj2 (Hext _ r) Hw)) as [i Hi].
        exists i. apply Hext. exact Hi.
      + intros [i Hi]. apply Hext. apply (HD I i0 p r).
        exists i. exact (proj2 (Hext _ r) Hi).
  Qed.

  #[program] Definition aspPartaslp {A} (w : ASLPStExc A) : ASPStExc S A :=
    fun pre r => ~ getASLPStExc w (fun _ => False) r /\ getASLPStExc w pre r.
  Next Obligation.
    apply (singletonProg_ext'
             (fun pre r => exists s, pre s /\ (~ getASLPStExc w (fun _ => False) r
                                               /\ getASLPStExc w (fun t => t = s) r))).
    - intros pre r. exact (iff_sym (aspPartaslp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartaslp {A} (w : ASLPStExc A) : DSLPStExc S A :=
    fun pre r => getASLPStExc w (fun _ => False) r \/ ~ getASLPStExc w (fun s => ~ pre s) r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (~ getASLPStExc w (fun _ => False) r
                                      /\ getASLPStExc w (fun t => t = s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartaslp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem aslp_split {A} (w : ASLPStExc A) pre r :
    getASLPStExc w pre r <-> (getASPStExc (aspPartaslp w) pre r \/ getDSLPStExc (dslpPartaslp w) pre r).
  Proof.
    refine (iff_trans (getProgASLP_carrier w pre r) _). split.
    - intros [He | Hall].
      + left. exact (proj2 (aspPartaslp_closed w pre r) He).
      + right. exact (proj2 (dslpPartaslp_closed w pre r) Hall).
    - intros [Ha | Hd].
      + left. exact (proj1 (aspPartaslp_closed w pre r) Ha).
      + right. exact (proj1 (dslpPartaslp_closed w pre r) Hd).
  Qed.

  (** Both binds compute the SAME composite relation. *)
  Lemma aslp_comp_recov_option (A B : Type)
    (Rx : S -> option (A * S) -> Prop) (F : A -> S -> option (B * S) -> Prop) :
    forall (s : S) (r : option (B * S)),
    (exists o, (~ ((exists t, False /\ Rx t o) \/ (forall t, Rx t o -> False))
      /\ ((exists t, t = s /\ Rx t o) \/ (forall t, Rx t o -> t = s)))
      /\ match o with
      | Some (a, smid) => (~ ((exists t, False /\ F a t r) \/ (forall t, F a t r -> False))
        /\ ((exists t, t = smid /\ F a t r) \/ (forall t, F a t r -> t = smid)))
      | None => r = None end) <->
    (exists o, Rx s o /\ match o with Some (a, smid) => F a smid r | None => r = None end).
  Proof. exact (comp_cong S _ _ _ _ (aslp_recov Rx) (fun a => aslp_recov (F a))). Qed.
  Lemma bind_asp_parts' {A B} (m : ASLPStExc A) (k : A -> ASLPStExc B) pre r :
    getASPStExc (bindASPStExc (aspPartaslp m) (fun a => aspPartaslp (k a))) pre r
    <-> (exists s, pre s /\
           (exists o, (~ getASLPStExc m (fun _ => False) o
                       /\ getASLPStExc m (fun t => t = s) o)
                      /\ match o with
                         | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                             /\ getASLPStExc (k a) (fun t => t = smid) r
                         | None => r = None
                         end)).
  Proof.
    split.
    - intros [[a Hk] | [Hr Hm]].
      + destruct (proj1 (aspPartaslp_closed (k a)
                           (fun s0 => getASPStExc (aspPartaslp m) pre (Some (a, s0))) r) Hk)
          as [smid [Hp Hrk]].
        destruct (proj1 (aspPartaslp_closed m pre (Some (a, smid))) Hp) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists (Some (a, smid)). split; [ exact Hrm | exact Hrk ].
      + destruct (proj1 (aspPartaslp_closed m pre None) Hm) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists None. split; [ exact Hrm | exact Hr ].
    - intros [s [Hps [[[a smid]|] [Hrm Hrk]]]].
      + left. exists a.
        exact (proj2 (aspPartaslp_closed (k a)
                        (fun s0 => getASPStExc (aspPartaslp m) pre (Some (a, s0))) r)
                 (ex_intro _ smid
                    (conj (proj2 (aspPartaslp_closed m pre (Some (a, smid)))
                             (ex_intro _ s (conj Hps Hrm))) Hrk))).
      + right. split; [ exact Hrk |].
        exact (proj2 (aspPartaslp_closed m pre None) (ex_intro _ s (conj Hps Hrm))).
  Qed.

  Lemma bind_dslp_parts' {A B} (m : ASLPStExc A) (k : A -> ASLPStExc B) pre r :
    getDSLPStExc (bindDSLPStExc (dslpPartaslp m) (fun a => dslpPartaslp (k a))) pre r
    <-> (forall s,
           (exists o, (~ getASLPStExc m (fun _ => False) o
                       /\ getASLPStExc m (fun t => t = s) o)
                      /\ match o with
                         | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                             /\ getASLPStExc (k a) (fun t => t = smid) r
                         | None => r = None
                         end) -> pre s).
  Proof.
    split.
    - intros [H1 H2] s [[[a smid]|] [Hrm Hrk]].
      + exact (proj1 (dslpPartaslp_closed m pre (Some (a, smid)))
                 (proj1 (dslpPartaslp_closed (k a)
                           (fun s0 => getDSLPStExc (dslpPartaslp m) pre (Some (a, s0))) r)
                    (H1 a) smid Hrk) s Hrm).
      + exact (proj1 (dslpPartaslp_closed m pre None) (H2 Hrk) s Hrm).
    - intro H. split.
      + intro a.
        exact (proj2 (dslpPartaslp_closed (k a)
                        (fun s0 => getDSLPStExc (dslpPartaslp m) pre (Some (a, s0))) r)
                 (fun smid Hrk =>
                    proj2 (dslpPartaslp_closed m pre (Some (a, smid)))
                      (fun s Hrm => H s (ex_intro _ (Some (a, smid)) (conj Hrm Hrk))))).
      + intro Hr.
        exact (proj2 (dslpPartaslp_closed m pre None)
                 (fun s Hrm => H s (ex_intro _ None (conj Hrm Hr)))).
  Qed.

  #[program] Definition bindASLPStExc {A B} (m : ASLPStExc A) (k : A -> ASLPStExc B) : ASLPStExc B :=
    fun pre r => bindASPStExc (aspPartaslp m) (fun a => aspPartaslp (k a)) pre r \/
                   bindDSLPStExc (dslpPartaslp m) (fun a => dslpPartaslp (k a)) pre r.
  Next Obligation.
    apply (aslp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists o, (~ getASLPStExc m (fun _ => False) o
                               /\ getASLPStExc m (fun t => t = s) o)
                              /\ match o with
                                 | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                                     /\ getASLPStExc (k a) (fun t => t = smid) r
                                 | None => r = None
                                 end))
                \/ (forall s,
                      (exists o, (~ getASLPStExc m (fun _ => False) o
                                  /\ getASLPStExc m (fun t => t = s) o)
                                 /\ match o with
                                    | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                                        /\ getASLPStExc (k a) (fun t => t = smid) r
                                    | None => r = None
                                    end) -> pre s))).
    - intros pre r. split.
      + intros [He | Hall];
          [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
          | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
      + intros [Ha | Hd];
          [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
          | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - apply aslp_shape_wf.
  Qed.

  (** [bindASLPStExc m k] is pointwise the ASLP of the composite relation. *)
  Lemma bindASLPProg_aslp {A B} (m : ASLPStExc A) (k : A -> ASLPStExc B) pre r :
    getASLPStExc (bindASLPStExc m k) pre r
    <-> ((exists s, pre s /\
            (exists o, (~ getASLPStExc m (fun _ => False) o
                        /\ getASLPStExc m (fun t => t = s) o)
                       /\ match o with
                          | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                              /\ getASLPStExc (k a) (fun t => t = smid) r
                          | None => r = None
                          end))
         \/ (forall s,
               (exists o, (~ getASLPStExc m (fun _ => False) o
                           /\ getASLPStExc m (fun t => t = s) o)
                          /\ match o with
                             | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                                 /\ getASLPStExc (k a) (fun t => t = smid) r
                             | None => r = None
                             end) -> pre s)).
  Proof.
    split.
    - intros [Ha | Hd];
        [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
        | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - intros [He | Hall];
        [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
        | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
  Qed.

  Lemma rec_retASLPProg {A} (a : A) (s : S) (r : option (A * S)) :
    (~ getASLPStExc (retASLPStExc a) (fun _ => False) r
     /\ getASLPStExc (retASLPStExc a) (fun t => t = s) r)
    <-> r = Some (a, s).
  Proof. exact (aslp_recov (fun s0 r0 => r0 = Some (a, s0)) s r). Qed.

  Lemma rec_bindASLPProg {A B} (m : ASLPStExc A) (k : A -> ASLPStExc B)
    (s : S) (r : option (B * S)) :
    (~ getASLPStExc (bindASLPStExc m k) (fun _ => False) r
     /\ getASLPStExc (bindASLPStExc m k) (fun t => t = s) r)
    <-> (exists o, (~ getASLPStExc m (fun _ => False) o
                    /\ getASLPStExc m (fun t => t = s) o)
                   /\ match o with
                      | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r
                                          /\ getASLPStExc (k a) (fun t => t = smid) r
                      | None => r = None
                      end).
  Proof.
    refine (iff_trans (aslp_rec_ext _ _ (bindASLPProg_aslp m k) s r)
              (aslp_recov
                 (fun s0 r0 =>
                    exists o, (~ getASLPStExc m (fun _ => False) o
                               /\ getASLPStExc m (fun t => t = s0) o)
                              /\ match o with
                                 | Some (a, smid) => ~ getASLPStExc (k a) (fun _ => False) r0
                                                     /\ getASLPStExc (k a) (fun t => t = smid) r0
                                 | None => r0 = None
                                 end)
                 s r)).
  Qed.

  #[global]
    Instance Monad__ASLPStExc : Monad ASLPStExc :=
    {| ret := fun _ => @retASLPStExc _ ;
      bind := fun _ _ => @bindASLPStExc _ _ |}.

  #[global] Instance Eq1__ASLPStExc : Eq1 ASLPStExc :=
    fun A m n => forall pre r, getASLPStExc m pre r <-> getASLPStExc n pre r.

  #[global] Instance Eq1Equivalence__ASLPStExc
    : @Eq1Equivalence ASLPStExc _ Eq1__ASLPStExc.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__ASLPStExc
    : @MonadLawsE ASLPStExc Eq1__ASLPStExc _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ASLPStExc. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (~ getASLPStExc (retASLPStExc x) (fun _ => False) o
                             /\ getASLPStExc (retASLPStExc x) (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getASLPStExc (f a) (fun _ => False) r0
                                   /\ getASLPStExc (f a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (~ getASLPStExc (f x) (fun _ => False) r0
                      /\ getASLPStExc (f x) (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getASLPStExc (retASLPStExc x) (fun _ => False) r1
                                  /\ getASLPStExc (retASLPStExc x) (fun t => t = s1) r1)
                    (fun s1 r1 => r1 = Some (x, s1))
                    (fun a1 s1 r1 => ~ getASLPStExc (f a1) (fun _ => False) r1
                                     /\ getASLPStExc (f a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getASLPStExc (f a1) (fun _ => False) r1
                                     /\ getASLPStExc (f a1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_retASLPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l S x
                    (fun a1 s1 r1 => ~ getASLPStExc (f a1) (fun _ => False) r1
                                     /\ getASLPStExc (f a1) (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp (retASLPStExc x) f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier (f x) pre r)))).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ASLPStExc. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (A * S)),
                 (exists o, (~ getASLPStExc m (fun _ => False) o
                             /\ getASLPStExc m (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getASLPStExc (retASLPStExc a) (fun _ => False) r0
                                   /\ getASLPStExc (retASLPStExc a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (~ getASLPStExc m (fun _ => False) r0
                      /\ getASLPStExc m (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getASLPStExc m (fun _ => False) r1
                                  /\ getASLPStExc m (fun t => t = s1) r1)
                    (fun s1 r1 => ~ getASLPStExc m (fun _ => False) r1
                                  /\ getASLPStExc m (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getASLPStExc (retASLPStExc a1) (fun _ => False) r1
                                     /\ getASLPStExc (retASLPStExc a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => r1 = Some (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retASLPProg a1 s1 r1) s r0)
                 (comp_ret_r S
                    (fun s1 r1 => ~ getASLPStExc m (fun _ => False) r1
                                  /\ getASLPStExc m (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp m _ pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier m pre r)))).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ASLPStExc. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (C * S)),
                 (exists o, (~ getASLPStExc (bindASLPStExc x f) (fun _ => False) o
                             /\ getASLPStExc (bindASLPStExc x f) (fun t => t = s) o)
                            /\ match o with
                               | Some (b, smid) =>
                                   ~ getASLPStExc (g b) (fun _ => False) r0
                                   /\ getASLPStExc (g b) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (~ getASLPStExc x (fun _ => False) o
                                 /\ getASLPStExc x (fun t => t = s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       ~ getASLPStExc (bindASLPStExc (f a) g)
                                           (fun _ => False) r0
                                       /\ getASLPStExc (bindASLPStExc (f a) g)
                                            (fun t => t = smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getASLPStExc (bindASLPStExc x f) (fun _ => False) r1
                                  /\ getASLPStExc (bindASLPStExc x f) (fun t => t = s1) r1)
                    (fun s1 r1 =>
                       exists o, (~ getASLPStExc x (fun _ => False) o
                                  /\ getASLPStExc x (fun t => t = s1) o)
                                 /\ match o with
                                    | Some (a, smid) =>
                                        ~ getASLPStExc (f a) (fun _ => False) r1
                                        /\ getASLPStExc (f a) (fun t => t = smid) r1
                                    | None => r1 = None
                                    end)
                    (fun b1 s1 r1 => ~ getASLPStExc (g b1) (fun _ => False) r1
                                     /\ getASLPStExc (g b1) (fun t => t = s1) r1)
                    (fun b1 s1 r1 => ~ getASLPStExc (g b1) (fun _ => False) r1
                                     /\ getASLPStExc (g b1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_bindASLPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc S
                       (fun s1 r1 => ~ getASLPStExc x (fun _ => False) r1
                                     /\ getASLPStExc x (fun t => t = s1) r1)
                       (fun a1 s1 r1 => ~ getASLPStExc (f a1) (fun _ => False) r1
                                        /\ getASLPStExc (f a1) (fun t => t = s1) r1)
                       (fun b1 s1 r1 => ~ getASLPStExc (g b1) (fun _ => False) r1
                                        /\ getASLPStExc (g b1) (fun t => t = s1) r1)
                       s r0)
                    (comp_cong S
                       (fun s1 r1 => ~ getASLPStExc x (fun _ => False) r1
                                     /\ getASLPStExc x (fun t => t = s1) r1)
                       (fun s1 r1 => ~ getASLPStExc x (fun _ => False) r1
                                     /\ getASLPStExc x (fun t => t = s1) r1)
                       (fun a1 s1 r1 =>
                          exists o, (~ getASLPStExc (f a1) (fun _ => False) o
                                     /\ getASLPStExc (f a1) (fun t => t = s1) o)
                                    /\ match o with
                                       | Some (b, smid) =>
                                           ~ getASLPStExc (g b) (fun _ => False) r1
                                           /\ getASLPStExc (g b) (fun t => t = smid) r1
                                       | None => r1 = None
                                       end)
                       (fun a1 s1 r1 =>
                          ~ getASLPStExc (bindASLPStExc (f a1) g) (fun _ => False) r1
                          /\ getASLPStExc (bindASLPStExc (f a1) g) (fun t => t = s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindASLPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindASLPProg_aslp (bindASLPStExc x f) g pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp x (fun a => bindASLPStExc (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ASLPStExc in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (~ getASLPStExc x (fun _ => False) o
                             /\ getASLPStExc x (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getASLPStExc (f a) (fun _ => False) r0
                                   /\ getASLPStExc (f a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (~ getASLPStExc y (fun _ => False) o
                                 /\ getASLPStExc y (fun t => t = s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       ~ getASLPStExc (g a) (fun _ => False) r0
                                       /\ getASLPStExc (g a) (fun t => t = smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (comp_cong S
                 (fun s1 r1 => ~ getASLPStExc x (fun _ => False) r1
                               /\ getASLPStExc x (fun t => t = s1) r1)
                 (fun s1 r1 => ~ getASLPStExc y (fun _ => False) r1
                               /\ getASLPStExc y (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getASLPStExc (f a1) (fun _ => False) r1
                                  /\ getASLPStExc (f a1) (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getASLPStExc (g a1) (fun _ => False) r1
                                  /\ getASLPStExc (g a1) (fun t => t = s1) r1)
                 (fun s1 r1 => aslp_rec_ext (getASLPStExc x) (getASLPStExc y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    aslp_rec_ext (getASLPStExc (f a1)) (getASLPStExc (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindASLPProg_aslp x f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp y g pre r)))).
  Qed.
End ProgASLPMonad.

Arguments retASLPStExc {_} {_}.
Arguments bindASLPStExc {_} {_} {_}.
Arguments getASLPStExc {_} {_}.

(* ================================================================= *)
(** * Terminating-slice variant (factored out of SPSimplerSpecMonads.v) *)
(* ================================================================= *)


Import MonadNotation.
Open Scope monad_scope.

Module StASLP.
  Import StTrans StASP StDSLP StDSP.
Section ProgASLPMonad.
  Variable S : Type.

  Definition TerminatingPositivelyJoinPreserving {A} (w : SPSt A) : Prop :=
    TerminatingProg S w /\ DisjunctiveProg S w.

  Definition ASLPSt (A : Type) : Type :=
    { w : SPSt A | TerminatingPositivelyJoinPreserving w }.

  Definition getASLPSt {A} (w : ASLPSt A) : SPSt A := proj1_sig w.

  Lemma aslp_recov {A} (R : S -> (A * S) -> Prop)
    (s : S) (r : (A * S)) :
    (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
     /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
    <-> R s r.
  Proof. exact (aslp_recov_gen S (A * S) R s r). Qed.

  Lemma aslp_wf {A} (R : S -> (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\
              (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
               /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s))))
           \/ (forall s,
                 (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
                  /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
                 -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj2 (aslp_recov R s r) Hs) ].
      + right. intros s H. exact (Hall s (proj1 (aslp_recov R s r) H)).
    - intros [[s [Hp H]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj1 (aslp_recov R s r) H) ].
      + right. intros s Hs. exact (Hall s (proj2 (aslp_recov R s r) Hs)).
  Qed.

  Lemma aslp_cong {A} (R R' : S -> (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\ R' s r) \/ (forall s, R' s r -> pre s)).
  Proof. exact (aslp_cong_gen S (A * S) R R' H). Qed.

  Lemma aslp_rec_ext {A} (w1 w2 : @SPSt S A)
    (H : forall pre r, w1 pre r <-> w2 pre r) :
    forall (s : S) (r : (A * S)),
      (~ w1 (fun _ => False) r /\ w1 (fun t => t = s) r)
      <-> (~ w2 (fun _ => False) r /\ w2 (fun t => t = s) r).
  Proof.
    intros s r. split.
    - intros [H1 H2]. split;
        [ intro Hc; exact (H1 (proj2 (H _ r) Hc)) | exact (proj1 (H _ r) H2) ].
    - intros [H1 H2]. split;
        [ intro Hc; exact (H1 (proj1 (H _ r) Hc)) | exact (proj2 (H _ r) H2) ].
  Qed.

  (** Dual of [dsp_carrier]: the carrier's well-formedness condition is
      equivalent to saying that [w] is the ASLP reading of its recovered
      relation. The proofs use this representation. *)
  Lemma aslp_carrier {A} (w : SPSt A) :
    TerminatingPositivelyJoinPreserving w <->
      (forall (pre : S -> Prop) (r : (A * S)), w pre r <->
      ((exists s, pre s /\ (~ w (fun _ => False) r /\ w (fun t => t = s) r)) \/
         (forall s, (~ w (fun _ => False) r /\ w (fun t => t = s) r) -> pre s))).
  Proof.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    split.
    - intros [HT HD] pre r.
      (* the join of the two-element family [{P, Q}] is [Q] when [P <= Q] *)
      assert (Hmono : forall (P Q : S -> Prop) y,
                 (forall s, P s -> Q s) -> w P y -> w Q y).
      { intros P Q y Hpq Hw.
        assert (Heq : Q = (fun s => exists b : bool, (if b then P else Q) s)).
        { apply Hext. intro s. split.
          - intro Hs. exists false. exact Hs.
          - intros [b Hb]. destruct b; [ exact (Hpq s Hb) | exact Hb ]. }
        rewrite Heq.
        apply (HD bool (inhabits true) (fun b => if b then P else Q) y).
        exists true. exact Hw. }
      destruct (classic (w (fun _ => False) r)) as [Hbot | Hnbot].
      + split.
        * intros _. right. intros s [Hn _]. destruct (Hn Hbot).
        * intros _. apply (Hmono (fun _ => False) pre r); [ intros s [] | exact Hbot ].
      + (* [S] is inhabited, else top and bottom coincide *)
        assert (Hinh : exists s0 : S, True).
        { apply NNPP. intro Hno. apply Hnbot.
          assert (Heq : (fun _ : S => True) = (fun _ : S => False)).
          { apply Hext. intro s. split;
              [ intros _; exact (Hno (ex_intro _ s I)) | intros [] ]. }
          pose proof (HT r) as Htop. rewrite Heq in Htop. exact Htop. }
        destruct Hinh as [sinh _].
        (* top-preservation makes some singleton already force [r] *)
        assert (Hex : exists s, w (fun t => t = s) r).
        { assert (Heq : (fun _ : S => True) = (fun s => exists s0 : S, s = s0)).
          { apply Hext. intro s. split;
              [ intros _; exists s; reflexivity | intros _; exact I ]. }
          pose proof (HT r) as Htop. rewrite Heq in Htop.
          exact (proj1 (HD S (inhabits sinh) (fun s0 s => s = s0) r) Htop). }
        (* the join of all preconditions that FAIL to force [r] *)
        pose (bad := fun s => exists i : { q : S -> Prop | ~ w q r }, proj1_sig i s).
        assert (Hbad : ~ w bad r).
        { unfold bad. intro Hc.
          destruct (proj1 (HD { q : S -> Prop | ~ w q r }
                             (inhabits (exist (fun q => ~ w q r) (fun _ : S => False) Hnbot))
                             (fun i s => proj1_sig i s) r) Hc) as [i Hi].
          exact (proj2_sig i Hi). }
        assert (Hub : forall q, ~ w q r -> forall s, q s -> bad s).
        { intros q Hq s Hs. unfold bad.
          exists (exist (fun q0 => ~ w q0 r) q Hq). exact Hs. }
        assert (Hrec : forall s, (~ w (fun _ => False) r /\ w (fun t => t = s) r)
                                 <-> ~ bad s).
        { intro s. split.
          - intros [_ Hw] Hb. unfold bad in Hb. destruct Hb as [i Hi].
            apply (proj2_sig i).
            apply (Hmono (fun t => t = s) (proj1_sig i) r);
              [ intros t Ht; rewrite Ht; exact Hi | exact Hw ].
          - intro Hnb. split; [ exact Hnbot |].
            apply NNPP. intro Hnw.
            exact (Hnb (Hub (fun t => t = s) Hnw s eq_refl)). }
        assert (Hmain : w pre r <-> exists s, pre s /\ ~ bad s).
        { split.
          - intro Hw. apply NNPP. intro Hno. apply Hbad.
            apply (Hmono pre bad r); [| exact Hw ].
            intros s Hs. apply NNPP. intro Hnb.
            exact (Hno (ex_intro _ s (conj Hs Hnb))).
          - intros [s [Hs Hnb]]. apply NNPP. intro Hnw.
            exact (Hnb (Hub pre Hnw s Hs)). }
        split.
        * intro Hw. left. destruct (proj1 Hmain Hw) as [s [Hs Hnb]].
          exists s. split; [ exact Hs | exact (proj2 (Hrec s) Hnb) ].
        * intros [[s [Hs Hr']] | Hall].
          -- apply Hmain. exists s.
             split; [ exact Hs | exact (proj1 (Hrec s) Hr') ].
          -- destruct Hex as [s0 Hs0]. apply Hmain. exists s0.
             split; [ exact (Hall s0 (conj Hnbot Hs0))
                    | exact (proj1 (Hrec s0) (conj Hnbot Hs0)) ].
    - intro HD. split.
      + intro r. apply (HD (fun _ => True) r). right. intros s _. exact I.
      + intros J Hi0 p r. destruct Hi0 as [i0]. split.
        * intro Hw. destruct (proj1 (HD (fun s => exists i : J, p i s) r) Hw)
            as [[s [[i Hpi] Hrec]] | Hall].
          -- exists i. apply (HD (fun s0 => p i s0) r). left.
             exists s. split; [ exact Hpi | exact Hrec ].
          -- destruct (classic (exists s, ~ w (fun _ => False) r
                                          /\ w (fun t => t = s) r)) as [[s0 Hs0] | Hno].
             ++ destruct (Hall s0 Hs0) as [i Hpi].
                exists i. apply (HD (fun s0' => p i s0') r). left.
                exists s0. split; [ exact Hpi | exact Hs0 ].
             ++ exists i0. apply (HD (fun s0 => p i0 s0) r). right.
                intros s Hrec. exfalso. exact (Hno (ex_intro _ s Hrec)).
        * intros [i Hw]. apply (HD (fun s => exists j : J, p j s) r).
          destruct (proj1 (HD (fun s0 => p i s0) r) Hw) as [[s [Hpi Hrec]] | Hall].
          -- left. exists s. split; [ exists i; exact Hpi | exact Hrec ].
          -- right. intros s Hrec. exists i. exact (Hall s Hrec).
  Qed.

  Lemma aslp_shape_wf {A} (R : S -> (A * S) -> Prop) :
    TerminatingPositivelyJoinPreserving
      (fun pre r => (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s)).
  Proof.
    split.
    - intros r. right. intros s _. exact I.
    - intros I [i0] p r. split.
      + intros [[s [[i Hi] Hs]] | Hall].
        * exists i. left. exists s. split; [ exact Hi | exact Hs ].
        * destruct (classic (exists s, R s r)) as [[s0 Hs0] | Hno].
          -- destruct (Hall s0 Hs0) as [i Hi]. exists i. left.
             exists s0. split; [ exact Hi | exact Hs0 ].
          -- exists i0. right. intros s Hs. exfalso.
             exact (Hno (ex_intro _ s Hs)).
      + intros [i [[s [Hp Hs]] | Hall]].
        * left. exists s. split; [ exists i; exact Hp | exact Hs ].
        * right. intros s Hs. exists i. exact (Hall s Hs).
  Qed.

  Lemma getProgASLP_carrier {A} (w : ASLPSt A) (pre : S -> Prop) (r : A * S) :
    getASLPSt w pre r <->
      ((exists s, pre s /\ (~ getASLPSt w (fun _ => False) r
                            /\ getASLPSt w (fun t => t = s) r)) \/
         (forall s, (~ getASLPSt w (fun _ => False) r
                     /\ getASLPSt w (fun t => t = s) r) -> pre s)).
  Proof. exact (proj1 (aslp_carrier (getASLPSt w)) (proj2_sig w) pre r). Qed.

  (** ** [ret], the two projections, and [bind] *)

  #[program] Definition retASLPSt {A} (a : A) : ASLPSt A :=
    fun pre r => (retASPSt a pre r) \/ (retDSLPSt a pre r).
  Next Obligation. exact (aslp_shape_wf (fun s r => r = (a, s))). Qed.

  Lemma aspPartaslp_closed {A} (w : ASLPSt A) pre r :
    (~ getASLPSt w (fun _ => False) r /\ getASLPSt w pre r)
    <-> (exists s, pre s /\ (~ getASLPSt w (fun _ => False) r
                             /\ getASLPSt w (fun t => t = s) r)).
  Proof.
    split.
    - intros [Hn Hw]. destruct (proj1 (getProgASLP_carrier w pre r) Hw) as [He | Hall];
        [ exact He |].
      apply NNPP. intro Hno. apply Hn. apply getProgASLP_carrier. right.
      intros s Hs. exfalso. exact (Hno (ex_intro _ s (conj (Hall s Hs) Hs))).
    - intros [s [Hp Hs]]. split.
      + intro Hc. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hc)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply getProgASLP_carrier. left. exists s. split; [ exact Hp | exact Hs ].
  Qed.

  Lemma dslpPartaslp_closed {A} (w : ASLPSt A) pre r :
    (getASLPSt w (fun _ => False) r \/ ~ getASLPSt w (fun s => ~ pre s) r)
    <-> (forall s, (~ getASLPSt w (fun _ => False) r
                    /\ getASLPSt w (fun t => t = s) r) -> pre s).
  Proof.
    split.
    - intros [Hbot | Hn] s Hs.
      + exfalso. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hbot)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply NNPP. intro Hnp. apply Hn. apply getProgASLP_carrier. left.
        exists s. split; [ exact Hnp | exact Hs ].
    - intro Hall.
      destruct (classic (exists s, ~ getASLPSt w (fun _ => False) r
                                   /\ getASLPSt w (fun t => t = s) r))
        as [[s0 Hs0] | Hno].
      + right. intro Hc.
        destruct (proj1 (getProgASLP_carrier w (fun t => ~ pre t) r) Hc)
          as [[s [Hnp Hs]] | Hev].
        * exact (Hnp (Hall s Hs)).
        * exact (Hev s0 Hs0 (Hall s0 Hs0)).
      + left. apply getProgASLP_carrier. right. intros s Hs.
        exfalso. exact (Hno (ex_intro _ s Hs)).
  Qed.

  Lemma aslp_healthy_ext {A} (w1 w2 : @SPSt S A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    TerminatingPositivelyJoinPreserving w1 -> TerminatingPositivelyJoinPreserving w2.
  Proof.
    intros Hext [HT HD]. split.
    - intro r. apply Hext. exact (HT r).
    - intros I i0 p r. split.
      + intro Hw. destruct (proj1 (HD I i0 p r) (proj2 (Hext _ r) Hw)) as [i Hi].
        exists i. apply Hext. exact Hi.
      + intros [i Hi]. apply Hext. apply (HD I i0 p r).
        exists i. exact (proj2 (Hext _ r) Hi).
  Qed.

  #[program] Definition aspPartaslp {A} (w : ASLPSt A) : ASPSt S A :=
    fun pre r => ~ getASLPSt w (fun _ => False) r /\ getASLPSt w pre r.
  Next Obligation.
    apply (singletonProg_ext S
             (fun pre r => exists s, pre s /\ (~ getASLPSt w (fun _ => False) r
                                               /\ getASLPSt w (fun t => t = s) r))).
    - intros pre r. exact (iff_sym (aspPartaslp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartaslp {A} (w : ASLPSt A) : DSLPSt S A :=
    fun pre r => getASLPSt w (fun _ => False) r \/ ~ getASLPSt w (fun s => ~ pre s) r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (~ getASLPSt w (fun _ => False) r
                                      /\ getASLPSt w (fun t => t = s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartaslp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem aslp_split {A} (w : ASLPSt A) pre r :
    getASLPSt w pre r
    <-> (getASPSt (aspPartaslp w) pre r \/ getDSLPSt (dslpPartaslp w) pre r).
  Proof.
    refine (iff_trans (getProgASLP_carrier w pre r) _). split.
    - intros [He | Hall].
      + left. exact (proj2 (aspPartaslp_closed w pre r) He).
      + right. exact (proj2 (dslpPartaslp_closed w pre r) Hall).
    - intros [Ha | Hd].
      + left. exact (proj1 (aspPartaslp_closed w pre r) Ha).
      + right. exact (proj1 (dslpPartaslp_closed w pre r) Hd).
  Qed.

  Lemma bind_asp_parts' {A B} (m : ASLPSt A) (k : A -> ASLPSt B) pre r :
    getASPSt (bindASPSt (aspPartaslp m) (fun a => aspPartaslp (k a))) pre r
    <-> (exists s, pre s /\
           (exists a smid,
               (~ getASLPSt m (fun _ => False) (a, smid)
                /\ getASLPSt m (fun t => t = s) (a, smid))
               /\ (~ getASLPSt (k a) (fun _ => False) r
                   /\ getASLPSt (k a) (fun t => t = smid) r))).
  Proof.
    split.
    - intros [a Hk].
      destruct (proj1 (aspPartaslp_closed (k a)
                         (fun s0 => getASPSt (aspPartaslp m) pre (a, s0)) r) Hk)
        as [smid [Hp Hrk]].
      destruct (proj1 (aspPartaslp_closed m pre (a, smid)) Hp) as [s [Hps Hrm]].
      exists s. split; [ exact Hps |]. exists a, smid.
      split; [ exact Hrm | exact Hrk ].
    - intros [s [Hps [a [smid [Hrm Hrk]]]]].
      exists a.
      exact (proj2 (aspPartaslp_closed (k a)
                      (fun s0 => getASPSt (aspPartaslp m) pre (a, s0)) r)
               (ex_intro _ smid
                  (conj (proj2 (aspPartaslp_closed m pre (a, smid))
                           (ex_intro _ s (conj Hps Hrm))) Hrk))).
  Qed.

  Lemma bind_dslp_parts' {A B} (m : ASLPSt A) (k : A -> ASLPSt B) pre r :
    getDSLPSt (bindDSLPSt (dslpPartaslp m) (fun a => dslpPartaslp (k a))) pre r
    <-> (forall s,
           (exists a smid,
               (~ getASLPSt m (fun _ => False) (a, smid)
                /\ getASLPSt m (fun t => t = s) (a, smid))
               /\ (~ getASLPSt (k a) (fun _ => False) r
                   /\ getASLPSt (k a) (fun t => t = smid) r)) -> pre s).
  Proof.
    split.
    - intros H s [a [smid [Hrm Hrk]]].
      exact (proj1 (dslpPartaslp_closed m pre (a, smid))
               (proj1 (dslpPartaslp_closed (k a)
                         (fun s0 => getDSLPSt (dslpPartaslp m) pre (a, s0)) r)
                  (H a) smid Hrk) s Hrm).
    - intros H a.
      exact (proj2 (dslpPartaslp_closed (k a)
                      (fun s0 => getDSLPSt (dslpPartaslp m) pre (a, s0)) r)
               (fun smid Hrk =>
                  proj2 (dslpPartaslp_closed m pre (a, smid))
                    (fun s Hrm => H s (ex_intro _ a (ex_intro _ smid (conj Hrm Hrk)))))).
  Qed.

  #[program] Definition bindASLPSt {A B}
    (m : ASLPSt A) (k : A -> ASLPSt B) : ASLPSt B :=
    fun pre r => bindASPSt (aspPartaslp m) (fun a => aspPartaslp (k a)) pre r \/
                   bindDSLPSt (dslpPartaslp m) (fun a => dslpPartaslp (k a)) pre r.
  Next Obligation.
    apply (aslp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists a smid,
                       (~ getASLPSt m (fun _ => False) (a, smid)
                        /\ getASLPSt m (fun t => t = s) (a, smid))
                       /\ (~ getASLPSt (k a) (fun _ => False) r
                           /\ getASLPSt (k a) (fun t => t = smid) r)))
                \/ (forall s,
                      (exists a smid,
                          (~ getASLPSt m (fun _ => False) (a, smid)
                           /\ getASLPSt m (fun t => t = s) (a, smid))
                          /\ (~ getASLPSt (k a) (fun _ => False) r
                              /\ getASLPSt (k a) (fun t => t = smid) r)) -> pre s))).
    - intros pre r. split.
      + intros [He | Hall];
          [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
          | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
      + intros [Ha | Hd];
          [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
          | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - apply aslp_shape_wf.
  Qed.

  Lemma bindASLPProg_aslp {A B} (m : ASLPSt A) (k : A -> ASLPSt B) pre r :
    getASLPSt (bindASLPSt m k) pre r
    <-> ((exists s, pre s /\
            (exists a smid,
                (~ getASLPSt m (fun _ => False) (a, smid)
                 /\ getASLPSt m (fun t => t = s) (a, smid))
                /\ (~ getASLPSt (k a) (fun _ => False) r
                    /\ getASLPSt (k a) (fun t => t = smid) r)))
         \/ (forall s,
               (exists a smid,
                   (~ getASLPSt m (fun _ => False) (a, smid)
                    /\ getASLPSt m (fun t => t = s) (a, smid))
                   /\ (~ getASLPSt (k a) (fun _ => False) r
                       /\ getASLPSt (k a) (fun t => t = smid) r)) -> pre s)).
  Proof.
    split.
    - intros [Ha | Hd];
        [ left; exact (proj1 (bind_asp_parts' m k pre r) Ha)
        | right; exact (proj1 (bind_dslp_parts' m k pre r) Hd) ].
    - intros [He | Hall];
        [ left; exact (proj2 (bind_asp_parts' m k pre r) He)
        | right; exact (proj2 (bind_dslp_parts' m k pre r) Hall) ].
  Qed.

  Lemma rec_retASLPProg {A} (a : A) (s : S) (r : A * S) :
    (~ getASLPSt (retASLPSt a) (fun _ => False) r
     /\ getASLPSt (retASLPSt a) (fun t => t = s) r)
    <-> r = (a, s).
  Proof. exact (aslp_recov (fun s0 r0 => r0 = (a, s0)) s r). Qed.

  Lemma rec_bindASLPProg {A B} (m : ASLPSt A) (k : A -> ASLPSt B)
    (s : S) (r : B * S) :
    (~ getASLPSt (bindASLPSt m k) (fun _ => False) r
     /\ getASLPSt (bindASLPSt m k) (fun t => t = s) r)
    <-> (exists a smid,
            (~ getASLPSt m (fun _ => False) (a, smid)
             /\ getASLPSt m (fun t => t = s) (a, smid))
            /\ (~ getASLPSt (k a) (fun _ => False) r
                /\ getASLPSt (k a) (fun t => t = smid) r)).
  Proof.
    refine (iff_trans (aslp_rec_ext _ _ (bindASLPProg_aslp m k) s r)
              (aslp_recov
                 (fun s0 r0 =>
                    exists a smid,
                      (~ getASLPSt m (fun _ => False) (a, smid)
                       /\ getASLPSt m (fun t => t = s0) (a, smid))
                      /\ (~ getASLPSt (k a) (fun _ => False) r0
                          /\ getASLPSt (k a) (fun t => t = smid) r0))
                 s r)).
  Qed.

  #[global] Instance Monad__ASLPSt : Monad ASLPSt :=
    {| ret := fun _ => @retASLPSt _ ;
       bind := fun _ _ => @bindASLPSt _ _ |}.

  #[global] Instance Eq1__ASLPSt : Eq1 ASLPSt :=
    fun A m n => forall pre r, getASLPSt m pre r <-> getASLPSt n pre r.

  #[global] Instance Eq1Equivalence__ASLPSt
    : @Eq1Equivalence ASLPSt _ Eq1__ASLPSt.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__ASLPSt
    : @MonadLawsE ASLPSt Eq1__ASLPSt _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ASLPSt. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (~ getASLPSt (retASLPSt x) (fun _ => False) (a, smid)
                      /\ getASLPSt (retASLPSt x) (fun t => t = s) (a, smid))
                     /\ (~ getASLPSt (f a) (fun _ => False) r0
                         /\ getASLPSt (f a) (fun t => t = smid) r0))
                 <-> (~ getASLPSt (f x) (fun _ => False) r0
                      /\ getASLPSt (f x) (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getASLPSt (retASLPSt x) (fun _ => False) r1
                                  /\ getASLPSt (retASLPSt x) (fun t => t = s1) r1)
                    (fun s1 r1 => r1 = (x, s1))
                    (fun a1 s1 r1 => ~ getASLPSt (f a1) (fun _ => False) r1
                                     /\ getASLPSt (f a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getASLPSt (f a1) (fun _ => False) r1
                                     /\ getASLPSt (f a1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_retASLPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l S x
                    (fun a1 s1 r1 => ~ getASLPSt (f a1) (fun _ => False) r1
                                     /\ getASLPSt (f a1) (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp (retASLPSt x) f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier (f x) pre r)))).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ASLPSt. intros pre r.
      assert (Hc : forall (s : S) (r0 : A * S),
                 (exists a smid,
                     (~ getASLPSt m (fun _ => False) (a, smid)
                      /\ getASLPSt m (fun t => t = s) (a, smid))
                     /\ (~ getASLPSt (retASLPSt a) (fun _ => False) r0
                         /\ getASLPSt (retASLPSt a) (fun t => t = smid) r0))
                 <-> (~ getASLPSt m (fun _ => False) r0
                      /\ getASLPSt m (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getASLPSt m (fun _ => False) r1
                                  /\ getASLPSt m (fun t => t = s1) r1)
                    (fun s1 r1 => ~ getASLPSt m (fun _ => False) r1
                                  /\ getASLPSt m (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getASLPSt (retASLPSt a1) (fun _ => False) r1
                                     /\ getASLPSt (retASLPSt a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => r1 = (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retASLPProg a1 s1 r1) s r0)
                 (comp_ret_r S
                    (fun s1 r1 => ~ getASLPSt m (fun _ => False) r1
                                  /\ getASLPSt m (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp m _ pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier m pre r)))).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ASLPSt. intros pre r.
      assert (Hc : forall (s : S) (r0 : C * S),
                 (exists b smid,
                     (~ getASLPSt (bindASLPSt x f) (fun _ => False) (b, smid)
                      /\ getASLPSt (bindASLPSt x f) (fun t => t = s) (b, smid))
                     /\ (~ getASLPSt (g b) (fun _ => False) r0
                         /\ getASLPSt (g b) (fun t => t = smid) r0))
                 <-> (exists a smid,
                         (~ getASLPSt x (fun _ => False) (a, smid)
                          /\ getASLPSt x (fun t => t = s) (a, smid))
                         /\ (~ getASLPSt (bindASLPSt (f a) g) (fun _ => False) r0
                             /\ getASLPSt (bindASLPSt (f a) g)
                                  (fun t => t = smid) r0))).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getASLPSt (bindASLPSt x f) (fun _ => False) r1
                                  /\ getASLPSt (bindASLPSt x f) (fun t => t = s1) r1)
                    (fun s1 r1 =>
                       exists a smid,
                         (~ getASLPSt x (fun _ => False) (a, smid)
                          /\ getASLPSt x (fun t => t = s1) (a, smid))
                         /\ (~ getASLPSt (f a) (fun _ => False) r1
                             /\ getASLPSt (f a) (fun t => t = smid) r1))
                    (fun b1 s1 r1 => ~ getASLPSt (g b1) (fun _ => False) r1
                                     /\ getASLPSt (g b1) (fun t => t = s1) r1)
                    (fun b1 s1 r1 => ~ getASLPSt (g b1) (fun _ => False) r1
                                     /\ getASLPSt (g b1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_bindASLPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc S
                       (fun s1 r1 => ~ getASLPSt x (fun _ => False) r1
                                     /\ getASLPSt x (fun t => t = s1) r1)
                       (fun a1 s1 r1 => ~ getASLPSt (f a1) (fun _ => False) r1
                                        /\ getASLPSt (f a1) (fun t => t = s1) r1)
                       (fun b1 s1 r1 => ~ getASLPSt (g b1) (fun _ => False) r1
                                        /\ getASLPSt (g b1) (fun t => t = s1) r1)
                       s r0)
                    (comp_cong S
                       (fun s1 r1 => ~ getASLPSt x (fun _ => False) r1
                                     /\ getASLPSt x (fun t => t = s1) r1)
                       (fun s1 r1 => ~ getASLPSt x (fun _ => False) r1
                                     /\ getASLPSt x (fun t => t = s1) r1)
                       (fun a1 s1 r1 =>
                          exists b smid,
                            (~ getASLPSt (f a1) (fun _ => False) (b, smid)
                             /\ getASLPSt (f a1) (fun t => t = s1) (b, smid))
                            /\ (~ getASLPSt (g b) (fun _ => False) r1
                                /\ getASLPSt (g b) (fun t => t = smid) r1))
                       (fun a1 s1 r1 =>
                          ~ getASLPSt (bindASLPSt (f a1) g) (fun _ => False) r1
                          /\ getASLPSt (bindASLPSt (f a1) g) (fun t => t = s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindASLPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindASLPProg_aslp (bindASLPSt x f) g pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp x (fun a => bindASLPSt (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ASLPSt in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (~ getASLPSt x (fun _ => False) (a, smid)
                      /\ getASLPSt x (fun t => t = s) (a, smid))
                     /\ (~ getASLPSt (f a) (fun _ => False) r0
                         /\ getASLPSt (f a) (fun t => t = smid) r0))
                 <-> (exists a smid,
                         (~ getASLPSt y (fun _ => False) (a, smid)
                          /\ getASLPSt y (fun t => t = s) (a, smid))
                         /\ (~ getASLPSt (g a) (fun _ => False) r0
                             /\ getASLPSt (g a) (fun t => t = smid) r0))).
      { intros s r0.
        exact (comp_cong S
                 (fun s1 r1 => ~ getASLPSt x (fun _ => False) r1
                               /\ getASLPSt x (fun t => t = s1) r1)
                 (fun s1 r1 => ~ getASLPSt y (fun _ => False) r1
                               /\ getASLPSt y (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getASLPSt (f a1) (fun _ => False) r1
                                  /\ getASLPSt (f a1) (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getASLPSt (g a1) (fun _ => False) r1
                                  /\ getASLPSt (g a1) (fun t => t = s1) r1)
                 (fun s1 r1 => aslp_rec_ext (getASLPSt x) (getASLPSt y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    aslp_rec_ext (getASLPSt (f a1)) (getASLPSt (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindASLPProg_aslp x f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp y g pre r)))).
  Qed.

End ProgASLPMonad.

Arguments retASLPSt {_} {_}.
Arguments bindASLPSt {_} {_} {_}.
Arguments getASLPSt {_} {_}.


(* ---- order and monotonicity ---- *)

Section StASLPOrders.
  Variable S : Type.
  Definition ordASLPSt {A} (m1 m2 : ASLPSt S A) : Prop :=
    forall pre r, getASLPSt m1 pre r -> getASLPSt m2 pre r.
  Lemma aslpMono {A} (w : ASLPSt S A) (P Q : S -> Prop) (r : (A * S)) :
    (forall s, P s -> Q s) -> getASLPSt w P r -> getASLPSt w Q r.
  Proof.
    exact (disjunctive_implies_monotone S (getASLPSt w) (proj2 (proj2_sig w)) P Q r).
  Qed.
  (** Inclusion of the recovered relation.  Unlike [ordASLPSt], [bind] is
      monotone for it; see [SpecificationMonads.v]. *)
  Definition ordASLPStRel {A} (m1 m2 : ASLPSt S A) : Prop :=
    forall s r,
      (~ getASLPSt m1 (fun _ => False) r /\ getASLPSt m1 (fun t => t = s) r) ->
      (~ getASLPSt m2 (fun _ => False) r /\ getASLPSt m2 (fun t => t = s) r).
End StASLPOrders.
Arguments ordASLPSt {_} {_}.
Arguments ordASLPStRel {_} {_}.
End StASLP.

(* ================================================================= *)
(** * Refinement order and monotonicity for ASLP *)
(* ================================================================= *)

Section ASLPOrders.
  Variable S : Type.
  Definition ordASLPStExc {A} (m1 m2 : ASLPStExc S A) : Prop :=
    forall pre r, getASLPStExc m1 pre r -> getASLPStExc m2 pre r.
  Lemma aslpMono {A} (w : ASLPStExc S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getASLPStExc w P r -> getASLPStExc w Q r.
  Proof.
    exact (disjunctive_implies_monotone S (getASLPStExc w) (proj2 (proj2_sig w)) P Q r).
  Qed.
  (** Inclusion of the recovered relation.  Unlike [ordASLPStExc], [bind] is
      monotone for it; see [SpecificationMonads.v]. *)
  Definition ordASLPStExcRel {A} (m1 m2 : ASLPStExc S A) : Prop :=
    forall s r,
      (~ getASLPStExc m1 (fun _ => False) r /\ getASLPStExc m1 (fun t => t = s) r) ->
      (~ getASLPStExc m2 (fun _ => False) r /\ getASLPStExc m2 (fun t => t = s) r).
End ASLPOrders.

Arguments ordASLPStExc {_} {_}.
Arguments ordASLPStExcRel {_} {_}.

(* ================================================================= *)
(** ** The reader-indexed variant                                    *)
(* ================================================================= *)

(** [ASLPRd R A = readerT R ASLPSP A]: one [ASLPSP] per environment.  The
    precondition slot stays a bare [Prop], so environments are specified
    INDEPENDENTLY — the pointwise lift, not a shared [R -> Prop].  Dually to [DSPRd], [ASLPSP] already collapses
    onto [DSLPSP], and this pointwise lift inherits that collapse.

    Laws come from the generic [readerT] instances in
    [ComputationMonads/TransformerLaws.v] over [Monad_ASLPSP]. *)

From ExtLib Require Import ReaderMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

Section RdASLPMonad.
  Variable R : Type.

  Definition ASLPRd (A : Type) : Type := readerT R ASLPSP A.

  Definition getASLPRd {A} (w : ASLPRd A) (r : R) : SPPure A :=
    getASLP (runReaderT w r).

  #[global] Instance Monad__ASLPRd : Monad ASLPRd :=
    @Monad_readerT R ASLPSP Monad_ASLPSP.

  #[global] Instance Eq1__ASLPRd : Eq1 ASLPRd :=
    Eq1_readerT R ASLPSP.

  #[global] Instance Eq1Equivalence__ASLPRd
    : @Eq1Equivalence ASLPRd _ Eq1__ASLPRd :=
    Eq1Equivalence_readerT R ASLPSP.

  #[global] Instance MonadLawsE__ASLPRd
    : @MonadLawsE ASLPRd Eq1__ASLPRd Monad__ASLPRd :=
    MonadLawsE_readerT R ASLPSP.

  Definition ordASLPRd {A} (m1 m2 : ASLPRd A) : Prop :=
    forall r p a, getASLPRd m1 r p a -> getASLPRd m2 r p a.
  Definition ordASLPRdAt {A} (pre : R -> Prop) (m1 m2 : ASLPRd A) : Prop :=
    forall r a, getASLPRd m1 r (pre r) a -> getASLPRd m2 r (pre r) a.

End RdASLPMonad.

Arguments getASLPRd {_} {_}.
