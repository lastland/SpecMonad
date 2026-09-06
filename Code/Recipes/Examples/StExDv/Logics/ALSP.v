(** * Angelic liberal strongest postcondition

    [obsASLP] is the DISJUNCTION of the angelic and the demonic-liberal
    readings of the observed relation: [r] is asserted at [pre] when some
    [pre]-state reaches [r] OR every state that reaches [r] is a [pre]-state.
    It is the terminating positively-join-preserving fragment of the ambient
    transformer space, and the De Morgan dual of [obsDSP]
    ([alsp_dsp_contrapositive]). *)

From Coq Require Import Lia RelationClasses Classical_Prop.
From ExtLib Require Import
  Monad MonadLaws MonadState MonadExc
  StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
From Hammer Require Import Tactics.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
From Incorrectness.Recipes Require Import DMRecipe Logic.
From Incorrectness.Recipes.Examples.StExDv Require Import
  Program SP PrePost Examples.
From Incorrectness.Recipes.Examples.StExDv.Logics Require Import ASP DLSP DSP.

Import MonadNotation.
Open Scope monad_scope.

Section ProgASLPMonad.
  Variable S : Type.

  Definition TerminatingPositivelyJoinPreserving {A} (w : ProgSP A) : Prop :=
    TerminatingProg S w /\ DisjunctiveProg S w.

  Definition ASLPProgSP (A : Type) : Type :=
    { w : ProgSP A | TerminatingPositivelyJoinPreserving w }.

  Definition getProgASLP {A} (w : ASLPProgSP A) : ProgSP A := proj1_sig w.

  Lemma aslp_recov {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
    (~ ((exists t, False /\ R t r) \/ (forall t, R t r -> False))
     /\ ((exists t, t = s /\ R t r) \/ (forall t, R t r -> t = s)))
    <-> R s r.
  Proof.
    split.
    - intros [Hne [[t [Heq Ht]] | Hall]]; [ subst t; exact Ht |].
      apply NNPP. intro Hns. apply Hne. right.
      intros t Ht. rewrite (Hall t Ht) in Ht. exact (Hns Ht).
    - intro Hs. split.
      + intros [[t [Hf _]] | Hall]; [ destruct Hf | exact (Hall s Hs) ].
      + left. exists s. split; [ reflexivity | exact Hs ].
  Qed.

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
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj1 (H s r) Hs) ].
      + right. intros s Hs. exact (Hall s (proj2 (H s r) Hs)).
    - intros [[s [Hp Hs]] | Hall].
      + left. exists s. split; [ exact Hp | exact (proj2 (H s r) Hs) ].
      + right. intros s Hs. exact (Hall s (proj1 (H s r) Hs)).
  Qed.

  Lemma aslp_rec_ext {A} (w1 w2 : @ProgSP S A)
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

  (** Dual of [dsp_carrier]: the healthiness condition that the type states is
      the same thing as "[w] is the ASLP of its own recovered relation", which
      is what the proofs use. *)
  Lemma aslp_carrier {A} (w : ProgSP A) :
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
  Proof. apply aslp_carrier. intros pre r. exact (aslp_wf R pre r). Qed.

  (** ... and every carrier element is the ASLP of its recovered relation. *)
  Lemma getProgASLP_carrier {A} (w : ASLPProgSP A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgASLP w pre r <->
      ((exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                            /\ getProgASLP w (fun t => t = s) r)) \/
         (forall s, (~ getProgASLP w (fun _ => False) r
                     /\ getProgASLP w (fun t => t = s) r) -> pre s)).
  Proof. exact (proj1 (aslp_carrier (getProgASLP w)) (proj2_sig w) pre r). Qed.

  #[program] Definition retASLPProg {A} (a : A) : ASLPProgSP A :=
    fun pre r => (retASPProg a pre r) \/ (retDSLPProg a pre r).
  Next Obligation. exact (aslp_shape_wf (fun s r => r = Some (a, s))). Qed.

  (** The two probe forms are the ASP and the DSLP of the recovered relation. *)
  Lemma aspPartaslp_closed {A} (w : ASLPProgSP A) pre r :
    (~ getProgASLP w (fun _ => False) r /\ getProgASLP w pre r)
    <-> (exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                             /\ getProgASLP w (fun t => t = s) r)).
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

  Lemma dslpPartaslp_closed {A} (w : ASLPProgSP A) pre r :
    (getProgASLP w (fun _ => False) r \/ ~ getProgASLP w (fun s => ~ pre s) r)
    <-> (forall s, (~ getProgASLP w (fun _ => False) r
                    /\ getProgASLP w (fun t => t = s) r) -> pre s).
  Proof.
    split.
    - intros [Hbot | Hn] s Hs.
      + exfalso. destruct (proj1 (getProgASLP_carrier w (fun _ => False) r) Hbot)
          as [[s0 [[] _]] | Hall]. exact (Hall s Hs).
      + apply NNPP. intro Hnp. apply Hn. apply getProgASLP_carrier. left.
        exists s. split; [ exact Hnp | exact Hs ].
    - intro Hall.
      destruct (classic (exists s, ~ getProgASLP w (fun _ => False) r
                                   /\ getProgASLP w (fun t => t = s) r)) as [[s0 Hs0] | Hno].
      + right. intro Hc.
        destruct (proj1 (getProgASLP_carrier w (fun t => ~ pre t) r) Hc)
          as [[s [Hnp Hs]] | Hev].
        * exact (Hnp (Hall s Hs)).
        * exact (Hev s0 Hs0 (Hall s0 Hs0)).
      + left. apply getProgASLP_carrier. right. intros s Hs.
        exfalso. exact (Hno (ex_intro _ s Hs)).
  Qed.

  Lemma singletonProg_ext' {A} (w1 w2 : @ProgSP S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
  Qed.

  Lemma aslp_healthy_ext {A} (w1 w2 : @ProgSP S A) :
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

  #[program] Definition aspPartaslp {A} (w : ASLPProgSP A) : ASPProgSP S A :=
    fun pre r => ~ getProgASLP w (fun _ => False) r /\ getProgASLP w pre r.
  Next Obligation.
    apply (singletonProg_ext'
             (fun pre r => exists s, pre s /\ (~ getProgASLP w (fun _ => False) r
                                               /\ getProgASLP w (fun t => t = s) r))).
    - intros pre r. exact (iff_sym (aspPartaslp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartaslp {A} (w : ASLPProgSP A) : DSLPProgSP S A :=
    fun pre r => getProgASLP w (fun _ => False) r \/ ~ getProgASLP w (fun s => ~ pre s) r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (~ getProgASLP w (fun _ => False) r
                                      /\ getProgASLP w (fun t => t = s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartaslp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem aslp_split {A} (w : ASLPProgSP A) pre r :
    getProgASLP w pre r <-> (getProgASP (aspPartaslp w) pre r \/ getProgDSLP (dslpPartaslp w) pre r).
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
  Lemma bind_asp_parts' {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgASP (bindASPProg (aspPartaslp m) (fun a => aspPartaslp (k a))) pre r
    <-> (exists s, pre s /\
           (exists o, (~ getProgASLP m (fun _ => False) o
                       /\ getProgASLP m (fun t => t = s) o)
                      /\ match o with
                         | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                             /\ getProgASLP (k a) (fun t => t = smid) r
                         | None => r = None
                         end)).
  Proof.
    split.
    - intros [[a Hk] | [Hr Hm]].
      + destruct (proj1 (aspPartaslp_closed (k a)
                           (fun s0 => getProgASP (aspPartaslp m) pre (Some (a, s0))) r) Hk)
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
                        (fun s0 => getProgASP (aspPartaslp m) pre (Some (a, s0))) r)
                 (ex_intro _ smid
                    (conj (proj2 (aspPartaslp_closed m pre (Some (a, smid)))
                             (ex_intro _ s (conj Hps Hrm))) Hrk))).
      + right. split; [ exact Hrk |].
        exact (proj2 (aspPartaslp_closed m pre None) (ex_intro _ s (conj Hps Hrm))).
  Qed.

  Lemma bind_dslp_parts' {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgDSLP (bindDSLPProg (dslpPartaslp m) (fun a => dslpPartaslp (k a))) pre r
    <-> (forall s,
           (exists o, (~ getProgASLP m (fun _ => False) o
                       /\ getProgASLP m (fun t => t = s) o)
                      /\ match o with
                         | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                             /\ getProgASLP (k a) (fun t => t = smid) r
                         | None => r = None
                         end) -> pre s).
  Proof.
    split.
    - intros [H1 H2] s [[[a smid]|] [Hrm Hrk]].
      + exact (proj1 (dslpPartaslp_closed m pre (Some (a, smid)))
                 (proj1 (dslpPartaslp_closed (k a)
                           (fun s0 => getProgDSLP (dslpPartaslp m) pre (Some (a, s0))) r)
                    (H1 a) smid Hrk) s Hrm).
      + exact (proj1 (dslpPartaslp_closed m pre None) (H2 Hrk) s Hrm).
    - intro H. split.
      + intro a.
        exact (proj2 (dslpPartaslp_closed (k a)
                        (fun s0 => getProgDSLP (dslpPartaslp m) pre (Some (a, s0))) r)
                 (fun smid Hrk =>
                    proj2 (dslpPartaslp_closed m pre (Some (a, smid)))
                      (fun s Hrm => H s (ex_intro _ (Some (a, smid)) (conj Hrm Hrk))))).
      + intro Hr.
        exact (proj2 (dslpPartaslp_closed m pre None)
                 (fun s Hrm => H s (ex_intro _ None (conj Hrm Hr)))).
  Qed.

  #[program] Definition bindASLPProg {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) : ASLPProgSP B :=
    fun pre r => bindASPProg (aspPartaslp m) (fun a => aspPartaslp (k a)) pre r \/
                   bindDSLPProg (dslpPartaslp m) (fun a => dslpPartaslp (k a)) pre r.
  Next Obligation.
    apply (aslp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists o, (~ getProgASLP m (fun _ => False) o
                               /\ getProgASLP m (fun t => t = s) o)
                              /\ match o with
                                 | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                                     /\ getProgASLP (k a) (fun t => t = smid) r
                                 | None => r = None
                                 end))
                \/ (forall s,
                      (exists o, (~ getProgASLP m (fun _ => False) o
                                  /\ getProgASLP m (fun t => t = s) o)
                                 /\ match o with
                                    | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                                        /\ getProgASLP (k a) (fun t => t = smid) r
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

  (** [bindASLPProg m k] is pointwise the ASLP of the composite relation. *)
  Lemma bindASLPProg_aslp {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) pre r :
    getProgASLP (bindASLPProg m k) pre r
    <-> ((exists s, pre s /\
            (exists o, (~ getProgASLP m (fun _ => False) o
                        /\ getProgASLP m (fun t => t = s) o)
                       /\ match o with
                          | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                              /\ getProgASLP (k a) (fun t => t = smid) r
                          | None => r = None
                          end))
         \/ (forall s,
               (exists o, (~ getProgASLP m (fun _ => False) o
                           /\ getProgASLP m (fun t => t = s) o)
                          /\ match o with
                             | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                                 /\ getProgASLP (k a) (fun t => t = smid) r
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
    (~ getProgASLP (retASLPProg a) (fun _ => False) r
     /\ getProgASLP (retASLPProg a) (fun t => t = s) r)
    <-> r = Some (a, s).
  Proof. exact (aslp_recov (fun s0 r0 => r0 = Some (a, s0)) s r). Qed.

  Lemma rec_bindASLPProg {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B)
    (s : S) (r : option (B * S)) :
    (~ getProgASLP (bindASLPProg m k) (fun _ => False) r
     /\ getProgASLP (bindASLPProg m k) (fun t => t = s) r)
    <-> (exists o, (~ getProgASLP m (fun _ => False) o
                    /\ getProgASLP m (fun t => t = s) o)
                   /\ match o with
                      | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                          /\ getProgASLP (k a) (fun t => t = smid) r
                      | None => r = None
                      end).
  Proof.
    refine (iff_trans (aslp_rec_ext _ _ (bindASLPProg_aslp m k) s r)
              (aslp_recov
                 (fun s0 r0 =>
                    exists o, (~ getProgASLP m (fun _ => False) o
                               /\ getProgASLP m (fun t => t = s0) o)
                              /\ match o with
                                 | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r0
                                                     /\ getProgASLP (k a) (fun t => t = smid) r0
                                 | None => r0 = None
                                 end)
                 s r)).
  Qed.


  #[global]
    Instance Monad__ASLPProgSP : Monad ASLPProgSP :=
    {| ret := fun _ => @retASLPProg _ ;
      bind := fun _ _ => @bindASLPProg _ _ |}.

  #[global] Instance Eq1__ProgASLP : Eq1 ASLPProgSP :=
    fun A m n => forall pre r, getProgASLP m pre r <-> getProgASLP n pre r.

  #[global] Instance Eq1Equivalence__ASLPProgSP
    : @Eq1Equivalence ASLPProgSP _ Eq1__ProgASLP.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLaws__ProgASLP
    : @MonadLawsE ASLPProgSP Eq1__ProgASLP _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__ProgASLP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (~ getProgASLP (retASLPProg x) (fun _ => False) o
                             /\ getProgASLP (retASLPProg x) (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (f a) (fun _ => False) r0
                                   /\ getProgASLP (f a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (~ getProgASLP (f x) (fun _ => False) r0
                      /\ getProgASLP (f x) (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP (retASLPProg x) (fun _ => False) r1
                                  /\ getProgASLP (retASLPProg x) (fun t => t = s1) r1)
                    (fun s1 r1 => r1 = Some (x, s1))
                    (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                     /\ getProgASLP (f a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                     /\ getProgASLP (f a1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_retASLPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l S x
                    (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                     /\ getProgASLP (f a1) (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp (retASLPProg x) f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier (f x) pre r)))).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__ProgASLP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (A * S)),
                 (exists o, (~ getProgASLP m (fun _ => False) o
                             /\ getProgASLP m (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (retASLPProg a) (fun _ => False) r0
                                   /\ getProgASLP (retASLPProg a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (~ getProgASLP m (fun _ => False) r0
                      /\ getProgASLP m (fun t => t = s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP m (fun _ => False) r1
                                  /\ getProgASLP m (fun t => t = s1) r1)
                    (fun s1 r1 => ~ getProgASLP m (fun _ => False) r1
                                  /\ getProgASLP m (fun t => t = s1) r1)
                    (fun a1 s1 r1 => ~ getProgASLP (retASLPProg a1) (fun _ => False) r1
                                     /\ getProgASLP (retASLPProg a1) (fun t => t = s1) r1)
                    (fun a1 s1 r1 => r1 = Some (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retASLPProg a1 s1 r1) s r0)
                 (comp_ret_r S
                    (fun s1 r1 => ~ getProgASLP m (fun _ => False) r1
                                  /\ getProgASLP m (fun t => t = s1) r1)
                    s r0)). }
      exact (iff_trans (bindASLPProg_aslp m _ pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (getProgASLP_carrier m pre r)))).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__ProgASLP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (C * S)),
                 (exists o, (~ getProgASLP (bindASLPProg x f) (fun _ => False) o
                             /\ getProgASLP (bindASLPProg x f) (fun t => t = s) o)
                            /\ match o with
                               | Some (b, smid) =>
                                   ~ getProgASLP (g b) (fun _ => False) r0
                                   /\ getProgASLP (g b) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (~ getProgASLP x (fun _ => False) o
                                 /\ getProgASLP x (fun t => t = s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       ~ getProgASLP (bindASLPProg (f a) g)
                                           (fun _ => False) r0
                                       /\ getProgASLP (bindASLPProg (f a) g)
                                            (fun t => t = smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong S
                    (fun s1 r1 => ~ getProgASLP (bindASLPProg x f) (fun _ => False) r1
                                  /\ getProgASLP (bindASLPProg x f) (fun t => t = s1) r1)
                    (fun s1 r1 =>
                       exists o, (~ getProgASLP x (fun _ => False) o
                                  /\ getProgASLP x (fun t => t = s1) o)
                                 /\ match o with
                                    | Some (a, smid) =>
                                        ~ getProgASLP (f a) (fun _ => False) r1
                                        /\ getProgASLP (f a) (fun t => t = smid) r1
                                    | None => r1 = None
                                    end)
                    (fun b1 s1 r1 => ~ getProgASLP (g b1) (fun _ => False) r1
                                     /\ getProgASLP (g b1) (fun t => t = s1) r1)
                    (fun b1 s1 r1 => ~ getProgASLP (g b1) (fun _ => False) r1
                                     /\ getProgASLP (g b1) (fun t => t = s1) r1)
                    (fun s1 r1 => rec_bindASLPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc S
                       (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                                     /\ getProgASLP x (fun t => t = s1) r1)
                       (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                        /\ getProgASLP (f a1) (fun t => t = s1) r1)
                       (fun b1 s1 r1 => ~ getProgASLP (g b1) (fun _ => False) r1
                                        /\ getProgASLP (g b1) (fun t => t = s1) r1)
                       s r0)
                    (comp_cong S
                       (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                                     /\ getProgASLP x (fun t => t = s1) r1)
                       (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                                     /\ getProgASLP x (fun t => t = s1) r1)
                       (fun a1 s1 r1 =>
                          exists o, (~ getProgASLP (f a1) (fun _ => False) o
                                     /\ getProgASLP (f a1) (fun t => t = s1) o)
                                    /\ match o with
                                       | Some (b, smid) =>
                                           ~ getProgASLP (g b) (fun _ => False) r1
                                           /\ getProgASLP (g b) (fun t => t = smid) r1
                                       | None => r1 = None
                                       end)
                       (fun a1 s1 r1 =>
                          ~ getProgASLP (bindASLPProg (f a1) g) (fun _ => False) r1
                          /\ getProgASLP (bindASLPProg (f a1) g) (fun t => t = s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindASLPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindASLPProg_aslp (bindASLPProg x f) g pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp x (fun a => bindASLPProg (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgASLP in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (~ getProgASLP x (fun _ => False) o
                             /\ getProgASLP x (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (f a) (fun _ => False) r0
                                   /\ getProgASLP (f a) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (~ getProgASLP y (fun _ => False) o
                                 /\ getProgASLP y (fun t => t = s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       ~ getProgASLP (g a) (fun _ => False) r0
                                       /\ getProgASLP (g a) (fun t => t = smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (comp_cong S
                 (fun s1 r1 => ~ getProgASLP x (fun _ => False) r1
                               /\ getProgASLP x (fun t => t = s1) r1)
                 (fun s1 r1 => ~ getProgASLP y (fun _ => False) r1
                               /\ getProgASLP y (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getProgASLP (f a1) (fun _ => False) r1
                                  /\ getProgASLP (f a1) (fun t => t = s1) r1)
                 (fun a1 s1 r1 => ~ getProgASLP (g a1) (fun _ => False) r1
                                  /\ getProgASLP (g a1) (fun t => t = s1) r1)
                 (fun s1 r1 => aslp_rec_ext (getProgASLP x) (getProgASLP y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    aslp_rec_ext (getProgASLP (f a1)) (getProgASLP (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindASLPProg_aslp x f pre r)
               (iff_trans (aslp_cong _ _ Hc pre r)
                  (iff_sym (bindASLPProg_aslp y g pre r)))).
  Qed.
End ProgASLPMonad.

Arguments retASLPProg {_} {_}.
Arguments bindASLPProg {_} {_} {_}.
Arguments getProgASLP {_} {_}.

(* ==================================================================== *)
(** * Refinement order and comparison targets                            *)
(* ==================================================================== *)

Section SpecOrdersASLP.
  Variable S : Type.

  Definition ordProgASLP {A} (m1 m2 : ASLPProgSP S A) : Prop :=
    forall pre r, getProgASLP m1 pre r -> getProgASLP m2 pre r.
  Lemma aslpMono {A} (w : ASLPProgSP S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getProgASLP w P r -> getProgASLP w Q r.
  Proof.
    intros Hsub Hw.
    destruct (proj1 (getProgASLP_carrier S w P r) Hw) as [[s [Hp Hrec]] | Hall].
    - apply getProgASLP_carrier. left.
      exists s. split; [ exact (Hsub s Hp) | exact Hrec ].
    - apply getProgASLP_carrier. right.
      intros s' Hrec'. exact (Hsub s' (Hall s' Hrec')).
  Qed.
  Theorem gen_aslp_over_raw {A} (w : ASLPProgSP S A) pre post :
    (forall r, getProgASLP w pre r -> post r)
    <-> ordProgSP (getProgASLP w) (pp2_over pre post).
  Proof.
    split.
    - intros H p r Hw Hsub. exact (H r (aslpMono w p pre r Hsub Hw)).
    - intros H r Hw. exact (H pre r Hw (fun s Hs => Hs)).
  Qed.

  Theorem gen_aslp_under_raw {A} (w : ASLPProgSP S A) pre post :
    (forall r, post r -> getProgASLP w pre r)
    <-> ordProgSP (pp2_under pre post) (getProgASLP w).
  Proof.
    split.
    - intros H p r [Hsub Hpost]. exact (aslpMono w pre p r Hsub (H r Hpost)).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
  Qed.
End SpecOrdersASLP.

Arguments ordProgASLP {_} {_}.

(* ==================================================================== *)
(** * The angelic-liberal recipe layer                                   *)
(* ==================================================================== *)

Section ASLPRecipes.

  Variable S : Type.

  #[program] Definition aslpOf {A} (R : SPRel S A) : ASLPProgSP S A :=
    fun pre r => (exists s, pre s /\ R s r) \/ (forall s, R s r -> pre s).
  Next Obligation. exact (aslp_shape_wf S R). Qed.

  Definition aslpRel {A} (w : ASLPProgSP S A) : SPRel S A :=
    fun s r =>
      ~ getProgASLP w (fun _ => False) r /\ getProgASLP w (fun t => t = s) r.

  Lemma aslpRel_of {A} (R : SPRel S A) :
    forall s r, aslpRel (aslpOf R) s r <-> R s r.
  Proof. intros s r. exact (aslp_recov S R s r). Qed.

  Lemma aslpOf_rel {A} (w : ASLPProgSP S A) (pre : S -> Prop) r :
    getProgASLP w pre r <-> getProgASLP (aslpOf (aslpRel w)) pre r.
  Proof. exact (getProgASLP_carrier S w pre r). Qed.

  Definition aslpLe : OrderM (ASLPProgSP S) :=
    fun A w1 w2 => relLe (aslpRel w1) (aslpRel w2).

  #[global] Instance OrderedMonad_ASLPProgSP :
    @OrderedMonad (ASLPProgSP S) (Monad__ASLPProgSP S) aslpLe.
  Proof.
    constructor.
    - intros A w s r H. exact H.
    - intros A x y z Hxy Hyz s r H. exact (Hyz s r (Hxy s r H)).
    - intros A B x y f g Hxy Hfg s r H.
      apply (rec_bindASLPProg S y g s r).
      apply (compRel_mono (aslpRel x) (aslpRel y)
               (fun a => aslpRel (f a)) (fun a => aslpRel (g a)) Hxy Hfg).
      exact (proj1 (rec_bindASLPProg S x f s r) H).
  Qed.

  Lemma eqLeASLP {A} (x y : ASLPProgSP S A) :
    @eq1 (ASLPProgSP S) (Eq1__ProgASLP S) A x y -> aslpLe A x y.
  Proof.
    intros H s r [Hbot Hs]. split.
    - intro Hc. exact (Hbot (proj2 (H (fun _ => False) r) Hc)).
    - exact (proj1 (H (fun t => t = s) r) Hs).
  Qed.

  Definition truthASLP : TruthOrder (ASLPProgSP S) aslpLe.
  Proof.
    refine {| trueW := fun A => aslpOf (fun (_ : S) (_ : option (A * S)) => True);
              falseW := fun A => aslpOf (fun (_ : S) (_ : option (A * S)) => False);
              truthPolarity := Forward |}.
    intros A w. split.
    - intros s r H. destruct (proj1 (aslpRel_of _ s r) H).
    - intros s r H. apply aslpRel_of. exact I.
  Defined.

  Definition makeASLPDM
    (observation : EffectObs (prog S) (ASLPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (ASLPProgSP S)
        (Monad__nditprog S) (Monad__ASLPProgSP S) (Eq1__ProgASLP S) observation)
    : DMRecipe (prog S) (ASLPProgSP S) :=
    {| monadM := Monad__nditprog S;
       eqM := Eq1__nditprog S;
       eqEquivM := Eq1Equivalence_nditprog S;
       lawsM := MonadLawsE__nditprog S;
       monadW := Monad__ASLPProgSP S;
       eqW := Eq1__ProgASLP S;
       eqEquivW := Eq1Equivalence__ASLPProgSP S;
       lawsW := MonadLaws__ProgASLP S;
       orderW := aslpLe;
       orderedW := OrderedMonad_ASLPProgSP;
       eqLeW := @eqLeASLP;
       truthOrder := truthASLP;
       theta := observation;
       thetaMorphism := morphism |}.

  Definition logicASLP
    (observation : EffectObs (prog S) (ASLPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (ASLPProgSP S)
        (Monad__nditprog S) (Monad__ASLPProgSP S) (Eq1__ProgASLP S) observation)
    : Logic (makeASLPDM observation morphism).
  Proof.
    refine {|
      meetW := fun A x y => aslpOf (fun s r => aslpRel x s r /\ aslpRel y s r);
      joinW := fun A x y => aslpOf (fun s r => aslpRel x s r \/ aslpRel y s r)
    |}.
    - intros A x y z. cbn. unfold aslpLe, relLe. split.
      + intro H. split; intros s r Hx;
          [ exact (proj1 (proj1 (aslpRel_of _ s r) (H s r Hx)))
          | exact (proj2 (proj1 (aslpRel_of _ s r) (H s r Hx))) ].
      + intros [Hy Hz] s r Hx. apply aslpRel_of.
        split; [exact (Hy s r Hx) | exact (Hz s r Hx)].
    - intros A x y z. cbn. unfold aslpLe, relLe. split.
      + intro H. split; intros s r Hw; apply H; apply aslpRel_of;
          [left | right]; exact Hw.
      + intros [Hx Hy] s r Hw.
        destruct (proj1 (aslpRel_of _ s r) Hw) as [H | H];
          [exact (Hx s r H) | exact (Hy s r H)].
  Defined.

  Definition makeASLPRecipe
    (observation : EffectObs (prog S) (ASLPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (ASLPProgSP S)
        (Monad__nditprog S) (Monad__ASLPProgSP S) (Eq1__ProgASLP S) observation)
    : LogicRecipe (prog S) (ASLPProgSP S) :=
    {| recipeDM := makeASLPDM observation morphism;
       recipeLogic := logicASLP observation morphism |}.

  (** The demonic and the angelic-liberal readings of one relation are De
      Morgan duals, exactly as the angelic and demonic-liberal ones are
      ([aspOf_dslpOf_contrapositive] in [Logics/DLSP.v]). *)
  Theorem dspOf_aslpOf_contrapositive {A} (R : SPRel S A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgDSP (dspOf R) pre r <->
      ~ getProgASLP (aslpOf R) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [Hasp Hdslp] [[s [Hnp Hr]] | Hall].
      + exact (Hnp (Hdslp s Hr)).
      + destruct Hasp as [s [Hp Hr]]. exact (Hall s Hr Hp).
    - intro H. split.
      + apply (aspOf_dslpOf_contrapositive S R pre r).
        intro Hd. apply H. right.
        intros s Hr Hp. exact (Hd s Hr Hp).
      + intros s Hr. apply NNPP. intro Hnp. apply H. left.
        exists s. split; [exact Hnp | exact Hr].
  Qed.

End ASLPRecipes.

Arguments aslpOf {_} {_}.
Arguments aslpRel {_} {_}.
Arguments aslpLe {_} {_}.

Definition aslpMonoSP {S A} (w : ASLPProgSP S A) : MonoSP (getProgASLP w) :=
  aslpMono S w.

(* ==================================================================== *)
(** * The observation                                                    *)
(* ==================================================================== *)

(** The disjunction of the angelic and the demonic-liberal readings of the
    same terminating slice.  [TerminatingPositivelyJoinPreserving] holds
    because that disjunction is exactly the ASLP shape established above. *)
#[program] Definition obsASLP {S A} (m : prog S A) : ASLPProgSP S A :=
  fun pre r => (obsASP m pre r) \/ (obsDSLP m pre r).
Next Obligation.
  exact (aslp_shape_wf S
           (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
Qed.

Lemma getProgASLP_obsASLP {S A} (m : prog S A) pre r :
  getProgASLP (obsASLP m) pre r
  <-> ((exists s, pre s /\ obsRel m s r) \/ (forall s, obsRel m s r -> pre s)).
Proof. split; intro H; exact H. Qed.

(** [obsASLP m] is the ASLP of exactly the relation [obsRel m]. *)
Lemma aslpRel_obsASLP {S A} (m : prog S A) :
  forall s r, aslpRel (obsASLP m) s r <-> obsRel m s r.
Proof. intros s r. exact (aslp_recov S (obsRel m) s r). Qed.

Theorem obsASLP_ret {S A} (a : A) :
  eq1 (obsASLP (ret a : prog S A)) (ret a).
Proof.
  unfold eq1, Eq1__ProgASLP. intros pre r.
  apply (aslp_cong S
           (fun s r0 => unOptionT (unOptionT (runStateT (ret a : prog S A) s))
                          (Some r0))
           (fun s r0 => r0 = Some (a, s))).
  intros s r0. destruct r0 as [[b s']|]; cbn; split; intro H; congruence.
Qed.

Theorem obsASLP_bind {S A B} (x : prog S A) (f : A -> prog S B) :
  eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
Proof.
  unfold eq1, Eq1__ProgASLP. intros pre r.
  assert (Hx : forall s y,
             (~ getProgASLP (obsASLP x) (fun _ => False) y
              /\ getProgASLP (obsASLP x) (fun t => t = s) y)
             <-> unOptionT (unOptionT (runStateT x s)) (Some y)).
  { intros s y.
    exact (aslp_recov S
             (fun s1 r1 => unOptionT (unOptionT (runStateT x s1)) (Some r1)) s y). }
  assert (Hf : forall a s y,
             (~ getProgASLP (obsASLP (f a)) (fun _ => False) y
              /\ getProgASLP (obsASLP (f a)) (fun t => t = s) y)
             <-> unOptionT (unOptionT (runStateT (f a) s)) (Some y)).
  { intros a s y.
    exact (aslp_recov S
             (fun s1 r1 => unOptionT (unOptionT (runStateT (f a) s1)) (Some r1)) s y). }
  refine (iff_trans
            (aslp_cong S
               (fun s r0 => unOptionT (unOptionT (runStateT (x >>= f) s)) (Some r0))
               (fun s r0 =>
                  exists o, (~ getProgASLP (obsASLP x) (fun _ => False) o
                             /\ getProgASLP (obsASLP x) (fun t => t = s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   ~ getProgASLP (obsASLP (f a)) (fun _ => False) r0
                                   /\ getProgASLP (obsASLP (f a)) (fun t => t = smid) r0
                               | None => r0 = None
                               end)
               _ pre r)
            (iff_sym (bindASLPProg_aslp S (obsASLP x) (fun a => obsASLP (f a)) pre r))).
  intros s r0. split.
  - intro H. apply (obsRel_bind x f) in H. destruct H as [o [Hxx Hk]].
    destruct o as [[a s']|].
    + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
    + exists None. split; [ apply Hx; exact Hxx | exact Hk ].
  - intros [[[a s']|] [Hm Hk]].
    + apply Hx in Hm. apply Hf in Hk. apply (obsRel_bind x f).
      exists (Some (a, s')). split; [ exact Hm | exact Hk ].
    + apply Hx in Hm. apply (obsRel_bind x f).
      exists None. split; [ exact Hm | exact Hk ].
Qed.

#[global] Instance aslpMorphism (S : Type) :
  @MonadMorphism (prog S) (ASLPProgSP S)
    (Monad__nditprog S) (Monad__ASLPProgSP S) (Eq1__ProgASLP S) (@obsASLP S).
Proof.
  constructor.
  - intros A a. apply obsASLP_ret.
  - intros A B m k. apply obsASLP_bind.
Qed.

Definition aslpRecipe (S : Type) : LogicRecipe (prog S) (ASLPProgSP S) :=
  makeASLPRecipe S (@obsASLP S) (aslpMorphism S).

(* ==================================================================== *)
(** * The logic                                                          *)
(* ==================================================================== *)

Definition alspPPApproxOps (S : Type) `{DS : DefaultState S}
  (direction : Direction) :
  @ApproxOps (prog S) (ASLPProgSP S) direction
    (aslpRecipe S) (PP S) :=
  spPPApproxOps direction (aslpRecipe S) (fun A => @getProgASLP S A).

#[global] Existing Instance alspPPApproxOps.

Definition ALSPTriple {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  Approx direction (aslpRecipe S) m (unaryPP pre post).

Theorem alsp_over_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ALSPTriple Over m pre post <->
  forall r,
    ((exists s, pre s /\ obsRel m s r) \/ (forall s, obsRel m s r -> pre s)) ->
    post r.
Proof. reflexivity. Qed.

Theorem alsp_under_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ALSPTriple Under m pre post <->
  forall r,
    post r ->
    (exists s, pre s /\ obsRel m s r) \/ (forall s, obsRel m s r -> pre s).
Proof. reflexivity. Qed.

Theorem alsp_triple_raw {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  ALSPTriple direction m pre post <->
  match direction with
  | Over => ordProgSP (getProgASLP (obsASLP m)) (pp2_over pre post)
  | Under => ordProgSP (pp2_under pre post) (getProgASLP (obsASLP m))
  end.
Proof.
  destruct direction.
  - exact (sp_over_raw (getProgASLP (obsASLP m)) (aslpMonoSP (obsASLP m)) pre post).
  - exact (sp_under_raw (getProgASLP (obsASLP m)) (aslpMonoSP (obsASLP m)) pre post).
Qed.

(** The De Morgan duality with the demonic reading.  This is the first place
    where both observations are in scope, so the instance of
    [dspOf_aslpOf_contrapositive] lives here. *)

Section ContrapositiveTransformers.
  Variable S : Type.

  Theorem obsDSP_contrapositive {A} (m : prog S A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgDSP (obsDSP m) pre r <->
      ~ getProgASLP (obsASLP m) (fun x => ~ pre x) r.
  Proof. exact (dspOf_aslpOf_contrapositive S (obsRel m) pre r). Qed.

End ContrapositiveTransformers.

Theorem alsp_dsp_contrapositive {S A} (m : prog S A)
  (pre : S -> Prop) (r : option (A * S)) :
  getProgDSP (obsDSP m) pre r <->
    ~ getProgASLP (obsASLP m) (fun x => ~ pre x) r.
Proof. exact (obsDSP_contrapositive S m pre r). Qed.

(* ==================================================================== *)
(** * Examples                                                           *)
(* ==================================================================== *)

Definition alspOnly {A} (wanted : A) : A -> Prop :=
  fun actual => actual = wanted.

Theorem progEx_alsp_1 :
  ALSPTriple Under progEx P0 (alspOnly (Some (tt, 1))).
Proof.
  apply alsp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 1)) in Hpost. subst r.
  left. exists 0. split; [reflexivity|].
  unfold obsRel, progEx, orP. cbn. sauto limit: 200.
Qed.

Theorem progEx_alsp_42 :
  ALSPTriple Under progEx P0 (alspOnly (Some (tt, 42))).
Proof.
  apply alsp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 42)) in Hpost. subst r.
  left. exists 0. split; [reflexivity|].
  unfold obsRel, progEx, orP. cbn. sauto limit: 200.
Qed.

(** Unreachable outcomes are asserted through the liberal disjunct. *)
Theorem progEx_alsp_None :
  ALSPTriple Under progEx P0
    (alspOnly (None : option (unit * nat))).
Proof.
  apply alsp_under_spec.
  intros r Hpost.
  change (r = None) in Hpost. subst r.
  right. intros s Hrel.
  unfold obsRel, progEx, orP in Hrel. cbn in Hrel.
  sauto limit: 200.
Qed.

(** [Some (tt, 99)] is reachable, but only from outside [P0], so NEITHER
    disjunct holds. *)
Theorem progEx_alsp_not_99 :
  ~ ALSPTriple Under progEx P0 (alspOnly (Some (tt, 99))).
Proof.
  intro H. apply alsp_under_spec in H.
  assert (Hpost : alspOnly (Some (tt, 99)) (Some (tt, 99))).
  { reflexivity. }
  destruct (H (Some (tt, 99)) Hpost) as [Hex | Hall].
  - destruct Hex as [s [Hs Hreach]].
    change (s = 0) in Hs. subst s.
    unfold obsRel, progEx, orP in Hreach. cbn in Hreach.
    sauto lq: on limit: 200.
  - specialize (Hall 98).
    assert (Hreach : obsRel progEx 98 (Some (tt, 99))).
    { unfold obsRel, progEx, orP. cbn. sauto limit: 200. }
    specialize (Hall Hreach). discriminate.
Qed.
