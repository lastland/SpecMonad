From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** The pure variant                                              *)
(* ================================================================= *)

(** At [SPPure] the precondition is a [Prop], and the DSP carrier condition
    [Strict /\ Conjunctive] turns out to be EQUIVALENT to the ASP one
    ([Singleton]) — see [strict_conj_iff_singleton] below.  [Strict] alone
    already forces [Singleton] ([strict_to_singleton]), and [Singleton] gives
    both connectives back ([singleton_to_join], [singleton_to_conjunctive]).

    So [DSPSP] is not a new monad: it is [ASPSP] under a different
    presentation of the same subset of [SPPure].  Its monad structure is
    therefore transported along that equivalence rather than rebuilt — none of
    the relation-recovery machinery that [DSPStExc] needs is required here,
    because the degeneracy that makes DSP interesting (a precondition that is
    a SET of states, so that [R⁻¹(r) ⊆ pre] carries more information than
    [R⁻¹(r) ∩ pre ≠ ∅]) is exactly what disappears when the state is
    dropped. *)

Section PureDSPMonad.

  Definition StrictConjunctive {A} (w : SPPure A) : Prop :=
    Strict w /\ Conjunctive w.

  Definition DSPSP (A : Type) : Type := { w : SPPure A | StrictConjunctive w }.

  Definition getDSP {A} (w : DSPSP A) : SPPure A := proj1_sig w.

  Theorem strict_conj_iff_singleton {A} (w : SPPure A) :
    StrictConjunctive w <-> Singleton w.
  Proof.
    split.
    - intros [HS _]. exact (strict_to_singleton w HS).
    - intro H. split;
        [ exact (proj1 (singleton_to_join w H))
        | exact (singleton_to_conjunctive w H) ].
  Qed.

  (** The transports.  Both are the identity on the underlying transformer, so
      every law below is the corresponding [ASPSP] law read through them. *)

  Definition asp_to_dsp {A} (w : ASPSP A) : DSPSP A :=
    exist _ (getASP w) (proj2 (strict_conj_iff_singleton (getASP w)) (proj2_sig w)).

  Definition dsp_to_asp {A} (w : DSPSP A) : ASPSP A :=
    exist _ (getDSP w) (proj1 (strict_conj_iff_singleton (getDSP w)) (proj2_sig w)).

  Lemma getDSP_asp_to_dsp {A} (w : ASPSP A) p a :
    getDSP (asp_to_dsp w) p a <-> getASP w p a.
  Proof. split; intro H; exact H. Qed.

  Lemma getASP_dsp_to_asp {A} (w : DSPSP A) p a :
    getASP (dsp_to_asp w) p a <-> getDSP w p a.
  Proof. split; intro H; exact H. Qed.

  Definition retDSP {A} (v : A) : DSPSP A := asp_to_dsp (retASP v).

  Definition bindDSP {A B} (m : DSPSP A) (k : A -> DSPSP B) : DSPSP B :=
    asp_to_dsp (bindASP (dsp_to_asp m) (fun a => dsp_to_asp (k a))).

  #[global] Instance Monad_DSPSP : Monad DSPSP :=
    {| ret := fun _ => retDSP ;
      bind := fun _ _ => bindDSP |}.

  #[global] Instance Eq1_DSPSP : Eq1 DSPSP :=
    fun A m n => forall p a, getDSP m p a <-> getDSP n p a.

  #[global] Instance Eq1Equivalence_DSPSP
    : @Eq1Equivalence DSPSP _ Eq1_DSPSP.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a); specialize (H2 p a). tauto.
  Qed.

  #[global] Instance MonadLawsE_DSPSP : @MonadLawsE DSPSP Eq1_DSPSP _.
  Proof.
    destruct (@MonadLawsE_ASPSP) as [Lbrl Lbrr Lbb Lpb].
    constructor.
    - intros A B f x. exact (Lbrl A B (fun a => dsp_to_asp (f a)) x).
    - intros A x. exact (Lbrr A (dsp_to_asp x)).
    - intros A B C x f g.
      exact (Lbb A B C (dsp_to_asp x) (fun a => dsp_to_asp (f a))
               (fun b => dsp_to_asp (g b))).
    - intros A B x y Hxy f g Hfg.
      exact (Lpb A B (dsp_to_asp x) (dsp_to_asp y) Hxy
               (fun a => dsp_to_asp (f a)) (fun a => dsp_to_asp (g a)) Hfg).
  Qed.

  Definition ordDSPSP {A} (m1 m2 : DSPSP A) : Prop :=
    forall p a, getDSP m1 p a -> getDSP m2 p a.
  Definition ordDSPSPAt {A} (pre : Prop) (m1 m2 : DSPSP A) : Prop :=
    forall a, getDSP m1 pre a -> getDSP m2 pre a.

End PureDSPMonad.

Section ProgDSPMonad.
  Variable S : Type.

  Definition StrictPositivelyMeetPreservingProg {A} (w : SPStExc A) : Prop :=
    StrictProg S w /\ ConjunctiveProg S w.
  
  Definition DSPStExc (A : Type) : Type :=
    { w : SPStExc A | StrictPositivelyMeetPreservingProg w }.

  Definition getDSPStExc {A} (w : DSPStExc A) : SPStExc A := proj1_sig w.

  (** ** Recovery, well-formedness, congruence

      Everything below is stated about the raw transformer
      [fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)]
      and about the composite relation, written out; no auxiliary definitions
      are introduced. *)

  (** Probing that transformer at [fun _ => True] and at the co-singleton of
      [s] recovers [R s r] exactly. The forward direction uses classical
      logic: some state reaches [r], and excluding [s] invalidates the
      precondition, so [s] itself must reach [r]. *)
  Lemma dsp_recov {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
    (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
     /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s)))
    <-> R s r.
  Proof.
    split.
    - intros [[[t [_ Ht]] _] Hn]. apply NNPP. intro Hns. apply Hn. split.
      + exists t. split; [ intro Heq; subst t; exact (Hns Ht) | exact Ht ].
      + intros t' Ht' Heq. subst t'. exact (Hns Ht').
    - intro Hs. split.
      + split; [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
      + intros [_ Hall]. exact (Hall s Hs eq_refl).
  Qed.

  (** The DSP shape at [R] is pointwise the DSP of the relation recovered
      from it by probing ([dsp_recov]). *)
  Lemma dsp_wf {A} (R : S -> option (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : option (A * S)),
      ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\
              (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
               /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s))))
           /\ (forall s,
                 (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
                  /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s)))
                 -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj2 (dsp_recov R s r) Hs) ].
      + intros s' H. exact (Hall s' (proj1 (dsp_recov R s' r) H)).
    - intros [[s [Hp H]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj1 (dsp_recov R s r) H) ].
      + intros s' Hs'. exact (Hall s' (proj2 (dsp_recov R s' r) Hs')).
  Qed.

  (** Extensionally equal relations give extensionally equal transformers. *)
  Lemma dsp_cong {A} (R R' : S -> option (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : option (A * S)),
      ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\ R' s r) /\ (forall s, R' s r -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj1 (H s r) Hs) ].
      + intros s' Hs'. exact (Hall s' (proj2 (H s' r) Hs')).
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj2 (H s r) Hs) ].
      + intros s' Hs'. exact (Hall s' (proj1 (H s' r) Hs')).
  Qed.

  (** ... and extensionally equal transformers recover the same relation. *)
  Lemma dsp_rec_ext {A} (w1 w2 : @SPStExc S A)
    (H : forall pre r, w1 pre r <-> w2 pre r) :
    forall (s : S) (r : option (A * S)),
      (w1 (fun _ => True) r /\ ~ w1 (fun t => t <> s) r)
      <-> (w2 (fun _ => True) r /\ ~ w2 (fun t => t <> s) r).
  Proof.
    intros s r. split.
    - intros [H1 H2]. split;
        [ exact (proj1 (H _ r) H1) | intro Hc; exact (H2 (proj2 (H _ r) Hc)) ].
    - intros [H1 H2]. split;
        [ exact (proj2 (H _ r) H1) | intro Hc; exact (H2 (proj1 (H _ r) Hc)) ].
  Qed.

  (** [StrictPositivelyMeetPreservingProg] is equivalent to saying that [w]
      is the DSP reading of its recovered relation. This connects the
      carrier's well-formedness condition to the representation used in proofs. *)
  Lemma dsp_carrier {A} (w : SPStExc A) :
    StrictPositivelyMeetPreservingProg w <->
      (forall (pre : S -> Prop) (r : option (A * S)), w pre r <->
      ((exists s, pre s /\ (w (fun _ => True) r /\ ~ w (fun t => t <> s) r)) /\
         (forall s, (w (fun _ => True) r /\ ~ w (fun t => t <> s) r) -> pre s))).
  Proof.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    split.
    - intros [HS HC] pre r.
      (* the meet of the two-element family [{P, Q}] is [P] when [P <= Q] *)
      assert (Hmono : forall (P Q : S -> Prop) y,
                 (forall s, P s -> Q s) -> w P y -> w Q y).
      { intros P Q y Hpq Hw.
        assert (Heq : P = (fun s => forall b : bool, (if b then P else Q) s)).
        { apply Hext. intro s. split.
          - intros Hs b. destruct b; [ exact Hs | exact (Hpq s Hs) ].
          - intro Hb. exact (Hb true). }
        rewrite Heq in Hw.
        exact (proj1 (HC bool (inhabits true) (fun b => if b then P else Q) y) Hw false). }
      destruct (classic (w (fun _ => True) r)) as [Htop | Hntop].
      + (* [r] is reachable, so the meet of all preconditions forcing [r] is
           itself one: the least precondition *)
        pose (least := fun s => forall i : { q : S -> Prop | w q r }, proj1_sig i s).
        assert (Hleast : w least r).
        { unfold least.
          apply (HC { q : S -> Prop | w q r }
                   (inhabits (exist (fun q => w q r) (fun _ : S => True) Htop))
                   (fun i => proj1_sig i) r).
          intro i. exact (proj2_sig i). }
        assert (Hlb : forall q, w q r -> forall s, least s -> q s).
        { intros q Hq s Hs. exact (Hs (exist (fun q0 => w q0 r) q Hq)). }
        (* strictness is what makes the least precondition nonempty *)
        assert (Hne : exists s, least s).
        { apply NNPP. intro Hno. apply (HS r).
          assert (Heq : least = (fun _ : S => False)).
          { apply Hext. intro s. split;
              [ intro Hs; exact (Hno (ex_intro _ s Hs)) | intros [] ]. }
          rewrite Heq in Hleast. exact Hleast. }
        assert (Hrec : forall s, (w (fun _ => True) r /\ ~ w (fun t => t <> s) r)
                                 <-> least s).
        { intro s. split.
          - intros [_ Hn]. apply NNPP. intro Hns. apply Hn.
            apply (Hmono least (fun t => t <> s) r); [| exact Hleast ].
            intros t Ht Heq. subst t. exact (Hns Ht).
          - intros Hls. split; [ exact Htop |].
            intro Hc. exact (Hlb (fun t => t <> s) Hc s Hls eq_refl). }
        split.
        * intro Hw. split.
          -- destruct Hne as [s Hs]. exists s.
             split; [ exact (Hlb pre Hw s Hs) | exact (proj2 (Hrec s) Hs) ].
          -- intros s Hs. exact (Hlb pre Hw s (proj1 (Hrec s) Hs)).
        * intros [_ Hall].
          apply (Hmono least pre r); [| exact Hleast ].
          intros s Hs. exact (Hall s (proj2 (Hrec s) Hs)).
      + (* [r] is unreachable: both sides are false *)
        split.
        * intro Hw. exfalso. apply Hntop.
          apply (Hmono pre (fun _ => True) r); [ intros; exact I | exact Hw ].
        * intros [[s [_ [Htop _]]] _]. exfalso. exact (Hntop Htop).
    - intro HD. split.
      + intros r Hc.
        destruct (proj1 (HD (fun _ => False) r) Hc) as [[s [[] _]] _].
      + intros J Hi0 p x. destruct Hi0 as [i0]. split.
        * intro Hw.
          destruct (proj1 (HD (fun s => forall i : J, p i s) x) Hw)
            as [[s [Hms Hrec]] Hall].
          intro i. apply (HD (fun s => p i s) x). split.
          -- exists s. split; [ exact (Hms i) | exact Hrec ].
          -- intros s' Hrec'. exact (Hall s' Hrec' i).
        * intro Hall. apply (HD (fun s => forall i : J, p i s) x).
          assert (Hpred : forall s, (w (fun _ => True) x
                                     /\ ~ w (fun t => t <> s) x) -> forall i, p i s).
          { intros s Hrec i.
            exact (proj2 (proj1 (HD (fun s0 => p i s0) x) (Hall i)) s Hrec). }
          destruct (proj1 (HD (fun s0 => p i0 s0) x) (Hall i0)) as [[s0 [_ Hrec0]] _].
          split; [ exists s0; split; [ exact (Hpred s0 Hrec0) | exact Hrec0 ]
                 | exact Hpred ].
  Qed.

  (** Everything of DSP shape inhabits the carrier — this discharges each
      [#[program]] obligation below. *)
  Lemma dsp_shape_wf {A} (R : S -> option (A * S) -> Prop) :
    StrictPositivelyMeetPreservingProg
      (fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)).
  Proof.
    split.
    - intros r [[s [Hbot _]] _]. exact Hbot.
    - intros I [i0] p r. split.
      + intros [[s [Hmeet HR]] Hclose] i. split.
        * exists s. split; [ exact (Hmeet i) | exact HR ].
        * intros s' Hs'. exact (Hclose s' Hs' i).
      + intros H. destruct (H i0) as [[s [Hp Hs]] _]. split.
        * exists s. split; [ intro i; exact (proj2 (H i) s Hs) | exact Hs ].
        * intros s' Hs' i. exact (proj2 (H i) s' Hs').
  Qed.

  (** ... and every carrier element is the DSP of its recovered relation. *)
  Lemma getProgDSP_carrier {A} (w : DSPStExc A)
    (pre : S -> Prop) (r : option (A * S)) :
    getDSPStExc w pre r <->
      ((exists s, pre s /\ (getDSPStExc w (fun _ => True) r
                            /\ ~ getDSPStExc w (fun t => t <> s) r)) /\
         (forall s, (getDSPStExc w (fun _ => True) r
                     /\ ~ getDSPStExc w (fun t => t <> s) r) -> pre s)).
  Proof. exact (proj1 (dsp_carrier (getDSPStExc w)) (proj2_sig w) pre r). Qed.

  (** ** The composite relation, and its unit/associativity laws

      The composite quantifies over the INTERMEDIATE OUTCOME [o : option (A * S)]
      and splits on it, rather than pairing an explicit [exists a smid] branch
      with a separate [None] branch.  This is the same shape as
      [outcomes_bind]. *)

  Lemma comp_cong {A B} (R R' : S -> option (A * S) -> Prop)
    (K K' : A -> S -> option (B * S) -> Prop)
    (HR : forall s r, R s r <-> R' s r)
    (HK : forall a s r, K a s r <-> K' a s r) :
    forall (s : S) (r : option (B * S)),
      (exists o, R s o /\ match o with
                          | Some (a, smid) => K a smid r
                          | None => r = None
                          end)
      <-> (exists o, R' s o /\ match o with
                               | Some (a, smid) => K' a smid r
                               | None => r = None
                               end).
  Proof.
    intros s r. split.
    - intros [[[a smid]|] [H1 H2]]; [ exists (Some (a, smid)) | exists None ];
        split; solve [ exact (proj1 (HR s _) H1)
                     | exact (proj1 (HK a smid r) H2) | exact H2 ].
    - intros [[[a smid]|] [H1 H2]]; [ exists (Some (a, smid)) | exists None ];
        split; solve [ exact (proj2 (HR s _) H1)
                     | exact (proj2 (HK a smid r) H2) | exact H2 ].
  Qed.

  Lemma comp_ret_l {A B} (v : A) (K : A -> S -> option (B * S) -> Prop)
    (s : S) (r : option (B * S)) :
    (exists o : option (A * S), o = Some (v, s)
        /\ match o with
           | Some (a, smid) => K a smid r
           | None => r = None
           end)
    <-> K v s r.
  Proof.
    split.
    - intros [o [Heq Hk]]. subst o. exact Hk.
    - intro Hk. exists (Some (v, s)). split; [ reflexivity | exact Hk ].
  Qed.

  Lemma comp_ret_r {A} (R : S -> option (A * S) -> Prop)
    (s : S) (r : option (A * S)) :
    (exists o, R s o /\ match o with
                        | Some (a, smid) => r = Some (a, smid)
                        | None => r = None
                        end)
    <-> R s r.
  Proof.
    split.
    - intros [[[a smid]|] [HR Heq]]; subst r; exact HR.
    - intro HR. exists r. split; [ exact HR |].
      destruct r as [[a smid]|]; reflexivity.
  Qed.

  Lemma comp_assoc {A B C} (R : S -> option (A * S) -> Prop)
    (F : A -> S -> option (B * S) -> Prop)
    (G : B -> S -> option (C * S) -> Prop) (s : S) (r : option (C * S)) :
    (exists o2 : option (B * S),
        (exists o1 : option (A * S),
            R s o1 /\ match o1 with
                      | Some (a, s1) => F a s1 o2
                      | None => o2 = None
                      end)
        /\ match o2 with
           | Some (b, s2) => G b s2 r
           | None => r = None
           end)
    <-> (exists o1 : option (A * S),
            R s o1 /\ match o1 with
                      | Some (a, s1) =>
                          exists o2 : option (B * S),
                            F a s1 o2 /\ match o2 with
                                         | Some (b, s2) => G b s2 r
                                         | None => r = None
                                         end
                      | None => r = None
                      end).
  Proof.
    split.
    - intros [o2 [[o1 [HR HF]] HG]]. exists o1. split; [ exact HR |].
      destruct o1 as [[a s1]|].
      + exists o2. split; [ exact HF | exact HG ].
      + subst o2. exact HG.
    - intros [o1 [HR H]]. destruct o1 as [[a s1]|].
      + destruct H as [o2 [HF HG]]. exists o2. split; [| exact HG ].
        exists (Some (a, s1)). split; [ exact HR | exact HF ].
      + exists None. split; [| exact H ].
        exists None. split; [ exact HR | reflexivity ].
  Qed.

  (** ** [ret] and [bind] *)

  #[program] Definition retDSPStExc {A} (a : A) : DSPStExc A :=
    fun pre r => (retASPStExc a pre r) /\ (retDSLPStExc a pre r).
  Next Obligation. exact (dsp_shape_wf (fun s r => r = Some (a, s))). Qed.

  (* We would like bindDSPStExc to match retDSPStExc, but this requires
     converting DSPStExc to both ASPStExc and DSLPStExc. *)

  (** The two probe forms are the ASP and the DSLP of the recovered relation. *)
  Lemma aspPartdsp_closed {A} (w : DSPStExc A) pre r :
    (getDSPStExc w (fun _ => True) r /\ ~ getDSPStExc w (fun s => ~ pre s) r)
    <-> (exists s, pre s /\ (getDSPStExc w (fun _ => True) r
                             /\ ~ getDSPStExc w (fun t => t <> s) r)).
  Proof.
    split.
    - intros [Htop Hn]. apply NNPP. intro Hno. apply Hn.
      apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split.
      + exists s0. split; [| exact Hr0 ].
        intro Hp. exact (Hno (ex_intro _ s0 (conj Hp Hr0))).
      + intros s Hs Hp. exact (Hno (ex_intro _ s (conj Hp Hs))).
    - intros [s [Hp Hs]]. split.
      + apply getProgDSP_carrier. split;
          [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
      + intro Hc.
        exact (proj2 (proj1 (getProgDSP_carrier w (fun t => ~ pre t) r) Hc) s Hs Hp).
  Qed.

  Lemma dslpPartdsp_closed {A} (w : DSPStExc A) pre r :
    (getDSPStExc w (fun _ => True) r -> getDSPStExc w pre r)
    <-> (forall s, (getDSPStExc w (fun _ => True) r
                    /\ ~ getDSPStExc w (fun t => t <> s) r) -> pre s).
  Proof.
    split.
    - intros H s Hs. refine (proj2 (proj1 (getProgDSP_carrier w pre r) (H _)) s Hs).
      apply getProgDSP_carrier. split;
        [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
    - intros Hall Htop. apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split; [ exists s0; split; [ exact (Hall s0 Hr0) | exact Hr0 ] | exact Hall ].
  Qed.

  (** Both well-formedness properties transport along pointwise equivalence. *)
  Lemma singletonProg_ext {A} (w1 w2 : @SPStExc S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
  Qed.

  Lemma dsp_healthy_ext {A} (w1 w2 : @SPStExc S A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    StrictPositivelyMeetPreservingProg w1 -> StrictPositivelyMeetPreservingProg w2.
  Proof.
    intros Hext [HS HC]. split.
    - intros r Hc. exact (HS r (proj2 (Hext _ r) Hc)).
    - intros I i0 p r. split.
      + intros Hw i. apply Hext.
        exact (proj1 (HC I i0 p r) (proj2 (Hext _ r) Hw) i).
      + intro Hall. apply Hext. apply (HC I i0 p r).
        intro i. exact (proj2 (Hext _ r) (Hall i)).
  Qed.

  #[program] Definition aspPartdsp {A} (w : DSPStExc A) : ASPStExc S A :=
    fun pre r => getDSPStExc w (fun _ => True) r /\ ~ getDSPStExc w (fun s => ~ pre s) r.
  Next Obligation.
    apply (singletonProg_ext
             (fun pre r => exists s, pre s /\ (getDSPStExc w (fun _ => True) r
                                               /\ ~ getDSPStExc w (fun t => t <> s) r))).
    - intros pre r. exact (iff_sym (aspPartdsp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartdsp {A} (w : DSPStExc A) : DSLPStExc S A :=
    fun pre r => getDSPStExc w (fun _ => True) r -> getDSPStExc w pre r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (getDSPStExc w (fun _ => True) r
                                      /\ ~ getDSPStExc w (fun t => t <> s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartdsp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem dsp_split {A} (w : DSPStExc A) pre r :
    getDSPStExc w pre r <-> (getASPStExc (aspPartdsp w) pre r /\ getDSLPStExc (dslpPartdsp w) pre r).
  Proof.
    refine (iff_trans (getProgDSP_carrier w pre r) _). split.
    - intros [He Hall]. split.
      + exact (proj2 (aspPartdsp_closed w pre r) He).
      + exact (proj2 (dslpPartdsp_closed w pre r) Hall).
    - intros [Ha Hd]. split.
      + exact (proj1 (aspPartdsp_closed w pre r) Ha).
      + exact (proj1 (dslpPartdsp_closed w pre r) Hd).
  Qed.

  (** Both binds compute the SAME composite relation, one existentially and
      one universally — which is why the conjunction below is the DSP of it. *)
  Lemma bind_asp_parts {A B} (m : DSPStExc A) (k : A -> DSPStExc B) pre r :
    getASPStExc (bindASPStExc (aspPartdsp m) (fun a => aspPartdsp (k a))) pre r
    <-> (exists s, pre s /\
           (exists o, (getDSPStExc m (fun _ => True) o
                       /\ ~ getDSPStExc m (fun t => t <> s) o)
                      /\ match o with
                         | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                             /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                         | None => r = None
                         end)).
  Proof.
    split.
    - intros [[a Hk] | [Hr Hm]].
      + destruct (proj1 (aspPartdsp_closed (k a)
                           (fun s0 => getASPStExc (aspPartdsp m) pre (Some (a, s0))) r) Hk)
          as [smid [Hp Hrk]].
        destruct (proj1 (aspPartdsp_closed m pre (Some (a, smid))) Hp) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists (Some (a, smid)). split; [ exact Hrm | exact Hrk ].
      + destruct (proj1 (aspPartdsp_closed m pre None) Hm) as [s [Hps Hrm]].
        exists s. split; [ exact Hps |].
        exists None. split; [ exact Hrm | exact Hr ].
    - intros [s [Hps [[[a smid]|] [Hrm Hrk]]]].
      + left. exists a.
        exact (proj2 (aspPartdsp_closed (k a)
                        (fun s0 => getASPStExc (aspPartdsp m) pre (Some (a, s0))) r)
                 (ex_intro _ smid
                    (conj (proj2 (aspPartdsp_closed m pre (Some (a, smid)))
                             (ex_intro _ s (conj Hps Hrm))) Hrk))).
      + right. split; [ exact Hrk |].
        exact (proj2 (aspPartdsp_closed m pre None) (ex_intro _ s (conj Hps Hrm))).
  Qed.

  Lemma bind_dslp_parts {A B} (m : DSPStExc A) (k : A -> DSPStExc B) pre r :
    getDSLPStExc (bindDSLPStExc (dslpPartdsp m) (fun a => dslpPartdsp (k a))) pre r
    <-> (forall s,
           (exists o, (getDSPStExc m (fun _ => True) o
                       /\ ~ getDSPStExc m (fun t => t <> s) o)
                      /\ match o with
                         | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                             /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                         | None => r = None
                         end) -> pre s).
  Proof.
    split.
    - intros [H1 H2] s [[[a smid]|] [Hrm Hrk]].
      + exact (proj1 (dslpPartdsp_closed m pre (Some (a, smid)))
                 (proj1 (dslpPartdsp_closed (k a)
                           (fun s0 => getDSLPStExc (dslpPartdsp m) pre (Some (a, s0))) r)
                    (H1 a) smid Hrk) s Hrm).
      + exact (proj1 (dslpPartdsp_closed m pre None) (H2 Hrk) s Hrm).
    - intro H. split.
      + intro a.
        exact (proj2 (dslpPartdsp_closed (k a)
                        (fun s0 => getDSLPStExc (dslpPartdsp m) pre (Some (a, s0))) r)
                 (fun smid Hrk =>
                    proj2 (dslpPartdsp_closed m pre (Some (a, smid)))
                      (fun s Hrm => H s (ex_intro _ (Some (a, smid)) (conj Hrm Hrk))))).
      + intro Hr.
        exact (proj2 (dslpPartdsp_closed m pre None)
                 (fun s Hrm => H s (ex_intro _ None (conj Hrm Hr)))).
  Qed.

  #[program] Definition bindDSPStExc {A B} (m : DSPStExc A) (k : A -> DSPStExc B) : DSPStExc B :=
    fun pre r => bindASPStExc (aspPartdsp m) (fun a => aspPartdsp (k a)) pre r /\
                   bindDSLPStExc (dslpPartdsp m) (fun a => dslpPartdsp (k a)) pre r.
  Next Obligation.
    apply (dsp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists o, (getDSPStExc m (fun _ => True) o
                               /\ ~ getDSPStExc m (fun t => t <> s) o)
                              /\ match o with
                                 | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                                     /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                                 | None => r = None
                                 end))
                /\ (forall s,
                      (exists o, (getDSPStExc m (fun _ => True) o
                                  /\ ~ getDSPStExc m (fun t => t <> s) o)
                                 /\ match o with
                                    | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                                        /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                                    | None => r = None
                                    end) -> pre s))).
    - intros pre r. split.
      + intros [He Hall]. split;
          [ exact (proj2 (bind_asp_parts m k pre r) He)
          | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
      + intros [Ha Hd]. split;
          [ exact (proj1 (bind_asp_parts m k pre r) Ha)
          | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - apply dsp_shape_wf.
  Qed.

  (** The relation recovered from [retDSPStExc a] is [fun s r => r = Some (a, s)]. *)
  Lemma rec_retDSPProg {A} (a : A) (s : S) (r : option (A * S)) :
    (getDSPStExc (retDSPStExc a) (fun _ => True) r
     /\ ~ getDSPStExc (retDSPStExc a) (fun t => t <> s) r)
    <-> r = Some (a, s).
  Proof. exact (dsp_recov (fun s0 r0 => r0 = Some (a, s0)) s r). Qed.

  (** [bindDSPStExc m k] is pointwise the DSP of the composite relation. *)
  Lemma bindDSPProg_dsp {A B} (m : DSPStExc A) (k : A -> DSPStExc B) pre r :
    getDSPStExc (bindDSPStExc m k) pre r
    <-> ((exists s, pre s /\
            (exists o, (getDSPStExc m (fun _ => True) o
                        /\ ~ getDSPStExc m (fun t => t <> s) o)
                       /\ match o with
                          | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                              /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                          | None => r = None
                          end))
         /\ (forall s,
               (exists o, (getDSPStExc m (fun _ => True) o
                           /\ ~ getDSPStExc m (fun t => t <> s) o)
                          /\ match o with
                             | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                                 /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                             | None => r = None
                             end) -> pre s)).
  Proof.
    split.
    - intros [Ha Hd]. split;
        [ exact (proj1 (bind_asp_parts m k pre r) Ha)
        | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - intros [He Hall]. split;
        [ exact (proj2 (bind_asp_parts m k pre r) He)
        | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
  Qed.

  (** The relation recovered from [bindDSPStExc m k] is the composite. *)
  Lemma rec_bindDSPProg {A B} (m : DSPStExc A) (k : A -> DSPStExc B)
    (s : S) (r : option (B * S)) :
    (getDSPStExc (bindDSPStExc m k) (fun _ => True) r
     /\ ~ getDSPStExc (bindDSPStExc m k) (fun t => t <> s) r)
    <-> (exists o, (getDSPStExc m (fun _ => True) o
                    /\ ~ getDSPStExc m (fun t => t <> s) o)
                   /\ match o with
                      | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r
                                          /\ ~ getDSPStExc (k a) (fun t => t <> smid) r
                      | None => r = None
                      end).
  Proof.
    refine (iff_trans (dsp_rec_ext _ _ (bindDSPProg_dsp m k) s r)
              (dsp_recov
                 (fun s0 r0 =>
                    exists o, (getDSPStExc m (fun _ => True) o
                               /\ ~ getDSPStExc m (fun t => t <> s0) o)
                              /\ match o with
                                 | Some (a, smid) => getDSPStExc (k a) (fun _ => True) r0
                                                     /\ ~ getDSPStExc (k a) (fun t => t <> smid) r0
                                 | None => r0 = None
                                 end)
                 s r)).
  Qed.

  #[global]
    Instance Monad__DSPStExc : Monad DSPStExc :=
    {| ret := fun _ => @retDSPStExc _ ;
      bind := fun _ _ => @bindDSPStExc _ _ |}.

  #[global] Instance Eq1__DSPStExc : Eq1 DSPStExc :=
    fun A m n => forall pre r, getDSPStExc m pre r <-> getDSPStExc n pre r.

  #[global] Instance Eq1Equivalence__DSPStExc
    : @Eq1Equivalence DSPStExc _ Eq1__DSPStExc.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__DSPStExc
    : @MonadLawsE DSPStExc Eq1__DSPStExc _.
  Proof.
    constructor.
    - (* bind_ret_l : the composite of [retDSPStExc x] with [f] is [f x] *)
      intros A B f x. unfold eq1, Eq1__DSPStExc. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (getDSPStExc (retDSPStExc x) (fun _ => True) o
                             /\ ~ getDSPStExc (retDSPStExc x) (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getDSPStExc (f a) (fun _ => True) r0
                                   /\ ~ getDSPStExc (f a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (getDSPStExc (f x) (fun _ => True) r0
                      /\ ~ getDSPStExc (f x) (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getDSPStExc (retDSPStExc x) (fun _ => True) r1
                                  /\ ~ getDSPStExc (retDSPStExc x) (fun t => t <> s1) r1)
                    (fun s1 r1 => r1 = Some (x, s1))
                    (fun a1 s1 r1 => getDSPStExc (f a1) (fun _ => True) r1
                                     /\ ~ getDSPStExc (f a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getDSPStExc (f a1) (fun _ => True) r1
                                     /\ ~ getDSPStExc (f a1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_retDSPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l x
                    (fun a1 s1 r1 => getDSPStExc (f a1) (fun _ => True) r1
                                     /\ ~ getDSPStExc (f a1) (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp (retDSPStExc x) f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier (f x) pre r)))).
    - (* bind_ret_r : the composite of [m] with [retDSPStExc] is [m] *)
      intros A m. unfold eq1, Eq1__DSPStExc. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (A * S)),
                 (exists o, (getDSPStExc m (fun _ => True) o
                             /\ ~ getDSPStExc m (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getDSPStExc (retDSPStExc a) (fun _ => True) r0
                                   /\ ~ getDSPStExc (retDSPStExc a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (getDSPStExc m (fun _ => True) r0
                      /\ ~ getDSPStExc m (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getDSPStExc m (fun _ => True) r1
                                  /\ ~ getDSPStExc m (fun t => t <> s1) r1)
                    (fun s1 r1 => getDSPStExc m (fun _ => True) r1
                                  /\ ~ getDSPStExc m (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getDSPStExc (retDSPStExc a1) (fun _ => True) r1
                                     /\ ~ getDSPStExc (retDSPStExc a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => r1 = Some (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retDSPProg a1 s1 r1) s r0)
                 (comp_ret_r
                    (fun s1 r1 => getDSPStExc m (fun _ => True) r1
                                  /\ ~ getDSPStExc m (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp m _ pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier m pre r)))).
    - (* bind_bind : associativity of the composite *)
      intros A B C x f g. unfold eq1, Eq1__DSPStExc. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (C * S)),
                 (exists o, (getDSPStExc (bindDSPStExc x f) (fun _ => True) o
                             /\ ~ getDSPStExc (bindDSPStExc x f) (fun t => t <> s) o)
                            /\ match o with
                               | Some (b, smid) =>
                                   getDSPStExc (g b) (fun _ => True) r0
                                   /\ ~ getDSPStExc (g b) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (getDSPStExc x (fun _ => True) o
                                 /\ ~ getDSPStExc x (fun t => t <> s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       getDSPStExc (bindDSPStExc (f a) g) (fun _ => True) r0
                                       /\ ~ getDSPStExc (bindDSPStExc (f a) g)
                                              (fun t => t <> smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getDSPStExc (bindDSPStExc x f) (fun _ => True) r1
                                  /\ ~ getDSPStExc (bindDSPStExc x f) (fun t => t <> s1) r1)
                    (fun s1 r1 =>
                       exists o, (getDSPStExc x (fun _ => True) o
                                  /\ ~ getDSPStExc x (fun t => t <> s1) o)
                                 /\ match o with
                                    | Some (a, smid) =>
                                        getDSPStExc (f a) (fun _ => True) r1
                                        /\ ~ getDSPStExc (f a) (fun t => t <> smid) r1
                                    | None => r1 = None
                                    end)
                    (fun b1 s1 r1 => getDSPStExc (g b1) (fun _ => True) r1
                                     /\ ~ getDSPStExc (g b1) (fun t => t <> s1) r1)
                    (fun b1 s1 r1 => getDSPStExc (g b1) (fun _ => True) r1
                                     /\ ~ getDSPStExc (g b1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_bindDSPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc
                       (fun s1 r1 => getDSPStExc x (fun _ => True) r1
                                     /\ ~ getDSPStExc x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 => getDSPStExc (f a1) (fun _ => True) r1
                                        /\ ~ getDSPStExc (f a1) (fun t => t <> s1) r1)
                       (fun b1 s1 r1 => getDSPStExc (g b1) (fun _ => True) r1
                                        /\ ~ getDSPStExc (g b1) (fun t => t <> s1) r1)
                       s r0)
                    (comp_cong
                       (fun s1 r1 => getDSPStExc x (fun _ => True) r1
                                     /\ ~ getDSPStExc x (fun t => t <> s1) r1)
                       (fun s1 r1 => getDSPStExc x (fun _ => True) r1
                                     /\ ~ getDSPStExc x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 =>
                          exists o, (getDSPStExc (f a1) (fun _ => True) o
                                     /\ ~ getDSPStExc (f a1) (fun t => t <> s1) o)
                                    /\ match o with
                                       | Some (b, smid) =>
                                           getDSPStExc (g b) (fun _ => True) r1
                                           /\ ~ getDSPStExc (g b) (fun t => t <> smid) r1
                                       | None => r1 = None
                                       end)
                       (fun a1 s1 r1 =>
                          getDSPStExc (bindDSPStExc (f a1) g) (fun _ => True) r1
                          /\ ~ getDSPStExc (bindDSPStExc (f a1) g) (fun t => t <> s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindDSPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindDSPProg_dsp (bindDSPStExc x f) g pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp x (fun a => bindDSPStExc (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__DSPStExc in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (getDSPStExc x (fun _ => True) o
                             /\ ~ getDSPStExc x (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getDSPStExc (f a) (fun _ => True) r0
                                   /\ ~ getDSPStExc (f a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (getDSPStExc y (fun _ => True) o
                                 /\ ~ getDSPStExc y (fun t => t <> s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       getDSPStExc (g a) (fun _ => True) r0
                                       /\ ~ getDSPStExc (g a) (fun t => t <> smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (comp_cong
                 (fun s1 r1 => getDSPStExc x (fun _ => True) r1
                               /\ ~ getDSPStExc x (fun t => t <> s1) r1)
                 (fun s1 r1 => getDSPStExc y (fun _ => True) r1
                               /\ ~ getDSPStExc y (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getDSPStExc (f a1) (fun _ => True) r1
                                  /\ ~ getDSPStExc (f a1) (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getDSPStExc (g a1) (fun _ => True) r1
                                  /\ ~ getDSPStExc (g a1) (fun t => t <> s1) r1)
                 (fun s1 r1 => dsp_rec_ext (getDSPStExc x) (getDSPStExc y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    dsp_rec_ext (getDSPStExc (f a1)) (getDSPStExc (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindDSPProg_dsp x f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp y g pre r)))).
  Qed.
End ProgDSPMonad.

Arguments retDSPStExc {_} {_}.
Arguments bindDSPStExc {_} {_} {_}.
Arguments getDSPStExc {_} {_}.

(* ================================================================= *)
(** * Terminating-slice variant (factored out of SPSimplerSpecMonads.v) *)
(* ================================================================= *)

From ExtLib Require Import Monad MonadState StateMonad OptionMonad.
From ITree Require Import Basics.Monad.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import SPPredicateTransformers.
From Incorrectness.Taxonomy.BaseSpecMonads.OldMonads Require Import ASPMonad DSLPMonad.

Module StDSP.
  Import StTrans StASP StDSLP.
Section ProgDSPMonad.
  Variable S : Type.

  Definition StrictPositivelyMeetPreservingProg {A} (w : SPSt A) : Prop :=
    StrictProg S w /\ ConjunctiveProg S w.
  
  Definition DSPSt (A : Type) : Type :=
    { w : SPSt A | StrictPositivelyMeetPreservingProg w }.

  Definition getDSPSt {A} (w : DSPSt A) : SPSt A := proj1_sig w.

  (** ** Recovery, well-formedness, congruence

      Everything below is stated about the raw transformer
      [fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)]
      and about the composite relation, written out; no auxiliary definitions
      are introduced. *)

  (** Probing that transformer at [fun _ => True] and at the co-singleton of
      [s] recovers [R s r] exactly.  This is the ONLY use of classical logic
      in the section: from "some state reaches [r]" together with "[fun t =>
      t <> s] is not a valid precondition for [r]" one concludes [R s r]. *)
  Lemma dsp_recov {A} (R : S -> (A * S) -> Prop)
    (s : S) (r : (A * S)) :
    (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
     /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s)))
    <-> R s r.
  Proof.
    split.
    - intros [[[t [_ Ht]] _] Hn]. apply NNPP. intro Hns. apply Hn. split.
      + exists t. split; [ intro Heq; subst t; exact (Hns Ht) | exact Ht ].
      + intros t' Ht' Heq. subst t'. exact (Hns Ht').
    - intro Hs. split.
      + split; [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
      + intros [_ Hall]. exact (Hall s Hs eq_refl).
  Qed.

  (** The DSP shape at [R] is pointwise the DSP of the relation recovered
      from it by probing ([dsp_recov]). *)
  Lemma dsp_wf {A} (R : S -> (A * S) -> Prop) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\
              (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
               /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s))))
           /\ (forall s,
                 (((exists t, True /\ R t r) /\ (forall t, R t r -> True))
                  /\ ~ ((exists t, t <> s /\ R t r) /\ (forall t, R t r -> t <> s)))
                 -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj2 (dsp_recov R s r) Hs) ].
      + intros s' H. exact (Hall s' (proj1 (dsp_recov R s' r) H)).
    - intros [[s [Hp H]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj1 (dsp_recov R s r) H) ].
      + intros s' Hs'. exact (Hall s' (proj2 (dsp_recov R s' r) Hs')).
  Qed.

  (** Extensionally equal relations give extensionally equal transformers. *)
  Lemma dsp_cong {A} (R R' : S -> (A * S) -> Prop)
    (H : forall s r, R s r <-> R' s r) :
    forall (pre : S -> Prop) (r : (A * S)),
      ((exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s))
      <-> ((exists s, pre s /\ R' s r) /\ (forall s, R' s r -> pre s)).
  Proof.
    intros pre r. split.
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj1 (H s r) Hs) ].
      + intros s' Hs'. exact (Hall s' (proj2 (H s' r) Hs')).
    - intros [[s [Hp Hs]] Hall]. split.
      + exists s. split; [ exact Hp | exact (proj2 (H s r) Hs) ].
      + intros s' Hs'. exact (Hall s' (proj1 (H s' r) Hs')).
  Qed.

  (** ... and extensionally equal transformers recover the same relation. *)
  Lemma dsp_rec_ext {A} (w1 w2 : @SPSt S A)
    (H : forall pre r, w1 pre r <-> w2 pre r) :
    forall (s : S) (r : (A * S)),
      (w1 (fun _ => True) r /\ ~ w1 (fun t => t <> s) r)
      <-> (w2 (fun _ => True) r /\ ~ w2 (fun t => t <> s) r).
  Proof.
    intros s r. split.
    - intros [H1 H2]. split;
        [ exact (proj1 (H _ r) H1) | intro Hc; exact (H2 (proj2 (H _ r) Hc)) ].
    - intros [H1 H2]. split;
        [ exact (proj2 (H _ r) H1) | intro Hc; exact (H2 (proj1 (H _ r) Hc)) ].
  Qed.

  (** [StrictPositivelyMeetPreservingProg] is equivalent to saying that [w]
      is the DSP reading of its recovered relation. This connects the
      carrier's well-formedness condition to the representation used in proofs. *)
  Lemma dsp_carrier {A} (w : SPSt A) :
    StrictPositivelyMeetPreservingProg w <->
      (forall (pre : S -> Prop) (r : (A * S)), w pre r <->
      ((exists s, pre s /\ (w (fun _ => True) r /\ ~ w (fun t => t <> s) r)) /\
         (forall s, (w (fun _ => True) r /\ ~ w (fun t => t <> s) r) -> pre s))).
  Proof.
    assert (Hext : forall P Q : S -> Prop, (forall s, P s <-> Q s) -> P = Q).
    { intros P Q HPQ. apply functional_extensionality. intro s.
      apply propositional_extensionality. exact (HPQ s). }
    split.
    - intros [HS HC] pre r.
      (* the meet of the two-element family [{P, Q}] is [P] when [P <= Q] *)
      assert (Hmono : forall (P Q : S -> Prop) y,
                 (forall s, P s -> Q s) -> w P y -> w Q y).
      { intros P Q y Hpq Hw.
        assert (Heq : P = (fun s => forall b : bool, (if b then P else Q) s)).
        { apply Hext. intro s. split.
          - intros Hs b. destruct b; [ exact Hs | exact (Hpq s Hs) ].
          - intro Hb. exact (Hb true). }
        rewrite Heq in Hw.
        exact (proj1 (HC bool (inhabits true) (fun b => if b then P else Q) y) Hw false). }
      destruct (classic (w (fun _ => True) r)) as [Htop | Hntop].
      + (* [r] is reachable, so the meet of all preconditions forcing [r] is
           itself one: the least precondition *)
        pose (least := fun s => forall i : { q : S -> Prop | w q r }, proj1_sig i s).
        assert (Hleast : w least r).
        { unfold least.
          apply (HC { q : S -> Prop | w q r }
                   (inhabits (exist (fun q => w q r) (fun _ : S => True) Htop))
                   (fun i => proj1_sig i) r).
          intro i. exact (proj2_sig i). }
        assert (Hlb : forall q, w q r -> forall s, least s -> q s).
        { intros q Hq s Hs. exact (Hs (exist (fun q0 => w q0 r) q Hq)). }
        (* strictness is what makes the least precondition nonempty *)
        assert (Hne : exists s, least s).
        { apply NNPP. intro Hno. apply (HS r).
          assert (Heq : least = (fun _ : S => False)).
          { apply Hext. intro s. split;
              [ intro Hs; exact (Hno (ex_intro _ s Hs)) | intros [] ]. }
          rewrite Heq in Hleast. exact Hleast. }
        assert (Hrec : forall s, (w (fun _ => True) r /\ ~ w (fun t => t <> s) r)
                                 <-> least s).
        { intro s. split.
          - intros [_ Hn]. apply NNPP. intro Hns. apply Hn.
            apply (Hmono least (fun t => t <> s) r); [| exact Hleast ].
            intros t Ht Heq. subst t. exact (Hns Ht).
          - intros Hls. split; [ exact Htop |].
            intro Hc. exact (Hlb (fun t => t <> s) Hc s Hls eq_refl). }
        split.
        * intro Hw. split.
          -- destruct Hne as [s Hs]. exists s.
             split; [ exact (Hlb pre Hw s Hs) | exact (proj2 (Hrec s) Hs) ].
          -- intros s Hs. exact (Hlb pre Hw s (proj1 (Hrec s) Hs)).
        * intros [_ Hall].
          apply (Hmono least pre r); [| exact Hleast ].
          intros s Hs. exact (Hall s (proj2 (Hrec s) Hs)).
      + (* [r] is unreachable: both sides are false *)
        split.
        * intro Hw. exfalso. apply Hntop.
          apply (Hmono pre (fun _ => True) r); [ intros; exact I | exact Hw ].
        * intros [[s [_ [Htop _]]] _]. exfalso. exact (Hntop Htop).
    - intro HD. split.
      + intros r Hc.
        destruct (proj1 (HD (fun _ => False) r) Hc) as [[s [[] _]] _].
      + intros J Hi0 p x. destruct Hi0 as [i0]. split.
        * intro Hw.
          destruct (proj1 (HD (fun s => forall i : J, p i s) x) Hw)
            as [[s [Hms Hrec]] Hall].
          intro i. apply (HD (fun s => p i s) x). split.
          -- exists s. split; [ exact (Hms i) | exact Hrec ].
          -- intros s' Hrec'. exact (Hall s' Hrec' i).
        * intro Hall. apply (HD (fun s => forall i : J, p i s) x).
          assert (Hpred : forall s, (w (fun _ => True) x
                                     /\ ~ w (fun t => t <> s) x) -> forall i, p i s).
          { intros s Hrec i.
            exact (proj2 (proj1 (HD (fun s0 => p i s0) x) (Hall i)) s Hrec). }
          destruct (proj1 (HD (fun s0 => p i0 s0) x) (Hall i0)) as [[s0 [_ Hrec0]] _].
          split; [ exists s0; split; [ exact (Hpred s0 Hrec0) | exact Hrec0 ]
                 | exact Hpred ].
  Qed.

  Lemma dsp_shape_wf {A} (R : S -> (A * S) -> Prop) :
    StrictPositivelyMeetPreservingProg
      (fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)).
  Proof.
    split.
    - intros r [[s [Hbot _]] _]. exact Hbot.
    - intros I [i0] p r. split.
      + intros [[s [Hmeet HR]] Hclose] i. split.
        * exists s. split; [ exact (Hmeet i) | exact HR ].
        * intros s' Hs'. exact (Hclose s' Hs' i).
      + intros H. destruct (H i0) as [[s [Hp Hs]] _]. split.
        * exists s. split; [ intro i; exact (proj2 (H i) s Hs) | exact Hs ].
        * intros s' Hs' i. exact (proj2 (H i) s' Hs').
  Qed.

  Lemma getProgDSP_carrier {A} (w : DSPSt A) (pre : S -> Prop) (r : A * S) :
    getDSPSt w pre r <->
      ((exists s, pre s /\ (getDSPSt w (fun _ => True) r
                            /\ ~ getDSPSt w (fun t => t <> s) r)) /\
         (forall s, (getDSPSt w (fun _ => True) r
                     /\ ~ getDSPSt w (fun t => t <> s) r) -> pre s)).
  Proof. exact (proj1 (dsp_carrier (getDSPSt w)) (proj2_sig w) pre r). Qed.

  (** ** The composite relation.  With no exceptional outcome it is a single
      existential over the intermediate state — no [match], no [None] case. *)

  Lemma comp_cong {A B} (R R' : S -> (A * S) -> Prop)
    (K K' : A -> S -> (B * S) -> Prop)
    (HR : forall s r, R s r <-> R' s r)
    (HK : forall a s r, K a s r <-> K' a s r) :
    forall (s : S) (r : B * S),
      (exists a smid, R s (a, smid) /\ K a smid r)
      <-> (exists a smid, R' s (a, smid) /\ K' a smid r).
  Proof.
    intros s r. split; intros [a [smid [H1 H2]]]; exists a, smid.
    - split; [ exact (proj1 (HR s _) H1) | exact (proj1 (HK a smid r) H2) ].
    - split; [ exact (proj2 (HR s _) H1) | exact (proj2 (HK a smid r) H2) ].
  Qed.

  Lemma comp_ret_l {A B} (v : A) (K : A -> S -> (B * S) -> Prop)
    (s : S) (r : B * S) :
    (exists a smid, (a, smid) = (v, s) /\ K a smid r) <-> K v s r.
  Proof.
    split.
    - intros [a [smid [Heq Hk]]].
      assert (Ha : a = v) by congruence. assert (Hs : smid = s) by congruence.
      subst a. subst smid. exact Hk.
    - intro Hk. exists v, s. split; [ reflexivity | exact Hk ].
  Qed.

  Lemma comp_ret_r {A} (R : S -> (A * S) -> Prop) (s : S) (r : A * S) :
    (exists a smid, R s (a, smid) /\ r = (a, smid)) <-> R s r.
  Proof.
    split.
    - intros [a [smid [HR Heq]]]. subst r. exact HR.
    - intro HR. destruct r as [a smid]. exists a, smid.
      split; [ exact HR | reflexivity ].
  Qed.

  Lemma comp_assoc {A B C} (R : S -> (A * S) -> Prop)
    (F : A -> S -> (B * S) -> Prop) (G : B -> S -> (C * S) -> Prop)
    (s : S) (r : C * S) :
    (exists b s2, (exists a s1, R s (a, s1) /\ F a s1 (b, s2)) /\ G b s2 r)
    <-> (exists a s1, R s (a, s1) /\ (exists b s2, F a s1 (b, s2) /\ G b s2 r)).
  Proof.
    split.
    - intros [b [s2 [[a [s1 [HR HF]]] HG]]].
      exists a, s1. split; [ exact HR |].
      exists b, s2. split; [ exact HF | exact HG ].
    - intros [a [s1 [HR [b [s2 [HF HG]]]]]].
      exists b, s2. split; [| exact HG ].
      exists a, s1. split; [ exact HR | exact HF ].
  Qed.

  (** ** [ret], the two projections, and [bind] *)

  #[program] Definition retDSPSt {A} (a : A) : DSPSt A :=
    fun pre r => (retASPSt a pre r) /\ (retDSLPSt a pre r).
  Next Obligation. exact (dsp_shape_wf (fun s r => r = (a, s))). Qed.

  Lemma aspPartdsp_closed {A} (w : DSPSt A) pre r :
    (getDSPSt w (fun _ => True) r /\ ~ getDSPSt w (fun s => ~ pre s) r)
    <-> (exists s, pre s /\ (getDSPSt w (fun _ => True) r
                             /\ ~ getDSPSt w (fun t => t <> s) r)).
  Proof.
    split.
    - intros [Htop Hn]. apply NNPP. intro Hno. apply Hn.
      apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split.
      + exists s0. split; [| exact Hr0 ].
        intro Hp. exact (Hno (ex_intro _ s0 (conj Hp Hr0))).
      + intros s Hs Hp. exact (Hno (ex_intro _ s (conj Hp Hs))).
    - intros [s [Hp Hs]]. split.
      + apply getProgDSP_carrier. split;
          [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
      + intro Hc.
        exact (proj2 (proj1 (getProgDSP_carrier w (fun t => ~ pre t) r) Hc) s Hs Hp).
  Qed.

  Lemma dslpPartdsp_closed {A} (w : DSPSt A) pre r :
    (getDSPSt w (fun _ => True) r -> getDSPSt w pre r)
    <-> (forall s, (getDSPSt w (fun _ => True) r
                    /\ ~ getDSPSt w (fun t => t <> s) r) -> pre s).
  Proof.
    split.
    - intros H s Hs. refine (proj2 (proj1 (getProgDSP_carrier w pre r) (H _)) s Hs).
      apply getProgDSP_carrier. split;
        [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
    - intros Hall Htop. apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split; [ exists s0; split; [ exact (Hall s0 Hr0) | exact Hr0 ] | exact Hall ].
  Qed.

  Lemma singletonProg_ext {A} (w1 w2 : @SPSt S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
  Qed.

  Lemma dsp_healthy_ext {A} (w1 w2 : @SPSt S A) :
    (forall pre r, w1 pre r <-> w2 pre r) ->
    StrictPositivelyMeetPreservingProg w1 -> StrictPositivelyMeetPreservingProg w2.
  Proof.
    intros Hext [HS HC]. split.
    - intros r Hc. exact (HS r (proj2 (Hext _ r) Hc)).
    - intros I i0 p r. split.
      + intros Hw i. apply Hext.
        exact (proj1 (HC I i0 p r) (proj2 (Hext _ r) Hw) i).
      + intro Hall. apply Hext. apply (HC I i0 p r).
        intro i. exact (proj2 (Hext _ r) (Hall i)).
  Qed.

  #[program] Definition aspPartdsp {A} (w : DSPSt A) : ASPSt S A :=
    fun pre r => getDSPSt w (fun _ => True) r /\ ~ getDSPSt w (fun s => ~ pre s) r.
  Next Obligation.
    apply (singletonProg_ext
             (fun pre r => exists s, pre s /\ (getDSPSt w (fun _ => True) r
                                               /\ ~ getDSPSt w (fun t => t <> s) r))).
    - intros pre r. exact (iff_sym (aspPartdsp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartdsp {A} (w : DSPSt A) : DSLPSt S A :=
    fun pre r => getDSPSt w (fun _ => True) r -> getDSPSt w pre r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (getDSPSt w (fun _ => True) r
                                      /\ ~ getDSPSt w (fun t => t <> s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartdsp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem dsp_split {A} (w : DSPSt A) pre r :
    getDSPSt w pre r
    <-> (getASPSt (aspPartdsp w) pre r /\ getDSLPSt (dslpPartdsp w) pre r).
  Proof.
    refine (iff_trans (getProgDSP_carrier w pre r) _). split.
    - intros [He Hall]. split.
      + exact (proj2 (aspPartdsp_closed w pre r) He).
      + exact (proj2 (dslpPartdsp_closed w pre r) Hall).
    - intros [Ha Hd]. split.
      + exact (proj1 (aspPartdsp_closed w pre r) Ha).
      + exact (proj1 (dslpPartdsp_closed w pre r) Hd).
  Qed.

  Lemma bind_asp_parts {A B} (m : DSPSt A) (k : A -> DSPSt B) pre r :
    getASPSt (bindASPSt (aspPartdsp m) (fun a => aspPartdsp (k a))) pre r
    <-> (exists s, pre s /\
           (exists a smid,
               (getDSPSt m (fun _ => True) (a, smid)
                /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
               /\ (getDSPSt (k a) (fun _ => True) r
                   /\ ~ getDSPSt (k a) (fun t => t <> smid) r))).
  Proof.
    split.
    - intros [a Hk].
      destruct (proj1 (aspPartdsp_closed (k a)
                         (fun s0 => getASPSt (aspPartdsp m) pre (a, s0)) r) Hk)
        as [smid [Hp Hrk]].
      destruct (proj1 (aspPartdsp_closed m pre (a, smid)) Hp) as [s [Hps Hrm]].
      exists s. split; [ exact Hps |]. exists a, smid.
      split; [ exact Hrm | exact Hrk ].
    - intros [s [Hps [a [smid [Hrm Hrk]]]]].
      exists a.
      exact (proj2 (aspPartdsp_closed (k a)
                      (fun s0 => getASPSt (aspPartdsp m) pre (a, s0)) r)
               (ex_intro _ smid
                  (conj (proj2 (aspPartdsp_closed m pre (a, smid))
                           (ex_intro _ s (conj Hps Hrm))) Hrk))).
  Qed.

  Lemma bind_dslp_parts {A B} (m : DSPSt A) (k : A -> DSPSt B) pre r :
    getDSLPSt (bindDSLPSt (dslpPartdsp m) (fun a => dslpPartdsp (k a))) pre r
    <-> (forall s,
           (exists a smid,
               (getDSPSt m (fun _ => True) (a, smid)
                /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
               /\ (getDSPSt (k a) (fun _ => True) r
                   /\ ~ getDSPSt (k a) (fun t => t <> smid) r)) -> pre s).
  Proof.
    split.
    - intros H s [a [smid [Hrm Hrk]]].
      exact (proj1 (dslpPartdsp_closed m pre (a, smid))
               (proj1 (dslpPartdsp_closed (k a)
                         (fun s0 => getDSLPSt (dslpPartdsp m) pre (a, s0)) r)
                  (H a) smid Hrk) s Hrm).
    - intros H a.
      exact (proj2 (dslpPartdsp_closed (k a)
                      (fun s0 => getDSLPSt (dslpPartdsp m) pre (a, s0)) r)
               (fun smid Hrk =>
                  proj2 (dslpPartdsp_closed m pre (a, smid))
                    (fun s Hrm => H s (ex_intro _ a (ex_intro _ smid (conj Hrm Hrk))))))
      .
  Qed.

  #[program] Definition bindDSPSt {A B}
    (m : DSPSt A) (k : A -> DSPSt B) : DSPSt B :=
    fun pre r => bindASPSt (aspPartdsp m) (fun a => aspPartdsp (k a)) pre r /\
                   bindDSLPSt (dslpPartdsp m) (fun a => dslpPartdsp (k a)) pre r.
  Next Obligation.
    apply (dsp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists a smid,
                       (getDSPSt m (fun _ => True) (a, smid)
                        /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
                       /\ (getDSPSt (k a) (fun _ => True) r
                           /\ ~ getDSPSt (k a) (fun t => t <> smid) r)))
                /\ (forall s,
                      (exists a smid,
                          (getDSPSt m (fun _ => True) (a, smid)
                           /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
                          /\ (getDSPSt (k a) (fun _ => True) r
                              /\ ~ getDSPSt (k a) (fun t => t <> smid) r)) -> pre s))).
    - intros pre r. split.
      + intros [He Hall]. split;
          [ exact (proj2 (bind_asp_parts m k pre r) He)
          | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
      + intros [Ha Hd]. split;
          [ exact (proj1 (bind_asp_parts m k pre r) Ha)
          | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - apply dsp_shape_wf.
  Qed.

  Lemma bindDSPProg_dsp {A B} (m : DSPSt A) (k : A -> DSPSt B) pre r :
    getDSPSt (bindDSPSt m k) pre r
    <-> ((exists s, pre s /\
            (exists a smid,
                (getDSPSt m (fun _ => True) (a, smid)
                 /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
                /\ (getDSPSt (k a) (fun _ => True) r
                    /\ ~ getDSPSt (k a) (fun t => t <> smid) r)))
         /\ (forall s,
               (exists a smid,
                   (getDSPSt m (fun _ => True) (a, smid)
                    /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
                   /\ (getDSPSt (k a) (fun _ => True) r
                       /\ ~ getDSPSt (k a) (fun t => t <> smid) r)) -> pre s)).
  Proof.
    split.
    - intros [Ha Hd]. split;
        [ exact (proj1 (bind_asp_parts m k pre r) Ha)
        | exact (proj1 (bind_dslp_parts m k pre r) Hd) ].
    - intros [He Hall]. split;
        [ exact (proj2 (bind_asp_parts m k pre r) He)
        | exact (proj2 (bind_dslp_parts m k pre r) Hall) ].
  Qed.

  Lemma rec_retDSPProg {A} (a : A) (s : S) (r : A * S) :
    (getDSPSt (retDSPSt a) (fun _ => True) r
     /\ ~ getDSPSt (retDSPSt a) (fun t => t <> s) r)
    <-> r = (a, s).
  Proof. exact (dsp_recov (fun s0 r0 => r0 = (a, s0)) s r). Qed.

  Lemma rec_bindDSPProg {A B} (m : DSPSt A) (k : A -> DSPSt B)
    (s : S) (r : B * S) :
    (getDSPSt (bindDSPSt m k) (fun _ => True) r
     /\ ~ getDSPSt (bindDSPSt m k) (fun t => t <> s) r)
    <-> (exists a smid,
            (getDSPSt m (fun _ => True) (a, smid)
             /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
            /\ (getDSPSt (k a) (fun _ => True) r
                /\ ~ getDSPSt (k a) (fun t => t <> smid) r)).
  Proof.
    refine (iff_trans (dsp_rec_ext _ _ (bindDSPProg_dsp m k) s r)
              (dsp_recov
                 (fun s0 r0 =>
                    exists a smid,
                      (getDSPSt m (fun _ => True) (a, smid)
                       /\ ~ getDSPSt m (fun t => t <> s0) (a, smid))
                      /\ (getDSPSt (k a) (fun _ => True) r0
                          /\ ~ getDSPSt (k a) (fun t => t <> smid) r0))
                 s r)).
  Qed.

  #[global] Instance Monad__DSPSt : Monad DSPSt :=
    {| ret := fun _ => @retDSPSt _ ;
       bind := fun _ _ => @bindDSPSt _ _ |}.

  #[global] Instance Eq1__DSPSt : Eq1 DSPSt :=
    fun A m n => forall pre r, getDSPSt m pre r <-> getDSPSt n pre r.

  #[global] Instance Eq1Equivalence__DSPSt
    : @Eq1Equivalence DSPSt _ Eq1__DSPSt.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLawsE__DSPSt
    : @MonadLawsE DSPSt Eq1__DSPSt _.
  Proof.
    constructor.
    - (* bind_ret_l *)
      intros A B f x. unfold eq1, Eq1__DSPSt. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (getDSPSt (retDSPSt x) (fun _ => True) (a, smid)
                      /\ ~ getDSPSt (retDSPSt x) (fun t => t <> s) (a, smid))
                     /\ (getDSPSt (f a) (fun _ => True) r0
                         /\ ~ getDSPSt (f a) (fun t => t <> smid) r0))
                 <-> (getDSPSt (f x) (fun _ => True) r0
                      /\ ~ getDSPSt (f x) (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getDSPSt (retDSPSt x) (fun _ => True) r1
                                  /\ ~ getDSPSt (retDSPSt x) (fun t => t <> s1) r1)
                    (fun s1 r1 => r1 = (x, s1))
                    (fun a1 s1 r1 => getDSPSt (f a1) (fun _ => True) r1
                                     /\ ~ getDSPSt (f a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getDSPSt (f a1) (fun _ => True) r1
                                     /\ ~ getDSPSt (f a1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_retDSPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l x
                    (fun a1 s1 r1 => getDSPSt (f a1) (fun _ => True) r1
                                     /\ ~ getDSPSt (f a1) (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp (retDSPSt x) f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier (f x) pre r)))).
    - (* bind_ret_r *)
      intros A m. unfold eq1, Eq1__DSPSt. intros pre r.
      assert (Hc : forall (s : S) (r0 : A * S),
                 (exists a smid,
                     (getDSPSt m (fun _ => True) (a, smid)
                      /\ ~ getDSPSt m (fun t => t <> s) (a, smid))
                     /\ (getDSPSt (retDSPSt a) (fun _ => True) r0
                         /\ ~ getDSPSt (retDSPSt a) (fun t => t <> smid) r0))
                 <-> (getDSPSt m (fun _ => True) r0
                      /\ ~ getDSPSt m (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getDSPSt m (fun _ => True) r1
                                  /\ ~ getDSPSt m (fun t => t <> s1) r1)
                    (fun s1 r1 => getDSPSt m (fun _ => True) r1
                                  /\ ~ getDSPSt m (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getDSPSt (retDSPSt a1) (fun _ => True) r1
                                     /\ ~ getDSPSt (retDSPSt a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => r1 = (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retDSPProg a1 s1 r1) s r0)
                 (comp_ret_r
                    (fun s1 r1 => getDSPSt m (fun _ => True) r1
                                  /\ ~ getDSPSt m (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp m _ pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier m pre r)))).
    - (* bind_bind *)
      intros A B C x f g. unfold eq1, Eq1__DSPSt. intros pre r.
      assert (Hc : forall (s : S) (r0 : C * S),
                 (exists b smid,
                     (getDSPSt (bindDSPSt x f) (fun _ => True) (b, smid)
                      /\ ~ getDSPSt (bindDSPSt x f) (fun t => t <> s) (b, smid))
                     /\ (getDSPSt (g b) (fun _ => True) r0
                         /\ ~ getDSPSt (g b) (fun t => t <> smid) r0))
                 <-> (exists a smid,
                         (getDSPSt x (fun _ => True) (a, smid)
                          /\ ~ getDSPSt x (fun t => t <> s) (a, smid))
                         /\ (getDSPSt (bindDSPSt (f a) g) (fun _ => True) r0
                             /\ ~ getDSPSt (bindDSPSt (f a) g)
                                    (fun t => t <> smid) r0))).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getDSPSt (bindDSPSt x f) (fun _ => True) r1
                                  /\ ~ getDSPSt (bindDSPSt x f) (fun t => t <> s1) r1)
                    (fun s1 r1 =>
                       exists a smid,
                         (getDSPSt x (fun _ => True) (a, smid)
                          /\ ~ getDSPSt x (fun t => t <> s1) (a, smid))
                         /\ (getDSPSt (f a) (fun _ => True) r1
                             /\ ~ getDSPSt (f a) (fun t => t <> smid) r1))
                    (fun b1 s1 r1 => getDSPSt (g b1) (fun _ => True) r1
                                     /\ ~ getDSPSt (g b1) (fun t => t <> s1) r1)
                    (fun b1 s1 r1 => getDSPSt (g b1) (fun _ => True) r1
                                     /\ ~ getDSPSt (g b1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_bindDSPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc
                       (fun s1 r1 => getDSPSt x (fun _ => True) r1
                                     /\ ~ getDSPSt x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 => getDSPSt (f a1) (fun _ => True) r1
                                        /\ ~ getDSPSt (f a1) (fun t => t <> s1) r1)
                       (fun b1 s1 r1 => getDSPSt (g b1) (fun _ => True) r1
                                        /\ ~ getDSPSt (g b1) (fun t => t <> s1) r1)
                       s r0)
                    (comp_cong
                       (fun s1 r1 => getDSPSt x (fun _ => True) r1
                                     /\ ~ getDSPSt x (fun t => t <> s1) r1)
                       (fun s1 r1 => getDSPSt x (fun _ => True) r1
                                     /\ ~ getDSPSt x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 =>
                          exists b smid,
                            (getDSPSt (f a1) (fun _ => True) (b, smid)
                             /\ ~ getDSPSt (f a1) (fun t => t <> s1) (b, smid))
                            /\ (getDSPSt (g b) (fun _ => True) r1
                                /\ ~ getDSPSt (g b) (fun t => t <> smid) r1))
                       (fun a1 s1 r1 =>
                          getDSPSt (bindDSPSt (f a1) g) (fun _ => True) r1
                          /\ ~ getDSPSt (bindDSPSt (f a1) g) (fun t => t <> s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindDSPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindDSPProg_dsp (bindDSPSt x f) g pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp x (fun a => bindDSPSt (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__DSPSt in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : B * S),
                 (exists a smid,
                     (getDSPSt x (fun _ => True) (a, smid)
                      /\ ~ getDSPSt x (fun t => t <> s) (a, smid))
                     /\ (getDSPSt (f a) (fun _ => True) r0
                         /\ ~ getDSPSt (f a) (fun t => t <> smid) r0))
                 <-> (exists a smid,
                         (getDSPSt y (fun _ => True) (a, smid)
                          /\ ~ getDSPSt y (fun t => t <> s) (a, smid))
                         /\ (getDSPSt (g a) (fun _ => True) r0
                             /\ ~ getDSPSt (g a) (fun t => t <> smid) r0))).
      { intros s r0.
        exact (comp_cong
                 (fun s1 r1 => getDSPSt x (fun _ => True) r1
                               /\ ~ getDSPSt x (fun t => t <> s1) r1)
                 (fun s1 r1 => getDSPSt y (fun _ => True) r1
                               /\ ~ getDSPSt y (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getDSPSt (f a1) (fun _ => True) r1
                                  /\ ~ getDSPSt (f a1) (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getDSPSt (g a1) (fun _ => True) r1
                                  /\ ~ getDSPSt (g a1) (fun t => t <> s1) r1)
                 (fun s1 r1 => dsp_rec_ext (getDSPSt x) (getDSPSt y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    dsp_rec_ext (getDSPSt (f a1)) (getDSPSt (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindDSPProg_dsp x f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp y g pre r)))).
  Qed.

End ProgDSPMonad.

Arguments retDSPSt {_} {_}.
Arguments bindDSPSt {_} {_} {_}.
Arguments getDSPSt {_} {_}.


(* ---- order and monotonicity ---- *)

Section StDSPOrders.
  Variable S : Type.
  Definition ordDSPSt {A} (m1 m2 : DSPSt S A) : Prop :=
    forall pre r, getDSPSt m1 pre r -> getDSPSt m2 pre r.
  Lemma dspMono {A} (w : DSPSt S A) (P Q : S -> Prop) (r : (A * S)) :
    (forall s, P s -> Q s) -> getDSPSt w P r -> getDSPSt w Q r.
  Proof.
    exact (conjunctive_implies_monotone S (getDSPSt w) (proj2 (proj2_sig w)) P Q r).
  Qed.
  (** Inclusion of the recovered relation.  Unlike [ordDSPSt], [bind] is
      monotone for it; see [SpecificationMonads.v]. *)
  Definition ordDSPStRel {A} (m1 m2 : DSPSt S A) : Prop :=
    forall s r,
      (getDSPSt m1 (fun _ => True) r /\ ~ getDSPSt m1 (fun t => t <> s) r) ->
      (getDSPSt m2 (fun _ => True) r /\ ~ getDSPSt m2 (fun t => t <> s) r).
End StDSPOrders.
Arguments ordDSPSt {_} {_}.
Arguments ordDSPStRel {_} {_}.
End StDSP.

(* ================================================================= *)
(** * Refinement order and monotonicity for DSP *)
(* ================================================================= *)

Section DSPOrders.
  Variable S : Type.
  Definition ordDSPStExc {A} (m1 m2 : DSPStExc S A) : Prop :=
    forall pre r, getDSPStExc m1 pre r -> getDSPStExc m2 pre r.
  Lemma dspMono {A} (w : DSPStExc S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getDSPStExc w P r -> getDSPStExc w Q r.
  Proof.
    exact (conjunctive_implies_monotone S (getDSPStExc w) (proj2 (proj2_sig w)) P Q r).
  Qed.
  (** Inclusion of the recovered relation.  Unlike [ordDSPStExc], [bind] is
      monotone for it; see [SpecificationMonads.v]. *)
  Definition ordDSPStExcRel {A} (m1 m2 : DSPStExc S A) : Prop :=
    forall s r,
      (getDSPStExc m1 (fun _ => True) r /\ ~ getDSPStExc m1 (fun t => t <> s) r) ->
      (getDSPStExc m2 (fun _ => True) r /\ ~ getDSPStExc m2 (fun t => t <> s) r).
End DSPOrders.

Arguments ordDSPStExc {_} {_}.
Arguments ordDSPStExcRel {_} {_}.

(* ================================================================= *)
(** ** The reader-indexed variant                                    *)
(* ================================================================= *)

(** [DSPRd R A = readerT R DSPSP A]: one [DSPSP] per environment.  The
    precondition slot stays a bare [Prop], so environments are specified
    INDEPENDENTLY — the pointwise lift, not a shared [R -> Prop].  Note that [DSPSP] already collapses onto [ASPSP]
    (see [strict_conj_iff_singleton] above), so this pointwise lift inherits
    that collapse: it does NOT recover the DSP/ASP distinction, which needs a
    shared [R -> Prop] precondition.

    Laws come from the generic [readerT] instances in
    [ComputationMonads/TransformerLaws.v] over [Monad_DSPSP]. *)

From ExtLib Require Import ReaderMonad.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws.

Section RdDSPMonad.
  Variable R : Type.

  Definition DSPRd (A : Type) : Type := readerT R DSPSP A.

  Definition getDSPRd {A} (w : DSPRd A) (r : R) : SPPure A :=
    getDSP (runReaderT w r).

  #[global] Instance Monad__DSPRd : Monad DSPRd :=
    @Monad_readerT R DSPSP Monad_DSPSP.

  #[global] Instance Eq1__DSPRd : Eq1 DSPRd :=
    Eq1_readerT R DSPSP.

  #[global] Instance Eq1Equivalence__DSPRd
    : @Eq1Equivalence DSPRd _ Eq1__DSPRd :=
    Eq1Equivalence_readerT R DSPSP.

  #[global] Instance MonadLawsE__DSPRd
    : @MonadLawsE DSPRd Eq1__DSPRd Monad__DSPRd :=
    MonadLawsE_readerT R DSPSP.

  Definition ordDSPRd {A} (m1 m2 : DSPRd A) : Prop :=
    forall r p a, getDSPRd m1 r p a -> getDSPRd m2 r p a.
  Definition ordDSPRdAt {A} (pre : R -> Prop) (m1 m2 : DSPRd A) : Prop :=
    forall r a, getDSPRd m1 r (pre r) a -> getDSPRd m2 r (pre r) a.

End RdDSPMonad.

Arguments getDSPRd {_} {_}.
