(** * Demonic strongest postcondition

    [obsDSP] is the CONJUNCTION of the angelic and the demonic-liberal
    readings of the observed relation: [r] is asserted at [pre] when some
    [pre]-state reaches [r] AND every state that reaches [r] is a
    [pre]-state.  Equivalently, [pre] is exactly the set of states from which
    [r] is reachable.  It is the strict positively-meet-preserving fragment
    of the ambient transformer space. *)

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
From Incorrectness.Recipes.Examples.StExDv.Logics Require Import ASP DLSP.

Import MonadNotation.
Open Scope monad_scope.

Section ProgDSPMonad.
  Variable S : Type.

  Definition StrictPositivelyMeetPreservingProg {A} (w : ProgSP A) : Prop :=
    StrictProg S w /\ ConjunctiveProg S w.

  Definition DSPProgSP (A : Type) : Type :=
    { w : ProgSP A | StrictPositivelyMeetPreservingProg w }.

  Definition getProgDSP {A} (w : DSPProgSP A) : ProgSP A := proj1_sig w.

  (** ** Recovery, well-formedness, congruence

      Everything below is stated about the raw transformer
      [fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s)]
      and about the composite relation, written out; no auxiliary definitions
      are introduced. *)

  (** Probing that transformer at [fun _ => True] and at the co-singleton of
      [s] recovers [R s r] exactly.  This is the ONLY use of classical logic
      in the section: from "some state reaches [r]" together with "[fun t =>
      t <> s] is not a valid precondition for [r]" one concludes [R s r]. *)
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

  (** Consequently every such transformer inhabits [DSPProgSP]: this discharges
      each of the [#[program]] obligations below. *)
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
  Lemma dsp_rec_ext {A} (w1 w2 : @ProgSP S A)
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

  (** The carrier condition [StrictPositivelyMeetPreservingProg] says the same
      thing as "[w] is the DSP of its own recovered relation".  This is the
      bridge between the healthiness reading (which the type states) and the
      fixed-point reading (which the proofs use). *)
  Lemma dsp_carrier {A} (w : ProgSP A) :
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
  Proof. apply dsp_carrier. intros pre r. exact (dsp_wf R pre r). Qed.

  (** ... and every carrier element is the DSP of its recovered relation. *)
  Lemma getProgDSP_carrier {A} (w : DSPProgSP A)
    (pre : S -> Prop) (r : option (A * S)) :
    getProgDSP w pre r <->
      ((exists s, pre s /\ (getProgDSP w (fun _ => True) r
                            /\ ~ getProgDSP w (fun t => t <> s) r)) /\
         (forall s, (getProgDSP w (fun _ => True) r
                     /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s)).
  Proof. exact (proj1 (dsp_carrier (getProgDSP w)) (proj2_sig w) pre r). Qed.

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

  #[program] Definition retDSPProg {A} (a : A) : DSPProgSP A :=
    fun pre r => (retASPProg a pre r) /\ (retDSLPProg a pre r).
  Next Obligation. exact (dsp_shape_wf (fun s r => r = Some (a, s))). Qed.

  (* We would like bindDSPProg to match retDSPProg, but this requires
     converting DSPProgSP to both ASPProgSP and DSLPProgSP. *)

  (** The two probe forms are the ASP and the DSLP of the recovered relation. *)
  Lemma aspPartdsp_closed {A} (w : DSPProgSP A) pre r :
    (getProgDSP w (fun _ => True) r /\ ~ getProgDSP w (fun s => ~ pre s) r)
    <-> (exists s, pre s /\ (getProgDSP w (fun _ => True) r
                             /\ ~ getProgDSP w (fun t => t <> s) r)).
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

  Lemma dslpPartdsp_closed {A} (w : DSPProgSP A) pre r :
    (getProgDSP w (fun _ => True) r -> getProgDSP w pre r)
    <-> (forall s, (getProgDSP w (fun _ => True) r
                    /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s).
  Proof.
    split.
    - intros H s Hs. refine (proj2 (proj1 (getProgDSP_carrier w pre r) (H _)) s Hs).
      apply getProgDSP_carrier. split;
        [ exists s; split; [ exact I | exact Hs ] | intros; exact I ].
    - intros Hall Htop. apply getProgDSP_carrier.
      destruct (proj1 (getProgDSP_carrier w (fun _ => True) r) Htop) as [[s0 [_ Hr0]] _].
      split; [ exists s0; split; [ exact (Hall s0 Hr0) | exact Hr0 ] | exact Hall ].
  Qed.

  (** Both healthiness classes transport along pointwise equivalence. *)
  Lemma singletonProg_ext {A} (w1 w2 : @ProgSP S A) :
    (forall pre r, w1 pre r <-> w2 pre r) -> SingletonProg S w1 -> SingletonProg S w2.
  Proof.
    intros Hext H pre r. split.
    - intro Hw. destruct (proj1 (H pre r) (proj2 (Hext pre r) Hw)) as [s0 [Hp Hs]].
      exists s0. split; [ exact Hp | exact (proj1 (Hext _ r) Hs) ].
    - intros [s0 [Hp Hs]]. apply Hext. apply (H pre r).
      exists s0. split; [ exact Hp | exact (proj2 (Hext _ r) Hs) ].
  Qed.

  Lemma dsp_healthy_ext {A} (w1 w2 : @ProgSP S A) :
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

  #[program] Definition aspPartdsp {A} (w : DSPProgSP A) : ASPProgSP S A :=
    fun pre r => getProgDSP w (fun _ => True) r /\ ~ getProgDSP w (fun s => ~ pre s) r.
  Next Obligation.
    apply (singletonProg_ext
             (fun pre r => exists s, pre s /\ (getProgDSP w (fun _ => True) r
                                               /\ ~ getProgDSP w (fun t => t <> s) r))).
    - intros pre r. exact (iff_sym (aspPartdsp_closed w pre r)).
    - intros pre r. split.
      + intros [s [Hp Hs]]. exists s. split; [ exact Hp |].
        exists s. split; [ reflexivity | exact Hs ].
      + intros [s0 [Hp [s [Heq Hs]]]]. subst s.
        exists s0. split; [ exact Hp | exact Hs ].
  Qed.

  #[program] Definition dslpPartdsp {A} (w : DSPProgSP A) : DSLPProgSP S A :=
    fun pre r => getProgDSP w (fun _ => True) r -> getProgDSP w pre r.
  Next Obligation.
    apply (msingletonProg_ext S
             (fun pre r => forall s, (getProgDSP w (fun _ => True) r
                                      /\ ~ getProgDSP w (fun t => t <> s) r) -> pre s)).
    - intros pre r. exact (iff_sym (dslpPartdsp_closed w pre r)).
    - apply dslp_msingleton.
  Qed.

  Theorem dsp_split {A} (w : DSPProgSP A) pre r :
    getProgDSP w pre r <-> (getProgASP (aspPartdsp w) pre r /\ getProgDSLP (dslpPartdsp w) pre r).
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
  Lemma bind_asp_parts {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgASP (bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a))) pre r
    <-> (exists s, pre s /\
           (exists o, (getProgDSP m (fun _ => True) o
                       /\ ~ getProgDSP m (fun t => t <> s) o)
                      /\ match o with
                         | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                             /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                         | None => r = None
                         end)).
  Proof.
    split.
    - intros [[a Hk] | [Hr Hm]].
      + destruct (proj1 (aspPartdsp_closed (k a)
                           (fun s0 => getProgASP (aspPartdsp m) pre (Some (a, s0))) r) Hk)
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
                        (fun s0 => getProgASP (aspPartdsp m) pre (Some (a, s0))) r)
                 (ex_intro _ smid
                    (conj (proj2 (aspPartdsp_closed m pre (Some (a, smid)))
                             (ex_intro _ s (conj Hps Hrm))) Hrk))).
      + right. split; [ exact Hrk |].
        exact (proj2 (aspPartdsp_closed m pre None) (ex_intro _ s (conj Hps Hrm))).
  Qed.

  Lemma bind_dslp_parts {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgDSLP (bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a))) pre r
    <-> (forall s,
           (exists o, (getProgDSP m (fun _ => True) o
                       /\ ~ getProgDSP m (fun t => t <> s) o)
                      /\ match o with
                         | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                             /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                         | None => r = None
                         end) -> pre s).
  Proof.
    split.
    - intros [H1 H2] s [[[a smid]|] [Hrm Hrk]].
      + exact (proj1 (dslpPartdsp_closed m pre (Some (a, smid)))
                 (proj1 (dslpPartdsp_closed (k a)
                           (fun s0 => getProgDSLP (dslpPartdsp m) pre (Some (a, s0))) r)
                    (H1 a) smid Hrk) s Hrm).
      + exact (proj1 (dslpPartdsp_closed m pre None) (H2 Hrk) s Hrm).
    - intro H. split.
      + intro a.
        exact (proj2 (dslpPartdsp_closed (k a)
                        (fun s0 => getProgDSLP (dslpPartdsp m) pre (Some (a, s0))) r)
                 (fun smid Hrk =>
                    proj2 (dslpPartdsp_closed m pre (Some (a, smid)))
                      (fun s Hrm => H s (ex_intro _ (Some (a, smid)) (conj Hrm Hrk))))).
      + intro Hr.
        exact (proj2 (dslpPartdsp_closed m pre None)
                 (fun s Hrm => H s (ex_intro _ None (conj Hrm Hr)))).
  Qed.

  #[program] Definition bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) : DSPProgSP B :=
    fun pre r => bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a)) pre r /\
                   bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a)) pre r.
  Next Obligation.
    apply (dsp_healthy_ext
             (fun pre r =>
                (exists s, pre s /\
                   (exists o, (getProgDSP m (fun _ => True) o
                               /\ ~ getProgDSP m (fun t => t <> s) o)
                              /\ match o with
                                 | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                                     /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                                 | None => r = None
                                 end))
                /\ (forall s,
                      (exists o, (getProgDSP m (fun _ => True) o
                                  /\ ~ getProgDSP m (fun t => t <> s) o)
                                 /\ match o with
                                    | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                                        /\ ~ getProgDSP (k a) (fun t => t <> smid) r
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

  (** The relation recovered from [retDSPProg a] is [fun s r => r = Some (a, s)]. *)
  Lemma rec_retDSPProg {A} (a : A) (s : S) (r : option (A * S)) :
    (getProgDSP (retDSPProg a) (fun _ => True) r
     /\ ~ getProgDSP (retDSPProg a) (fun t => t <> s) r)
    <-> r = Some (a, s).
  Proof. exact (dsp_recov (fun s0 r0 => r0 = Some (a, s0)) s r). Qed.

  (** [bindDSPProg m k] is pointwise the DSP of the composite relation. *)
  Lemma bindDSPProg_dsp {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) pre r :
    getProgDSP (bindDSPProg m k) pre r
    <-> ((exists s, pre s /\
            (exists o, (getProgDSP m (fun _ => True) o
                        /\ ~ getProgDSP m (fun t => t <> s) o)
                       /\ match o with
                          | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                              /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                          | None => r = None
                          end))
         /\ (forall s,
               (exists o, (getProgDSP m (fun _ => True) o
                           /\ ~ getProgDSP m (fun t => t <> s) o)
                          /\ match o with
                             | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                                 /\ ~ getProgDSP (k a) (fun t => t <> smid) r
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

  (** The relation recovered from [bindDSPProg m k] is the composite. *)
  Lemma rec_bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B)
    (s : S) (r : option (B * S)) :
    (getProgDSP (bindDSPProg m k) (fun _ => True) r
     /\ ~ getProgDSP (bindDSPProg m k) (fun t => t <> s) r)
    <-> (exists o, (getProgDSP m (fun _ => True) o
                    /\ ~ getProgDSP m (fun t => t <> s) o)
                   /\ match o with
                      | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                                          /\ ~ getProgDSP (k a) (fun t => t <> smid) r
                      | None => r = None
                      end).
  Proof.
    refine (iff_trans (dsp_rec_ext _ _ (bindDSPProg_dsp m k) s r)
              (dsp_recov
                 (fun s0 r0 =>
                    exists o, (getProgDSP m (fun _ => True) o
                               /\ ~ getProgDSP m (fun t => t <> s0) o)
                              /\ match o with
                                 | Some (a, smid) => getProgDSP (k a) (fun _ => True) r0
                                                     /\ ~ getProgDSP (k a) (fun t => t <> smid) r0
                                 | None => r0 = None
                                 end)
                 s r)).
  Qed.

  #[global]
    Instance Monad__DSPProgSP : Monad DSPProgSP :=
    {| ret := fun _ => @retDSPProg _ ;
      bind := fun _ _ => @bindDSPProg _ _ |}.

  #[global] Instance Eq1__ProgDSP : Eq1 DSPProgSP :=
    fun A m n => forall pre r, getProgDSP m pre r <-> getProgDSP n pre r.

  #[global] Instance Eq1Equivalence__DSPProgSP
    : @Eq1Equivalence DSPProgSP _ Eq1__ProgDSP.
  Proof.
    intro A. constructor.
    - intros x pre r. tauto.
    - intros x y H pre r. specialize (H pre r). tauto.
    - intros x y z H1 H2 pre r. specialize (H1 pre r). specialize (H2 pre r). tauto.
  Qed.

  #[global] Instance MonadLaws__ProgDSP
    : @MonadLawsE DSPProgSP Eq1__ProgDSP _.
  Proof.
    constructor.
    - (* bind_ret_l : the composite of [retDSPProg x] with [f] is [f x] *)
      intros A B f x. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (getProgDSP (retDSPProg x) (fun _ => True) o
                             /\ ~ getProgDSP (retDSPProg x) (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (f a) (fun _ => True) r0
                                   /\ ~ getProgDSP (f a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (getProgDSP (f x) (fun _ => True) r0
                      /\ ~ getProgDSP (f x) (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP (retDSPProg x) (fun _ => True) r1
                                  /\ ~ getProgDSP (retDSPProg x) (fun t => t <> s1) r1)
                    (fun s1 r1 => r1 = Some (x, s1))
                    (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_retDSPProg x s1 r1)
                    (fun a1 s1 r1 => iff_refl _) s r0)
                 (comp_ret_l x
                    (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp (retDSPProg x) f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier (f x) pre r)))).
    - (* bind_ret_r : the composite of [m] with [retDSPProg] is [m] *)
      intros A m. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (A * S)),
                 (exists o, (getProgDSP m (fun _ => True) o
                             /\ ~ getProgDSP m (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (retDSPProg a) (fun _ => True) r0
                                   /\ ~ getProgDSP (retDSPProg a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (getProgDSP m (fun _ => True) r0
                      /\ ~ getProgDSP m (fun t => t <> s) r0)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => getProgDSP (retDSPProg a1) (fun _ => True) r1
                                     /\ ~ getProgDSP (retDSPProg a1) (fun t => t <> s1) r1)
                    (fun a1 s1 r1 => r1 = Some (a1, s1))
                    (fun s1 r1 => iff_refl _)
                    (fun a1 s1 r1 => rec_retDSPProg a1 s1 r1) s r0)
                 (comp_ret_r
                    (fun s1 r1 => getProgDSP m (fun _ => True) r1
                                  /\ ~ getProgDSP m (fun t => t <> s1) r1)
                    s r0)). }
      exact (iff_trans (bindDSPProg_dsp m _ pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (getProgDSP_carrier m pre r)))).
    - (* bind_bind : associativity of the composite *)
      intros A B C x f g. unfold eq1, Eq1__ProgDSP. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (C * S)),
                 (exists o, (getProgDSP (bindDSPProg x f) (fun _ => True) o
                             /\ ~ getProgDSP (bindDSPProg x f) (fun t => t <> s) o)
                            /\ match o with
                               | Some (b, smid) =>
                                   getProgDSP (g b) (fun _ => True) r0
                                   /\ ~ getProgDSP (g b) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (getProgDSP x (fun _ => True) o
                                 /\ ~ getProgDSP x (fun t => t <> s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       getProgDSP (bindDSPProg (f a) g) (fun _ => True) r0
                                       /\ ~ getProgDSP (bindDSPProg (f a) g)
                                              (fun t => t <> smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (iff_trans
                 (comp_cong
                    (fun s1 r1 => getProgDSP (bindDSPProg x f) (fun _ => True) r1
                                  /\ ~ getProgDSP (bindDSPProg x f) (fun t => t <> s1) r1)
                    (fun s1 r1 =>
                       exists o, (getProgDSP x (fun _ => True) o
                                  /\ ~ getProgDSP x (fun t => t <> s1) o)
                                 /\ match o with
                                    | Some (a, smid) =>
                                        getProgDSP (f a) (fun _ => True) r1
                                        /\ ~ getProgDSP (f a) (fun t => t <> smid) r1
                                    | None => r1 = None
                                    end)
                    (fun b1 s1 r1 => getProgDSP (g b1) (fun _ => True) r1
                                     /\ ~ getProgDSP (g b1) (fun t => t <> s1) r1)
                    (fun b1 s1 r1 => getProgDSP (g b1) (fun _ => True) r1
                                     /\ ~ getProgDSP (g b1) (fun t => t <> s1) r1)
                    (fun s1 r1 => rec_bindDSPProg x f s1 r1)
                    (fun b1 s1 r1 => iff_refl _) s r0)
                 (iff_trans
                    (comp_assoc
                       (fun s1 r1 => getProgDSP x (fun _ => True) r1
                                     /\ ~ getProgDSP x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                        /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                       (fun b1 s1 r1 => getProgDSP (g b1) (fun _ => True) r1
                                        /\ ~ getProgDSP (g b1) (fun t => t <> s1) r1)
                       s r0)
                    (comp_cong
                       (fun s1 r1 => getProgDSP x (fun _ => True) r1
                                     /\ ~ getProgDSP x (fun t => t <> s1) r1)
                       (fun s1 r1 => getProgDSP x (fun _ => True) r1
                                     /\ ~ getProgDSP x (fun t => t <> s1) r1)
                       (fun a1 s1 r1 =>
                          exists o, (getProgDSP (f a1) (fun _ => True) o
                                     /\ ~ getProgDSP (f a1) (fun t => t <> s1) o)
                                    /\ match o with
                                       | Some (b, smid) =>
                                           getProgDSP (g b) (fun _ => True) r1
                                           /\ ~ getProgDSP (g b) (fun t => t <> smid) r1
                                       | None => r1 = None
                                       end)
                       (fun a1 s1 r1 =>
                          getProgDSP (bindDSPProg (f a1) g) (fun _ => True) r1
                          /\ ~ getProgDSP (bindDSPProg (f a1) g) (fun t => t <> s1) r1)
                       (fun s1 r1 => iff_refl _)
                       (fun a1 s1 r1 => iff_sym (rec_bindDSPProg (f a1) g s1 r1))
                       s r0))). }
      exact (iff_trans (bindDSPProg_dsp (bindDSPProg x f) g pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp x (fun a => bindDSPProg (f a) g) pre r)))).
    - (* Proper_bind *)
      intros A B x y Hxy f g Hfg. unfold eq1, Eq1__ProgDSP in *. intros pre r.
      assert (Hc : forall (s : S) (r0 : option (B * S)),
                 (exists o, (getProgDSP x (fun _ => True) o
                             /\ ~ getProgDSP x (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (f a) (fun _ => True) r0
                                   /\ ~ getProgDSP (f a) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
                 <-> (exists o, (getProgDSP y (fun _ => True) o
                                 /\ ~ getProgDSP y (fun t => t <> s) o)
                                /\ match o with
                                   | Some (a, smid) =>
                                       getProgDSP (g a) (fun _ => True) r0
                                       /\ ~ getProgDSP (g a) (fun t => t <> smid) r0
                                   | None => r0 = None
                                   end)).
      { intros s r0.
        exact (comp_cong
                 (fun s1 r1 => getProgDSP x (fun _ => True) r1
                               /\ ~ getProgDSP x (fun t => t <> s1) r1)
                 (fun s1 r1 => getProgDSP y (fun _ => True) r1
                               /\ ~ getProgDSP y (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getProgDSP (f a1) (fun _ => True) r1
                                  /\ ~ getProgDSP (f a1) (fun t => t <> s1) r1)
                 (fun a1 s1 r1 => getProgDSP (g a1) (fun _ => True) r1
                                  /\ ~ getProgDSP (g a1) (fun t => t <> s1) r1)
                 (fun s1 r1 => dsp_rec_ext (getProgDSP x) (getProgDSP y) Hxy s1 r1)
                 (fun a1 s1 r1 =>
                    dsp_rec_ext (getProgDSP (f a1)) (getProgDSP (g a1)) (Hfg a1) s1 r1)
                 s r0). }
      exact (iff_trans (bindDSPProg_dsp x f pre r)
               (iff_trans (dsp_cong _ _ Hc pre r)
                  (iff_sym (bindDSPProg_dsp y g pre r)))).
  Qed.
End ProgDSPMonad.

Arguments retDSPProg {_} {_}.
Arguments bindDSPProg {_} {_} {_}.
Arguments getProgDSP {_} {_}.

(* ==================================================================== *)
(** * Refinement order and comparison targets                            *)
(* ==================================================================== *)

Section SpecOrdersDSP.
  Variable S : Type.

  Definition ordProgDSP {A} (m1 m2 : DSPProgSP S A) : Prop :=
    forall pre r, getProgDSP m1 pre r -> getProgDSP m2 pre r.
  Lemma dspMono {A} (w : DSPProgSP S A) (P Q : S -> Prop) (r : option (A * S)) :
    (forall s, P s -> Q s) -> getProgDSP w P r -> getProgDSP w Q r.
  Proof.
    intros Hsub Hw.
    destruct (proj1 (getProgDSP_carrier S w P r) Hw) as [[s [Hp Hrec]] Hall].
    apply getProgDSP_carrier. split.
    - exists s. split; [ exact (Hsub s Hp) | exact Hrec ].
    - intros s' Hrec'. exact (Hsub s' (Hall s' Hrec')).
  Qed.
  Theorem gen_dsp_over_raw {A} (w : DSPProgSP S A) pre post :
    (forall r, getProgDSP w pre r -> post r)
    <-> ordProgSP (getProgDSP w) (pp2_over pre post).
  Proof.
    split.
    - intros H p r Hw Hsub. exact (H r (dspMono w p pre r Hsub Hw)).
    - intros H r Hw. exact (H pre r Hw (fun s Hs => Hs)).
  Qed.

  Theorem gen_dsp_under_raw {A} (w : DSPProgSP S A) pre post :
    (forall r, post r -> getProgDSP w pre r)
    <-> ordProgSP (pp2_under pre post) (getProgDSP w).
  Proof.
    split.
    - intros H p r [Hsub Hpost]. exact (dspMono w pre p r Hsub (H r Hpost)).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
  Qed.
End SpecOrdersDSP.

Arguments ordProgDSP {_} {_}.

(* ==================================================================== *)
(** * The demonic recipe layer                                           *)
(* ==================================================================== *)

Section DSPRecipes.

  Variable S : Type.

  #[program] Definition dspOf {A} (R : SPRel S A) : DSPProgSP S A :=
    fun pre r => (exists s, pre s /\ R s r) /\ (forall s, R s r -> pre s).
  Next Obligation. exact (dsp_shape_wf S R). Qed.

  Definition dspRel {A} (w : DSPProgSP S A) : SPRel S A :=
    fun s r =>
      getProgDSP w (fun _ => True) r /\ ~ getProgDSP w (fun t => t <> s) r.

  Lemma dspRel_of {A} (R : SPRel S A) :
    forall s r, dspRel (dspOf R) s r <-> R s r.
  Proof. intros s r. exact (dsp_recov S R s r). Qed.

  Lemma dspOf_rel {A} (w : DSPProgSP S A) (pre : S -> Prop) r :
    getProgDSP w pre r <-> getProgDSP (dspOf (dspRel w)) pre r.
  Proof. exact (getProgDSP_carrier S w pre r). Qed.

  Definition dspLe : OrderM (DSPProgSP S) :=
    fun A w1 w2 => relLe (dspRel w1) (dspRel w2).

  #[global] Instance OrderedMonad_DSPProgSP :
    @OrderedMonad (DSPProgSP S) (Monad__DSPProgSP S) dspLe.
  Proof.
    constructor.
    - intros A w s r H. exact H.
    - intros A x y z Hxy Hyz s r H. exact (Hyz s r (Hxy s r H)).
    - intros A B x y f g Hxy Hfg s r H.
      apply (rec_bindDSPProg S y g s r).
      apply (compRel_mono (dspRel x) (dspRel y)
               (fun a => dspRel (f a)) (fun a => dspRel (g a)) Hxy Hfg).
      exact (proj1 (rec_bindDSPProg S x f s r) H).
  Qed.

  Lemma eqLeDSP {A} (x y : DSPProgSP S A) :
    @eq1 (DSPProgSP S) (Eq1__ProgDSP S) A x y -> dspLe A x y.
  Proof.
    intros H s r [Htop Hn]. split.
    - exact (proj1 (H (fun _ => True) r) Htop).
    - intro Hc. exact (Hn (proj2 (H (fun t => t <> s) r) Hc)).
  Qed.

  Definition truthDSP : TruthOrder (DSPProgSP S) dspLe.
  Proof.
    refine {| trueW := fun A => dspOf (fun (_ : S) (_ : option (A * S)) => True);
              falseW := fun A => dspOf (fun (_ : S) (_ : option (A * S)) => False);
              truthPolarity := Forward |}.
    intros A w. split.
    - intros s r H. destruct (proj1 (dspRel_of _ s r) H).
    - intros s r H. apply dspRel_of. exact I.
  Defined.

  Definition makeDSPDM
    (observation : EffectObs (prog S) (DSPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (DSPProgSP S)
        (Monad__nditprog S) (Monad__DSPProgSP S) (Eq1__ProgDSP S) observation)
    : DMRecipe (prog S) (DSPProgSP S) :=
    {| monadM := Monad__nditprog S;
       eqM := Eq1__nditprog S;
       eqEquivM := Eq1Equivalence_nditprog S;
       lawsM := MonadLawsE__nditprog S;
       monadW := Monad__DSPProgSP S;
       eqW := Eq1__ProgDSP S;
       eqEquivW := Eq1Equivalence__DSPProgSP S;
       lawsW := MonadLaws__ProgDSP S;
       orderW := dspLe;
       orderedW := OrderedMonad_DSPProgSP;
       eqLeW := @eqLeDSP;
       truthOrder := truthDSP;
       theta := observation;
       thetaMorphism := morphism |}.

  Definition logicDSP
    (observation : EffectObs (prog S) (DSPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (DSPProgSP S)
        (Monad__nditprog S) (Monad__DSPProgSP S) (Eq1__ProgDSP S) observation)
    : Logic (makeDSPDM observation morphism).
  Proof.
    refine {|
      meetW := fun A x y => dspOf (fun s r => dspRel x s r /\ dspRel y s r);
      joinW := fun A x y => dspOf (fun s r => dspRel x s r \/ dspRel y s r)
    |}.
    - intros A x y z. cbn. unfold dspLe, relLe. split.
      + intro H. split; intros s r Hx;
          [ exact (proj1 (proj1 (dspRel_of _ s r) (H s r Hx)))
          | exact (proj2 (proj1 (dspRel_of _ s r) (H s r Hx))) ].
      + intros [Hy Hz] s r Hx. apply dspRel_of.
        split; [exact (Hy s r Hx) | exact (Hz s r Hx)].
    - intros A x y z. cbn. unfold dspLe, relLe. split.
      + intro H. split; intros s r Hw; apply H; apply dspRel_of;
          [left | right]; exact Hw.
      + intros [Hx Hy] s r Hw.
        destruct (proj1 (dspRel_of _ s r) Hw) as [H | H];
          [exact (Hx s r H) | exact (Hy s r H)].
  Defined.

  Definition makeDSPRecipe
    (observation : EffectObs (prog S) (DSPProgSP S))
    (morphism :
      @MonadMorphism (prog S) (DSPProgSP S)
        (Monad__nditprog S) (Monad__DSPProgSP S) (Eq1__ProgDSP S) observation)
    : LogicRecipe (prog S) (DSPProgSP S) :=
    {| recipeDM := makeDSPDM observation morphism;
       recipeLogic := logicDSP observation morphism |}.

End DSPRecipes.

Arguments dspOf {_} {_}.
Arguments dspRel {_} {_}.
Arguments dspLe {_} {_}.

Definition dspMonoSP {S A} (w : DSPProgSP S A) : MonoSP (getProgDSP w) :=
  dspMono S w.

(* ==================================================================== *)
(** * The observation                                                    *)
(* ==================================================================== *)

(** The conjunction of the angelic and the demonic-liberal readings of the
    same terminating slice.  [StrictPositivelyMeetPreservingProg] holds
    because that conjunction is exactly the DSP shape established above. *)
#[program] Definition obsDSP {S A} (m : prog S A) : DSPProgSP S A :=
  fun pre r => (obsASP m pre r) /\ (obsDSLP m pre r).
Next Obligation.
  exact (dsp_shape_wf S
           (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
Qed.

Lemma getProgDSP_obsDSP {S A} (m : prog S A) pre r :
  getProgDSP (obsDSP m) pre r
  <-> ((exists s, pre s /\ obsRel m s r) /\ (forall s, obsRel m s r -> pre s)).
Proof. split; intro H; exact H. Qed.

(** [obsDSP m] is the DSP of exactly the relation [obsRel m]. *)
Lemma dspRel_obsDSP {S A} (m : prog S A) :
  forall s r, dspRel (obsDSP m) s r <-> obsRel m s r.
Proof. intros s r. exact (dsp_recov S (obsRel m) s r). Qed.

Theorem obsDSP_ret {S A} (a : A) :
  eq1 (obsDSP (ret a : prog S A)) (ret a).
Proof.
  unfold eq1, Eq1__ProgDSP. intros pre r.
  apply (dsp_cong S
           (fun s r0 => unOptionT (unOptionT (runStateT (ret a : prog S A) s))
                          (Some r0))
           (fun s r0 => r0 = Some (a, s))).
  intros s r0. destruct r0 as [[b s']|]; cbn; split; intro H; congruence.
Qed.

Theorem obsDSP_bind {S A B} (x : prog S A) (f : A -> prog S B) :
  eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
Proof.
  unfold eq1, Eq1__ProgDSP. intros pre r.
  assert (Hx : forall s y,
             (getProgDSP (obsDSP x) (fun _ => True) y
              /\ ~ getProgDSP (obsDSP x) (fun t => t <> s) y)
             <-> unOptionT (unOptionT (runStateT x s)) (Some y)).
  { intros s y.
    exact (dsp_recov S
             (fun s1 r1 => unOptionT (unOptionT (runStateT x s1)) (Some r1)) s y). }
  assert (Hf : forall a s y,
             (getProgDSP (obsDSP (f a)) (fun _ => True) y
              /\ ~ getProgDSP (obsDSP (f a)) (fun t => t <> s) y)
             <-> unOptionT (unOptionT (runStateT (f a) s)) (Some y)).
  { intros a s y.
    exact (dsp_recov S
             (fun s1 r1 => unOptionT (unOptionT (runStateT (f a) s1)) (Some r1)) s y). }
  refine (iff_trans
            (dsp_cong S
               (fun s r0 => unOptionT (unOptionT (runStateT (x >>= f) s)) (Some r0))
               (fun s r0 =>
                  exists o, (getProgDSP (obsDSP x) (fun _ => True) o
                             /\ ~ getProgDSP (obsDSP x) (fun t => t <> s) o)
                            /\ match o with
                               | Some (a, smid) =>
                                   getProgDSP (obsDSP (f a)) (fun _ => True) r0
                                   /\ ~ getProgDSP (obsDSP (f a)) (fun t => t <> smid) r0
                               | None => r0 = None
                               end)
               _ pre r)
            (iff_sym (bindDSPProg_dsp S (obsDSP x) (fun a => obsDSP (f a)) pre r))).
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

#[global] Instance dspMorphism (S : Type) :
  @MonadMorphism (prog S) (DSPProgSP S)
    (Monad__nditprog S) (Monad__DSPProgSP S) (Eq1__ProgDSP S) (@obsDSP S).
Proof.
  constructor.
  - intros A a. apply obsDSP_ret.
  - intros A B m k. apply obsDSP_bind.
Qed.

Definition dspRecipe (S : Type) : LogicRecipe (prog S) (DSPProgSP S) :=
  makeDSPRecipe S (@obsDSP S) (dspMorphism S).

(* ==================================================================== *)
(** * The logic                                                          *)
(* ==================================================================== *)

Definition dspPPApproxOps (S : Type) `{DS : DefaultState S}
  (direction : Direction) :
  @ApproxOps (prog S) (DSPProgSP S) direction
    (dspRecipe S) (PP S) :=
  spPPApproxOps direction (dspRecipe S) (fun A => @getProgDSP S A).

#[global] Existing Instance dspPPApproxOps.

Definition DSPTriple {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  Approx direction (dspRecipe S) m (unaryPP pre post).

Theorem dsp_over_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DSPTriple Over m pre post <->
  forall r,
    ((exists s, pre s /\ obsRel m s r) /\ (forall s, obsRel m s r -> pre s)) ->
    post r.
Proof. reflexivity. Qed.

Theorem dsp_under_spec {S A} `{DS : DefaultState S} (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DSPTriple Under m pre post <->
  forall r,
    post r ->
    (exists s, pre s /\ obsRel m s r) /\ (forall s, obsRel m s r -> pre s).
Proof. reflexivity. Qed.

Theorem dsp_triple_raw {S A} `{DS : DefaultState S}
  (direction : Direction) (m : prog S A)
  (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DSPTriple direction m pre post <->
  match direction with
  | Over => ordProgSP (getProgDSP (obsDSP m)) (pp2_over pre post)
  | Under => ordProgSP (pp2_under pre post) (getProgDSP (obsDSP m))
  end.
Proof.
  destruct direction.
  - exact (sp_over_raw (getProgDSP (obsDSP m)) (dspMonoSP (obsDSP m)) pre post).
  - exact (sp_under_raw (getProgDSP (obsDSP m)) (dspMonoSP (obsDSP m)) pre post).
Qed.

(** The DSP triple is the conjunction of the ASP and DSLP triples of the
    same pre/post pair, in the same direction. *)
Theorem dsp_split_triple {S A} `{DS : DefaultState S}
  (m : prog S A) (pre : S -> Prop) (post : option (A * S) -> Prop) :
  DSPTriple Under m pre post <->
  (forall r, post r -> exists s, pre s /\ obsRel m s r) /\
  (forall r, post r -> forall s, obsRel m s r -> pre s).
Proof.
  split.
  - intro H. split; intros r Hpost; apply (H r Hpost).
  - intros [H1 H2] r Hpost. split; [exact (H1 r Hpost) | exact (H2 r Hpost)].
Qed.

(* ==================================================================== *)
(** * Examples                                                           *)
(* ==================================================================== *)

Definition dspOnly {A} (wanted : A) : A -> Prop :=
  fun actual => actual = wanted.

Theorem progRet_dsp_inc :
  DSPTriple Under progRet preEq0 postEq0.
Proof.
  apply dsp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 0)) in Hpost. subst r.
  split.
  - exists 0. split; reflexivity.
  - intros s Hrel. unfold obsRel in Hrel. cbn in Hrel.
    inversion Hrel. reflexivity.
Qed.

(** [Some (tt, 1)] is reachable from [P0] and from nowhere else. *)
Theorem progEx_dsp_1 :
  DSPTriple Under progEx P0 (dspOnly (Some (tt, 1))).
Proof.
  apply dsp_under_spec.
  intros r Hpost.
  change (r = Some (tt, 1)) in Hpost. subst r.
  split.
  - exists 0. split; [reflexivity|].
    unfold obsRel, progEx, orP. cbn. sauto limit: 200.
  - intros s Hrel.
    unfold obsRel, progEx, orP in Hrel. cbn in Hrel.
    change (s = 0).
    destruct Hrel as [a [Ha Hrel]]. subst a. cbn in Hrel.
    destruct Hrel as [Hrel | Hrel]; inversion Hrel; lia.
Qed.

(** [Some (tt, 42)] is reachable from outside [P0], so the demonic
    conjunct fails. *)
Theorem progEx_dsp_not_42 :
  ~ DSPTriple Under progEx P0 (dspOnly (Some (tt, 42))).
Proof.
  intro H. apply dsp_under_spec in H.
  assert (Hpost : dspOnly (Some (tt, 42)) (Some (tt, 42))).
  { reflexivity. }
  destruct (H (Some (tt, 42)) Hpost) as [_ Hall].
  specialize (Hall 1).
  assert (Hreach : obsRel progEx 1 (Some (tt, 42))).
  { unfold obsRel, progEx, orP. cbn. sauto limit: 200. }
  specialize (Hall Hreach). discriminate.
Qed.

(** [None] is unreachable, so the angelic conjunct fails. *)
Theorem progEx_dsp_not_None :
  ~ DSPTriple Under progEx P0
      (dspOnly (None : option (unit * nat))).
Proof.
  intro H. apply dsp_under_spec in H.
  assert (Hpost : dspOnly (None : option (unit * nat)) None).
  { reflexivity. }
  destruct (H None Hpost) as [[s [_ Hreach]] _].
  unfold obsRel, progEx, orP in Hreach. cbn in Hreach.
  sauto limit: 200.
Qed.

Theorem progEx_dsp_not_99 :
  ~ DSPTriple Under progEx P0 (dspOnly (Some (tt, 99))).
Proof.
  intro H. apply dsp_under_spec in H.
  assert (Hpost : dspOnly (Some (tt, 99)) (Some (tt, 99))).
  { reflexivity. }
  destruct (H (Some (tt, 99)) Hpost) as [[s [Hs Hreach]] _].
  change (s = 0) in Hs. subst s.
  unfold obsRel, progEx, orP in Hreach. cbn in Hreach.
  sauto lq: on limit: 200.
Qed.
