(** * Counterexamples to the arrow laws without disjunctivity or
      conjunctivity (paper, Appendix D.3)

    [AngArr.SPArrAng] and [DemArr.SPArrDem] are monotone binary transformers
    with the angelic, respectively demonic, codomain condition, which under
    monotonicity is strictness ([AngArr.codomain_iff_strict]), respectively
    termination ([DemArr.codomain_iff_terminating]).  With the operations of
    [ASPArr], respectively [DSLPArr], the law
    [first g >>> arr fst == arr fst >>> g] fails ([AngArr.first_fst_fails],
    [DemArr.first_fst_fails]), so neither satisfies [ArrowLaws]
    ([AngArr.not_ArrowLaws], [DemArr.not_ArrowLaws]).  The monad
    counterexample of Appendix D.2 is [StatefulSPostCounterexample.Dem]. *)

From Coq Require Import RelationClasses Classical_Prop.
From Incorrectness.Lib.Arrow Require Import Arrow.
From Incorrectness.SP Require Import SPostArr.

(* ================================================================= *)
(** ** [SPArrAng]: the arrow law [first_fst] without disjunctivity *)
(* ================================================================= *)

Module AngArr.

  (** An admitted result needs a satisfiable precondition. *)
  Definition sp_codomain {B A} (f : SPArrT B A) : Prop :=
    forall P a, f P a -> exists b, P b.

  Lemma codomain_iff_strict {B A} (f : SPArrT B A) :
    sp_monotone f -> (sp_codomain f <-> sp_strict f).
  Proof.
    intro Hm. split.
    - intros Hc a Hf. destruct (Hc _ a Hf) as [b []].
    - intros Hs P a Hf. apply NNPP. intro Hn.
      apply (Hs a). apply (Hm P); [| exact Hf].
      intros b Hb. exact (Hn (ex_intro _ b Hb)).
  Qed.

  Definition SPArrAng (B A : Type) : Type :=
    { f : SPArrT B A | sp_monotone f /\ sp_codomain f }.

  Definition getAng {B A} (f : SPArrAng B A) : (B -> Prop) -> A -> Prop := proj1_sig f.

  Coercion getAng : SPArrAng >-> Funclass.

  #[program] Definition ofASPArr {B A} (f : ASPArr B A) : SPArrAng B A := getASPArr f.
  Next Obligation.
  Proof.
    split; [exact (proj1 (proj2_sig f)) |].
    apply codomain_iff_strict; [exact (proj1 (proj2_sig f)) | exact (proj1 (proj2 (proj2_sig f)))].
  Qed.

  (** The operations of [ASPArr], on the larger carrier. *)
  #[program] Definition pureAng {A B} (h : A -> B) : SPArrAng A B :=
    getASPArr (pureASP h).
  Next Obligation.
  Proof.
    split; [exact (proj1 (proj2_sig (pureASP h))) |].
    intros P b [a [Ha _]]. exists a. exact Ha.
  Qed.

  #[program] Definition compAng {A B C} (f : SPArrAng A B) (g : SPArrAng B C) :
    SPArrAng A C :=
    fun P c => g (f P) c.
  Next Obligation.
  Proof.
    split.
    - intros P Q HPQ c H.
      apply (proj1 (proj2_sig g) (proj1_sig f P) (proj1_sig f Q)); [| exact H].
      intro b. exact (proj1 (proj2_sig f) P Q HPQ b).
    - intros P c H.
      destruct (proj2 (proj2_sig g) _ c H) as [b Hb].
      exact (proj2 (proj2_sig f) P b Hb).
  Qed.

  #[program] Definition firstAng {A B C} (f : SPArrAng A B) : SPArrAng (A * C) (B * C) :=
    fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Next Obligation.
  Proof.
    split.
    - intros P Q HPQ [b c] H.
      exact (proj1 (proj2_sig f) (fun a => P (a, c)) (fun a => Q (a, c))
               (fun a => HPQ (a, c)) b H).
    - intros P [b c] H.
      destruct (proj2 (proj2_sig f) _ b H) as [a Ha]. exists (a, c). exact Ha.
  Qed.

  Lemma compAng_ASP {A B C} (f : ASPArr A B) (g : ASPArr B C) P c :
    compAng (ofASPArr f) (ofASPArr g) P c <-> compASP f g P c.
  Proof. reflexivity. Qed.

  Definition Ang_eq {A B} (f g : SPArrAng A B) : Prop := forall P b, f P b <-> g P b.

  #[global] Instance Ang_eq_Equivalence {A B} : Equivalence (@Ang_eq A B).
  Proof.
    constructor.
    - intros f P b. reflexivity.
    - intros f g H P b. symmetry. apply H.
    - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
  Qed.

  Definition arrow : Arrow SPArrAng :=
    {| arr_pure := @pureAng; arr_comp := @compAng; arr_first := @firstAng |}.

  Definition equality : ArrowEq SPArrAng :=
    {| arrow_eq := @Ang_eq; arrow_eq_equiv := fun A B => @Ang_eq_Equivalence A B |}.

  (** [g] needs both Booleans in its precondition; [pre] pairs each Boolean
      only with itself. *)
  #[program] Definition g : SPArrAng bool unit :=
    fun pre _ => pre true /\ pre false.
  Next Obligation.
  Proof.
    split.
    - intros P Q HPQ a [Ht Hf]. exact (conj (HPQ _ Ht) (HPQ _ Hf)).
    - intros P a [Ht _]. exists true. exact Ht.
  Qed.

  Definition pre : bool * bool -> Prop :=
    fun bc => (fst bc = true /\ snd bc = true) \/ (fst bc = false /\ snd bc = false).

  (** [first g >>> arr fst] rejects: it hands [g] a single slice
      [fun b => pre (b, c)], none of which contains both Booleans.
      [arr fst >>> g] accepts: it hands [g] the union of the slices. *)
  Theorem first_fst_fails :
    exists (g : SPArrAng bool unit) (pre : bool * bool -> Prop) (a : unit),
      ~ (compAng (@firstAng _ _ bool g) (pureAng fst) pre a <->
           compAng (pureAng fst) g pre a).
  Proof.
    exists g, pre, tt. intros [_ H].
    assert (Hr : compAng (pureAng fst) g pre tt)
      by (split; [ exists (true, true) | exists (false, false) ]; unfold pre; cbn; auto).
    destruct (H Hr) as [[u c] [[Ht Hf] _]]. cbn in Ht, Hf.
    destruct c;
      [ destruct Hf as [[E _] | [_ E]] | destruct Ht as [[_ E] | [E _]] ];
      discriminate E.
  Qed.

  Theorem not_ArrowLaws : ~ @ArrowLaws SPArrAng arrow equality.
  Proof.
    intro HL. destruct first_fst_fails as [g' [pre' [a H]]].
    exact (H (@first_fst SPArrAng arrow equality HL _ _ _ g' pre' a)).
  Qed.

End AngArr.

(* ================================================================= *)
(** ** [SPArrDem]: the arrow law [first_fst] without conjunctivity *)
(* ================================================================= *)

Module DemArr.

  (** A total precondition admits every result. *)
  Definition sp_codomain {B A} (f : SPArrT B A) : Prop :=
    forall P a, (forall b, P b) -> f P a.

  Lemma codomain_iff_terminating {B A} (f : SPArrT B A) :
    sp_monotone f -> (sp_codomain f <-> sp_terminating f).
  Proof.
    intro Hm. split.
    - intros Hc a. apply Hc. intros _. exact I.
    - intros Ht P a HP. apply (Hm (fun _ => True)); [intros b _; exact (HP b) | exact (Ht a)].
  Qed.

  Definition SPArrDem (B A : Type) : Type :=
    { f : SPArrT B A | sp_monotone f /\ sp_codomain f }.

  Definition getDem {B A} (f : SPArrDem B A) : (B -> Prop) -> A -> Prop := proj1_sig f.

  Coercion getDem : SPArrDem >-> Funclass.

  #[program] Definition ofDSLPArr {B A} (f : DSLPArr B A) : SPArrDem B A := getDSLPArr f.
  Next Obligation.
  Proof.
    split; [exact (proj1 (proj2_sig f)) |].
    apply codomain_iff_terminating;
      [exact (proj1 (proj2_sig f)) | exact (proj1 (proj2 (proj2_sig f)))].
  Qed.

  (** The operations of [DSLPArr], on the larger carrier. *)
  #[program] Definition pureDem {A B} (h : A -> B) : SPArrDem A B :=
    getDSLPArr (pureDSLP h).
  Next Obligation.
  Proof.
    split; [exact (proj1 (proj2_sig (pureDSLP h))) |].
    intros P b HP a _. exact (HP a).
  Qed.

  #[program] Definition compDem {A B C} (f : SPArrDem A B) (g : SPArrDem B C) :
    SPArrDem A C :=
    fun P c => g (f P) c.
  Next Obligation.
  Proof.
    split.
    - intros P Q HPQ c H.
      apply (proj1 (proj2_sig g) (proj1_sig f P) (proj1_sig f Q)); [| exact H].
      intro b. exact (proj1 (proj2_sig f) P Q HPQ b).
    - intros P c HP.
      apply (proj2 (proj2_sig g)). intro b.
      exact (proj2 (proj2_sig f) P b HP).
  Qed.

  #[program] Definition firstDem {A B C} (f : SPArrDem A B) : SPArrDem (A * C) (B * C) :=
    fun P bc => f (fun a => P (a, snd bc)) (fst bc).
  Next Obligation.
  Proof.
    split.
    - intros P Q HPQ [b c] H.
      exact (proj1 (proj2_sig f) (fun a => P (a, c)) (fun a => Q (a, c))
               (fun a => HPQ (a, c)) b H).
    - intros P [b c] HP.
      exact (proj2 (proj2_sig f) (fun a => P (a, c)) b (fun a => HP (a, c))).
  Qed.

  Lemma compDem_DSLP {A B C} (f : DSLPArr A B) (g : DSLPArr B C) P c :
    compDem (ofDSLPArr f) (ofDSLPArr g) P c <-> compDSLP f g P c.
  Proof. reflexivity. Qed.

  Definition Dem_eq {A B} (f g : SPArrDem A B) : Prop := forall P b, f P b <-> g P b.

  #[global] Instance Dem_eq_Equivalence {A B} : Equivalence (@Dem_eq A B).
  Proof.
    constructor.
    - intros f P b. reflexivity.
    - intros f g H P b. symmetry. apply H.
    - intros f g h H1 H2 P b. etransitivity; [apply H1 | apply H2].
  Qed.

  Definition arrow : Arrow SPArrDem :=
    {| arr_pure := @pureDem; arr_comp := @compDem; arr_first := @firstDem |}.

  Definition equality : ArrowEq SPArrDem :=
    {| arrow_eq := @Dem_eq; arrow_eq_equiv := fun A B => @Dem_eq_Equivalence A B |}.

  (** Dually, [g] needs one of the Booleans in its precondition, and [pre]
      is the complement of [AngArr.pre]. *)
  #[program] Definition g : SPArrDem bool unit :=
    fun pre _ => pre true \/ pre false.
  Next Obligation.
  Proof.
    split.
    - intros P Q HPQ a [Ht | Hf]; [left; exact (HPQ _ Ht) | right; exact (HPQ _ Hf)].
    - intros P a HP. left. exact (HP true).
  Qed.

  Definition pre : bool * bool -> Prop := fun bc => ~ AngArr.pre bc.

  (** [first g >>> arr fst] accepts: each slice misses only one Boolean.
      [arr fst >>> g] rejects: the intersection of the slices is empty. *)
  Theorem first_fst_fails :
    exists (g : SPArrDem bool unit) (pre : bool * bool -> Prop) (a : unit),
      ~ (compDem (@firstDem _ _ bool g) (pureDem fst) pre a <->
           compDem (pureDem fst) g pre a).
  Proof.
    exists g, pre, tt. intros [H _].
    assert (Hl : compDem (@firstDem _ _ bool g) (pureDem fst) pre tt)
      by (intros [u [|]] _; cbn; [right | left]; intros [[? ?] | [? ?]]; discriminate).
    destruct (H Hl) as [Ht | Hf].
    - exact (Ht (true, true) eq_refl (or_introl (conj eq_refl eq_refl))).
    - exact (Hf (false, false) eq_refl (or_intror (conj eq_refl eq_refl))).
  Qed.

  Theorem not_ArrowLaws : ~ @ArrowLaws SPArrDem arrow equality.
  Proof.
    intro HL. destruct first_fst_fails as [g' [pre' [a H]]].
    exact (H (@first_fst SPArrDem arrow equality HL _ _ _ g' pre' a)).
  Qed.

End DemArr.
