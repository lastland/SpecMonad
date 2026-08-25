From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy Require Import NonDetProg NonDetItProg ProgFacts WP Pred PredFacts SPost WPred NonDetItObservation.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Setoids.Setoid.

Import MonadNotation.
Open Scope monad_scope.

From Incorrectness.Taxonomy Require Import SPSpecMonads.

Section ObsASP.
  Variable S : Type.
  
  #[program] Definition obsASP {A} (m : nditprog S A) : ASPProgSP S A :=
    fun pre r => exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
  Next Obligation.
    unfold SingletonProg. intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
      exists s. split; [reflexivity | exact Hr].
    - intros [s0 [Hp [s [Heq Hr]]]]. subst s.
      exists s0. split; [exact Hp | exact Hr].
  Qed.

  Lemma getProg_obsASP {A} (m : nditprog S A) pre r :
    getProgASP (obsASP m) pre r
    <-> exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
  Proof. split; intro H; exact H. Qed.

  (* ---------------- [obsASP] is a monad morphism ---------------- *)

  Lemma outcomes_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) s ob :
    unOptionT (unOptionT (runStateT (x >>= f) s)) ob <->
    (exists oy, unOptionT (unOptionT (runStateT x s)) oy /\
       match oy with
       | Some (Some (a, s')) => unOptionT (unOptionT (runStateT (f a) s')) ob
       | Some None => ob = Some None
       | None => ob = None
       end).
  Proof.
    cbn. split; intros [oy [H1 H2]]; exists oy; split; [exact H1 | | exact H1 |];
      destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  Qed.

  Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : nditprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgASP. intros pre r. split.
    - intros [s [Hp Hr]]. exists s. split; [exact Hp |].
      destruct r as [[b s']|]; cbn in Hr; congruence.
    - intros [s [Hp Heq]]. exists s. split; [exact Hp |].
      destruct r as [[b s']|]; cbn; congruence.
  Qed.

  Theorem obsASP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
  Proof.
    unfold eq1, Eq1__ProgASP. intros pre r. split.
    - intros [s [Hp Hrel]]. apply outcomes_bind in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[[a s']|]|].
      + left. exists a, s'. split; [| exact Hk].
        exists s. split; [exact Hp | exact Hx].
      + right. split; [congruence |]. exists s. split; [exact Hp | exact Hx].
      + discriminate Hk.
    - intros [[a [s' [[s [Hp Hx]] Hf]]] | [Hr [s [Hp Hx]]]].
      + exists s. split; [exact Hp |]. apply outcomes_bind.
        exists (Some (Some (a, s'))). split; [exact Hx | exact Hf].
      + exists s. split; [exact Hp |]. apply outcomes_bind.
        exists (Some None). split; [exact Hx | congruence].
  Qed.

End ObsASP.

Arguments obsASP {_} {_}.

Section ASPTriple.
  Definition tripleASP {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
      match kind with
      | Over => forall r, getProgASP (obsASP prog) pre r -> post r
      | Under => forall r, post r -> getProgASP (obsASP prog) pre r
      end.

  (** Neither of these is [SingletonProg], so they are plain [ProgSP]: at the
      empty precondition [pp2_over] still yields [post r], and at the full
      one [pp2_under] holds even when no single state carries [pre]. *)
  Definition tripleASPspec {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match kind with
    | Over => ordProgSP (getProgASP (obsASP prog)) (pp2_over pre post)
    | Under => ordProgSP (pp2_under pre post) (getProgASP (obsASP prog))
    end.

  Theorem tripleASPDefEq {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleASP prog kind pre post <-> tripleASPspec prog kind pre post.
  Proof.
    unfold tripleASP, tripleASPspec, ordProgSP, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: instantiate the quantified precondition at [pre] itself *)
      intros H p r [Hsub Hpost]. destruct (H r Hpost) as [s [Hpre Hreach]].
      exists s. split; [ exact (Hsub s Hpre) | exact Hreach ].
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - intros H p r [s [Hp Hreach]] Hsub.
      exact (H r (ex_intro _ s (conj (Hsub s Hp) Hreach))).
    - intros H r Hobs. exact (H pre r Hobs (fun s Hs => Hs)).
  Qed.


  (** For this ONE direction the comparison target can itself be an ASP:
      [tripleASP _ Over pre post] unfolds to the relation inclusion
      [Out <= {(s,r) | pre s -> post r}], and that relation read as an ASP is
      the target.  (The [Under] direction has no such form — it asserts that
      SOME [pre]-state reaches [r], a disjunction over states, and the ASP
      order only ever expresses containment of one fixed relation.) *)
  #[program] Definition pp2asp_over' {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : ASPProgSP S A :=
    fun p r => exists s, p s /\ (pre s -> post r).
  Next Obligation.
    intros p r. split.
    - intros [s [Hp Hm]]. exists s. split; [ exact Hp |].
      exists s. split; [ reflexivity | exact Hm ].
    - intros [s0 [Hp [s [Heq Hm]]]]. subst s.
      exists s0. split; [ exact Hp | exact Hm ].
  Qed.

  Theorem tripleASP_over_inmonad {S A}
    (prog : nditprog S A)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleASP prog Over pre post
    <-> ordProgASP (obsASP prog) (pp2asp_over' pre post).
  Proof.
    split.
    - intros H p r [s [Hp Hout]]. exists s. split; [ exact Hp |].
      intro Hpre. exact (H r (ex_intro _ s (conj Hpre Hout))).
    - intros H r [s [Hpre Hout]].
      destruct (H pre r (ex_intro _ s (conj Hpre Hout))) as [s1 [Hp1 Himp]].
      exact (Himp Hp1).
  Qed.
End ASPTriple.

Arguments tripleASP {_} {_}.

Section ASPExamples.
  Example progA : nditprog nat unit :=
  put 42 ;;
  s <- get ;;
  orP _ (put s) (put (s + 1)).

  Theorem progA_all :
    tripleASP progA Over
      (fun _ => True)
      (fun r =>
         match r with
         | Some (_, s') => s' >= 42
         | None => False
         end).
  Proof.
    unfold tripleASP. intros r [sigma [_ Hrel]].
    destruct r as [[[] s'] |]; cbn in Hrel; sauto.
  Qed.

  Theorem progA_42 :
    tripleASP progA Under
      (fun _ => True)
      (fun r => r = Some (tt, 42)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split.
    - exact I.
    - cbn. sauto.
  Qed.

  Theorem progA_43 :
    tripleASP progA Under
      (fun _ => True)
      (fun r => r = Some (tt, 43)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split.
    - exact I.
    - cbn. sauto.
  Qed.

  (* ================================================================= *)
  (** ** Examples: nondeterminism + divergence                          *)
  (* ================================================================= *)

  Example progB : nditprog nat unit :=
    put 42 ;;
    s <- get ;;
    orP _ (put s) (spinP _).

  Theorem progB_42 :
    tripleASP progB Under
      (fun _ => True)
      (fun r => r = Some (tt, 42)).
  Proof.
    unfold tripleASP. intros r ->. exists 0. split; [exact I | sauto].
  Qed.

  Theorem progB_not_None :
    tripleASP progB Over
      (fun _ => True)
      (fun r => r <> None).
  Proof.
    unfold tripleASP. intros r [sigma [_ Hrel]] ->. cbn in Hrel. sauto.
  Qed.
    
  (** [progEx] reaches [Some (tt, 1)] only from state [0] — enough for the
      [Under] triple, which asks for *some* [pre] state to reach each [post]
      outcome. *)
  Example progEx : nditprog nat unit :=
    s <- get ;;
    orP _ (put (s + 1)) (put 42).

  Theorem progEx_under :
    tripleASP progEx Under
      (fun _ => True)
      (fun r => r = Some (tt, 1)).
  Proof.
    intros r ->. exists 0. split; [exact I | cbn; sauto].
  Qed.

End ASPExamples.
Section ObsDSLP.
  Variable S : Type.

  (** The demonic-liberal observation: [r] forces [pre] at every state that can
      reach it.  Dually to [obsASP], which is the ASP of the same terminating
      slice [unOptionT (unOptionT (runStateT m s)) (Some r)], this is its DSLP —
      so [MSingletonProg] is immediate from [dslp_msingleton]. *)
  #[program] Definition obsDSLP {A} (m : nditprog S A) : DSLPProgSP S A :=
    fun pre r => forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
  Next Obligation.
    exact (dslp_msingleton S (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
  Qed.

  Lemma getProgMSP_obsDSLP {A} (m : nditprog S A) pre r :
    getProgDSLP (obsDSLP m) pre r
    <-> forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
  Proof. split; intro H; exact H. Qed.

  (* --------------- [obsDSLP] is a monad morphism --------------- *)

  Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : nditprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgDSLP. intros pre r. split.
    - intros H s0 Heq. apply H. subst r. cbn. reflexivity.
    - intros H s Hr. apply H. cbn in Hr. congruence.
  Qed.

  Theorem obsDSLP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
  Proof.
    unfold eq1, Eq1__ProgDSLP. intros pre r. split.
    - intro H. split.
      + (* normal return: [x] reaches [Some (a, s')], then [f a] reaches [r] *)
        intros a s' Hf s Hx. apply H. apply outcomes_bind.
        exists (Some (Some (a, s'))). split; [exact Hx | exact Hf].
      + (* exception: [x] raises, and [r] must be [None] *)
        intros Hr s Hx. apply H. apply outcomes_bind.
        exists (Some None). split; [exact Hx | congruence].
    - intros [H1 H2] s Hrel. apply outcomes_bind in Hrel.
      destruct Hrel as [oy [Hx Hk]]. destruct oy as [[[a s']|]|].
      + exact (H1 a s' Hk s Hx).
      + assert (Hr : r = None) by congruence. exact (H2 Hr s Hx).
      + discriminate Hk.
  Qed.
End ObsDSLP.

Arguments obsDSLP {_} {_}.

Section DSLPTriple.
  Definition tripleDSLP {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getProgDSLP (obsDSLP prog) pre r -> post r
    | Under => forall r, post r -> getProgDSLP (obsDSLP prog) pre r
    end.


  (** As on the ASP side, neither of these is [MSingletonProg], so both are
      plain [ProgSP].  They are in fact the same two transformers used for
      ASP: the [Over] / [Under] readings turn only on the observation being
      monotone in its precondition, which all four observations are. *)
  Definition tripleDSLPspec {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => ordProgSP (getProgDSLP (obsDSLP prog)) (pp2_over pre post)
    | Under => ordProgSP (pp2_under pre post) (getProgDSLP (obsDSLP prog))
    end.

  Theorem tripleDSLPDefEq {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleDSLP prog kind pre post <-> tripleDSLPspec prog kind pre post.
  Proof.
    unfold tripleDSLP, tripleDSLPspec, ordProgSP, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: push the quantified precondition through [pre <= p] *)
      intros H p r [Hsub Hpost] s Hout. exact (Hsub s (H r Hpost s Hout)).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* Over: pull it back through [p <= pre] *)
      intros H p r Hdslp Hsub. apply (H r).
      intros s Hout. exact (Hsub s (Hdslp s Hout)).
    - intros H r Hdslp. exact (H pre r Hdslp (fun s Hs => Hs)).
  Qed.

  (** Dually, [tripleDSLP _ Under pre post] is the relation inclusion
      [Out <= {(s,r) | post r -> pre s}].  Note the comparison REVERSES —
      [pp2 <= obs] rather than [obs <= pp2] — because reading a relation as a
      DSLP is antitone in the relation. *)
  #[program] Definition pp2dslp_under' {S A} (pre : S -> Prop) (post : option (A * S) -> Prop)
    : DSLPProgSP S A :=
    fun p r => forall s, (post r -> pre s) -> p s.
  Next Obligation. exact (dslp_msingleton S (fun s r => post r -> pre s)). Qed.

  Theorem tripleDSLP_under_inmonad {S A}
    (prog : nditprog S A)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleDSLP prog Under pre post
    <-> ordProgDSLP (pp2dslp_under' pre post) (obsDSLP prog).
  Proof.
    split.
    - intros H p r Hd s Hout. apply Hd. intro Hpost. exact (H r Hpost s Hout).
    - intros H r Hpost s Hout.
      exact (H (fun t => post r -> pre t) r (fun t Ht => Ht) s Hout Hpost).
  Qed.
End DSLPTriple.

Arguments tripleDSLP {_} {_}.

Section OHearnExample.
  Definition example_state : nditprog (nat * nat * nat) unit :=
    s <- get ;;
    let '(x, y, _) := s in
    if Nat.even x then
      if negb (Nat.even y) then put (x, y, 42) else ret tt
    else ret tt.

  Theorem example_incorrect_1 :
    tripleASP example_state Under
      (fun '(x, _, z) => z = 11)
      (fun r =>
         match r with
         | Some (tt, (x, y, z)) =>
             z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
         | _ => False
         end).
  Proof.
    unfold tripleASP.
    intros [[[] [[x y] z]]|] H; [| contradiction].
    destruct H as [-> [Hx Hy]].
    exists (x, y, 11). split; [reflexivity |].
    cbn. eexists. split; [reflexivity |].
    cbn. rewrite Hx, Hy. reflexivity.
  Qed.
  
  Theorem example_incorrect_2 :
    tripleASP example_state Under
      (fun _ => True)
      (fun r =>
         match r with
         | Some (tt, (_, _, z)) => z = 42
         | _ => False
         end).
  Proof.
    unfold tripleASP.
    intros [[[] [[x y] z]]|] H; [| contradiction].
    cbn in H. subst z.
    (* the final state itself is a witness: both branches preserve [x], [y]
       and either set [z := 42] or leave it at [42] *)
    exists (x, y, 42). split; [exact I |].
    cbn. eexists. split; [reflexivity |].
    cbn. destruct (Nat.even x); destruct (negb (Nat.even y)); reflexivity.
  Qed.

  Theorem example_incorrect_unprovable :
    ~ tripleASP example_state Under
        (fun '(_, _, z) => z = 11)
        (fun r =>
           match r with
           | Some (tt, (_, _, z)) => z = 42
           | _ => False
           end).
  Proof.
    (* [Some (tt, (1, 0, 42))] satisfies the postcondition but is reachable
       only from itself — and its [z] is [42], not [11] *)
    intro H.
    specialize (H (Some (tt, (1, 0, 42))) eq_refl).
    destruct H as [[[x y] z] [Hpre Hrel]].
    cbn in Hpre. subst z.
    cbn in Hrel. destruct Hrel as [a [Ha Hrel]]. subst a. cbn in Hrel.
    destruct (Nat.even x) eqn:Hx; destruct (negb (Nat.even y)) eqn:Hy;
      cbn in Hrel; inversion Hrel; subst; try discriminate Hx.
  Qed.
End OHearnExample.

Section OHearnRewritingRules.
  Variable S : Type.

  Theorem first_symmetry_rule_1_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleASP m Under pre post1 /\
       tripleASP m Under pre post2) ->
        tripleASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] r [Hr1 | Hr2].
    - exact (H1 r Hr1).
    - exact (H2 r Hr2).
  Qed.

  Theorem first_symmetry_rule_2_asp :
    forall A (m : nditprog S A) pre post1 post2,
      tripleASP m Under pre (fun r => post1 r \/ post2 r) ->
      (tripleASP m Under pre post1 /\
       tripleASP m Under pre post2).
  Proof.
    intros A m pre post1 post2 H. split.
    - intros r Hr. exact (H r (or_introl Hr)).
    - intros r Hr. exact (H r (or_intror Hr)).
  Qed.

  Theorem first_symmetry_rule_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleASP m Under pre post1 /\
       tripleASP m Under pre post2) <->
        tripleASP m Under pre (fun r => post1 r \/ post2 r).
  Proof.
    intros A m pre post1 post2. split.
    - apply first_symmetry_rule_1_asp.
    - apply first_symmetry_rule_2_asp.
  Qed.

  Theorem second_symmetry_rule_asp_1 :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleASP m Over pre post1 /\
         tripleASP m Over pre post2) ->
      tripleASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2 [H1 H2] r Hasp.
    split; [exact (H1 r Hasp) | exact (H2 r Hasp)].
  Qed.

  Theorem second_symmetry_rule_asp_2 :
    forall A (m : nditprog S A) pre post1 post2,
      tripleASP m Over pre (fun r => post1 r /\ post2 r) ->
      (tripleASP m Over pre post1 /\
         tripleASP m Over pre post2).
  Proof.
    intros A m pre post1 post2 H. split; intros r Hasp;
      [exact (proj1 (H r Hasp)) | exact (proj2 (H r Hasp))].
  Qed.

  Theorem second_symmetry_rule_asp :
    forall A (m : nditprog S A) pre post1 post2,
      (tripleASP m Over pre post1 /\
         tripleASP m Over pre post2) <->
        tripleASP m Over pre (fun r => post1 r /\ post2 r).
  Proof.
    intros A m pre post1 post2. split.
    - apply second_symmetry_rule_asp_1.
    - apply second_symmetry_rule_asp_2.
  Qed.

  (** Rule of consequence, [Under]: WEAKEN the precondition and SHRINK the
      postcondition — the opposite of the [Over] direction below, because
      [Under] has the observation in the conclusion. *)
  Theorem first_imp_symmetry_rule_asp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleASP m Under pre post /\
           (forall r, pre r -> pre' r) /\ (forall r, post' r -> post r)) -> tripleASP m Under pre' post'.
  Proof.
    intros A m pre pre' post post' [Htriple [Hpre Hpost]] r Hpost'.
    destruct (Htriple r (Hpost r Hpost')) as [s [Hp Hr]].
    exists s. split; [exact (Hpre s Hp) | exact Hr].
  Qed.

  Theorem second_imp_symmetry_rule_asp :
      forall A (m : nditprog S A) pre pre' post post',
        (tripleASP m Over pre post /\
           (forall r, pre' r -> pre r) /\ (forall r, post r -> post' r)) -> tripleASP m Over pre' post'.
  Proof.
    intros A m pre pre' post post' [Htriple [Hpre Hpost]] r [s [Hp' Hr]].
    apply Hpost. apply Htriple. exists s. split; [exact (Hpre s Hp') | exact Hr].
  Qed.

  (** A result witnessed by the under-approximation is reached from a [u]-state;
      if [u] entails [o], the over-approximation must accept it. *)
  Theorem principle_of_agreement_asp :
      forall A (m : nditprog S A) u u' o o',
        (tripleASP m Under u u' /\ tripleASP m Over o o' /\
           (forall r, u r -> o r)) -> (forall r, u' r -> o' r).
  Proof.
    intros A m u u' o o' [Hinc [Hcor Himp]] r Hu'.
    destruct (Hinc r Hu') as [s [Hu Hr]].
    apply Hcor. exists s. split; [exact (Himp s Hu) | exact Hr].
  Qed.

  Theorem principle_of_denial_asp :
      forall A (m : nditprog S A) u u' o o',
        (tripleASP m Under u u' /\ (forall r, u r -> o r) /\ ~(forall r, u' r -> o' r)) -> ~(tripleASP m Over o o').
  Proof.
    intros A m u u' o o' [Hinc [Himp Hnot]] Hcor.
    apply Hnot.
    apply (principle_of_agreement_asp A m u u' o o').
    exact (conj Hinc (conj Hcor Himp)).
  Qed.
End OHearnRewritingRules.
Section ObsDSP.
  Variable S : Type.

  #[program] Definition obsDSP {A} (m : nditprog S A) : DSPProgSP S A :=
    fun pre r => (obsASP m pre r) /\ (obsDSLP m pre r).
  Next Obligation.
    exact (dsp_shape_wf S (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
  Qed.

  Lemma getProgDSP_obsDSP {A} (m : nditprog S A) pre r :
    getProgDSP (obsDSP m) pre r
    <-> ((exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r))
         /\ (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s)).
  Proof. split; intro H; exact H. Qed.

  (* ---------------- [obsDSP] is a monad morphism ---------------- *)

  Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : nditprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgDSP. intros pre r.
    apply (dsp_cong S
             (fun s r0 => unOptionT (unOptionT (runStateT (ret a : nditprog S A) s))
                            (Some r0))
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. destruct r0 as [[b s']|]; cbn; split; intro H; congruence.
  Qed.

  Theorem obsDSP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
  Proof.
    unfold eq1, Eq1__ProgDSP. intros pre r.
    (* the two probes collapse back to the raw outcome relation *)
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
    - intro H. apply (outcomes_bind S) in H. destruct H as [oy [Hxx Hk]].
      destruct oy as [[[a s']|]|].
      + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
      + exists None. split; [ apply Hx; exact Hxx | congruence ].
      + discriminate Hk.
    - intros [[[a s']|] [Hm Hk]].
      + apply Hx in Hm. apply Hf in Hk. apply (outcomes_bind S).
        exists (Some (Some (a, s'))). split; [ exact Hm | exact Hk ].
      + apply Hx in Hm. apply (outcomes_bind S).
        exists (Some None). split; [ exact Hm | congruence ].
  Qed.
End ObsDSP.

Arguments obsDSP {_} {_}.

Section DSPTriple.
  Definition tripleDSP {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getProgDSP (obsDSP prog) pre r -> post r
    | Under => forall r, post r -> getProgDSP (obsDSP prog) pre r
    end.

  Definition tripleDSPspec {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => ordProgSP (getProgDSP (obsDSP prog)) (pp2_over pre post)
    | Under => ordProgSP (pp2_under pre post) (getProgDSP (obsDSP prog))
    end.

  Theorem tripleDSPDefEq {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleDSP prog kind pre post <-> tripleDSPspec prog kind pre post.
  Proof.
    unfold tripleDSP, tripleDSPspec, ordProgSP, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: both conjuncts of the DSP move along [pre <= p] *)
      intros H p r [Hsub Hpost].
      destruct (H r Hpost) as [[s [Hp Hout]] Hall]. split.
      + exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* Over: and along [p <= pre] in the other direction *)
      intros H p r [[s [Hp Hout]] Hall] Hsub. apply (H r). split.
      + exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hobs. exact (H pre r Hobs (fun s Hs => Hs)).
  Qed.
End DSPTriple.

Arguments tripleDSP {_} {_}.
Section ObsASLP.
  Variable S : Type.

  #[program] Definition obsASLP {A} (m : nditprog S A) : ASLPProgSP S A :=
    fun pre r => (obsASP m pre r) \/ (obsDSLP m pre r).
  Next Obligation.
    exact (aslp_shape_wf S (fun s r => unOptionT (unOptionT (runStateT m s)) (Some r))).
  Qed.

  Lemma getProgASLP_obsASLP {A} (m : nditprog S A) pre r :
    getProgASLP (obsASLP m) pre r
    <-> ((exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r))
         \/ (forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s)).
  Proof. split; intro H; exact H. Qed.

  (* ---------------- [obsASLP] is a monad morphism ---------------- *)

  Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : nditprog S A)) (ret a).
  Proof.
    unfold eq1, Eq1__ProgASLP. intros pre r.
    apply (aslp_cong S
             (fun s r0 => unOptionT (unOptionT (runStateT (ret a : nditprog S A) s))
                            (Some r0))
             (fun s r0 => r0 = Some (a, s))).
    intros s r0. destruct r0 as [[b s']|]; cbn; split; intro H; congruence.
  Qed.

  Theorem obsASLP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
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
    - intro H. apply (outcomes_bind S) in H. destruct H as [oy [Hxx Hk]].
      destruct oy as [[[a s']|]|].
      + exists (Some (a, s')). split; [ apply Hx; exact Hxx | apply Hf; exact Hk ].
      + exists None. split; [ apply Hx; exact Hxx | congruence ].
      + discriminate Hk.
    - intros [[[a s']|] [Hm Hk]].
      + apply Hx in Hm. apply Hf in Hk. apply (outcomes_bind S).
        exists (Some (Some (a, s'))). split; [ exact Hm | exact Hk ].
      + apply Hx in Hm. apply (outcomes_bind S).
        exists (Some None). split; [ exact Hm | congruence ].
  Qed.
End ObsASLP.

Arguments obsASLP {_} {_}.

Section ASLPTriple.
  Definition tripleASLP {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getProgASLP (obsASLP prog) pre r -> post r
    | Under => forall r, post r -> getProgASLP (obsASLP prog) pre r
    end.


  Definition tripleASLPspec {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => ordProgSP (getProgASLP (obsASLP prog)) (pp2_over pre post)
    | Under => ordProgSP (pp2_under pre post) (getProgASLP (obsASLP prog))
    end.

  Theorem tripleASLPDefEq {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop) :
    tripleASLP prog kind pre post <-> tripleASLPspec prog kind pre post.
  Proof.
    unfold tripleASLP, tripleASLPspec, ordProgSP, pp2_over, pp2_under.
    destruct kind; split.
    - (* Under: whichever disjunct held still holds after weakening *)
      intros H p r [Hsub Hpost].
      destruct (H r Hpost) as [[s [Hp Hout]] | Hall].
      + left. exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + right. intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hpost. exact (H pre r (conj (fun s Hs => Hs) Hpost)).
    - (* Over *)
      intros H p r Hobs Hsub. apply (H r).
      destruct Hobs as [[s [Hp Hout]] | Hall].
      + left. exists s. split; [ exact (Hsub s Hp) | exact Hout ].
      + right. intros s' Hout'. exact (Hsub s' (Hall s' Hout')).
    - intros H r Hobs. exact (H pre r Hobs (fun s Hs => Hs)).
  Qed.
End ASLPTriple.

Arguments tripleASLP {_} {_}.

Section ContrapositiveTransformers.
  Variable S : Type.
  
  Theorem obsASP_contrapositive {A} (m : nditprog S A) pre r :
  getProgASP (obsASP m) pre r <->
    ~ getProgDSLP (obsDSLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [s [Hp Hr]] Hall. exact (Hall s Hr Hp).
    - intro Hnn. apply NNPP. intro Habs. apply Hnn.
      intros s Hr Hp. apply Habs. exists s. split; [exact Hp | exact Hr].
  Qed.

  Theorem obsDSP_contrapositive {A} (m : nditprog S A) pre r :
    getProgDSP (obsDSP m) pre r <->
      ~ getProgASLP (obsASLP m) (fun x => ~ pre x) r.
  Proof.
    split.
    - intros [[s [Hp Hr]] Hall] [[s' [Hnp Hr']] | Hall'].
      + exact (Hnp (Hall s' Hr')).
      + exact (Hall' s Hr Hp).
    - intro Hnn. split.
      + apply NNPP. intro Hnex. apply Hnn. right.
        intros s Hr Hp. apply Hnex. exists s. split; [exact Hp | exact Hr].
      + intros s Hr. apply NNPP. intro Hnp. apply Hnn. left.
        exists s. split; [exact Hnp | exact Hr].
  Qed.

End ContrapositiveTransformers.

Section TaxonomySPTransformers.
  Variable S : Type.

   Theorem cc_aslp_implies_asp :
    forall A (m: nditprog S A) pre post,
      tripleASLP m Over pre post ->
      tripleASP m Over pre post.
   Proof. intros A m pre post H r Hasp. apply (H r). left. exact Hasp. Qed.

   Theorem cc_aslp_implies_dslp :
    forall A (m: nditprog S A) pre post,
      tripleASLP m Over pre post ->
      tripleDSLP m Over pre post.
   Proof. intros A m pre post H r Hdslp. apply (H r). right. exact Hdslp. Qed.

   Theorem cc_dslp_implies_dsp :
    forall A (m: nditprog S A) pre post,
      tripleDSLP m Over pre post ->
      tripleDSP m Over pre post.
   Proof. intros A m pre post H r [_ Hdslp]. exact (H r Hdslp). Qed.

   Theorem cc_asp_implies_dsp :
    forall A (m: nditprog S A) pre post,
      tripleASP m Over pre post ->
      tripleDSP m Over pre post.
   Proof. intros A m pre post H r [Hasp _]. exact (H r Hasp). Qed.

   Theorem ii_dsp_implies_dslp :
    forall A (m: nditprog S A) pre post,
      tripleDSP m Under pre post ->
      tripleDSLP m Under pre post.
   Proof. intros A m pre post H r Hpost. exact (proj2 (H r Hpost)). Qed.

   Theorem ii_dslp_implies_aslp :
    forall A (m: nditprog S A) pre post,
      tripleDSLP m Under pre post ->
      tripleASLP m Under pre post.
   Proof. intros A m pre post H r Hpost. right. exact (H r Hpost). Qed.

   Theorem ii_asp_implies_aslp :
    forall A (m: nditprog S A) pre post,
      tripleASP m Under pre post ->
      tripleASLP m Under pre post.
   Proof. intros A m pre post H r Hpost. left. exact (H r Hpost). Qed.

   Theorem ii_dsp_implies_asp :
    forall A (m: nditprog S A) pre post,
      tripleDSP m Under pre post ->
      tripleASP m Under pre post.
   Proof. intros A m pre post H r Hpost. exact (proj1 (H r Hpost)). Qed.

   Theorem ci_aslp_dsp_contrapositive :
    forall A (m : nditprog S A) pre post,
      tripleASLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleDSP m Under pre post.
   Proof.
     intros A m pre post H r Hpost. split.
     - apply NNPP. intro Hnex. apply (H r); [| exact Hpost]. right.
       intros s Hr Hp. apply Hnex. exists s. split; [exact Hp | exact Hr].
     - intros s Hr. apply NNPP. intro Hnp. apply (H r); [| exact Hpost]. left.
       exists s. split; [exact Hnp | exact Hr].
   Qed.

   Theorem ci_aslp_dsp_contrapositive' :
    forall A (m : nditprog S A) pre post,
      tripleDSP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleASLP m Over pre post.
   Proof.
     intros A m pre post H r Haslp. apply NNPP. intro Hnpost.
     destruct (H r Hnpost) as [[s0 [Hnp Hr0]] Hall].
     destruct Haslp as [[s [Hp Hr]] | Hall2].
     - exact (Hall s Hr Hp).
     - exact (Hnp (Hall2 s0 Hr0)).
   Qed.

     Theorem ci_asp_dslp_contrapositive :
    forall A (m : nditprog S A) pre post,
      tripleASP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleDSLP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost s Hr.
    apply NNPP. intro Hnpre.
    apply (Hii r); [| exact Hpost].
    exists s. split; [exact Hnpre | exact Hr].
  Qed.

  Theorem ci_asp_dslp_contrapositive' :
    forall A (m : nditprog S A) pre post,
      tripleDSLP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleASP m Over pre post.
  Proof.
    intros A m pre post Hii r [s [Hpre Hr]].
    apply NNPP. intro Hnpost.
    exact (Hii r Hnpost s Hr Hpre).
  Qed.

  (** The other diagonal of the square: a DSLP over-approximation of the
      negated pair is an ASP under-approximation of the original, and back.
      Both readings are the single relational statement
      [forall r, post r -> exists s, pre s /\ reach m s r], reached in each
      direction by [NNPP]. *)
  Theorem ci_dslp_asp_contrapositive :
    forall A (m : nditprog S A) pre post,
      tripleDSLP m Over (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleASP m Under pre post.
  Proof.
    intros A m pre post Hii r Hpost.
    apply NNPP. intro Hnex.
    apply (Hii r); [| exact Hpost].
    intros s Hr Hpre. apply Hnex. exists s. split; [exact Hpre | exact Hr].
  Qed.

  Theorem ci_dslp_asp_contrapositive' :
    forall A (m : nditprog S A) pre post,
      tripleASP m Under (fun s => ~ (pre s)) (fun r => ~ (post r)) ->
      tripleDSLP m Over pre post.
  Proof.
    intros A m pre post Hii r Hdslp.
    apply NNPP. intro Hnpost.
    destruct (Hii r Hnpost) as [s [Hnpre Hr]].
    exact (Hnpre (Hdslp s Hr)).
  Qed.
End TaxonomySPTransformers.

Section SPExamples.
  Definition P0 : nat -> Prop := fun s => s = 0.

  (** [progEx] from state [s] yields exactly [Some (tt, s + 1)] and
      [Some (tt, 42)], and never raises.  So relative to [P0 = {0}] the four
      outcomes below realise the four reachability classes:
      [Some (tt, 1)]  reachable only from [P0]      — both ASP and DSLP hold;
      [Some (tt, 42)] reachable from [P0] and outside — ASP only;
      [None]          unreachable                    — DSLP only (vacuously);
      [Some (tt, 99)] reachable only from outside    — neither. *)

  #[program] Theorem progEx_asp_1 :
    (obsASP progEx) P0 (Some (tt, 1)).
  Proof. exists 0. split; [reflexivity | cbn; sauto]. Qed.

  #[program] Theorem progEx_dslp_1 :
    (obsDSLP progEx) P0 (Some (tt, 1)).
  Proof. intros s Hr. cbn in Hr. unfold P0. sauto lq: on. Qed.

  #[program] Theorem progEx_dsp_1 :
    (obsDSP progEx) P0 (Some (tt, 1)).
  Proof. split; [exact progEx_asp_1 | exact progEx_dslp_1]. Qed.

  #[program] Theorem progEx_aslp_1 :
    (obsASLP progEx) P0 (Some (tt, 1)).
  Proof. left. exact progEx_asp_1. Qed.
  
  #[program] Theorem progEx_asp_42 :
    (obsASP progEx) P0 (Some (tt, 42)).
  Proof. exists 0. split; [reflexivity | cbn; sauto]. Qed.

  #[program] Theorem progEx_dslp_not_42 :
    ~ (obsDSLP progEx) P0 (Some (tt, 42)).
  Proof.
    intro H. specialize (H 1).
    assert (Hreach : unOptionT (unOptionT (runStateT progEx 1))
                       (Some (Some (tt, 42)))) by (cbn; sauto).
    specialize (H Hreach). unfold P0 in H. discriminate.
  Qed.

  #[program] Theorem progEx_dsp_not_42 :
    ~ (obsDSP progEx) P0 (Some (tt, 42)).
  Proof. intros [_ Hdslp]. exact (progEx_dslp_not_42 Hdslp). Qed.

  #[program] Theorem progEx_aslp_42 :
    (obsASLP progEx) P0 (Some (tt, 42)).
  Proof. left. exact progEx_asp_42. Qed.

  #[program] Theorem progEx_asp_not_None :
    ~ (obsASP progEx) P0 None.
  Proof. intros [s [_ Hr]]. cbn in Hr. sauto. Qed.

  #[program] Theorem progEx_dslp_None :
    (obsDSLP progEx) P0 None.
  Proof. intros s Hr. cbn in Hr. sauto. Qed.

  #[program] Theorem progEx_dsp_not_None :
    ~ (obsDSP progEx) P0 None.
  Proof. intros [Hasp _]. exact (progEx_asp_not_None Hasp). Qed.

  #[program] Theorem progEx_aslp_None :
    (obsASLP progEx) P0 None.
  Proof. right. exact progEx_dslp_None. Qed.

  #[program] Theorem progEx_asp_not_99 :
    ~ (obsASP progEx) P0 (Some (tt, 99)).
  Proof. intros [s [Hp Hr]]. unfold P0 in Hp. subst s. cbn in Hr. sauto. Qed.

  #[program] Theorem progEx_dslp_not_99 :
    ~ (obsDSLP progEx) P0 (Some (tt, 99)).
  Proof.
    intro H. specialize (H 98).
    assert (Hreach : unOptionT (unOptionT (runStateT progEx 98))
                       (Some (Some (tt, 99)))) by (cbn; sauto).
    specialize (H Hreach). unfold P0 in H. discriminate.
  Qed.

  #[program] Theorem progEx_dsp_not_99 :
    ~ (obsDSP progEx) P0 (Some (tt, 99)).
  Proof. intros [Hasp _]. exact (progEx_asp_not_99 Hasp). Qed.

  #[program] Theorem progEx_aslp_not_99 :
    ~ (obsASLP progEx) P0 (Some (tt, 99)).
  Proof.
    intros [Hasp | Hdslp];
      [ exact (progEx_asp_not_99 Hasp) | exact (progEx_dslp_not_99 Hdslp) ].
  Qed.

  Example progRet : nditprog nat unit := ret tt.

  Definition preEq0 : nat -> Prop := fun s => s = 0.
  Definition postEq0 : option (unit * nat) -> Prop :=
    fun r => r = Some (tt, 0).

  Theorem progRet_asp_inc :
    tripleASP progRet Under preEq0 postEq0.
  Proof.
    intros r Hpost. unfold postEq0 in Hpost. subst r.
    exists 0. split; [reflexivity | cbn; sauto].
  Qed.

  Theorem progRet_dsp_inc :
    tripleDSP progRet Under preEq0 postEq0.
  Proof.
    intros r Hpost. split; [ exact (progRet_asp_inc r Hpost) |].
    unfold postEq0 in Hpost. subst r.
    intros s Hr. cbn in Hr. unfold preEq0. sauto.
  Qed.
  
End SPExamples.

Section GaloisConnection.
  Variable S : Type.
  
  (** [obsDWLP] and [obsAWP] applied to a postcondition are the two readings of
      the same terminating slice that [obsASP] / [obsDSLP] use, so the triples
      differ only in the order of the [s] and [r] quantifiers. *)
  Lemma dwlp_slice {A} (m : nditprog S A) (s : S) (p : option (A * S) -> Prop) :
    unOptionT (runStateT (obsDWLP m) s) p
    <-> (forall r, unOptionT (unOptionT (runStateT m s)) (Some r) -> p r).
  Proof.
    cbn. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    cbn. split.
    - intros H r Hr. exact (H (Some r) Hr).
    - intros H oa Hoa. destruct oa as [r|]; [ exact (H r Hoa) | exact I ].
  Qed.

  Lemma awp_slice {A} (m : nditprog S A) (s : S) (p : option (A * S) -> Prop) :
    unOptionT (runStateT (obsAWP m) s) p
    <-> (exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ p r).
  Proof.
    cbn. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    cbn. split; intros [r [Hr Hp]]; exists r; split; assumption.
  Qed.

  Theorem dwlp_asp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsDWLP m pre SubsetOf post <->
        tripleASP m Over pre post.
  Proof.
    intros A m pre post. split.
    - intros H r [s [Hpre Hr]].
      exact (proj1 (dwlp_slice m s post) (H s Hpre) r Hr).
    - intros H s Hpre. apply dwlp_slice.
      intros r Hr. exact (H r (ex_intro _ s (conj Hpre Hr))).
    Qed.

  Theorem awp_dslp :
    forall A (m: nditprog S A) pre post,
      tripleWP obsAWP m pre SupersetOf post <->
        tripleDSLP m Under pre post.
  Proof.
    intros A m pre post. split.
    - intros H r Hpost s Hr.
      exact (H s (proj2 (awp_slice m s post) (ex_intro _ r (conj Hr Hpost)))).
    - intros H s Hawp.
      destruct (proj1 (awp_slice m s post) Hawp) as [r [Hr Hpost]].
      exact (H r Hpost s Hr).
  Qed.
End GaloisConnection.

(*Section PrePostEmbedding.
  Variable S : Type.

  Definition PrePostS (A : Type) := ((S -> Prop) * (S -> option (A * S) -> Prop))%type.

  Definition ret_PrePostS {A} (a : A) : PrePostS A := (fun _ => True, fun s r => r = Some (a, s)).

  Definition bind_PrePostS {A B} (m : PrePostS A) (k : A -> PrePostS B) : PrePostS B :=
    (fun s0 x => fst m s0 /\ (forall a s1, snd m s0 (Some (a, s1)) -> fst (k a) s1),
     fun s0 x => (exists a s1, snd m s0 (Some (a, s1)) /\ snd (k a) s1 x) \/ (x = None /\ snd m s0 None)).

End PrePostEmbedding.*)
