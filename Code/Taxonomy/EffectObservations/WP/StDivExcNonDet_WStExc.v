(** * WP observations of [stdivexcnd] into [WStExc]

    The observations [obsDWP] / [obsDWLP] / [obsAWP] / [obsAWLP], the WP
    triples they support, and their monad morphism laws.  Comparisons
    between the four observations live in
    [Taxonomy_StDivExcNonDet_StExc.v]. *)

From Coq Require Import Lia Classical_Prop PeanoNat Morphisms RelationClasses.
From ExtLib Require Import Monad MonadState MonadExc StateMonad OptionMonad.
From Hammer Require Import Tactics.
From ITree Require Import Basics.Monad.
From Incorrectness.Classes Require Import Arrow StateArrowT.
From Incorrectness.Taxonomy.ComputationMonads Require Import TransformerLaws StExcNonDet StDivExcNonDet StDivITree.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import WPureMonad PredMonad.
From Incorrectness.Taxonomy.Arrows Require Import PredArr SPostArr.
From Incorrectness.Taxonomy Require Import ExampleProgramDefs.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

Section NDItObservationWP.

  Variable S : Type.

  (** Demonic WP (total): ALL outcomes must terminate and satisfy
      the postcondition.  Divergence is not acceptable. *)
  Lemma obsDWP_mono {A} (m : stdivexcnd S A) (s : S) :
    wpure_mono (fun post =>
      match runStateT m s with
      | mkOptionT inner => match inner with
          | mkOptionT outcomes => forall oa, outcomes oa ->
              match oa with Some r => post r | None => False end
          end end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    intros oa Ho. specialize (H oa Ho).
    destruct oa as [r|]; [ exact (Hpq r H) | exact H ].
  Qed.

  Definition obsDWP {A} (m : stdivexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsDWP_mono m s))).

  (** Demonic WLP (partial): ALL terminating outcomes satisfy the
      postcondition.  Divergence is acceptable. *)
  Lemma obsDWLP_mono {A} (m : stdivexcnd S A) (s : S) :
    wpure_mono (fun post =>
      match runStateT m s with
      | mkOptionT inner => match inner with
          | mkOptionT outcomes => forall oa, outcomes oa ->
              match oa with Some r => post r | None => True end
          end end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    intros oa Ho. specialize (H oa Ho).
    destruct oa as [r|]; [ exact (Hpq r H) | exact H ].
  Qed.

  Definition obsDWLP {A} (m : stdivexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsDWLP_mono m s))).

  (** Angelic WP (total): SOME terminating outcome satisfies the
      postcondition. *)
  Lemma obsAWP_mono {A} (m : stdivexcnd S A) (s : S) :
    wpure_mono (fun post =>
      match runStateT m s with
      | mkOptionT inner => match inner with
          | mkOptionT outcomes => exists r, outcomes (Some r) /\ post r
          end end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    destruct H as [r [Ho Hp]]. exists r. split; [ exact Ho | exact (Hpq r Hp) ].
  Qed.

  Definition obsAWP {A} (m : stdivexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsAWP_mono m s))).

  (** Angelic WLP (partial): SOME terminating outcome satisfies the
      postcondition, OR divergence is possible. *)
  Lemma obsAWLP_mono {A} (m : stdivexcnd S A) (s : S) :
    wpure_mono (fun post =>
      match runStateT m s with
      | mkOptionT inner => match inner with
          | mkOptionT outcomes =>
              (exists r, outcomes (Some r) /\ post r) \/ outcomes None
          end end).
  Proof.
    intros p q Hpq H. destruct (runStateT m s) as [inner]. destruct inner as [outcomes].
    destruct H as [[r [Ho Hp]] | Hn];
      [ left; exists r; split; [ exact Ho | exact (Hpq r Hp) ] | right; exact Hn ].
  Qed.

  Definition obsAWLP {A} (m : stdivexcnd S A) : WStExc S A :=
    mkStateT (fun s => @mkOptionT WPure _ (mkWPure _ (obsAWLP_mono m s))).

  Theorem obsDPCollapse :
    forall {A} (m : stdivexcnd S A) post s0,
      (~ unOptionT (unOptionT (runStateT m s0)) None) ->
      (unOptionT (runStateT (obsDWP m) s0) post <-> unOptionT (runStateT (obsDWLP m) s0) post).
  Proof.
    intros A m post s0 Hnd. cbn.
    destruct (runStateT m s0) as [[outcomes]]. cbn in Hnd.
    split.
    - (* DWP -> DWLP: weaken [False] to [True] in the divergence branch. *)
      intros H oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [exact H | exact I].
    - (* DWLP -> DWP: divergence is unreachable, so its branch is vacuous. *)
      intros H oa Hoa. specialize (H oa Hoa).
      destruct oa as [r|]; [exact H | exfalso; exact (Hnd Hoa)].
  Qed.

  Theorem obsAPCollapse :
    forall {A} (m : stdivexcnd S A) post s0,
      (~ unOptionT (unOptionT (runStateT m s0)) None) ->
      (unOptionT (runStateT (obsAWP m) s0) post <-> unOptionT (runStateT (obsAWLP m) s0) post).
  Proof.
    intros A m post s0 Hnd. cbn.
    destruct (runStateT m s0) as [[outcomes]]. cbn in Hnd.
    split.
    - (* AWP -> AWLP: left-inject the terminating witness. *)
      intro H. left. exact H.
    - (* AWLP -> AWP: the divergence disjunct is ruled out. *)
      intros [H | Hdiv]; [exact H | exfalso; exact (Hnd Hdiv)].
  Qed.

End NDItObservationWP.

Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.
Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.

(* ================================================================= *)
(** ** WP triples                                                    *)
(* ================================================================= *)

Section WPTriples.

  Inductive approxKindWP := | SubsetOf | SupersetOf.

  Definition tripleWP {S A}
    (obs : stdivexcnd S A -> WStExc S A)
    (prog : stdivexcnd S A)
    (pre : S -> Prop)
    (kind:approxKindWP)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match kind with
    | SubsetOf =>
        forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | SupersetOf =>
        forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.

  Lemma pp2wp_subset_mono {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) (s0 : S) :
    wpure_mono (fun p => pre s0 /\ (forall r, post r -> p r)).
  Proof.
    intros p q Hpq [Hpre Hsub]. split; [ exact Hpre |].
    intros r Hr. exact (Hpq r (Hsub r Hr)).
  Qed.

  Definition pp2wp_subset {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : WStExc S A :=
    mkStateT (fun s0 => @mkOptionT WPure _ (mkWPure _ (pp2wp_subset_mono pre post s0))).

  Lemma pp2wp_superset_mono {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) (s0 : S) :
    wpure_mono (fun p => (forall r, p r -> post r) -> pre s0).
  Proof.
    intros p q Hpq H Hsub. apply H. intros r Hr. exact (Hsub r (Hpq r Hr)).
  Qed.

  Definition pp2wp_superset {S A} (pre : S -> Prop) (post : option (A * S) -> Prop) : WStExc S A :=
    mkStateT (fun s0 => @mkOptionT WPure _ (mkWPure _ (pp2wp_superset_mono pre post s0))).

  Definition tripleWPspec {S A}
    (obs : stdivexcnd S A -> WStExc S A)
    (prog : stdivexcnd S A)
    (pre : S -> Prop)
    (kind:approxKindWP)
    (post : option (A * S) -> Prop)
    : Prop
    :=
    match kind with
    | SubsetOf =>
        ordWStExc (obs prog) (pp2wp_subset pre post)
    | SupersetOf =>
        ordWStExc (pp2wp_superset pre post) (obs prog)
    end.

  Section tripleWPDefEq.
    Variable S : Type.
    
    Theorem obsDWLP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsDWLP prog) s) p ->
        unOptionT (runStateT (obsDWLP prog) s) q.
    Proof.
      intros s p q H Hp. exact (obsDWLP_mono _ prog s p q H Hp).
    Qed.
    
    Theorem obsDWP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsDWP prog) s) p ->
        unOptionT (runStateT (obsDWP prog) s) q.
    Proof.
      intros s p q H Hp. exact (obsDWP_mono _ prog s p q H Hp).
    Qed.
    
    Theorem obsAWLP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsAWLP prog) s) p ->
        unOptionT (runStateT (obsAWLP prog) s) q.
    Proof.
      intros s p q H Hp. exact (obsAWLP_mono _ prog s p q H Hp).
    Qed.
    
    Theorem obsAWP_monotonic {A} prog :
      forall s (p q : option (A * S) -> Prop),
        (forall r, p r -> q r) ->
        unOptionT (runStateT (obsAWP prog) s) p ->
        unOptionT (runStateT (obsAWP prog) s) q.
    Proof.
      intros s p q H Hp. exact (obsAWP_mono _ prog s p q H Hp).
    Qed.
    
    Theorem tripleWPDefEq {A}
      (obs : stdivexcnd S A -> WStExc S A)
      (prog : stdivexcnd S A)
      (kind:approxKindWP)
      (pre : S -> Prop)
      (post : option (A * S) -> Prop)
      (Hmono : forall s (p q : option (A * S) -> Prop),
          (forall r, p r -> q r) ->
          unOptionT (runStateT (obs prog) s) p ->
          unOptionT (runStateT (obs prog) s) q) :
      tripleWP obs prog pre kind post <-> tripleWPspec obs prog pre kind post.
    Proof.
      unfold tripleWP, tripleWPspec, ordWStExc, pp2wp_subset, pp2wp_superset.
      destruct kind; cbn [runStateT unOptionT]; split.
      - intros H s p [Hpre Hsub]. apply (Hmono s post p Hsub). exact (H s Hpre).
      - intros H s Hpre. apply (H s post). split; [exact Hpre | intros r hr; exact hr].
      - intros H s p Hwp Hsub. apply H. apply (Hmono s p post Hsub). exact Hwp.
      - intros H s Hwp. apply (H s post Hwp). intros r hr; exact hr.
    Qed.
    
  End tripleWPDefEq.

End WPTriples.

Section MonadMorphismLawsWP.
  Variable S : Type.

  Lemma outcomes_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) sigma ob :
  unOptionT (unOptionT (runStateT (x >>= f) sigma)) ob <->
  (exists oy, unOptionT (unOptionT (runStateT x sigma)) oy /\
    match oy with
    | Some (Some (a, s')) => unOptionT (unOptionT (runStateT (f a) s')) ob
    | Some None => ob = Some None
    | None => ob = None
    end).
  Proof.
  cbn. split.
  - intros [oy [H1 H2]]. exists oy. split; [exact H1|]. destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  - intros [oy [H1 H2]]. exists oy. split; [exact H1|]. destruct oy as [[[a s']|]|]; cbn in *; exact H2.
  Qed.
  
  Lemma obsDWP_ret {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsDWP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    cbn. split.
    - intro H. exact (H (Some (Some (a, s0))) eq_refl).
    - intros H oa Hoa. subst oa. exact H.
  Qed.

  Lemma obsDWP_unfold {A} (m : stdivexcnd S A) s post :
  unOptionT (runStateT (obsDWP m) s) post <->
  (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
              match oa with Some r => post r | None => False end).
  Proof. unfold obsDWP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

  (** WP bind adequacy: the Dijkstra [wp_bind] law (same shape for all four
    WP observations; shown for [obsDWP]).  The [None] branch threads [x]'s
    exception through to [post None]. *)
  Lemma obsDWP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) s post :
    unOptionT (runStateT (obsDWP (x >>= f)) s) post <->
    unOptionT (runStateT (obsDWP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWP (f a)) s') post
               | None => post None
               end).
  Proof.
  rewrite (obsDWP_unfold (x >>= f) s post). rewrite (obsDWP_unfold x s _).
  setoid_rewrite outcomes_bind. split.
  - intros HL oy Hoy. destruct oy as [[[a s']|]|].
    + cbn beta iota. rewrite obsDWP_unfold. intros ob Hob.
      apply HL. exists (Some (Some (a, s'))). split; [exact Hoy | exact Hob].
    + apply (HL (Some None)). exists (Some None). split; [exact Hoy | reflexivity].
    + apply (HL None). exists None. split; [exact Hoy | reflexivity].
  - intros HR oa [oy [Hoy Hk]]. specialize (HR oy Hoy). destruct oy as [[[a s']|]|].
    + cbn beta iota in HR. rewrite obsDWP_unfold in HR. exact (HR oa Hk).
    + cbn in Hk. subst oa. exact HR.
    + cbn in Hk. subst oa. destruct HR.
  Qed.

  Lemma obsDWLP_ret {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsDWLP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    cbn. split.
    - intro H. exact (H (Some (Some (a, s0))) eq_refl).
    - intros H oa Hoa. subst oa. exact H.
  Qed.

  Lemma obsDWLP_unfold {A} (m : stdivexcnd S A) s post :
  unOptionT (runStateT (obsDWLP m) s) post <->
  (forall oa, unOptionT (unOptionT (runStateT m s)) oa ->
              match oa with Some r => post r | None => True end).
  Proof. unfold obsDWLP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

  (** [wp_bind] for demonic-liberal WP. *)
  Lemma obsDWLP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) s post :
  unOptionT (runStateT (obsDWLP (x >>= f)) s) post <->
  unOptionT (runStateT (obsDWLP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsDWLP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsDWLP_unfold (x >>= f) s post). rewrite (obsDWLP_unfold x s _).
  setoid_rewrite outcomes_bind. split.
  - intros HL oy Hoy. destruct oy as [[[a s']|]|].
    + cbn beta iota. rewrite obsDWLP_unfold. intros ob Hob.
      apply HL. exists (Some (Some (a, s'))). split; [exact Hoy | exact Hob].
    + apply (HL (Some None)). exists (Some None). split; [exact Hoy | reflexivity].
    + exact I.
  - intros HR oa [oy [Hoy Hk]]. specialize (HR oy Hoy). destruct oy as [[[a s']|]|].
    + cbn beta iota in HR. rewrite obsDWLP_unfold in HR. exact (HR oa Hk).
    + cbn in Hk. subst oa. exact HR.
    + cbn in Hk. subst oa. exact I.
  Qed.

  Lemma obsAWP_ret {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsAWP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    cbn. split.
    - intros [r [Hr Hp]]. injection Hr as Hr. subst r. exact Hp.
    - intro H. exists (Some (a, s0)). split; [ reflexivity | exact H ].
  Qed.

  Lemma obsAWP_unfold {A} (m : stdivexcnd S A) s post :
  unOptionT (runStateT (obsAWP m) s) post <->
  (exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r).
  Proof. unfold obsAWP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.

  (** [wp_bind] for angelic-total WP. *)
  Lemma obsAWP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) s post :
  unOptionT (runStateT (obsAWP (x >>= f)) s) post <->
  unOptionT (runStateT (obsAWP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsAWP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsAWP_unfold (x >>= f) s post). rewrite (obsAWP_unfold x s _). split.
  - intros [r [Hr Hpost]]. apply outcomes_bind in Hr. destruct Hr as [oy [Hoy Hk]].
    destruct oy as [[[a s']|]|].
    + exists (Some (a, s')). split; [exact Hoy|].
      cbn beta iota. rewrite obsAWP_unfold. exists r. split; [exact Hk | exact Hpost].
    + cbn in Hk. injection Hk as Hk. subst r. exists None. split; [exact Hoy|]. cbn beta iota. exact Hpost.
    + cbn in Hk. discriminate Hk.
  - intros [rx [Hrx HQ]]. destruct rx as [[a s']|].
    + cbn beta iota in HQ. rewrite obsAWP_unfold in HQ. destruct HQ as [r [Hr Hpost]].
      exists r. split; [|exact Hpost]. apply outcomes_bind.
      exists (Some (Some (a, s'))). split; [exact Hrx | exact Hr].
    + cbn beta iota in HQ. exists None. split; [|exact HQ]. apply outcomes_bind.
      exists (Some None). split; [exact Hrx | reflexivity].
  Qed.

  Lemma obsAWLP_ret {A} (a : A) (s0 : S) (post : option (A * S) -> Prop) :
    unOptionT (runStateT (obsAWLP (ret a)) s0) post <->
    unOptionT (runStateT (WPureMonad.retP S a) s0) post.
  Proof.
    cbn. split.
    - intros [[r [Hr Hp]] | Hd];
        [ injection Hr as Hr; subst r; exact Hp | discriminate Hd ].
    - intro H. left. exists (Some (a, s0)). split; [ reflexivity | exact H ].
  Qed.

  Lemma obsAWLP_unfold {A} (m : stdivexcnd S A) s post :
  unOptionT (runStateT (obsAWLP m) s) post <->
  ((exists r, unOptionT (unOptionT (runStateT m s)) (Some r) /\ post r)
   \/ unOptionT (unOptionT (runStateT m s)) None).
  Proof. unfold obsAWLP. cbn. destruct (runStateT m s) as [[outcomes]]. cbn. reflexivity. Qed.
  
  (** [wp_bind] for angelic-liberal WP (the divergence disjunct threads
    through both [x] diverging and [f] diverging after [x] converges). *)
  Lemma obsAWLP_bind {A B} (x : stdivexcnd S A) (f : A -> stdivexcnd S B) s post :
  unOptionT (runStateT (obsAWLP (x >>= f)) s) post <->
  unOptionT (runStateT (obsAWLP x) s)
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obsAWLP (f a)) s') post
               | None => post None end).
  Proof.
  rewrite (obsAWLP_unfold (x >>= f) s post). rewrite (obsAWLP_unfold x s _). split.
  - intros [[r [Hr Hpost]] | Hdiv].
    + apply outcomes_bind in Hr. destruct Hr as [oy [Hoy Hk]]. destruct oy as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoy|].
        cbn beta iota. rewrite obsAWLP_unfold. left. exists r. split; [exact Hk | exact Hpost].
      * cbn in Hk. injection Hk as Hk. subst r. left. exists None. split; [exact Hoy|]. cbn beta iota. exact Hpost.
      * cbn in Hk. discriminate Hk.
    + apply outcomes_bind in Hdiv. destruct Hdiv as [oy [Hoy Hk]]. destruct oy as [[[a s']|]|].
      * left. exists (Some (a, s')). split; [exact Hoy|].
        cbn beta iota. rewrite obsAWLP_unfold. right. exact Hk.
      * cbn in Hk. discriminate Hk.
      * right. exact Hoy.
  - intros [[rx [Hrx HQ]] | Hdivx].
    + destruct rx as [[a s']|].
      * cbn beta iota in HQ. rewrite obsAWLP_unfold in HQ. destruct HQ as [[r [Hr Hpost]] | Hdivf].
        -- left. exists r. split; [|exact Hpost]. apply outcomes_bind.
           exists (Some (Some (a, s'))). split; [exact Hrx | exact Hr].
        -- right. apply outcomes_bind. exists (Some (Some (a, s'))). split; [exact Hrx | exact Hdivf].
      * cbn beta iota in HQ. left. exists None. split; [|exact HQ]. apply outcomes_bind.
        exists (Some None). split; [exact Hrx | reflexivity].
    + right. apply outcomes_bind. exists None. split; [exact Hdivx | reflexivity].
  Qed.
End MonadMorphismLawsWP.

(* ================================================================= *)
(** ** WP examples: pure nondeterminism (no divergence)               *)
(* ================================================================= *)

Example progA_DWP := obsDWP progA.
Example progA_AWP := obsAWP progA.

(** DWP can prove a property that holds for ALL outcomes. *)
Theorem progA_DWP_all :
  tripleWP obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

Theorem progA_DWP_all_spec :
  tripleWPspec obsDWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  (* [tripleWPspec _ Under] is the spec-as-WP-element form
     [(pre s /\ post <= p) -> wp p s]; derive it from the direct form
     [progA_DWP_all] by monotonicity of [obsDWP] in its postcondition. *)
  unfold tripleWPspec, ordWStExc, pp2wp_subset.
  intros s p Hp. cbn [runStateT unOptionT] in Hp. destruct Hp as [_ Hsub].
  pose proof progA_DWP_all as Hall. unfold tripleWP in Hall. specialize (Hall s I).
  exact (obsDWP_mono _ progA s _ p Hsub Hall).
Qed.

(** DWP cannot prove a property that holds for only one branch. *)
Theorem progA_DWP_not42 : 
  not (
    tripleWP obsDWP progA
      (fun _ => True)
      SubsetOf
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 42
        | None => False
        end)).
Proof.
  intro contra.
  unfold tripleWP in contra. specialize (contra 0 I). cbn in contra.
  specialize (contra (Some (Some (tt, 43)))). sauto.
Qed.

(** AWP can prove a property satisfied by SOME outcome. *)
Theorem progA_AWP_42 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

Theorem progA_AWP_43 :
  tripleWP obsAWP progA
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 43
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 43)). split; sauto.
Qed.

(** AWP, over-approximate ([Over]) reading: [awp(post) ⊆ pre], the
    "necessary precondition" of partial incorrectness — every state from
    which [progA] can *angelically* reach an outcome in [post] must lie in
    [pre].  [progA] overwrites the state with [put 42] and then yields [42]
    or [43], so no run reaches state [100]; hence [awp(reach 100)] is empty
    and even the empty precondition [fun _ => False] is a valid (necessary)
    precondition.  (Contrast: for a *reachable* post like [reach 43],
    [awp] would be all of [nat], forcing [pre] to be [True].) *)
Theorem progA_AWP_100_over :
  tripleWP obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  unfold tripleWP. intros s H. cbn in H.
  destruct H as [r [Hr Heq]]. subst r. cbn in Hr. sauto.
Qed.

Theorem progA_AWP_100_over_spec :
  tripleWPspec obsAWP progA
    (fun _ => False)
    SupersetOf
    (fun r : option (unit * nat) => r = Some (tt, 100)).
Proof.
  (* [tripleWPspec _ Over] is [forall s p, awp p s -> ((p <= post) -> pre s)].
     An angelic witness [r] of [awp p s] satisfies [p], hence [p <= post]
     forces [r = Some (tt, 100)] — unreachable for [progA]. *)
  unfold tripleWPspec, ordWStExc, pp2wp_superset.
  intros s p Hp Hsub. cbn in Hp.
  destruct Hp as [r [Hr Hpr]]. specialize (Hsub r Hpr).
  subst r. cbn in Hr. sauto.
Qed.
  
(* ================================================================= *)
(** ** WP examples: nondeterminism + divergence                       *)
(* ================================================================= *)

Example progB_DWP := obsDWP progB.
Example progB_DWLP := obsDWLP progB.
Example progB_AWP := obsAWP progB.

(** DWP is unprovable: the divergent branch forces [False]. *)
Theorem progB_DWP_unprovable :
  not (
    tripleWP obsDWP progB
      (fun _ => True)
      SubsetOf
      (fun r : option (unit * nat) =>
          match r with
          | Some (_, s) => s = 42
          | None => False
          end)).
Proof.
  intro contra.
  unfold tripleWP in contra. specialize (contra 0 I). cbn in contra.
  specialize (contra None). sauto.
Qed.

(** DWLP succeeds: divergent branches are ignored. *)
Theorem progB_DWLP_42 :
  tripleWP obsDWLP progB
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. intros [[[]|]|] H; sauto.
Qed.

(** AWP succeeds: the converging branch witnesses the postcondition. *)
Theorem progB_AWP_42 :
  tripleWP obsAWP progB
    (fun _ => True)
    SubsetOf
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s = 42
      | None => False
      end).
Proof.
  intros s0 _. cbn. exists (Some (tt, 42)). split; sauto.
Qed.

(** "There are divergent branches": divergence (the outermost [None]
    outcome) is *not* a result, so it is invisible to the SP observations
    ([obsRel] only sees the terminating [Some r] slice — cf.
    [progB_not_None]).  It is carried only by the *liberal* WP
    observations: [obsAWLP m s post = (exists terminating r, post r) \/
    (divergence reachable)].  Taking [post := fun _ => False] empties the
    terminating disjunct, so the triple says exactly "from every state,
    SOME branch diverges" (angelic), witnessed here by the [spinP] branch.

    This is the same shape as the (false) [progloom_correct] attempt —
    [progloom] never diverges, [progB] does.  Using [obsDWLP] instead
    would read "ALL branches diverge", which is false for [progB] (the
    [put s] branch converges). *)
Theorem progB_has_divergent_branch :
  tripleWP obsAWLP progB (fun _ => True) SubsetOf (fun _ => False).
Proof.
  intros s _. cbn.
  right.
  exists (Some (Some (tt, 42))). split; [reflexivity|].
  cbn. exists (Some (Some (42, 42))). split; [reflexivity|].
  cbn. right. reflexivity.
Qed.


(** The DWP-Inc triple now holds: [dwp(postEq0)(s)] forces [s = 0]. *)
Theorem progRet_dwp_inc :
  tripleWP obsDWP progRet preEq0 SupersetOf postEq0.
Proof.
  intros s Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(** Likewise DWLP-Inc holds (the divergence branch is vacuous, since
    [progRet] never diverges). *)
Theorem progRet_dwlp_inc :
  tripleWP obsDWLP progRet preEq0 SupersetOf postEq0.
Proof.
  intros s Hwp. cbn in Hwp.
  specialize (Hwp (Some (Some (tt, s))) eq_refl).
  unfold postEq0 in Hwp. injection Hwp as Hs. exact Hs.
Qed.

(* ================================================================= *)
(** ** The law of the excluded miracle                               *)
(* ================================================================= *)

(** [stdivexcnd] is bigger than the language: the everywhere-blocked
    element has no outcomes at all, and [obsDWP] quantifies over the
    outcome set, so it establishes every postcondition -- a MIRACLE.  The
    non-empty fragment [stdivexcndNE] of [StDivExcNonDet.v] is exactly
    what rules this out. *)

Definition blockedP {S A} : stdivexcnd S A :=
  mkStateT (fun _ => @mkOptionT (optionT SetM) _ (@mkOptionT SetM _ (fun _ => False))).

Theorem blocked_is_miracle {S A} (s : S) :
  unOptionT (runStateT (obsDWP (@blockedP S A)) s) (fun _ => False).
Proof.
  apply obsDWP_unfold. intros oa Hoa. destruct oa as [r|]; destruct Hoa.
Qed.

Theorem blocked_not_nonEmpty {S A} (s : S) : ~ @nonEmptyOutcomes S A blockedP.
Proof. intro H. destruct (H s) as [oa Hoa]. destruct Hoa. Qed.

(** On the non-empty fragment, [obsDWP] is strict: no program establishes
    [False].  This is Dijkstra's first healthiness condition. *)
Theorem obsDWP_excluded_miracle {S A} (m : stdivexcnd S A) (s : S) :
  nonEmptyOutcomes m ->
  ~ unOptionT (runStateT (obsDWP m) s) (fun _ => False).
Proof.
  intros Hne H. destruct (Hne s) as [oa Hoa].
  pose proof (proj1 (obsDWP_unfold S m s (fun _ => False)) H oa Hoa) as Hc.
  destruct oa as [r|]; exact Hc.
Qed.
