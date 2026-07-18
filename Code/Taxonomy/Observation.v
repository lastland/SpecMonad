(** * Observation functions for [prog].

    Maps [prog S A] (deterministic computation via ITree) to specification
    types.

    WP observations: [obsAWP] and [obsDWP] (total) and [obsAWLP] and [obsDWLP]
    (partial, tolerates divergence) map into [ProgWP S A]. Because [prog S A] is
    deterministic, we show [obsWPCollapse] and [obsWLPCollapse] theorems that
    state [obsAWP] is equivalent to [obsDWP], [obsAWLP] is equivalent to
    [obsDWLP].

    SP observation: [obsASP] and [obsDSLP], then [obsDSP] and [obsASLP] can be
    defined based on the former two. Even though [prog S A] is deterministic, it
    is not necessarily reversible, so we cannot collapse any of the [sp]s. *)

From Coq Require Import Classical_Prop.
From ExtLib Require Import
  Monad MonadState MonadExc
  StateMonad OptionMonad.
From Incorrectness.Classes Require Import Arrow.
From Incorrectness.Taxonomy Require Import Prog WP Rel SPost WPred.
From Paco Require Import paco.
From Hammer Require Import Tactics.
From ITree Require Import ITree Eq Props.Infinite.
From ITree.Extra Require Import Dijkstra.PureITreeBasics.

Import MonadNotation.
Open Scope monad_scope.

(* ================================================================= *)
(** ** WP observations                                                *)
(* ================================================================= *)

(** There is no nondeterminism in [prog], so [awp] and [dwp] are the same. We
    only define [wp] here. *)

Section ObservationWP.

  Variable S : Type.

  Definition obsAWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                        | mkOptionT o => exists r, eutt eq o (ret r) /\ post r
                        end)).

  Definition obsAWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (exists r, eutt eq o (ret r) /\ post r) \/
                                           any_infinite o
                        end)).

  Definition obsDWP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o => (forall r, eutt eq o (ret r) -> post r) /\
                                           ~ any_infinite o
                        end)).

  Definition obsDWLP {A} (m : prog S A) : ProgWP S A :=
    mkStateT
      (fun s => mkOptionT
               (fun post => match runStateT m s with
                         | mkOptionT o =>
                             (forall r, eutt eq o (ret r) -> post r) : Prop
                         end)).

  Theorem obsWPCollapse :
    forall {A} (m : prog S A) post s0,
      unOptionT (runStateT (obsAWP m) s0) post <->
        unOptionT (runStateT (obsDWP m) s0) post.
  Proof.
    intros. cbn. destruct (runStateT m s0) as [o] eqn:Hs. split.
    - intros [r [He Hp]]. split.
      + intros r' He'. rewrite He' in He. apply eutt_inv_Ret in He. subst. exact Hp.
      + intro Hinf. rewrite He in Hinf. exact (ret_not_div Hinf).
    - intros [Hall Hninf].
      destruct (eutt_reta_or_div o) as [[a Ha] | Hinf]; [| contradiction].
      symmetry in Ha. exists a. auto.
  Qed.

  Theorem obsWLPCollapse :
    forall {A} (m : prog S A) post s0,
      unOptionT (runStateT (obsAWLP m) s0) post <->
        unOptionT (runStateT (obsDWLP m) s0) post.
  Proof.
    intros. cbn. destruct (runStateT m s0) as [o] eqn:Hs. split.
    - intros [[r [He Hp]] | Hinf].
      + intros r' He'. rewrite He' in He. apply eutt_inv_Ret in He. subst. exact Hp.
      + intros r' He'. exfalso. rewrite He' in Hinf. exact (ret_not_div Hinf).
    - intros Hall.
      destruct (eutt_reta_or_div o) as [[a Ha] | Hinf].
      + left. symmetry in Ha. exists a. auto.
      + right. exact Hinf.
  Qed.
  
End ObservationWP.

Arguments obsAWP {_} {_}.
Arguments obsAWLP {_} {_}.
Arguments obsDWP {_} {_}.
Arguments obsDWLP {_} {_}.

Inductive approximationKind := | Under | Over.

(** Backward (WP) triple, defined as an *exegesis* (apply the WP
    observation to [post], compare by inclusion with [pre]), matching
    [NonDetItObservation.tripleWP].

    - [Under] reads  [pre ⊆ wp⟦m⟧(post)]  (e.g. [b ⊆ dwlp(c)]).
    - [Over]  reads  [wp⟦m⟧(post) ⊆ pre]  (e.g. [awp(c) ⊆ b]).

    This replaces the earlier [pp2wp]/[ordProgWP] (spec-as-element +
    refinement over all predicates) encoding; that encoding agrees with
    this one on [Under] but degenerates on [Over], and only the direct
    form makes the [awp ⊣ dslp] Galois connection provable. *)
Definition tripleWP {S A}
  (obs : prog S A -> ProgWP S A)
  (prog : prog S A)
  (is_correct:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
    match is_correct with
    | Under =>
        forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | Over =>
        forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.

Example progA : prog nat unit :=
  put 42 ;;
  s <- get ;;
  put s.

Example progA_WP := obsDWP progA.

(** [progA] deterministically converges to [(tt, 42)] from any initial
    state. *)
Lemma progA_run :
  forall s, eutt eq (unOptionT (runStateT progA s)) (Ret (Some (tt, 42))).
Proof.
  intro s. unfold progA. cbn.
  repeat (setoid_rewrite bind_ret_l; cbn).
  reflexivity.
Qed.

Theorem progA_WP_all :
  forall s, unOptionT (runStateT progA_WP s)
              (fun r : option (unit * nat) =>
                 match r with
                 | Some (_, s) => s = 42
                 | None => False
                 end).
Proof.
  intro s. pose proof (progA_run s) as Hrun.
  unfold progA_WP, obsDWP. cbn [runStateT unOptionT].
  destruct (runStateT progA s) as [o] eqn:E. cbn in Hrun.
  split.
  - intros r Hr. rewrite Hrun in Hr. apply eutt_inv_Ret in Hr. subst r. reflexivity.
  - intro Hinf. rewrite Hrun in Hinf. exact (ret_not_div Hinf).
Qed.

Theorem progA_WP_all_triple :
  tripleWP obsDWP progA Under
    (fun _ => True)
    (fun r : option (unit * nat) =>
      match r with
      | Some (_, s) => s >= 42
      | None => False
      end).
Proof.
  unfold tripleWP. intros s _.
  pose proof (progA_run s) as Hrun.
  unfold obsDWP. cbn [runStateT unOptionT].
  destruct (runStateT progA s) as [o] eqn:E. cbn in Hrun.
  split.
  - intros r Hr. rewrite Hrun in Hr. apply eutt_inv_Ret in Hr. subst r.
    cbn. auto with arith.
  - intro Hinf. rewrite Hrun in Hinf. exact (ret_not_div Hinf).
Qed.

Theorem progA_WP_not43 :
  not (forall s, unOptionT (runStateT progA_WP s)
                   (fun r : option (unit * nat) =>
                      match r with
                      | Some (_, s) => s = 43
                      | None => False
                      end)).
Proof.
  intro H. specialize (H 0). pose proof (progA_run 0) as Hrun.
  unfold progA_WP, obsDWP in H. cbn [runStateT unOptionT] in H.
  destruct (runStateT progA 0) as [o] eqn:E. cbn in Hrun.
  destruct H as [Hall _].
  specialize (Hall (Some (tt, 42)) Hrun). cbn in Hall. discriminate.
Qed.

(** A [Correct] triple fails exactly when the postcondition excludes a
    reachable outcome: [progA] reaches state [42], which violates [s = 43]. *)
Theorem progA_WP_not43_triple :
  not (tripleWP obsDWP progA Under
      (fun _ => True)
      (fun r : option (unit * nat) =>
        match r with
        | Some (_, s) => s = 43
        | None => False
        end)).
Proof.
  unfold tripleWP. intro H.
  specialize (H 0 I). pose proof (progA_run 0) as Hrun.
  unfold obsDWP in H. cbn [runStateT unOptionT] in H.
  destruct (runStateT progA 0) as [o] eqn:E. cbn in Hrun.
  destruct H as [Hall _].
  specialize (Hall (Some (tt, 42)) Hrun). cbn in Hall. discriminate.
Qed.

(*
monad trans:
(pre : Prop) -> (A -> Prop / pre)

S -> (pre : Prop) -> (A * S -> Prop / pre)

arrow trans:                  
(A -> Prop) -> B -> Prop

S -> (A -> Prop) -> S * B -> Prop     <-- monad trans                    

(S * A -> Prop) -> S * B -> Prop      <-- arrow trans
                
(S * unit -> Prop) -> (A * S -> Prop) <-- specialize
*)
                  
(* ================================================================= *)
(** ** SP observations                                                *)
(* ================================================================= *)

Section ObservationSP.

  Variable S : Type.

  (** [sp]s do not collapse under nondeterminism. They only collapse when
      programs are reversible.

      TODO: Question: Is there a type that we can use to represent reversible
      definitions? *)

  (** Reachability relation for a deterministic [prog]: an initial state
      [s] reaches outcome [r] iff the computation converges to [ret r]. *)
  Definition obsRel {A} (m : prog S A)
    : Rel S (option (A * S)) :=
    fun s r => eutt eq (unOptionT (runStateT m s)) (ret r).

  (** The four SP transformers are readings of the reachability relation
      [obsRel] (no [ASPostArr]/[SPRecord]): ASP and DSLP come from
      [SPost.v], while DSP and ASLP are their conjunction/disjunction. *)
  Definition obsASP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := asp (obsRel m).
  Definition obsDSLP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := dslp (obsRel m).
  Definition obsDSP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := fun pre r => asp (obsRel m) pre r /\ dslp (obsRel m) pre r.
  Definition obsASLP {A} (m : prog S A)
    : (S -> Prop) -> option (A * S) -> Prop := fun pre r => asp (obsRel m) pre r \/ dslp (obsRel m) pre r.

  (* -------------------------------------------------------------- *)
  (** *** Theorem 3.7: Square inclusions                             *)
  (* -------------------------------------------------------------- *)

  Theorem obsDSP_sub_obsASP {A} (m : prog S A) pre r :
    obsDSP m pre r -> obsASP m pre r.
  Proof. intros [H _]. exact H. Qed.

  Theorem obsDSP_sub_obsDSLP {A} (m : prog S A) pre r :
    obsDSP m pre r -> obsDSLP m pre r.
  Proof. intros [_ H]. exact H. Qed.

  Theorem obsASP_sub_obsASLP {A} (m : prog S A) pre r :
    obsASP m pre r -> obsASLP m pre r.
  Proof. intro H. left. exact H. Qed.

  Theorem obsDSLP_sub_obsASLP {A} (m : prog S A) pre r :
    obsDSLP m pre r -> obsASLP m pre r.
  Proof. intro H. right. exact H. Qed.

  (* -------------------------------------------------------------- *)
  (** *** Characterizations (paper Definitions 3.5 and 3.6)          *)
  (* -------------------------------------------------------------- *)

  Corollary obsDSP_char {A} (m : prog S A) pre r :
    obsDSP m pre r <->
    (exists sigma, obsRel m sigma r) /\
    (forall sigma, obsRel m sigma r -> pre sigma).
  Proof.
    unfold obsDSP. symmetry. apply dsp_asp_dslp.
  Qed.

  Corollary obsASLP_char {A} (m : prog S A) pre r :
    obsASLP m pre r <->
    (exists sigma, pre sigma /\ obsRel m sigma r) \/
    ~ (exists sigma, obsRel m sigma r).
  Proof.
    unfold obsASLP. symmetry. apply aslp_asp_dslp.
  Qed.

  (* -------------------------------------------------------------- *)
  (** *** [ret] as the pure [Rel]-arrow                             *)
  (* -------------------------------------------------------------- *)

  (** [Rel] is an [Arrow] ([Arrow_Rel] in [Rel.v]) with
      [arr_pure f a b := f a = b] (the graph of [f]).  The *reachability*
      observation of [ret a] is exactly the pure arrow of [s |-> Some
      (a, s)] (return value [a], state unchanged): *)
  Lemma ret_run {A} (a : A) (sigma : S) :
    eutt eq (unOptionT (runStateT (ret a : prog S A) sigma)) (Ret (Some (a, sigma))).
  Proof. cbn. reflexivity. Qed.

  Lemma obsRel_ret_arr_pure {A} (a : A) :
    arrow_eq (obsRel (ret a)) (arr_pure (fun s : S => Some (a, s))).
  Proof.
    unfold arrow_eq, ArrowEq_Rel, Rel_eq. intros sigma r.
    unfold obsRel. rewrite ret_run. unfold arr_pure, Arrow_Rel; cbn.
    split.
    - intro H. apply eutt_inv_Ret in H. exact H.
    - intro H. subst r. reflexivity.
  Qed.

  (** [obsASP = asp (obsRel _)] is the *angelic reading*, of type
      [Rel (S -> Prop) (option (A * S))].  [obsASP (ret a)] is therefore
      [asp] applied to the pure arrow above — the direct image of [pre]
      under [s |-> Some (a, s)].  It is NOT itself an [arr_pure]: [asp]
      turns the function graph into an existential relation
      ([exists s, pre s /\ r = Some (a, s)]), which is not a function graph. *)
  Lemma obsASP_ret_asp_arr_pure {A} (a : A) (pre : S -> Prop) (r : option (A * S)) :
    obsASP (ret a) pre r <-> asp (arr_pure (fun s : S => Some (a, s))) pre r.
  Proof.
    unfold obsASP, asp.
    split; intros [sigma [Hpre Hrel]]; exists sigma; (split; [exact Hpre |]).
    - apply obsRel_ret_arr_pure. exact Hrel.
    - apply obsRel_ret_arr_pure. exact Hrel.
  Qed.

End ObservationSP.

Arguments obsRel {_} {_}.
Arguments obsASP {_} {_}.
Arguments obsASLP {_} {_}.
Arguments obsDSP {_} {_}.
Arguments obsDSLP {_} {_}.

(* ================================================================= *)
(** ** SP triples over the precondition-taking (arrow) observations    *)
(* ================================================================= *)

(** The SP observations [obsASP]/[obsDSLP]/[obsDSP]/[obsASLP] above are
    *arrows* — [Rel (S -> Prop) (option (A * S))]: they take a
    precondition [pre : S -> Prop] and return a postcondition predicate
    (ASP/DSLP and their conjunction/disjunction over [obsRel]).
    A triple compares [obs m pre] with [post] by inclusion.  Carrying the
    precondition as a genuine argument (rather than the point-based
    [eq (tt,s)] encoding) is what makes the contrapositive transformers
    and the [awp -| dslp] Galois connection hold. *)

Definition tripleSP {S A}
  (obs : prog S A -> (S -> Prop) -> option (A * S) -> Prop)
  (m : prog S A) (kind : approximationKind)
  (pre : S -> Prop) (post : option (A * S) -> Prop) : Prop :=
  match kind with
  | Over  => forall r, obs m pre r -> post r          (* sp(pre) ⊆ post *)
  | Under => forall r, post r -> obs m pre r          (* post ⊆ sp(pre) *)
  end.

(* -------------------------------------------------------------- *)
(** *** Examples                                                   *)
(* -------------------------------------------------------------- *)

Theorem progA_all_triple :
  tripleSP obsASP progA Over (fun _ => True)
    (fun r : option (unit * nat) =>
       match r with Some (_, s) => s >= 42 | None => False end).
Proof.
  unfold tripleSP, obsASP, asp. intros r [sigma [_ Hrel]].
  unfold obsRel in Hrel. rewrite (progA_run sigma) in Hrel.
  apply eutt_inv_Ret in Hrel. subst r. cbn. auto with arith.
Qed.

Theorem progA_42 :
  tripleSP obsASP progA Under (fun _ => True) (fun r => r = Some (tt, 42)).
Proof.
  unfold tripleSP. intros r Hr. subst r.
  unfold obsASP, asp. exists 0. split; [exact I |].
  unfold obsRel. apply progA_run.
Qed.

Definition example_state : prog (nat * nat * nat) unit :=
  s <- get ;;
  let '(x, y, _) := s in
  if Nat.even x then
    if negb (Nat.even y) then put (x, y, 42) else ret tt
  else ret tt.

Lemma example_run : forall x y z0,
  Nat.even x = true -> negb (Nat.even y) = true ->
  eutt eq (unOptionT (runStateT example_state (x, y, z0)))
          (Ret (Some (tt, (x, y, 42)))).
Proof.
  intros x y z0 Hx Hy. unfold example_state. cbn.
  setoid_rewrite bind_ret_l. cbn. rewrite Hx, Hy. cbn.
  repeat (setoid_rewrite bind_ret_l; cbn). reflexivity.
Qed.

Theorem example_incorrect_1 :
  tripleSP obsASP example_state Under
    (fun '(x, _, z) => z = 11)
    (fun r =>
       match r with
       | Some (tt, (x, y, z)) =>
           z = 42 /\ Nat.even x = true /\ negb (Nat.even y) = true
       | _ => False
       end).
Proof.
  unfold tripleSP. intros r Hpost.
  destruct r as [[u [[x y] z]] |]; [| contradiction]. destruct u.
  cbn in Hpost. destruct Hpost as [Hz [Hx Hy]]. subst z.
  unfold obsASP, asp. exists (x, y, 11). split; [reflexivity |].
  unfold obsRel. apply example_run; assumption.
Qed.

Section SPTaxonomy.

  Variable S : Type.

  (* ------------------------------------------------------------ *)
  (** *** Theorem 3.8: square implications (correctness side)      *)
  (* ------------------------------------------------------------ *)

  Theorem cc_aslp_implies_asp :
    forall A (m : prog S A) pre post,
      tripleSP obsASLP m Over pre post -> tripleSP obsASP m Over pre post.
  Proof.
    unfold tripleSP in *. intros A m pre post H r Hr.
    apply H. apply obsASP_sub_obsASLP. exact Hr.
  Qed.

  Theorem cc_aslp_implies_dslp :
    forall A (m : prog S A) pre post,
      tripleSP obsASLP m Over pre post -> tripleSP obsDSLP m Over pre post.
  Proof.
    unfold tripleSP in *. intros A m pre post H r Hr.
    apply H. apply obsDSLP_sub_obsASLP. exact Hr.
  Qed.

  Theorem cc_dslp_implies_dsp :
    forall A (m : prog S A) pre post,
      tripleSP obsDSLP m Over pre post -> tripleSP obsDSP m Over pre post.
  Proof.
    unfold tripleSP in *. intros A m pre post H r Hr.
    apply H. apply obsDSP_sub_obsDSLP. exact Hr.
  Qed.

  Theorem cc_asp_implies_dsp :
    forall A (m : prog S A) pre post,
      tripleSP obsASP m Over pre post -> tripleSP obsDSP m Over pre post.
  Proof.
    unfold tripleSP in *. intros A m pre post H r Hr.
    apply H. apply obsDSP_sub_obsASP. exact Hr.
  Qed.

  Theorem ii_dsp_implies_dslp :
    forall A (m : prog S A) pre post,
      tripleSP obsDSP m Under pre post -> tripleSP obsDSLP m Under pre post.
  Proof.
    unfold tripleSP in *. intros A m pre post H r Hpost.
    apply obsDSP_sub_obsDSLP. apply H. exact Hpost.
  Qed.

  (* ------------------------------------------------------------ *)
  (** *** Theorem 3.8: contrapositive transformers                 *)
  (*      (now provable — the precondition is a real argument)      *)
  (* ------------------------------------------------------------ *)

  Theorem ci_aslp_dsp_contrapositive :
    forall A (m : prog S A) pre post,
      tripleSP obsASLP m Over (fun s => ~ pre s) (fun r => ~ post r) ->
      tripleSP obsDSP m Under pre post.
  Proof.
    intros A m pre post H. unfold tripleSP, obsASLP, obsDSP, asp, dslp in *.
    intros r Hpost. split.
    - apply NNPP. intro Hnasp. apply (H r); [| exact Hpost].
      right. intros sigma Hrel Hpre. apply Hnasp. exists sigma. split; [exact Hpre | exact Hrel].
    - intros sigma Hrel. apply NNPP. intro Hnpre. apply (H r); [| exact Hpost].
      left. exists sigma. split; [exact Hnpre | exact Hrel].
  Qed.

  Theorem ci_aslp_dsp_contrapositive' :
    forall A (m : prog S A) pre post,
      tripleSP obsDSP m Under (fun s => ~ pre s) (fun r => ~ post r) ->
      tripleSP obsASLP m Over pre post.
  Proof.
    intros A m pre post H. unfold tripleSP, obsDSP, obsASLP, asp, dslp in *.
    intros r Hobsaslp. apply NNPP. intro Hnpost.
    destruct (H r Hnpost) as [[sigma [Hnpre Hrel]] Hall].
    destruct Hobsaslp as [[s' [Hpre' Hrel']] | Hdslp].
    - exact (Hall s' Hrel' Hpre').
    - exact (Hnpre (Hdslp sigma Hrel)).
  Qed.

  (* ------------------------------------------------------------ *)
  (** *** Galois connections                                       *)
  (* ------------------------------------------------------------ *)

  (** [asp -| dwlp]: [tripleWP obsDWLP _ Under] coincides with
      [tripleSP obsASP _ Over].  Both unfold to
      [forall s r, pre s -> obsRel m s r -> post r]. *)
  Theorem gc_asp_dwlp :
    forall A (m : prog S A) pre post,
      tripleWP obsDWLP m Under pre post <-> tripleSP obsASP m Over pre post.
  Proof.
    intros A m pre post. unfold tripleWP, tripleSP, obsASP, asp. split.
    - intros H r [sigma [Hpre Hrel]].
      specialize (H sigma Hpre). unfold obsDWLP in H. cbn [runStateT unOptionT] in H.
      unfold obsRel in Hrel. destruct (runStateT m sigma) as [o] eqn:E. cbn in H, Hrel.
      exact (H r Hrel).
    - intros H s Hpre. unfold obsDWLP. cbn [runStateT unOptionT].
      destruct (runStateT m s) as [o] eqn:E. intros r Hr.
      apply (H r). exists s. split; [exact Hpre |].
      unfold obsRel. rewrite E. cbn. exact Hr.
  Qed.

  Lemma obsAWP_unfold : forall A (m : prog S A) s post,
    unOptionT (runStateT (obsAWP m) s) post <->
    exists r, eutt eq (unOptionT (runStateT m s)) (ret r) /\ post r.
  Proof.
    intros. unfold obsAWP. cbn [runStateT unOptionT].
    destruct (runStateT m s) as [o]. cbn. reflexivity.
  Qed.

  (** [awp -| dslp] (Zhang & Kaminski, OOPSLA 2022), relational form. *)
  Theorem gc_awp_dslp :
    forall A (m : prog S A) (pre : S -> Prop) (post : option (A * S) -> Prop),
      tripleWP obsAWP m Over pre post
      <->
      (forall r s, eutt eq (unOptionT (runStateT m s)) (ret r) -> post r -> pre s).
  Proof.
    intros A m pre post. unfold tripleWP. split.
    - intros HL r s Hreach Hpost. apply HL. apply obsAWP_unfold.
      exists r. split; assumption.
    - intros HR s Hawp. apply obsAWP_unfold in Hawp.
      destruct Hawp as [r [Hreach Hpost]]. exact (HR r s Hreach Hpost).
  Qed.

  (** [awp -| dslp], fully triple-based: now provable since [obsDSLP] is
      the precondition-taking arrow. *)
  Theorem gc_awp_dslp_triple :
    forall A (m : prog S A) pre post,
      tripleWP obsAWP m Over pre post <-> tripleSP obsDSLP m Under pre post.
  Proof.
    intros A m pre post. unfold tripleSP, obsDSLP, dslp. rewrite gc_awp_dslp. split.
    - intros H r Hpost sigma Hrel. apply (H r sigma Hrel Hpost).
    - intros H r s Hrel Hpost. apply (H r Hpost s Hrel).
  Qed.

End SPTaxonomy.

Section MonadMorphismLaws.
  Variable S : Type.

  Lemma obsDWP_ret {A} (a : A) post s0 :
    unOptionT (runStateT (obsDWP (ret a)) s0) post <->
      unOptionT (runStateT (Incorrectness.Taxonomy.WP.retP A a) s0) post.
  Admitted.

End MonadMorphismLaws.
