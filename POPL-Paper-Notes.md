### Rethinking Triples

1. It is not possible to define over-approximate WP triples the same way as in F*.
```ocaml
(* PREVIOUS WAY *)
Definition PureWP A := (A -> Prop) -> Prop.
Definition ProgWP A := stateT S (optionT PureWP) A.

pp2wp pre post := mkStateT (fun s0 => mkOptionT (fun p => pre s0 /\ (forall r, post r -> p r))).

ordProgWP m1 m2 := forall s p, unOptionT (runStateT m1 s) p -> unOptionT (runStateT m2 s) p.

tripleWP obs m Under pre post := ordProgWP (pp2wp pre post) (obs m).
tripleWP obs m Over pre post := ordProgWP (obs m) (pp2wp pre post).
```
**Under (works)**:
$$(\forall s. pre (s) \implies wp(post)(s)) \iff (\forall s, p. (pre (s) \land post \leq p) \implies wp(p)(s))$$
```ocaml
Theorem dwlp {A} :
    forall (m : nditprog S A) pre post,
      (forall s, pre s -> unOptionT (runStateT (obsDWLP m) s) post) <->
      (forall s p, (pre s /\ (forall r, post r -> p r)) -> unOptionT (runStateT (obsDWLP m) s) p).
```
Definitional equivalence proof given in the TripleDefinitions section of @NonDetItObservation.v. There are proofs for all the weakest precondition predicate transformers. 

**Over (breaks)**: (maybe use a co-Yoneda - like exists p, p <= post /\ (forall s, wp(p)(s) ==> pre s)) - duality of above? maybe look in SPost.v or somewhere in repo?
$$(\forall s. wp(post)(s) \implies pre(s)) \implies (\forall s, p. wp(p)(s) \implies (pre (s) \land post \leq p))$$
This direction does not work for all programs, pre, and post with a counterexample in @NonDetItObservation.v. 
```ocaml
~ (forall (m : nditprog nat unit) (pre : nat -> Prop)
                (post : option (unit * nat) -> Prop),
           (forall s, unOptionT (runStateT (obsAWP m) s) post -> pre s) ->
           (forall s p, unOptionT (runStateT (obsAWP m) s) p ->
                        (pre s /\ (forall r, post r -> p r)))).
```
Consider the program `return ()`, precondition `fun _ => True`, and postcondition `post := {Some (tt,1)}`. For `awp`, `unOptionT (runStateT (obsAWP (ret tt) s) post == exists r, outcomes (Some r) /\ post r`, so `r == {Some (tt,1)}`. The left implication is true, as its conclusion is true. However, for `p := {Some (tt,0)}`, the right implication does not hold, as the antecedent is true but $post \nleq p$. 
The opposite direction does work (also proved in @NonDetItObservation.v). 
```ocaml
forall (m : nditprog S A) pre post,
      (forall s p, unOptionT (runStateT (obsAWP m) s) p -> (pre s /\ (forall r, post r -> p r))) ->
      (forall s, unOptionT (runStateT (obsAWP m) s) post -> pre s).
```
There are similar proofs for all the weakest precondition predicate transformers.

Since these two definitions are not equivalent, this breaks proofs related to the partial incorrectness Galois connection between $awp$ and $dslp$.
![[Screenshot 2026-06-15 at 12.51.17.png]]
So, instead, we directly compare `pre` to the computed WP, as follows:
```ocaml
Definition tripleWP {S A}
  (obs : nditprog S A -> ProgWP S A)
  (prog : nditprog S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
    match kind with
    | Under =>
        forall s, pre s -> unOptionT (runStateT (obs prog) s) post
    | Over =>
        forall s, unOptionT (runStateT (obs prog) s) post -> pre s
    end.
```
This is actually what Loom does - additionally, it proves that the "spec-as-element" encoding and the direct encoding coincide for under-approximate triples.
```ocaml
def triple (pre : l) (c : m α) (post : α -> l) : Prop := pre ≤ wp c post

noncomputable
def spec (pre : l) (post : α -> l) : Cont l α := 
  fun p => pre ⊓ ⌜post ≤ p⌝

lemma triple_spec (pre : l) (c : m α) (post : α -> l) :
  spec pre post <= wp c <-> triple pre c post := by
    constructor
    { intro h; unfold triple
      specialize h post; apply le_trans'; apply h
      unfold spec; simp [trueE] }
    intro t p; unfold spec
    by_cases h: post ≤ p
    { apply inf_le_of_left_le; apply le_trans; apply t
      solve_by_elim [Cont.monotone_lift (x := c)] }
    have : (post ≤ p) = False := by simp [h]
    simp [this, falseE]
end
```
TODO: use something neutral (subset/superset) instead of under/over

2. It is not possible to define SP triples the same way as in F* OR by simply comparing `post` to the computed SP.
```ocaml
(* PREVIOUS WAY *)
Definition PureSP (A : Type) : Type := Prop -> A -> Prop.
Definition ProgSP (S A : Type) : Type := stateT S (optionT PureSP) A.

pp2sp pre post := mkStateT (fun s0 => @mkOptionT PureSP _ (fun p r => p /\ (pre s0 -> post r))).

ordProgWP m1 m2 := forall s p r, unOptionT (runStateT m1 s) p r -> unOptionT (runStateT m2 s) p r.

Definition obsASP {S A} (m : nditprog S A) : ProgSP S A :=
    mkStateT (fun s => @mkOptionT PureSP _ (fun p r => p /\ obsRel m (tt, s) r)).

tripleSP obs m Under pre post := ordProgSP (pp2wp pre post) (obs m).
tripleSP obs m Over pre post := ordProgSP (obs m) (pp2wp pre post).
```
However, this runs into the same issue as the naive formalization of `tripleWP`, where the under-approximation over all predicates is not definitionally equivalent to the appropriate under-approximation. But, we cannot fix `tripleSP` the same way that we fixed `tripleWP`, as follows:
```ocaml
Definition tripleSP {S A}
  (obs : nditprog S A -> ProgSP S A)
  (prog : nditprog S A)
  (kind:approximationKind)
  (pre : S -> Prop)
  (post : option (A * S) -> Prop)
  : Prop
  :=
    match kind with
    | Over =>
        forall s r, unOptionT (runStateT (obs prog) s) (pre s) r -> post r
    | Under =>
        forall s r, post r -> unOptionT (runStateT (obs prog) s) (pre s) r
    end.
```
The Over side is correct, as it unfolds to: $$\forall s, r. pre (s) \land R(s,r) \implies post (r)$$
However, the Under side unfolds to: $$\forall s, r. post(r) \implies (pre (s) \land R (s, r))$$
which forces every state in `post` to be reachable from *every* state AND `pre` to hold everywhere. The **actual** under-approximate triple is as follows:
$$\forall r, post(r) \implies (\exists s. pre(s) \land R(s,r))$$
This brings us to the current (simplified using `WPred`) formalization:
```ocaml
Definition Pred (A B : Type) : Type := A -> B -> Prop.
Definition obsRel {A} (m : nditprog S A) : Pred S (option (A * S)) :=
fun s r =>
  match r with
  | Some (a, s') => unOptionT (unOptionT (runStateT m s)) (Some (Some (a, s')))
  | None => unOptionT (unOptionT (runStateT m s)) (Some None)

Definition obsASP {A} (m : nditprog S A) := fun pre b => exists a, pre a /\ obsRel m a b
Definition obsDSLP {A} (m : nditprog S A) := fun pre b => forall a, obsRel m a b -> pre a.
Definition obsDSP {A} (m : nditprog S A) := fun pre b => asp (obsRel m) pre b /\ dslp R pre b.
Definition obsASLP {A} (m : nditprog S A) := fun pre b => asp (obsRel m) pre b \/ dslp (obsRel m) pre b.
  
Definition tripleSP {S A}
  (obs : nditprog S A -> (S -> Prop) -> option (A * S) -> Prop)
  (m : nditprog S A)
  (kind:approximationKind)
  (pre : S -> Prop) 
  (post : option (A * S) -> Prop)
  : Prop :=
    match kind with
    | Over => forall r, obs prog pre r -> post r
    | Under => forall r, post r -> obs prog pre r
    end.
```
For `asp`, the Over side unfolds to:
$$\forall r. (\exists s. pre(s) \land R(s,r)) \implies post(r)$$
which is equivalent to the prior formalization, and, therefore, correct.
For `asp`, the Under side unfolds to:
$$\forall r. post (r) \implies (\exists s. pre(s) \land R(s,r))$$
which is the correct under-approximate triple.

3. Loom already started thinking about strongest postcondition, but using the adjunction $sp \dashv wp$
Loom defines `sp` as the canonical left adjoint of `wp` using the Galois connection: $\forall pre, post. asp(pre) \leq post \iff pre \leq dwlp(post)$
TODO: is it difficult to get this sInf and sSup? some Classical axioms? could they prove the tripleSP we have as a theorem?
```ocaml
def sp (x : m α) (pre : l) : α -> l := (sInf fun post => pre <= wp x post)

lemma le_wp_sp_le (x : m α) [LawfulMonad m] [MAlgDet m l] :
  post ≠ ⊤ -> (sp x pre <= post -> pre <= wp x post) := by
    intro pne
    by_cases ex: Nonempty (Set.Elem fun post ↦ pre ≤ wp x post)
    { have : pre <= wp x (sp x pre) := by {
    unfold sp; simp [sInf]; rw [@wp_iInf]
    revert ex; simp [Set.Elem, Set.Mem, Membership.mem] }
    solve_by_elim [wp_cons, le_trans] }
    rw [@Set.not_nonempty_iff_eq_empty'] at ex
    simp [sp, ex, *]

lemma sp_le_le_wp (x : m α) :
  (pre <= wp x post -> sp x pre <= post) := by
    intro a; --refine inf_le_of_left_le ?_
    exact CompleteSemilatticeInf.sInf_le (fun post ↦ pre ≤ wp x post) post a
```
However, one direction (le_wp_sp_le) needs MAlgDet (so wp preserves ⨅, via wp_iInf) and a post ≠ ⊤ side condition. If `wp = dwlp`, then `sp = asp` and they would not need these side conditions (proven in @Loom/MonadAlgebras/WP/ScratchLiberalSP.lean).
However, they do not take it to the triple level, as follows:
```ocaml
def tripleSP (pre : l) (c : m α) (post : α -> l) : Prop := sp c pre <= post
```
This is only a valid adjunction for `dwlp` to `asp`. To get the other strongest postcondition predicate transformers, one would:
- use the incorrectness Galois connection $awp \dashv dslp$
- use $dsp = asp \land dslp$ and $aslp = asp \lor dslp$
If we instantiate `wp = awp` and `sp = asp`, then:
```ocaml
def dslp (x : m α) (b : l) : α -> l := sSup {c | wp x c <= b}
def dsp (x : m α) (b : l) : α -> l := fun τ => sp x b τ ⊓ dslp x b τ
def aslp (x : m α) (b : l) : α -> l := fun τ => sp x b τ ⊔ dslp x b τ
```
Benefits:
- defining SP as adjoint gives Galois connection by construction (vs. defining the SP transformers operationally and proving the Galois connection)
Caveats:
- no way to construct this using monad algebra transformers (this is reliant on `Cont l`)

4. Using these triple definitions, we can prove all of the arrows in the following diagram in @NonDetItObservation.v.![[Screenshot 2026-06-16 at 15.04.52.png]]

5. We also have the following proofs of soundness w.r.t `return` and `bind` in @NonDetItObservation.v. The only predicate transformers that do not follow these laws are `obsDSP` and `obASLP`, because they are defined as the meet/join of `asp` and `dslp`. 
Return WP:
```ocaml
Lemma tripleWP_ret_Under {S A} (a : A) (pre : S -> Prop) post :
  tripleWP obs(DWP/DWLP/AWP/AWLP) (ret a) Under pre post <-> (forall s, pre s -> post (Some (a, s))). 
  
(* unOptionT (runStateT (obs (ret a)) s) post = post (Some (a, s)) - TODO: put this in proof above *)
(* on the RHS: return that will give weakest precondition predicate transformer monad *)
  
Lemma tripleWP_ret_Over {S A} (a : A) (pre : S -> Prop) post :
  tripleWP obs(DWP/DWLP/AWP/AWLP) (ret a) Over pre post <-> (forall s, post (Some (a, s)) -> pre s).
```
 From state `s`, `ret a` has the single converging outcome `Some (a, s)`, so every WP observation collapses to `post (Some (a,s))`. 
 
 Return SP:
 ```ocaml
 Lemma tripleSP_ret_Over {S A} (a : A) (pre : S -> Prop) post :
  tripleSP obsASP (ret a) Over pre post <-> (forall s, pre s -> post (Some (a, s))).
  
Lemma tripleSP_ret_Under {S A} (a : A) (pre : S -> Prop) post :
  tripleSP obsASP (ret a) Under pre post <->
  (forall r, post r -> exists s, pre s /\ r = Some (a, s)).
 ```
From state `s`, `ret a` has the single converging outcome `Some (a, s)`, so `obsRel (ret a) s r <-> r = Some (a, s)`.

Bind:
```ocaml
Theorem tripleWP_bind {S A B} (x : nditprog S A) (f : A -> nditprog S B) kind pre post :
  tripleWP obs(DWP/DWLP/AWP/AWLP) (x >>= f) kind pre post <->
  tripleWP obs(DWP/DWLP/AWP/AWLP) x kind pre
    (fun rx => match rx with
               | Some (a, s') => unOptionT (runStateT (obs(DWP/DWLP/AWP/AWLP) (f a)) s') post
               | None => post None
               end).
               
Theorem tripleSP_seq {S A B} (x : nditprog S A) (f : A -> nditprog S B)
  (pre : S -> Prop) (mid : option (A * S) -> Prop) (post : option (B * S) -> Prop) :
  tripleSP obsASP x Over pre mid ->
  (forall a s', mid (Some (a, s')) -> tripleSP obsASP (f a) Over (eq s') post) ->
  (mid None -> post None) ->
  tripleSP obsASP (x >>= f) Over pre post.
```
6. What would need to change if you removed / added effects?
TODO - you would need to reprove a lot of things, but Claude is pretty good at it :)
TODO: Maybe we just consider this subset? But we might want to be more flexible with the specification monad...
a. how much can we throw away before things get weird?
b. maybe focus on getting rid of the effects that cause collapses in Taxonomy paper
c. reversible programs - effect?
DM4All did not have a general recipe for stacking theta monad morphisms
- DM4Free has some insight
- Loom has some insight - but restricted to continuation monad
	- check if they gain as much as DM4Free
	- do more than DM4Free, since partial / total / liberal get interpreted
	- our way: need to start with a theta and apply monad transformers - Loom does it in more modular way

6. How did Loom represent incorrectness? Why is this wrong?
This is how Loom claims to represent incorrectness:
```ocaml
open TotalCorrectness AngelicChoice (* using awp for triple correctness *)

bdef progloom returns (u: Unit)
  require balance > 0
  ensures False do
  let mut amount ← pick Nat
  if amount > balance then
    throw "Insufficient funds"
  else
    balance := balance - amount
  return
```
Translated into Rocq in our framework:
```ocaml
Definition progloom : nditprog nat unit :=
    amount  <- pickP ;;
    balance <- get ;;
    if Nat.ltb balance amount then raise tt else put (balance - amount).
    
Theorem progloom_triple :
    tripleWP obsAWP progloom Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
```
So, $pre \subseteq awp(post)$ is stating that **the throw is reachable from every balance > 0**.
Compare this to the actual incorrectness triple:
```ocaml
Theorem progloom_triple_asp :
	tripleSP obsASP progloom Over
	  (fun balance => balance > 0)
	  (fun r => match r with Some (tt, _) => False | None => True end).
```
So, $post \subseteq asp(pre)$ is stating that **the throw is reachable from some balance > 0**.
We see that `progloom_triple` is strictly stronger. They coincide for `progloom`, but if you change `progloom` to only throwing an exception when `Nat.even balance` (or anything that is not reachable from every `balance > 0`), then their triple fails. This contradicts their claim for being able to *prove* that an exception is thrown for a program.

"In such a case, it would be nice to prove (in the sense of program logics for under-approximate reasoning [82, 113]) that the exception at line 10 may be thrown. To achieve this, we instruct Loom to use angelic non-determinism and treat exceptions as “success” (the exact mechanism will be shown in Sec. 4). With this semantics, we will try to prove False post-condition. Intuitively, verification of such goal can only succeed if an exception is thrown, because, in this case, the VC will ignore any postcondition and will just return True."

```ocaml
Definition progloom_harder : nditprog nat unit :=
    amount  <- pickP ;;
    balance <- get ;;
    if Nat.even balance then raise tt else put (balance - amount).
    
Theorem progloom_triple_harder :
    ~ (tripleWP obsAWP progloom_harder Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end)).
      
Theorem progloom_triple_asp_harder :
    tripleSP obsASP progloom_harder Under
      (fun balance => balance > 0)
      (fun r => match r with Some (tt, _) => False | None => True end).
```

TODO priorities:
- co-Yoneda characterization for failing Over?
- ret / bind for triples **
- starting to write ** (focus on the main definitions + contributions + high-level story)
	- prepare contributions + high-level story draft for Thursday meeting w Catalin