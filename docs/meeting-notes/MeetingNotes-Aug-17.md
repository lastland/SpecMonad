We represent nondeterministic, divergent stateful programs as the following type: `nddprog A := S -> option (A * S) -> Prop`, where `None` represents divergence and the arrow to `Prop` represents nondeterminism. In the Taxonomy paper, the sppts have the type: `(S -> Prop) -> (A * S) -> Prop`. So that our predicate transformers form a monad, we restrict our focus to a smaller class of strongest postcondition predicate transformers.

In Back and Wright's, "Refinement Calculus: A Systematic Introduction", they introduce homomorphism properties of predicate transformers other than just monotonicity. The main classes of predicate transformers are (for `w : (S -> Prop) -> (A * S) -> Prop`):
- *strict*: if they preserve bottom
 `forall r, ~ w (fun _ => False) r`
- *terminating*: if they preserve top
 `forall r, w (fun _ => True) r`
- *conjunctive*: if they preserve *nonempty* meets of predicates
```ocaml
forall r,
w (fun s => q1 s /\ q2 s /\ ...) r <-> 
(w (fun s => q1 s) r) /\ (w (fun s => q2 s) r) /\ ...
```
- *disjunctive*: if they preserve *nonempty* joins of predicates
```ocaml
forall r,
w (fun s => q1 s \/ q2 s \/ ...) r <->
(w (fun s => q1 s) r) \/ (w (fun s => q2 s) r) \/ ...
```
Furthermore, an *universally conjunctive* predicate transformer preserves arbitrary meets (*terminating* + *conjunctive*). A *universally disjunctive* predicate transformer preserves arbitrary joins (*strict + disjunctive*). 

**COMMENT: use Inhabited typeclass for Conjunctive/Disjunctive?**
Yes, see below.

We formalize these classes as follows for `ProgSP A := (S -> Prop) -> (A * S) -> Prop`:
```ocaml
Definition StrictProg {A} (w : ProgSP A) : Prop :=
 forall r, ~ w (fun _ => False) r.

Definition TerminatingProg {A} (w : ProgSP A) : Prop :=
 forall r, w (fun _ => True) r.

Definition ConjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type), inhabited I -> 
 forall (p : I -> (S -> Prop)) r,
  w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type), inhabited I -> 
 forall (p : I -> (S -> Prop)) r,
  w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
```

**COMMENT: check in associativity proof to make sure that infinitary is necessary / explain why it is necessary**

The monad laws are polymorphic on the intermediate type `A`. In order for the associativity of `bind` to work, the predicate transformer must be additive at every arity the binds can generate. For finite `A` and finite `S`, one could consider finite meets and joins. Consider if one restricted the definition to finite index set `I`. 
```ocaml
Definition FinDisjunctiveProg {A} (w : ProgSP A) : Prop :=
     (forall r, ~ w (fun _ => False) r)                              (* empty join *)
  /\ (forall p q r, w (fun s => p s \/ q s) r <-> w p r \/ w q r).   (* binary join *)
```
We get the following counterexample:
```ocaml
S := nat
A := nat
B := unit

Definition m : ProgSP nat :=
  fun pre r => exists s, pre s.

Definition k : nat -> ProgSP unit :=
  fun a => fun pre r => (exists s, pre s) /\ r = (tt, a).
  
Definition g : ProgSP unit :=
  fun pre r => forall n, exists s, s > n /\ pre s. (* pre is infinite *)
(* g is finitely disjunctive *)

pre := fun _ => True
r := (tt, 0)

(* LHS *)
bind (bind m k) (fun _ => g) pre r <->
g (fun _ => True) r <->
(* nat is infinite *) <->
True

(* RHS *)
bind m (fun a => bind (k a) (fun _ => g)) pre r <->
exists a, g (fun s1 => s1 = a) r <->
exists a, (* {a} is infinite *) <->
False
```

**COMMENT: monotonicity implies one of these directions - check which one**
```ocaml
Definition MonotoneProg {A} (w : ProgSP A) : Prop :=
  forall (p q : S -> Prop) (r : A * S),
    (forall s, p s -> q s) -> w p r -> w q r.
```

For disjunctive, the <-- direction:
```ocaml
Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type), inhabited I -> 
 forall (p : I -> (S -> Prop)) r,
  w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
```
Assume:
`forall (p q : S -> Prop) (r : A * S),`
    `(forall s, p s -> q s) -> w p r -> w q r`
`w (fun s => p i0 s) r`

So, since `forall s, (fun s => p i0 s) s -> (fun s => exists i, p i s) s`, we get `w (fun s => exists i, p i s) r`. 

For conjunctive, the --> direction:
```ocaml
Definition ConjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type), inhabited I -> 
 forall (p : I -> (S -> Prop)) r,
  w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.
```
Assume:
Assume:
`forall (p q : S -> Prop) (r : A * S),`
    `(forall s, p s -> q s) -> w p r -> w q r`
`w (fun s => forall i, p i s) r`
`i`

So, since `forall s, (fun s => forall i', p i' s) s -> (fun s => p i s)`, we get `w (fun s => p i s) r`. 

**COMMENT: exists could trigger on different i's inside and outside?**
```ocaml
Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type), inhabited I -> 
 forall (p : I -> (S -> Prop)) r,
  w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
```
Yes, and this is what makes this predicate transformer quite constrained. The <-- comes from monotonicity, but --> states that the verdict that the predicate transformer `w` makes, which we see can be triggered by different `i`'s depending on `s`, must actually be triggered by one particular `i` regardless of the state. Consider the family of singleton preconditions:
```ocaml
p i := (fun s => s = i)

LHS: w (fun s => exists i, s = i) r
(* each state is witnessed by itself *)
RHS: exists i, w (fun s => s = i) r
(* state must be equal to singular witness *)
```

**TODO: geometric logic - arbitrary disjunction + finite conjunction**
Need to look into this...

**TODO: look at book for practical examples? case studies, maybe from dwlp?**
Refinement Calculus book does not provide specific examples. Can look for more case studies online / think about converting dwlp examples to asp examples...

We examine $asp$ to see what classes it falls into (definition from "Taxonomy..."):
$$asp[p](b) = \lambda \tau. \bigvee_{\sigma \in [p]^{-1}(\tau)} b(\sigma)$$
- strict: for `b = (fun _ => False)`, `asp[p](b) = False` $\checkmark$
- terminating: when $[p]^{-1}(\tau) = \emptyset$, for `b = (fun _ => True)`, `asp[p](b) != True` `X`
- conjunctive: `X`
```ocaml
(* consider that r has two states s1 and s2 that lead to it *)
asp[p](fun s => q1 s /\ q2 s)(r) == (q1 s1 /\ q2 s1) \/ (q1 s2 /\ q2 s2)
!= 
asp[p](fun s => q1 s)(r) /\ asp[p](fun s => q2 s)(r) ==
  (q1 s1 \/ q1 s2) /\ (q2 s1 \/ q2 s2)
```
- disjunctive: $\checkmark$ 
So, we consider *strict* + *disjunctive* (aka join-preserving) strongest postcondition predicate transformers.
```ocaml
Definition JoinPreservingProg {A} (w : ProgSP A) : Prop :=
  StrictProg S w /\ DisjunctiveProg S w.
```
Single-decomposition version:
```ocaml
Definition SingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) r,
      w pre r <-> exists s0, pre s0 /\ w (fun s => s = s0) r.
```
Again, these are equivalent definitions:
```ocaml
Theorem join_iff_singleton_prog {A} (w : ProgSP A) :
    JoinPreservingProg w <-> SingletonProg w.
```
We define join-preserving sppts as a refinement:
```ocaml
Definition ASPProgSP (A : Type) : Type := { w : ProgSP A | SingletonProg w }.
```
We define `ret` and `bind` from the Taxonomy definition of $asp$. $$asp[p](b) = \lambda \tau. \bigvee_{\sigma \in [p]^{-1}(\tau)} b(\sigma)$$Given an arbitrary precondition ($b$ / `pre`) and arbitrary final state ($\tau$), there needs to exist some initial state that satisfies $b$ and leads to $\tau$. Note that our predicate transformers take a precondition and final *result*, which is the final value of the computation + the final state. The behavior of `ret` requires that the final value be the value `v` passed into `ret`. Additionally, `ret` requires that there be no modification of the state, so the final state is simply the initial state. Since the reachability relation of states is reflexive, the initial state trivially leads to the (same) final state. We represent this as follows:
```ocaml
#[program] Definition retASPProg {A} (v : A) :=
  fun pre (r : A * S) => exists s0, pre s0 /\ r = (v, s0).
```
For `bind`, we use the $asp$ definition for sequenced programs. By definition, `[p1 ; p2]`$^{-1}(\tau)$ == (`[p2]` $\circ$ `[p1]` )$^{-1}$($\tau$) == `[p1]`$^{-1}$ (`[p2]`$^{-1}$($\tau$)). So, there needs to exist some initial state that satisfies $b$ and leads to $\tau$ via some intermediate state after the computation of `p1`. The behavior of `bind` requires that the intermediate value of the first computation `m` be passed to a function `k` that executes the second computation. So, we require that such an intermediate value exists to pass into `k` (`exists a, k a ...`) AND that there exists a corresponding intermediate state `s1` that satisfies `m pre (a, s1)` (which means there exists an initial state satisfying `pre` that leads to `(a, s1)` after the computation of `m`) and leads to `r`. 
```ocaml
#[program] Definition bindASPProg {A B} (m : ASPProgSP) (k : A -> ASPProgSP B) :=
  fun pre r => exists a, k a (fun s1 => m pre (a, s1)) r.
```
We show that the monad laws hold:
```ocaml
#[global]
    Instance Monad__SingletonProgSP : Monad ASPProgSP :=
    {| ret := fun _ => @retASPProg _ ;
      bind := fun _ _ => @bindASPProg _ _ |}.
#[global] Instance Eq1__ProgASP : Eq1 ASPProgSP :=
    fun A m n => forall pre r, getProgASP m pre r <-> getProgASP n pre r.
#[global] Instance Eq1Equivalence__ASPProgSP
    : @Eq1Equivalence ASPProgSP _ Eq1__ProgASP.
#[global] Instance MonadLawsE__ProgASP
    : @MonadLawsE ASPProgSP Eq1__ProgASP _.
```
Using this monad, we define our effect observation, as follows:
```ocaml
#[program] Definition obsASP {A} (m : nddprog S A) : ASPProgSP S A :=
    fun pre r => exists s, pre s /\ unOptionT (runStateT m s) (Some r).
```
And, we prove that it is a monad morphism:
```ocaml
Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : nddprog S A)) (ret a).
Theorem obsASP_bind {A B} (x : nddprog S A) (f : A -> nddprogS B) :
  eq1 (obsASP (x >>= f)) (obsASP x >>= (fun a => obsASP (f a))).
``` 
This specification monad is the *angelic* version, so it is only appropriate when defining the triple based on ASP:
```ocaml
Inductive approxKind := | Under | Over.

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
```
We can successfully verify all of the examples that use `tripleSP obsASP` in the old file - both `Under` and `Over`.

We, again, examine $dslp$ to see what classes it falls into (definition from "Taxonomy..."):
$$dslp[p](b) = \lambda \tau. \bigwedge_{\sigma \in [p]^{-1}(\tau)} b(\sigma)$$
- strict: when $[p]^{-1}(\tau) = \emptyset$, for `b = (fun _ => False), dslp[p](b) != False X`
- terminating: for `b = (fun _ => True)`, `dslp[p](b) = True` $\checkmark$
- conjunctive: $\checkmark$ 
- disjunctive: `X`
```ocaml
(* consider that r has two states s1 and s2 that lead to it *)
dslp[p](fun s => q1 s \/ q2 s)(r) == (q1 s1 \/ q2 s1) /\ (q1 s2 \/ q2 s2)
!= 
dslp[p](fun s => q1 s)(r) \/ dslp[p](fun s => q2 s)(r) ==
  (q1 s1 /\ q1 s2) \/ (q2 s1 /\ q2 s2)
```
So, we consider *terminating* + *conjunctive* (aka meet-preserving) strongest postcondition predicate transformers.
```ocaml
Definition MeetPreservingProg {A} (w : ProgSP A) : Prop :=
	TerminatingProg S w /\ ConjunctiveProg S w.
```
Single-decomposition version:
```ocaml
Definition MSingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : A * S),
      w pre r <-> forall s0, ~ pre s0 -> w (fun s => s <> s0) r.
```
Again, these are equivalent definitions:
```ocaml
Theorem meet_iff_msingleton_prog {A} (w : ProgSP A) :
    MeetPreservingProg w <-> MSingletonProg w.
```
We define meet-preserving sppts as a refinement:
```ocaml
Definition DSLPProgSP (A : Type) : Type := { w : ProgSP A | MSingletonProg w }.
```
We define `ret` and `bind` from the Taxonomy definition of $dslp$. $$dslp[p](b) = \lambda \tau. \bigwedge_{\sigma \in [p]^{-1}(\tau)} b(\sigma)$$
Given an arbitrary precondition ($b$ / `pre`) and arbitrary final state ($\tau$), all initial states that lead to $\tau$ need to satisfy $b$. Additionally, $\tau$ can be unreachable. The behavior of `ret` requires that the final value be the value `v` passed into `ret`. Additionally, `ret` requires that there be no modification of the state, so the final state is simply the initial state. Since the reachability relation of states is reflexive, the initial state trivially leads to the (same) final state. We represent this as follows:
```ocaml
#[program] Definition retDSLPProg {A} (v : A) :=
  fun pre r => forall s0, r = (v, s0) -> pre s0.
```
For `bind`, we, again, consider the $dslp$ definition for sequenced programs. So, all initial states that lead to $\tau$ via some intermediate state after the computation of `p1` need to satisfy $b$ or $\tau$ is unreachable. So, we require that for all intermediate values that are passed into `k` (`forall a, k a ...`), all intermediate states `s1` that lead to `r` need to satisfy `m pre (a, s1)` (which means all initial states that lead to `(a, s1)` after the computation of `m` need to satisfy `pre` OR `s1` can be unreachable) OR `r` can be unreachable. 
```ocaml
#[program] Definition bindDSLPProg {A B} (m : DSLPProgSP) (k : A -> DSLPProgSP B) :=
  fun pre r => forall a, k a (fun s1 => m pre (a, s1)) r.
```
The monad laws hold:
```ocaml
#[global]
    Instance Monad_DSLPProgSP : Monad DSLPProgSP :=
    {| ret := fun _ => @retDSLPProg _ ;
      bind := fun _ _ => @bindDSLPProg _ _ |}.
#[global] Instance Eq1__ProgDSLP : Eq1 DSLPProgSP :=
    fun A m n => forall pre r, getProgDSLP m pre r <-> getProgDSLP n pre r.
#[global] Instance Eq1Equivalence__DSLPProgSP
    : @Eq1Equivalence DSLPProgSP _ Eq1__ProgDSLP.
#[global] Instance MonadLawsE__ProgDSLP
    : @MonadLawsE DSLPProgSP Eq1__ProgDSLP _.
```
 Using this monad, we define our effect observation, as follows:
 ```ocaml
 #[program] Definition obsDSLP {A} (m : nditprog S A) : MSingletonProgSP S A :=
    fun pre r => forall s, unOptionT (unOptionT (runStateT m s)) (Some r) -> pre s.
 ```
 And, we prove that it is a monad morphism:
 ```ocaml
 Theorem obsDSLP_ret {A} (a : A) : eq1 (obsDSLP (ret a : nditprog S A)) (ret a).
 Theorem obsDSLP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsDSLP (x >>= f)) (obsDSLP x >>= (fun a => obsDSLP (f a))).
 ```
 This specification is the *demonic* version, so it is only appropriate when defining the triple based on DSLP:
 ```ocaml
 Inductive approxKind := | Under | Over.
 
 Definition tripleDSLP {S A}
    (prog : nditprog S A)
    (kind : approxKind)
    (pre : S -> Prop)
    (post : option (A * S) -> Prop)
    : Prop :=
    match kind with
    | Over => forall r, getProgMSP (obsDSLP prog) pre r -> post r
    | Under => forall r, post r -> getProgMSP (obsDSLP prog) pre r
    end.
 ```
 We can successfully verify all of the examples that use `tripleSP obsDSLP` in the old file - both `Under` and `Over`.

**COMMENT: can you have something that is both strict + terminating? can you have something that you don't know if it is strict + terminating? which of these properties is most important for the monad laws?**

Yes, you can have predicate transformers that are both strict and terminating. Strict and terminating just determine the edge-case behavior. For strongest postcondition predicate transformer, `(fun _ => True)` is the set of all initial states and `(fun _ => False)` is the empty set. Considering strict + terminating conjunctive predicate transformers gives the subclass of predicate transformers where `dsp` and `dslp` behave the same. Consider strict + terminating disjunctive predicate transformers gives the subclass of predicate transformers where `asp` and `aslp` behave the same. 

No, it is straightforward to probe if a predicate transformer is strict or terminating. Simply pass in the precondition `(fun _ => True)` or `(fun _ => False)` and check the verdict of the predicate transformer for all outcomes.

Each of the homomorphism properties fulfill a different role for the predicate transformer:
- strict (`forall r, ~ w (fun _ => False) r`):
	- needs to be true for $asp$ and $dsp$, since both $asp$ and $dsp$ require that the final state be reachable from `pre = (fun _ => False)`, which is a contradiction, so, necessarily, `~ w (fun _ => False) r`
- terminating (`forall r, w (fun _ => True) r`):
	- needs to be true for $aslp$ and $dslp$, since both $aslp$ and $dslp$ require that the final state be reachable from `pre = (fun _ => True)` OR be unreachable - since `pre` is vacuously true, `w (fun _ => True) r` holds for regardless of `r`, reachable or not
- disjunctive
	- necessary for associativity of bind
- conjunctive
	- necessary for associativity of bind

**COMMENT: what happens if you only have conjunctive / disjunctive (no terminating / strict)?**

I can't think of a scenario where one would have undefined behavior when passing in a precondition and result to a predicate transformer? Clarification?

We, again, examine $dsp$ to see what classes it falls into (definition from "Taxonomy..."):
$$dsp[p](b) = \lambda \tau. \bigwedge_{\sigma \in [p]^{-1}(\tau)} b(\sigma) \text{, if } [p]^{-1}(\tau) \neq \emptyset \text{, otherwise, }false$$
- strict: for `b = (fun _ => False)`, `dsp[p](b) = False` $\checkmark$
- terminating: when $[p]^{-1}(\tau) \neq \emptyset$, for `b = (fun _ => True)`,  `dsp[p](b) != True X`
- conjunctive: $\checkmark$ 
- disjunctive: `X`
```ocaml
(* consider that r has two states s1 and s2 that lead to it *)
dsp[p](fun s => q1 s \/ q2 s)(r) == (q1 s1 \/ q2 s1) /\ (q1 s2 \/ q2 s2)
!= 
dsp[p](fun s => q1 s)(r) \/ dsp[p](fun s => q2 s)(r) ==
  (q1 s1 /\ q1 s2) \/ (q2 s1 /\ q2 s2)
```
So, we consider *strict* + *positively conjunctive* strongest postcondition predicate transformers. 
 ```ocaml
Definition StrictPositivelyMeetPreservingProg {A} (w : ProgSP A) : Prop :=
    StrictProg S w /\ ConjunctiveProg S w.
 ```
 We define strict, positively meet-preserving sppts as a refinement:
 ```ocaml
 Definition DSPProgSP (A : Type) : Type :=
    { w : ProgSP A | StrictPositivelyMeetPreservingProg w }.
 ```
 We utilize the following characterization to define `ret` and `bind`: $$dsp[p](b) = asp[p](b) \cap dslp[p](b)$$
 Let us consider why this equality holds. For a final state to be in $dslp[p](b)$, it must be either unreachable OR strictly reachable from an initial state in $b$. For a final state to be in $asp[p](b)$, it must be reachable from an initial state in $b$. The conjunction of these gives us final states that are strictly reachable from an initial state in $b$. So, one can think of $dslp$ as the condition-checker and $asp$ as the reachability-checker. This informs the structure of our `ret` and `bind`.
 
 In the `ret` case, the conjunction of an `ASPProgSP` predicate transformer and a `DSLPProgSP` predicate transformer is trivially a `DSPProgSP` predicate transformer. We unfold the two definitions:
```ocaml
retASPProg {A} (a : A) := fun pre r => exists s0, pre s0 /\ r = (a, s0)
retDSLPProg {A} (a : A) := fun pre r => forall s0, r = (a, s0) -> pre s0.

retDSPProg {A} (a : A) := fun pre r =>
  (exists s0, pre s0 /\ r = (a, s0)) /\ (forall s0, r = (a, s0) -> pre s0) <-> 
  (exists s0, pre s0 /\ r = (a, s0))
```
We confirm that this predicate transformer is *strict* and *positively conjunctive* (aka a `DSPProgSP` predicate transformer).
- strict: for `b = (fun _ => False)`, `retDSPProg a b = False` for all `r` 
- conjunctive: $\checkmark$ 
So, we get:
```ocaml
#[program] Definition retDSPProg {A} (v : A) : DSPProgSP A :=
  fun pre a => retASPProg v pre a /\ retDSLPProg v pre a.
```
 
 In the `bind` case, it is *not* sufficient to simply take the conjunction of `bindASPProgSP` and `bindDSLPProgSP`, as follows: 
```ocaml
bindASPProg m k := fun pre r => exists a, k a (fun s0 => m pre (a, s0)) r
bindDSLPProg m k := fun pre r => forall a, k a (fun s0 => m pre (a, s0)) r

bindDSPProg m k := fun pre r =>
  (exists a, k a (fun s0 => m pre (a, s0)) r) /\ (forall a, k a (fun s0 => m pre (a, s0)) r) 
  <->
  (exists a, True) /\ (forall a, k a (fun s0 => m pre (a, s0)) r)
```
For `bind`, the $dsp$ definition of sequenced programs requires that all initial states that lead to $\tau$ via some intermediate state after the computation of `p1` need to satisfy $b$ and $\tau$ must be reachable. 
Consider that both `m` and `k a` are in $dsp$ form, this means that:
- `m pre (a, s0)` iff `(a, s0)` is reachable AND all initial states leading to it are in `pre` 
- `k a (fun s1 => m pre (a, s1)) r` iff `r` is reachable AND all intermediate states leading to it must be in `(fun s1 => m pre (a, s1))` (which means that `(a, s1)` must be reachable AND all initial states leading to it are in `pre`)
The first conjunct, `(exists a, True)` just tells us that the intermediate state space is inhabited, which is necessary for this threading. Let us consider `(forall a, k a (fun s0 => m pre (a, s0)) r)`. This is saying that for all `a`:
1. `r` is reachable
2. all intermediate states that reach `r` must be reachable from `m`
3. all initial states leading to the above intermediate states that reach `r` must be in `pre`
Let us remind ourselves what $dsp$ requires. $dsp$ requires that:
- `r` is reachable via some intermediate state
- that intermediate state must be strictly reachable by initial states in `pre` 
The first bug is in (1). $dsp$ does not require that *every* result `a` of `m` leads to `r`, just *some* result `a`. The second bug is in (2). $dsp$ does not require that *all* intermediate states leading to `r` must be reachable from `m`, just *some* intermediate state.  

We return to our previous intuition: a $dsp$ predicate transformer is the conjunction of a reachability-checker $asp$ predicate transformer and a condition-checker $dslp$ predicate transformer. Therefore, we consider a different strategy. 
1. Extract reachability-checker part of `m` and `k a` and bind them using `bindASPProg`
2. Extract condition-checker part of `m` and `k a` and bind them using `bindDSLPProg` 
3. Take the conjunction of these two binds

So, how do we do these things?
1. For an arbitrary `w : DSPProgSP A`, we construct the following `ASPProgSP A` predicate transformer:
```ocaml
(* w pre r means that r is reachable only from initial states in pre *)
#[program] Definition aspOf {A} (w : DSPProgSP A) : ASPProgSP A :=
fun pre r => 
  w (fun _ => True) r  
    (* r is reachable only from all initial states *) 
    (* aka r is reachable *)
    /\
  ~ w (fun s => ~ pre s) r 
    (* r is NOT reachable only from initial states outside of pre *)
    (* aka r is reachable from some initial state in pre OR unreachable *)

(* r is reachable from some state in pre = asp! *)
```
2. For an arbitrary `w : DSLPProgSP A`, we construct the following `DSLPProgSP A` predicate transformer:
```ocaml
(* w pre r means that r is reachable only from initial states in pre *)
#[program] Definition dslpOf {A} (w : DSPProgSP A) : DSLPProgSP A :=
fun pre r =>
  w pre r 
    (* r is reachable only from initial states in pre *)
    \/ 
  ~ w (fun _ => True) r 
    (* r is NOT reachable from all initial states *)
    (* aka r is unreachable *)

(* r is reachable only from initial states in pre OR r is unreachable = dslp! *)
```
3. Now, we take the conjunction of the `bindASPProg` of `aspOf m` and `aspOf (k a)` AND `bindDSLPProg` of `dslpOf m` and `dslpOf (k a)`
```ocaml
#[program] Definition bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) :=
  fun pre r => bindASPProg (aspOf m) (fun a => aspOf (k a)) /\ 
               bindDSLPProg (dslpOf m) (fun a => dslpOf (k a)).
```
The monad laws hold:
```ocaml
#[global]
    Instance Monad__DSPProgSP : Monad DSPProgSP :=
    {| ret := fun _ => @retDSPProg _ ;
      bind := fun _ _ => @bindDSPProg _ _ |}.
#[global] Instance Eq1__ProgDSP : Eq1 DSPProgSP :=
    fun A m n => forall pre r, getProgDSP m pre r <-> getProgDSP n pre r.
#[global] Instance Eq1Equivalence__DSPProgSP
    : @Eq1Equivalence DSPProgSP _ Eq1__ProgDSP.
#[global] Instance MonadLaws__ProgDSP
    : @MonadLawsE DSPProgSP Eq1__ProgDSP _.
```
Using this monad, we define our effect observation as follows:
```ocaml
#[program] Definition obsDSP {A} (m : nditprog S A) : DSPProgSP S A :=
    fun pre r => (obsASP m pre r) /\ (obsDSLP m pre r).
```
And, we prove that it is a monad morphism:
```ocaml
Theorem obsDSP_ret {A} (a : A) : eq1 (obsDSP (ret a : nditprog S A)) (ret a).
Theorem obsDSP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsDSP (x >>= f)) (obsDSP x >>= (fun a => obsDSP (f a))).
```
We use this to define the triple based on DSP:
```ocaml
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
```
We can successfully verify all of the examples that use `tripleSP obsDSP` in the old file - both `Under` and `Over`.

Similarly, we examine $aslp$ to see what classes it falls into (definition from "Taxonomy..."):
$$aslp[p](b) = \lambda \tau \bigvee_{\sigma \in [p]^{-1}(\tau)} b(\sigma), \text{ if } [p]^{-1}(\tau) \neq \emptyset \text{, otherwise, } true$$
- strict: when $[p]^{-1}(\tau) \neq \emptyset$, for `b = (fun _ => False)`, `aslp[p](b) != False` `X`
- terminating: for `b = (fun _ => True)`, `aslp[p](b) = True` $\checkmark$
- conjunctive: `X`
```ocaml
(* consider that r has two states s1 and s2 that lead to it *)
aslp[p](fun s => q1 s /\ q2 s)(r) == (q1 s1 /\ q2 s1) \/ (q1 s2 /\ q2 s2)
!= 
aslp[p](fun s => q1 s)(r) /\ aslp[p](fun s => q2 s)(r) ==
  (q1 s1 \/ q1 s2) /\ (q2 s1 \/ q2 s2)
```
- disjunctive: $\checkmark$ 
So, we consider *terminating* + *positively disjunctive* strongest postcondition predicate transformers.
```ocaml
Definition TerminatingPositivelyJoinPreservingProg {A} (w : ProgSP A) : Prop :=
	TerminatingProg S w /\ DisjunctiveProg S w.
```
We define terminating, positively join-preserving sppts as a refinement:
```ocaml
 Definition ASLPProgSP (A : Type) : Type :=
    { w : ProgSP A | TerminatingPositivelyJoinPreservingProg w }.
```
We utilize the following characterization to define `ret` and `bind` :
$$aslp[p](b) = asp[p](b) \cup dslp[p](b)$$
Let us consider why this equality holds. Let us consider why this equality holds. For a final state to be in $dslp[p](b)$, it must be either unreachable OR strictly reachable from an initial state in $b$. For a final state to be in $asp[p](b)$, it must be reachable from an initial state in $b$. This disjunction of these gives us final states that are reachable from some initial state in $b$ OR unreachable. So, in this case, $dslp$ and $asp$ fulfill opposite role. Here, $dslp$ allows unreachable final states to be included and $asp$ checks the condition that there must exist a path from an initial state to the final state. This, again, informs the structure of our `ret` and `bind`.

In the `ret` case, the disjunction of an `ASPProgSP` predicate transformer and a `DSLPProgSP` predicate transformer is trivially a `DSPProgSP` predicate transformer. 
```ocaml
#[program] Definition retASLPProg {A} (v : A) : ASLPProgSP A :=
  fun pre a => retASPProg v pre a \/ retDSLPProg v pre a.
```

In the bind case, we run into a similar problem by naively taking the disjunction of `bindASPProgSP` and `bindDSLPProgSP`, as follows:
```ocaml
bindASPProg m k := fun pre r => exists a, k a (fun s0 => m pre (a, s0)) r
bindDSLPProg m k := fun pre r => forall a, k a (fun s0 => m pre (a, s0)) r

bindDSPProg m k := fun pre r =>
  (exists a, k a (fun s0 => m pre (a, s0)) r) \/ (forall a, k a (fun s0 => m pre (a, s0)) r) 
  <->
  (exists a, True) -> (exists a, k a (fun s0 => m pre (a, s0)) r)
```
For `bind`, the $aslp$ definition of sequenced programs requires that there exist some initial state satisfying $b$ that leads to $\tau$ via some intermediate state after the computation of `p1` or that $\tau$ is unreachable. 
Consider that both `m` and `k a` are in $aslp$ form, this means that:
- `m pre (a, s0)` iff `(a, s0)` is unreachable OR there exists an initial state leading to it in `pre`
- `k a (fun s1 => m pre (a, s1)) r` iff `r` is unreachable OR there exists an intermediate state leading to it that must be in `(fun s1 => m pre (a, s1))` (which means that `(a, s1)` is unreachable OR there exists an initial state leading to it in `pre`)
Consider `(exists a, k a (fun s0 => m pre (a, s0)) r)`. This is saying that there exists `a` s.t. `r` is unreachable OR there exists an intermediate state `s0` reaching `r` that is either unreachable from `m` OR there exists an initial state reaching `s0` from `pre`.  However, this is not conditioned by the intermediate state space being inhabited. Consider an intermediate state `s1` that leads to `r` and is reachable solely from initial states outside of `pre`. This certainly does not satisfy `(exists a, k a (fun s0 => m pre (a, s0)) r)`, meaning that `bindASLPProg pre r` is false, but it does not rule out the possibility of another intermediate state fulfilling $aslp$'s condition of a path existing from `pre` to `r` via this other intermediate state. So, we see that our initial definition of `bindASLPProg` is incorrect.

`forall w pre r, w pre r <-> (aspOf w /\ dslpOf w) pre r`
`m` and `k a` 
TODO: ret and bind that doesn't use conjunction / disjunction?

We use the same procedure as for $dsp$:
1. For an arbitrary `w : ASLPProgSP A`, we construct the following `ASPProgSP A` predicate transformer:
```ocaml
(* w pre r means that r is reachable from some state in pre OR is unreachable *)
#[program] Definition aspOf {A} (w : ASLPProgSP A) : ASPProgSP A :=
fun pre r =>
  w pre r 
  (* r is reachable from some state in pre OR is unreachable *)
  /\
  ~ w (fun _ => False) r 
  (* r is NOT reachable from no initial state AND is NOT unreachable *)
  (* aka r is reachable from some initial state *)
  
(* r is reachable from some state in pre = asp! *)
```
2. For an arbitrary `w : ASLPProgSP A`, we construct the following `DSLPProgSP A` predicate transformer:
```ocaml
(* w pre r means that r is reachable from some state in pre OR is unreachable *)
#[program] Definition dslpOf {A} (w : ASLPProgSP A) : DSLPProgSP A :=
fun pre r =>
  w (fun _ => False) r 
  (* r is reachable from no initial state OR is unreachable *)
  (* aka r is unreachable *)
  \/ 
  ~ w (fun s => ~ pre s) r 
  (* r is NOT reachable from some state outside of pre AND is NOT unreachable *)
  (* aka r is reachable only from initial states in pre *)
  
(* r is reachable only from initial states in pre OR r is unreachable = dslp! *)
```
3. Now, we take the disjunction of the `bindASPProg` of `aspOf m` and `aspOf (k a)` AND `bindDSLPProg` of `dslpOf m` and `dslpOf (k a)`
```ocaml
#[program] Definition bindASLPProg {A B} (m : ASLPProgSP A) (k : A -> ASLPProgSP B) :=
  fun pre r => bindASPProg (aspOf m) (fun a => aspOf (k a)) \/ 
               bindDSLPProg (dslpOf m) (fun a => dslpOf (k a)).
```
The monad laws hold:
```ocaml
#[global]
    Instance Monad__ASLPProgSP : Monad ASLPProgSP :=
    {| ret := fun _ => @retASLPProg _ ;
      bind := fun _ _ => @bindASLPProg _ _ |}.
#[global] Instance Eq1__ProgASLP : Eq1 ASLPProgSP :=
    fun A m n => forall pre r, getProgASLP m pre r <-> getProgASLP n pre r.
#[global] Instance Eq1Equivalence__ASLPProgSP
    : @Eq1Equivalence ASLPProgSP _ Eq1__ProgASLP.
#[global] Instance MonadLaws__ProgASLP
    : @MonadLawsE ASLPProgSP Eq1__ProgASLP _.
```
Using this monad, we define our effect observation as follows:
```ocaml
#[program] Definition obsASLP {A} (m : nditprog S A) : ASLPProgSP S A :=
    fun pre r => (obsASP m pre r) \/ (obsDSLP m pre r).
```
And, we prove that it is a monad morphism:
```ocaml
Theorem obsASLP_ret {A} (a : A) : eq1 (obsASLP (ret a : nditprog S A)) (ret a).
Theorem obsASLP_bind {A B} (x : nditprog S A) (f : A -> nditprog S B) :
    eq1 (obsASLP (x >>= f)) (obsASLP x >>= (fun a => obsASLP (f a))).
```
We use this to define the triple based on ASLP:
```ocaml
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
```
We can successfully verify all of the examples that use `tripleSP obsASLP` in the old file - both `Under` and `Over`.

Additionally, we proved all the stated relationships between `ASP / DSLP / DSP / ASLP` that were in the old file.



Potential paper structure:
1. Introduction 
2. Overview of:
	1. Taxonomy paper (to introduce different predicate transformers and relationships between them)
	2. DM framework (to introduce specification monads and effect observations)
	3. Refinement calculus book (to introduce restricted classes of strongest postcondition predicate transformers required for specification monads)
3. Presentation of weakest precondition predicate transformers
4. Presentation of strongest postcondition predicate transformers
5. 



TODO:
- check about the Galois connection / embedding between PrePost and these specification monads - is there `ordProgSP` version of triple comparing the predicate transformers?
	- I messed with trying to think of the embedding myself - did not make progress. The prior embeddings results in predicate transformers that do not fall into our subclasses. Claude thought of something for pp2asp_over and pp2dslp_under - but I need to look into this more in order to claim that it is correct. If this does not exist, will need to think of story for why....
- TODO: record with multiple observations to generate multiple program logics - DM-style
- TODO: case studies!!!
- TODO: DM transformer story
- TODO: write down bullet points / key ideas
- TODO: merge together with weakest pre stuff

Deadlines:
- PLDI - November 12
- ESOP - October 15