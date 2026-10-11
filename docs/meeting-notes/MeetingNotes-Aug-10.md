In DM4All, Kenji considers the following monad of strongest postcondition predicate transformers with the following restrictions:
```ocaml
(* Restricted sppt *)
Definition PureSP (A : Type) : Type := Prop -> A -> Prop.
Definition Monotone {A} (w : PureSP A) : Prop :=
  forall (p q : Prop) (a : A), (p -> q) -> w p a -> w q a.
Definition Codomain {A} (w : PureSP A) : Prop :=
  forall (p : Prop) (a : A), w p a -> p.
Definition KenjiPureSP (A : Type) : Type := { w : PureSP A | Monotone w /\ Codomain w }.

(* ret and bind *)
#[program] Definition retKenjiPureSP {A} (v : A) : KenjiPureSP A :=
    fun pre a => pre /\ a = v.
#[program] Definition bindKenjiPureSP {A B} (m : KenjiPureSP A)(k : A -> KenjiPureSP B) : KenjiPureSP B :=
    fun pre b => exists a, k a (m pre a) b.
(* I trust that the monad laws hold *)
```
Consider the natural way extend this to sppts reasoning about stateful programs with exceptions:
```ocaml
(* natural extension to (S -> Prop) -> (option (A * S) -> Prop) *)
Definition ProgSP (A : Type) : Type := (S -> Prop) -> (option (A * S) -> Prop).
Definition MonotoneS {A} (w : ProgSP A) : Prop :=
  forall (p q : S -> Prop) (r : option (A * S)), (forall (s : S), p s -> q s) -> w p r -> w q r.
Definition CodomainS {A} (w : ProgSP A) : Prop :=
  forall (p : S -> Prop) (r : option (A * S)), w p r -> (exists, p s).
Definition KenjiProgSP (A : Type) : Type := { w : ProgSP A | MonotoneS w /\ CodomainS w }.

(* natural way to define ret and bind *)
#[program] Definition retKenjiProgSP {A} (v : A) : KenjiProgSP A :=
    fun pre r => exists s0, pre s0 /\ r = Some (v, s0).
#[program] Definition bindKenjiProgSP {A B} (m : KenjiProgSP A)(k : A -> KenjiProgSP B) : KenjiProgSP B :=
    fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
```
However, the bind monad law breaks:
```ocaml
#[program] Definition m : KenjiProgSP bool bool :=
    fun pre r => exists s, pre s.
#[program] Definition k : bool -> KenjiProgSP bool unit :=
    fun a => fun pre r => (exists s, pre s) /\ r = Some (tt, a).
#[program] Definition g : KenjiProgSP bool unit :=
    fun pre r => pre true /\ pre false.
    
Definition pre : bool -> Prop := fun _ => True.
Definition r : option (unit * bool) := Some (tt, true).

(** LHS **)

  (* bind (bind m k) (fun _ : unit => g) pre r <->
     (exists b : unit, g (fun s1 => (bind m k) pre (Some (b, s1))) r) \/ (r = None /\ (bind m k) pre None) <->
     (exists b : unit, g (fun s1 => (bind m k) pre (Some (b, s1))) r) <->
     g (fun s1 => (bind m k) pre (Some (tt, s1))) r <-> (see below)
     g (fun s1 => True) r <-> (unfold g)
     True /\ True <-> True
   *)

  (* (bind m k) pre (Some (tt, s1)) <-> (unfold bind)
     exists a, k a (fun s0 => m pre (Some (a, s0))) (Some (tt, s1)) <-> (unfold k)
     exists a, (exists s, m pre (Some (a, s))) /\ a = s1 <-> (unfold m)
     exists a, (exists s, pre s) /\ a = s1 <-> (a := true)
     exists s, pre s <-> (s := s1)
     True *)
     
(** RHS **)

  (* bind m (fun a => bind (k a) (fun _ : unit => g)) pre r <->
     (exists a : bool, (bind (k a) g) (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None) <->
     (exists a : bool, (bind (k a) g) (fun s0 => m pre (Some (a, s0))) r) <->
     (exists a : bool, (bind (k a) g) (fun _ => exists s, pre s) r) <->
     (exists a : bool, (bind (k a) g) (fun _ => True) r) <->
     (exists a : bool, False) <-> False
   *)

  (* (bind (k a) g) (fun _ => True) r <->
     (exists b : unit, g (fun s1 => k a (fun _ => True) (Some (b,s1))) r) \/ (r = None /\ k a (fun _ => True) None) <->
     (exists b : unit, g (fun s1 => k a (fun _ => True) (Some (b,s1))) r) <->
     g (fun s1 => k a (fun _ => True) (Some (tt, s1))) r <-> (seebelow)
     g (fun s1 => s1 = a) r <->
     (fun s1 => s1 = a) true /\ (fun s1 => s1 = a) false <->
     (true = a) /\ (false a) <-> False *)

  (* k a (fun _ => True) (Some (tt, s1)) <->
     (exists s, True) /\ Some (tt, s1) = Some (tt, a) <->
     s1 = a *)

Theorem ProgSP_bind_bind_fails :
    ~ (forall (A B C S : Type) 
    (m : KenjiProgSP S A) 
    (f : A -> KenjiProgSP S B)
    (g : B -> KenjiProgSP S C) 
    (pre : S -> Prop) 
    (r : option (C * S)),
    getKenjiProgSP S (bindKenjiProgSP S (bindKenjiProgSP S mf) g) pre r <->
    getKenjiProgSP S (bindKenjiProgSP S m (fun a => bindKenjiProgSP S (f a) g)) pre r).
```
INTUITION: The problematic predicate transformer here is `g := fun pre r => pre true /\ pre false`. It requires that two distinct initial states satisfy the precondition. The LHS of the bind simplifies as follows:
`bind (bind m k) (fun _ : unit => g) pre r <-> g (fun s1 => True) r`.
The precondition passed to g is not problematic, since it always returns True. However the RHS of the bind simplifies as follows:
`bind m (fun a => (bind k a) (fun _ : unit => g)) pre r <-> (exists a : bool, g (fun s1 => s1 = a) r) <-> (exists a : bool, (a = true) /\ (a = false)`, where here we see the case where a precondition like `(fun s1 => s1 = a)` cannot possibly be satisfied by two distinct initial states.

We suggest strengthening our restriction.

From Back and Wright's, "Refinement Calculus: A Systematic Introduction", they introduce homomorphism properties of predicate transformers other than just monotonicity. The main classes of predicate transformers (written directly for predicate transformer over stateful programs that throw exceptions, `S : (S -> Prop) -> (option (A * S) -> Prop)`) are:
- *strict*: if they preserve bottom
 `forall r, ~ S (fun _ => False) r`
- *terminating*: if they preserve top
 `forall r, S (fun _ => True) r`
- *conjunctive*: if they preserve nonempty meets of predicates
```ocaml
forall r,
S (fun s => q1 s /\ q2 s /\ ...) r <-> 
(S (fun s => q1 s) r) /\ (S (fun s => q2 s) r) /\ ...
```
- *disjunctive*: if they preserve nonempty joins of predicates
```ocaml
forall r,
S (fun s => q1 s \/ q2 s \/ ...) r <->
(S (fun s => q1 s) r) \/ (S (fun s => q2 s) r) \/ ...
```
Furthermore, a *universally conjunctive* predicate transformer preserves arbitrary meets (*terminating* + *conjunctive*). A *universally disjunctive* predicate transformer preserves arbitrary joins (*strict + disjunctive*). 

We formalize these classes as follows for `ProgSP`:
`ProgSP`
```ocaml
Definition StrictProg {A} (w : ProgSP A) : Prop :=
 forall (r : option (A * S)), ~ w (fun _ => False) r.

Definition TerminatingProg {A} (w : ProgSP A) : Prop :=
 forall (r : option (A * S)), w (fun _ => True) r.

Definition ConjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type) (i0 : I) (p : I -> (S -> Prop)) (r : option (A * S)),
  w (fun s => forall i, p i s) r <-> forall i, w (fun s => p i s) r.

Definition DisjunctiveProg {A} (w : ProgSP A) : Prop :=
 forall (I : Type) (i0 : I) (p : I -> (S -> Prop)) (r : option (A * S)),
  w (fun s => exists i, p i s) r <-> exists i, w (fun s => p i s) r.
```

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
- disjunctive: $\checkmark$ TODO: formalize
```ocaml
asp[p](fun s => q1 s \/ q2 s)(r) == (q1 s1 \/ q2 s1) \/ (q1 s2 \/ q2 s2)
==
asp[p](fun s => q1 s)(r) /\ asp[p](fun s => q2 s)(r) ==
  (q1 s1 \/ q1 s2) \/ (q2 s1 \/ q2 s2)
```
So, we consider *strict* + *disjunctive* (aka join-preserving) strongest postcondition predicate transformers.

Actually, for the `PureSP` variant, this is equivalent to Kenji's restriction:
`PureSP`
```ocaml
Definition Strict {A} (w : PureSP A) : Prop :=
 forall (a : A), ~ w False a.

Definition Terminating {A} (w : PureSP A) : Prop :=
 forall (a : A), w True r.

Definition Conjunctive {A} (w : PureSP A) : Prop :=
 forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
  w (forall i, p i) r <-> forall i, w (p i) r.

Definition Disjunctive {A} (w : PureSP A) : Prop :=
 forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
  w (exists i, p i) r <-> exists i, w (p i) r.
```
Official definition:
```ocaml
Definition JoinPreserving {A} (w : PureSP A) : Prop :=
  Strict w /\ Disjunctive w.
```
In order to speed up proofs, Claude suggests the following single-decomposition version:
```ocaml
Definition Singleton {A} (w : PureSP A) : Prop :=
  forall (p : Prop) (a : A), w p a <-> p /\ w True a.
```
Intuitively:
```ocaml
For (w : PureSP A) (pre : Prop) (a : A),
w pre a <-> (* same as saying exists proof of pre *)
w (exists i : pre, True) a <-> (* by join preserving *)
exists i : pre, w True a <-> (* same as saying exists proof of pre *)
pre /\ w True a
```
And, indeed, these are equivalent definitions:
```ocaml
Theorem join_iff_singleton {A} (w : PureSP A) :
  JoinPreserving w <-> Singleton w.
```
Additionally:
```ocaml
Theorem kenji_iff_singleton {A} (w : PureSP A) :
  KenjiPureSP w <-> Singleton w.
```
Since Kenji's `PureSP` formalization forms a monad, we know that our `PureSP` join-preserving predicate transformer also form a monad.

However, join-preserving is a strictly stronger restriction than monotone + codomain when reasoning about stateful programs that can throw exceptions - shown by the fact that the same ret / bind equations form a monad:
```ocaml
Definition JoinPreservingProg {A} (w : ProgSP A) : Prop :=
  StrictProg S w /\ DisjunctiveProg S w.
```
Single-decomposition version:
```ocaml
Definition SingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : option (A * S)),
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
The definitions for ret and bind are the same as our KenjiSPProg attempt - we prove that they are also join-preserving.
```ocaml
#[program] Definition retASPProg {A} (v : A) : SingletonProgSP A :=
  fun pre r => exists s0, pre s0 /\ r = Some (v, s0).
    
 #[program] Definition bindASPProg {A B} (m : SingletonProgSP A) (k : A -> SingletonProgSP B) : SingletonProgSP B :=
  fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
```
And, we show that the monad laws hold:
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
Let us return to our "problematic" predicate transformer:
```ocaml
#[program] Definition g : KenjiProgSP bool unit :=
    fun pre r => pre true /\ pre false.
```
This is notably *not* disjunctive:
```ocaml
g (fun s => q1 s \/ q2 s) r <-> 
(q1 true \/ q2 true) /\ (q1 false \/ q2 false)
!=
(g (fun s => q1 s) r) \/ (g (fun s => q2 s) r) <->
(q1 true /\ q1 false) \/ (q2 false /\ q2 false)
```
Intuitively, monotonicity and codomain from above are *local* conditions: each constrains `w` at one precondition or along one comparison. Join-preserving is a *global* condition relating `w`'s values along incomparable preconditions. Specifically, the predicate transformer cannot require that the precondition is satisfied by a group of distinctive initial states (like `g` requiring that `pre` holds of `true` and `false`).

Using this monad, we define our effect observation, as follows:
```ocaml
#[program] Definition obsASP {A} (m : nditprog S A) : ASPProgSP S A :=
    fun pre r => exists s, pre s /\ unOptionT (unOptionT (runStateT m s)) (Some r).
```
And, we prove that it is a monad morphism:
```ocaml
Theorem obsASP_ret {A} (a : A) : eq1 (obsASP (ret a : nditprog S A)) (ret a).
Theorem obsASP_bind {A B} (x : nditprog S A) (f : A -> nditprogS B) :
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
- conjunctive: $\checkmark$ TODO: formalize
```ocaml
dslp[p](fun s => q1 s /\ q2 s)(r) == (q1 s1 /\ q2 s1) /\ (q1 s2 /\ q2 s2)
==
dslp[p](fun s => q1 s)(r) /\ dslp[p](fun s => q2 s)(r) ==
  (q1 s1 /\ q1 s2) /\ (q2 s1 /\ q2 s2)
```
- disjunctive: `X`
```ocaml
(* consider that r has two states s1 and s2 that lead to it *)
dslp[p](fun s => q1 s \/ q2 s)(r) == (q1 s1 \/ q2 s1) /\ (q1 s2 \/ q2 s2)
!= 
dslp[p](fun s => q1 s)(r) \/ dslp[p](fun s => q2 s)(r) ==
  (q1 s1 /\ q1 s2) \/ (q2 s1 /\ q2 s2)
```
So, we consider *terminating* + *conjunctive* (aka meet-preserving) strongest postcondition predicate transformers.

For `PureSP`, there is a dual definition as given by Kenji:
Kenji's definition for *angelic* sppts:
`SPost`$A = (pre:\mathbb{P}) \rightarrow (A \rightarrow \mathbb{P}_{/pre})$, where $\mathbb{P}_{/pre} := \{q : \mathbb{P} | q \implies pre\}$
Dual definition for *demonic* sppts:
`SMPost`$A = (pre:\mathbb{P}) \rightarrow (A \rightarrow \mathbb{P}^{/pre})$, where $\mathbb{P}^{/pre} := \{q : \mathbb{P} | pre \implies q\}$ 
```ocaml
Definition CodomainDSLP {A} (w : PureSP A) : Prop :=
 forall (p : Prop) (a : A), p -> w p a.

Definition KenjiPureDSLP {A} (w : PureSP A) : Prop := Monotone w /\ CodomainDSLP w.
```
Here is the definition w.r.t indexed sets of preconditions:
```ocaml
Definition MeetPreserving {A} (w : PureSP A) : Prop :=
	Terminating w /\ Conjunctive w.
```
Single-decomposition version:
```ocaml
Definition MSingleton {A} (w : PureSP A) : Prop :=
    forall (p : Prop) (a : A), w p a <-> p \/ w False a.
```
These are equivalent definitions:
```ocaml
Theorem meet_iff_msingleton {A} (w : PureSP A) :
    MeetPreserving w <-> MSingleton w.
    
Theorem kenjidslp_iff_msingleton {A} (w : PureSP A) :
    KenjiPureDSLP w <-> MSingleton w.
```
We define meet-preserving sppts as a refinement:
```ocaml
Definition DSLPSP (A : Type) : Type := { w : PureSP A | MSingleton w }.
```
The following ret and bind form a monad:
```ocaml
#[program] Definition retDSLP {A} (v : A) : DSLPSP A :=
    fun p a => a = v -> p.
    
#[program] Definition bindDSLP {A B} (m : DSLPSP A) (k : A -> MSingletonSP B) : MSingletonSP B :=
    fun p b => forall a, (k a) (m p a) b.
```
And, we show that the monad laws hold:
```ocaml
#[global] Instance Monad_DSLPSP : Monad DSLPSP :=
    {| ret := fun _ => retDSLP ;
      bind := fun _ _ => bindDSLP |}.
#[global] Instance Eq1_DSLPSP : Eq1 DSLPSP :=
    fun A m n => forall p a, getDSLP m p a <-> getDSLP n p a.
#[global] Instance Eq1Equivalence_DSLPSP
    : @Eq1Equivalence DSLPSP _ Eq1_DSLPSP.
#[global] Instance MonadLawsE_DSLPSP
    : @MonadLawsE DSLPSP Eq1_DSLPSP _.
```

Now, we show that these meet-preserving strongest postcondition predicate transformers also form a monad when reasoning about stateful programs that can throw exceptions.
```ocaml
Definition MeetPreservingProg {A} (w : ProgSP A) : Prop :=
	TerminatingProg S w /\ ConjunctiveProg S w.
```
Single-decomposition version:
```ocaml
Definition MSingletonProg {A} (w : ProgSP A) : Prop :=
    forall (pre : S -> Prop) (r : option (A * S)),
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
Here are meet-preserving ret and bind:
```ocaml
#[program] Definition retDSLPProg {A} (v : A) : DSLPProgSP A :=
    fun pre r => forall s0, r = Some (v, s0) -> pre s0.

#[program] Definition bindDSLPProg {A B} (m : DSLPProgSP A) (k : A -> DSLPProgSP B) : DSLPProgSP B :=
  fun pre r => (forall a, k a (fun s0 => m pre (Some (a, s0))) r) /\ (r = None -> m pre None).
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

We, again, examine $dsp$ to see what classes it falls into (definition from "Taxonomy..."):
$$dsp[p](b) = \lambda \tau. \bigwedge_{\sigma \in [p]^{-1}(\tau)} b(\sigma) \text{, if } [p]^{-1}(\tau) \neq \emptyset \text{, otherwise, }false$$
- strict: for `b = (fun _ => False)`, `dsp[p](b) = False` $\checkmark$
- terminating: when $[p]^{-1}(\tau) \neq \emptyset$, for `b = (fun _ => True)`,  `dsp[p](b) != True X`
- conjunctive: $\checkmark$ TODO: formalize
```ocaml
dsp[p](fun s => q1 s /\ q2 s)(r) == (q1 s1 /\ q2 s1) /\ (q1 s2 /\ q2 s2)
==
dsp[p](fun s => q1 s)(r) /\ dsp[p](fun s => q2 s)(r) ==
  (q1 s1 /\ q1 s2) /\ (q2 s1 /\ q2 s2)
```
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
 We utilize the following characterization to define `ret` and `bind`:
 $$dsp[p](b) = asp[p](b) \cap dslp[p](b)$$
 Let us consider why this equality holds. Consider the total correctness version of the weakest precondition predicate transformer. The following equality holds:
 $$dwp[p](b) = dwp[p](\lambda \_.true) \cap dwlp[p](b)$$
 The liberal part (dwlp) checks that paths starting in the precondition terminate in the postcondition or diverge. 
 The termination part (dwp) checks that all paths terminate. 
 Together, this ensures that all paths starting in the precondition terminate in the postcondition.
 
 This mirrors the above strongest postcondition predicate transformer characterization. 
 
 The liberal part (dslp) checks that final states are either unreachable or strictly reachable by initial states in the precondition. 
 The reachability part (asp) checks that the final state is reachable. 
 Together, this ensures that all final states are strictly reachable by initial states in the precondition. 
 
In the `ret` case, the conjunction of an `ASPProgSP` predicate transformer and a `DSLPProgSP` predicate transformer is trivially a `DSPProgSP` predicate transformer. We unfold the two definitions:
```ocaml
retASPProg {A} (a : A) := fun pre r => exists s0, pre s0 /\ r = Some (a, s0)
retDSLPProg {A} (a : A) := fun pre r => forall s0, r = Some (a, s0) -> pre s0.

retDSPProg {A} (a : A) := fun pre r =>
  (exists s0, pre s0 /\ r = Some (a, s0)) /\ (forall s0, r = Some (a, s0) -> pre s0) <-> 
  (exists s0, pre s0 /\ r = Some (a, s0))
```
We confirm that this predicate transformer is *strict* and *positively conjunctive* (aka a `DSPProgSP` predicate transformer).
- strict: for `b = (fun _ => False)`, `retDSPProg a b = False` for all `r` 
- conjunctive: $\checkmark$ TODO: formalize
```ocaml
(* consider that r has two states s1 and s2 that lead to it *)
retDSPProg a (fun s => q1 s /\ q2 s) (r) == (exists s0, q1 s0 /\ q2 s0 /\ r = Some (a, s0))
==
retDSPProg a (fun s => q1 s) (r) /\ retDSPProg a (fun s => q2 s) (r) ==
(exists s0, q1 s0 /\ r = Some (a, s0)) /\ (exists s1, q2 s1 /\ r = Some (a, s1)) (* is only True when s0 == s1*)
<->
(exists s0, q1 s0 /\ q2 s0 /\ r = Some (a, s0))
```
For `bind`, we first unfold both definitions of bind for the `ASPProgSP` predicate transformer and the `DSLPProgSP` predicate transformer:
```ocaml
bindASPProg {A B} (m : ASPProgSP A) (k : A -> ASPProgSP B) := 
  fun pre r => 
  (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None)
bindDSLPProg {A B} (m : DSLPProgSP A) (k : A -> DSLPProgSP B) :=
  fun pre r =>
  (forall a, k a (fun s0 => m pre (Some (a, s0))) r) /\ (r = None -> m pre None)
```
TODO...




```ocaml
bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) := fun pre r =>
  ((exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None)) /\
  ((forall a, k a (fun s0 => m pre (Some (a, s0))) r) /\ (r = None -> m pre None))
  
Definition aspPartdsp {A} (w : DSPProgSP A) : ASPProgSP A :=
  fun pre r => getProgDSP w (fun _ => True) r /\
               ~ getProgDSP w (fun s => ~ pre s) r.
(* first conjunct isolates reachable states *)
(* second conjunct removes states not reachable from pre *)

Definition dslpPartdsp {A} (w : DSPProgSP A) : DSLPProgSP A :=
  fun pre r => getProgDSP w (fun _ => True) r ->
               getProgDSP w pre r.
(* if state is reachable, it must satisfy pre *)
  
bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) := fun pre r =>
  bindASPProg (aspPartdsp m) (fun a => aspPartdsp (k a)) pre r /\
  bindDSLPProg (dslpPartdsp m) (fun a => dslpPartdsp (k a)) pre r.
```


 ```ocaml
#[program] Definition retDSPProg {A} (a : A) : DSPProgSP A :=
    fun pre r => (retASPProg a pre r) /\ (retDSLPProg a pre r).
    
#[program] Definition bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) : DSPProgSP B := (* bindASPProg a pre r /\ bindDSLPProg a pre r *)
 let C : S -> option (B * S) -> Prop := fun s r =>
  exists o, (getProgDSP m (fun _ => True) o
            /\ ~ getProgDSP m (fun t => t <> s) o)
            /\ match o with
               | Some (a, smid) => getProgDSP (k a) (fun _ => True) r
                            /\ ~ getProgDSP (k a) (fun t => t <> smid) r
               | None => r = None
               end in
    fun pre r => (exists s, pre s /\ C s r) /\ (forall s, C s r -> pre s).
 ```
Comparison to `bindASPProg` and `bindDSLPProg`:
```ocaml
#[program] Definition bindASPProg {A B} (m : SingletonProgSP A) (k : A -> SingletonProgSP B) : SingletonProgSP B :=
  fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
  
#[program] Definition bindDSLPProg {A B} (m : DSLPProgSP A) (k : A -> DSLPProgSP B) : DSLPProgSP B :=
  fun pre r => (forall a, k a (fun s0 => m pre (Some (a, s0))) r) /\ (r = None -> m pre None).
```
Intuition for bind:

For `asp`: 
1. there exists `s` that satisfies `pre` and leads to some `rmid = Some (a, s0)` 
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

Similarly, consider the definition of $aslp$. The $\bigvee$ implies that the predicate transformer should be disjunctive, BUT when $\tau$ is unreachable -> `aslp[p](b) = True`
![[Screenshot 2026-08-03 at 15.12.52.png]]
so, we consider *terminating* + *positively disjunctive* strongest postcondition predicate transformers.
```ocaml
Definition TerminatingPositivelyJoinPreservingProg {A} (w : ProgSP A) : Prop :=
	TerminatingProg S w /\ DisjunctiveProg S w.
```
We define terminating, positively join-preserving sppts as a refinement:
```ocaml
 Definition ASLPProgSP (A : Type) : Type :=
    { w : ProgSP A | TerminatingPositivelyJoinPreservingProg w }.
```
We utilize the following characterization to define `ret` and `bind`:
![[Screenshot 2026-08-03 at 15.47.42.png]]
```ocaml
#[program] Definition retASLPProg {A} (a : A) : ASLPProgSP A :=
    fun pre r => (retASPProg a pre r) \/ (retDSLPProg a pre r).

#[program] Definition bindASLPProg {A B}
    (m : ASLPProgSP A) (k : A -> ASLPProgSP B) : ASLPProgSP B :=
    let C : S -> option (B * S) -> Prop :=
      fun s r =>
        exists o, (~ getProgASLP m (fun _ => False) o
                   /\ getProgASLP m (fun t => t = s) o)
                  /\ match o with
                     | Some (a, smid) => ~ getProgASLP (k a) (fun _ => False) r
                                         /\ getProgASLP (k a) (fun t => t = smid) r
                     | None => r = None
                     end in
    fun pre r => (exists s, pre s /\ C s r) \/ (forall s, C s r -> pre s).
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

TODO:
- check about the Galois connection / embedding between PrePost and these specification monads
- is there `ordProgSP` version of triple comparing the predicate transformers?
- make sure all theorems / figures in Taxonomy paper are formalized