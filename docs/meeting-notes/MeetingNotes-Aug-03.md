In DM4All, Kenji considers the following monad of strongest postcondition predicate transformers with the following restrictions:
```ocaml
(* Restricted sppt *)
Definition PureSP (A : Type) : Type := Prop -> A -> Prop.
Definition Monotone {A} (w : PureSP A) : Prop :=
  forall (p q : Prop) (a : A), (p -> q) -> w p a -> w q a.
Definition Codomain {A} (w : PureSP A) : Prop :=
  forall (p : Prop) (a : A), w p a -> p.
Definition KenjiPureSP {A} (w : SP A) : Prop := Monotone w /\ Codomain w.

(* ret and bind *)
Definition PureSP_ret {A} (v : A) : PureSP A :=
  fun pre a => pre /\ a = v.
Definition PureSP_bind {A B} (m : PureSP A) (f : A -> PureSP B): PureSP B :=
  fun pre b => exists a, f a (m pre a) b.
(* ret and bind are KenjiPureSP sppts (I trust that the monad laws hold) *)
Lemma PureSP_ret_kenji {A} (v : A) : KenjiPureSP (PureSP_ret v).
Lemma PureSP_bind_kenji {A B} (m : PureSP A) (f : A -> PureSP B) :
  KenjiPureSP m -> (forall a, KenjiPureSP (f a)) -> KenjiPureSP(PureSP_bind m f).
```
Consider the natural way extend this to sppts reasoning about stateful programs with exceptions:
```ocaml
(* natural extension to (S -> Prop) -> (option (A * S) -> Prop) *)
Definition ProgSP (A : Type) : Type := (S -> Prop) -> (option (A * S) -> Prop).
Definition MonotoneS {A} (w : ProgSP A) : Prop :=
  forall (p q : S -> Prop) (r : option (A * S)), (forall (s : S), p s -> q s) -> w p r -> w q r.
Definition CodomainS {A} (w : ProgSP A) : Prop :=
  forall (p : S -> Prop) (r : option (A * S)), w p r -> (exists, p s).
Definition KenjiProgSP {A} (w : ProgSP A) : Prop := MonotoneS w /\ CodomainS w.

(* natural way to define ret and bind *)
Definition ProgSP_ret {A} (v : A) : ProgSP A :=
  fun pre r => exists s0, pre s0 /\ r = Some (v, s0).
Definition ProgSP_bind {A B} (m : ProgSP A) (k : A -> ProgSP B): ProgSP B :=
  fun pre r => (exists a, k a (fun s0 => m pre (Some (a, s0))) r) \/ (r = None /\ m pre None).
  
(* confirmation that both are KenjiProgSP sppts *)
Lemma ProgSP_ret_kenji {A} (v : A) : KenjiProgSP (ProgSP_ret v).
Lemma ProgSP_bind_kenji {A B} (m : ProgSP A) (k : A -> ProgSP B) :
  KenjiProgSP m -> (forall a, KenjiProgSP (k a)) -> KenjiProgSP(ProgSP_bind m k).
```
However, the bind monad law breaks:
```ocaml
(* precondition must hold for two distinct initial states *)
Definition g_two : ProgSP unit :=
  fun pre _ => exists x y, pre x /\ pre y /\ x <> y.
(* it is a KenjiProgSP sppt *)
Lemma m_kenji : KenjiProgSP m.

(* precondition non-empty *)
Definition m_any : ProgSP bool := fun pre _ => exists s, pre s.
(* it is a KenjiProgSP sppt *)
Lemma m'_kenji : KenjiProgSP m'.

Definition f (sA sB : S) : bool -> ProgSP unit :=
  fun a => fun pre r => (exists s, pre s) /\ r = Some (tt, if a then sA else sB)
(* it is a KenjiProgSP sppt *)
Lemma f_kenji (sA sB : S) (a : bool) : KenjiProgSP (f sA sB a).

Theorem ProgSP_bind_bind_fails (sA sB : S) (Hne : sA <> sB) :
    ~ (forall (A B C : Type) (m : ProgSP A) (f : A -> ProgSP B)
              (g : B -> ProgSP C) (pre : S -> Prop) (r : option (C * S)),
         ProgSP_bind (ProgSP_bind m f) g pre r <->
         ProgSP_bind m (fun a => ProgSP_bind (f a) g) pre r).

assert (HL : ProgSP_bind 
		 (ProgSP_bind mAny (fPin sA sB))
         (fun _ : unit => gTwo) 
         (fun _ => True) 
         (Some (tt, sA))).
assert (HR : ~ ProgSP_bind 
		 mAny
         (fun a => ProgSP_bind (fPin sA sB a) (fun _ : unit => gTwo))
         (fun _ => True) 
         (Some (tt, sA))).
```

We suggest strengthening our restriction.

From Back and Wright's, "Refinement Calculus: A Systematic Introduction":
For an indexed set of predicates $\{p_i | i \in I \}$ and $S \in \Sigma \rightarrow \Gamma$, where $\Sigma$ represents the initial state space and $\Gamma$ the final state space: ![[Screenshot 2026-08-03 at 13.21.10.png]]![[Screenshot 2026-08-03 at 09.49.49.png]]
![[Screenshot 2026-08-03 at 09.47.32.png]]
![[Screenshot 2026-08-03 at 13.21.10.png]]where join-preserving preserve *arbitrary* joins == *universally disjunctive* == *strict* + *disjunctive*.

The types of predicate transformers are defined as follows for `ProgSP` and `PureSP`:
`PureSP`: 
```ocaml
Definition Strict {A} (w : PureSP A) : Prop :=
 forall (a : A), ~ w False a.

Definition Terminating {A} (w : PureSP A) : Prop :=
 forall (a : A), w True a.

Definition Conjunctive {A} (w : PureSP A) : Prop :=
 forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
  w (forall i, p i) a <-> forall i, w (p i) a.

Definition Disjunctive {A} (w : PureSP A) : Prop :=
 forall (I : Type) (i0 : I) (p : I -> Prop) (a : A),
  w (exists i, p i) a <-> exists i, w (p i) a.
```
`ProgSP`:
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

First, we show that for the pure, it is the same definition.
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
(* needs to exist initial state that satifies pre and leads to r *)
    
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
Intuitively, monotonicity and codomain from above are *local* conditions: each constrains `w` at one precondition or along one comparison. Join-preserving is a *global* condition relating `w`'s values along incomparable preconditions. Specifically, any precondition passed to the strongest postcondition predicate transformer must be satisfiable by a *single* initial state, not a group of initial states. This is what allowed the previous bad behavior in the associativity of the bind.

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

To handle *demonic* sppts, we define a new specification monad of *meet-preserving* strongest postcondition predicate transformers, where this means that they preserve *arbitrary* meets == *universally conjunctive* == *terminating* + *conjunctive*, as defined below.
![[Pasted image 20260803145353.png]]
![[Screenshot 2026-08-03 at 13.22.58.png]]
For pure, there is a dual definition as given by Kenji:
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
(* every initial state that leads to r needs to satisfy pre - can be vacuous *)

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

From the characterizations of $asp$ and $dslp$, we see a pattern emerge:
![[Pasted image 20260803145505.png]]
$asp$ : *strict* + *disjunctive*
![[Screenshot 2026-08-03 at 14.55.23.png]]
$\bigvee$ corresponds to $\cup$ AND when $\tau$ is unreachable -> `asp[p](b) = False` (nullary element of $\lor$)

$dslp$ : *terminating* + *conjunctive*
![[Screenshot 2026-08-03 at 15.00.05.png]]
$\bigwedge$ corresponds to $\cap$ AND when $\tau$ is unreachable -> `dslp[p](b) = True` (nullary element of $\land$)

Now, consider the definition of $dsp$. The $\bigwedge$ implies that the predicate transformer should be conjunctive, BUT when $\tau$ is unreachable -> `dsp[p](b) = False`
![[Screenshot 2026-08-03 at 15.09.42.png]]
so, we consider *strict* + *positively conjunctive* strongest postcondition predicate transformers.
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
 ![[Screenshot 2026-08-03 at 15.38.48.png]]
 ```ocaml
#[program] Definition retDSPProg {A} (a : A) : DSPProgSP A :=
    fun pre r => (retASPProg a pre r) /\ (retDSLPProg a pre r).
    
#[program] Definition bindDSPProg {A B} (m : DSPProgSP A) (k : A -> DSPProgSP B) : DSPProgSP B :=
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