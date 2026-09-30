(** * [SPArrT]: strongest-postcondition predicate transformers

      [SPArrT A B] = [(A -> Prop) -> B -> Prop]

    The raw carrier every SP arrow refines: an element sends a precondition
    on [A] to the outcomes in [B] it accepts.  Each refinement is cut out by
    homomorphism properties, which say which operations on preconditions an
    element preserves:

      [MonotoneSPost] ([GaloisArr.v])     monotone
      [ASPArr]  ([ASPArrowCore.v])        monotone, strict, disjunctive
      [DSLPArr] ([DSLPArrowCore.v])       monotone, terminating, conjunctive
      [DSPArr]  ([DSPArrowCore.v])        monotone, strict, conjunctive
      [ASLPArr] ([ASLPArrowCore.v])       monotone, terminating, disjunctive

    Conjunctivity and disjunctivity quantify over NONEMPTY families;
    strictness and termination are the empty cases.  "Terminating" is top
    preservation, not termination of a computation.

    The arrow operations are not shared: angelic and demonic [arr_pure]
    differ, and DSP / ASLP composition is not composition of transformers
    ([DSPArrowCore.v]), so [SPArrT] has no arrow structure of its own that
    the refinements inherit. *)

Definition SPArrT (A B : Type) : Type := (A -> Prop) -> B -> Prop.

Definition sp_monotone {A B} (f : SPArrT A B) : Prop :=
  forall (P Q : A -> Prop), (forall a, P a -> Q a) -> forall b, f P b -> f Q b.

Definition sp_strict {A B} (f : SPArrT A B) : Prop :=
  forall b, ~ f (fun _ => False) b.

Definition sp_terminating {A B} (f : SPArrT A B) : Prop :=
  forall b, f (fun _ => True) b.

Definition sp_conjunctive {A B} (f : SPArrT A B) : Prop :=
  forall (I : Type), inhabited I -> forall (P : I -> A -> Prop) b,
    f (fun a => forall i, P i a) b <-> forall i, f (P i) b.

Definition sp_disjunctive {A B} (f : SPArrT A B) : Prop :=
  forall (I : Type), inhabited I -> forall (P : I -> A -> Prop) b,
    f (fun a => exists i, P i a) b <-> exists i, f (P i) b.
