(** * Arrow typeclasses and laws.

    We define Hughes-style [Arrow], [ArrowChoice], [ArrowApply], and
    [ArrowLoop] typeclasses with their laws.  The canonical relational
    instance [Pred A B := A -> B -> Prop] lives in [Taxonomy/Pred.v];
    its law instances live in [Taxonomy/PredFacts.v]. *)

From Coq Require Import Morphisms FunctionalExtensionality.

(* ================================================================= *)
(** ** Helper functions for products and sums                         *)
(* ================================================================= *)

Definition swap {A B} (p : A * B) : B * A :=
  let '(a, b) := p in (b, a).

Definition assoc_prod {A B C} (p : (A * B) * C) : A * (B * C) :=
  let '((a, b), c) := p in (a, (b, c)).

Definition unassoc_prod {A B C} (p : A * (B * C)) : (A * B) * C :=
  let '(a, (b, c)) := p in ((a, b), c).

Definition sum_bimap {A B C D} (f : A -> C) (g : B -> D) (x : A + B) : C + D :=
  match x with inl a => inl (f a) | inr b => inr (g b) end.

Definition assoc_sum {A B C} (x : (A + B) + C) : A + (B + C) :=
  match x with
  | inl (inl a) => inl a
  | inl (inr b) => inr (inl b)
  | inr c => inr (inr c)
  end.

Definition sum_prod_dist {A C D} (p : (A + C) * D) : (A * D) + (C * D) :=
  let '(ac, d) := p in
  match ac with inl a => inl (a, d) | inr c => inr (c, d) end.

Definition swap_sum {A B} (x : A + B) : B + A :=
  match x with inl a => inr a | inr b => inl b end.

(* ================================================================= *)
(** ** Arrow typeclass                                                *)
(* ================================================================= *)

Class Arrow (arr : Type -> Type -> Type) := {
  arr_pure : forall {A B}, (A -> B) -> arr A B ;
  arr_comp : forall {A B C}, arr A B -> arr B C -> arr A C ;
  arr_first : forall {A B C}, arr A B -> arr (A * C)%type (B * C)%type
}.

Section ArrowDerived.
  Context {arr : Type -> Type -> Type} `{Arrow arr}.

  Definition arr_id {A} : arr A A :=
    arr_pure (fun x => x).

  Definition arr_second {A B C} (f : arr A B) : arr (C * A)%type (C * B)%type :=
    arr_comp (arr_pure swap) (arr_comp (arr_first f) (arr_pure swap)).

  Definition arr_split {A B C D} (f : arr A B) (g : arr C D)
    : arr (A * C)%type (B * D)%type :=
    arr_comp (arr_first f) (arr_second g).

  Definition arr_fanout {A B C} (f : arr A B) (g : arr A C)
    : arr A (B * C)%type :=
    arr_comp (arr_pure (fun a => (a, a))) (arr_split f g).
End ArrowDerived.

(* ================================================================= *)
(** ** Arrow equality and laws                                        *)
(* ================================================================= *)

Class ArrowEq (arr : Type -> Type -> Type) := {
  arrow_eq : forall {A B}, arr A B -> arr A B -> Prop ;
  arrow_eq_equiv :: forall A B, Equivalence (@arrow_eq A B)
}.

Class ArrowLaws (arr : Type -> Type -> Type)
  `{Harr : Arrow arr} `{Heq : ArrowEq arr} := {
  comp_id_l : forall {A B} (f : arr A B),
    arrow_eq (arr_comp arr_id f) f ;
  comp_id_r : forall {A B} (f : arr A B),
    arrow_eq (arr_comp f arr_id) f ;
  comp_assoc : forall {A B C D} (f : arr A B) (g : arr B C) (h : arr C D),
    arrow_eq (arr_comp (arr_comp f g) h) (arr_comp f (arr_comp g h)) ;
  pure_comp : forall {A B C} (f : A -> B) (g : B -> C),
    arrow_eq (arr_comp (arr_pure f) (arr_pure g))
             (arr_pure (fun x => g (f x))) ;
  first_pure : forall {A B C} (f : A -> B),
    arrow_eq (@arr_first _ _ A B C (arr_pure f))
             (arr_pure (fun p : A * C => let '(a, c) := p in (f a, c))) ;
  first_comp : forall {A B C D} (f : arr A B) (g : arr B C),
    arrow_eq (@arr_first _ _ _ _ D (arr_comp f g))
             (arr_comp (arr_first f) (arr_first g)) ;
  first_fst : forall {A B C} (f : arr A B),
    arrow_eq (arr_comp (@arr_first _ _ _ _ C f) (arr_pure fst))
             (arr_comp (arr_pure fst) f) ;
  first_assoc : forall {A B C D} (f : arr A B),
    arrow_eq
      (arr_comp (@arr_first _ _ _ _ D (@arr_first _ _ A B C f))
                (arr_pure assoc_prod))
      (arr_comp (arr_pure assoc_prod) (@arr_first _ _ A B (C * D) f)) ;
  comp_proper :: forall (X Y Z : Type),
    Proper (@arrow_eq arr Heq X Y ==> @arrow_eq arr Heq Y Z ==>
            @arrow_eq arr Heq X Z) (@arr_comp arr Harr X Y Z) ;
  first_proper :: forall (X Y Z : Type),
    Proper (@arrow_eq arr Heq X Y ==>
            @arrow_eq arr Heq (X*Z)%type (Y*Z)%type) (@arr_first arr Harr X Y Z) ;
  first_natural : forall {A B C D} (f : arr A B) (g : C -> D),
    arrow_eq
      (arr_comp (arr_first f)
        (arr_pure (fun '(b, c) => (b, g c))))
      (arr_comp (arr_pure (fun '(a, c) => (a, g c)))
        (arr_first f))
}.

(* ================================================================= *)
(** ** ArrowChoice                                                    *)
(* ================================================================= *)

Class ArrowChoice (arr : Type -> Type -> Type) `{Arrow arr} := {
  arr_left : forall {A B C}, arr A B -> arr (A + C)%type (B + C)%type
}.

Section ArrowChoiceDerived.
  Context {arr : Type -> Type -> Type} `{ArrowChoice arr}.

  Definition arr_right {A B C} (f : arr A B) : arr (C + A)%type (C + B)%type :=
    arr_comp (arr_pure swap_sum) (arr_comp (arr_left f) (arr_pure swap_sum)).
End ArrowChoiceDerived.

Class ArrowChoiceLaws (arr : Type -> Type -> Type)
  `{ArrowChoice arr} `{ArrowEq arr} := {
  left_pure : forall {A B C} (f : A -> B),
    arrow_eq (@arr_left _ _ _ A B C (arr_pure f))
             (arr_pure (fun x => sum_bimap f (fun c : C => c) x)) ;
  left_comp : forall {A B C D} (f : arr A B) (g : arr B C),
    arrow_eq (@arr_left _ _ _ _ _ D (arr_comp f g))
             (arr_comp (arr_left f) (arr_left g)) ;
  left_inl : forall {A B C} (f : arr A B),
    arrow_eq (arr_comp f (arr_pure (@inl B C)))
             (arr_comp (arr_pure inl) (arr_left f)) ;
  left_assoc : forall {A B C D} (f : arr A B),
    arrow_eq
      (arr_comp (@arr_left _ _ _ _ _ D (@arr_left _ _ _ A B C f))
                (arr_pure assoc_sum))
      (arr_comp (arr_pure assoc_sum) (@arr_left _ _ _ A B (C + D) f)) ;
  left_inr : forall {A B C} (f : arr A B),
    arrow_eq (arr_comp (arr_pure (@inr A C)) (@arr_left _ _ _ A B C f))
             (arr_pure (@inr B C)) ;
  left_natural : forall {A B C D} (f : arr A B) (g : C -> D),
    arrow_eq (arr_comp (@arr_left _ _ _ A B C f)
                       (arr_pure (fun x => sum_bimap (fun b : B => b) g x)))
             (arr_comp (arr_pure (fun x => sum_bimap (fun a : A => a) g x))
                       (@arr_left _ _ _ A B D f)) ;
  first_left_dist : forall {A B C D} (f : arr A B),
    arrow_eq
      (arr_comp (@arr_first _ _ _ _ D (@arr_left _ _ _ A B C f))
                (arr_pure sum_prod_dist))
      (arr_comp (arr_pure sum_prod_dist)
                (@arr_left _ _ _ _ _ (C * D)%type (arr_first f))) ;
  left_proper : forall {A B C},
    Proper (@arrow_eq arr _ A B ==> @arrow_eq arr _ (A + C)%type (B + C)%type)
           (@arr_left _ _ _ A B C)
}.

(* ================================================================= *)
(** ** ArrowApply                                                     *)
(* ================================================================= *)

Class ArrowApply (arr : Type -> Type -> Type) `{Arrow arr} := {
  arr_app : forall {A B}, arr (arr A B * A)%type B
}.

(** The full application contract includes Hughes' pairing,
    precomposition, and postcomposition laws, static application, and
    extensionality of dynamically selected arrow/argument pairs. *)
Class ArrowApplyLaws (arr : Type -> Type -> Type)
  `{ArrowApply arr} `{ArrowEq arr} := {
  app_law : forall {A B} (f : arr A B),
    arrow_eq (arr_comp (arr_pure (fun a => (f, a))) arr_app) f ;
  (** Standard application coherence: pairing, precomposition, and
      postcomposition also hold for dynamically selected arrows. *)
  app_unit : forall (A B : Type),
    arrow_eq
      (arr_comp
        (arr_first (arr_pure (fun x : A => arr_pure (fun y : B => (x, y)))))
        arr_app)
      (@arr_id arr _ (A * B)) ;
  app_precompose : forall {A B C} (g : arr A B),
    arrow_eq
      (arr_comp (arr_first (arr_pure (fun f : arr B C => arr_comp g f)))
        arr_app)
      (arr_comp (arr_second g) arr_app) ;
  app_postcompose : forall {A B C} (h : arr B C),
    arrow_eq
      (arr_comp (arr_first (arr_pure (fun f : arr A B => arr_comp f h)))
        arr_app)
      (arr_comp arr_app h) ;
  (** Application respects the arrow equality inside ordinary input
      values.  This supplies continuation congruence for derived bind. *)
  app_ext : forall {X A B} (u v : X -> arr A B * A),
    (forall x, arrow_eq (fst (u x)) (fst (v x)) /\
               snd (u x) = snd (v x)) ->
    arrow_eq (arr_comp (arr_pure u) arr_app)
             (arr_comp (arr_pure v) arr_app)
}.

(* ================================================================= *)
(** ** ArrowLoop                                                      *)
(* ================================================================= *)

Class ArrowLoop (arr : Type -> Type -> Type) `{Arrow arr} := {
  arr_loop : forall {A B C}, arr (A * C)%type (B * C)%type -> arr A B
}.

Class ArrowLoopLaws (arr : Type -> Type -> Type)
  `{ArrowLoop arr} `{ArrowEq arr} := {
  loop_left_tightening : forall {A B C D}
    (h : arr A B) (f : arr (B * D)%type (C * D)%type),
    arrow_eq (arr_loop (arr_comp (arr_first h) f))
             (arr_comp h (arr_loop f)) ;
  loop_right_tightening : forall {A B C D}
    (f : arr (A * D)%type (B * D)%type) (g : arr B C),
    arrow_eq (arr_loop (arr_comp f (arr_first g)))
             (arr_comp (arr_loop f) g) ;
  loop_sliding : forall {A B C}
    (f : arr (A * C)%type (B * C)%type) (k : C -> C),
    arrow_eq (arr_loop (arr_comp f (arr_second (arr_pure k))))
             (arr_loop (arr_comp (arr_second (arr_pure k)) f)) ;
  loop_vanishing : forall {A B C D}
    (f : arr ((A * C) * D)%type ((B * C) * D)%type),
    arrow_eq (arr_loop (arr_loop f))
             (arr_loop (arr_comp (arr_pure unassoc_prod)
                         (arr_comp f (arr_pure assoc_prod)))) ;
  loop_superposing : forall {A B C D}
    (f : arr (A * D)%type (B * D)%type),
    arrow_eq (@arr_second _ _ A B C (arr_loop f))
             (arr_loop (arr_comp (arr_pure assoc_prod)
                         (arr_comp (@arr_second _ _ (A*D) (B*D) C f)
                                   (arr_pure unassoc_prod))))
}.

(* ================================================================= *)
(** ** Arrow Transformer                                              *)
(* ================================================================= *)

(** An arrow transformer lifts arrows from one type to another,
    analogous to monad transformers. *)

Class ArrowT (T : (Type -> Type -> Type) -> Type -> Type -> Type) := {
  arrowT_lift : forall {arr : Type -> Type -> Type} `{Arrow arr} {A B},
    arr A B -> T arr A B
}.

(* ================================================================= *)
(** ** Applied forms of the [ArrowApply] laws                         *)
(* ================================================================= *)

(** Each law, precomposed with a pure pair-builder [fun x => (u x, t x)].
    This is the shape every client meets: the arrow fed to [arr_app] is
    computed from the input, never sitting alone on the left. *)

Section ArrowApplyDerived.

  Context {arr : Type -> Type -> Type}
          `{HA : Arrow arr} `{HAA : @ArrowApply arr HA}
          `{HE : ArrowEq arr} `{HL : @ArrowLaws arr HA HE}
           `{HAAL : @ArrowApplyLaws arr HA HAA HE}.

  (** Compatibility names for the previous application contract. *)
  Lemma app_pair {A B} :
    arrow_eq (arr_comp
      (arr_first (arr_pure (fun x : A => arr_pure (fun y : B => (x, y)))))
      arr_app) (@arr_id arr HA (A * B)).
  Proof. apply app_unit. Qed.

  Lemma app_post {A B C} (h : arr B C) :
    arrow_eq (arr_comp
      (arr_first (arr_pure (fun f : arr A B => arr_comp f h))) arr_app)
      (arr_comp arr_app h).
  Proof. apply app_postcompose. Qed.

  Lemma arr_pure_ext {A B} (f g : A -> B) :
    (forall x, f x = g x) -> arrow_eq (arr_pure f) (arr_pure g).
  Proof.
    intro H. replace g with f by (extensionality x; apply H). reflexivity.
  Qed.

  (** [app_pair] applied: feeding [app] the pairing arrow returns the pair. *)
  Lemma app_pair_at {X A B} (u : X -> A) (t : X -> B) :
    arrow_eq (arr_comp (arr_pure (fun x => (arr_pure (fun v : B => (u x, v)), t x)))
                       arr_app)
             (arr_pure (fun x => (u x, t x))).
  Proof.
    transitivity
      (arr_comp (arr_comp (arr_pure (fun x => (u x, t x)))
                   (@arr_first _ _ A (arr B (A * B)%type) B
                      (arr_pure (fun a : A => arr_pure (fun v : B => (a, v))))))
                arr_app).
    - apply comp_proper; [| reflexivity ].
      symmetry.
      etransitivity; [ apply comp_proper; [ reflexivity | apply first_pure ] |].
      etransitivity; [ apply pure_comp |].
      apply arr_pure_ext. intro x. reflexivity.
    - etransitivity; [ apply comp_assoc |].
      etransitivity; [ apply comp_proper; [ reflexivity | apply app_pair ] |].
      apply comp_id_r.
  Qed.

  (** [app_post] applied: postcomposition passes through [app]. *)
  Lemma app_post_at {X A B C} (u : X -> arr A B) (t : X -> A) (h : arr B C) :
    arrow_eq (arr_comp (arr_pure (fun x => (arr_comp (u x) h, t x))) arr_app)
             (arr_comp (arr_comp (arr_pure (fun x => (u x, t x))) arr_app) h).
  Proof.
    transitivity
      (arr_comp (arr_comp (arr_pure (fun x => (u x, t x)))
                   (@arr_first _ _ (arr A B) (arr A C) A
                      (arr_pure (fun f : arr A B => arr_comp f h))))
                arr_app).
    - apply comp_proper; [| reflexivity ].
      symmetry.
      etransitivity; [ apply comp_proper; [ reflexivity | apply first_pure ] |].
      etransitivity; [ apply pure_comp |].
      apply arr_pure_ext. intro x. reflexivity.
    - etransitivity; [ apply comp_assoc |].
      etransitivity; [ apply comp_proper; [ reflexivity | apply app_post ] |].
      symmetry. apply comp_assoc.
  Qed.

  (** [app_ext] applied: [app] sees its arrow argument up to [arrow_eq]. *)
  Lemma app_ext_at {X A B} (u v : X -> arr A B) (t : X -> A) :
    (forall x, arrow_eq (u x) (v x)) ->
    arrow_eq (arr_comp (arr_pure (fun x => (u x, t x))) arr_app)
             (arr_comp (arr_pure (fun x => (v x, t x))) arr_app).
  Proof. intro H. apply app_ext. intro x. split; [apply H | reflexivity]. Qed.

End ArrowApplyDerived.
