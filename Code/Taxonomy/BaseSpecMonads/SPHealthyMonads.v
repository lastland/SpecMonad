(** * The pure SP monads, built by the same refinement recipe

    The companion of [WPHealthyMonads.v], for the other base transformer:

      [SPPure A = Prop -> (A -> Prop)]      vs      [WPureT A = (A -> Prop) -> Prop]

    [HealthySP] below plays the role [HealthyWP] plays there — subset carrier,
    projections, [Monad], [Eq1], [Eq1Equivalence], orders — so the packaging is
    written once for both SP monads instead of twice.

    Two things do NOT carry over, and they are the point of this file.

    - **The four conditions give only TWO monads here.**  [SPPure]'s
      precondition slot is a bare [Prop], of which there are only two up to
      propositional extensionality, so [Strict] alone already forces
      [Singleton] and [Terminating] alone forces [MSingleton].  Hence
      [DemonicTotal] collapses onto [AngelicTotal] and [AngelicLiberal] onto
      [DemonicLiberal] — [strict_conj_iff_singleton] in [DSPMonad.v],
      [term_disj_iff_msingleton] in [ASLPMonad.v].  On [PT A] the four classes
      are pairwise incomparable ([WPHealthyMonads.v], [Section Separation]);
      here they are not.

    - **[ret] and [bind] are NOT shared.**  On the WP side all four monads
      inherit one [ret]/[bind] from [WPure] and differ only by the carrier
      condition, which is why [HealthyWP] can hand out [MonadLawsE] too.  Here
      the angelic and demonic monads have genuinely different operations,

        [retASP  v = fun p a => p /\ a = v]      [bindASP  m k = fun p b => exists a, k a (m p a) b]
        [retDSLP v = fun p a => a = v -> p]      [bindDSLP m k = fun p b => forall a, k a (m p a) b]

      and the raw transformer type carries no monad structure at all for them
      to restrict.  So [HealthySP] takes [ret]/[bind] as parameters and stops
      short of the laws: each instance proves its own [MonadLawsE].

    The derived monads are shown to agree with the hand-built [ASPSP] /
    [DSLPSP] of [ASPMonad.v] / [DSLPMonad.v], which remain the ones the rest of
    the development uses. *)

From Coq Require Import Morphisms RelationClasses.
From ExtLib Require Import Monad.
From ITree Require Import Basics.Monad.
From Incorrectness.Taxonomy.BaseSpecMonads Require Import
  Healthiness SPPredicateTransformers ASPMonad DSLPMonad.

(** ** What an SP refinement has to supply *)

Module Type SP_COND.
  Parameter Cond : forall (A : Type), SPPure A -> Prop.
  Parameter retRaw : forall (A : Type), A -> SPPure A.
  Parameter bindRaw : forall (A B : Type),
      SPPure A -> (A -> SPPure B) -> SPPure B.
  Parameter Cond_ret : forall (A : Type) (a : A), Cond A (retRaw A a).
  Parameter Cond_bind : forall (A B : Type) (m : SPPure A) (k : A -> SPPure B),
      Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindRaw A B m k).
End SP_COND.

(** ** The shared packaging *)

Module HealthySP (C : SP_COND).

  Definition W (A : Type) : Type := { w : SPPure A | C.Cond A w }.

  Definition getW {A} (w : W A) : SPPure A := proj1_sig w.

  Lemma getW_cond {A} (w : W A) : C.Cond A (getW w).
  Proof. exact (proj2_sig w). Qed.

  Definition retW {A} (a : A) : W A :=
    exist _ (C.retRaw A a) (C.Cond_ret A a).

  Definition bindW {A B} (m : W A) (k : A -> W B) : W B :=
    exist _ (C.bindRaw A B (getW m) (fun a => getW (k a)))
            (C.Cond_bind A B (getW m) (fun a => getW (k a))
               (getW_cond m) (fun a => getW_cond (k a))).

  #[global] Instance Monad_W : Monad W :=
    {| ret := fun _ => @retW _ ; bind := fun _ _ => @bindW _ _ |}.

  #[global] Instance Eq1_W : Eq1 W :=
    fun A m n => forall p a, getW m p a <-> getW n p a.

  #[global] Instance Eq1Equivalence_W : @Eq1Equivalence W _ Eq1_W.
  Proof.
    intro A. constructor.
    - intros x p a. tauto.
    - intros x y H p a. specialize (H p a). tauto.
    - intros x y z H1 H2 p a. specialize (H1 p a); specialize (H2 p a). tauto.
  Qed.

  (** The orders, matching the WP side's [ordW] / [ordWAt]. *)

  Definition ordW {A} (m1 m2 : W A) : Prop :=
    forall p a, getW m1 p a -> getW m2 p a.

  Definition ordWAt {A} (pre : Prop) (m1 m2 : W A) : Prop :=
    forall a, getW m1 pre a -> getW m2 pre a.

  #[global] Instance ordW_PreOrder {A} : PreOrder (@ordW A).
  Proof.
    constructor.
    - intros x p a H. exact H.
    - intros x y z H1 H2 p a H. exact (H2 p a (H1 p a H)).
  Qed.

  (** [MonadLawsE] is deliberately NOT here: it depends on [retRaw]/[bindRaw],
      which differ between the instances.  See the file header. *)

End HealthySP.

(** ** The two instances *)

Module AngelicTotalSP <: SP_COND.
  Definition Cond (A : Type) (w : SPPure A) : Prop := Singleton w.
  Definition retRaw (A : Type) (a : A) : SPPure A := getASP (retASP a).
  Definition bindRaw (A B : Type) (m : SPPure A) (k : A -> SPPure B) : SPPure B :=
    fun p b => exists a, k a (m p a) b.
  Definition Cond_ret (A : Type) (a : A) : Cond A (retRaw A a) :=
    proj2_sig (retASP a).
  Lemma Cond_bind (A B : Type) (m : SPPure A) (k : A -> SPPure B) :
    Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindRaw A B m k).
  Proof.
    intros Hm Hk.
    exact (proj2_sig (bindASP (exist _ m Hm) (fun a => exist _ (k a) (Hk a)))).
  Qed.
End AngelicTotalSP.

Module DemonicLiberalSP <: SP_COND.
  Definition Cond (A : Type) (w : SPPure A) : Prop := MSingleton w.
  Definition retRaw (A : Type) (a : A) : SPPure A := getDSLP (retDSLP a).
  Definition bindRaw (A B : Type) (m : SPPure A) (k : A -> SPPure B) : SPPure B :=
    fun p b => forall a, k a (m p a) b.
  Definition Cond_ret (A : Type) (a : A) : Cond A (retRaw A a) :=
    proj2_sig (retDSLP a).
  Lemma Cond_bind (A B : Type) (m : SPPure A) (k : A -> SPPure B) :
    Cond A m -> (forall a, Cond B (k a)) -> Cond B (bindRaw A B m k).
  Proof.
    intros Hm Hk.
    exact (proj2_sig (bindDSLP (exist _ m Hm) (fun a => exist _ (k a) (Hk a)))).
  Qed.
End DemonicLiberalSP.

Module ASP  := HealthySP AngelicTotalSP.    (** angelic total   = [ASPSP]  *)
Module DSLP := HealthySP DemonicLiberalSP.  (** demonic liberal = [DSLPSP] *)

(** ** The derived monads are the hand-built ones

    Same carrier condition, same [ret], same [bind] — so nothing downstream
    has to move; [ASPMonad.v] and [DSLPMonad.v] remain the definitions in use,
    and this file shows they are what the recipe produces. *)

Section Agreement.
  Context {A B : Type}.

  Definition ASP_carrier_agrees : ASP.W A = ASPSP A := eq_refl.
  Definition DSLP_carrier_agrees : DSLP.W A = DSLPSP A := eq_refl.

  Lemma ASP_ret_agrees (a : A) (p : Prop) (x : A) :
    ASP.getW (ASP.retW a) p x <-> getASP (retASP a) p x.
  Proof. split; intro H; exact H. Qed.

  Lemma ASP_bind_agrees (m : ASPSP A) (k : A -> ASPSP B) (p : Prop) (b : B) :
    ASP.getW (ASP.bindW m k) p b <-> getASP (bindASP m k) p b.
  Proof. split; intro H; exact H. Qed.

  Lemma DSLP_ret_agrees (a : A) (p : Prop) (x : A) :
    DSLP.getW (DSLP.retW a) p x <-> getDSLP (retDSLP a) p x.
  Proof. split; intro H; exact H. Qed.

  Lemma DSLP_bind_agrees (m : DSLPSP A) (k : A -> DSLPSP B) (p : Prop) (b : B) :
    DSLP.getW (DSLP.bindW m k) p b <-> getDSLP (bindDSLP m k) p b.
  Proof. split; intro H; exact H. Qed.

End Agreement.

(** Hence the laws transport, rather than being reproved. *)

#[global] Instance MonadLawsE_ASP_W : @MonadLawsE ASP.W ASP.Eq1_W ASP.Monad_W.
Proof.
  destruct (@MonadLawsE_ASPSP) as [Lbrl Lbrr Lbb Lpb].
  constructor.
  - intros A B f x. exact (Lbrl A B f x).
  - intros A x. exact (Lbrr A x).
  - intros A B C x f g. exact (Lbb A B C x f g).
  - intros A B x y Hxy f g Hfg. exact (Lpb A B x y Hxy f g Hfg).
Qed.

#[global] Instance MonadLawsE_DSLP_W : @MonadLawsE DSLP.W DSLP.Eq1_W DSLP.Monad_W.
Proof.
  destruct (@MonadLawsE_DSLPSP) as [Lbrl Lbrr Lbb Lpb].
  constructor.
  - intros A B f x. exact (Lbrl A B f x).
  - intros A x. exact (Lbrr A x).
  - intros A B C x f g. exact (Lbb A B C x f g).
  - intros A B x y Hxy f g Hfg. exact (Lpb A B x y Hxy f g Hfg).
Qed.
