Require Forcing.

Inductive Obj := O.
Definition Hom (p q : Obj) := bool.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Definition eq (A : Type) (x y : A) : Prop := forall (P : A -> Prop), P x -> P y.
Definition refl : forall A (x : A), eq A x x := fun A x P p => p.
Definition eq_rect : forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, eq A x y -> P y :=
  fun A x P p y e => e P p.

Forcing Translate eq using Obj Hom.
Forcing Translate refl using Obj Hom.
Forcing Translate eq_rect using Obj Hom.

Forcing Definition Empty : Type using Obj Hom.
Proof.
intros p q α.
exact False.
Defined.

Forcing Definition Empty_rect : forall A, Empty -> A using Obj Hom.
Proof.
intros p A e.
destruct (e p #).
Defined.

Definition propext := forall (A B : Prop), (A -> B) -> (B -> A) -> eq Prop A B.

Forcing Translate propext using Obj Hom.

Definition A₀ := fun p q (α : p ≤ q) r (β : q ≤ r) => True.
Definition A₁ := fun p q (α : p ≤ q) r (β : q ≤ r) => if β r Datatypes.true then True else False.

Definition lift {p q} (α : Hom p q) : p ≤ q := fun r β => xorb α β.

Forcing Definition neg_propext : propext -> Empty using Obj Hom.
Proof.
intros p hpext.
specialize (hpext p # (A₀ p) (A₁ p) (fun q α H => I) (fun q α H => I)).
compute in hpext.
specialize (hpext (fun q α H r β => H r β r (@lift r r true))).
compute in *.
apply hpext.
intros; constructor.
Qed.
