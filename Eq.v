Require Forcing.

Section Eq.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Forcing Definition eq : forall (A : Type), A -> A -> Type using Obj Hom.
Proof.
compute in *.
intros p A x y q α.
exact (x = y).
Defined.

Forcing Definition refl : forall (A : Type) (x : A), eq A x x using Obj Hom.
Proof.
intros; reflexivity.
Defined.

Forcing Definition eq_rect
     : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, eq A x y -> P y
using Obj Hom.
Proof.
intros p A x P Hx y e; compute in *.
change (fun (p0 : Obj) (α : p ≤ p0) => y p0 (fun (R : Obj) (k : Hom p0 R) => α R k)) with y.
specialize (e p #).
change (x = y) in e.
destruct e.
apply Hx.
Defined.

End Eq.
