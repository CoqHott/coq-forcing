Definition Obj := nat.
Axiom Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Axiom ε : forall n, n ≤ S n.
Axiom δ₀ δ₁ : forall n, S n ≤ n.

Set Primitive Projections.
Set Universe Polymorphism.

Record CType@{i} p := cType {
  type : forall p0 (α : p ≤ p0), Type@{i};
  path :
    (forall p0 (α : p ≤ p0), type p0 α) ->
    (forall p0 (α : p ≤ p0), type p0 α) ->
    (forall p0 (α : p ≤ p0), type p0 α) ->
    Type@{i};
}.
