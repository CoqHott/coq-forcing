Definition Obj := nat.
Axiom Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Axiom ε : forall n, n ≤ S n.
Axiom δ₀ δ₁ : forall n, S n ≤ n.

Set Primitive Projections.
Set Universe Polymorphism.

Record Typeᶠ@{i} p := cType {
  type : forall p0 (α : p ≤ p0), Type@{i};
  path :
    (forall p0 (α : p ≤ p0), type (S p0) (α ∘ ε p0)) ->
    (forall p0 (α : p ≤ p0), type p0 (α ∘ ε p0 ∘ δ₀ p0)) ->
    (forall p0 (α : p ≤ p0), type p0 (α ∘ ε p0 ∘ δ₁ p0)) ->
    Type@{i};
}.

Definition mkTypeᶠ@{i j} p : Typeᶠ@{j} p.
Proof.
refine (cType@{j} p _ _).
+ refine (fun p0 α => Typeᶠ@{i} p).
+ intros; exact Prop.
Defined.

Definition mkProdᶠ@{i j k} p
  (A : forall p0 (α : p ≤ p0), Typeᶠ@{i} p0)
  (B : forall p0 (α : p ≤ p0), (forall p1 (α0 : p0 ≤ p1), (A p1 (α ∘ α0)).(type _) p1 #) -> Typeᶠ@{j} p0)
  : Typeᶠ@{k} p.
Proof.
refine (cType@{k} p _ _).
+ refine (fun p0 α => forall x : (forall p1 α0, (A p1 (α ∘ α0)).(type _) p1 #), (B p0 α x).(type _) p0 #).
+ intros.
  exact Prop.
Defined.
