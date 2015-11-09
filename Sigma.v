Require Forcing.

Set Primitive Projections.

Section Sigma.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Record _sig_ p
  (A : forall p0 : Obj, p ≤ p0 -> forall p : Obj, p0 ≤ p -> Type)
  (P : forall (p0 : Obj) (α : p ≤ p0),
    (forall (p1 : Obj) (α0 : p0 ≤ p1), A p1 (# ∘ (α ∘ (# ∘ (α0 ∘ #)))) p1 #) -> forall p : Obj, p0 ≤ p -> Type)
  p0 (α : p ≤ p0) : Type := _exist_
{
  _proj1_ : (forall p1 (α0 : p0 ≤ p1), A p1 (α ∘ α0) p1 #);
  _proj2_ : (forall p1 (α0 : p0 ≤ p1), P p1 (α ∘ α0) (fun p2 α1 => _proj1_ p2 (α0 ∘ α1)) p1 #);
}.

Forcing Definition sig : forall (A : Type) (P : A -> Type), Type using Obj Hom.
Proof.
exact _sig_.
Defined.

Forcing Definition exist : forall A (P : A -> Type) (x : A) (p : P x), sig A P using Obj Hom.
Proof.
intros p A P x π.
refine (_exist_ _ _ _ _ _ _ π).
Defined.

Forcing Definition proj1 : forall A P, sig A P -> A using Obj Hom.
Proof.
intros p A P σ.
refine ((σ p #).(_proj1_ p A _ p #) p #).
Defined.

Forcing Definition proj2 : forall A P (σ : sig A P), P (proj1 A P σ) using Obj Hom.
Proof.
intros p A P σ.
compute.
change (
P p #
  (fun (p0 : Obj) (α : p ≤ p0) => (σ p0 α).(_proj1_ _ _ _ _ _) p0 #) p 
  #).
eapply ((σ p #).(_proj2_ _ _ _ _ _) p #).

eapply _proj2_.

Abort.

End Sigma.
