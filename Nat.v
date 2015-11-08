Require Forcing.

Section Nat.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Inductive ᶠᶠnat (p : Obj) q (α : p ≤ q) :=
| ᶠᶠO : ᶠᶠnat p q α
| ᶠᶠS : (forall r (β : q ≤ r), ᶠᶠnat r r #) -> ᶠᶠnat p q α
.

Forcing Definition nat : Type using Obj Hom.
Proof.
exact ᶠᶠnat.
Defined.

Forcing Definition O : nat using Obj Hom.
Proof.
intros p.
refine (ᶠᶠO p p #).
Defined.

Forcing Definition S : nat -> nat using Obj Hom.
Proof.
intros p n.
refine (ᶠᶠS p _ _ _).
intros p0 α.
apply (n _ α).
Defined.

End Nat.
