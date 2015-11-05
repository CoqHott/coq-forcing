Declare ML Module "forcing".

Axiom Obj : Type.
Axiom Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Ltac _force c := force Obj Hom c.

Goal True.
Proof.
_force (fun (A : Type) (x : A) => x).
_force (fun (A : Type) (P : forall x : A, Type) (x : A) => P x).
_force (forall A : Type, (A -> Type) -> A -> Type).
_force (fun (A : Type) (x : A) (y : A) => forall (P : A -> Type), P x -> P y).
_force (forall A : Type, A -> A -> Type).
_force ((fun (A : Type) (x : A) => x) Type (forall A : Type, A -> A)).
_force (fun (A B : Type) (x : A) (y : B) => forall (P : A -> B -> Type) (Q : B -> Type), P x y -> Q y).
Abort.
