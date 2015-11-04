Declare ML Module "forcing".

Axiom Obj : Type.
Axiom Hom : Obj -> Obj -> Type.

Goal True.
Proof.
force Obj Hom (fun (A : Type) (x : A) => x).
Admitted.
