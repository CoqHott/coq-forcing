Require Import Forcing.

Axiom Obj : Type.
Axiom Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Ltac _force c := force Obj Hom c.

Forcing Translate bool using Obj Hom.
Forcing Translate nat using Obj Hom.
Forcing Translate list using Obj Hom.

Inductive vect (A : Type) : nat -> Type :=
| nilv : vect A 0
| consv : A -> forall n, vect A n -> vect A (S n).

Forcing Translate vect using Obj Hom.

Goal True.
Proof.
_force (fun A n (v : vect A n) => 
          match v in vect _ n return (match n with |0 => bool |_ => nat end) with 
            |nilv _ => true 
            |consv _ _ x r => 1 
          end).
exact I.
Qed.