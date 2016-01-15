Require Import Forcing.

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
(* _force ((fun (A : Type) (x : A) => x) Type (forall A : Type, A -> A)). *)
_force (fun (A B : Type) (x : A) (y : B) => forall (P : A -> B -> Type) (Q : B -> Type), P x y -> Q y).
exact I.
Qed.

Definition foo := fun A (x : A) => x.
Definition bar := foo (foo (forall A : Type, A -> A) (fun A (x : A) => x) Type Type).
Definition qux := (fun (A : Type) (x : A) => x) Type (forall A : Type, A -> A).
Definition quz := Type -> Type.
Definition eq := fun (A : Type) (x y : A) => forall (P : A -> Prop), P x -> P y.

Forcing Translate list using Obj Hom.
Forcing Translate sum using Obj Hom.
Forcing Translate nat using Obj Hom.

Scheme natᶠ_rect := Induction for natᶠ Sort Type.

Forcing Definition idn : nat -> nat using Obj Hom.
Proof.
  intros p n.
  specialize (n p #).
  induction n as [|p n IHn].
  + apply Oᶠ.
  + apply Sᶠ, IHn.
Defined.  

Print sum.
Print sumᶠ.

Definition baz := sum Type Type.
Forcing Translate baz using Obj Hom.

Print bazᶠ.

Forcing Definition mlk : forall A, list A using Obj Hom.
Proof.
compute.
exact nilᶠ.
Defined.

Definition test_let := let X := forall A, A in X -> X.

Forcing Translate test_let using Obj Hom.
