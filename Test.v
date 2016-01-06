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

Forcing Translate foo using Obj Hom.
Forcing Translate bar using Obj Hom.
Forcing Translate qux using Obj Hom.
Forcing Translate quz using Obj Hom.
Forcing Translate eq using Obj Hom.

Print ᶠfoo.
Print ᶠbar.
Print ᶠqux.
Print ᶠquz.
Forcing Translate nat using Obj Hom.
Forcing Translate unit using Obj Hom.
Forcing Translate list using Obj Hom.
Forcing Translate sum using Obj Hom.

(** Define a term directly in the forcing layer. *)

Forcing Definition sum : Type -> Type -> Type using Obj Hom.
Proof.
intros p A B p0 α.
exact ((forall p1 (α0 : p0 ≤ p1), A p1 ((α ∘ α0) ∘ #) p1 #) + (forall p1 (α0 : p0 ≤ p1), B p1 ((α ∘ α0) ∘ #) p1 #))%type. 
Defined.

Print sum.
Print ᶠsum.

Definition baz := sum Type Type.
Forcing Translate baz using Obj Hom.

Print ᶠbaz.
