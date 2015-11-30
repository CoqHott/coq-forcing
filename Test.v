Require Import Cube Forcing.

Ltac _force c := force c.

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

Forcing Translate foo.
Forcing Translate bar.
Forcing Translate qux.
Forcing Translate quz.

Print ᶠfoo.
Print ᶠbar.
Print ᶠqux.
Print ᶠquz.

(* Fail Forcing Translate nat using Obj Hom. *)

(** Define a term directly in the forcing layer. *)

Forcing Definition sum : Type -> Type -> Type.
Proof.
intros p A B p0 α.
exact ((forall p1 (α0 : p0 ≤ p1), A p1 ((α ∘ α0) ∘ #) p1 #) + (forall p1 (α0 : p0 ≤ p1), B p1 ((α ∘ α0) ∘ #) p1 #))%type. 
Defined.

Print sum.
Print ᶠsum.

Definition baz := sum Type Type.
Forcing Translate baz.

Print ᶠbaz.
