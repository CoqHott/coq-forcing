Require Import Forcing.

Axiom Obj : Type.
Axiom Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Definition foo := fun A (x : A) => x.
Definition bar := fun A B => forall x : A, B x.
Definition qux := (fun (A : Type) (x : A) => x) Type (forall A : Type, A -> A).
Definition quz := Type -> Type.
Definition eq := fun (A : Type) (x y : A) => forall (P : A -> Prop), P x -> P y.

Open Scope forcing_scope.

Definition baz := forall A : Type, A.

Fail Forcing Translate baz using Obj Hom.
Check
fun p : Obj =>
@box _ _ _ _ _
  (@BProdᶠ Obj Hom p (@BTYPEᶠ Obj Hom p)
     (@mkBox Obj Hom p (BArrowᶠ p (@BTYPEᶠ Obj Hom p) (@BTYPEᶠ Obj Hom p))
        (fun (p0 : Obj) (α : p ≤ p0) (A : @Box Obj Hom p0 (@BTYPEᶠ Obj Hom α)) => A)
        (fun (p0 : Obj) (α : p ≤ p0) (A : @Box Obj Hom p0 (@BTYPEᶠ Obj Hom α)) => A))) p 
  #.

Forcing Translate quz using Obj Hom.

Fail Forcing Translate bar using Obj Hom.


(* Fail Forcing Translate qux using Obj Hom. *)

(* Forcing Translate eq using Obj Hom. *)


