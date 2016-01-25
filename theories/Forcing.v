Declare ML Module "forcing".

Set Primitive Projections.
Set Universe Polymorphism.

Section Forcing.

Context {Obj : Type} {Hom : Obj -> Obj -> Type}.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Record Typeᶠ (p : Obj) := typeᶠ {
  type : forall p0 (α : p ≤ p0), Type;
  mono : (forall p0 (α : p ≤ p0), type p0 α) -> Type;
}.

Definition Typeᶿ {p} (A : forall p0 (α : p ≤ p0), Typeᶠ p0) :=
  forall p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1),
    type _ (A p0 α) p1 α0 = type _ (A p1 (α ∘ α0)) p1 #.

Definition TYPEᶠ p := {|
  type := fun p0 (α : p ≤ p0) => Typeᶠ p0;
  mono := @Typeᶿ p;
|}.

Definition cast {A B} (e : A = B) : B -> A := match e with eq_refl => fun x => x end.

Definition realizes p
  (A : forall p0 (α : p ≤ p0), Typeᶠ p0)
  (Aᴿ : Typeᶿ A)
  (x : forall p0 (α : p ≤ p0), type _ (A p0 α) p0 #) :=
  forall p0 (α : p ≤ p0),
    mono _ (A p0 α)
      (fun p1 (α0 : p0 ≤ p1) => cast (Aᴿ p0 α p1 α0) (x p1 (α ∘ α0))).

Definition Prodᶿ {p}
  (A : forall p0 (α : p ≤ p0), Typeᶠ p0)
  (Aᴿ : Typeᶿ A)
  (B : forall p0 (α : p ≤ p0)
    (x : forall p1 (α0 : p0 ≤ p1), type _ (A p1 (α ∘ α0)) p1 #)
    (xᴿ : realizes _
      (fun p1 (α0 : p0 ≤ p1) => A p1 (α ∘ α0))
      (fun p1 (α0 : p0 ≤ p1) => Aᴿ p1 (α ∘ α0))
      x),
    Typeᶠ p0)
(*   (Bᴿ : Typeᶿ A) *)
  := tt.


End Forcing.

Notation "t ∈ u " := (realizes _ u _ t) (at level 70, no associativity) : forcing_scope.
