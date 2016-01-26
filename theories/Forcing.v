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

Definition TYPEᶠ p : Typeᶠ p := {|
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

Record Box_ (p : Obj) (A : forall p0 (α : p ≤ p0), Typeᶠ p0) (Aᴿ : Typeᶿ A) := mkBox {
  box : forall p0 (α : p ≤ p0), type _ (A p0 α) p0 #;
  mon : realizes p A Aᴿ box;
}.

Definition lift_ (p : Obj) A Aᴿ (x : Box_ p A Aᴿ) p0 (α : p ≤ p0) :
  Box_ p0 (fun p1 (α0 : p0 ≤ p1) => A p1 (α ∘ α0)) (fun p1 (α0 : p0 ≤ p1) => Aᴿ p1 (α ∘ α0)) :=
  {|
    box := fun p1 (α0 : p0 ≤ p1) => box _ _ _ x p1 (α ∘ α0);
    mon := fun p1 (α0 : p0 ≤ p1) => mon _ _ _ x p1 (α ∘ α0);
  |}.

Definition BTypeᶠ (p : Obj) :=
  Box_ p (fun p0 (α : p ≤ p0) => TYPEᶠ p0) (fun p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1) => eq_refl).

Definition BTYPEᶠ (p : Obj) : BTypeᶠ p.
Proof.
simple refine ({| box := fun p0 (α : p ≤ p0) => _; mon := _; |}).
+ exact (TYPEᶠ p0).
+ refine (fun p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1) p2 (α1 : p1 ≤ p2) => eq_refl).
Defined.

Definition Box (p : Obj) (A : BTypeᶠ p) :=
  Box_ p (box _ _ _ A) (fun p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1) => mon _ _ _ A p0 α p0 # p1 α0).

Definition lift {p : Obj} {A} (x : Box p A) {p0} (α : p ≤ p0) : Box p0 (lift_ p _ _ A p0 α) := lift_ p _ _ x p0 α.

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
  (Bᴿ : forall p0 (α : p ≤ p0)
    (x : forall p1 (α0 : p0 ≤ p1), type _ (A p1 (α ∘ α0)) p1 #)
    (xᴿ : realizes _
      (fun p1 (α0 : p0 ≤ p1) => A p1 (α ∘ α0))
      (fun p1 (α0 : p0 ≤ p1) => Aᴿ p1 (α ∘ α0))
      x),
    Typeᶿ
      (fun p1 (α0 : p0 ≤ p1) =>
        B p1 (α ∘ α0)
          (fun p2 (α1 : p1 ≤ p2) => x p2 (α0 ∘ α1))
          (fun p2 (α1 : p1 ≤ p2) => xᴿ p2 (α0 ∘ α1))))
  (f : forall p0 (α : p ≤ p0) x xᴿ, type _ (B p0 α x xᴿ) p0 #)
  :=

    forall
    (x : forall p0 (α : p ≤ p0), type _ (A p0 α) p0 #)
    (xᴿ : realizes _
      (fun p0 (α : p ≤ p0) => A p0 α)
      (fun p0 (α : p ≤ p0) => Aᴿ p0 α) x),
    realizes _
      (fun p0 (α : p ≤ p0) =>
        B p0 α
          (fun p1 (α0 : p0 ≤ p1) => x p1 (α ∘ α0))
          (fun p1 (α0 : p0 ≤ p1) => xᴿ p1 (α ∘ α0)))
      (fun p0 (α : p ≤ p0) =>
        Bᴿ p0 α
          (fun p1 (α0 : p0 ≤ p1) => x p1 (α ∘ α0))
          (fun p1 (α0 : p0 ≤ p1) => xᴿ p1 (α ∘ α0)) p0 #)
      (fun p0 (α : p ≤ p0) =>
        cast (Bᴿ p0 α
          (fun p1 (α0 : p0 ≤ p1) => x p1 (α ∘ α0))
          (fun p1 (α0 : p0 ≤ p1) => xᴿ p1 (α ∘ α0)) p0 # p0 #)
        (f p0 α
          (fun p1 (α0 : p0 ≤ p1) => x p1 (α ∘ α0))
          (fun p1 (α0 : p0 ≤ p1) => xᴿ p1 (α ∘ α0))))
.

End Forcing.

Arguments box {_ _ _ _ _} _ _ _.
Arguments type {_ _ _} _ _ _.

Notation "t ∈ u " := (realizes _ u _ t) (at level 70, no associativity) : forcing_scope.
