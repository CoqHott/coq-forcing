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

Record Box_ (p : Obj) (A : forall p0 (α : p ≤ p0), Typeᶠ p0) (Aᴿ : Typeᶿ A) := mkBox_ {
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

Definition mkBox (p : Obj) (A : BTypeᶠ p) t tr : Box p A := mkBox_ p _ _ t tr.

Definition lift {p : Obj} {A} (x : Box p A) {p0} (α : p ≤ p0) : Box p0 (lift_ p _ _ A p0 α) := lift_ p _ _ x p0 α.

Definition Arrowᶠ (p : Obj) (A : BTypeᶠ p) (B : BTypeᶠ p) : Typeᶠ p.
Proof.
simple refine ({| type := _; mono := _ |}).
+ simple refine (fun p0 (α : p ≤ p0) => _).
  simple refine (Box p0 (lift_ p _ _ A p0 α) -> type _ (box _ _ _ B p0 α) p0 #).
+ simple refine (fun f => forall x : Box p A, _).
  simple refine (mono _ (box _ _ _ B p #) (fun p0 (α : p ≤ p0) => cast (mon _ _ _ B p # p # p0 α) (f p0 α (lift x α)))).
Defined.

Definition BArrowᶠ (p : Obj) (A : BTypeᶠ p) (B : BTypeᶠ p) : BTypeᶠ p.
Proof.
simple refine ({| box := fun p0 (α : p ≤ p0) => _; |}).
+ simple refine (Arrowᶠ p0 (lift_ p _ _ A _ α) (lift_ p _ _ B _ α)).
+ refine (fun p0 (α : p ≤ p0) (p1 : Obj) (α0 : p0 ≤ p1) (p2 : Obj) (α1 : p1 ≤ p2) => eq_refl).
Defined.

Definition Prodᵀ (p : Obj) (A : BTypeᶠ p) (B : Box p (BArrowᶠ p A (BTYPEᶠ p))) :=
  fun p0 (α : p ≤ p0) => forall x : Box p0 (lift_ p _ _ A p0 α), type _ ((box _ _ _ B p0 α) x) p0 #.

Definition Prodᶿ (p : Obj) (A : BTypeᶠ p) (B : Box p (BArrowᶠ p A (BTYPEᶠ p)))
  (f : forall p0 (α : p ≤ p0), Prodᵀ p A B p0 α) :=
  forall x : Box p A, mono _ (box _ _ _ B p # x) (fun p0 (α : p ≤ p0) => cast (mon _ _ _ B p # x p # p0 α) (f p0 α (lift x α))).

Definition Prodᶠ (p : Obj) (A : BTypeᶠ p) (B : Box p (BArrowᶠ p A (BTYPEᶠ p))) : Typeᶠ p := {|
  type := Prodᵀ p A B;
  mono := Prodᶿ p A B
|}.

Definition BProdᶠ (p : Obj) (A : BTypeᶠ p) (B : Box p (BArrowᶠ p A (BTYPEᶠ p))) : BTypeᶠ p.
Proof.
simple refine ({| box := fun p0 (α : p ≤ p0) => _; |}).
+ simple refine (Prodᶠ p0 (lift_ p _ _ A _ α) (lift_ p _ _ B _ α)).
+ refine (fun p0 (α : p ≤ p0) (p1 : Obj) (α0 : p0 ≤ p1) (p2 : Obj) (α1 : p1 ≤ p2) => eq_refl).
Defined.

End Forcing.

Arguments box {_ _ _ _ _} _ _ _.
Arguments type {_ _ _} _ _ _.

Notation "A →ᶠ B" := (@Arrowᶠ _ _ _ A B)
  (at level 99, B at level 200, right associativity) : forcing_scope.

Notation "A →ᵇ B" := (@BArrowᶠ _ _ _ A B)
  (at level 99, B at level 200, right associativity) : forcing_scope.
