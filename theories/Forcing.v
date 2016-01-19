Declare ML Module "forcing".

Set Primitive Projections.
Set Universe Polymorphism.

Record Typeᶠ@{i j k l} {Obj : Type@{i}} {Hom : Obj -> Obj -> Type@{j}} (p : Obj) := typeᶠ {
  type : forall p0 (α : Hom p p0), Type@{k};
  mono : (forall p0 (α : Hom p p0), type p0 α) -> Type@{l};
}.
