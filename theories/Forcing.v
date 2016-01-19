Declare ML Module "forcing".

Set Primitive Projections.
Set Universe Polymorphism.

Record CType@{i j k} {Obj : Type@{i}} {Hom : Obj -> Obj -> Type@{j}} (p : Obj) := cType {
  type : forall p0 (α : Hom p p0), Type@{k};
}.
