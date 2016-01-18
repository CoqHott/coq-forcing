Require Forcing.

Section Unit.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Forcing Definition unit : Type using Obj Hom.
Proof.
intros p p0 α. exact unit.
Defined.

Forcing Definition tt : unit using Obj Hom.
Proof.
intros p; exact tt.
Defined.

(** Translation of the 'pure' elimination principle. *)
Definition unit_rect :
forall (p : Obj)
  (P : forall p0 : Obj, p ≤ p0 -> (forall p1 : Obj, p0 ≤ p1 -> ᶠunit p1 p1 #) -> forall p1 : Obj, p0 ≤ p1 -> Type),
(forall (p0 : Obj) (α : p ≤ p0), P p0 (# ∘ (α ∘ #)) (fun (p1 : Obj) (_ : p0 ≤ p1) => ᶠtt p1) p0 #) ->
forall (i : forall p0 : Obj, p ≤ p0 -> ᶠunit p0 p0 #),
match i p # with Datatypes.tt => P p # (fun _ _ => ᶠtt p) p # end.
Proof.
intros p P Ptt i.
destruct i.
apply Ptt.
Qed.

End Unit.
