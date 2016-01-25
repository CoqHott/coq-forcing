Require Forcing.

Set Primitive Projections.

Section Sigma.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Forcing Translate sigT using Obj Hom.

Definition sig_rec : forall A (B:A -> Type) P, (forall a:A, B a -> P) -> sigT B -> P :=
  fun A B P f x => match x with existT _ a b => f a b end.

Forcing Translate sig_rec using Obj Hom.

Definition sig_mem A (B:A -> Type) : forall R, sigT B -> (sigT B -> R) -> R:=
  fun R x => sig_rec A B (({x : A & B x} -> R) -> R) (fun a b k => k (existT _ a b)) x.

Forcing Translate sig_mem using Obj Hom.

Definition sig_rect : forall A (B:A -> Type) P,
    (forall (a:A) (b: B a), P (existT _ a b)) -> forall (x : sigT B), sig_mem A B _ x P :=
fun A B P f x => match x with
              | existT _ a b => f a b
              end.

Forcing Translate sig_rect using Obj Hom.


End Sigma.
