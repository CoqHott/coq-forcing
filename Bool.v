Require Forcing.

Section Bool.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Inductive ᶠᶠbool p : forall q, p ≤ q -> Type :=
| ᶠᶠtrue : ᶠᶠbool p p #
| ᶠᶠfalse : ᶠᶠbool p p #.

Forcing Definition bool : Type using Obj Hom.
Admitted.

Forcing Definition true : bool using Obj Hom.
Admitted.

Forcing Definition false : bool using Obj Hom.
Admitted.

Forcing Definition bool_rect : forall P,
  P true -> P false -> forall b, P b using Obj Hom.
Proof.
intros p P Ptt Pff b.
change (P p # b p #).
Abort.

End Bool.
