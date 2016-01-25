Require Forcing.

Section Bool.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Forcing Translate bool using Obj Hom.

Definition bool_rec : forall P, P -> P -> bool -> P :=
  fun P Ptt Pff b => match b with true => Ptt | false => Pff end.

Forcing Translate bool_rec using Obj Hom.


Definition bool_mem : forall R, bool -> (bool -> R) -> R :=
  fun R b => bool_rec ((bool -> R) -> R) (fun k => k true) (fun k => k false) b.

Forcing Translate bool_mem using Obj Hom.

Forcing Translate eq using Obj Hom.

Definition eta_eq : forall (b : bool), b = b :=
fun b => match b return b = b with true => eq_refl | false => eq_refl end.

Fail Forcing Translate eta_eq using Obj Hom.

Definition bool_rect : forall P,
    P true -> P false -> forall (b : bool), bool_mem _ b P :=
  fun P pt pf b => match b with
                | true => pt
                | false => pf
                end.

Forcing Translate bool_rect using Obj Hom.

End Bool.
