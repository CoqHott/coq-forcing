Require Forcing.

Section Bool.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Forcing Translate bool using Obj Hom.

Forcing Definition bool_rec : forall P, P -> P -> bool -> P using Obj Hom.
Proof.
intros p P Ptt Pff b.
destruct (b p #); [apply Ptt|apply Pff].
Defined.

Definition bool_mem : forall R, bool -> (bool -> R) -> R :=
  fun R b => bool_rec ((bool -> R) -> R) (fun k => k true) (fun k => k false) b.

Forcing Translate bool_mem using Obj Hom.

Forcing Definition bool_rect : forall P,
  P true -> P false -> forall b, bool_mem _ b P using Obj Hom.
Proof.
intros p P Ptt Pff b.
compute.
destruct (b p #); [apply Ptt|apply Pff].
Fail Defined. (** stupid universe errors *)
Abort.

End Bool.
