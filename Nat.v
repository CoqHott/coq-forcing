Require Forcing.

Section Nat.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).


Inductive nat_ (p : Obj) : Type :=
| O_ : nat_ p
| S_ : (forall r (g : p ≤ r), nat_ r) -> nat_ p.

Forcing Definition nat : Type using Obj Hom.
Proof.
intros p q f.
exact (nat_ q).
Defined.

Forcing Definition O : nat using Obj Hom.
Proof.
intros.
apply O_.
Defined.

Forcing Definition S : nat -> nat using Obj Hom.
Proof.
intros p n.
apply S_.
apply n.
Defined.

Forcing Definition nat_rec : forall (P : Type), P -> (P -> P) -> nat -> P using Obj Hom.
Proof.
  intros p P H0 HS n. compute in *.

  exact ((fix F (p' : Obj)
              (P :  forall p0 : Obj, p' ≤ p0 -> forall p : Obj, p0 ≤ p -> Type)
              (H0 : forall (p0 : Obj) (α : p' ≤ p0), P p0 α p0 #)
              (HS:  forall (p0 : Obj) (α : p' ≤ p0),
                    (forall (p : Obj) (α0 : p0 ≤ p), P p (α ∘ α0) p #) -> P p0 α p0 #)
              (n : nat_ p') {struct n} : P p' # p' # :=
            match n with
            | O_ _ =>    H0 p' #
            | S_ _ n0 => HS p' #
                   (fun (p1 : Obj) (α1 : p' ≤ p1) =>
                      F p1
                        (fun p1 f1 => P  p1 (α1 ∘ f1))
                        (fun p1 f1 => H0 p1 (α1 ∘ f1))
                        (fun p1 f1 => HS p1 (α1 ∘ f1))
                        (n0 p1 α1))
            end) p P H0 HS (n p #)).
Defined.

Definition foo := fun (P : Type) (H0 : P) (HS : P -> P) => nat_rec P H0 HS O.
Definition bar := fun (P : Type) (H0 : P) (HS : P -> P) (n : nat) => nat_rec P H0 HS (S n).
Definition qux := fun (P : Type) (H0 : P) (HS : P -> P) (n : nat) => HS (nat_rec P H0 HS n).

Forcing Translate foo using Obj Hom.
Forcing Translate bar using Obj Hom.
Forcing Translate qux using Obj Hom.

Eval compute in ᶠbar.
Eval compute in ᶠqux.

Check (eq_refl : ᶠbar = ᶠqux).

End Nat.
