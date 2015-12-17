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
  exact O_. 
Defined.

Forcing Definition S : nat -> nat using Obj Hom.
Proof.
  exact S_. 
Defined.

Fixpoint nat_rec_ (p : Obj)
  (P : forall p0 : Obj, p ≤ p0 -> forall p : Obj, p0 ≤ p -> Type)
  (H0 : forall (p0 : Obj) (α : p ≤ p0),
       P p0 (fun (R : Obj) (k : Hom p0 R) => α R k) p0 #)
  (HS : forall (p0 : Obj) (α : p ≤ p0),
       (forall (p : Obj) (α0 : p0 ≤ p), P p (α ∘ α0) p #) ->
       P p0 (fun (R : Obj) (k : Hom p0 R) => α R k) p0 #)
  (n : nat_ p):
   P p # p # := match n with
            | O_ _ =>    H0 p #
            | S_ _ n0 => HS p #
                   (fun (p1 : Obj) (α1 : p ≤ p1) =>
                      nat_rec_ p1
                        (fun p1 f1 => P  p1 (α1 ∘ f1))
                        (fun p1 f1 => H0 p1 (α1 ∘ f1))
                        (fun p1 f1 => HS p1 (α1 ∘ f1))
                        (n0 p1 α1))
            end.


Forcing Definition nat_rec : forall (P : Type), P -> (P -> P) -> nat -> P using Obj Hom.
Proof.
  intros p P H0 HS n. 
  exact (nat_rec_ p P H0 HS (n p #)).
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

Definition nat_mem : forall R, nat -> (nat -> R) -> R :=
  fun R : Type =>
    nat_rec ((nat -> R) -> R) (fun f => f O)
            (fun H f => H (fun n => f (S n))).

Forcing Translate nat_mem using Obj Hom.

Forcing Definition nat_rect : forall (P : nat -> Type),
    P O ->
    (forall (n:nat), nat_mem _ n P -> nat_mem _ (S n) P) ->
    forall n : nat, nat_mem _ n P using Obj Hom.
Proof.
  intros p P H0 HS n. unfold ᶠnat_mem, ᶠnat_rec . set (n0 := n p #). clearbody n0; clear n.

  (* avoiding noise in the actual definition *)
  (* may be improved using LTac ? *)
  
  set (Type_of_P := fun p => forall p0 : Obj,
                  p ≤ p0 ->
                  (forall p : Obj, p0 ≤ p -> ᶠnat p p #) ->
                  forall p : Obj, p0 ≤ p -> Type).
  set (Type_of_H0 := fun p (P:Type_of_P p) => forall (p0 : Obj) (α : p ≤ p0),
       P p0 (# ∘ (α ∘ #)) (fun (p : Obj) (_ : p0 ≤ p) => ᶠO p) p0 #).
  set (Type_of_HS := fun p (P:Type_of_P p) => forall (p0 : Obj) (α : p ≤ p0)
         (n : forall p : Obj, p0 ≤ p -> ᶠnat p p #),
       (forall (p1 : Obj) (α0 : p0 ≤ p1),
        ᶠnat_mem p1
          (fun (p : Obj) (_ : p1 ≤ p) (p2 : Obj) (_ : p ≤ p2) =>
           forall p3 : Obj, p2 ≤ p3 -> Type)
          (fun (p : Obj) (α1 : p1 ≤ p) => n p (# ∘ (α0 ∘ (α1 ∘ #))))
          (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
           P p2 (# ∘ (# ∘ (α ∘ (# ∘ (# ∘ (α0 ∘ (α1 ∘ #)))))))) p1 
          #) ->
       ᶠnat_mem p0
         (fun (p : Obj) (_ : p0 ≤ p) (p1 : Obj) (_ : p ≤ p1) =>
          forall p2 : Obj, p1 ≤ p2 -> Type)
         (fun (p : Obj) (α0 : p0 ≤ p) =>
          ᶠS p
            (fun (p1 : Obj) (α1 : p ≤ p1) => n p1 (# ∘ (α0 ∘ (α1 ∘ #)))))
         (fun (p1 : Obj) (α0 : p0 ≤ p1) =>
          P p1 (α ∘ α0)) p0 
         #).
  set (Type_of_Goal := fun p (P:Type_of_P p) (H0:Type_of_H0 p P) (HS:Type_of_HS p P) n0 => nat_rec_ p
     (fun (p0 : Obj) (_ : p ≤ p0) (p1 : Obj) (_ : p0 ≤ p1) =>
      (forall p2 : Obj,
       p1 ≤ p2 ->
       (forall p3 : Obj, p2 ≤ p3 -> ᶠnat p3 p3 #) ->
       forall p3 : Obj, p2 ≤ p3 -> Type) ->
      forall p2 : Obj, p1 ≤ p2 -> Type)
     (fun (p0 : Obj) (_ : p ≤ p0)
        (f : forall p1 : Obj,
             p0 ≤ p1 ->
             (forall p2 : Obj, p1 ≤ p2 -> ᶠnat p2 p2 #) ->
             forall p2 : Obj, p1 ≤ p2 -> Type) =>
      f p0 # (fun (p1 : Obj) (_ : p0 ≤ p1) => ᶠO p1))
     (fun (p0 : Obj) (_ : p ≤ p0)
        (H : forall p1 : Obj,
             p0 ≤ p1 ->
             (forall p2 : Obj,
              p1 ≤ p2 ->
              (forall p3 : Obj, p2 ≤ p3 -> ᶠnat p3 p3 #) ->
              forall p3 : Obj, p2 ≤ p3 -> Type) ->
             forall p2 : Obj, p1 ≤ p2 -> Type)
        (f : forall p1 : Obj,
             p0 ≤ p1 ->
             (forall p2 : Obj, p1 ≤ p2 -> ᶠnat p2 p2 #) ->
             forall p2 : Obj, p1 ≤ p2 -> Type) =>
      H p0 #
        (fun (p1 : Obj) (α0 : p0 ≤ p1)
           (n : forall p2 : Obj, p1 ≤ p2 -> ᶠnat p2 p2 #) =>
         f p1 (fun (R : Obj) (k : Hom p1 R) => α0 R k)
           (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
            ᶠS p2 (fun (p3 : Obj) (α2 : p2 ≤ p3) => n p3 (α1 ∘ α2))))) n0
     (fun (p0 : Obj) (α : p ≤ p0) =>
      P p0 (fun (R : Obj) (k : Hom p0 R) => α R k)) p 
     #).

  (* Now the definition using a fixpoint *)
  
  exact ((fix F p 
              (P : Type_of_P p)
              (H0 : Type_of_H0 p P)
              (HS : Type_of_HS p P)
              (n0 : ᶠnat p p #) : Type_of_Goal p P H0 HS n0
             := match n0 with
            | O_ _ =>   H0 p #
            | S_ _ n => HS p # n
                   (fun (p1 : Obj) (α1 : p ≤ p1) =>
                      F p1
                        (fun p1 f1 => P  p1 (α1 ∘ f1))
                        (fun p1 f1 => H0 p1 (α1 ∘ f1))
                        (fun p1 f1 => HS p1 (α1 ∘ f1))
                        (n p1 α1)) end
          ) p P H0 HS n0).
Defined.


Definition bar2 := fun (P : nat -> Type) (H0 : P O)
    (HS : (forall (n:nat), nat_mem _ n P -> nat_mem _ (S n) P))
    (n : nat) => nat_rect P H0 HS (S n).
Definition qux2 := fun (P : nat -> Type) (H0 : P O)
    (HS : (forall (n:nat), nat_mem _ n P -> nat_mem _ (S n) P))
    (n : nat) => HS n (nat_rect P H0 HS n).

Forcing Translate bar2 using Obj Hom.
Forcing Translate qux2 using Obj Hom.

Eval compute in ᶠbar2.
Eval compute in ᶠqux2.

Check (eq_refl : ᶠbar2 = ᶠqux2).


End Nat.
