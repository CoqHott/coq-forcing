Require Forcing.

Section List.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).


Inductive list_ (p : Obj) (A : forall q (f : p ≤ q), Type) : Type :=
| nil_ : list_ p A
| cons_ : (forall q f, A q f) -> (forall q (f : p ≤ q), list_ q (fun r g => A r (f ∘ g))) -> list_ p A.

Forcing Definition list : Type -> Type using Obj Hom.
Proof.
intros p A q f.
exact (list_ q (fun r g => A r (f ∘ g) r #)).
Defined.


Forcing Definition nil : forall A, list A using Obj Hom.
Proof.
intros.
apply nil_.
Defined.

Forcing Definition cons : forall A, A -> list A -> list A using Obj Hom.
Proof.
intros p A x l.
apply cons_.
+ intros r g. apply x.
+ intros r g. apply l.
Defined.

Definition list_rec_ := 
(fun (p : Obj) (A P : forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type)
   (H0 : forall (p0 : Obj) (α : p ≤ p0), P p0 (# ∘ (α ∘ #)) p0 #)
   (HS : forall (p0 : Obj) (α : p ≤ p0),
         (forall (p1 : Obj) (α0 : p0 ≤ p1), A p1 (# ∘ (# ∘ (# ∘ (α ∘ (# ∘ (α0 ∘ #)))))) p1 #) ->
         (forall (p1 : Obj) (α0 : p0 ≤ p1), P p1 (# ∘ (# ∘ (α ∘ (# ∘ (# ∘ (α0 ∘ #)))))) p1 #) ->
         P p0 (# ∘ (# ∘ (α ∘ (# ∘ (# ∘ #))))) p0 #)
   (n : forall (p0 : Obj) (α : p ≤ p0),
        ᶠlist p0 (fun (p1 : Obj) (α0 : p0 ≤ p1) => A p1 (# ∘ (# ∘ (# ∘ (# ∘ (α ∘ (α0 ∘ #))))))) p0 #) =>
 (fun H : forall (q : Obj) (f : p ≤ q), P q f q # => (fun X : forall (q : Obj) (f : p ≤ q), P q f q # => X p #) H)
   (fun (q : Obj) (f : p ≤ q) =>
    (fun n0 : list_ q (fun (r : Obj) (g : q ≤ r) => A r (f ∘ g) r #) =>
     let A0 := fun (r : Obj) (g : q ≤ r) => A r (f ∘ g) r # in
     let HeqA0 := eq_refl in
     list__rect
       (fun (q0 : Obj) (A1 : forall q1 : Obj, q0 ≤ q1 -> Type) (_ : list_ q0 A1) =>
        forall f0 : p ≤ q0, A1 = (fun (r : Obj) (g : q0 ≤ r) => A r (f0 ∘ g) r #) -> P q0 f0 q0 #)
       (fun (p0 : Obj) (A1 : forall q0 : Obj, p0 ≤ q0 -> Type) (f0 : p ≤ p0)
          (_ : A1 = (fun (r : Obj) (g : p0 ≤ r) => A r (f0 ∘ g) r #)) => H0 p0 f0)
       (fun (p0 : Obj) (A1 : forall q0 : Obj, p0 ≤ q0 -> Type) (a : forall (q0 : Obj) (f0 : p0 ≤ q0), A1 q0 f0)
          (l : forall (q0 : Obj) (f0 : p0 ≤ q0), list_ q0 (fun (r : Obj) (g : q0 ≤ r) => A1 r (f0 ∘ g)))
          (X : forall (q0 : Obj) (f0 : p0 ≤ q0) (f1 : p ≤ q0),
               (fun (r : Obj) (g : q0 ≤ r) => A1 r (f0 ∘ g)) = (fun (r : Obj) (g : q0 ≤ r) => A r (f1 ∘ g) r #) ->
               P q0 f1 q0 #) (f0 : p ≤ p0) (HeqA1 : A1 = (fun (r : Obj) (g : p0 ≤ r) => A r (f0 ∘ g) r #)) =>
        HS p0 f0
          (fun (p1 : Obj) (α : p0 ≤ p1) =>
           (fun HeqA2 : (fun (r : Obj) (g : p0 ≤ r) => A r (f0 ∘ g) r #) = A1 =>
            match
              HeqA2 in (_ = y)
              return
                ((forall (q0 : Obj) (f1 : p0 ≤ q0), y q0 f1) ->
                 (forall (q0 : Obj) (f1 : p0 ≤ q0), list_ q0 (fun (r : Obj) (g : q0 ≤ r) => y r (f1 ∘ g))) ->
                 (forall (q0 : Obj) (f1 : p0 ≤ q0) (f2 : p ≤ q0),
                  (fun (r : Obj) (g : q0 ≤ r) => y r (f1 ∘ g)) = (fun (r : Obj) (g : q0 ≤ r) => A r (f2 ∘ g) r #) ->
                  P q0 f2 q0 #) -> A p1 (f0 ∘ α) p1 #)
            with
            | eq_refl =>
                fun (a0 : forall (q0 : Obj) (f1 : p0 ≤ q0), A q0 (f0 ∘ f1) q0 #)
                  (_ : forall (q0 : Obj) (f1 : p0 ≤ q0),
                       list_ q0
                         (fun (r : Obj) (g : q0 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => f0 R (f1 R (g R k))) r #))
                  (_ : forall (q0 : Obj) (f1 : p0 ≤ q0) (f2 : p ≤ q0),
                       (fun (r : Obj) (g : q0 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => f0 R (f1 R (g R k))) r #) =
                       (fun (r : Obj) (g : q0 ≤ r) => A r (f2 ∘ g) r #) -> P q0 f2 q0 #) => 
                a0 p1 α
            end a l X) (eq_sym HeqA1))
          (fun (r : Obj) (g : p0 ≤ r) =>
           (fun HeqA2 : (fun (r0 : Obj) (g0 : p0 ≤ r0) => A r0 (f0 ∘ g0) r0 #) = A1 =>
            match
              HeqA2 in (_ = y)
              return
                ((forall (q0 : Obj) (f1 : p0 ≤ q0), y q0 f1) ->
                 (forall (q0 : Obj) (f1 : p0 ≤ q0), list_ q0 (fun (r0 : Obj) (g0 : q0 ≤ r0) => y r0 (f1 ∘ g0))) ->
                 (forall (q0 : Obj) (f1 : p0 ≤ q0) (f2 : p ≤ q0),
                  (fun (r0 : Obj) (g0 : q0 ≤ r0) => y r0 (f1 ∘ g0)) =
                  (fun (r0 : Obj) (g0 : q0 ≤ r0) => A r0 (f2 ∘ g0) r0 #) -> P q0 f2 q0 #) -> 
                 P r (f0 ∘ g) r #)
            with
            | eq_refl =>
                fun (_ : forall (q0 : Obj) (f1 : p0 ≤ q0), A q0 (f0 ∘ f1) q0 #)
                  (_ : forall (q0 : Obj) (f1 : p0 ≤ q0),
                       list_ q0
                         (fun (r0 : Obj) (g0 : q0 ≤ r0) =>
                          A r0 (fun (R : Obj) (k : Hom r0 R) => f0 R (f1 R (g0 R k))) r0 #))
                  (X0 : forall (q0 : Obj) (f1 : p0 ≤ q0) (f2 : p ≤ q0),
                        (fun (r0 : Obj) (g0 : q0 ≤ r0) =>
                         A r0 (fun (R : Obj) (k : Hom r0 R) => f0 R (f1 R (g0 R k))) r0 #) =
                        (fun (r0 : Obj) (g0 : q0 ≤ r0) => A r0 (f2 ∘ g0) r0 #) -> P q0 f2 q0 #) =>
                X0 r g (f0 ∘ g) eq_refl
            end a l X) (eq_sym HeqA1))) q A0 n0 f HeqA0) (n q f)))
.

Forcing Definition list_rec : forall A (P : Type), P -> (A -> P -> P) -> list A -> P using Obj Hom.
Proof.
exact list_rec_.
Defined.

Definition foo := fun A (P : Type) (H0 : P) (HS : A -> P -> P) => list_rec A P H0 HS (nil A).
Definition bar := fun A (P : Type) (H0 : P) (HS : A -> P -> P) (x : A) (l : list A) => list_rec A P H0 HS (cons A x l).
Definition qux := fun A (P : Type) (H0 : P) (HS : A -> P -> P) (x : A) (l : list A) => HS x (list_rec A P H0 HS l).

Forcing Translate foo using Obj Hom.
Forcing Translate bar using Obj Hom.
Forcing Translate qux using Obj Hom.

Eval compute in ᶠbar.
Eval compute in ᶠqux.

Fail Check (eq_refl : ᶠbar = ᶠqux).

Forcing Definition list_rec' : forall A (P : Type), P -> (A -> P -> P) -> list A -> P using Obj Hom.
Proof.
intros p A P H0 HS n.
compute in *.
cut (forall q f, P q f q #).
{ intros X. apply X. }

intros q f.
specialize (n q f).
remember (fun (r : Obj) (g : q ≤ r) => A r (f ∘ g) r #) as A0.
induction n.

+ apply H0.
+ apply HS.
- intros.
  apply eq_sym in HeqA0; destruct HeqA0.
  apply a.
- intros r g.
  apply eq_sym in HeqA0; destruct HeqA0.
  eapply (X r g (f ∘ g)).
reflexivity.
Fail Defined.
Abort.

End List.
