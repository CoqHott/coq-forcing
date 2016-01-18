Require Forcing.

Section Eq.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

Definition eq_rec_ p
         (A P : forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type)
         (x : forall (p0 : Obj) (α : p ≤ p0),
      A p0 α p0 #) 
      (Hrefl : forall (p0 : Obj) (α : p ≤ p0), P p0 α p0 #) 
      (y:forall (p0 : Obj) (α : p ≤ p0),
          A p0 α _ #)
      (e : eqᶠ p A x y) : P p # p # :=
  match e with eq_reflᶠ _ _ _ => Hrefl p # end. 

Definition eq_rec_nd A (x : A) (P : Type) (p : P) y (e : x = y) : P := match e with eq_refl _ => p end.

Forcing Translate eq_rec_nd using Obj Hom.

Definition eq_mem : forall A x R, forall y, x = y ->
                                  (forall y, x = y -> R) -> R :=
  fun A x (R : Type) =>
    eq_rec_nd A x ((forall y, x = y -> R) -> R) (fun f => f x (eq_refl x)).

Forcing Translate eq_mem using Obj Hom.

Forcing Definition eq_rect' : forall A (x :A) (P : forall y, x = y -> Type),
    (* eq_mem _ _ _ _ (eq_refl x) P -> *)
    P x (eq_refl x) ->
    forall y (e:x = y), eq_mem _ _ _ _ e P using Obj Hom.
Proof.

    intros p A x P P_refl y e.

pose (Type_of_A := fun p => forall p0 : Obj, p ≤ p0 -> forall p : Obj, p0 ≤ p -> Type). 
  pose (Type_of_x := fun p (A:Type_of_A p) => forall p0 (α: p ≤ p0), A p0 α p0 #).
  pose (Type_of_P := fun p (A:Type_of_A p) (x:Type_of_x p A) =>
                       forall (p0 : Obj) (α : p ≤ p0)
        (y : forall (p : Obj) (α0 : p0 ≤ p), A p (α ∘ α0) p #),
      (forall (p : Obj) (α0 : p0 ≤ p),
       eqᶠ p
         (fun (p1 : Obj) (α1 : p ≤ p1) =>
          A p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))
         (fun (p1 : Obj) (α1 : p ≤ p1) =>
          x p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))
         (fun (p1 : Obj) (α1 : p ≤ p1) => y p1 (α0 ∘ α1))) ->
      forall p : Obj, p0 ≤ p -> Type).
  pose (Type_of_P_refl := fun p (A:Type_of_A p) (x:Type_of_x p A) (P:Type_of_P p A x) =>
      forall (p0 : Obj) (α : p ≤ p0),
         eq_memᶠ p0 (fun (p : Obj) (α0 : p0 ≤ p) => A p (α ∘ α0))
           (fun (p : Obj) (α0 : p0 ≤ p) => x p (α ∘ α0))
           (fun (p : Obj) (_ : p0 ≤ p) (p1 : Obj) (_ : p ≤ p1) =>
            forall p2 : Obj, p1 ≤ p2 -> Type)
           (fun (p : Obj) (α0 : p0 ≤ p) => x p (α ∘ α0))
           (fun (p : Obj) (α0 : p0 ≤ p) =>
            eq_reflᶠ p
              (fun (p1 : Obj) (α1 : p ≤ p1) =>
               A p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))
              (fun (p1 : Obj) (α1 : p ≤ p1) =>
               x p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k)))))
           (fun (p : Obj) (α0 : p0 ≤ p) => P p (α ∘ α0)) p0 
           #). 
  pose (Goal_Type := fun  p (A:Type_of_A p) (x:Type_of_x p A) (P:Type_of_P p A x)
              (P_refl : Type_of_P_refl p A x P) y
              (e0 : eqᶠ p A x y ) =>
                       eq_rec_ p
     (fun (p0 : Obj) (α : p ≤ p0) =>
      A p0 (fun (R : Obj) (k : Hom p0 R) => α R k))
     (fun (p0 : Obj) (α : p ≤ p0) (p1 : Obj) (α0 : p0 ≤ p1) =>
      (forall (p2 : Obj) (α1 : p1 ≤ p2)
         (y0 : forall (p3 : Obj) (α2 : p2 ≤ p3),
               A p3
                 (fun (R : Obj) (k : Hom p3 R) =>
                  α R (α0 R (α1 R (α2 R k)))) p3 
                 #),
       (forall (p3 : Obj) (α2 : p2 ≤ p3),
        eqᶠ p3
          (fun (p4 : Obj) (α3 : p3 ≤ p4) =>
           A p4
             (fun (R : Obj) (k : Hom p4 R) =>
              α R (α0 R (α1 R (α2 R (α3 R k))))))
          (fun (p4 : Obj) (α3 : p3 ≤ p4) =>
           x p4
             (fun (R : Obj) (k : Hom p4 R) =>
              α R (α0 R (α1 R (α2 R (α3 R k))))))
          (fun (p4 : Obj) (α3 : p3 ≤ p4) => y0 p4 (α2 ∘ α3)) )
       -> forall p3 : Obj, p2 ≤ p3 -> Type) ->
      forall p2 : Obj, p1 ≤ p2 -> Type)
     (fun (p0 : Obj) (α : p ≤ p0) =>
      x p0 (fun (R : Obj) (k : Hom p0 R) => α R k))
     (fun (p0 : Obj) (α : p ≤ p0)
        (f : forall (p1 : Obj) (α0 : p0 ≤ p1)
               (y0 : forall (p2 : Obj) (α1 : p1 ≤ p2),
                     A p2
                       (fun (R : Obj) (k : Hom p2 R) =>
                        α R (α0 R (α1 R k))) p2 #),
             (forall (p2 : Obj) (α1 : p1 ≤ p2),
              eqᶠ p2
                (fun (p3 : Obj) (α2 : p2 ≤ p3) =>
                 A p3
                   (fun (R : Obj) (k : Hom p3 R) =>
                    α R (α0 R (α1 R (α2 R k)))))
                (fun (p3 : Obj) (α2 : p2 ≤ p3) =>
                 x p3
                   (fun (R : Obj) (k : Hom p3 R) =>
                    α R (α0 R (α1 R (α2 R k)))))
                (fun (p3 : Obj) (α2 : p2 ≤ p3) => y0 p3 (α1 ∘ α2)) 
                ) -> forall p2 : Obj, p1 ≤ p2 -> Type) =>
      f p0 # (fun (p1 : Obj) (α0 : p0 ≤ p1) => x p1 (α ∘ α0))
        (fun (p1 : Obj) (α0 : p0 ≤ p1) =>
         eq_reflᶠ p1
           (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
            A p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R k))))
           (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
            x p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R k))))))
     y e0
     (fun (p0 : Obj) (α : p ≤ p0) =>
      P p0 (fun (R : Obj) (k : Hom p0 R) => α R k)) p 
     #).

  compute. set (e0 := e p #).
  clearbody e0; clear e. simpl.
  change (Goal_Type p A x P P_refl y e0).
  exact (match e0 as e1 return
               (* (match e0 with | ᶠeq_refl _ _ _ => _ end P p #)  *)
                 Goal_Type _ _ _ _ _ _ e1
                 with
            | eq_reflᶠ _ _ _ =>  P_refl p # end).
Defined. 
 
Forcing Definition leibniz : forall A (x :A) (P : A -> Type),
    P x ->
    forall y (e:x = y), P y using Obj Hom.
Proof.
  intros p A x P P_refl y e.
  exact (match e p # in eqᶠ _ _ _ y' return P p # y' p # 
         with | eq_reflᶠ _ _ _ => P_refl p # end).
Defined. 

Forcing Definition eq_rect_partial_refl : forall A (x :A) (P : A -> Type)
    (a : P x), leibniz A x P a x (eq_refl _) = a using Obj Hom.
Proof.
  intros. reflexivity.
Defined. 

End Eq.
