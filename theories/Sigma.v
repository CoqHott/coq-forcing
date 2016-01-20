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

Forcing Definition sig_rect' : forall A (B:A -> Type) P,
    (forall (a:A) (b: B a), P (existT _ a b)) -> forall (x : sigT B), sig_mem A B _ x P
                                                     using Obj Hom.
intros p A B P H x.
compute. generalize (x p #).
exact (fun x => match x with
        | existTᶠ _ _ _ a b => H p # a b
                end).
(* Universe issue *)
Show Proof.
Abort.

Forcing Definition sig_rect' : forall A (B:A -> Type) P,
    (forall (a:A) (b: B a), P (existT _ a b)) -> forall (x : sigT B), sig_mem A B _ x P
                                                     using Obj Hom.

exact (fun (p : Obj)
   (A : forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type)
   (B : forall (p0 : Obj) (α : p ≤ p0),
        (forall (p1 : Obj) (α0 : p0 ≤ p1),
         A p1 (# ∘ (α ∘ (# ∘ (α0 ∘ #)))) p1 #) ->
        forall p1 : Obj, p0 ≤ p1 -> Type)
   (P : forall (p0 : Obj) (α : p ≤ p0),
        (forall (p1 : Obj) (α0 : p0 ≤ p1),
         (fun
            (A0 : forall p2 : Obj,
                  p1 ≤ p2 -> forall p3 : Obj, p2 ≤ p3 -> Type)
            (P : forall (p2 : Obj) (α1 : p1 ≤ p2),
                 (forall (p3 : Obj) (α2 : p2 ≤ p3),
                  A0 p3 (α1 ∘ (# ∘ (α2 ∘ #))) p3 #) ->
                 forall p3 : Obj, p2 ≤ p3 -> Type) 
            (p2 : Obj) (α1 : p1 ≤ p2) =>
          sigTᶠ p2
            (fun (p3 : Obj) (α2 : p2 ≤ p3) => A0 p3 (α1 ∘ (α2 ∘ #)))
            (fun (p3 : Obj) (α2 : p2 ≤ p3) => P p3 (α1 ∘ (α2 ∘ #))))
           (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
            A p2 (# ∘ (# ∘ (α ∘ (# ∘ (α0 ∘ (α1 ∘ #)))))))
           (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
            B p2 (# ∘ (α ∘ (# ∘ (α0 ∘ (α1 ∘ #)))))) p1 
           #) -> forall p1 : Obj, p0 ≤ p1 -> Type)
   (H : forall (p0 : Obj) (α : p ≤ p0)
          (a : forall (p1 : Obj) (α0 : p0 ≤ p1),
               A p1 (# ∘ (# ∘ (# ∘ (α ∘ (# ∘ (α0 ∘ #)))))) p1 #)
          (b : forall (p1 : Obj) (α0 : p0 ≤ p1),
               B p1 (# ∘ (# ∘ (α ∘ (# ∘ (# ∘ (α0 ∘ #))))))
                 (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                  a p2 (# ∘ (α0 ∘ (α1 ∘ #)))) p1 
                 #),
        P p0 (# ∘ (α ∘ (# ∘ (# ∘ #))))
          (fun (p1 : Obj) (α0 : p0 ≤ p1) =>
           existTᶠ p1
             (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
              A p2 (# ∘ (# ∘ (# ∘ (α ∘ (# ∘ (# ∘ (α0 ∘ (α1 ∘ #)))))))))
             (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
              B p2 (# ∘ (# ∘ (α ∘ (# ∘ (# ∘ (α0 ∘ (α1 ∘ #))))))))
             (fun (p2 : Obj) (α1 : p1 ≤ p2) => a p2 (# ∘ (α0 ∘ (α1 ∘ #))))
             (fun (p2 : Obj) (α1 : p1 ≤ p2) => b p2 (α0 ∘ (α1 ∘ #)))) p0 
          #)
   (x : forall (p0 : Obj) (α : p ≤ p0),
        (fun
           (A0 : forall p1 : Obj,
                 p0 ≤ p1 -> forall p2 : Obj, p1 ≤ p2 -> Type)
           (P0 : forall (p1 : Obj) (α0 : p0 ≤ p1),
                 (forall (p2 : Obj) (α1 : p1 ≤ p2),
                  A0 p2 (α0 ∘ (# ∘ (α1 ∘ #))) p2 #) ->
                 forall p2 : Obj, p1 ≤ p2 -> Type) 
           (p1 : Obj) (α0 : p0 ≤ p1) =>
         sigTᶠ p1 (fun (p2 : Obj) (α1 : p1 ≤ p2) => A0 p2 (α0 ∘ (α1 ∘ #)))
           (fun (p2 : Obj) (α1 : p1 ≤ p2) => P0 p2 (α0 ∘ (α1 ∘ #))))
          (fun (p1 : Obj) (α0 : p0 ≤ p1) =>
           A p1 (# ∘ (# ∘ (# ∘ (# ∘ (α ∘ (α0 ∘ #)))))))
          (fun (p1 : Obj) (α0 : p0 ≤ p1) =>
           B p1 (# ∘ (# ∘ (# ∘ (α ∘ (α0 ∘ #)))))) p0 
          #) =>
 (fun
    x0 : sigTᶠ p
           (fun (p0 : Obj) (α : p ≤ p0) =>
            A p0 (fun (R : Obj) (k : Hom p0 R) => α R k))
           (fun (p0 : Obj) (α : p ≤ p0) =>
            B p0 (fun (R : Obj) (k : Hom p0 R) => α R k)) =>
  match
    x0 as x1
    return
      (match x1 with
       | existTᶠ _ _ _ a b =>
           fun
             k : forall (p0 : Obj) (α : p ≤ p0),
                 (forall (p1 : Obj) (α0 : p0 ≤ p1),
                  sigTᶠ p1
                    (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                     A p2
                       (fun (R : Obj) (k : Hom p2 R) =>
                        α R (α0 R (α1 R k))))
                    (fun (p2 : Obj) (α1 : p1 ≤ p2)
                       (x2 : forall (p3 : Obj) (α2 : p2 ≤ p3),
                             A p3
                               (fun (R : Obj) (k : Hom p3 R) =>
                                α R (α0 R (α1 R (α2 R k)))) p3 
                               #) =>
                     B p2
                       (fun (R : Obj) (k : Hom p2 R) =>
                        α R (α0 R (α1 R k)))
                       (fun (p3 : Obj) (α2 : p2 ≤ p3) =>
                        x2 p3 (fun (R : Obj) (k : Hom p3 R) => α2 R k)))) ->
                 forall p1 : Obj, p0 ≤ p1 -> Type =>
           k p #
             (fun (p0 : Obj) (α : p ≤ p0) =>
              existTᶠ p0 (fun (p1 : Obj) (α0 : p0 ≤ p1) => A p1 (α ∘ α0))
                (fun (p1 : Obj) (α0 : p0 ≤ p1)
                   (x2 : forall (p2 : Obj) (α1 : p1 ≤ p2),
                         A p2
                           (fun (R : Obj) (k0 : Hom p2 R) =>
                            α R (α0 R (α1 R k0))) p2 
                           #) =>
                 B p1 (α ∘ α0)
                   (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                    x2 p2 (fun (R : Obj) (k0 : Hom p2 R) => α1 R k0)))
                (fun (p1 : Obj) (α0 : p0 ≤ p1) => a p1 (α ∘ α0))
                (fun (p1 : Obj) (α0 : p0 ≤ p1) => b p1 (α ∘ α0)))
       end
         (fun (p0 : Obj) (α : p ≤ p0) =>
          P p0 (fun (R : Obj) (k : Hom p0 R) => α R k)) p 
         #)
  with
  | existTᶠ _ _ _ a b => H p # a b
  end) (x p #)).
Defined. 

End Sigma.
