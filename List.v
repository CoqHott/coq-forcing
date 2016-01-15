Require Forcing.

Section List.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Forcing Translate list using Obj Hom.

Fixpoint list_rec_ p
         (A P : forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type)
         (Hnil : forall (p0 : Obj) (α : p ≤ p0), P p0 α p0 #)
         (Hcons: forall (p0 : Obj) (α : p ≤ p0),
             (forall (p : Obj) (α0 : p0 ≤ p), A p (α ∘ α0) p #) ->
             (forall (p1 : Obj) (α0 : p0 ≤ p1),
                 ᶠlist p1 (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                             A p2 (α ∘ (α0 ∘ α1)))) ->
             (forall (p : Obj) (α0 : p0 ≤ p), P p (α ∘ α0) p #) ->
             P p0 α p0 #)
         (l : ᶠlist p A) {struct l} : P p # p # :=
            match l with
            | ᶠnil _ _ =>       Hnil p #
            | ᶠcons _ _ ny ll => Hcons p # ny ll
                   (fun (p1 : Obj) (α1 : p ≤ p1) =>
                      list_rec_ p1 
                        (fun p1 f1 => A     p1 (α1 ∘ f1))
                        (fun p1 f1 => P     p1 (α1 ∘ f1))
                        (fun p1 f1 => Hnil  p1 (α1 ∘ f1))
                        (fun p1 f1 => Hcons p1 (α1 ∘ f1))
                        (ll p1 α1))
            end.
 

Forcing Definition list_rec : forall A (P : Type), P -> (A -> list A -> P -> P) -> list A -> P using Obj Hom.
Proof.
  intros p A P Hnil Hcons l.
  exact (list_rec_ p A P Hnil Hcons (l p #)).
Defined.

Definition bar := fun A (P : Type) (H0 : P) (HS : A -> list A -> P -> P) (x : A) (l : list A) => list_rec A P H0 HS (cons x l).

Definition qux := fun A (P : Type) (H0 : P) (HS : A -> list A -> P -> P) (x : A) (l : list A) => HS x l (list_rec A P H0 HS l).

Forcing Translate bar using Obj Hom.
Forcing Translate qux using Obj Hom.

Eval compute in ᶠbar.
Eval compute in ᶠqux.

Check (eq_refl : ᶠbar = ᶠqux).

Definition list_mem : forall A R, list A -> (list A -> R) -> R :=
  fun A R : Type =>
    list_rec A ((list A -> R) -> R) (fun f => f nil)
             (fun a _ H f => H (fun ll => f (cons a ll))).

Forcing Translate list_mem using Obj Hom.

Forcing Definition list_rect : forall A (P : list A -> Type),
    P nil ->
    (forall (a:A) (l:list A), list_mem _ _ l P -> list_mem _ _ (cons a l) P) ->
    forall l : list A, list_mem _ _ l P using Obj Hom.
Proof.
  simpl; intros p A P Hnil Hcons l. 

  (* avoiding noise in the actual definition *)
  (* may be improved using LTac ? *)
  
  pose (Type_of_A := fun p => forall p0 : Obj, p ≤ p0 -> forall p : Obj, p0 ≤ p -> Type). 
  pose (Type_of_P := fun p (A : Type_of_A p) => forall (p0 : Obj) (α : p ≤ p0),
      (forall (p1 : Obj) (α0 : p0 ≤ p1),
       ᶠlist p1
         (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
          A p2 (# ∘ (α ∘ (# ∘ (α0 ∘ (α1 ∘ #))))))) -> forall p : Obj, p0 ≤ p -> Type).
  pose (Type_of_Hnil := fun p (A : Type_of_A p) (P : Type_of_P p A) =>
                          forall (p0 : Obj) (α : p ≤ p0),
         P p0 (fun (R : Obj) (k : Hom p0 R) => α R k)
           (fun (p : Obj) (α0 : p0 ≤ p) =>
            ᶠnil p
              (fun (p1 : Obj) (α1 : p ≤ p1) =>
               A p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k)))))
           p0 #).
  pose (Type_of_Hcons := fun p (A : Type_of_A p) (P : Type_of_P p A) =>
                           forall (p0 : Obj) (α : p ≤ p0)
            (a : forall (p : Obj) (α0 : p0 ≤ p), A p (α ∘ α0) p #)
            (l : forall (p : Obj) (α0 : p0 ≤ p),
                 ᶠlist p
                   (fun (p1 : Obj) (α1 : p ≤ p1) =>
                    A p1
                      (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))),
          (forall (p : Obj) (α0 : p0 ≤ p),
           ᶠlist_mem p
             (fun (p1 : Obj) (α1 : p ≤ p1) =>
              A p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))
             (fun (p1 : Obj) (_ : p ≤ p1) (p2 : Obj) (_ : p1 ≤ p2) =>
              forall p3 : Obj, p2 ≤ p3 -> Type)
             (fun (p1 : Obj) (α1 : p ≤ p1) => l p1 (α0 ∘ α1))
             (fun (p1 : Obj) (α1 : p ≤ p1) =>
              P p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))
             p #) ->
          ᶠlist_mem p0 (fun (p : Obj) (α0 : p0 ≤ p) => A p (α ∘ α0))
            (fun (p : Obj) (_ : p0 ≤ p) (p1 : Obj) (_ : p ≤ p1) =>
             forall p2 : Obj, p1 ≤ p2 -> Type)
            (fun (p : Obj) (α0 : p0 ≤ p) =>
             ᶠcons p
               (fun (p1 : Obj) (α1 : p ≤ p1) =>
                A p1 (fun (R : Obj) (k : Hom p1 R) => α R (α0 R (α1 R k))))
               (fun (p1 : Obj) (α1 : p ≤ p1) => a p1 (α0 ∘ α1))
               (fun (p1 : Obj) (α1 : p ≤ p1) => l p1 (α0 ∘ α1)))
            (fun (p : Obj) (α0 : p0 ≤ p) => P p (α ∘ α0)) p0 
            #).

  pose (Goal_Type := fun  p (A : Type_of_A p) (P : Type_of_P p A)
              (Hnil : Type_of_Hnil p A P)
              (Hcons : Type_of_Hcons p A P)
              (l0 : ᶠlist p A) =>
(fix
 list_rec_ (p0 : Obj) (A0 P0 : forall p1 : Obj, p0 ≤ p1 -> forall p2 : Obj, p1 ≤ p2 -> Type)
           (Hnil0 : forall (p1 : Obj) (α : p0 ≤ p1), P0 p1 α p1 #)
           (Hcons0 : forall (p1 : Obj) (α : p0 ≤ p1),
                     (forall (p2 : Obj) (α0 : p1 ≤ p2), A0 p2 (α ∘ α0) p2 #) ->
                     (forall (p2 : Obj) (α0 : p1 ≤ p2),
                      ᶠlist p2
                        (fun (r : Obj) (g : p2 ≤ r) => A0 r (fun (R : Obj) (k : Hom r R) => α R (α0 R (g R k))))) ->
                     (forall (p2 : Obj) (α0 : p1 ≤ p2), P0 p2 (α ∘ α0) p2 #) -> P0 p1 α p1 #)
           (l : ᶠlist p0 (fun (r : Obj) (g : p0 ≤ r) => A0 r (fun (R : Obj) (k : Hom r R) => g R k))) {struct l} :
   P0 p0 # p0 # :=
   match l with
   | ᶠnil _ _ => Hnil0 p0 #
   | ᶠcons _ _ ny ll =>
       Hcons0 p0 # ny ll
         (fun (p1 : Obj) (α1 : p0 ≤ p1) =>
          list_rec_ p1 (fun (p2 : Obj) (f1 : p1 ≤ p2) => A0 p2 (α1 ∘ f1))
            (fun (p2 : Obj) (f1 : p1 ≤ p2) => P0 p2 (α1 ∘ f1))
            (fun (p2 : Obj) (f1 : p1 ≤ p2) => Hnil0 p2 (α1 ∘ f1))
            (fun (p2 : Obj) (f1 : p1 ≤ p2) => Hcons0 p2 (α1 ∘ f1)) (ll p1 α1))
   end) p (fun (p0 : Obj) (α : p ≤ p0) => A p0 (fun (R : Obj) (k : Hom p0 R) => α R k))
  (fun (p0 : Obj) (α : p ≤ p0) (p1 : Obj) (α0 : p0 ≤ p1) =>
   (forall (p2 : Obj) (α1 : p1 ≤ p2),
    (forall (p3 : Obj) (α2 : p2 ≤ p3),
     ᶠlist p3
       (fun (r : Obj) (g : p3 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (α1 R (α2 R (g R k))))))) ->
    forall p3 : Obj, p2 ≤ p3 -> Type) -> forall p2 : Obj, p1 ≤ p2 -> Type)
  (fun (p0 : Obj) (α : p ≤ p0)
     (f : forall (p1 : Obj) (α0 : p0 ≤ p1),
          (forall (p2 : Obj) (α1 : p1 ≤ p2),
           ᶠlist p2
             (fun (r : Obj) (g : p2 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (α1 R (g R k)))))) ->
          forall p2 : Obj, p1 ≤ p2 -> Type) =>
   f p0 #
     (fun (p1 : Obj) (α0 : p0 ≤ p1) =>
      ᶠnil p1 (fun (r : Obj) (g : p1 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (g R k))))))
  (fun (p0 : Obj) (α : p ≤ p0) (a : forall (p1 : Obj) (α0 : p0 ≤ p1), A p1 (α ∘ α0) p1 #)
     (_ : forall (p1 : Obj) (α0 : p0 ≤ p1),
          ᶠlist p1 (fun (r : Obj) (g : p1 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (g R k)))))
     (H : forall (p1 : Obj) (α0 : p0 ≤ p1),
          (forall (p2 : Obj) (α1 : p1 ≤ p2),
           (forall (p3 : Obj) (α2 : p2 ≤ p3),
            ᶠlist p3
              (fun (r : Obj) (g : p3 ≤ r) =>
               A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (α1 R (α2 R (g R k))))))) ->
           forall p3 : Obj, p2 ≤ p3 -> Type) -> forall p2 : Obj, p1 ≤ p2 -> Type)
     (f : forall (p1 : Obj) (α0 : p0 ≤ p1),
          (forall (p2 : Obj) (α1 : p1 ≤ p2),
           ᶠlist p2
             (fun (r : Obj) (g : p2 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (α1 R (g R k)))))) ->
          forall p2 : Obj, p1 ≤ p2 -> Type) =>
   H p0 #
     (fun (p1 : Obj) (α0 : p0 ≤ p1)
        (ll : forall (p2 : Obj) (α1 : p1 ≤ p2),
              ᶠlist p2
                (fun (r : Obj) (g : p2 ≤ r) => A r (fun (R : Obj) (k : Hom r R) => α R (α0 R (α1 R (g R k))))))
      =>
      f p1 (fun (R : Obj) (k : Hom p1 R) => α0 R k)
        (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
         ᶠcons p2
           (fun (p3 : Obj) (α2 : p2 ≤ p3) => A p3 (fun (R : Obj) (k : Hom p3 R) => α R (α0 R (α1 R (α2 R k)))))
           (fun (p3 : Obj) (α2 : p2 ≤ p3) => a p3 (fun (R : Obj) (k : Hom p3 R) => α0 R (α1 R (α2 R k))))
           (fun (p3 : Obj) (α2 : p2 ≤ p3) => ll p3 (α1 ∘ α2))))) l0
  (fun (p0 : Obj) (α : p ≤ p0) => P p0 (fun (R : Obj) (k : Hom p0 R) => α R k)) p #
).

  compute. set (l0 := l p #). clearbody l0; clear l.
  change (Goal_Type p A P Hnil Hcons l0).

  (* Now the definition using a fixpoint *)

  exact ((fix F p (A : Type_of_A p) (P : Type_of_P p A)
              (Hnil : Type_of_Hnil p A P)
              (Hcons : Type_of_Hcons p A P)
              (l0 : ᶠlist p A) : Goal_Type p A P Hnil Hcons l0   
         := 
            match l0 as l1 return Goal_Type _ _ _ _ _ l1 with
            | ᶠnil _ _ =>       Hnil p #
            | ᶠcons _ _ a ll => 
              Hcons p # a ll 
                   (fun (p1 : Obj) (α1 : p ≤ p1) =>
                      F p1
                        (fun p1 f1 => A     p1 (α1 ∘ f1))
                        (fun p1 f1 => P     p1 (α1 ∘ f1))
                        (fun p1 f1 => Hnil  p1 (α1 ∘ f1))
                        (fun p1 f1 => Hcons p1 (α1 ∘ f1))
                        (ll p1 α1)) end
          ) p A P Hnil Hcons l0).
Defined.

Definition bar2 := fun A (P : list A -> Type)
    (H0 : P nil)
    (HS : forall (a:A) (l:list A), list_mem _ _ l P -> list_mem _ _ (cons a l) P)
    x (l : list A) => list_rect A P H0 HS (cons x l).

Definition qux2 := fun A (P : list A -> Type)
    (H0 : P nil)
    (HS : forall (a:A) (l:list A), list_mem _ _ l P -> list_mem _ _ (cons a l) P)
    x (l : list A) => HS x l (list_rect A P H0 HS l).

Forcing Translate bar2 using Obj Hom.
Forcing Translate qux2 using Obj Hom.

Eval compute in ᶠbar2.
Eval compute in ᶠqux2.

Check (eq_refl : ᶠbar2 = ᶠqux2).

End List.
