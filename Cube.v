Set Primitive Projections.
Set Universe Polymorphism.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

CoInductive Glob : Type :=
  { obj : Type ;
    eq : forall x y : obj, Glob}.

CoInductive elt (G:Glob): Type :=
  { here : G.(obj) ;
    next : elt (G.(eq) here here)}.

Definition Cubical : Type := { G : Glob & forall x, elt (G.(eq) x x)}. 

(* CoInductive hom (X Y : Glob) : Type := *)
(*   { Gfun : X.(obj) -> Y.(obj); *)
(*     Gfun_next : forall x x': X.(obj), hom (X.(eq) x x') (Y.(eq) (Gfun x) (Gfun x'))}. *)

(* Definition IsEqual X Y (f g : hom X Y) (x:X.(obj)) : Glob := *)
(*     Y.(eq) (f.(Gfun _ _) x) (g.(Gfun _ _) x).  *)

CoFixpoint _Typeᶠ : Glob := Build_Glob Glob (fun _ _ => _Typeᶠ).  

Definition Typeᶠ : Cubical.
Proof.
  refine (existT _ _Typeᶠ _).
  intros x. cofix. refine (Build_elt _Typeᶠ x Typeᶠ).
Defined. 

CoFixpoint Prodᶠ (A:Glob) (B : elt A -> Typeᶠ.1.(obj)) : Glob :=
  Build_Glob (forall x: elt A, (B x).(obj))
             (fun f g => Prodᶠ A (fun x => (B x).(eq) (f x) (g x))).  

CoFixpoint Lamᶠ (A:Glob) (B : elt A -> Typeᶠ.1.(obj)) (t: forall x: elt A, elt (B x)) :
  elt (Prodᶠ A B).
refine (Build_elt (Prodᶠ A B) (fun x => (t x).(here _)) _).
cbn. apply Lamᶠ. intros x. apply ((t x).(next _)).
Defined. 

Definition Appᶠ (A:Glob) (B : elt A -> Typeᶠ.1.(obj)) 
           (f : elt (Prodᶠ A B)) : forall (x : elt A), elt (B x).
intro x; revert B f. cofix.  intros B f. 
simple refine (Build_elt (B x) (f.(here _) x) _).
apply (Appᶠ (fun x => (eq (B x) (here (Prodᶠ A B) f x) (here (Prodᶠ A B) f x)))).
apply (f.(next _)). 
Defined. 

CoFixpoint etaᶠ (A:Glob) : elt A -> elt A :=
  fun x => Build_elt _ x.(here _) (etaᶠ _ x.(next _)).

Definition eta_lawᶠ :
  (forall (A:Glob) x, etaᶠ A x = x) ->
   forall (A:Glob) x, (etaᶠ A x).(next _) = x.(next _).
Proof.
  intros e A x.
  exact (e (eq A (here A (etaᶠ A x)) (here A (etaᶠ A x))) (next A x)). 
Defined. 

Definition AppLam_idᶠ (A:Glob) 
           (t: forall x: elt A, elt A := fun x => x) (x:elt A) : Appᶠ _ _ (Lamᶠ _ _ t) x =
                                                  t x.
Proof.
  lazy. 
Abort.

Definition AppLamᶠ (A:Glob) (B : elt A -> Typeᶠ.1.(obj)) 
           (t: forall x: elt A, elt (B x)) (x:elt A) : (Appᶠ _ _ (Lamᶠ _ _ t) x).(here _) =
                                                  (t x).(here _).
Proof.
  reflexivity.
Defined.

Definition AppLam_nextᶠ (A:Glob) (B : elt A -> Typeᶠ.1.(obj)) (x:elt A)
           (t: forall x: elt A, elt (B x)) 
  (e : forall (B : elt A -> Typeᶠ.1.(obj))
          (t: forall x: elt A, elt (B x)) , Appᶠ _ _ (Lamᶠ _ _ t) x = t x) :
  (Appᶠ _ _ (Lamᶠ _ _ t) x).(next _) =
  (t x).(next _).          
  exact (e 
           (fun x0 : elt A =>
              eq (B x0) (here (Prodᶠ A B) (Lamᶠ A B t) x0)
                 (here (Prodᶠ A B) (Lamᶠ A B t) x0))
           (fun x0 : elt A => next (B x0) (t x0))).
Defined. 


Definition Bangᶠ (A:Cubical) (t:A.1.(obj)) : elt A.1 := Build_elt A.1 t (A.2 t).

(*

Definition Obj := nat.
Axiom Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Axiom ε : forall n, n ≤ S n.
Axiom δ₀ δ₁ : forall n, S n ≤ n.


Record Typeᶠ@{i} p := cType {
  type : forall p0 (α : p ≤ p0), Type@{i};
  path :
    (forall p0 (α : p ≤ p0), type (S p0) (α ∘ ε p0)) ->
    (forall p0 (α : p ≤ p0), type p0 (α ∘ ε p0 ∘ δ₀ p0)) ->
    (forall p0 (α : p ≤ p0), type p0 (α ∘ ε p0 ∘ δ₁ p0)) ->
    Type@{i};
}.

Definition mkTypeᶠ@{i j} p : Typeᶠ@{j} p.
Proof.
simple refine (cType@{j} p _ _).
+ refine (fun p0 α => Typeᶠ@{i} p).
+ intros e x y.  exact Prop.
Defined.

Definition mkProdᶠ@{i j k} p
  (A : forall p0 (α : p ≤ p0), Typeᶠ@{i} p0)
  (B : forall p0 (α : p ≤ p0), (forall p1 (α0 : p0 ≤ p1), (A p1 (α ∘ α0)).(type _) p1 #) -> Typeᶠ@{j} p0)
  : Typeᶠ@{k} p.
Proof.
refine (cType@{k} p _ _).
+ refine (fun p0 α => forall x : (forall p1 α0, (A p1 (α ∘ α0)).(type _) p1 #), (B p0 α x).(type _) p0 #).
+ intros.
  exact Prop.
Defined.
*)