Set Primitive Projections.
Set Universe Polymorphism.

Axiom proof_admitted : forall {a}, a.
Tactic Notation "admit" := exact proof_admitted.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

CoInductive Glob : Type :=
  { obj : Type ;
    eq : forall x y : obj, Glob
  }.

CoInductive elt (G:Glob): Type :=
  { here : G.(obj) ;
    next : elt (G.(eq) here here)  }.

CoFixpoint Prodᶠ (A:Glob) (B : elt A -> Glob) : Glob :=
  Build_Glob (forall x: elt A, (B x).(obj))
             (fun f g => Prodᶠ A (fun x => ((B x).(eq) (f x) (g x)))).

CoFixpoint Lamᶠ (A:Glob) (B : elt A -> Glob) (t: forall x: elt A, elt (B x)) :
  elt (Prodᶠ A B).
refine (Build_elt (Prodᶠ A B) (fun x => (t x).(here _)) _).
cbn. apply Lamᶠ. intros x. apply ((t x).(next _)).
Defined. 

Definition Appᶠ (A:Glob) (B : elt A -> Glob) 
           (f : elt (Prodᶠ A B)) : forall (x : elt A), elt (B x).
intro x; revert B f. cofix.  intros B f. 
simple refine (Build_elt (B x) (f.(here _) x) _).
apply (Appᶠ (fun x => (eq (B x) (here (Prodᶠ A B) f x) (here (Prodᶠ A B) f x)))).
apply (f.(next _)). 
Defined. 

Record TypeEquiv (A B : Glob) : Type :=
  {
    equiv : elt (Prodᶠ A (fun _ => B)) ;
    equiv_inv : elt (Prodᶠ B (fun _ => A)) ;
    sect : forall x, (A.(eq) (Appᶠ _ _ equiv_inv (Appᶠ _ _ equiv x)).(here _) x.(here _)).(obj);
    retr : forall x, (B.(eq) (Appᶠ _ _ equiv (Appᶠ _ _ equiv_inv x)).(here _) x.(here _)).(obj);
    (* no adjunction required ? *)
  }.

Definition Equiv (A B : Glob) : Glob.
Proof.
  refine (Build_Glob (TypeEquiv A B) (fun f g => _)).
  exact (Prodᶠ A (fun x => (B.(eq) (Appᶠ _ _ f.(equiv _ _) x).(here _) (Appᶠ _ _ g.(equiv _ _) x).(here _)))).
Defined.

Definition Typeᶠ : Glob := Build_Glob Glob Equiv. 

Definition Id_fun A: elt (Prodᶠ A (fun _ => A)) := Lamᶠ A (fun _ => A) (fun x => x).  
    
Definition Identity (A:Glob) : TypeEquiv A A.
simple refine (Build_TypeEquiv _ _ (Id_fun A) (Id_fun A) _ _).
- intros. exact ((x.(next _)).(here _)).
- intros. exact ((x.(next _)).(here _)).
Defined. 
  
(*
Definition ID_eq (A:Glob) : elt
     (_Prodᶠ A .1 (fun x : elt A .1 => eq A .1 (here A .1 x) (here A .1 x))).
Proof.
  cbn in *. revert A. cofix. intro A. simple refine (Build_elt _ _ _).
    + cbn. intros x. exact (x.(next _).(here _)).
    + cbn. simple refine (Build_elt _ _ _).
      * cbn. intro x. exact (x.(next _).(next _).(here _)).
      * cbn. admit. 
Admitted. 
*)

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


Definition Bangᶠ (A:Glob) (t:A.1.(obj)) : elt A.1 := Build_elt A.1 t (A.2 t).

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