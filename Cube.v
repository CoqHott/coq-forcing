Set Primitive Projections.
Set Universe Polymorphism.

Axiom proof_admitted : forall {a}, a.
Tactic Notation "admit" := exact proof_admitted.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

(* CoInductive Glob : Type := *)
(*   glob : forall Obj : Type, (Obj -> Obj -> Glob) -> Glob *)
(* with *)
(*  Elt : Type :=  *)
(*   elt : forall (G:Glob) (here : match G with *)
(*                  | glob Obj _ => Obj *)
(*                  end), Elt (G.(eq) here here) -> Elt G. *)

CoInductive Glob : Type :=
  { obj : Type ;
    eq : forall x y : obj, Glob
  }.

CoInductive elt (G:Glob): Type :=
  { here : G.(obj) ;
    next : elt (G.(eq) here here)  }.

CoInductive IsCubical (G:Glob) : Type :=
  { refl : forall x, elt (G.(eq) x x);
    eq_cubical : forall x y, IsCubical (G.(eq) x y)}.

Definition Cubical : Type := { G : Glob & IsCubical G}.

(* CoInductive hom (X Y : Glob) : Type := *)
(*   { Gfun : X.(obj) -> Y.(obj); *)
(*     Gfun_next : forall x x': X.(obj), hom (X.(eq) x x') (Y.(eq) (Gfun x) (Gfun x'))}. *)

(* Definition IsEqual X Y (f g : hom X Y) (x:X.(obj)) : Glob := *)
(*     Y.(eq) (f.(Gfun _ _) x) (g.(Gfun _ _) x).  *)

CoFixpoint _Prodᶠ (A:Glob) (B : elt A -> Cubical) : Glob :=
  Build_Glob (forall x: elt A, (B x).1.(obj))
             (fun f g => _Prodᶠ A
        (fun x => ((B x).1.(eq) (f x) (g x); (B x).2.(eq_cubical _) (f x) (g x)))).  

Definition Prodᶠ_elt (A : Glob) : forall (Obj : elt A -> Type) (f : forall x : elt A, Obj x)
     (F : forall x : elt A, Obj x -> Obj x -> Glob),
   (forall (x : elt A) (e : Obj x), elt (F x e e)) ->
   forall G : forall (x : elt A) (e e' : Obj x), IsCubical (F x e e'),
     elt (_Prodᶠ A (fun x : elt A => (F x (f x) (f x); G x (f x) (f x)))).
  cofix. intros Obj f F G' G. simple refine (Build_elt _ _ _).
  + cbn. intro x. exact (G' _ _).(here _).
  + cbn.
    pose (_Obj := fun x => obj (F x (f x) (f x))).
    pose (_f := fun x => (here (F x (f x) (f x)) (G' x (f x))): _Obj x).
    pose (_F := fun x => eq (F x (f x) (f x))).
    pose (_G := fun x => eq_cubical (F x (f x) (f x)) (G x (f x) (f x))).
    pose (_G' := fun x => refl (F x (f x) (f x)) (G x (f x) (f x))).
    refine (Prodᶠ_elt _Obj _f _F _G' _G).
Defined. 

CoFixpoint Prodᶠ_cubical (A:Glob) (B : elt A -> Cubical) : IsCubical (_Prodᶠ A B).
econstructor.
- intro f. cbn in *. 
  set (Obj := fun x : elt A => obj (B x) .1).
  change (forall x : elt A, Obj x) in f. 
  set (F := fun x : elt A => eq (B x) .1 : Obj x -> Obj x -> Glob).
  set (G := fun x : elt A => eq_cubical (B x) .1 (B x) .2 : forall e e', IsCubical (F x e e')).
  set (G' := fun x : elt A => (B x).2.(refl _) : forall (e:Obj x), elt (F x e e)).
  refine (Prodᶠ_elt _ Obj f F G' G).
- intros f g. refine (Prodᶠ_cubical _ _).
Defined.

Definition Prodᶠ (A:Glob) (B : elt A -> Cubical) : Cubical :=
  (_Prodᶠ A B; Prodᶠ_cubical A B).


Record TypeEquiv (A B : Glob) : Type :=
  {
    equiv : A.(obj) -> B.(obj) ;
    equiv_inv : B.(obj) -> A.(obj) ;
    sect : forall x, (A.(eq) (equiv_inv (equiv x)) x).(obj);
    retr : forall x, (B.(eq) (equiv (equiv_inv x)) x).(obj);
    (* no adjunction required ? *)
  }.

Definition Equiv (A B : Cubical) : Cubical.
Proof.
  simple refine (existT _ _ _). 
  - refine (Build_Glob (TypeEquiv A.1 B.1) (fun f g => _)).
    exact (_Prodᶠ A.1 (fun x => (B.1.(eq) (f.(equiv _ _) x.(here _)) (g.(equiv _ _) x.(here _)); B.2.(eq_cubical _) _ _))).
  - cbn. refine (Build_IsCubical _ _ _).
    {
    cbn. intro e. simple refine (Build_elt _ _ _).
    + cbn. intro x. exact (B.2.(refl _) _).(here _).
    + exact ((Prodᶠ_cubical A.1 (fun x : elt A .1 =>
         (eq B .1 (equiv A .1 B .1 e (here A .1 x))
            (equiv A .1 B .1 e (here A .1 x));
         eq_cubical B .1 B .2 (equiv A .1 B .1 e (here A .1 x))
                    (equiv A .1 B .1 e (here A .1 x))))).(refl _) _).
    }
    {
      cbn. intros e e'.  exact (Prodᶠ_cubical _ _).
    }
Defined.

Definition _Typeᶠ : Glob := Build_Glob Cubical (fun A B => (Equiv A B).1).  

Definition Identity (A:Cubical) : TypeEquiv A.1 A.1.
simple refine (Build_TypeEquiv _ _ (fun x => x) (fun x => x) _ _).
- intros. exact ((A.2.(refl _) x).(here _)).
- intros. exact ((A.2.(refl _) x).(here _)).
Defined. 
  
(*
Definition ID_eq (A:Cubical) : elt
     (_Prodᶠ A .1 (fun x : elt A .1 => eq A .1 (here A .1 x) (here A .1 x))).
Proof.
  cbn in *. revert A. cofix. intro A. simple refine (Build_elt _ _ _).
    + cbn. intros x. exact (x.(next _).(here _)).
    + cbn. simple refine (Build_elt _ _ _).
      * cbn. intro x. exact (x.(next _).(next _).(here _)).
      * cbn. admit. 
Admitted. 
*)

Definition Typeᶠ : Cubical.
Proof.
  refine (existT _ _Typeᶠ _).
  econstructor.
  { intros A. simpl. simple refine (Build_elt _ _ _).
    - simpl. exact (Identity A).
    - cbn.
      simple refine (Build_elt _ _ _).
    + cbn. intro x. exact (A.2.(refl _) _).(here _).
    + exact ((Prodᶠ_cubical A.1 _).(refl _) _).
    }
  {
    intros X Y. cbn.  econstructor.
    - cbn. intro e.
      pose (Obj := fun x:elt X.1 => obj Y.1).
      pose (f := fun x => (equiv X .1 Y .1 e (here X .1 x)) : Obj x).
      pose (F := fun x : elt X .1 => eq Y .1).
      pose (G' := fun x : elt X .1 => eq_cubical Y .1 Y .2).
      pose (G := fun x : elt X .1 => refl Y .1 Y .2).
      refine (Prodᶠ_elt X.1 Obj f F G G'). 
    - intros e e'. cbn. exact (Prodᶠ_cubical X.1 _). 
  }
Defined. 

CoFixpoint Prodᶠ (A:Cubical) (B : elt A.1 -> Typeᶠ.1.(obj)) : Glob.
refine (  Build_Glob (forall x: elt A.1, (B x).1.(obj))
             (fun f g => Prodᶠ A (fun x => ((B x).1.(eq) (f x) (g x) ; _)))).
intros e. pose (  eq (B x) .1 (f x) (g x)). exact ((B x).2 (f x)).

CoFixpoint Lamᶠ (A:Glob) (B : elt A -> Typeᶠ.1.(obj)) (t: forall x: elt A, elt (B x).1) :
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