Require Forcing.
Require Import Eq.

Section Univalence.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

Forcing Definition Empty : Type using Obj Hom.
Proof.
intros p q α.
exact False.
Defined.

Forcing Definition Empty_rect : forall A, Empty -> A using Obj Hom.
Proof.
intros p A e.
destruct (e p #).
Defined.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

(* Notation "g ° f" := (fun x => g (f x)) (at level 70) : type_scope. *)

Definition univalence := forall (A B : Type) (f:A -> B) (g:B -> A),
    (fun x => g (f x)) == @id _ ->
    (fun x => f (g x)) == @id _ ->
    A = B.

Forcing Translate pointwise_paths using Obj Hom.
Forcing Translate ID using Obj Hom.
Forcing Translate id using Obj Hom.
Forcing Translate univalence using Obj Hom.

Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h: f = g) : f == g :=
  match h with eq_refl _ => fun x => eq_refl _ end. 

Axiom funext_ : forall A (B : A -> Type) (f g : forall a, B a), f == g -> f = g.

Definition eq__is_eq : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #),
    x = y -> ᶠeq p _ x y p #.
Proof.
  intros. destruct H. apply ᶠeq_refl.
Defined.

Definition eq_is_eq_ : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #),
   ᶠeq p _ x y p # -> x = y.
Proof.
  intros. destruct H. apply eq_refl.
Defined.

Forcing Definition Box : Type -> Type using Obj Hom.
Proof.
  intros.
  (* exact (forall p1 (α0 : p0 ≤ p1), X p1 α p1 α0).  *)
  exact (forall p1 (α0 : p0 ≤ p1), X p1 (α ∘ α0) p1 #).
Defined.

Forcing Definition Box_unit : forall (A:Type) , A -> Box A using Obj Hom.
Proof.
  refine (fun p A X => X).
Defined.   

(* Forcing Definition Box_counit : forall (A:Type) , Box A -> A using Obj Hom. *)
(* Proof. *)
(*   intros. exact (X p # p #). *)
(* Defined.  *)

(* Forcing Definition Box_unit_counit : forall (A:Type) x, eq _ (Box_counit A (Box_unit A x)) x using Obj Hom. *)
(* Proof. *)
(*   intros. reflexivity. *)
(* Defined. *)

(* Axiom box_naturality@{i} : forall p *)
(*                 (A : forall p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), Type@{i}) *)
(*                 (x : forall p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), A p1 (α ∘ α0) p1 #) p0 *)
(*                 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), *)
(*     @Logic.eq (A p1 (α ∘ α0) p1 #) (x p0 α p1 α0) (x p1 (α ∘ α0) p1 #). *)

Definition Box_modality_fun : forall (A B:Type), (Box A -> Box B) -> A -> Box B :=
  fun A B f x => f (Box_unit _ x).  

Forcing Definition Box_modality_fun2 : forall (A B:Type), (Box A -> Box B) -> A -> Box B using Obj Hom.
Proof.
  intros p A B f x p0 α0.
  compute in *. refine (f p # _ p0 α0). intros.
  exact (x p2 (α ∘ α1)).
Defined.

Forcing Definition Box_modality_inv : forall (A B:Type), (A -> Box B) -> Box A -> Box B using Obj Hom.
Proof.
  intros p A B f x p0 α0. compute in *.
  (* refine (f p0 α0 (x p0 α0) p0 #). *)
  refine (f p # (x p #) p0 α0).
  (* refine (f p # _ p0 α0). compute in *.  *)
  (* exact (fun p3 α2 => x p3 α2 p3 #). *)
Defined.
                                                  
Forcing Translate Box_modality_fun using Obj Hom.

Forcing Definition Box_modality : forall (A B:Type) f,
    Box_modality_fun A B (Box_modality_inv A B f) = f using Obj Hom.
Proof.
  intros p A B f. 
  compute in *. apply eq__is_eq, funext_. intro p0. apply funext_. intro α0.
  apply funext_; intro x. apply funext_. intro p1. apply funext_. intro α1.
  reflexivity. 
Abort.   

Forcing Definition Box_modality : forall (A B:Type) f x,
    Box_modality_inv A B (Box_modality_fun2 A B f) x = f x using Obj Hom.
Proof.
  intros p A B f x. 
  apply eq__is_eq, funext_. intro p0. apply funext_. intro α0.
  (* apply funext_; intro x. *)
  apply funext_. intro p1. apply funext_. intro α1.
  (* Opaque ᶠBox_modality_inv ᶠBox_unit. *)
  compute in *. 
  (* assert ((fun p2 (α : p0 ≤ p2) p3 (α2 : p2 ≤ p3) => *)
  (*            x p # p3 (α ∘ α2)) =  *)
  (*        (fun p2 (α : p0 ≤ p2) p3 (α2 : p2 ≤ p3) => *)
  (*            x p2 α p3 α2)). *)
  (* admit. *)
  (* rewrite H. reflexivity.  *)
Abort.

Definition propext_Box := forall (P Q : Type), (P -> Q) -> (Q -> P)
                                               -> Box P = Box Q.

Forcing Translate propext_Box using Obj Hom.

Axiom propext_ : forall (P Q : Type), (P -> Q) -> (Q -> P) -> P = Q. 

Forcing Definition propext_preservation_Box : propext_Box using Obj Hom.
Proof.
  intros p P Q H H'.
  apply eq__is_eq.
  apply funext_. intro q0. apply funext_. intro α0. apply funext_. intro r. 
  apply funext_. intro α1. apply propext_. 
  
  - intro HP. compute. intros. apply H. intros. apply HP. 
  - intro HQ. compute. intros. apply H'. intros. apply HQ. 
Defined. 
  
End Univalence. 