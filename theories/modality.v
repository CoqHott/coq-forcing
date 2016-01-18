Require Forcing.
Require Import Eq.

Section Modality.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

Forcing Definition eq_rect_partial : forall A (x :A) (P : A -> Type),
    P x ->
    forall y (e:x = y), P y using Obj Hom.
Proof.
  intros p A x P P_refl y e.
  exact (match e p # in ᶠeq _ _ _ y' q f return P p # y' q f
         with | ᶠeq_refl _ _ _ => P_refl p # end).
Defined.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, eq (f x) (g x).

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type}
           (f g : forall x, B x) (h: f = g) :
    f == g :=
  match h with eq_refl _ => fun x => eq_refl _ end.

Definition IsEquiv A B (f: A -> B) :=
  { g:B -> A &
    prod ((fun x => g (f x)) == @id _) 
         ((fun x => f (g x)) == @id _ ) }.

Definition IsEquiv_id (A : Type) : IsEquiv _ _ (@id A).
Proof.
  refine (existT _ _ _).
  - exact (@id _).                                    
  - split. all : intro; reflexivity. 
Defined.

Definition path_to_equiv (A B : Type) :
  A = B -> {f : A -> B & IsEquiv A B f}.
Proof.
  refine (eq_rect_partial Type A (fun B => {f : A -> B & IsEquiv A B f}) _ B).
  refine (existT _ _ _).
  - exact (@id _).
  - exact (IsEquiv_id _).
Defined. 

Definition univalence := forall (A B : Type), IsEquiv _ _ (path_to_equiv A B).
   
Forcing Translate pointwise_paths using Obj Hom.
Forcing Translate sigT using Obj Hom. 
Forcing Translate prod using Obj Hom. 
Forcing Translate ID using Obj Hom.
Forcing Translate id using Obj Hom.
Forcing Translate IsEquiv using Obj Hom. 
Forcing Translate IsEquiv_id using Obj Hom. 
Forcing Translate path_to_equiv using Obj Hom.
Forcing Translate univalence using Obj Hom.

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


Definition univalence_fun_Box := forall (A B : Type),
    {f : A -> B & IsEquiv A B f} -> Box A = Box B.

Forcing Translate univalence_fun_Box using Obj Hom.

Axiom univalence_fun_ : forall (A B : Type),
    {f : A -> B & IsEquiv A B f} -> A = B.

Forcing Definition univalence_preservation_Box : univalence_fun_Box using Obj Hom.
Proof.
  intros p A B f_equiv.
  specialize (f_equiv p #). destruct f_equiv as [f f_equiv].
  apply eq__is_eq.
  apply funext_. intro q0. apply funext_. intro α0. apply funext_. intro r. 
  apply funext_. intro α1.
  specialize (f_equiv r (α0 ∘ α1)). destruct f_equiv as [g section].
  specialize (section r #). destruct section as (section, retraction).
  refine (univalence_fun_ _ _ (existT _ _ _)).

  - intro x. compute. intros. apply f. intros. apply x. 
  - refine (existT _ _ _).
    + intro x. compute. intros. apply g. intros. apply x. 
    + split.
      {
        intro x. simpl. apply funext_. intro q2. apply funext_. intro α2.
        compute in x. specialize (section r # x).
        apply eq_is_eq_ in section.
        apply apD10 in section. specialize (section q2).
        apply apD10 in section. specialize (section α2).
        exact section. }
      {
        intro x. simpl. apply funext_. intro q2. apply funext_. intro α2.
        compute in x. specialize (retraction r # x).
        apply eq_is_eq_ in retraction.
        apply apD10 in retraction. specialize (retraction q2).
        apply apD10 in retraction. specialize (retraction α2).
        exact retraction. }
Defined. 
  
End Modality.
