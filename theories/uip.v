Require Forcing.
Require Import Eq.

Section Funext.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

Opaque Hom. 

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).


Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Forcing Definition leibniz : forall A (x :A) (P : A -> Type),
    P x ->
    forall y (e:x = y), P y using Obj Hom.
Proof.
  intros p A x P P_refl y e.
  exact (match e p # in eqᶠ _ _ _ y'  return P p # y' p #
         with | eq_reflᶠ _ _ _ => P_refl p # end).
Defined.

Definition apD10 {A} {B:A->Type}
           {f g : forall x, B x} (h: f = g) :
  f == g.
Proof.
  refine (leibniz _ f (fun g => f == g) _ g h).
  intro. apply eq_refl. 
Defined. 

Forcing Translate pointwise_paths using Obj Hom.
Forcing Translate apD10 using Obj Hom.

Axiom funext_simpl_ : forall A (B : A -> Type) (f g : forall a, B a),
    f == g -> f = g.

Axiom uip_ : forall A (x:A) e, e = eq_refl x.

Definition uip := forall A (x:A) e, e = eq_refl x.

Forcing Translate uip using Obj Hom.

Definition eq__is_eq : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #),
    x = y -> eqᶠ p _ x y.
Proof.
  intros. destruct H. apply eq_reflᶠ.
Defined.

Definition eq_is_eq_ : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #),
   eqᶠ p _ x y -> x = y.
Proof.
  intros. destruct H. apply eq_refl.
Defined.

Definition eq_is_section : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #)
    (e:x=y) (e':eqᶠ p _ x y),
  eq__is_eq _ _ _ _ e = e' -> e = eq_is_eq_ _ _ _ _ e'.
Proof. 
  intros. destruct e. simpl in *. 
  rewrite <- H. simpl. reflexivity.
Defined. 

Definition eq_is_retraction : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #)
    (e:x=y) (e':eqᶠ p _ x y),
  eq_is_eq_ _ _ _ _ e' = e -> e'  = eq__is_eq _ _ _ _ e.
Proof. 
  intros. destruct e'. simpl in *. 
  rewrite <- H. simpl. reflexivity.
Defined. 

Forcing Definition uip_preservation : uip using Obj Hom.
Proof.
  intros p A x e.
  apply eq__is_eq.
  apply funext_simpl_. intro p1.
  apply funext_simpl_. intro α0.
  pose (uip_ _ _ (eq_is_eq_ _ _ _ _ (e p1 α0))).
  apply eq_is_retraction in e0. exact e0. 
Defined.

End Funext. 