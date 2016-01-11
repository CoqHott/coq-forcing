Require Forcing.
Require Import Eq.

Section Univalence.

Definition Obj := bool.
Definition Hom (p q : Obj) := unit.
(* p <= q. *)

Opaque Hom. 

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

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

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

(* Forcing Definition foo : forall A (x y:A), eq x y using Obj Hom. *)

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, eq (f x) (g x).

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

Fixpoint even n := match n with 0 => true | 1 => false | S (S n) => even n end.

Definition A₀ := fun p q (α : p ≤ q) r (β : q ≤ r) => if r then True else False.
Definition A₁ := fun p q (α : p ≤ q) r (β : q ≤ r) => if r then False else True. 

Definition pointwise_paths_ {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Definition apD10_ {A} {B:A->Type}
           (f g : forall x, B x) (h: f = g) :
    pointwise_paths_ f g :=
  match h with eq_refl _ => fun x => eq_refl _ end.

Definition type_naturalityA : forall p p0
                                       (α : p ≤ p0) p1 (α0 : p0 ≤ p1),
    @Logic.eq Type (A₁ p p0 α p1 α0) (A₁ p p1 (α ∘ α0) p1 #).
Proof. intros. compute. destruct p1; reflexivity.
Defined.

(* Definition type_monotonicityA : forall p p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), *)
(*     A₁ p p0 α p0 # -> A₁ p p1 (α ∘ α0) p1 #. *)
(* Proof. *)
(*   intros. destruct p1; compute in *; auto.  destruct p0; auto. *)
(* Abort. *)

Definition neg (b:bool) : bool := if b then false else true. 

Axiom funext_ : forall A (B : A -> Type) (f g : forall a, B a), pointwise_paths_ f g -> f = g.

Definition funext := forall A (B : A -> Type) (f g : forall a, B a), f == g -> f = g.

Forcing Translate funext using Obj Hom.

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

Forcing Definition funext_preservation : funext using Obj Hom.
Proof.
  intros p A B f g H. 
  apply eq__is_eq, funext_. intro q.
  apply funext_. intro α. apply funext_. intro a. 
  specialize (H q α a). apply eq_is_eq_ in H. 
  apply apD10_ in H. specialize (H q). apply apD10_ in H. exact (H #).
Qed.

Forcing Definition neg_univ : univalence -> Empty using Obj Hom.
Proof.
  intros p huniv.

  (* Definition of the equivalence function and its inverse *)

  refine (let f := _ : forall (p0 : Obj) (α : p ≤ p0),
                 (forall (p1 : Obj) (α0 : p0 ≤ p1),
                  A₀ p p1 (α ∘ α0) p1 #) ->  A₁ p p0 α p0 # in _).
  intros. specialize (H (neg p0) (fun _ _ => tt)). destruct p0; exact H.
  refine (let g := _ : forall (p0 : Obj) (α : p ≤ p0),
             (forall (p1 : Obj) (α0 : p0 ≤ p1),
                  A₁ p p1 (α ∘ α0) p1 #) ->  A₀ p p0 α p0 # in _).
  intros. specialize (H (neg p0) (fun _ _ => tt)). destruct p0; exact H.

  specialize (huniv p # (A₀ p) (A₁ p) f g).
  
  (* Proof of False using A₀ = A₁ *)

  apply eq_is_eq_, apD10_ in huniv. specialize (huniv p).
  apply apD10_ in huniv. specialize (huniv #).
  apply apD10_ in huniv. specialize (huniv p). 
  apply apD10_ in huniv. specialize (huniv #). compute in *.
  destruct p. 
  exact ((fun X => match huniv in _ = X return X with eq_refl _ => I end) False).  
  symmetry in huniv.
  exact ((fun X => match huniv in _ = X return X with eq_refl _ => I end) False).  

  (* Dealing with section and retraction *)
  
  compute. intros. apply eq__is_eq, funext_. intro p1. apply funext_. intro α0.
  assert ((fun (R : bool) (_ : Hom true R) => α0 R tt) = (fun (R : bool) (k : Hom p1 R) => α0 R k)).
  apply funext_. intro p2. apply funext_. intro α1. destruct α1. reflexivity.
  rewrite <- H. destruct p1; reflexivity.

  compute. intros. apply eq__is_eq, funext_. intro p1. apply funext_. intro α0.
  assert ((fun (R : bool) (_ : Hom true R) => α0 R tt) = (fun (R : bool) (k : Hom p1 R) => α0 R k)).
  apply funext_. intro p2. apply funext_. intro α1. destruct α1. reflexivity.
  rewrite <- H. destruct p1; reflexivity.
  
Defined.

  
End Univalence. 