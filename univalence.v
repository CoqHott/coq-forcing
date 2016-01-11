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

Forcing Translate False using Obj Hom.

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, eq (f x) (g x).

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition apD10 {A} {B:A->Type}
           (f g : forall x, B x) (h: f = g) :
    f == g :=
  match h with eq_refl _ => fun x => eq_refl _ end.

Definition IsEquiv (A B : Type) (f:A -> B) :=
  { g:B -> A &
    prod ((fun x => g (f x)) == @id _) 
         ((fun x => f (g x)) == @id _ ) }.

Definition univalence_fun := forall (A B : Type),
    {f : A -> B & IsEquiv A B f} -> A = B.
                            
Forcing Translate pointwise_paths using Obj Hom.
Forcing Translate sigT using Obj Hom. 
Forcing Translate prod using Obj Hom. 
Forcing Translate ID using Obj Hom.
Forcing Translate id using Obj Hom.
Forcing Translate IsEquiv using Obj Hom. 
Forcing Translate univalence_fun using Obj Hom. 

Fixpoint even n := match n with 0 => true | 1 => false | S (S n) => even n end.

Definition A₀ := fun p q (α : p ≤ q) r (β : q ≤ r) => if r then True else False.
Definition A₁ := fun p q (α : p ≤ q) r (β : q ≤ r) => if r then False else True. 

Definition neg (b:bool) : bool := if b then false else true. 

Axiom funext_ : forall A (B : A -> Type) (f g : forall a, B a), f == g -> f = g.

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
  apply apD10 in H. specialize (H q). apply apD10 in H. exact (H #).
Qed.

Forcing Definition neg_univ : univalence_fun -> False using Obj Hom.
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

  refine (let H := _ : (forall (p0 : Obj) (α : p ≤ p0),
           ᶠsigT p0
             (fun (p1 : Obj) (α0 : p0 ≤ p1) (p2 : Obj) (α1 : p1 ≤ p2) =>
              (forall (p3 : Obj) (α2 : p2 ≤ p3),
               A₀ p p3 (# ∘ (# ∘ (α ∘ (α0 ∘ (α1 ∘ (α2 ∘ #)))))) p3 #) ->
              A₁ p p2 (# ∘ (α ∘ (α0 ∘ (α1 ∘ #)))) p2 #)
             (fun (p1 : Obj) (α0 : p0 ≤ p1)
                (f : forall (p2 : Obj) (α1 : p1 ≤ p2),
                     (forall (p3 : Obj) (α2 : p2 ≤ p3),
                      A₀ p p3
                        (# ∘ (# ∘ (α ∘ (α0 ∘ (α1 ∘ (# ∘ (α2 ∘ #))))))) p3
                        #) ->
                     A₁ p p2 (# ∘ (α ∘ (α0 ∘ (α1 ∘ (# ∘ #))))) p2 #) =>
              ᶠIsEquiv p1
                (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                 A₀ p p2 (# ∘ (# ∘ (α ∘ (α0 ∘ (α1 ∘ #))))))
                (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                 A₁ p p2 (# ∘ (α ∘ (α0 ∘ (α1 ∘ #)))))
                (fun (p : Obj) (α1 : p1 ≤ p) => f p (α1 ∘ #))) p0 
             #) in _). 

  intros. refine (ᶠexistT _ _ _ _ _). exact f.
  intros. refine (ᶠexistT _ _ _ _ _). exact g.

    (* Dealing with section and retraction *)

  split.
  {
    compute. intros. apply eq__is_eq, funext_. intro p4. apply funext_. intro α3.
    assert ((fun (R : bool) (k : Hom p4 R) => α3 R tt) = (fun (R : bool) (k : Hom p4 R) => α3 R k)).
    apply funext_. intro p5. apply funext_. intro α4. destruct α4. reflexivity.
    rewrite <- H. destruct p4; reflexivity.
  }
  {
    compute. intros. apply eq__is_eq, funext_. intro p4. apply funext_. intro α3.
    assert ((fun (R : bool) (k : Hom p4 R) => α3 R tt) = (fun (R : bool) (k : Hom p4 R) => α3 R k)).
    apply funext_. intro p5. apply funext_. intro α4. destruct α4. reflexivity.
    rewrite <- H. destruct p4; reflexivity.
    }
  
  specialize (huniv p # (A₀ p) (A₁ p) H).
  
  (* Proof of False using A₀ = A₁ *)

  apply eq_is_eq_, apD10 in huniv. specialize (huniv p).
  apply apD10 in huniv. specialize (huniv #).
  apply apD10 in huniv. specialize (huniv p). 
  apply apD10 in huniv. specialize (huniv #). compute in *.
  destruct p. inversion huniv. 
  destruct ((fun X => match huniv in _ = X return X with eq_refl _ => I end) tt).  
  symmetry in huniv.
  destruct ((fun X => match huniv in _ = X return X with eq_refl _ => I end) tt).  
  
Defined.

End Univalence. 