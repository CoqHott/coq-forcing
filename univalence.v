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

Forcing Definition eq : forall (A : Type), A -> A -> Type using Obj Hom.
Proof.
compute in *.
intros p A x y q α.
exact (x = y).
Defined.

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
  := forall x:A, eq _ (f x) (g x).

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Notation "g ° f" := (fun x => g (f x)) (at level 70) : type_scope.

Definition univalence := forall (A B : Type) (f:A -> B) (g:B -> A),
    g ° f == @id _ ->
    f ° g == @id _ ->
    eq Type A B.

Forcing Translate pointwise_paths using Obj Hom.
Forcing Translate ID using Obj Hom.
Forcing Translate id using Obj Hom.
Forcing Translate univalence using Obj Hom.

Fixpoint even n := match n with 0 => true | 1 => false | S (S n) => even n end.

Definition A₀ := fun p q (α : p ≤ q) r (β : q ≤ r) => if r then True else False.
Definition A₁ := fun p q (α : p ≤ q) r (β : q ≤ r) => if r then False else True. 

Definition pointwise_paths_ {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Definition apD10_ {A} {B:A->Type} {f g : forall x, B x} (h: f = g) :pointwise_paths_ f g :=
  match h with eq_refl => fun x => eq_refl end. 

Definition type_naturalityA : forall p p0
                                       (α : p ≤ p0) p1 (α0 : p0 ≤ p1),
    @Logic.eq Type (A₁ p p0 α p1 α0) (A₁ p p1 (α ∘ α0) p1 #).
Proof. intros. compute. destruct p1; reflexivity.
Defined.

Definition type_monotonicityA : forall p p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1),
    A₁ p p0 α p0 # -> A₁ p p1 (α ∘ α0) p1 #.
Proof.
  intros. destruct p1; compute in *; auto.  destruct p0; auto.
Abort.

Definition neg (b:bool) : bool := if b then false else true. 

Axiom funext_ : forall A (B : A -> Type) (f g : forall a, B a), pointwise_paths_ f g -> f = g.

Definition funext := forall A (B : A -> Type) (f g : forall a, B a), f == g -> eq _ f g.

Forcing Translate funext using Obj Hom.

Forcing Definition funext_preservation : funext using Obj Hom.
Proof.
  intros p A B f g H. compute in *.
  apply funext_. intro q. apply funext_. intro α. apply funext_. intro a. 
  specialize (H q α a).
  apply apD10_ in H. specialize (H q). apply apD10_ in H. exact (H #).
Qed.

Forcing Definition neg_propext : univalence -> Empty using Obj Hom.
Proof.
  intros p huniv.
  refine (let f := _ : forall (p0 : Obj) (α : p ≤ p0),
                 (forall (p1 : Obj) (α0 : p0 ≤ p1),
                  A₀ p p1 (# ∘ (# ∘ (α ∘ (# ∘ (α0 ∘ #))))) p1 #) ->
                 A₁ p p0 (# ∘ (α ∘ (# ∘ #))) p0 # in _).
  intros. specialize (H (neg p0) (fun _ _ => tt)). destruct p0; exact H.
  refine (let g := _ : forall (p0 : Obj) (α : p ≤ p0),
             (forall (p1 : Obj) (α0 : p0 ≤ p1),
                  A₁ p p1 (# ∘ (# ∘ (α ∘ (# ∘ (α0 ∘ #))))) p1 #) ->
                 A₀ p p0 (# ∘ (# ∘ (# ∘ (α ∘ (# ∘ #))))) p0 # in _).
  intros. specialize (H (neg p0) (fun _ _ => tt)). destruct p0; exact H.

  specialize (huniv p # (A₀ p) (A₁ p) f g).
  
  apply apD10_ in huniv. specialize (huniv p).
  apply apD10_ in huniv. specialize (huniv #).
  apply apD10_ in huniv. specialize (huniv p). 
  apply apD10_ in huniv. specialize (huniv #). compute in *.
  destruct p. 
  exact ((fun X => match huniv in _ = X return X with eq_refl => I end) False).  
  symmetry in huniv.
  exact ((fun X => match huniv in _ = X return X with eq_refl => I end) False).  

  compute. intros. apply funext_. intro p1. apply funext_. intro α0.
  assert ((fun (R : bool) (_ : Hom true R) => α0 R tt) = α0).
  apply funext_. intro p2. apply funext_. intro α1. destruct α1. reflexivity.
  destruct H. destruct p1; reflexivity.

  compute. intros. apply funext_. intro p1. apply funext_. intro α0.
  assert ((fun (R : bool) (_ : Hom true R) => α0 R tt) = α0).
  apply funext_. intro p2. apply funext_. intro α1. destruct α1. reflexivity.
  destruct H. destruct p1; reflexivity.
  
Defined.


Axiom propext_ : forall (P Q : Type), (P -> Q) -> (Q -> P) -> P = Q. 

Definition propext_inv : forall (P Q : Type), P = Q -> P -> Q.
Proof. intros. destruct H. exact X. Defined.

Axiom type_naturality@{i j} : forall p
                (A : forall p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), Type@{i}) 
                p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1),
    @Logic.eq Type@{j} (A p0 α p1 α0) (A p1 (α ∘ α0) p1 #).

Forcing Definition Box : Type -> Type using Obj Hom.
Proof.
  intros. exact (forall p1 (α0 : p0 ≤ p1), X p1 (α ∘ α0) p1 #). 
Defined.

Forcing Definition Box_unit : forall (A:Type) , A -> Box A using Obj Hom.
Proof.
  intros p A. compute. exact (@id _). 
Defined.   

Forcing Definition Box_counit : forall (A:Type) , Box A -> A using Obj Hom.
Proof.
  intros. exact (X p # p #).
Defined. 

Forcing Definition Box_unit_counit : forall (A:Type) x, eq _ (Box_counit A (Box_unit A x)) x using Obj Hom.
Proof.
  intros. reflexivity.
Defined.

Axiom box_naturality@{i} : forall p
                (A : forall p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), Type@{i})
                (x : forall p0 (α : p ≤ p0) p1 (α0 : p0 ≤ p1), A p1 (α ∘ α0) p1 #) p0
                (α : p ≤ p0) p1 (α0 : p0 ≤ p1),
    @Logic.eq (A p1 (α ∘ α0) p1 #) (x p0 α p1 α0) (x p1 (α ∘ α0) p1 #).

Forcing Definition Box_modality_fun : forall (A B:Type), (A -> Box B) -> Box A -> Box B using Obj Hom.
Proof.
  intros p A B f x.
  compute in *. intros. apply f. intros. apply x.
Defined.

Definition Box_modality_inv : forall (A B:Type), (Box A -> Box B) -> A -> Box B :=
  fun A B f x => f (Box_unit _ x).  
                                                  
Forcing Translate Box_modality_inv using Obj Hom.


Forcing Definition Box_modality : forall (A B:Type), (A -> Box B) -> Box A -> Box B using Obj Hom.
Proof.
  intros p A B f x. 
  compute in *. intros. apply f. intros. apply x.
Defined.

Definition propext_Box := forall (A B : Type), (A -> B) -> (B -> A) ->
                                               eq Type (Box A) (Box B).

Forcing Translate propext_Box using Obj Hom.

Forcing Definition propext_preservation_Box : propext_Box using Obj Hom.
Proof.
  intros p P Q H H'. compute in *. 
  apply funext_. intro q. apply funext_. intro α. apply funext_. intro r. 
  apply funext_. intro α1. apply propext_. 
  - intro HP. intros. rewrite type_naturality.
    apply H. intros. change (P _ (α ∘ α1 ∘ α0∘ α2) _ #). apply HP. 
  - intro HQ. intros. rewrite type_naturality.
    apply H'. intros. change (Q _ (α ∘ α1 ∘ α0∘ α2) _ #). apply HQ. 
Defined. 

  
End Univalence. 