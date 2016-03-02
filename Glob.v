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

Arguments here {_} _.
Arguments next {_} _.

CoFixpoint Prodᶠ (A:Glob) (B : elt A -> Glob) : Glob :=
  Build_Glob (forall x: elt A, (B x).(obj))
             (fun f g => Prodᶠ A (fun x => ((B x).(eq) (f x) (g x)))).

CoFixpoint Lamᶠ (A:Glob) (B : elt A -> Glob) (t: forall x: elt A, elt (B x)) :
  elt (Prodᶠ A B).
Proof.
refine (Build_elt (Prodᶠ A B) (fun x => (t x).(here)) _).
cbn. apply Lamᶠ. intros x. apply ((t x).(next)).
Defined.

Definition Appᶠ (A:Glob) (B : elt A -> Glob) 
           (f : elt (Prodᶠ A B)) : forall (x : elt A), elt (B x).
Proof.
intro x; revert B f. cofix.  intros B f. 
simple refine (Build_elt (B x) (f.(here) x) _).
apply (Appᶠ (fun x => (eq (B x) (here f x) (here f x)))).
apply (f.(next)). 
Defined.

Record TypeEquiv (A B : Glob) : Type :=
  {
    equiv : elt (Prodᶠ A (fun _ => B)) ;
    equiv_inv : elt (Prodᶠ B (fun _ => A)) ;
    sect : forall x, (A.(eq) (Appᶠ _ _ equiv_inv (Appᶠ _ _ equiv x)).(here) x.(here)).(obj);
    retr : forall x, (B.(eq) (Appᶠ _ _ equiv (Appᶠ _ _ equiv_inv x)).(here) x.(here)).(obj);
    (* no adjunction required ? *)
  }.

Definition Equiv (A B : Glob) : Glob.
Proof.
  refine (Build_Glob (TypeEquiv A B) (fun f g => _)).
  exact (Prodᶠ A (fun x => (B.(eq) (Appᶠ _ _ f.(equiv _ _) x).(here) (Appᶠ _ _ g.(equiv _ _) x).(here)))).
Defined.

Definition Typeᶠ : Glob := Build_Glob Glob Equiv. 

Definition Id_fun A: elt (Prodᶠ A (fun _ => A)) := Lamᶠ A (fun _ => A) (fun x => x).  

Definition Identity (A:Glob) : TypeEquiv A A.
Proof.
simple refine (Build_TypeEquiv _ _ (Id_fun A) (Id_fun A) _ _).
- intros. exact ((x.(next)).(here)).
- intros. exact ((x.(next)).(here)).
Defined. 

Definition Identityᶠ (A : Glob) : elt (Equiv A A).
Proof.
simple refine (Build_elt (Equiv A A) (Identity A) _).
apply Lamᶠ; intros x; apply (x.(next)).
Defined.

Definition Typeᵇ : elt Typeᶠ.
Proof.
simple refine (Build_elt Typeᶠ Typeᶠ _).
cbn.
simple refine (Build_elt (Equiv Typeᶠ Typeᶠ) (Identity Typeᶠ) _).
apply Lamᶠ; intros x; apply (x.(next)).
Defined.

Definition ID_eq (A:Glob) : elt (Prodᶠ A (fun x : elt A => A.(eq) x.(here) x.(here))).
Proof.
  cbn in *.
  apply Lamᶠ; intros x; apply (x.(next)).
Defined.

Definition eqᵇ : elt (Prodᶠ Typeᶠ (fun A => Prodᶠ A.(here) (fun x => Prodᶠ A.(here) (fun y => Typeᶠ)))).
Proof.
apply Lamᶠ; intros A.
apply Lamᶠ; intros x.
apply Lamᶠ; intros y.
simple refine (Build_elt _ _ _).
+ refine (A.(here).(eq) x.(here) y.(here)).
+ clear. simple refine (Build_elt (Equiv _ _) (Identity _) _).
  apply Lamᶠ; intros E; apply (E.(next)).
Defined.

Definition reflᵇ : elt (Prodᶠ Typeᶠ (fun A => Prodᶠ A.(here) (fun x => (Appᶠ _ _ (Appᶠ _ _ (Appᶠ _ _ eqᵇ A) x) x).(here)))).
Proof.
apply Lamᶠ; intros A.
apply Lamᶠ; intros x.
cbn.
apply x.(next).
Defined.
