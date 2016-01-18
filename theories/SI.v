Require Forcing.

Inductive le : nat -> nat -> Type :=
  | le_0 : forall n, 0 <= n
  | le_n_S : forall m n:nat, n <= m -> S n <= S m
where "n <= m" := (le n m) : nat_scope.

Definition Obj :Type := nat.
Definition Hom : Obj -> Obj -> Type := fun n m => m <= n.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Axiom le_Sn_0 : forall n, 0 ≤ S n -> False.

Definition le_S' m : S m ≤ m.
Proof.
  intros R k. 
  induction k.
  - apply le_0.
  - apply le_n_S. exact IHk. 
Defined.

Definition pointwise_paths_ {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Definition apD10_ {A} {B:A->Type} {f g : forall x, B x} (h: f = g) :pointwise_paths_ f g :=
  match h with eq_refl => fun x => eq_refl end. 

Axiom funext_ : forall A (B : A -> Type) (f g : forall a, B a), pointwise_paths_ f g -> f = g.

Axiom nat_irr : forall m n (p q : m <= n), p = q.

Definition nat_irrY m n (p q : m ≤ n): p = q.
Proof.
  apply funext_. intro R. apply funext_. intro e.
  apply nat_irr.
Defined. 

Forcing Definition later : Type -> Type using Obj Hom.
Proof.
  intros p T q f.
  exact (match q as n return (p ≤ n -> Type) with
         | 0 => fun _ => unit
         | S q => fun (f:p ≤ S q) =>
             T q (f ∘ (le_S' q)) q # 
         end f).
Defined.

Definition le_n_S_admitted m n : m ≤ n -> S m ≤ S n.
Admitted. 

Definition le_S_n_admitted m n : S m ≤ S n -> m ≤ n.
Admitted. 

Forcing Definition Box : Type -> Type using Obj Hom.
Proof.
  intros.
  exact (forall p1 (α0 : p0 ≤ p1), X p1 (α ∘ α0) p1 #).
Defined.

Forcing Definition fixp_ : forall (T:Type), ((later T) ->  T) -> Box T using Obj Hom.
Proof.
 
  intros p.

  induction p; intros T f q α; apply f; intros q0 α0.
  - destruct q0; try exact tt.
    destruct (le_Sn_0 _ (α ∘ α0)).
  - destruct q0; try exact tt.
    simpl.
    refine (let T' := _ :
           forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type in _).
    {
      intros.
      refine (T p0 _ p1 X0). 
      assert (S p ≤ S p0).
      {
        apply le_n_S_admitted; auto. 
       }
      exact (X1 ∘ ((le_S' p0))).
    }
    refine (let X := _ : p ≤ q0 in _).
    { pose (α ∘ α0). apply le_S_n_admitted; auto.
     }
    
    assert (le_n_S_admitted p q0 (le_S_n_admitted p q0 (α ∘ α0)) =
            α ∘ α0).
    generalize (α ∘ α0). clear. intro.
    apply nat_irrY.
    change (T q0 (α ∘ α0 ∘ (le_S' q0)) q0 #).
    rewrite <- H. 
    apply (IHp T'). intros q1 α1 x.
    apply f. intros. specialize (x _  α2).

    assert ((fun (p1 : Obj) (α3 : p0 ≤ p1) =>
      T p1
        (fun (R : Obj) (k : Hom p1 R) =>
         le_n_S_admitted p q1
           (fun (R0 : Obj) (k0 : Hom q1 R0) => α1 R0 k0) R
           (le_S' q1 R (α2 R (α3 R k))))) =
             (fun (p : Obj) (α : p0 ≤ p) =>
         T' p (fun (R : Obj) (k : Hom p R) => α1 R (α2 R (α R k))))).
    unfold T'. 
    apply funext_. intro q3. apply funext_. intro α4.
    apply f_equal. 
    intros. apply nat_irrY.
    rewrite H0.
    
    apply x. 
Defined. 

Forcing Definition Box_counit : forall (A:Type) , Box A -> A using Obj Hom.
Proof.
  intros. exact (X p # p #).
Defined.

Definition fixp : forall (T:Type), ((later T) ->  T) -> T  :=
  fun T f => Box_counit _ (fixp_ T f).

