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

Forcing Definition fixp : forall (T:Type), ((later T) ->  T) -> T using Obj Hom.
Proof.
 
  intros p.
   
  assert (forall (T : forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type)
             q (f:p ≤ q), (forall (p0 : Obj) (α : q ≤ p0),
                 (forall (p1 : Obj) (α0 : p0 ≤ p1),
                     ᶠlater p1
                            (fun (p2 : Obj) (α1 : p1 ≤ p2) =>
                               T p2 ((f ∘ α ∘ α0 ∘ α1))) p1 
                            #) -> T p0 (f ∘ α) p0 #) -> T q f q #).

  (* intros T q α f. *)
  induction p; intros T q α f; apply f; intros q0 α0.
   - destruct q0; try exact tt.
     destruct (le_Sn_0 _ (α ∘ α0)).
   - destruct q0; try exact tt.
     refine (let T' := _ :
           forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type in _).
    {
      intros.
      refine (T p0 _ p1 X0). 
      (* admit. *)
      assert (S p ≤ S p0).
      {
        apply le_n_S_admitted; auto. 
       }
      exact (X1 ∘ ((le_S' p0))).
    }
    refine (let X := _ : p ≤ q0 in _).
    { pose (α ∘ α0). apply le_S_n_admitted; auto.
     }
    
    pose (IHp T' q0 X). unfold T' in t. simpl in *. 
    simpl in t. unfold X in t.
    assert (le_n_S_admitted p q0 (le_S_n_admitted p q0 (α ∘ α0)) =
            α ∘ α0).
    generalize (α ∘ α0). clear. intro.
    
    apply nat_irrY. rewrite H in t. clear H.

    refine (t _). intros q1 α1 x.
    
    assert (le_n_S_admitted p q1 (le_S_n_admitted p q0 (α ∘ α0) ∘ α1)
                  ∘ le_S' q1 = α ∘ α0 ∘ le_S' _ ∘ α1).
    apply nat_irrY. rewrite H.        

    apply f. intros q2 α2. specialize (x q2 α2). 

    assert ((fun (p2 : Obj) (α3 : q2 ≤ p2) =>
            T p2 (le_n_S_admitted p p2
              (fun (R0 : Obj) (k0 : Hom p2 R0) =>
               le_S_n_admitted p q0 (α ∘ α0) R0 (α1 R0 (α2 R0 (α3 R0 k0))))
              ∘ le_S' p2)) =
             fun (p2 : Obj) (α3 : q2 ≤ p2) => T p2 (fun (R : Obj) (k : Hom p2 R) =>
         α R (α0 R (le_S' q0 R (α1 R (α2 R (α3 R k))))))).
    apply funext_. intro q3. apply funext_. intro α4.
    apply f_equal. 
    intros. apply nat_irrY.
    rewrite <- H0.

    exact x.
    
  - intro T. exact (X T p #).
Defined. 
