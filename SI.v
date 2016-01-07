Require Forcing.
Require Import Arith. 

Definition Obj :Type := nat.
Definition Hom : Obj -> Obj -> Type := fun n m => m <= n.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).


Definition le_S' m : S m ≤ m.
Proof.
  intros R k. eapply le_trans; try eassumption. apply le_S. reflexivity.  
Defined.

Definition inj {m n} (e: Hom n m) : n ≤ m.
Proof.
  intros R k. eapply le_trans; eassumption. 
Defined.

Definition inj2 {m n m' n'} (e: Hom n m -> Hom n' m') : n ≤ m -> n' ≤ m'.
Proof.
  intros H. refine (inj (e _)). exact (H _ (le_refl _)). 
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
             T q (f ∘ (inj (le_n_Sn q))) q # 
         end f).
Defined.

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
  induction p; intros T q α f; apply f; intros q0 α0;
    destruct q0; try exact tt.
  - destruct (le_Sn_0 _ ((α ∘ α0) (S q0) (le_refl _))).
  - simpl.
    refine (let T' := _ : forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type  in _).
    + intros.
      refine (T p0 _ p1 X0). exact (inj2 (le_n_S _ _) X ∘ (inj (le_n_Sn p0))).
      (* exact ((inj (le_n_Sn p)) ∘ X). *)
    + refine (let X := _ : p ≤ q0 in _). 
      * apply (inj2 (le_S_n _ _) (α ∘ α0)).
        (* intros R e. apply le_S_n. refine ( (S R) (le_n_S R q0 e)). *)
      * pose (IHp T' q0 X). unfold T', X in t.
        assert (inj2 (le_n_S q0 p) (inj2 (le_S_n q0 p) (α ∘ α0)) = α ∘ α0).
        apply nat_irrY. rewrite H in t. clear H. refine (t _).
        intros q1 α1 x. 
        assert ((inj2 (le_n_S q1 p) (inj2 (le_S_n q0 p) (α ∘ α0) ∘ α1)
      ∘ inj (Nat.le_succ_diag_r q1)) = α ∘ α0 ∘  inj (le_n_Sn _) ∘ α1).
        apply nat_irrY. rewrite H.        
        apply f. intros q2 α2. specialize (x q2 α2). 
        assert ((fun (p2 : Obj) (α3 : q2 ≤ p2) =>
      T p2
        (fun (R : Obj) (k : Hom p2 R) =>
         α R (α0 R (inj (Nat.le_succ_diag_r q0) R (α1 R (α2 R (α3 R k))))))) =
                (fun (p2 : Obj) (α3 : q2 ≤ p2) =>
                   T' p2
                      (fun (R : Obj) (k : Hom p2 R) => X R (α1 R (α2 R (α3 R k)))))
               ).
        apply funext_. intro q3. apply funext_. intro α3.
        apply funext_. intro q4. apply funext_. intro α4.
        unfold T'. simpl.  assert
                             ((fun (R : Obj) (k : Hom q3 R) =>
      α R (α0 R (inj (Nat.le_succ_diag_r q0) R (α1 R (α2 R (α3 R k)))))) =
                              (inj2 (le_n_S q3 p)
        (fun (R0 : Obj) (k0 : Hom q3 R0) =>
         X R0 (α1 R0 (α2 R0 (α3 R0 k0)))) ∘ inj (Nat.le_succ_diag_r q3))).
        apply nat_irrY. rewrite H0. reflexivity.
        rewrite H0. exact x.
  - intro T. exact (X T p #).
Defined. 
