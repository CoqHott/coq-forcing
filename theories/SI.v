(* Formalisation of Guarded Recursive Types using the cbn forcing plugin with the ordered set of natural numbers
 as forcing conditions *)

Require Forcing.
Require Eq.
Require Import PeanoNat.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

(*
Set Universe Polymorphism.
*)


Definition Obj :Type := nat.
Definition Hom : Obj -> Obj -> Type := fun n m => m <= n.

Notation "P ≤ Q" := (forall R, Hom Q R -> Hom P R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).

Lemma Yle_to_le : forall n m, n ≤ m -> m <= n.
Proof.
  intros n m H.
  unfold Hom in H.
  eapply H.
  eapply le_n.
Qed.

Lemma le_to_Yle : forall n m, n <= m -> m ≤ n.
Proof.
unfold Hom.
intros n m H R H'.
refine (Nat.le_trans _ n _ _ _); tauto.
Qed.


Lemma Yle_Sn_0 : forall n, 0 ≤ S n -> False.
Proof.
  unfold Hom;
  intros n H.
  specialize (H (S n) (le_n (S n))).
  inversion H.
Qed.

Definition Yle_S' m : S m ≤ m.
Proof.
  eapply le_to_Yle.
  eapply le_S.
  eapply le_n.
Defined.

Definition Ynat_irr p q (α α' : p ≤ q): α = α'.
Proof.
  unfold Hom in α,α'.
  apply (functional_extensionality_dep α α').
  intro r.
  apply (functional_extensionality_dep (α r) (α' r)).
  intro α''.
  apply ProofIrrelevance.proof_irrelevance.
Defined.

Forcing Definition later : Type -> Type using Obj Hom.
Proof.
  intros p T q f.
  destruct q.
  exact unit.
  exact (T q (f ∘ (Yle_S' q)) q #).
Defined.

Notation "⊳ A" := (later A) (at level 40).

Lemma Yle_n_S m n : m ≤ n -> S m ≤ S n.
Proof.
 intros H.
 eapply le_to_Yle.
 eapply le_n_S.
 eapply Yle_to_le.
 eapply H.
Qed.
 

Definition Yle_S_n m n : S m ≤ S n -> m ≤ n.
Proof.
 intros H.
 eapply le_to_Yle.
 eapply le_S_n.
 eapply Yle_to_le.
 eapply H.
Qed.

Forcing Definition later_app : forall A B (t : ⊳ (A -> B)) (u : ⊳ A), ⊳ B using Obj Hom.
Proof.
  intros p A B t u.
  destruct p.
  exact tt.
  apply (t (S p) #).
  intros q β.
  (* how to avoid the rewrite ? *)
  rewrite (Ynat_irr _ _ (Yle_S' p ∘ β) (Yle_n_S p q β ∘ Yle_S' q)).
  exact (u (S q) (Yle_n_S p q β)).
Defined.

Notation "t ⊙ u" := (later_app _ _ t u) (at level 40).

Forcing Definition nextp : forall (T:Type), T -> (later T) using Obj Hom.
Proof.
  intros.
  destruct p;
  unfold laterᶠ.
  exact tt.
  refine (X p _).
Defined.

Forcing Translate eq using Obj Hom.

Definition eq_is_eq : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #),
    Logic.eq x y -> eqᶠ p _ x y.
Proof.
  intros. rewrite H. apply eq_reflᶠ.
Defined.

Lemma funext_ext : forall (p : Obj) (f g : forall (p0 : Obj) (α : p ≤ p0), forall p1 : Obj, p0 ≤ p1 -> Type),
 (forall (p0 p1 : Obj) (α : p ≤ p0) (α' : p0 ≤ p1), (f p0 α p1 α') = (g p0 α p1 α')) -> f = g.
Proof.
 intros p f g H.
 eapply (functional_extensionality_dep f g).
 intro p0.
 eapply (functional_extensionality (f p0) (g p0)).
 intro α.
 eapply (functional_extensionality_dep (f p0 α) (g p0 α)).
 intro p1.
 eapply (functional_extensionality (f p0 α p1) (g p0 α p1)).
 intro α'.
 eapply H. 
Qed.

Forcing Definition next_id : forall A u, nextp _ (fun (x : A) => x) ⊙ u = u using Obj Hom.
Proof.
intros p A u.
apply eq_is_eq.
apply functional_extensionality_dep.
intros q.
apply functional_extensionality_dep.
intros β.
destruct q.
  now destruct (u 0 β).
cbn.
cbv.
+ 


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
    destruct (Yle_Sn_0 _ (α ∘ α0)).
  - destruct q0; try exact tt.
    cbn.
    simple refine (let T' := _ :
               forall p0 : Obj, p ≤ p0 -> forall p1 : Obj, p0 ≤ p1 -> Type in _).
   {
      intros.
      refine (T p0 _ p1 _). 
      assert (S p ≤ S p0).
      {
        apply Yle_n_S; auto. 
       }
      exact (X1 ∘ ((Yle_S' p0))).
      assumption.
    }
    simple refine (let X := _ : p ≤ q0 in _).
    { 
      pose (α ∘ α0). apply Yle_S_n; auto.
    }
    assert (Yle_n_S p q0 (Yle_S_n p q0 (α ∘ α0)) =
            α ∘ α0).
    generalize (α ∘ α0). clear. intro.
    apply Ynat_irr.
    change (T q0 (α ∘ α0 ∘ (Yle_S' q0)) q0 #).
    rewrite <- H.
    apply (IHp T'). intros q1 α1 x.
    apply f. intros. specialize (x _  α2).

    assert ((fun (p1 : Obj) (α3 : p0 ≤ p1) =>
      T p1
        (fun (R : Obj) (k : Hom p1 R) =>
         Yle_n_S p q1
           (fun (R0 : Obj) (k0 : Hom q1 R0) => α1 R0 k0) R
           (Yle_S' q1 R (α2 R (α3 R k))))) =
             (fun (p : Obj) (α : p0 ≤ p) =>
         T' p (fun (R : Obj) (k : Hom p R) => α1 R (α2 R (α R k))))).
    unfold T'. 
    apply functional_extensionality_dep. intro q3. apply functional_extensionality_dep. intro α4.
    apply f_equal. 
    intros. apply Ynat_irr.
    rewrite H0.
    
    apply x. 
Defined. 

Forcing Definition Box_counit : forall (A:Type) , Box A -> A using Obj Hom.
Proof.
  intros. exact (X p # p #).
Defined.

Definition fixp : forall (T:Type), ((later T) ->  T) -> T  :=
  fun T f => Box_counit _ (fixp_ T f).

Forcing Definition switchp : (later Type) -> Type using Obj Hom.
Proof.
  intros p H p' H'.
  destruct p'.
  exact unit.
  refine (H (S p') _ p' _).
  eapply H'.
  tauto.
Defined.

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.



Forcing Definition switch_next : forall (T:Type), (switchp (nextp Type T)) = (later T) using Obj Hom.
Proof.
  intros.
  eapply eq_is_eq.
  apply (funext_ext p).
  intros.
  destruct p0;
  destruct p1;
  reflexivity.
Defined.

Forcing Definition mu : (Type -> Type) -> Type using Obj Hom.
Proof.
intros p f p' H.
eapply fixp.
intro x.
refine (f p' H _ p' _).
intros.
eapply (switchp x).
auto.
Qed.


Forcing Definition unfold : forall (f: Type -> Type), mu f = f (later (mu f)) using Obj Hom.
Proof.
unfold mup.
