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

Notation "P ≤ Q" := (forall R, Hom P R -> Hom Q R) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom _ R) => k).
Notation "f ∘ g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40).
Notation "f 'o' g" := (fun (R : Obj) (k : Hom _ R) => f R (g R k)) (at level 40, only parsing).

Lemma Yle_to_le : forall n m, m ≤ n -> m <= n.
Proof.
  intros n m H.
  unfold Hom in H.
  eapply H.
  eapply le_n.
Qed.

Lemma le_to_Yle : forall n m, n <= m -> n ≤ m.
Proof.
unfold Hom.
intros n m H R H'.
refine (Nat.le_trans _ n _ _ _); tauto.
Qed.


Lemma Yle_Sn_0 : forall n, S n ≤ 0 -> False.
Proof.
  unfold Hom;
  intros n H.
  specialize (H (S n) (le_n (S n))).
  inversion H.
Qed.

Definition Yle_S' m : m ≤ S m.
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
  intros p f q.
  exact (match q with
           |0 => fun _ => unit
           |S q => fun α => f q (α ∘ Yle_S' q) q # end).
Defined.

Forcing Definition later_all : Type -> Type using Obj Hom.
Proof.
  intros p f q.
  exact (match q with
           |0 => fun _ => unit
           |S q => fun α => forall r (β : r ≤ q), f r (α ∘ ((Yle_S' q) ∘ β))  r # end).
Defined.

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

Lemma S_0_absurd {n:nat} : (S n <= 0) -> False.
Proof.
  intros.
  inversion H.
Qed.
Axiom cheat:forall{A}, A.


Forcing Definition Box : Type -> Type using Obj Hom.
Proof.
  refine (fun p X q α => forall q' (α0 : q' ≤ q), X q' (α ∘ α0) q' #).
Defined.

Forcing Definition Box_counit : forall (A:Type) , Box A -> A using Obj Hom.
Proof.
intros p A BA. exact (BA p # p #).
Defined.

Forcing Definition nextp : forall (T:Type), forall t : T, later T using Obj Hom.
Proof.
  intros p T f.
  destruct p;
  cbn.
  exact tt. apply f.
Defined.

Forcing Definition sfixp : forall (T:Type), ((later T) ->  T) -> Box T using Obj Hom.
Proof.
  intros p T f q α.
  refine (nat_rect 
            (fun p0 => forall (α : p0 ≤ p) p1 (α1 : p1 ≤ p0) α2, T p1 α2 p1 #) _ _ p # q α _).
  + intros _ r r_le_0 β. apply f. intros s γ.
    destruct s; try exact tt. 
    exact (False_rect _ (S_0_absurd (Yle_to_le _ _ (r_le_0 ∘ γ)))).
  + intros ? IH β ? γ δ.
    apply f. intros s ω. destruct s; try exact tt. 
    exact (IH (β ∘ Yle_S' n) _ (Yle_S_n _ _ (γ ∘ ω ∘ (Yle_n_S _ _ #)) ) _).
Defined.

Forcing Definition sfixp_all : forall (T:Type), ((later_all T) ->  T) -> Box T using Obj Hom.
Proof.
  intros p T f q α.
  refine (nat_rect 
            (fun p0 => forall (α : p0 ≤ p) p1 (α1 : p1 ≤ p0) α2, T p1 α2 p1 #) _ _ p # q α _).
  + intros _ r r_le_0 β. apply f. intros s γ.
    destruct s; try exact tt. 
    exact (False_rect _ (S_0_absurd (Yle_to_le _ _ (r_le_0 ∘ γ)))).
  + intros ? IH β ? γ δ.
    apply f. intros s ω. destruct s; try exact tt. cbn.
    intros ? η. exact (IH (β ∘ Yle_S' n) _ (Yle_S_n _ _ (γ ∘ ω ∘ (Yle_n_S _ _ η)) ) _).
Defined.

(* Autre possibilité : sfix : ((later T -> Box T) -> Box T)
   ou (later T -> Box T) -> T) *)

Recursive Extraction sfixpᶠ.
About sfixpᶠ.

Section test.
  Variable p : Obj.
  Variable (T : forall p0 : Obj, p0 ≤ p -> forall p1 : Obj, p1 ≤ p0 -> Type).
  Variable (f : forall (p0 : Obj) (α : p0 ≤ p),
               (forall (p1 : Obj) (α0 : p1 ≤ p0), laterᶠ p1 (fun (p2 : Obj) (α1 : p2 ≤ p1) => T p2 (# ∘ (α ∘ (# ∘ (α0 ∘ (α1 ∘ #)))))) p1 #) ->
               T p0 (# ∘ (α ∘ (# ∘ #))) p0 #).
  (* (q : Obj) (α : q ≤ p). *)

  Definition fixf q := Eval compute in sfixpᶠ p T f (S q) cheat.
End test.

  Extraction fixf.
(*
sfixp :
let sfixp__U1da0_ _ f q =
  let rec f0 n r =
    match n with
    | O ->
      Obj.magic f r __ (fun p0 _ ->
        match p0 with
        | O -> Tt
        | S _ -> assert false (* absurd case *))
    | S n0 ->
      Obj.magic f r __ (fun p0 _ ->
        match p0 with
        | O -> Tt
        | S p1 -> Obj.magic f0 n0 p1)
  in f0 q q

fixf:
let fixf _ f q =
  Obj.magic f (S q) __ (fun p0 _ ->
    match p0 with
    | O -> Tt
    | S p1 -> f0 q p1

*)

  Definition fixp : forall (T:Type), ((later T) ->  T) -> T  :=
  fun T f => Box_counit _ (sfixp T f).

Forcing Translate fixp using Obj Hom.



(* Forcing Definition switchp : (later_all Type) -> Type using Obj Hom. *)
(* Proof. *)
(*   intros p H p' H'. *)
(*   refine (match p' with  *)
(*       |0 => unit *)
(*       |S q => _ end). *)
(*   exact unit. *)

(*   refine (H (S p') H' p' # p' #). *)

(* Defined. *)

Lemma funext_ext : forall (p : Obj) (f g : forall (p0 : Obj) (α : p0 ≤ p), forall p1 : Obj, p1 ≤ p0 -> Type),
 (forall (p0 p1 : Obj) (α : p0 ≤ p) (α' : p1 ≤ p0), (f p0 α p1 α') = (g p0 α p1 α')) -> f = g.
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

Inductive eq {A : Type} (x : A) : A -> Type :=  eq_refl : eq x x
where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.

Forcing Translate eq using Obj Hom.

Definition eq_is_eq : forall p A (x y: forall p0 (f:p0 ≤ p), A p0 f p0 #),
    Logic.eq x y -> eqᶠ p _ x y.
Proof.
  intros. rewrite H. apply eq_reflᶠ.
Defined.

Forcing Definition unfold_fixp : forall (f:(later Type) ->  Type), 
  fixp Type f = f (nextp Type (fixp Type f)) using Obj Hom.
Proof.
 intros p f.
 eapply eq_is_eq.
 apply (funext_ext).
 intros.
 destruct p0;
 cbn;
 f_equal;
 eapply functional_extensionality_dep;
 intros q;
 eapply functional_extensionality_dep;
 intros α''; 
 destruct q;
 cbn;
 try reflexivity.
 assert ((S q) <= 0).
 exact (α'' (S q) (le_n (S q))).
 inversion H.
 eapply functional_extensionality_dep.
 intros.
 eapply functional_extensionality_dep.
 intros.
 unfold fixpᶠ, Box_counitᶠ, sfixpᶠ.
Admitted.


Forcing Definition switch_next : forall (T:Type), (switchp (nextp Type T)) = (later T) using Obj Hom.
Proof.
  intros.
  eapply eq_is_eq.
  apply (funext_ext p).
  intros.
  destruct p0;
  destruct p1; cbn;
  try reflexivity.
  Admitted.

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
