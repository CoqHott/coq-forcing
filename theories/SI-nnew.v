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
  intros p f q α.
  destruct q.
  exact unit.
  refine (f q (α o Yle_S' q) q #). 
Defined.
Print laterᶠ. 

(* refine (forall r : Obj, forall α' : (r ≤ q), f r _ r _). *)
(*   exact ((α ∘ (Yle_S' q)) ∘ α'). *)
(*   exact #. *)
(* Defined. *)

Print laterᶠ.

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

Forcing Definition Box : Type -> Type using Obj Hom.
Proof.
  refine (fun p X q α => forall q' (α0 : q' ≤ q), X q' (α ∘ α0) q' #).
Defined.

Forcing Definition Box_counit : forall (A:Type) , Box A -> A using Obj Hom.
Proof.
  intros. eapply X.  (* exact (X p # p #). *)
Defined.

Forcing Definition nextp : forall (T:Type), forall t : T, later T using Obj Hom.
Proof.
  intros p T f.
  destruct p;
  cbn.
  exact tt. apply f.
Defined.

Lemma S_0_absurd {n:nat} : (S n <= 0) -> False.
Proof.
  intros.
  inversion H.
Qed.
Axiom cheat:forall{A}, A.
Forcing Definition sfixp : forall (T:Type), ((later T) ->  T) -> Box T using Obj Hom.
Proof.
  intros p T f q α.
  change (fun R k => α R k) with α.
  refine (nat_rect (fun p0 => forall (α:p0≤p) (p1:Obj) (α1:p1≤p0) (α2:p1≤p), T p1 α2 p1 #) _ _ _ _ _ _ _).
  intros α' r α'' α'''.
apply f.
intros.
 (* refine (nat_rect (fun p0 => forall (α:p0≤p),  T p0 α p0 #) *)
red.
destruct p0;
 try exact tt.
 apply False_rect;
 apply (S_0_absurd (Yle_to_le  _ _ (α'' o α0))).
 intros n IH α' r α'' α'''.
 (* destruct r. *)
 (* - apply f. *)
 (*   intros. *)
 (*   red. *)
 (*   destruct p0. *)
 (*   exact tt. *)
 (*   apply cheat. *)
 (* - apply f. *)
 (*   intros. *)
 (*   destruct p0. *)
 (*   cbn. exact tt. *)
 (*   cbn. *)
 (*   intros. *)
 (*   apply IH. *)
 (*   exact (α' ∘ Yle_S' n). *)
 (*   exact (Yle_S_n r0 n (α'' ∘ (α0 ∘ (Yle_n_S r0 p0 α'0)))). *)
   apply f; intros;
 destruct p0 as [|p0];
 try exact tt.
 cbn.
 intros.
 eapply IH.
 exact (α' ∘ Yle_S' n).
 exact (Yle_S_n p0 n (α'' ∘ α0)). (* ∘ (Yle_n_S r0 p0 α'0)))). *)
 exact α.
 exact #.
Defined.

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



Forcing Definition switchp : (later Type) -> Type using Obj Hom.
Proof.
  intros p H p' H'.
  destruct p'.
  exact unit.
  refine (H (S p') _ p' _ p' _);
  tauto
Defined.

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
