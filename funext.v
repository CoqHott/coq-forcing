Require Forcing.
Require Import Eq.

Section Univalence.

Variable Obj : Type.
Variable Hom : Obj -> Obj -> Type.

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

Forcing Definition eq_rect_partial : forall A (x :A) (P : A -> Type),
    P x ->
    forall y (e:x = y), P y using Obj Hom.
Proof.
  intros p A x P P_refl y e.
  exact (match e p # in ᶠeq _ _ _ y' q f return P p # y' q f
         with | ᶠeq_refl _ _ _ => P_refl p # end).
Defined.

Definition apD10 {A} {B:A->Type}
           (f g : forall x, B x) (h: f = g) :
  f == g.
Proof.
  refine (eq_rect_partial _ f (fun g => f == g) _ g h).
  intro; reflexivity.
Defined. 

Opaque apD10.

Definition IsEquiv (A B : Type) (f:A -> B) :=
  { g:B -> A &
    prod ((fun x => g (f x)) == @id _) 
         ((fun x => f (g x)) == @id _ ) }.

Definition univalence_fun := forall (A B : Type),
    {f : A -> B & IsEquiv A B f} -> A = B.
                            
Forcing Translate pointwise_paths using Obj Hom.
Forcing Translate apD10 using Obj Hom.
Forcing Translate sigT using Obj Hom. 
Forcing Translate prod using Obj Hom. 
Forcing Translate ID using Obj Hom.
Forcing Translate id using Obj Hom.
Forcing Translate IsEquiv using Obj Hom. 
Forcing Translate univalence_fun using Obj Hom. 

Axiom funext_ : forall A (B : A -> Type) (f g : forall a, B a),
    IsEquiv _ _ (apD10 f g).

Definition funext := forall A (B : A -> Type) (f g : forall a, B a),
    IsEquiv _ _ (apD10 f g).

Forcing Translate funext using Obj Hom.

Definition eq__is_eq : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #),
    x = y -> ᶠeq p _ x y p #.
Proof.
  intros. destruct H. reflexivity. 
Defined.

Definition eq_is_eq_ : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #) q f,
   ᶠeq p _ x y q f -> x = y.
Proof.
  intros. destruct H. reflexivity.
Defined. 

Definition eq_is_eq_section : forall p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #)
    (e : x = y), eq_is_eq_ _ _ _ _ p # (eq__is_eq _ _ _ _ e) = e.
Proof.
  intros. destruct e. reflexivity.
Defined. 

Definition eq_is_eq_retraction  p A (x y: forall p0 (f:p ≤ p0), A p0 f p0 #)
           (e :  ᶠeq p _ x y p #)  :
    eq__is_eq _ _ _ _ (eq_is_eq_ _ _ _ _ _ _ e) = e.
Admitted. 

Definition concat : forall (A : Type) (x y z : A), x = y -> y = z -> x = z.
Proof. 
  destruct 1. exact (@id _).
Defined.

Definition ap A B (f : A -> B) x y : x = y -> f x = f y.
Proof. 
  destruct 1. reflexivity.
Defined. 

Opaque eq__is_eq.

Forcing Definition funext_preservation : funext using Obj Hom.
Proof.
  intros p A B f g. refine (ᶠexistT _ _ _ _ _).
  - intros.  
    apply eq__is_eq.
    apply funext_. intro p1.
    apply funext_. intro α0.
    apply funext_. intro a. 
    specialize (H p1 α0 a). apply eq_is_eq_ in H.
    apply apD10 in H. specialize (H p1). apply apD10 in H. exact (H #).
  - intros. split.
    + compute. intros. apply eq__is_eq.
      apply funext_. intro q1. apply funext_. intro α1. simpl. 
      eapply concat; try apply eq_is_eq_retraction. apply ap.
      set (H0 := funext_ _ _ (fun (p1 : Obj) (α2 : q1 ≤ p1) => f p1 (α ∘ α0 ∘ α1 ∘ α2)) 
                         (fun (p1 : Obj) (α2 : q1 ≤ p1) => g p1 (α ∘ α0∘ α1∘ α2))).
      destruct H0 as [H0 (H0',H0'')].
      set (x0 := (eq_is_eq_ _ _ _ _ _ _ (x q1 α1))).
      specialize (H0' x0).
      unfold id in H0'. 
      eapply concat. 2: apply H0'. apply ap.
      apply funext_. intro p2. simpl.
      set (H1 := funext_ (q1 ≤ p2)
      (fun α2 : q1 ≤ p2 =>
       forall
         a : forall (p3 : Obj) (α3 : p2 ≤ p3),
             A p3
               (fun (R : Obj) (k : Hom p3 R) =>
                α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
               #,
       B p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k))))
         (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
          a p3 (fun (R : Obj) (k : Hom p3 R) => α3 R k)) p2 
         #)
      (fun α2 : q1 ≤ p2 =>
       f p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
      (fun α2 : q1 ≤ p2 =>
       g p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))).
      destruct H1 as [H1 (H1',H1'')]. clear H0 H0' H0''.
      set (x1 := (apD10
     (fun (p3 : Obj) (α2 : q1 ≤ p3) =>
      f p3 (fun (R : Obj) (k : Hom p3 R) => α R (α0 R (α1 R (α2 R k)))))
     (fun (p3 : Obj) (α2 : q1 ≤ p3) =>
      g p3 (fun (R : Obj) (k : Hom p3 R) => α R (α0 R (α1 R (α2 R k)))))
     x0 p2)).
      specialize (H1' x1).
      unfold id in H1'. rewrite <- H1'. apply ap.
      clear H1 H1' H1''.
      apply funext_. intro α2. simpl. 
      set (H1 := funext_
       (forall (p3 : Obj) (α3 : p2 ≤ p3),
        A p3
          (fun (R : Obj) (k : Hom p3 R) =>
           α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
          #)
       (fun
          a : forall (p3 : Obj) (α3 : p2 ≤ p3),
              A p3
                (fun (R : Obj) (k : Hom p3 R) =>
                 α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
                # =>
        B p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k))))
          (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
           a p3 (fun (R : Obj) (k : Hom p3 R) => α3 R k)) p2 
          #)
       (f p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
       (g p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))).
      destruct H1 as [H1 (H1',H1'')].
      set (x2 := (apD10
     (fun α3 : q1 ≤ p2 =>
      f p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α3 R k)))))
     (fun α3 : q1 ≤ p2 =>
      g p2 (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α3 R k)))))
     x1 α2)).
      specialize (H1' x2).
      unfold id in H1'. rewrite <- H1'. apply ap.
      clear H1 H1' H1''.
      apply funext_. intro a. simpl in *.
      destruct (x p2 (α1 ∘ α2)). 
      unfold apD10.
      apply ap. 
      apply funext_. intro α2.
      apply ap. 
      fold eq__is_eq. 
      
      rewrite <- H0'. 
      simpl in H0'. apply apD10 in H0'. rewrite <- H0'. 
      assert ((fun p2 : Obj =>
        (let
         (x0, _) :=
         funext_ (q1 ≤ p2)
           (fun α2 : q1 ≤ p2 =>
            forall
              a : forall (p3 : Obj) (α3 : p2 ≤ p3),
                  A p3
                    (fun (R : Obj) (k : Hom p3 R) =>
                     α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
                    #,
            B p2
              (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k))))
              (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
               a p3 (fun (R : Obj) (k : Hom p3 R) => α3 R k)) p2 
              #)
           (fun α2 : q1 ≤ p2 =>
            f p2
              (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
           (fun α2 : q1 ≤ p2 =>
            g p2
              (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
         in
         x0)
          (fun α2 : q1 ≤ p2 =>
           (let
            (x0, _) :=
            funext_
              (forall (p3 : Obj) (α3 : p2 ≤ p3),
               A p3
                 (fun (R : Obj) (k : Hom p3 R) =>
                  α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
                 #)
              (fun
                 a : forall (p3 : Obj) (α3 : p2 ≤ p3),
                     A p3
                       (fun (R : Obj) (k : Hom p3 R) =>
                        α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
                       # =>
               B p2
                 (fun (R : Obj) (k : Hom p2 R) =>
                  α R (α0 R (α1 R (α2 R k))))
                 (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
                  a p3 (fun (R : Obj) (k : Hom p3 R) => α3 R k)) p2 
                 #)
              (f p2
                 (fun (R : Obj) (k : Hom p2 R) =>
                  α R (α0 R (α1 R (α2 R k)))))
              (g p2
                 (fun (R : Obj) (k : Hom p2 R) =>
                  α R (α0 R (α1 R (α2 R k))))) in
            x0)
             (fun
                a : forall (p3 : Obj) (α3 : p2 ≤ p3),
                    A p3
                      (fun (R : Obj) (k : Hom p3 R) =>
                       α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
                      # =>
              match
                match
                  match
                    match
                      x p2 (α1 ∘ α2) in (ᶠeq _ _ _ y' q f0)
                      return
                        (forall
                           x1 : forall (p3 : Obj) (α3 : q ≤ p3),
                                A p3
                                  (fun (R : Obj) (k : Hom p3 R) =>
                                   α R (α0 R (α1 R ...))) p3 
                                  #,
                         ᶠeq q
                           (fun (p3 : Obj) (α3 : q ≤ p3) =>
                            B p3
                              (fun (R : Obj) (k : Hom p3 R) =>
                               α R (α0 R (α1 R ...)))
                              (fun (p4 : Obj) (α4 : p3 ≤ p4) =>
                               x1 p4 (α3 ∘ α4)))
                           (fun (p3 : Obj) (α3 : q ≤ p3) =>
                            f p3
                              (fun (R : Obj) (k : Hom p3 R) =>
                               α R (α0 R (α1 R ...)))
                              (fun (p4 : Obj) (α4 : p3 ≤ p4) =>
                               x1 p4 (α3 ∘ α4)))
                           (fun (p3 : Obj) (α3 : q ≤ p3) =>
                            y' p3 (f0 ∘ α3)
                              (fun (p4 : Obj) (α4 : p3 ≤ p4) =>
                               x1 p4 (α3 ∘ α4))) q 
                           #)
                    with
                    | ᶠeq_refl _ _ _ =>
                        fun
                          x0 : forall (p3 : Obj) (α3 : p2 ≤ p3),
                               A p3
                                 (fun (R : Obj) (k : Hom p3 R) =>
                                  α R (α0 R (α1 R (α2 R (...))))) p3 
                                 # =>
                        ᶠeq_refl p2
                          (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
                           B p3
                             (fun (R : Obj) (k : Hom p3 R) =>
                              α R (α0 R (α1 R (α2 R (...)))))
                             (fun (p4 : Obj) (α4 : p3 ≤ p4) =>
                              x0 p4 (α3 ∘ α4)))
                          (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
                           f p3
                             (fun (R : Obj) (k : Hom p3 R) =>
                              α R (α0 R (α1 R (α2 R (...)))))
                             (fun (p4 : Obj) (α4 : p3 ≤ p4) =>
                              x0 p4 (α3 ∘ α4)))
                    end a in (ᶠeq _ _ _ y p3 α3)
                    return
                      ((fun (p4 : Obj) (α4 : p2 ≤ p4) =>
                        f p4
                          (fun (R : Obj) (k : Hom p4 R) =>
                           α R (α0 R (α1 R (α2 R (α4 R k)))))
                          (fun (p5 : Obj) (α5 : p4 ≤ p5) => a p5 (α4 ∘ α5))) =
                       y)
                  with
                  | ᶠeq_refl _ _ _ =>
                      eq_refl
                        (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
                         f p3
                           (fun (R : Obj) (k : Hom p3 R) =>
                            α R (α0 R (α1 R (α2 R (α3 R k)))))
                           (fun (p4 : Obj) (α4 : p3 ≤ p4) =>
                            a p4 (α3 ∘ α4)))
                  end in (_ = b)
                  return
                    (forall x0 : Obj,
                     (fun α3 : p2 ≤ x0 =>
                      f x0
                        (fun (R : Obj) (k : Hom x0 R) =>
                         α R (α0 R (α1 R (α2 R (α3 R k)))))
                        (fun (p3 : Obj) (α4 : x0 ≤ p3) => a p3 (α3 ∘ α4))) =
                     b x0)
                with
                | eq_refl _ =>
                    fun x0 : Obj =>
                    eq_refl
                      (fun α3 : p2 ≤ x0 =>
                       f x0
                         (fun (R : Obj) (k : Hom x0 R) =>
                          α R (α0 R (α1 R (α2 R (α3 R k)))))
                         (fun (p3 : Obj) (α4 : x0 ≤ p3) => a p3 (α3 ∘ α4)))
                end p2 in (_ = b)
                return
                  (forall x0 : p2 ≤ p2,
                   f p2
                     (fun (R : Obj) (k : Hom p2 R) =>
                      α R (α0 R (α1 R (α2 R (x0 R k)))))
                     (fun (p3 : Obj) (α3 : p2 ≤ p3) => a p3 (x0 ∘ α3)) =
                   b x0)
              with
              | eq_refl _ =>
                  fun x0 : p2 ≤ p2 =>
                  eq_refl
                    (f p2
                       (fun (R : Obj) (k : Hom p2 R) =>
                        α R (α0 R (α1 R (α2 R (x0 R k)))))
                       (fun (p3 : Obj) (α3 : p2 ≤ p3) => a p3 (x0 ∘ α3)))
              end #))) = 
      set (H1 := funext_ (q1 ≤ p2)
           (fun α2 : q1 ≤ p2 =>
            forall
              a : forall (p3 : Obj) (α3 : p2 ≤ p3),
                  A p3
                    (fun (R : Obj) (k : Hom p3 R) =>
                     α R (α0 R (α1 R (α2 R (α3 R k))))) p3 
                    #,
            B p2
              (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k))))
              (fun (p3 : Obj) (α3 : p2 ≤ p3) =>
               a p3 (fun (R : Obj) (k : Hom p3 R) => α3 R k)) p2 
              #)
           (fun α2 : q1 ≤ p2 =>
            f p2
              (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
           (fun α2 : q1 ≤ p2 =>
            g p2
              (fun (R : Obj) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
         ).
         
      destruct p2. 
      destruct 
      set (H1 := funext_ _ _ (fun (α0 : p0 ≤ p1) => f p1 (α ∘ α0)) 
                        (fun (α0 : p0 ≤ p1) => g p1 (α ∘ α0))).

      simpl. set (x0 := x q1 α1).
      destruct (funext_ bool
        (fun a : bool =>
         forall (f0 : q1 ≤ a)
           (a0 : forall (p2 : bool) (α2 : a ≤ p2),
                 A p2
                   (fun (R : bool) (k : Hom p2 R) =>
                    α R (α0 R (α1 R (f0 R (α2 R k))))) p2
                   (fun (R : bool) (k : Hom p2 R) => k)),
         B a (fun (R : bool) (k : Hom a R) => α R (α0 R (α1 R (f0 R k))))
           (fun (p2 : bool) (α2 : a ≤ p2) =>
            a0 p2 (fun (R : bool) (k : Hom p2 R) => α2 R k)) a
           (fun (R : bool) (k : Hom a R) => k))
        (fun (p2 : bool) (α2 : q1 ≤ p2) =>
         f p2
           (fun (R : bool) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))
        (fun (p2 : bool) (α2 : q1 ≤ p2) =>
         g p2
           (fun (R : bool) (k : Hom p2 R) => α R (α0 R (α1 R (α2 R k)))))).
      clear x. 
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