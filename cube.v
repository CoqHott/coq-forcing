Set Primitive Projections.
Set Universe Polymorphism.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).

Record CUBE :=
  { T : Type;
    R : T -> T -> Type;
    h : T -> Type;
    F : forall A0 A1 : T, R A0 A1 -> h A0 -> h A1 -> Type;
    M : forall A0 A1, R A0 A1 -> h A0 -> h A1 -> T;
  }.

Record Pack A B R := pack
  { T0 : A ;
    T1 : B;
    Te : R T0 T1
  }.

Arguments T0 {_ _ _} _.
Arguments T1 {_ _ _} _.
Arguments Te {_ _ _} _.
Arguments pack {_ _ _} _ _ _.

Definition Cube0 : CUBE :=
  Build_CUBE Type (fun A0 A1 => A0 -> A1 -> Type) (fun x => x)
                              (fun _ _ X x y => X x y)
                              (fun _ _ X x y => X x y).

Definition CubeS (C : CUBE) : CUBE.
Proof.
- simple refine (Build_CUBE _ _ _ _ _).
  + exact (Pack C.(T) C.(T) C.(R)).
  + intros A0 A1.
    simple refine (Pack (C.(R) A0.(T0) A1.(T0)) (C.(R) A0.(T1) A1.(T1)) _).
    intros r0 r1.
    refine (let h' := fun A:Pack C.(T) C.(T) C.(R) =>
                        (Pack (C.(h) A.(T0)) (C.(h) A.(T1)) (C.(F) _ _ A.(Te)))
            in _).
    simple refine (forall (x0 : h' A0) (x1 : h' A1), _).
    simple refine (C.(R) _ _).
    simple refine (C.(M) _ _ r0 x0.(T0) x1.(T0)).
    simple refine (C.(M) _ _ r1 x0.(T1) x1.(T1)).
  + intros A. exact (Pack (C.(h) A.(T0)) (C.(h) A.(T1)) (C.(F) _ _ A.(Te))).
  + intros A0 A1 Ae x0 x1. exact (forall x x', C.(F) _ _ (Ae.(Te) x0 x1) x x').
  + intros A0 A1 r x0 x1. 
    cbn in *. simple refine (pack (C.(M) _ _ r.(T0) x0.(T0) x1.(T0))
                                  (C.(M) _ _ r.(T1) x0.(T1) x1.(T1))
                                  (r.(Te) x0 x1)).
Defined.

Fixpoint cube (n : nat) := match n with 0 => Cube0 | S n => CubeS (cube n) end.

Definition TYPE := forall n, (cube n).(T).
Definition ELT (A : TYPE) := forall n, (cube n).(h) (A n).

Axiom A : TYPE.

Check (A 0 : Type).

Check ((A 1).(T0) : Type).
Check ((A 1).(T1) : Type).
Check ((A 1).(Te) : (A 1).(T0) -> (A 1).(T1) -> Type).

Check ((A 2).(T0).(T0) : Type).
Check ((A 2).(T0).(T1) : Type).
Check ((A 2).(T0).(Te) : (A 2).(T0).(T0) -> (A 2).(T0).(T1) -> Type).
Check ((A 2).(T1).(T0) : Type).
Check ((A 2).(T0).(T1) : Type).
Check ((A 2).(T1).(Te) : (A 2).(T1).(T0) -> (A 2).(T1).(T1) -> Type).
Check ((A 2).(Te).(T0) : (A 2).(T0).(T0) -> (A 2).(T1).(T0) -> Type).
Check ((A 2).(Te).(T1) : (A 2).(T0).(T1) -> (A 2).(T1).(T1) -> Type).
Check ((A 2).(Te).(Te) :
  forall x₀ : Pack (A 2).(T0).(T0) (A 2).(T0).(T1) (A 2).(T0).(Te),
  forall x₁ : Pack (A 2).(T1).(T0) (A 2).(T1).(T1) (A 2).(T1).(Te),
  (A 2).(Te).(T0) x₀.(T0) x₁.(T0) -> (A 2).(Te).(T1) x₀.(T1) x₁.(T1) -> Type).

Check ((A 3).(T0).(T0).(T0) : Type).
Check ((A 3).(T0).(T0).(T1) : Type).
Check ((A 3).(T0).(T0).(Te) : (A 3).(T0).(T0).(T0) -> (A 3).(T0).(T0).(T1) -> Type).
Check ((A 3).(T0).(T1).(T0) : Type).
Check ((A 3).(T0).(T1).(T1) : Type).
Check ((A 3).(T0).(T1).(Te) : (A 3).(T0).(T1).(T0) -> (A 3).(T0).(T1).(T1) -> Type).
Check ((A 3).(T0).(Te).(Te) :
  forall x₀ : Pack (A 3).(T0).(T0).(T0) (A 3).(T0).(T0).(T1) (A 3).(T0).(T0).(Te),
  forall x₁ : Pack (A 3).(T0).(T1).(T0) (A 3).(T0).(T1).(T1) (A 3).(T0).(T1).(Te),
  (A 3).(T0).(Te).(T0) x₀.(T0) x₁.(T0) -> (A 3).(T0).(Te).(T1) x₀.(T1) x₁.(T1) -> Type).
Check ((A 3).(T1).(T0).(T0) : Type).
Check ((A 3).(T1).(T0).(T1) : Type).
Check ((A 3).(T1).(T0).(Te) : (A 3).(T1).(T0).(T0) -> (A 3).(T1).(T0).(T1) -> Type).
Check ((A 3).(T1).(T1).(T0) : Type).
Check ((A 3).(T1).(T1).(T1) : Type).
Check ((A 3).(T1).(T1).(Te) : (A 3).(T1).(T1).(T0) -> (A 3).(T1).(T1).(T1) -> Type).
Check ((A 3).(T1).(Te).(Te) :
  forall x₀ : Pack (A 3).(T1).(T0).(T0) (A 3).(T1).(T0).(T1) (A 3).(T1).(T0).(Te),
  forall x₁ : Pack (A 3).(T1).(T1).(T0) (A 3).(T1).(T1).(T1) (A 3).(T1).(T1).(Te),
  (A 3).(T1).(Te).(T0) x₀.(T0) x₁.(T0) -> (A 3).(T1).(Te).(T1) x₀.(T1) x₁.(T1) -> Type).
Check ((A 3).(T0).(Te).(T0) : (A 3).(T0).(T0).(T0) -> (A 3).(T0).(T1).(T0) -> Type).
Check ((A 3).(T0).(Te).(T1) : (A 3).(T0).(T0).(T1) -> (A 3).(T0).(T1).(T1) -> Type).
Check ((A 3).(T1).(Te).(T0) : (A 3).(T1).(T0).(T0) -> (A 3).(T1).(T1).(T0) -> Type).
Check ((A 3).(T1).(Te).(T1) : (A 3).(T1).(T0).(T1) -> (A 3).(T1).(T1).(T1) -> Type).
Check ((A 3).(Te).(T0).(T0) : (A 3).(T0).(T0).(T0) -> (A 3).(T1).(T0).(T0) -> Type).
Check ((A 3).(Te).(T0).(T1) : (A 3).(T0).(T0).(T1) -> (A 3).(T1).(T0).(T1) -> Type).
Check ((A 3).(Te).(T1).(T0) : (A 3).(T0).(T1).(T0) -> (A 3).(T1).(T1).(T0) -> Type).
Check ((A 3).(Te).(T1).(T1) : (A 3).(T0).(T1).(T1) -> (A 3).(T1).(T1).(T1) -> Type).
Check ((A 3).(Te).(Te) :
  forall x₀ :
    Pack
      (Pack (A 3).(T0).(T0).(T0) (A 3).(T0).(T0).(T1) (A 3).(T0).(T0).(Te))
      (Pack (A 3).(T0).(T1).(T0) (A 3).(T0).(T1).(T1) (A 3).(T0).(T1).(Te))
      (fun x₀₀ x₀₁ =>
        forall x₀ᵢ₀ : (A 3).(T0).(Te).(T0) x₀₀.(T0) x₀₁.(T0),
        forall x₀ᵢ₁ : (A 3).(T0).(Te).(T1) x₀₀.(T1) x₀₁.(T1),
        _),
  forall x₁ :
    Pack
      (Pack (A 3).(T1).(T0).(T0) (A 3).(T1).(T0).(T1) (A 3).(T1).(T0).(Te))
      (Pack (A 3).(T1).(T1).(T0) (A 3).(T1).(T1).(T1) (A 3).(T1).(T1).(Te))
      (fun x₁₀ x₁₁ =>
        forall x₁ᵢ₀ : (A 3).(T1).(Te).(T0) x₁₀.(T0) x₁₁.(T0),
        forall x₁ᵢ₁ : (A 3).(T1).(Te).(T1) x₁₀.(T1) x₁₁.(T1),
        _),
  Pack _ _ _).

Eval compute in
(fun
             (x₀₀ : Pack (T0 (T0 (T0 (A 3)))) (T1 (T0 (T0 (A 3))))
                      (Te (T0 (T0 (A 3)))))
             (x₀₁ : Pack (T0 (T1 (T0 (A 3)))) (T1 (T1 (T0 (A 3))))
                      (Te (T1 (T0 (A 3))))) =>
           forall (x₀ᵢ₀ : T0 (Te (T0 (A 3))) (T0 x₀₀) (T0 x₀₁))
             (x₀ᵢ₁ : T1 (Te (T0 (A 3))) (T1 x₀₀) (T1 x₀₁)),
           F (cube 0)
             (M (cube 0) (T0 (T0 (T0 (A 3)))) (T0 (T1 (T0 (A 3))))
                (T0 (Te (T0 (A 3)))) (T0 x₀₀) (T0 x₀₁))
             (M (cube 0) (T1 (T0 (T0 (A 3)))) (T1 (T1 (T0 (A 3))))
                (T1 (Te (T0 (A 3)))) (T1 x₀₀) (T1 x₀₁))
             (Te (Te (T0 (A 3))) x₀₀ x₀₁) x₀ᵢ₀ x₀ᵢ₁).

(*
Definition Arrowᶠ (A : TYPE) (B : TYPE) : TYPE.
Proof.
intros n; revert A B; induction n; cbn - [cube]; intros A B.
+ exact (ELT A -> (B 0)).
+ cbn.
  simple refine (pack _ _ _).
  fold (cube n).(T).
cbn.


Definition Typeᶠ : TYPE.
Proof.
intros n; induction n; cbn.
+ exact Type.
+ 
Defined.



 *)