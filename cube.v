Set Primitive Projections.
Unset Printing Primitive Projection Compatibility.
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
  + intros A0 A1 Ae x0 x1. cbn in *.
    exact (Pack _ _ (C.(F) _ _ (Ae.(Te) x0 x1))).
(*     exact (forall x x', C.(F) _ _ (Ae.(Te) x0 x1) x x'). *)
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
Check ((A 3).(Te).(T0).(Te) :
  forall x₀ : Pack (A 3).(T0).(T0).(T0) (A 3).(T0).(T0).(T1) (A 3).(T0).(T0).(Te),
  forall x₁ : Pack (A 3).(T1).(T0).(T0) (A 3).(T1).(T0).(T1) (A 3).(T1).(T0).(Te),
    (A 3).(Te).(T0).(T0) x₀.(T0) x₁.(T0) ->
    (A 3).(Te).(T0).(T1) x₀.(T1) x₁.(T1) ->
    Type).
Check ((A 3).(Te).(T1).(Te) :
  forall x₀ : Pack (A 3).(T0).(T1).(T0) (A 3).(T0).(T1).(T1) (A 3).(T0).(T1).(Te),
  forall x₁ : Pack (A 3).(T1).(T1).(T0) (A 3).(T1).(T1).(T1) (A 3).(T1).(T1).(Te),
    (A 3).(Te).(T1).(T0) x₀.(T0) x₁.(T0) ->
    (A 3).(Te).(T1).(T1) x₀.(T1) x₁.(T1) ->
    Type).

Eval compute in ltac:(let T := type of (A 3).(Te).(Te) in exact T).

Check ((A 3).(Te).(Te) :
  forall x₀ :
    Pack
      (Pack (A 3).(T0).(T0).(T0) (A 3).(T0).(T0).(T1) (A 3).(T0).(T0).(Te))
      (Pack (A 3).(T0).(T1).(T0) (A 3).(T0).(T1).(T1) (A 3).(T0).(T1).(Te))
      (fun x₀₀ x₀₁ => Pack
        ((A 3).(T0).(Te).(T0) x₀₀.(T0) x₀₁.(T0))
        ((A 3).(T0).(Te).(T1) x₀₀.(T1) x₀₁.(T1))
        (fun x₀ᵢ₀ x₀ᵢ₁ => (A 3).(T0).(Te).(Te) x₀₀ x₀₁ x₀ᵢ₀ x₀ᵢ₁)),
  forall x₁ :
    Pack
      (Pack (A 3).(T1).(T0).(T0) (A 3).(T1).(T0).(T1) (A 3).(T1).(T0).(Te))
      (Pack (A 3).(T1).(T1).(T0) (A 3).(T1).(T1).(T1) (A 3).(T1).(T1).(Te))
      (fun x₁₀ x₁₁ => Pack
        ((A 3).(T1).(Te).(T0) x₁₀.(T0) x₁₁.(T0))
        ((A 3).(T1).(Te).(T1) x₁₀.(T1) x₁₁.(T1))
        (fun x₁ᵢ₀ x₁ᵢ₁ => (A 3).(T1).(Te).(Te) x₁₀ x₁₁ x₁ᵢ₀ x₁ᵢ₁)),
  Pack
    ((A 3).(Te).(T0).(T0) x₀.(T0).(T0) x₁.(T0).(T0) -> (A 3).(Te).(T1).(T0) x₀.(T1).(T0) x₁.(T1).(T0) -> Type)
    ((A 3).(Te).(T0).(T1) x₀.(T0).(T1) x₁.(T0).(T1) -> (A 3).(Te).(T1).(T1) x₀.(T1).(T1) x₁.(T1).(T1) -> Type)
    (fun A₀ A₁ =>
      forall x'₀ : Pack
        ((A 3).(Te).(T0).(T0) x₀.(T0).(T0) x₁.(T0).(T0))
        ((A 3).(Te).(T0).(T1) x₀.(T0).(T1) x₁.(T0).(T1))
        ((A 3).(Te).(T0).(Te) (x₀.(T0)) (x₁.(T0))),
      forall x'₁ : Pack
        ((A 3).(Te).(T1).(T0) x₀.(T1).(T0) x₁.(T1).(T0))
        ((A 3).(Te).(T1).(T1) x₀.(T1).(T1) x₁.(T1).(T1))
        ((A 3).(Te).(T1).(Te) (x₀.(T1)) (x₁.(T1))),
      A₀ (x'₀.(T0)) (x'₁.(T0)) -> A₁ (x'₀.(T1)) (x'₁.(T1)) -> Type
    )).
