Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.convex_hull.convex_hull_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition point_array_strategy0 :=
  forall (p : Z) (l1 : list Point) (n : Z),
    TT &&
    emp **
    ((PointArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : list Point),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.full p n l2))
      ).

Definition point_array_strategy1 :=
  forall (p : Z) (y : Z) (l1 : list Point) (x : Z),
    TT &&
    emp **
    ((PointArray.seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : list Point),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.seg p x y l2))
      ).

Definition point_array_strategy2 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((PointArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    ((PointArray.undef_seg p (Z.add x 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    (((&(((p + (x * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |->_)) **
    (((&(((p + (x * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |->_))
    ).

Definition point_array_strategy3 :=
  forall (x : Z) (y : Z) (p : Z),
    TT &&
    (“ (Z.lt x y) ”) &&
    emp **
    ((PointArray.undef_seg p x y))
    |--
    (
    TT &&
    emp **
    (((&(((p + (x * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |->_)) **
    ((PointArray.undef_seg p (Z.add x 1) y))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp **
    (((&(((p + (x * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |->_))
    ).

Definition point_array_strategy4 :=
  forall (z : Z) (y : Z) (x : Z) (p : Z) (a : Point),
    TT &&
    (“ (y = Z.add x 1) ”) &&
    (“ (Z.lt x z) ”) &&
    emp **
    ((store_point (p + x * sizeof("Point")) a)) **
    ((PointArray.undef_seg p y z))
    |--
    (
    TT &&
    emp **
    ((PointArray.undef_seg p x z))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy5 :=
  forall (x : Z) (y : Z) (p : Z) (l : list Point) (a : Point),
    TT &&
    (“ (Z.le x y) ”) &&
    emp **
    ((PointArray.seg p x y l)) **
    ((store_point (p + y * sizeof("Point")) a))
    |--
    (
    TT &&
    emp **
    ((PointArray.seg p x (Z.add y 1)
       (@app Point l (@cons Point a (@nil Point)))))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy6 :=
  forall (vy : Z) (vx : Z) (i : Z) (p : Z),
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> vx)) **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> vy))
    |--
    (
    TT &&
    emp **
    ((store_point (p + i * sizeof("Point")) (point_mk vx vy)))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy7 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (vy : Z) (vx : Z) (i : Z) (p : Z),
    TT &&
    emp **
    ((store_point (p + i * sizeof("Point")) (point_mk vx vy))) -*
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> vx)) **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> vy))
    ).

Definition point_array_strategy8 :=
  forall (vx : Z) (i : Z) (n : Z) (p : Z) (l : list Point),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.full p n l))
    |--
    (
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> point_y (Znth i l default_point))) **
    ((PointArray.missing_i p i 0 n l))
    ) ** (
    TT &&
    (“ (vx = point_x (Znth i l default_point)) ”) &&
    emp -*
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> vx))
    ).

Definition point_array_strategy9 :=
  forall (vy : Z) (i : Z) (n : Z) (p : Z) (l : list Point),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.full p n l))
    |--
    (
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> point_x (Znth i l default_point))) **
    ((PointArray.missing_i p i 0 n l))
    ) ** (
    TT &&
    (“ (vy = point_y (Znth i l default_point)) ”) &&
    emp -*
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> vy))
    ).

Definition point_array_strategy10 :=
  forall (vx : Z) (i : Z) (y : Z) (x : Z) (p : Z) (l : list Point),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> point_y (Znth (i - x) l default_point))) **
    ((PointArray.missing_i p i x y l))
    ) ** (
    TT &&
    (“ (vx = point_x (Znth (i - x) l default_point)) ”) &&
    emp -*
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> vx))
    ).

Definition point_array_strategy11 :=
  forall (vy : Z) (i : Z) (y : Z) (x : Z) (p : Z) (l : list Point),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.seg p x y l))
    |--
    (
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> point_x (Znth (i - x) l default_point))) **
    ((PointArray.missing_i p i x y l))
    ) ** (
    TT &&
    (“ (vy = point_y (Znth (i - x) l default_point)) ”) &&
    emp -*
    TT &&
    emp **
    (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> vy))
    ).

Definition point_array_strategy12 :=
  forall (i : Z) (n : Z) (p : Z) (l : list Point),
    TT &&
    (“ (Z.le 0 i) ”) &&
    (“ (Z.lt i n) ”) &&
    emp **
    ((PointArray.missing_i p i 0 n l)) **
    ((store_point (p + i * sizeof("Point"))
       (point_mk (point_x (Znth i l default_point))
                 (point_y (Znth i l default_point)))))
    |--
    (
    TT &&
    emp **
    ((PointArray.full p n l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy13 :=
  forall (i : Z) (y : Z) (x : Z) (p : Z) (l : list Point),
    TT &&
    (“ (Z.le x i) ”) &&
    (“ (Z.lt i y) ”) &&
    emp **
    ((PointArray.missing_i p i x y l)) **
    ((store_point (p + i * sizeof("Point"))
       (point_mk (point_x (Znth (i - x) l default_point))
                 (point_y (Znth (i - x) l default_point)))))
    |--
    (
    TT &&
    emp **
    ((PointArray.seg p x y l))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy14 :=
  forall (p : Z) (a : Point),
    TT &&
    emp **
    ((store_point p a))
    |--
    (
    TT &&
    emp **
    (((&((p) # "Point" ->ₛ "x")) # Int |-> point_x a)) **
    (((&((p) # "Point" ->ₛ "y")) # Int |-> point_y a))
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition point_array_strategy15 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (a : Point) (p : Z),
    TT &&
    emp **
    (((&((p) # "Point" ->ₛ "x")) # Int |-> point_x a)) **
    (((&((p) # "Point" ->ₛ "y")) # Int |-> point_y a)) -*
    TT &&
    emp **
    ((store_point p a))
    ).

Module Type point_array_Strategy_Correct.

  Axiom point_array_strategy0_correctness : point_array_strategy0.
  Axiom point_array_strategy1_correctness : point_array_strategy1.
  Axiom point_array_strategy2_correctness : point_array_strategy2.
  Axiom point_array_strategy3_correctness : point_array_strategy3.
  Axiom point_array_strategy4_correctness : point_array_strategy4.
  Axiom point_array_strategy5_correctness : point_array_strategy5.
  Axiom point_array_strategy6_correctness : point_array_strategy6.
  Axiom point_array_strategy7_correctness : point_array_strategy7.
  Axiom point_array_strategy8_correctness : point_array_strategy8.
  Axiom point_array_strategy9_correctness : point_array_strategy9.
  Axiom point_array_strategy10_correctness : point_array_strategy10.
  Axiom point_array_strategy11_correctness : point_array_strategy11.
  Axiom point_array_strategy12_correctness : point_array_strategy12.
  Axiom point_array_strategy13_correctness : point_array_strategy13.
  Axiom point_array_strategy14_correctness : point_array_strategy14.
  Axiom point_array_strategy15_correctness : point_array_strategy15.

End point_array_Strategy_Correct.
