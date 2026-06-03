Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition point_array_strategy0 :=
  forall (p : Z) (l1 : (@list Point)) (n : Z),
    TT &&
    emp **
    ((PointArray.full p n l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Point)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.full p n l2))
      ).

Definition point_array_strategy1 :=
  forall (p : Z) (y : Z) (l1 : (@list Point)) (x : Z),
    TT &&
    emp **
    ((PointArray.seg p x y l1))
    |--
    (
    TT &&
    emp
    ) ** (
    ALL (l2 : (@list Point)),
      TT &&
      (“ (l1 = l2) ”) &&
      emp -*
      TT &&
      emp **
      ((PointArray.seg p x y l2))
      ).

Module Type point_array_Strategy_Correct.

  Axiom point_array_strategy0_correctness : point_array_strategy0.
  Axiom point_array_strategy1_correctness : point_array_strategy1.

End point_array_Strategy_Correct.
