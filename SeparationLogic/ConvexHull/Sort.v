Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Point Point_Order Point_Array_Specs.

Local Open Scope Z_scope.

(** Compatibility layer.

    The organized definitions live in [Point_Order] and [Point_Array_Specs].
    This file preserves the previous [ConvexHull.Sort.*] names. *)

Definition x : point -> Z := Point_Order.x.
Definition y : point -> Z := Point_Order.y.

Definition default_point : point := Point_Order.default_point.

Definition point_cmp_xy : point -> point -> Z := Point_Order.point_cmp_xy.
Definition point_cross : point -> point -> point -> Z := Point_Order.point_cross.
Definition point_dot : point -> point -> point -> Z := Point_Order.point_dot.
Definition point_at_mid : point -> point -> point -> Z := Point_Order.point_at_mid.
Definition point_cmp_polar : point -> point -> point -> Z := Point_Order.point_cmp_polar.

Lemma point_cross_gt_0_ccw : forall a b c,
  point_cross a b c > 0 <-> ccw a b c.
Proof.
  apply Point_Order.point_cross_gt_0_ccw.
Qed.

Lemma point_cross_le_0_not_ccw : forall a b c,
  point_cross a b c <= 0 <-> ~ ccw a b c.
Proof.
  apply Point_Order.point_cross_le_0_not_ccw.
Qed.

Definition point_bound : Z := Point_Order.point_bound.
Definition point_in_bound : point -> Prop := Point_Order.point_in_bound.

Lemma point_bound_sub : forall a b,
  point_in_bound a -> point_in_bound b ->
  -20000 <= x a - x b <= 20000 /\ -20000 <= y a - y b <= 20000.
Proof.
  apply Point_Order.point_bound_sub.
Qed.

Definition PointCoordsBound : list point -> Prop :=
  Point_Array_Specs.PointCoordsBound.

Definition point_swap : list point -> Z -> Z -> list point :=
  Point_Array_Specs.point_swap.

Definition point_mk : Z -> Z -> point :=
  Point_Array_Specs.point_mk.

Definition PointPermutation : list point -> list point -> Prop :=
  Point_Array_Specs.PointPermutation.

Definition PointSameOutsideRange : list point -> list point -> Z -> Z -> Prop :=
  Point_Array_Specs.PointSameOutsideRange.

Definition PointSortedRange_Point : point -> list point -> Z -> Z -> Prop :=
  Point_Array_Specs.PointSortedRange_Point.

Definition PointTailReverseState : list point -> list point -> Z -> Z -> Z -> Prop :=
  Point_Array_Specs.PointTailReverseState.

Definition PointPolarPartitionedAt : point -> list point -> Z -> Z -> Z -> Prop :=
  Point_Array_Specs.PointPolarPartitionedAt.

Definition PointPolarPartitionScanInv :
  point -> list point -> list point -> Z -> Z -> point -> Z -> Z -> Prop :=
  Point_Array_Specs.PointPolarPartitionScanInv.
