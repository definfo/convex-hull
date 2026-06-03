Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
From ListLib.Base Require Import Positional.
From ConvexHull Require Import Record_Geo_Point Point_Order.

Local Open Scope Z_scope.
Import ListNotations.

Definition PointCoordsBound (l : list point) : Prop :=
  Forall (fun p => point_in_bound p) l.

Definition point_swap (l : list point) (i j : Z) : list point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Definition point_mk (x y : Z) : point :=
  {| point_x := x; point_y := y |}.

Definition PointPermutation : list point -> list point -> Prop :=
  @Permutation point.

Definition PointSameOutsideRange (l l1 : list point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

Definition PointSortedRange_Point
    (gp : point) (l : list point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_polar gp (Znth i l default_point) (Znth j l default_point) <= 0.

Definition PointTailReverseState
    (before cur : list point) (n rev_i rev_j : Z) : Prop :=
  Zlength cur = Zlength before /\
  0 <= n <= Zlength before /\
  1 <= rev_i <= n /\
  0 <= rev_j < n /\
  rev_j = n - rev_i /\
  rev_i <= rev_j + 1 /\
  (forall k, 0 <= k < Zlength before -> (k = 0 \/ n <= k) ->
     Znth k cur default_point = Znth k before default_point) /\
  (forall k, 1 <= k < rev_i ->
     Znth k cur default_point = Znth (n - k) before default_point) /\
  (forall k, rev_i <= k <= rev_j ->
     Znth k cur default_point = Znth k before default_point) /\
  (forall k, rev_j < k < n ->
     Znth k cur default_point = Znth (n - k) before default_point).

Definition PointPolarPartitionedAt
    (gp : point) (l : list point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => point_cmp_polar gp x (Znth p l default_point) <= 0)
         (sublist low p l) /\
  Forall (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
         (sublist (p + 1) (high + 1) l).

Definition PointPolarPartitionScanInv
    (gp : point) (before cur : list point)
    (low high : Z) (pivot : point) (i j : Z) : Prop :=
  PointPermutation before cur /\
  PointSameOutsideRange before cur low high /\
  Znth high cur default_point = pivot /\
  (forall k, low <= k <= i ->
     point_cmp_polar gp (Znth k cur default_point) pivot <= 0) /\
  (forall k, i < k < j ->
     point_cmp_polar gp pivot (Znth k cur default_point) < 0).
