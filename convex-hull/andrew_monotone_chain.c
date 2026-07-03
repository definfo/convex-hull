#include "convex_hull_def.h"
#include "safeexec_def.h"

/*@ Extern Coq (is_convex_hull : list Point -> list Point -> Prop)
               (andrew_lower_scan_inv : list Point -> list Point -> Z -> Z -> Prop)
               (andrew_upper_scan_inv : list Point -> list Point -> Z -> Z -> Z
   -> Prop) (point_bound : Z) (point_in_bound : Point -> Prop) (points_in_bound
   : list Point -> Prop) (points_not_all_same : list Point -> Prop)
               (point_permutation : list Point -> list Point -> Prop)
               (point_same_outside_range : list Point -> list Point -> Z -> Z ->
   Prop) (point_xy_sorted : list Point -> Prop) (point_xy_sorted_range : list
   Point -> Z -> Z -> Prop) (point_xy_partitioned_at : list Point -> Z -> Z -> Z
   -> Prop) (point_xy_partition_scan_inv : list Point -> list Point -> Z -> Z ->
   Point -> Z -> Z -> Prop) (point_cmp_leftdown : Point -> Point -> Z)
               (point_cross_by_value : Z -> Z -> Z -> Z -> Z -> Z -> Z)
               (default_point : Point)
               (empty_point_stack : list Point)
               (andrew_monotone_chain_m : list Point -> program (list Point) unit)
               (build_chain : list Point -> program (list Point) unit)
               (build_upper_chain_cont : list Point -> list Point -> program (list Point) unit)
               (andrew_lower_remaining_cont : list Point -> list Point -> Z ->
   (unit -> list Point -> Prop) -> Prop)
               (andrew_upper_remaining_cont : list Point -> list Point -> Z -> Z ->
   (unit -> list Point -> Prop) -> Prop)
               (point_prefix_reverse_state : list Point -> list Point -> Z -> Z ->
   Prop)
*/

static int cmp_xy(int a_x, int a_y, int b_x, int b_y)
/*@ Require emp
    Ensure a_x == a_x@pre && a_y == a_y@pre &&
           b_x == b_x@pre && b_y == b_y@pre &&
           __return == point_cmp_leftdown(point_mk(a_x@pre, a_y@pre),
                                          point_mk(b_x@pre, b_y@pre))
*/
{
  /*@ Assert
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre
  */
  if (a_x < b_x)
    return -1;
  if (a_x > b_x)
    return 1;
  if (a_y < b_y)
    return -1;
  if (a_y > b_y)
    return 1;
  return 0;
}

static int cross_prod(int a_x, int a_y, int b_x, int b_y, int c_x, int c_y)
/*@ Require -point_bound <= a_x && a_x <= point_bound &&
            -point_bound <= a_y && a_y <= point_bound &&
            -point_bound <= b_x && b_x <= point_bound &&
            -point_bound <= b_y && b_y <= point_bound &&
            -point_bound <= c_x && c_x <= point_bound &&
            -point_bound <= c_y && c_y <= point_bound
    Ensure a_x == a_x@pre && a_y == a_y@pre &&
           b_x == b_x@pre && b_y == b_y@pre &&
           c_x == c_x@pre && c_y == c_y@pre &&
           __return == point_cross_by_value(a_x, a_y, b_x, b_y, c_x, c_y)
*/
{
  /*@ Assert
        a_x == a_x@pre && a_y == a_y@pre &&
        b_x == b_x@pre && b_y == b_y@pre &&
        c_x == c_x@pre && c_y == c_y@pre &&
        -point_bound <= a_x && a_x <= point_bound &&
        -point_bound <= a_y && a_y <= point_bound &&
        -point_bound <= b_x && b_x <= point_bound &&
        -point_bound <= b_y && b_y <= point_bound &&
        -point_bound <= c_x && c_x <= point_bound &&
        -point_bound <= c_y && c_y <= point_bound
  */
  return (b_x - a_x) * (c_y - a_y) - (b_y - a_y) * (c_x - a_x);
}

static void swap_points(struct Point *pts, int n, int i, int j)
/*@ With (pts_l : list Point)
    Require
      0 <= i && i < n && 0 <= j && j < n &&
      i != j &&
      Zlength(pts_l) == n &&
      PointArray::full(pts, n, pts_l)
    Ensure
      pts == pts@pre &&
      n == n@pre &&
      i == i@pre &&
      j == j@pre &&
      Zlength(pts_l) == n &&
      PointArray::full(pts, n, point_swap(pts_l, i, j))
*/
{
  int tmp_x = pts[i].x;
  int tmp_y = pts[i].y;
  pts[i].x = pts[j].x;
  pts[i].y = pts[j].y;
  pts[j].x = tmp_x;
  pts[j].y = tmp_y;
}

static int partition_xy_points(struct Point *pts, int n, int low, int high)
/*@ With (pts_l : list Point)
    Require
      0 <= low && low <= high && high < n &&
      0 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      PointArray::full(pts, n, pts_l)
    Ensure
      pts == pts@pre &&
      n == n@pre &&
      low == low@pre &&
      high == high@pre &&
      low <= __return && __return <= high &&
      exists pts_out,
        Zlength(pts_out) == n &&
        points_in_bound(pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_same_outside_range(pts_l, pts_out, low, high) &&
        point_xy_partitioned_at(pts_out, low, high, __return) &&
        PointArray::full(pts, n, pts_out)
*/
{
  int pivot_x = pts[high].x;
  int pivot_y = pts[high].y;
  int i = low - 1;
  /*@ Inv Assert
      exists pts_cur,
        Zlength(pts_cur) == n &&
        pts == pts@pre &&
        n == n@pre &&
        low == low@pre &&
        high == high@pre &&
        0 <= n && n <= 50000 &&
        0 <= low && low <= high && high < n &&
        low - 1 <= i && i < j && j <= high &&
        pts_cur[high].x == pivot_x &&
        pts_cur[high].y == pivot_y &&
        points_in_bound(pts_cur) &&
        point_in_bound(point_mk(pivot_x, pivot_y)) &&
        point_xy_partition_scan_inv(pts_l, pts_cur,
                                    low, high,
                                    point_mk(pivot_x, pivot_y), i, j) &&
        PointArray::full(pts, n, pts_cur)
  */
  for (int j = low; j < high; j++) {
    int ax = pts[j].x;
    int ay = pts[j].y;
    int c = cmp_xy(ax, ay, pivot_x, pivot_y);
    if (c <= 0) {
      i++;
      if (i != j) {
        swap_points(pts, n, i, j);
      }
    }
  }
  if (i + 1 != high) {
    swap_points(pts, n, i + 1, high);
  }
  return i + 1;
}

static void quicksort_xy_points(struct Point *pts, int n, int left, int right)
/*@ With (pts_l : list Point)
    Require
      0 <= n && n <= 50000 &&
      0 <= left && -1 <= right && right < n &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      PointArray::full(pts, n, pts_l)
    Ensure
      exists pts_out,
        Zlength(pts_out) == n &&
        points_in_bound(pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_same_outside_range(pts_l, pts_out, left, right) &&
        point_xy_sorted_range(pts_out, left, right) &&
        PointArray::full(pts, n, pts_out)
*/
{
  if (left < right) {
    int p = partition_xy_points(pts, n, left, right);
    if (p > left)
      quicksort_xy_points(pts, n, left, p - 1);
    if (p < right)
      quicksort_xy_points(pts, n, p + 1, right);
  }
}

static int andrew_build_from_sorted(struct Point *pts, int n, struct Point *hull)
/*@ high_level_spec <= low_level_spec
    With (pts_l : list Point)
    Require
      2 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      points_not_all_same(pts_l) &&
      point_xy_sorted(pts_l) &&
      PointArray::full(pts, n, pts_l) *
      PointArray::undef_full(hull, 2 * n)
    Ensure
      exists pts_out hull_out,
        Zlength(pts_out) == n &&
        2 <= __return && __return <= 2 * n &&
        Zlength(hull_out) == __return &&
        points_in_bound(pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_xy_sorted(pts_out) &&
        is_convex_hull(pts_l, hull_out) &&
        PointArray::full(pts, n, pts_out) *
        PointArray::seg(hull, 0, __return, hull_out) *
        PointArray::undef_seg(hull, __return, 2 * n)
*/
;

static int andrew_build_from_sorted(struct Point *pts, int n, struct Point *hull)
/*@ low_level_spec
    With (pts_l : list Point) X
    Require
      2 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      points_not_all_same(pts_l) &&
      point_xy_sorted(pts_l) &&
      safeExec(equiv(empty_point_stack), andrew_monotone_chain_m(pts_l), X) &&
      PointArray::full(pts, n, pts_l) *
      PointArray::undef_full(hull, 2 * n)
    Ensure
      exists pts_out hull_out,
        Zlength(pts_out) == n &&
        2 <= __return && __return <= 2 * n &&
        Zlength(hull_out) == __return &&
        points_in_bound(pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_xy_sorted(pts_out) &&
        safeExec(equiv(hull_out), return(tt), X) &&
        PointArray::full(pts, n, pts_out) *
        PointArray::seg(hull, 0, __return, hull_out) *
        PointArray::undef_seg(hull, __return, 2 * n)
*/
{
  int k = 0;
  /*@ Inv Assert
      exists pts_sorted lower,
        0 <= i && i <= n &&
        0 <= k && k <= i &&
        (0 < i => 1 <= k) &&
        pts == pts@pre &&
        hull == hull@pre &&
        n == n@pre &&
        2 <= n && n <= 50000 &&
        Zlength(pts_l) == n &&
        Zlength(pts_sorted) == n &&
        points_in_bound(pts_sorted) &&
        point_permutation(pts_l, pts_sorted) &&
        point_xy_sorted(pts_sorted) &&
        andrew_lower_scan_inv(pts_sorted, lower, i, k) &&
        andrew_lower_remaining_cont(pts_sorted, lower, i, X) &&
        PointArray::full(pts, n, pts_sorted) *
        PointArray::seg(hull, 0, k, lower) *
        PointArray::undef_seg(hull, k, 2 * n)
  */
  for (int i = 0; i < n; i++) {
    /*@ Inv Assert
        exists pts_sorted lower,
          0 <= i && i < n &&
          0 <= k && k <= i &&
          (0 < i => 1 <= k) &&
          pts == pts@pre &&
          hull == hull@pre &&
          n == n@pre &&
          2 <= n && n <= 50000 &&
          Zlength(pts_l) == n &&
          Zlength(pts_sorted) == n &&
          points_in_bound(pts_sorted) &&
          point_permutation(pts_l, pts_sorted) &&
          point_xy_sorted(pts_sorted) &&
          point_in_bound(pts_sorted[i]) &&
          andrew_lower_scan_inv(pts_sorted, lower, i, k) &&
          andrew_lower_remaining_cont(pts_sorted, lower, i, X) &&
          PointArray::full(pts, n, pts_sorted) *
          PointArray::seg(hull, 0, k, lower) *
          PointArray::undef_seg(hull, k, 2 * n)
    */
    while (k >= 2) {
      if (cross_prod(hull[k - 2].x, hull[k - 2].y, hull[k - 1].x, hull[k - 1].y,
                     pts[i].x, pts[i].y) > 0) {
        break;
      }
      k--;
    }
    hull[k].x = pts[i].x;
    hull[k].y = pts[i].y;
    k++;
  }

  int lower_n = k;
  /*@ Inv Assert
      exists pts_sorted hull_cur,
        0 <= i + 1 && i + 1 <= n - 1 &&
        2 <= lower_n && lower_n <= k && k <= 2 * n &&
        pts == pts@pre &&
        hull == hull@pre &&
        n == n@pre &&
        2 <= n && n <= 50000 &&
        Zlength(pts_l) == n &&
        Zlength(pts_sorted) == n &&
        points_in_bound(pts_sorted) &&
        point_permutation(pts_l, pts_sorted) &&
        point_xy_sorted(pts_sorted) &&
        andrew_upper_scan_inv(pts_sorted, hull_cur, i + 1, k, lower_n) &&
        andrew_upper_remaining_cont(pts_sorted, hull_cur, i + 1, lower_n, X) &&
        PointArray::full(pts, n, pts_sorted) *
        PointArray::seg(hull, 0, k, hull_cur) *
        PointArray::undef_seg(hull, k, 2 * n)
  */
  for (int i = n - 2; i >= 0; i--) {
    /*@ Inv Assert
        exists pts_sorted hull_cur,
          0 <= i && i <= n - 2 &&
          2 <= lower_n && lower_n <= k && k < 2 * n &&
          pts == pts@pre &&
          hull == hull@pre &&
          n == n@pre &&
          2 <= n && n <= 50000 &&
          Zlength(pts_l) == n &&
          Zlength(pts_sorted) == n &&
          points_in_bound(pts_sorted) &&
          point_permutation(pts_l, pts_sorted) &&
          point_xy_sorted(pts_sorted) &&
          point_in_bound(pts_sorted[i]) &&
          andrew_upper_scan_inv(pts_sorted, hull_cur, i + 1, k, lower_n) &&
          andrew_upper_remaining_cont(pts_sorted, hull_cur, i + 1, lower_n, X) &&
          PointArray::full(pts, n, pts_sorted) *
          PointArray::seg(hull, 0, k, hull_cur) *
          PointArray::undef_seg(hull, k, 2 * n)
    */
    while (k > lower_n) {
      if (cross_prod(hull[k - 2].x, hull[k - 2].y, hull[k - 1].x, hull[k - 1].y,
                     pts[i].x, pts[i].y) > 0) {
        break;
      }
      k--;
    }
    hull[k].x = pts[i].x;
    hull[k].y = pts[i].y;
    k++;
  }

  k--;
  /*@ Assert
      exists pts_sorted hull_closed hull_original,
        pts == pts@pre &&
        hull == hull@pre &&
        n == n@pre &&
        2 <= n && n <= 50000 &&
        2 <= k && k <= 2 * n &&
        Zlength(pts_l) == n &&
        Zlength(pts_sorted) == n &&
        Zlength(hull_closed) == k + 1 &&
        Zlength(hull_original) == k &&
        points_in_bound(pts_sorted) &&
        point_permutation(pts_l, pts_sorted) &&
        point_xy_sorted(pts_sorted) &&
        hull_original == sublist(0, k, hull_closed) &&
        safeExec(equiv(rev(hull_original)), return(tt), X) &&
        store(&lower_n, lower_n) *
        PointArray::full(pts, n, pts_sorted) *
        PointArray::seg(hull, 0, k, hull_original) *
        PointArray::undef_seg(hull, k, 2 * n)
  */
  int left = 0;
  /*@ Inv Assert
      exists pts_sorted hull_original hull_cur hull_out,
        0 <= left && left <= k / 2 &&
        2 <= k && k <= 2 * n &&
        pts == pts@pre &&
        hull == hull@pre &&
        n == n@pre &&
        2 <= n && n <= 50000 &&
        Zlength(pts_l) == n &&
        Zlength(pts_sorted) == n &&
        Zlength(hull_original) == k &&
        Zlength(hull_cur) == k &&
        Zlength(hull_out) == k &&
        points_in_bound(pts_sorted) &&
        point_permutation(pts_l, pts_sorted) &&
        point_xy_sorted(pts_sorted) &&
        hull_out == rev(hull_original) &&
        point_prefix_reverse_state(hull_original, hull_cur, k, left) &&
        safeExec(equiv(hull_out), return(tt), X) &&
        store(&lower_n, lower_n) *
        PointArray::full(pts, n, pts_sorted) *
        PointArray::seg(hull, 0, k, hull_cur) *
        PointArray::undef_seg(hull, k, 2 * n)
  */
  while (left < k - 1 - left) {
    int right = k - 1 - left;
    int tmp_x = hull[left].x;
    int tmp_y = hull[left].y;
    hull[left].x = hull[right].x;
    hull[left].y = hull[right].y;
    hull[right].x = tmp_x;
    hull[right].y = tmp_y;
    left++;
  }

  /*@ Assert
      exists pts_sorted hull_out,
        pts == pts@pre &&
        hull == hull@pre &&
        n == n@pre &&
        2 <= k && k <= 2 * n &&
        Zlength(pts_l) == n &&
        Zlength(pts_sorted) == n &&
        Zlength(hull_out) == k &&
        points_in_bound(pts_sorted) &&
        point_permutation(pts_l, pts_sorted) &&
        point_xy_sorted(pts_sorted) &&
        safeExec(equiv(hull_out), return(tt), X) &&
        store(&lower_n, lower_n) *
        store(&left, left) *
        PointArray::full(pts, n, pts_sorted) *
        PointArray::seg(hull, 0, k, hull_out) *
        PointArray::undef_seg(hull, k, 2 * n)
  */
  return k;
}

int andrew_monotone_chain(struct Point *pts, int n, struct Point *hull)
/*@ With (pts_l : list Point)
    Require
      2 <= n && n <= 50000 &&
      Zlength(pts_l) == n &&
      points_in_bound(pts_l) &&
      points_not_all_same(pts_l) &&
      PointArray::full(pts, n, pts_l) *
      PointArray::undef_full(hull, 2 * n)
    Ensure
      exists pts_out hull_out,
        Zlength(pts_out) == n &&
        2 <= __return && __return <= 2 * n &&
        Zlength(hull_out) == __return &&
        points_in_bound(pts_out) &&
        point_permutation(pts_l, pts_out) &&
        point_xy_sorted(pts_out) &&
        is_convex_hull(pts_l, hull_out) &&
        PointArray::full(pts, n, pts_out) *
        PointArray::seg(hull, 0, __return, hull_out) *
        PointArray::undef_seg(hull, __return, 2 * n)
*/
{
  quicksort_xy_points(pts, n, 0, n - 1);
  /*@ Assert
      exists pts_sorted,
        pts == pts@pre &&
        hull == hull@pre &&
        n == n@pre &&
        2 <= n && n <= 50000 &&
        Zlength(pts_l) == n &&
        Zlength(pts_sorted) == n &&
        points_in_bound(pts_sorted) &&
        points_not_all_same(pts_sorted) &&
        point_permutation(pts_l, pts_sorted) &&
        point_xy_sorted(pts_sorted) &&
        PointArray::full(pts, n, pts_sorted) *
        PointArray::undef_full(hull, 2 * n)
  */
  int ret = andrew_build_from_sorted(pts, n, hull)
    /*@ where(high_level_spec) */;
  return ret;
}
