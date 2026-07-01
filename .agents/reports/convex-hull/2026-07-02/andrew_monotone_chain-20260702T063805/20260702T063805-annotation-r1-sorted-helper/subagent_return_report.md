## Subagent Return Report

- round_outcome: blocked
- summary: Proposed the corrected Graham-style sorted-input helper boundary for Andrew refinement. The C scratch and annotation_scratch_lib were created from the current formal snapshots. The scratch C candidate moves `safeExec(equiv(empty_point_stack), andrew_monotone_chain_m(...), X)` to `andrew_monotone_chain_from_sorted`, where the input list is sorted. The public `andrew_monotone_chain` now sorts, asserts the sorted state, and calls the helper with `where(high_level_spec)`.
- phase_started_at: 2026-07-02T06:38:05+08:00
- phase_finished_at: 2026-07-02T06:44:21+08:00
- phase_elapsed_seconds: 376
- timing_summary: known command time 4.288 seconds; total wall-clock includes required doc/context reading, analysis, scratch edit, and report writing
- command_timings:
  - qcp-mcp load attempt 1: 0.683 seconds, failed before C parsing
  - annotation_scratch_lib coqc gate: 3.036 seconds, passed
  - qcp-mcp load attempt 2: 0.569 seconds, failed before C parsing
  - gcc syntax sanity check: sub-second, passed
- human_activity_timings: manual analysis/edit/reporting not precisely split; see `timing_log.md`
- slowest_steps: scratch lib `coqc`, 3.036 seconds
- major_time_sinks: semantic boundary review and MCP environment blocker
- ready_for_main: no
- annotation_checking_status: blocked
- qcp_mcp_requirement_satisfied: no
- annotation_scratch_lib_coqc_status: passed
- ready_for_main_symexec: no
- annotation_checking_report: `annotation_checking_report.md`
- vc_informal_proof_report: n/a
- ready_for_main_common_case_formal_lib_spec_update: empty
- ready_for_main_proof_manual: n/a
- ready_for_main_common_case_formal_lib_append: n/a
- migrated_helper_imports: n/a
- witness_group_plan: n/a
- grouping_source: n/a
- proof_pattern_summary: n/a
- group_helper_policy: n/a
- worker_reports: n/a
- checkpoint_reuse_summary: n/a
- round_checkpoint: n/a
- partial_proof_packet: n/a
- reuse_index: n/a
- protected_prefix_respected: n/a
- blocking_reason: qcp-mcp cannot start in this environment; `load_target_file` returns `Error: typer is required. Install with 'pip install mcp[cli]'` before reading the scratch C. The shell Python also lacks `typer`, `mcp`, and `pip`.
- recommended_next_phase: annotation -> annotation after fixing qcp-mcp Python dependency, then rerun qcp-mcp on the same candidate patch from a fresh scratch
- cleanup_status: completed; owned scratch C, annotation_scratch_lib, and scratch-lib `.vo` / `.vos` / `.vok` / `.glob` / `.aux` artifacts were removed after reports were persisted

## qcp-mcp Result

- file: `/home/comonad/Develop/qcp/convex-hull/.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- line: n/a; startup failed before C parsing
- reached_eof: no
- result:

```text
Error: typer is required. Install with 'pip install mcp[cli]'
```

## annotation_scratch_lib coqc Status

- file: `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- status: passed
- elapsed: 3.036 seconds
- common_case_formal_lib_changes_needed: no

## Candidate C Patch

Apply this hunk to `convex-hull/andrew_monotone_chain.c` after qcp-mcp is restored and the scratch candidate is rerun to EOF.

```diff
--- convex-hull/andrew_monotone_chain.c
+++ convex-hull/andrew_monotone_chain.c
@@ -184,7 +184,8 @@
   }
 }
 
-int andrew_monotone_chain(struct Point *pts, int n, struct Point *hull)
+static int andrew_monotone_chain_from_sorted(struct Point *pts, int n,
+                                             struct Point *hull)
 /*@ high_level_spec <= low_level_spec
     With (pts_l : list Point)
     Require
@@ -192,25 +193,29 @@
       Zlength(pts_l) == n &&
       points_in_bound(pts_l) &&
       points_not_all_same(pts_l) &&
+      point_xy_sorted(pts_l) &&
       PointArray::full(pts, n, pts_l) *
       PointArray::undef_full(hull, 2 * n)
     Ensure
-      exists pts_out hull_out,
-        Zlength(pts_out) == n &&
+      exists hull_out,
+        pts == pts@pre &&
+        hull == hull@pre &&
+        n == n@pre &&
         2 <= __return && __return <= 2 * n &&
         Zlength(hull_out) == __return &&
-        points_in_bound(pts_out) &&
-        point_permutation(pts_l, pts_out) &&
-        point_xy_sorted(pts_out) &&
-        andrew_complete_hull_shape(pts_out, hull_out) &&
+        points_in_bound(pts_l) &&
+        points_not_all_same(pts_l) &&
+        point_xy_sorted(pts_l) &&
+        andrew_complete_hull_shape(pts_l, hull_out) &&
         is_convex_hull(pts_l, hull_out) &&
-        PointArray::full(pts, n, pts_out) *
+        PointArray::full(pts, n, pts_l) *
         PointArray::seg(hull, 0, __return, hull_out) *
         PointArray::undef_seg(hull, __return, 2 * n)
 */
 ;
 
-int andrew_monotone_chain(struct Point *pts, int n, struct Point *hull)
+static int andrew_monotone_chain_from_sorted(struct Point *pts, int n,
+                                             struct Point *hull)
 /*@ low_level_spec
     With (pts_l : list Point) X
     Require
@@ -218,28 +223,30 @@
       Zlength(pts_l) == n &&
       points_in_bound(pts_l) &&
       points_not_all_same(pts_l) &&
+      point_xy_sorted(pts_l) &&
       safeExec(equiv(empty_point_stack), andrew_monotone_chain_m(pts_l), X) &&
       PointArray::full(pts, n, pts_l) *
       PointArray::undef_full(hull, 2 * n)
     Ensure
-      exists pts_out hull_out,
-        Zlength(pts_out) == n &&
+      exists hull_out,
+        pts == pts@pre &&
+        hull == hull@pre &&
+        n == n@pre &&
         2 <= __return && __return <= 2 * n &&
         Zlength(hull_out) == __return &&
-        points_in_bound(pts_out) &&
-        point_permutation(pts_l, pts_out) &&
-        point_xy_sorted(pts_out) &&
-        andrew_complete_hull_shape(pts_out, hull_out) &&
+        points_in_bound(pts_l) &&
+        points_not_all_same(pts_l) &&
+        point_xy_sorted(pts_l) &&
+        andrew_complete_hull_shape(pts_l, hull_out) &&
         safeExec(equiv(hull_out), return(tt), X) &&
-        PointArray::full(pts, n, pts_out) *
+        PointArray::full(pts, n, pts_l) *
         PointArray::seg(hull, 0, __return, hull_out) *
         PointArray::undef_seg(hull, __return, 2 * n)
 */
 {
-  quicksort_xy_points(pts, n, 0, n - 1);
   int k = 0;
   /*@ Inv Assert
-      exists pts_sorted lower,
+      exists lower,
         0 <= i && i <= n &&
         0 <= k && k <= i &&
         pts == pts@pre &&
@@ -247,19 +254,18 @@
         n == n@pre &&
         2 <= n && n <= 50000 &&
         Zlength(pts_l) == n &&
-        Zlength(pts_sorted) == n &&
-        points_in_bound(pts_sorted) &&
-        point_permutation(pts_l, pts_sorted) &&
-        point_xy_sorted(pts_sorted) &&
-        andrew_lower_scan_inv(pts_sorted, lower, i, k) &&
-        safeExec(equiv(lower), build_chain(sublist(i, n, pts_sorted)), X) &&
-        PointArray::full(pts, n, pts_sorted) *
+        points_in_bound(pts_l) &&
+        points_not_all_same(pts_l) &&
+        point_xy_sorted(pts_l) &&
+        andrew_lower_scan_inv(pts_l, lower, i, k) &&
+        safeExec(equiv(lower), build_chain(sublist(i, n, pts_l)), X) &&
+        PointArray::full(pts, n, pts_l) *
         PointArray::seg(hull, 0, k, lower) *
         PointArray::undef_seg(hull, k, 2 * n)
   */
   for (int i = 0; i < n; i++) {
     /*@ Inv Assert
-        exists pts_sorted lower,
+        exists lower,
           0 <= i && i < n &&
           0 <= k && k <= i &&
           pts == pts@pre &&
@@ -267,14 +273,13 @@
           n == n@pre &&
           2 <= n && n <= 50000 &&
           Zlength(pts_l) == n &&
-          Zlength(pts_sorted) == n &&
-          points_in_bound(pts_sorted) &&
-          point_permutation(pts_l, pts_sorted) &&
-          point_xy_sorted(pts_sorted) &&
-          point_in_bound(pts_sorted[i]) &&
-          andrew_lower_scan_inv(pts_sorted, lower, i, k) &&
-          safeExec(equiv(lower), build_chain(sublist(i, n, pts_sorted)), X) &&
-          PointArray::full(pts, n, pts_sorted) *
+          points_in_bound(pts_l) &&
+          points_not_all_same(pts_l) &&
+          point_xy_sorted(pts_l) &&
+          point_in_bound(pts_l[i]) &&
+          andrew_lower_scan_inv(pts_l, lower, i, k) &&
+          safeExec(equiv(lower), build_chain(sublist(i, n, pts_l)), X) &&
+          PointArray::full(pts, n, pts_l) *
           PointArray::seg(hull, 0, k, lower) *
           PointArray::undef_seg(hull, k, 2 * n)
     */
@@ -292,7 +297,7 @@
 
   int lower_n = k;
   /*@ Inv Assert
-      exists pts_sorted hull_cur,
+      exists hull_cur,
         0 <= i + 1 && i + 1 <= n - 1 &&
         2 <= lower_n && lower_n <= k && k <= 2 * n &&
         pts == pts@pre &&
@@ -300,19 +305,18 @@
         n == n@pre &&
         2 <= n && n <= 50000 &&
         Zlength(pts_l) == n &&
-        Zlength(pts_sorted) == n &&
-        points_in_bound(pts_sorted) &&
-        point_permutation(pts_l, pts_sorted) &&
-        point_xy_sorted(pts_sorted) &&
-        andrew_upper_scan_inv(pts_sorted, hull_cur, i + 1, k, lower_n) &&
-        safeExec(equiv(hull_cur), build_upper_chain_cont(pts_sorted, sublist(0, lower_n, hull_cur)), X) &&
-        PointArray::full(pts, n, pts_sorted) *
+        points_in_bound(pts_l) &&
+        points_not_all_same(pts_l) &&
+        point_xy_sorted(pts_l) &&
+        andrew_upper_scan_inv(pts_l, hull_cur, i + 1, k, lower_n) &&
+        safeExec(equiv(hull_cur), build_upper_chain_cont(pts_l, sublist(0, lower_n, hull_cur)), X) &&
+        PointArray::full(pts, n, pts_l) *
         PointArray::seg(hull, 0, k, hull_cur) *
         PointArray::undef_seg(hull, k, 2 * n)
   */
   for (int i = n - 2; i >= 1; i--) {
     /*@ Inv Assert
-        exists pts_sorted hull_cur,
+        exists hull_cur,
           1 <= i && i <= n - 2 &&
           2 <= lower_n && lower_n <= k && k < 2 * n &&
           pts == pts@pre &&
@@ -320,14 +324,13 @@
           n == n@pre &&
           2 <= n && n <= 50000 &&
           Zlength(pts_l) == n &&
-          Zlength(pts_sorted) == n &&
-          points_in_bound(pts_sorted) &&
-          point_permutation(pts_l, pts_sorted) &&
-          point_xy_sorted(pts_sorted) &&
-          point_in_bound(pts_sorted[i]) &&
-          andrew_upper_scan_inv(pts_sorted, hull_cur, i + 1, k, lower_n) &&
-          safeExec(equiv(hull_cur), build_upper_chain_cont(pts_sorted, sublist(0, lower_n, hull_cur)), X) &&
-          PointArray::full(pts, n, pts_sorted) *
+          points_in_bound(pts_l) &&
+          points_not_all_same(pts_l) &&
+          point_xy_sorted(pts_l) &&
+          point_in_bound(pts_l[i]) &&
+          andrew_upper_scan_inv(pts_l, hull_cur, i + 1, k, lower_n) &&
+          safeExec(equiv(hull_cur), build_upper_chain_cont(pts_l, sublist(0, lower_n, hull_cur)), X) &&
+          PointArray::full(pts, n, pts_l) *
           PointArray::seg(hull, 0, k, hull_cur) *
           PointArray::undef_seg(hull, k, 2 * n)
     */
@@ -344,23 +347,67 @@
   }
 
   /*@ Assert
-      exists pts_sorted hull_out,
+      exists hull_out,
         pts == pts@pre &&
         hull == hull@pre &&
         n == n@pre &&
         2 <= k && k <= 2 * n &&
         Zlength(pts_l) == n &&
-        Zlength(pts_sorted) == n &&
         Zlength(hull_out) == k &&
-        points_in_bound(pts_sorted) &&
-        point_permutation(pts_l, pts_sorted) &&
-        point_xy_sorted(pts_sorted) &&
-        andrew_complete_hull_shape(pts_sorted, hull_out) &&
+        points_in_bound(pts_l) &&
+        points_not_all_same(pts_l) &&
+        point_xy_sorted(pts_l) &&
+        andrew_complete_hull_shape(pts_l, hull_out) &&
         safeExec(equiv(hull_out), return(tt), X) &&
         store(&lower_n, lower_n) *
-        PointArray::full(pts, n, pts_sorted) *
+        PointArray::full(pts, n, pts_l) *
         PointArray::seg(hull, 0, k, hull_out) *
         PointArray::undef_seg(hull, k, 2 * n)
   */
   return k;
 }
+
+int andrew_monotone_chain(struct Point *pts, int n, struct Point *hull)
+/*@ With (pts_l : list Point)
+    Require
+      2 <= n && n <= 50000 &&
+      Zlength(pts_l) == n &&
+      points_in_bound(pts_l) &&
+      points_not_all_same(pts_l) &&
+      PointArray::full(pts, n, pts_l) *
+      PointArray::undef_full(hull, 2 * n)
+    Ensure
+      exists pts_out hull_out,
+        Zlength(pts_out) == n &&
+        2 <= __return && __return <= 2 * n &&
+        Zlength(hull_out) == __return &&
+        points_in_bound(pts_out) &&
+        point_permutation(pts_l, pts_out) &&
+        point_xy_sorted(pts_out) &&
+        andrew_complete_hull_shape(pts_out, hull_out) &&
+        is_convex_hull(pts_l, hull_out) &&
+        PointArray::full(pts, n, pts_out) *
+        PointArray::seg(hull, 0, __return, hull_out) *
+        PointArray::undef_seg(hull, __return, 2 * n)
+*/
+{
+  quicksort_xy_points(pts, n, 0, n - 1);
+  /*@ Assert
+      exists pts_sorted,
+        pts == pts@pre &&
+        hull == hull@pre &&
+        n == n@pre &&
+        2 <= n && n <= 50000 &&
+        Zlength(pts_l) == n &&
+        Zlength(pts_sorted) == n &&
+        points_in_bound(pts_sorted) &&
+        points_not_all_same(pts_sorted) &&
+        point_permutation(pts_l, pts_sorted) &&
+        point_xy_sorted(pts_sorted) &&
+        PointArray::full(pts, n, pts_sorted) *
+        PointArray::undef_full(hull, 2 * n)
+  */
+  int ret = andrew_monotone_chain_from_sorted(pts, n, hull)
+    /*@ where(high_level_spec) */;
+  return ret;
+}
```

## Candidate Lib Patch

```diff
empty
```
