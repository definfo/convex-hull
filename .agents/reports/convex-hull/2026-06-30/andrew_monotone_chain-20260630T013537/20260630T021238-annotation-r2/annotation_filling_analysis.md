## Annotation Filling Analysis

- status: completed
- checked_scope: `convex-hull/andrew_monotone_chain.c`
- scratch_c_path: `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- annotation_scratch_lib_path: `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- phase_input_version: `c_sha256=e7d370bd04b534e5c745368f7b413c9fe21529aea277288067a5d995eb188483`; `common_case_formal_lib_sha256=e8d7914088f143e2c8acad9c67318bffcc3bf7ecda89ae0d1890adff555d52d1`

### Fresh Scratch

The official hashes matched the r2 delegation ticket before scratch creation. Fresh scratch files were created from:

- `convex-hull/andrew_monotone_chain.c`
- `convex-hull/ConvexHull/convex_hull_lib.v`

The scratch C required the same loader-only include adjustment used in r1 because qcp-mcp has no separate include-path argument for this invocation:

```diff
-#include "convex_hull_def.h"
+#include "../../convex-hull/convex_hull_def.h"
```

This is not a candidate C annotation patch and must not be applied to the official source.

### Spec-First Review

The relevant Andrew predicates already exist in the scratch copy of `convex_hull_lib.v`:

- `andrew_hull_result`
- `andrew_lower_scan_inv`
- `andrew_upper_scan_inv`
- `andrew_lower_append_ready`
- `andrew_upper_append_ready`
- supporting point-chain, sortedness, range-use, envelope, capacity, and convex-hull predicates

These definitions describe mathematical geometry properties over sorted point lists and hull chains. They are not a new recursive/state-machine mirror of the C loops. No `annotation_scratch_lib` source patch was needed.

### Predicate-First Annotation Review

The existing C annotations expose the intended hidden properties:

- `quicksort_xy_points` exposes sortedness, permutation, and outside-range preservation.
- The lower loop uses `andrew_lower_scan_inv` together with `PointArray::seg(hull, 0, k, lower)` and `PointArray::undef_seg(hull, k, 2 * n)`.
- The upper loop uses `andrew_upper_scan_inv` with the fixed lower prefix and upper suffix geometry.
- The final assertion connects `pts_l`, `pts_sorted`, and `hull_out` through `andrew_hull_result`.
- Memory predicates use `PointArray` builtin predicates, not duplicate custom array predicates.

No candidate C annotation patch was needed.

### qcp-mcp Summary

- load target: passed on scratch C
- symbolic target: line 330, file end
- symbolic result: success
- loaded strategies: `point_array`
- qcp_mcp_requirement_satisfied: yes

Manual witness counts reported by qcp-mcp remain downstream proof obligations, not annotation blockers:

| function | auto_solved | manual |
| --- | ---: | ---: |
| `cmp_xy` | 8 | 5 |
| `cross_prod` | 1 | 8 |
| `swap_points` | 8 | 1 |
| `partition_xy_points` | 22 | 6 |
| `quicksort_xy_points` | 11 | 4 |
| `andrew_monotone_chain` | 63 | 13 |

### Scratch Lib Compile Gate

`coqc` on the fresh `annotation_scratch_lib` passed after main rebuilt the official ConvexHull dependencies. The scratch lib was byte-identical to the official `convex_hull_lib.v`.

### Ready-For-Main Patch

- C annotation patch: empty
- `annotation_scratch_lib` spec patch: empty
- scratch-only include workaround: not for main

### Cleanup

Cleanup completed. Deleted:

- `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.vo`
- `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.glob`
- `.tmp/convex-hull/ConvexHull/.andrew_monotone_chain__annotation_subagent_tmp_lib.aux`

Post-cleanup check found no remaining `andrew_monotone_chain__annotation_subagent_tmp` files under `.tmp/convex-hull`.
