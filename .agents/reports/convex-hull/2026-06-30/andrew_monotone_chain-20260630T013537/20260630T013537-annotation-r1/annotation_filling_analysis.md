## Annotation Filling Analysis

- status: blocked
- checked_scope: `convex-hull/andrew_monotone_chain.c`
- scratch_c_path: `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- annotation_scratch_lib_path: `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- phase_input_version: `c_sha256=e7d370bd04b534e5c745368f7b413c9fe21529aea277288067a5d995eb188483`; `common_case_formal_lib_sha256=e8d7914088f143e2c8acad9c67318bffcc3bf7ecda89ae0d1890adff555d52d1`

### Spec-First Review

Existing Andrew definitions in `convex_hull_lib.v` were reviewed in the scratch copy. The relevant definitions are present:

- `andrew_lower_scan_inv`
- `andrew_upper_scan_inv`
- `andrew_lower_append_ready`
- `andrew_upper_append_ready`
- `andrew_hull_result`
- supporting chain/range/envelope predicates

The definitions are mathematical property predicates over sorted point lists, chain membership/ranges, strict index use, left turns, envelopes, capacity, and convex hull correctness. They are not a direct C loop/state-machine mirror. No source-level `annotation_scratch_lib` spec patch was identified in this round.

### Predicate-First Annotation Review

The existing C annotations already expose the intended hidden properties:

- sorted/permutation relation after `quicksort_xy_points`
- lower scan progress through `andrew_lower_scan_inv`
- upper scan progress through `andrew_upper_scan_inv`
- output buffer as `PointArray::seg(hull, 0, k, ...)` plus `PointArray::undef_seg(hull, k, 2 * n)`
- final `andrew_hull_result(pts_l, pts_sorted, hull_out)`

The annotations also use `PointArray` builtin predicates rather than duplicate memory predicates. No official C annotation patch was identified in this round.

### qcp-mcp Summary

The fresh scratch initially failed to load because qcp-mcp did not receive an include path for the `.tmp` location:

- failed load: line 1, `fatal error: No such file convex_hull_def.h in search path`

To exercise qcp-mcp on the scratch only, the scratch include was changed from:

```c
#include "convex_hull_def.h"
```

to:

```c
#include "../../convex-hull/convex_hull_def.h"
```

This include adjustment is not a ready-for-main patch and should not be applied to the official C file.

After that scratch-only include adjustment:

- qcp-mcp load: success
- qcp-mcp symbolic to line 330: success
- loaded strategies: `point_array`
- file-end result: success

Manual witness counts reported by qcp-mcp:

| function | auto_solved | manual |
| --- | ---: | ---: |
| `cmp_xy` | 8 | 5 |
| `cross_prod` | 1 | 8 |
| `swap_points` | 8 | 1 |
| `partition_xy_points` | 22 | 6 |
| `quicksort_xy_points` | 11 | 4 |
| `andrew_monotone_chain` | 63 | 13 |

These are downstream proof obligations, not qcp annotation blockers.

### Blocking Evidence

The required annotation-checking Rocq compile gate failed for the scratch lib:

```text
File "./.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v", line 16, characters 0-104:
Error:
Compiled library ConvexHull.Reversal (in file .../SeparationLogic/ConvexHull/Reversal.vo) makes inconsistent assumptions over library ConvexHull.Record_Geo_Point
```

Additional dependency consistency check evidence:

```text
Fatal Error: User error: Inconsistent assumptions over module ConvexHull.Graham_Scan_M .
```

Timestamp evidence shows stale compiled dependencies relative to newer compiled ConvexHull artifacts:

- `SeparationLogic/ConvexHull/Reversal.vo`: 2026-06-09
- `SeparationLogic/ConvexHull/Record_Geo_Point.vo`: 2026-06-29
- `SeparationLogic/ConvexHull/Graham_Scan_M.vo`: 2026-06-29

The round write set does not allow rebuilding official `.vo` artifacts under `SeparationLogic/ConvexHull`, so the annotation quality gate cannot be completed by this subagent.

### Ready-For-Main Patch

- C annotation patch: empty
- `annotation_scratch_lib` spec patch: empty
- scratch-only include workaround: not for main

### Cleanup

Deleted:

- `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- `.tmp/convex-hull/ConvexHull/.andrew_monotone_chain__annotation_subagent_tmp_lib.aux`
- `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.glob`
