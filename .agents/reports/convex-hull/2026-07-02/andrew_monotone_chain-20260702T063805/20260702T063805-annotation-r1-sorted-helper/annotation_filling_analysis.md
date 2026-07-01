## Annotation Filling Analysis

- status: blocked
- case: `convex-hull/andrew_monotone_chain.c`
- proof_type: refinement-proof
- scratch_c: `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- annotation_scratch_lib: `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- target_focus: move `safeExec` refinement from public unsorted `andrew_monotone_chain` to a sorted-input scan helper.

## Candidate Design

The candidate introduces a helper:

```c
static int andrew_monotone_chain_from_sorted(struct Point *pts, int n,
                                             struct Point *hull)
```

The helper owns the `high_level_spec <= low_level_spec` refinement boundary.
Its precondition includes `point_xy_sorted(pts_l)` and retains `points_not_all_same(pts_l)`.
Its low-level precondition uses:

```c
safeExec(equiv(empty_point_stack), andrew_monotone_chain_m(pts_l), X)
```

where `pts_l` is now the sorted helper input, not the public unsorted input.

The public `andrew_monotone_chain` keeps the original high-level convex-hull spec over `pts_l`, runs `quicksort_xy_points`, asserts a sorted `pts_sorted`, then calls:

```c
int ret = andrew_monotone_chain_from_sorted(pts, n, hull)
  /*@ where(high_level_spec) */;
```

## Hidden Properties Used

- sorted helper input: `point_xy_sorted(pts_l)`
- lower scan residual: `safeExec(equiv(lower), build_chain(sublist(i, n, pts_l)), X)`
- upper scan residual: `safeExec(equiv(hull_cur), build_upper_chain_cont(pts_l, sublist(0, lower_n, hull_cur)), X)`
- helper memory shape: `PointArray::full(pts, n, pts_l)` plus written hull prefix and unwritten hull suffix
- public post-sort bridge: `point_permutation(pts_l, pts_sorted)`, `point_xy_sorted(pts_sorted)`, and `points_not_all_same(pts_sorted)`

## Annotation Scratch Lib

- changes needed: none
- coqc_status: passed
- command:

```sh
coqc -R SeparationLogic/SeparationLogic SimpleC.SL \
  -R SeparationLogic/unifysl Logic \
  -R SeparationLogic/sets SetsClass \
  -R SeparationLogic/compcert_lib compcert.lib \
  -R SeparationLogic/auxlibs AUXLib \
  -R SeparationLogic/examples SimpleC.EE \
  -R SeparationLogic/StrategyLib SimpleC.StrategyLib \
  -R SeparationLogic/Common SimpleC.Common \
  -R SeparationLogic/fixedpoints FP \
  -R SeparationLogic/MonadLib MonadLib \
  -R SeparationLogic/listlib ListLib \
  -R SeparationLogic/MaxMinLib MaxMinLib \
  -R SeparationLogic/GraphLib GraphLib \
  -R SeparationLogic/ConvexHull ConvexHull \
  -R .tmp/convex-hull/ConvexHull SimpleC.EE.convex_hull \
  .tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v
```

- elapsed: 3.036 seconds

The existing `convex_hull_lib.v` already has the needed monad aliases and helper continuation:

- `empty_point_stack`
- `andrew_monotone_chain_m`
- `build_chain`
- `build_upper_chain_cont`

No additional `common_case_formal_lib` spec definition is proposed.

## qcp-mcp Status

- qcp_mcp_requirement_satisfied: no
- target_file: `/home/comonad/Develop/qcp/convex-hull/.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`
- reached_eof: no
- failing_stage: MCP wrapper startup, before C parsing and before any file/line symbolic state
- evidence:

```text
Error: typer is required. Install with 'pip install mcp[cli]'
```

The shell Python in this environment also lacks `typer`, `mcp`, and `pip`, so the subagent could not repair the MCP wrapper locally:

```text
python3 typer missing: ModuleNotFoundError("No module named 'typer'")
python3 mcp missing: ModuleNotFoundError("No module named 'mcp'")
/nix/store/.../python3: No module named pip
```

## Extra Sanity Check

Plain C syntax passed:

```sh
gcc -fsyntax-only -Iconvex-hull -I. .tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c
```

This is not a substitute for qcp-mcp and is recorded only as a syntax sanity check.

## Risks For Main

- Because qcp-mcp could not start, the candidate is not ready for formal main-state integration.
- The post-sort call assertion includes `points_not_all_same(pts_sorted)`; after qcp-mcp is restored, generated VCs may need an existing or new proof lemma that `points_not_all_same` is preserved by `point_permutation`.
- Public final correctness relies on the existing `is_convex_hull_base_permutation` style lemma to move the helper result from sorted `pts_out` back to the original `pts_l`.

## Outcome

The annotation candidate is semantically corrected and scratch-lib compile checked, but this annotation round is blocked until qcp-mcp can load and symbolically execute the scratch C to EOF.
