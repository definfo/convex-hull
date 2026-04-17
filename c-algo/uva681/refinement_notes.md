# qcp-mcp Workflow and Refinement Split

## 1) qcp-mcp stateful workflow

From the `user-qcp` MCP tool descriptors, the workflow is stateful and should be:

1. `load_target_file(file=ABS_PATH_TO_C_FILE)`
   - Starts a symbolic-execution session for one C file.
2. `symbolic(line=LAST_LINE)`
   - Run whole-file symbolic verification.
3. If failed, localize and debug with:
   - `check(line=...)` to inspect state at one line,
   - `step(steps=...)` to execute incrementally from current breakpoint.
4. `proof(function_name=..., witness_type=1..5, number=...)`
   - Export one witness goal for Coq-side proof scripting.
5. `close()`
   - End session before loading another file.

Important: `step`/`check`/`symbolic` are meaningful only after a successful `load_target_file`.

## 2) C split for Rocq refinement

The code is split so that Rocq-relevant logic has an explicit boundary:

- `main.c`
  - UVA input/output and testcase formatting only.
- `hull.c` + `hull.h`
  - Geometry helpers (`cross`, `dist2`), preprocess/sorting adapter, and proof boundary function.
- `build_hull_from_sorted_tail(...)`
  - Refinement target for Rocq `build_hull p l`:
    - `pivot` corresponds to `p`,
    - `sorted_tail` corresponds to sorted `l`,
    - iteration order mirrors Rocq's `build_hull_next` over `rev l`,
    - pop condition uses `cross(...) <= 0`,
    - post-step normalization rotates hull to min-(y,x).

`graham_scan(...)` remains an end-to-end UVA adapter that performs dedup + sorting and then adapts order before calling `build_hull_from_sorted_tail(...)`.

## 3) Suggested proof staging

1. Verify `build_hull_from_sorted_tail` first (no IO, no parsing).
2. Prove/relate loop invariant with Rocq:
   - stack content after each iteration corresponds to `run_tail [p] ...`.
3. Add adapter lemmas:
   - UVA polar-sort order transformed to Rocq-consumed order.
4. Keep `main.c` out of core refinement proof; treat as a trusted IO shell.
