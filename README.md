# Convex Hull — QCP Verification

End-to-end separation-logic verification of three convex-hull
implementations / variants, built on the **QCP** symbolic-execution /
VC-generation toolchain and proved in Rocq.

All three are verified as plain C functions operating in place on an
array of `struct Point { int x; int y; }`. Each discharges a postcondition
of the same shape:

> the output `hull` array holds exactly the convex hull of the input point
> set (`is_convex_hull pts_l hull_out`), the input array is returned as a
> permutation of itself, every point stays within the bounded coordinate
> range, and the returned integer is the hull size.

| Case | C source | Abstract monad model | What is proved |
|------|----------|----------------------|----------------|
| Andrew's monotone chain | [`andrew_monotone_chain.c`](andrew_monotone_chain.c) | `ConvexHull.Andrew_Monotone_Chain_M` | full functional correctness of `andrew_monotone_chain` |
| Graham's scan           | [`graham_scan.c`](graham_scan.c)             | `ConvexHull.Graham_Scan_M`           | full functional correctness of `graham_scan` |
| Graham's scan + dedup   | [`graham_scan_dedup.c`](graham_scan_dedup.c) | `ConvexHull.Graham_Scan_M`           | full functional correctness of `graham_scan_dedup`, a dedup-first variant |

## Status

All three cases are at the **done** state of the verification workflow.

* Symbolic execution runs to the end of file and regenerates the goal /
  proof-auto / goal-check files.
* Every manual verification condition (VC) is closed with `Qed` — there are
  **no `Admitted` and no extra `Axiom`s** anywhere in the delivered Coq
  sources (the only `Axiom` tokens are `From AUXLib Require Import ... Axioms`,
  i.e. the standard library module name).
* The `*_goal_check.v` modules compile, which is the final gate confirming
  that every generated VC has a matching witness proof.

Manual witness proof counts (top-level `Lemma proof_of_*_wit_*` statements,
excluding generated `split_goal_*` sub-goals):

| Case | Witness lemmas | Functions covered |
|------|---------------:|-------------------|
| Andrew | 135 | `cmp_xy`, `cross_prod`, `swap_points`, `partition_xy_points`, `quicksort_xy_points`, `andrew_build_from_sorted`, `andrew_monotone_chain` |
| Graham |  65 | `leftdown`, `cross_prod`, `dot_prod`, `cmp_polar`, `swap_points`, `partition_polar_points`, `quicksort_polar_points`, `build_hull_from_sorted_tail`, `graham_scan` |
| Graham + dedup | 209 | `leftdown_dedup`, `cross_prod`, `dot_prod`, `cmp_polar`, `swap_points`, `partition_polar_points`, `quicksort_polar_points`, `dedup_points_and_find_leftmost`, `build_hull_from_sorted_tail_dedup`, `graham_scan_dedup` |

The shared math / spec library is
[`ConvexHull/convex_hull_lib.v`](ConvexHull/convex_hull_lib.v) (~5.7k lines,
225 helper lemmas, 85 definitions) on top of the pre-existing
[`SeparationLogic/ConvexHull/`](SeparationLogic/ConvexHull) theory
(geo predicates, point order, hull equivalence, abstract monad models —
~10.8k lines total).

## Repository layout

```
convex-hull/
├── andrew_monotone_chain.c        # verified C (Andrew's monotone chain)
├── graham_scan.c                  # verified C (Graham's scan)
├── graham_scan_dedup.c            # verified C (Graham's scan, dedup-first variant)
├── convex_hull_def.h              # shared Point record + Extern Coq decls
├── safeexec_def.h                 # safeExec / monad Extern Coq decls
├── point_array.strategies         # PointArray separation-logic strategies
├── safeexec.strategies            # safeExec / monad strategies
└── ConvexHull/                    # generated + manual Coq artifacts
    ├── convex_hull_lib.v              # shared spec + helper library (manual)
    ├── point_array_strategy_*.v       # strategy goal/proof (generated+proof)
    ├── safeexec_strategy_*.v          # strategy goal/proof (generated+proof)
    ├── andrew_monotone_chain_goal.v           # generated VC goals
    ├── andrew_monotone_chain_proof_auto.v     # generated auto-discharged VC
    ├── andrew_monotone_chain_proof_manual.v   # manual witness proofs
    ├── andrew_monotone_chain_goal_check.v     # final VC-correctness gate
    ├── graham_scan_goal.v
    ├── graham_scan_proof_auto.v
    ├── graham_scan_proof_manual.v
    ├── graham_scan_goal_check.v
    ├── graham_scan_dedup_goal.v
    ├── graham_scan_dedup_proof_auto.v
    ├── graham_scan_dedup_proof_manual.v
    └── graham_scan_dedup_goal_check.v
```

File roles (per the project contract):

* `*_goal.v`, `*_proof_auto.v`, `*_goal_check.v` — **generated** by `symexec`
  from the annotated C source; never edited by hand.
* `*_proof_manual.v` — the manual witness theorem proofs; one `Lemma
  proof_of_<fn>_<kind>_wit_<n>` per generated VC, all closed with `Qed`.
* `convex_hull_lib.v` — the case-local formal library: point geometry
  predicates, ordering, sorting/partition invariants, hull equivalence, and
  the abstract monad programs (`andrew_monotone_chain_m`, `build_chain`,
  `build_hull`, ...).

## The specifications

### Andrew's monotone chain — `andrew_monotone_chain`

```
Require  2 <= n <= 50000 ∧ points_in_bound(pts_l) ∧ points_not_all_same(pts_l)
         PointArray::full(pts, n, pts_l) * PointArray::undef_full(hull, 2*n)
Ensure   ∃ pts_out hull_out,
           point_permutation(pts_l, pts_out) ∧ point_xy_sorted(pts_out) ∧
           is_convex_hull(pts_l, hull_out) ∧ 2 <= |hull_out| <= 2*n ∧
           PointArray::full(pts, n, pts_out) *
           PointArray::seg(hull, 0, ret, hull_out) *
           PointArray::undef_seg(hull, ret, 2*n)
```

Pipeline: `quicksort_xy_points` (x-then-y, via `partition_xy_points`) →
`andrew_build_from_sorted` builds the lower and upper chains with a
`cross_prod`-based pop-while-non-ccw stack discipline.

Key proof ideas:

* **Convexity** — under x-y sorting, consecutive (counter-)clockwise
  relations force a partial turn order, so any three sorted points keep a
  consistent orientation; this is what makes the pop/push stack maintain a
  valid chain.
* **Maximality** — the loop invariant on each chain is *semi-plane inclusion*
  (without the closing edge). Because Andrew's lower and upper chains share
  the same first and last point, the middle edge cancels and the two
  semi-planes compose into a full hull.

### Graham's scan — `graham_scan`

```
Require  2 <= n <= 50000 ∧ points_in_bound(pts_l)
         PointArray::full(pts, n, pts_l) * PointArray::undef_full(hull, n)
Ensure   ∃ pts_out hull_out,
           point_permutation(pts_l, pts_out) ∧
           is_convex_hull(pts_l, hull_out) ∧ 1 <= |hull_out| <= n ∧
           PointArray::full(pts, n, pts_out) *
           PointArray::seg(hull, 0, ret, hull_out) *
           PointArray::undef_seg(hull, ret, n)
```

Pipeline: pick the leftmost (down-most) pivot → `quicksort_polar_points`
(polar angle around the pivot, via `partition_polar_points` and
`cmp_polar` / `cross_prod` / `dot_prod`) → `build_hull_from_sorted_tail`
walks the sorted tail, popping while the next point would make a non-left
turn (`graham_scan_inc`).

Key proof ideas:

* **Convexity** — `cmp_polar` partitions points into polar wedges around the
  pivot; within a wedge, ordering is by `cross_prod` / `dot_prod`, giving the
  monotone turn order that the stack discipline preserves.
* **Maximality** — the hull-construction loop invariant is *semi-plane
  inclusion with the edge from the hull's top back to the pivot*, so the
  closing edge to the pivot completes the hull exactly.

### Graham's scan with dedup — `graham_scan_dedup`

```
Require  2 <= n <= 50000 ∧ points_in_bound(pts_l) ∧ points_not_all_same(pts_l)
         PointArray::full(pts, n, pts_l) * PointArray::undef_full(hull, n)
Ensure   ∃ pts_out hull_out,
           point_dedup_result(pts_l, pts_out, unique_n, pivot) ∧
           is_convex_hull(pts_l, hull_out) ∧ 0 <= |hull_out| <= n ∧
           PointArray::full(pts, n, pts_out) *
           PointArray::seg(hull, 0, ret, hull_out) *
           PointArray::undef_seg(hull, ret, n)
```

This is a **dedup-first** variant of Graham's scan. Before sorting, the input
array is compacted in place by `dedup_points_and_find_leftmost`, which folds
the leftmost-pivot search and duplicate removal into one pass: each point is
checked against the already-kept unique prefix (`point_no_dup_prefix`,
`point_prefix_has_same`); if it is a duplicate it is skipped, otherwise it is
swapped to the end of the unique prefix. The function returns `unique_n` and
writes the pivot index out, establishing `point_dedup_scan_inv` /
`point_dedup_result`.

After dedup the pipeline is Graham's scan on the unique prefix: swap pivot to
front → `quicksort_polar_points` → `build_hull_from_sorted_tail_dedup` (the
dedup-aware hull builder, which carries the same `build_hull` monad
refinement as the plain case but threads the full-array length `n_full`
through the `undef_seg` framing so the unused tail stays framed out).

Key proof ideas:

* **Dedup invariant** — `point_dedup_scan_inv` relates the live array to the
  *original* input list `pts_l` while the unique prefix grows; the inner
  `point_dedup_inner_scan_inv` tracks the linear duplicate scan. Together they
  prove that the compacted prefix is exactly the duplicate-free subsequence of
  `pts_l`, and that `points_not_all_same(pts_l)` forces `unique_n >= 2` so the
  downstream scan still has a real hull to build.
* **Convexity / maximality** — inherited from the plain Graham model
  (`point_polar_sorted`, `leftmost`, `graham_scan_inc`); the dedup case only
  adds the framing / size bookkeeping (`point_polar_cmp_safe_pair`,
  `point_polar_cmp_safe_range`) needed to sort a prefix of length `unique_n`
  inside an array of length `n`.
* **Weaker return bound** — because duplicates are removed before hull
  construction, the hull size is bounded only by `0 <= ret <= n` (the plain
  case guarantees `1 <= |hull_out| <= n`; the dedup precondition
  `points_not_all_same` is what still rules out the degenerate `ret = 0`).

## How to build

The driver is the top-level [`Makefile`](Makefile). From the repo root,
inside the Nix flake shell (`direnv allow`):

```sh
# Regenerate Coq VC files from the annotated C (symexec) and compile everything.
make build          # all three cases (graham_scan + andrew + dedup), full .vo
make quick          # .vos (quick, no .vo)
make vok-check      # .vok (full correctness gate)

# Per-case QCP workflows (symexec + coqc for one case at a time):
make andrew-build   # Andrew's monotone chain only
make dedup-build    # Graham's scan + dedup only
# (the plain Graham case is the default workflow; `make symexec` regenerates
#  its generated files, and `make build` compiles it together with the others.)

# Just regenerate the generated VC files without compiling:
make symexec andrew-symexec dedup-symexec
```

`make build` regenerates `_CoqProject` / `CoqMakefile` from the Makefile so
all three cases' `.v` files are tracked, then runs symexec for each case and
compiles every `.vo` (the `*_goal_check.v` module per case is the final
VC-correctness gate). Each per-case `*-build` target does the same for one
workflow: `andrew-build`, `dedup-build`, and the plain Graham workflow that
`build` includes by default.


`symexec` is invoked with the project's standard flags, notably
`-IQCP_examples/QCP_demos_LLM/` for the shared C headers and
`-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM` for the strategy /
Coq dependency mapping (the `-I` and `-slp` flags are not interchangeable).

The Coq side is built through the auto-generated `CoqMakefile` from
[`_CoqProject`](_CoqProject), which wires up the
`SeparationLogic/...` library roots and the case-local
`convex-hull/ConvexHull` → `SimpleC.EE.convex_hull` logical path.

## Verification workflow

This repository follows the orchestrator + phase-subagent workflow described
in [`AGENTS.md`](AGENTS.md):

1. **intake** — record case info, formal-lib frozen prefix, file boundaries.
2. **annotation** — annotate the C (contracts, loop invariants, `Assert`s),
   backed by `qcp-mcp` interactive checks on an isolated scratch, then pass
   the `annotation-checking` quality gate before the main agent backfills the
   real `.c` / `convex_hull_lib.v`.
3. **goal-frozen** — run `symexec` to freeze `*_goal.v` / `*_proof_auto.v` /
   `*_goal_check.v` and record the frozen lib prefix.
4. **vc-checking** — triage every VC into natural-language proof groups.
5. **vc-proving** — close each manual witness VC in Rocq; helper lemmas are
   developed on isolated proving scratch, audited, and migrated into the
   helper-suffix region of `convex_hull_lib.v` (frozen prefix untouched).
6. **final-check** — structural audit, re-run symexec + `coqc`, confirm no
   `Admitted` / extra `Axiom`, confirm `*_proof_manual.v` contains only
   witness proofs, confirm no stale scratch / `.tmp` / `.aux` artifacts.
7. **done** — all three cases are here.
