# Graham Scan Sorting Annotation Audit

Scope: sorting-related functions in `convex-hull/graham_scan.c`:
`swap_points`, `partition_polar_points`, and `quicksort_polar_points`.

## Eliminated Assertions

- `swap_points`: the branch assertion for `i < j` was removed.
  The existing point-array strategies can split `PointArray::full` at field
  accesses to `pts[i]` and `pts[j]`, preserve the missing pieces, and fold the
  updated fields back into the final `point_swap` array.

- `swap_points`: the branch assertion for `j < i` was removed for the same
  reason. The order-specific segment decomposition is no longer needed as a C
  annotation.

- `partition_polar_points`: the assertion before reading `pts[high]` was
  removed. The existing point-array field strategies recover the `high` element
  from `PointArray::full` and keep the remaining array resource.

- `partition_polar_points`: the loop-body assertion before reading `pts[j]`
  was removed. The loop invariant already gives `PointArray::full` for the
  current logical array, and point-array strategies recover the current element
  on demand.

- `partition_polar_points`: the assertion after reading `ax` and `ay` was
  removed. The needed bounds and point facts are derivable from
  `PointCoordsBound pts_cur`, the loop invariant, and the field-read equalities
  exposed by the point-array strategies.

## Retained Annotations

- `swap_points` function contract is necessary. It is the semantic interface
  that lets callers replace an in-place two-point exchange with
  `PointArray::full(pts, n, point_swap(pts_l, i, j))`. Point strategies can
  automate local memory rearrangement, but they do not state the public
  permutation effect of the helper.

- `partition_polar_points` function contract is necessary. It exposes the
  partition result, range preservation, point permutation, and final array
  ownership needed by `quicksort_polar_points`.

- `partition_polar_points` loop invariant is necessary. It carries the
  algorithmic scan state in `PointPolarPartitionScanInv`, the current logical
  array `pts_cur`, pivot cache facts, bounds, and full array ownership across
  iterations. Point strategies only handle local array/field resources; they do
  not synthesize this semantic loop state.

- `quicksort_polar_points` function contract is necessary. It is the recursive
  sorting interface: callers need the final permutation, same-outside-range
  property, sorted range property, and full array ownership.

## Strategy Changes

No new point strategy was needed for this cleanup. The current
`convex-hull/point_array.strategies` rules are sufficient to eliminate the
local sorting assertions listed above.
