## VC Proving Failure Analysis

- case: `convex-hull/ConvexHull/andrew_monotone_chain.c`
- round: `20260630T155146-vc-proving-r4`
- owner: `vc-proving-subagent`
- outcome: blocked

### Evidence

- r4 scratch manual compiles only with 8 admitted witness lemmas:
  - `proof_of_andrew_monotone_chain_entail_wit_1`
  - `proof_of_andrew_monotone_chain_entail_wit_3`
  - `proof_of_andrew_monotone_chain_entail_wit_4_1`
  - `proof_of_andrew_monotone_chain_entail_wit_4_2`
  - `proof_of_andrew_monotone_chain_entail_wit_5`
  - `proof_of_andrew_monotone_chain_entail_wit_7`
  - `proof_of_andrew_monotone_chain_entail_wit_8_1`
  - `proof_of_andrew_monotone_chain_entail_wit_8_2`
- r4 task-local lib compiles and preserves the frozen prefix exactly:
  - `diff` over lines `1..4125` between official `convex_hull_lib.v` and r4 task-local lib produced 0 lines.
- r4 helper suffix has no `Admitted`, no `Axiom`, and no forbidden top-level `Definition` / `Fixpoint` / `Inductive` / `Notation` after line 4125.
- Generated dependency chain compiled in the r4 overlay:
  - `convex_hull_lib.v`
  - `point_array_strategy_goal.v`
  - `point_array_strategy_proof.v`
  - `andrew_monotone_chain_goal.v`
  - `andrew_monotone_chain_proof_auto.v`
- r4 scratch manual compiled with remaining admits.
- `coqtop` search found no existing bridge lemma for:
  - `andrew_complete_hull_shape`
  - `andrew_lower_finished_chain`
  - `andrew_upper_suffix_geometry`
  - `point_chain_left_envelope`
- `Print Graham_Scan_M.is_convex_hull` shows it requires `Graham_Scan_M.rev_ccw_convex` and `Hull_Equiv.is_max_hull'_edges`, while the frozen Andrew predicates track range use, index monotonicity, left turns, and envelope facts. Existing searched lemmas bridge hull correctness from `Record_Geo_Point.sort`, `rev_consec_ccw`, and `is_max_hull'`, not from the frozen Andrew predicates.

### Blocking Helper Families

The following helper families remain unproved and are needed by the 8 unsolved witnesses:

- `point_list_not_all_same_of_points_not_all_same_permutation`
- `andrew_lower_scan_inv_init`
- `andrew_lower_scan_inv_pop`
- `andrew_lower_scan_inv_push`
- `andrew_upper_scan_inv_init_from_lower_finished`
- `andrew_upper_scan_inv_pop`
- `andrew_upper_scan_inv_push`
- Andrew hull-correctness bridge:
  - from `andrew_lower_finished_chain` + `andrew_upper_suffix_geometry` + `andrew_upper_capacity` + `andrew_upper_append_ready` to `andrew_complete_hull_shape`
  - from `andrew_complete_hull_shape` to `is_convex_hull` over the original base via `point_permutation`

### Diagnosis

This is not a quicksort/spatial-array blocker. Quicksort composition and direct Andrew bounds witnesses were reconstructed and compile-gated in r4 scratch.

The remaining blocker is semantic: the current frozen Andrew specification requires preservation and final hull-correctness theorems that are not present in the existing library and are too substantial to introduce safely as ad hoc witness-local proof scripts. Proving them appears to require a designed mathematical bridge between the frozen Andrew scan predicates and the imported Graham/Hull_Equiv correctness predicates.

No official files were edited.
