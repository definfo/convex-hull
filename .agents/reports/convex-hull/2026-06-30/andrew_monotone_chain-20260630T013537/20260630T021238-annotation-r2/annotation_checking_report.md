## Annotation Checking Report

- status: passed
- checked_scope: `convex-hull/andrew_monotone_chain.c`; scratch C `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`; annotation scratch lib `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- qcp_mcp_requirement_satisfied: yes
- annotation_scratch_lib_coqc_status: passed
- spec_definition_status: passed; required Andrew predicates exist and are mathematical property definitions over geometry, sortedness, chain usage, envelope/capacity, and hull correctness, not C loop/state-machine mirrors
- function_spec_status: passed; final spec uses `andrew_hull_result`, sorting exposes permutation/sortedness, helper specs expose comparison/swap/partition semantics, and qcp-mcp reached file end
- invariant_status: passed; core invariants include lower/upper scan predicates plus `PointArray` segment/undef-tail ownership, not only ranges and memory shape
- annotation_scratch_lib_changes: empty
- summary: Fresh r2 scratch was created from official snapshots. qcp-mcp parsed and symbolically executed the scratch C to file end after a scratch-only include workaround. The `annotation_scratch_lib` compiled successfully under repository Coq flags after the official ConvexHull dependency rebuild. No C annotation or spec source patch was identified.
- failed_checks: none
- required_annotation_rework: none
- required_annotation_scratch_lib_rework: none
- ready_for_main_common_case_formal_lib_update: no; patch is empty
- ready_for_main_symexec: yes
- timing_summary: qcp load 5.55s; qcp symbolic file-end 5.26s; qcp close 2.70s; scratch-lib coqc 8.97s; remaining source review/report activity was not separately stopwatched
- timing_gaps: exact manual review, report editing, and scratch setup/cleanup wall-clock segments were not fully stopwatched

### Key Answers

1. Target mathematical spec: `andrew_hull_result base sorted hull`, supported by lower/upper scan predicates and final convex hull shape.
2. Spec style: property-level definitions over chains, sortedness, range use, envelopes, capacity, permutation, and convex hull; not a direct C loop body mirror.
3. Function `Ensure`: uses the final mathematical result predicate and preserves `PointArray` resources.
4. Helper specs: sorting/partition specs expose permutation, sorted range, outside-range preservation, and partition properties needed by the caller.
5. Core loop invariants: lower and upper loops include scan predicates plus output segment/undef-tail shape.
6. Missing invariant state: none identified by qcp-mcp in this round; remaining obligations are manual Rocq witness obligations.
7. Rework target if continuing: no annotation/spec rework; proceed to main-owned annotation gate validation and formal symexec refresh.
