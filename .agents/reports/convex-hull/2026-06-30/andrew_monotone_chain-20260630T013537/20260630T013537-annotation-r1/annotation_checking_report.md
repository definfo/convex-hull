## Annotation Checking Report

- status: blocked
- checked_scope: `convex-hull/andrew_monotone_chain.c`; scratch C `.tmp/convex-hull/andrew_monotone_chain__annotation_subagent_tmp.c`; annotation scratch lib `.tmp/convex-hull/ConvexHull/andrew_monotone_chain__annotation_subagent_tmp_lib.v`
- qcp_mcp_requirement_satisfied: yes
- annotation_scratch_lib_coqc_status: failed
- spec_definition_status: source-reviewed; required Andrew predicates exist and are mathematical property definitions, not a C loop/state-machine mirror
- function_spec_status: source-reviewed; final spec uses `andrew_hull_result`, sorting exposes permutation/sortedness, lower/upper loops use scan invariants; qcp-mcp reached file end
- invariant_status: source-reviewed; core invariants include logical scan predicates and PointArray segment/undef resource preservation; qcp-mcp reached file end
- annotation_scratch_lib_changes: empty
- summary: qcp-mcp successfully parsed and symbolically executed the scratch C to file end after a scratch-only include path adjustment. No C annotation or spec source patch was identified. The quality gate is blocked because the scratch lib cannot be compiled while existing compiled ConvexHull dependencies are inconsistent.
- failed_checks: `annotation_scratch_lib` coqc gate failed due stale/inconsistent official `.vo` dependencies: `ConvexHull.Reversal.vo` makes inconsistent assumptions over `ConvexHull.Record_Geo_Point`; `coqchk` also reports inconsistent assumptions over `ConvexHull.Graham_Scan_M`.
- required_annotation_rework: none identified in this round
- required_annotation_scratch_lib_rework: none identified at source level; main or an authorized owner should rebuild/refresh official ConvexHull compiled dependencies, then rerun this annotation-checking gate on a fresh scratch
- ready_for_main_common_case_formal_lib_update: no
- ready_for_main_symexec: no
- timing_summary: qcp failed load 5.13s; qcp successful load 3.51s; qcp symbolic file-end 5.30s; scratch-lib coqc failure 1.16s; dependency consistency check exceeded 30s and returned inconsistent assumptions
- timing_gaps: full wall-clock activity was not stopwatched per edit/review segment; coqchk emitted very large output and exact total runtime was not captured beyond the polling window

### Key Answers

1. Target mathematical spec: `andrew_hull_result base sorted hull`, supported by lower/upper scan predicates and final convex hull shape.
2. Spec style: property-level definitions over chains, ranges, envelopes, sortedness, permutation, and convex hull; not a direct C loop body mirror.
3. Function `Ensure`: uses the final mathematical result predicate and preserves `PointArray` resources.
4. Helper specs: sorting/partition specs expose permutation, sorted range, and partition properties needed by the caller.
5. Core loop invariants: lower and upper loops include scan predicates plus output segment/undef-tail shape.
6. Missing invariant state: none identified by qcp-mcp; remaining obligations are proof obligations.
7. Rework target if continuing: not C annotation/spec source; first fix the stale compiled Rocq dependency state so the scratch lib compile gate can run.
