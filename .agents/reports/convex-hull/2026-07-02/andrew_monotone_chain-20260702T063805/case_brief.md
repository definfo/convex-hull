## Case Brief

- case_name: andrew_monotone_chain
- c_path: convex-hull/andrew_monotone_chain.c
- target_function: andrew_monotone_chain
- proof_type: refinement-proof
- output_path: convex-hull/ConvexHull
- reference_cases: convex-hull/graham_scan.c build_hull_from_sorted_tail; SeparationLogic/ConvexHull/Andrew_Monotone_Chain_M.v
- style_reference_cases: positive=convex-hull/graham_scan.c sorted helper refinement; negative=current whole-function refinement over unsorted input
- annotation_style: refinement-required+predicate-first
- anti_patterns: do not refine public unsorted input directly against andrew_monotone_chain_m; do not introduce a Rocq mirror of the C scan algorithm
- lib_frozen_prefix_end_line: 4140
- lib_frozen_prefix_snapshot: sha256:39fdbadc074592cf4e944800202200aa438f9456569ac127c9cbf01471b557f1
- annotation_spec_definitions_status: pending-scratch-review
- proof_manual_scope: witness-proofs-after-lib-migration
- current_phase: annotation
- main_state_files: convex-hull/andrew_monotone_chain.c; convex-hull/ConvexHull/andrew_monotone_chain_goal.v; convex-hull/ConvexHull/andrew_monotone_chain_proof_auto.v; convex-hull/ConvexHull/andrew_monotone_chain_proof_manual.v; convex-hull/ConvexHull/andrew_monotone_chain_goal_check.v; convex-hull/ConvexHull/convex_hull_lib.v
- persistent_report_dir: .agents/reports/convex-hull/2026-07-02/andrew_monotone_chain-20260702T063805
- report_layout: run-root-snapshots-plus-round-dirs
- latest_round_report_dir: .agents/reports/convex-hull/2026-07-02/andrew_monotone_chain-20260702T063805/20260702T063805-annotation-r1-sorted-helper
