## Case Brief

- case_name: andrew_monotone_chain
- c_path: convex-hull/andrew_monotone_chain.c
- target_function: andrew_monotone_chain
- proof_type: direct-proof
- output_path: convex-hull/ConvexHull
- reference_cases: convex-hull/graham_scan.c; convex-hull/graham_scan_dedup.c; QCP_examples/QCP_demos_LLM/int_array_merge_rel.c
- style_reference_cases: positive: QCP_examples/QCP_demos_LLM/int_array_merge_rel.c, QCP_examples/QCP_demos_LLM/majorityElement.c; negative: .agents/skills/annotation-filling/docs/incorrect-examples/max_sub_array_lib.v
- annotation_style: predicate-first
- anti_patterns: do not introduce a Rocq recursive/state-machine mirror of the C loops; do not weaken final correctness to range/memory only; do not replace PointArray memory predicates with duplicate custom array predicates; do not reintroduce andrew_hull_result after it was unfolded
- lib_frozen_prefix_end_line: 4125
- lib_frozen_prefix_snapshot: sha256:a80daa2e4d0ff96d525fd94f8fda721edb8d69cb29e09934011b37248a9e6442
- annotation_spec_definitions_status: integrated-and-refrozen
- proof_manual_scope: witness-proofs-after-lib-migration
- current_phase: vc-proving
- main_state_files: convex-hull/andrew_monotone_chain.c; convex-hull/ConvexHull/andrew_monotone_chain_goal.v; convex-hull/ConvexHull/andrew_monotone_chain_proof_auto.v; convex-hull/ConvexHull/andrew_monotone_chain_proof_manual.v; convex-hull/ConvexHull/andrew_monotone_chain_goal_check.v; convex-hull/ConvexHull/convex_hull_lib.v
- persistent_report_dir: .agents/reports/convex-hull/2026-06-30/andrew_monotone_chain-20260630T013537
- report_layout: run-root-snapshots-plus-round-dirs
- latest_round_report_dir: .agents/reports/convex-hull/2026-06-30/andrew_monotone_chain-20260630T013537/20260630T112443-vc-proving-r1

