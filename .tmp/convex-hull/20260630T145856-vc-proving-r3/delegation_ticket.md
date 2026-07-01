## Delegation Ticket

- subagent_name: vc-proving-subagent
- skill_name: vc-proving
- task_type: vc-proving-phase
- phase: vc-proving
- phase_input_version: post-refactor goal sha256:65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef
- trigger_rule: r3 relaunch after r1/r2 subagent transport failures; no proof report was produced
- iteration_owner: subagent
- return_condition: completed | blocked | stale
- target_scope: all 37 proof lemmas in current proof manual
- scratch_seed_files: convex-hull/ConvexHull/andrew_monotone_chain_proof_manual.v; convex-hull/ConvexHull/convex_hull_lib.v
- scratch_owned_paths: .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_r3_tmp_proof_manual.v; .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_r3_tmp_lib.v; .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T145856
- witness_group_plan: .tmp/convex-hull/20260630T145856-vc-proving-r3/vc_checking_group_plan.json
- grouping_source: vc-checking-group-plan
- worker_manual_workdir: .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T145856
- report_staging_dir: .tmp/convex-hull/20260630T145856-vc-proving-r3
- previous_vc_proving_checkpoint: none
- previous_partial_proof_packet: none
- checkpoint_reuse_policy: exact_or_pattern
- timing_required: true
- proof_manual_write_contract: witness-proofs-after-lib-migration
- lib_write_contract: frozen-prefix-then-helper-imports-and-lemmas
- protected_lib_prefix_end_line: 4125
- task_local_scratch_lib_module: SimpleC.EE.convex_hull.convex_hull_lib
- worker_execution_mode: coqc_only
- allowed_write_set: r3 scratch paths, r3 worker workdir, r3 report_staging_dir
- forbidden_write_set: official main-state files; generated files; common_case_formal_lib; official proof manual; stale r1/r2 scratch/workdirs
- vc_informal_proof_report_path: .agents/reports/convex-hull/2026-06-30/andrew_monotone_chain-20260630T013537/20260630T024232-vc-checking-r1/vc_checking_informal_proof_report.md
- stale_if: any frozen input hash changes; witness set changes; formal proof_manual/common_case_formal_lib integration by main; symexec refresh

## Re-entry Brief

- reentered_from_phase: vc-proving
- why_reentered: r1 failed with `429 Too Many Requests`; r2 failed with `stream disconnected before completion`; neither returned a phase result.
- what_failed_last_round: subagent transport/backend only. r1/r2 worker summaries showed `no_report` for all 37 goals, so no proof payload exists.
- affected_witnesses_or_files: all 37 witnesses remain unproved in official proof_manual. Stale r1/r2 `.tmp` workspaces exist and must not be reused.
- what_changed_since_last_round: no official input changed. r3 uses fresh scratch names ending in `vc_proving_r3`.
- must_focus_this_round: use fresh r3 scratch, prove or return a structured blocked/stale result. If concurrent workers fail again, switch within this subagent to serial fallback; do not return merely because workers failed.

## Frozen Input Hashes

- C: sha256:9ae7c264b2f4b8f06ae63a9c234b3dd1c94581cb4bb6a6e909665e43a5342842
- common_case_formal_lib: sha256:a80daa2e4d0ff96d525fd94f8fda721edb8d69cb29e09934011b37248a9e6442
- goal: sha256:65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef
- proof_auto: sha256:e5155859b0b92f01ae072f486ff55c26b60d37c9b7be9989ed9b93465f3eb7d3
- proof_manual: sha256:33c9f7cded508a1687ca8a83b6a5196f22318286a4d300c81a435bfda66bc097
- goal_check: sha256:55f5ee519f32b889f41791eb31047192979e5474bdd55e859200248145e126ec

