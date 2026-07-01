## Delegation Ticket

- subagent_name: vc-proving-subagent
- skill_name: vc-proving
- task_type: vc-proving-phase
- phase: vc-proving
- phase_input_version: post-refactor goal sha256:65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef
- trigger_rule: r4 relaunch after r3 blocked with 20/37 solved only in worker-local scratch
- iteration_owner: subagent
- return_condition: completed | blocked | stale
- target_scope: all 37 proof lemmas in current proof manual; prioritize unsolved groups 05-07, but final handoff must cover all 37
- scratch_seed_files: convex-hull/ConvexHull/andrew_monotone_chain_proof_manual.v; convex-hull/ConvexHull/convex_hull_lib.v
- scratch_owned_paths: .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_r4_tmp_proof_manual.v; .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_r4_tmp_lib.v; .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T155146
- witness_group_plan: .tmp/convex-hull/20260630T155146-vc-proving-r4/vc_checking_group_plan.json
- grouping_source: vc-checking-group-plan
- worker_manual_workdir: .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T155146
- report_staging_dir: .tmp/convex-hull/20260630T155146-vc-proving-r4
- previous_vc_proving_checkpoint: none
- previous_partial_proof_packet: none
- checkpoint_reuse_policy: pattern_reference
- timing_required: true
- proof_manual_write_contract: witness-proofs-after-lib-migration
- lib_write_contract: frozen-prefix-then-helper-imports-and-lemmas
- protected_lib_prefix_end_line: 4125
- task_local_scratch_lib_module: SimpleC.EE.convex_hull.convex_hull_lib
- worker_execution_mode: coqc_only
- worker_runtime_status: concurrent Codex worker runtime unavailable in r3 (`Read-only file system (os error 30)`); serial fallback is authorized from round start if needed
- allowed_write_set: r4 scratch paths, r4 worker workdir, r4 report_staging_dir
- forbidden_write_set: official main-state files; generated files; common_case_formal_lib; official proof manual; stale r1/r2/r3 scratch/workdirs
- vc_informal_proof_report_path: .agents/reports/convex-hull/2026-06-30/andrew_monotone_chain-20260630T013537/20260630T024232-vc-checking-r1/vc_checking_informal_proof_report.md
- r3_pattern_references: .tmp/convex-hull/20260630T145856-vc-proving-r3/subagent_return_report.md; .tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_r3_tmp_proof_manual__vc_proving_workers__00/group_00; group_01; group_02; group_03; group_04
- r3_unsolved_groups: group_05 quicksort_xy_composition; group_06 andrew_lower_scan; group_07 andrew_upper_scan
- stale_if: any frozen input hash changes; witness set changes; formal proof_manual/common_case_formal_lib integration by main; symexec refresh

## Re-entry Brief

- reentered_from_phase: vc-proving
- why_reentered: r3 returned `blocked` after solving only groups 00-04 in worker-local scratch. No merged helper-free manual or migrated task_local_scratch_lib exists.
- what_failed_last_round: groups 05-07 remain unsolved; worker runtime unavailable; r3 serial fallback ran out before helper families for quicksort sorted-range and Andrew lower/upper scan were proved.
- affected_witnesses_or_files: official proof manual still has all 37 admitted witness proofs; r4 must produce a full handoff or an updated blocked report. r3 solved proofs are only proof-pattern references until r4 reconstructs them in fresh scratch and compile-gates them.
- what_changed_since_last_round: no official inputs changed. r4 uses fresh scratch names ending in `vc_proving_r4`.
- must_focus_this_round: build group-local helper lemmas for `point_xy_sorted_range` composition/preservation and Andrew lower/upper scan transitions; then migrate helpers into r4 task_local_scratch_lib and verify a helper-free full manual.

## Frozen Input Hashes

- C: sha256:9ae7c264b2f4b8f06ae63a9c234b3dd1c94581cb4bb6a6e909665e43a5342842
- common_case_formal_lib: sha256:a80daa2e4d0ff96d525fd94f8fda721edb8d69cb29e09934011b37248a9e6442
- goal: sha256:65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef
- proof_auto: sha256:e5155859b0b92f01ae072f486ff55c26b60d37c9b7be9989ed9b93465f3eb7d3
- proof_manual: sha256:33c9f7cded508a1687ca8a83b6a5196f22318286a4d300c81a435bfda66bc097
- goal_check: sha256:55f5ee519f32b889f41791eb31047192979e5474bdd55e859200248145e126ec

