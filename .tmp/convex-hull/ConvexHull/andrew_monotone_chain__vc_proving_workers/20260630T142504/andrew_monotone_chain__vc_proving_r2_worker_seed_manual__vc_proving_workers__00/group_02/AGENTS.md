# Refinement VC Solver - Proof Group Worker

You are solving the assigned Rocq proof obligation(s) in an isolated worker copy of the proof manual.
Each run assigns one proof group to this worker. The focused goal file(s) are listed below, but your witness-proof edits go into `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v` and reusable helper lemmas go into worker_helper_scratch_lib `worker_helper/worker_helper_scratch_lib.v`.

## Workflow
1. **Inspect the proof group.** Read the assigned `goal_*.v` file(s) and the Proof Group Notes, then edit the matching witness proofs in `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v`.
2. **Reuse within the group.** Start from the representative or common proof pattern when one is provided. Adapt carefully; do not blindly copy variable names.

3. **Record an informal proof/reuse decision.** For every assigned goal, write a brief informal proof and whether the proof script can be reused, adapted, or must be written fresh in `proof_strategy_report.json`.
4. **Put helper lemmas in worker_helper_scratch_lib.** If a reusable fact is needed, add a proved top-level lemma to `worker_helper/worker_helper_scratch_lib.v`, not to the manual and not to common_case_formal_lib.
5. **Compile worker_helper_scratch_lib and manual together.** The worker manual already imports `VCWorker.worker_helper_scratch_lib`. Every solved report must be backed by a successful compile of worker_helper_scratch_lib followed by the manual.
6. **Keep proving until done.** Continue until every assigned goal is solved, the process timeout stops you, or you identify a concrete proof-obligation defect.
7. **No difficulty-based admits.** Do not intentionally leave a goal `Admitted.` because it is difficult, long, or lacks a direct helper lemma.

## Rules
- Read `tutorial/refinement_proof_tutorial.md` first for the overall proof workflow. It links to `tutorial/spatial_proof_tutorial.md` (for spatial entailments) and `tutorial/safeExec_proof_tutorial.md` (for the execution side) — consult them as needed.
- Edit only `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v`, `worker_helper/worker_helper_scratch_lib.v`, `proof_report.json`, and `proof_strategy_report.json`.
- Do not change any assigned witness lemma statement. Preserve the prelude/imports exactly as generated.
- You may add top-level helper lemmas in `worker_helper/worker_helper_scratch_lib.v` when needed. Helper lemmas must be proved and must not use `Admitted.`.
- If a helper lemma proof needs an extra library, add a minimal `Require Import ... .` or `From ... Require Import ... .` line in `worker_helper/worker_helper_scratch_lib.v` before the helper lemma. Do not add standalone `Import`, `Require Export`, or generated case imports under `SimpleC.EE.*`; the merge pipeline only migrates audited helper-suffix `Require Import` lines.
- Do not add top-level `Definition`, `Fixpoint`, `CoFixpoint`, `Inductive`, `CoInductive`, `Notation`, or `Axiom`.
- Prefer short, tutorial-aligned proofs over clever proofs.
- **Do NOT modify common_case_formal_lib, task_local_scratch_lib `andrew_monotone_chain__vc_proving_r2_tmp_lib.v`, `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v`, or the read-only `case_deps/` overlay.** They are compile-only dependencies resolved through the worker `_CoqProject` loadpath. The overlay exposes the current task_local_scratch_lib under the canonical `<case>_lib` logical module name for compilation only. If a proof needs an auxiliary fact, add a proved helper lemma in worker_helper_scratch_lib `worker_helper/worker_helper_scratch_lib.v`; the merge pipeline will migrate proved helper lemmas into task_local_scratch_lib after validation.
- Develop proofs by editing the goal file directly and using `coqc` to check.
- To inspect intermediate proof state, insert Rocq commands like `Show.`, `Show n.`, or `Show Existentials.` and re-run `coqc`. Remove these debug commands before declaring the proof complete.
- Use `Search <pattern>.`, `Check <name>.`, `Print <name>.`, and `About <name>.` to discover lemmas, definitions, and types. Wrap them in a separate scratch lemma or remove them after use so they don't appear in the final proof.
- After each goal, verify the worker manual compiles by running:
  ```
  coqc -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/worker_helper VCWorker -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic SimpleC.SL -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl Logic -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets SetsClass -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib compcert.lib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs AUXLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib SimpleC.StrategyLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common SimpleC.Common -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints FP -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib MonadLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib ListLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib MaxMinLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib GraphLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull ConvexHull -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull SimpleC.EE.convex_hull /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull/convex_hull_lib.v && coqc -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/worker_helper VCWorker -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic SimpleC.SL -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl Logic -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets SetsClass -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib compcert.lib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs AUXLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib SimpleC.StrategyLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common SimpleC.Common -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints FP -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib MonadLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib ListLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib MaxMinLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib GraphLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull ConvexHull -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull SimpleC.EE.convex_hull /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull/point_array_strategy_goal.v && coqc -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/worker_helper VCWorker -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic SimpleC.SL -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl Logic -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets SetsClass -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib compcert.lib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs AUXLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib SimpleC.StrategyLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common SimpleC.Common -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints FP -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib MonadLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib ListLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib MaxMinLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib GraphLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull ConvexHull -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull SimpleC.EE.convex_hull /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull/point_array_strategy_proof.v && coqc -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/worker_helper VCWorker -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic SimpleC.SL -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl Logic -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets SetsClass -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib compcert.lib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs AUXLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib SimpleC.StrategyLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common SimpleC.Common -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints FP -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib MonadLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib ListLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib MaxMinLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib GraphLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull ConvexHull -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull SimpleC.EE.convex_hull /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull/andrew_monotone_chain_goal.v && coqc -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/worker_helper VCWorker -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic SimpleC.SL -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl Logic -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets SetsClass -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib compcert.lib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs AUXLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib SimpleC.StrategyLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common SimpleC.Common -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints FP -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib MonadLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib ListLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib MaxMinLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib GraphLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull ConvexHull -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull SimpleC.EE.convex_hull worker_helper/worker_helper_scratch_lib.v && coqc -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/worker_helper VCWorker -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic SimpleC.SL -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl Logic -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets SetsClass -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib compcert.lib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs AUXLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib SimpleC.StrategyLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common SimpleC.Common -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints FP -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib MonadLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib ListLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib MaxMinLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib GraphLib -R /home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull ConvexHull -Q /home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull SimpleC.EE.convex_hull andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v
  ```
  Fix compile errors before moving on. Update `proof_report.json` only after `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v` compiles and the assigned goal no longer contains `Admitted.`.
- `coqc` and `coqtop` in this worker are wrapped with a hard 4 GiB memory kill guard. Use the bare command names so the wrappers stay in effect.
- Your writable and inspectable workspace is this group directory only.
- You may run the generated `coqc` command even though it contains absolute Rocq `-Q`/`-R`/`-I` dependency paths. Those paths are compile-only dependencies.
- Do NOT inspect compile-only dependency paths with shell tools or editor reads. In particular, do not run `cat`, `sed`, `rg`, `grep`, `find`, `ls`, `head`, `tail`, or similar commands on:
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/SeparationLogic`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/unifysl`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/sets`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/compcert_lib`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/auxlibs`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/StrategyLib`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/Common`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/fixedpoints`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/MonadLib`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/listlib`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/MaxMinLib`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/GraphLib`
  - `/home/definfo/Develop/qcp/convex-hull/SeparationLogic/ConvexHull`
  - `/home/definfo/Develop/qcp/convex-hull/.tmp/convex-hull/ConvexHull/andrew_monotone_chain__vc_proving_workers/20260630T142504/andrew_monotone_chain__vc_proving_r2_worker_seed_manual__vc_proving_workers__00/group_02/case_deps/convex_hull`
- Allowed reads are limited to `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v`, `worker_helper/worker_helper_scratch_lib.v`, assigned `goal_*.v` files in this group, `AGENTS.md`, `tutorial/*.md`, `_CoqProject`, and optional proof reuse reference `proof_reuse_pattern_references.json` if present.
- Allowed uses of dependency paths are `coqc`/`coqtop` compilation or proof-state checking for the current assigned goal only, not browsing unrelated modules or source files.
- Forbidden examples:
  - `rg "lemma_name" /path/to/some_outside_directory/foo.v`
  - `sed -n '1,200p' /path/to/some_outside_directory/foo.v`
  - `find .. -name '*.v'`
  - `cat ../group_01/andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v`
- If you need to understand an external definition, lemma, or notation, use Rocq commands such as `Print`, `Search`, `Check`, and `About` inside `coqtop` or a temporary local scratch `.v` file for the current assigned goal. Do not inspect the external source file with shell/editor reads.
- Do NOT modify anything in `tutorial/`.
- Keep proving until every assigned goal is solved or the process timeout stops you. Do not intentionally admit a goal because the proof is hard, long, or no direct theorem was found.
- You may stop early on an unsolved goal only when you find a concrete proof-obligation defect showing the goal is not provable as stated.
- A proof-obligation defect must include specific Rocq evidence: the reduced goal, contradictory hypotheses, a missing necessary precondition, or a minimal counterexample argument. General statements such as "needs a helper lemma", "no direct theorem found", "large composition proof", or "remaining bound not exposed" are not valid blockers.
- If you find a concrete proof-obligation defect, keep your best partial proof in `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v` and end the assigned goal with `Admitted.` so the file still compiles. Then write a blocker report explaining the exact defect and the last meaningful proof state reached.

## Reports
After each goal, append an entry to `proof_report.json`:
- Solved: `{"goal": "<lemma_name>", "status": "solved", "elapsed_seconds": <number>, "coqc_seconds": <number or null>, "slow_steps": ["<optional tactic/compile bottleneck>"]}`
- Unsolved: `{"goal": "<lemma_name>", "status": "admitted", "elapsed_seconds": <number>, "coqc_seconds": <number or null>, "report": "<concise explanation of what went wrong and what was tried>"}`

The file is a JSON array of all entries: `[{"goal": "...", "status": "solved", "elapsed_seconds": 0.0, "coqc_seconds": null}, ...]`.
If exact timing is unavailable, use `null` and explain the timing gap in `proof_strategy_report.json`.

When you finish the group, also write `proof_strategy_report.json` describing your clustering and reuse decisions:
```json
{
  "clusters": [
    {"name": "A",
      "representative": "<lemma_name_of_representative>",
      "members": ["<lemma_name>", "..."]}
  ],
  "reuse_decisions": [
    {"goal": "<lemma_name>",
      "informal_proof": "<one or two sentences>",
      "reuse_decision": "reuse|adapt|fresh|blocked",
      "reason": "<hash match, proof pattern match, context mismatch, or no prior match>"}
  ],
  "notes": "<short summary of the helper/witness proof strategy>",
  "timing": {
    "elapsed_seconds": <number or null>,
    "slowest_goals": ["<lemma_name>", "..."],
    "major_time_sinks": ["<proof search, coqc, rocq-mcp startup, etc.>"],
    "timing_gaps": ["<unknown timing and why>"]
  }
}
```

## Assigned Goals
- `proof_of_swap_points_return_wit_1` (`goal_14__proof_of_swap_points_return_wit_1.v`)

## Proof Group Notes
- proof_group_id: swap_points_model
- grouping_source: vc-checking-group-plan
- representative_witness: proof_of_swap_points_return_wit_1
- natural_language_proof_pattern: Normalize nested field stores into the point_swap list model and preserve full array ownership.
- shared_helper_candidates: empty
- proving_hints: Rewrite replace_Znth and point_swap_Znth lemmas; use point_eq_by_xy for point extensionality.
- grouping_confidence: high

## Files
- `andrew_monotone_chain__vc_proving_r2_worker_seed_manual.v` - worker-local full proof manual (editable)
- `worker_helper/worker_helper_scratch_lib.v` - worker_helper_scratch_lib (editable)
- `goal_*.v` - assigned goal files for focused reading (read-only)
- `proof_reuse_pattern_references.json` - optional JSON proof-pattern references from an earlier checkpoint (read-only if present)
- `tutorial/refinement_proof_tutorial.md` - main proof tutorial (read-only)
- `tutorial/spatial_proof_tutorial.md` - spatial entailment tactics (read-only)
- `tutorial/safeExec_proof_tutorial.md` - execution-side tactics (read-only)
