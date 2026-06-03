---
name: vc-proving
description: 默认使用脚本化隔离 Codex worker，并在 Windows 下只通过本地 coqc.exe / coqtop.exe 编译反馈证明 qcp/symexec 生成的 manual VC；若 Codex worker 环境不可恢复，则允许在同一 proving scratch 上执行串行 fallback。worker / fallback 产出的 helper lemmas 先迁移到本轮 task_local_scratch_lib，所有目标 VC 完成后才由主 agent 与 helper-free manual 一次性回填正式文件。
---

# VC Proving

这个 skill 只负责把已确认可证的 manual VC 变成可编译的 Rocq 证明，并保持 formal 文件职责清晰。
它固定绑定给 `vc-proving-subagent`；phase、ledger 状态和 delegation 合同统一由 `verification-orchestrator` 定义；本 skill 不再重复定义它们。

## 何时使用

- case 已由 `verification-orchestrator` 置于 `vc-proving` 阶段。
- 主 agent 已为当前 proving 轮次启动 `vc-proving-subagent`。
- 目标 witness 已被确认可以进入 proving。
- 默认通过 `split_manual_goals.py`、`prepare_agent_concurrent.py`、`run_agent_concurrent.py`、`validate_and_merge.py`、`migrate_helpers_to_lib.py`、`verify_manual_goals.py` 启动脚本化 sandboxed Codex worker，并发证明 witness；每轮结束时若已产生 compile-gated 局部成果，应通过 `checkpoint_round.py` 固化为 report checkpoint / JSON partial proof packet，供下一轮 fresh scratch 复用；若 Codex worker 环境不可恢复，则在同一轮切换到 proving scratch 上的串行 fallback，完成 helper-to-`task_local_scratch_lib` migration 后把可回填结果交给主 agent。若只是 worker 内 `rocq-mcp` 启动或调用失败，但 worker-local `coqc` 可用，则这不是证明阻塞：记录 MCP 失败证据，立即改用 worker-local `coqc` / 必要时 `coqtop` 驱动同一份 worker manual 继续证明。

## 进入前提

- 当前 `goal` / witness 集合对应最新冻结版本。
- 目标 witness 不处于 stale 状态。
- 主 agent 已决定当前轮到哪些 witness 正式进入证明。
- 当前 delegation ticket 的 `subagent_name` 固定为 `vc-proving-subagent`。
- 当前 delegation ticket 已给出最新正式 `*_proof_manual.v` / `common_case_formal_lib` 快照和本轮 proving scratch 路径；若旧 proving scratch 仍存在，必须先删除再重建。
- 当前 delegation ticket 已明确：
  - `proof_manual_write_contract = witness-proofs-after-lib-migration`
  - `lib_write_contract = frozen-prefix-then-helper-imports-and-lemmas`
  - `protected_lib_prefix_end_line`
  - `task_local_scratch_lib_module`（若无法唯一推断，必须显式提供给 prepare 脚本）
  - `worker_execution_mode`（`rocq_mcp` 或 `coqc_only`；`use_rocq_mcp` 只作为旧 manifest 兼容字段）
  - `witness_group_plan`（来自 `vc-checking` 的自然语言证明分组；若缺失，脚本才使用排序分块 fallback）
  - `previous_vc_proving_checkpoint`（若存在上一轮可复用 checkpoint，则给出 `vc_proving_round_checkpoint.json`；没有则写 `none`）
  - `previous_partial_proof_packet`（默认由 checkpoint manifest 间接指定；只有脱离 checkpoint 调试时才直接给出）
  - `checkpoint_reuse_policy`（`exact_or_pattern`、`exact`、`extended_candidate`、`pattern_reference` 或 `disabled`；默认 `exact_or_pattern`）
  - checkpoint direct-reuse stale 条件：`source_goal_version`、`lib_frozen_prefix_hash`、`protected_lib_prefix_end_line`、packet hash、helper payload 冲突或 direct candidate compile gate 失败任一发生时不得自动移除 worker scope；但在 `exact_or_pattern` / `pattern_reference` 下仍应生成 proof-pattern reference 供 worker 学习和改写
- 当前 delegation ticket 已明确：本轮 `vc-proving` 的 `iteration_owner` 是 `vc-proving-subagent`，main 线程不会在等待一段时间后接管本轮 proving。
- 若来自返工、重新证明或下游回流，当前 ticket 还必须附带 `Re-entry Brief`，说明上一轮在哪个 witness / 文件上失败、这次为何重开。

## 直接输出

- 已在 proving scratch `*_proof_manual.v` / `task_local_scratch_lib` 上验证过、可回填到正式 manual 的 witness proofs 和可回填到 `common_case_formal_lib` 的 helper-suffix imports / helper lemmas；这些 helper imports / helper lemmas 只作为本轮批量集成候选返回，不允许 subagent 或 worker 提前修改 `common_case_formal_lib`。
- worker 产生的 `proof_report.json`、`proof_strategy_report.json`、merged scratch manual 路径、migrated scratch manual/lib 路径和参考案例映射。
- 若本轮不是 annotation-bug / stale，且有已通过 merge/migration/compile gate 的 solved witness 或 helper payload，应输出本轮 `vc_proving_round_checkpoint.json`、`partial_proof_packet.json`、`reuse_index.json` 的持久 report 路径，以及 checkpoint reuse 命中数 / 未解 witness 列表；checkpoint 是 report artifact，不是继续沿用旧 scratch。
- 本轮 proving 总 wall-clock 耗时、split / prepare / run / validate / migrate / verify 各步骤耗时、worker-local 或串行 fallback 的 proof search / coqc 耗时、失败编译和重跑耗时、proof 分析/编辑、helper 设计/迁移/清理、worker 等待/fallback 切换等 activity 耗时、最慢 witness/helper，以及主要 proof bottleneck。不能只报告最后一次成功编译；失败、超时、worker 准备和等待同样属于本轮 proving 成本。
- 若本轮返回 `blocked` 或总耗时超过 600 秒，必须额外输出 blocked / long-duration 诊断：blocked reason、long-duration reason、具体证据、受影响 witness/helper/文件、已经尝试过的路径、下一步建议。
- 正式回填 `*_proof_manual.v` / `common_case_formal_lib` 前的集成建议、依赖顺序和风险提示；若本轮包含多个 witness / worker，必须说明 helper-free manual 与 `task_local_scratch_lib` 应在所有目标 VC 完成后作为同一批次合并。
- `Subagent Return Report`，其 `round_outcome` 只能是 `completed`、`blocked` 或 `stale`。

## 会使哪些产物失效

- 任何 `*_proof_manual.v` 或 `common_case_formal_lib` 的改动，都会使旧的 final-check 结论失效。
- 若 proving 中暴露出 annotation 层问题，主 agent 必须退回 annotation，并按 orchestrator 规则使当前 proving 计划失效。

## 主 / 子 Agent 局部边界

- `vc-proving-subagent` 拥有 proving scratch `*_proof_manual.v` / `task_local_scratch_lib`、脚本化 worker workdir 和该轮 worker-local `coqc.exe` / `coqtop.exe` 编译反馈使用权；若进入串行 fallback，则额外拥有 proving scratch / scratch-local manual 上的隔离 `coqc.exe` / `coqtop.exe` 编译循环使用权。Windows 下不得调用 `rocq-mcp`。
- `vc-proving-subagent` 默认通过 `scripts/` 启动隔离的 Codex worker 分组证明；若已记录 Codex CLI / transport / backend / worker 会话不可恢复，则允许在 phase subagent 自己的 proving scratch 上执行串行 fallback proof loop。
- 主 agent 独占正式 `*_proof_manual.v` / `common_case_formal_lib` 写入、symexec、coqc、`Admitted` / 额外 `Axiom` review 和最终 proof 集成。`common_case_formal_lib` 只能在当前 vc-proving 轮次所有目标 VC 都完成后，与 helper-free manual 一次性同步回填；禁止为了单个 helper lemma 提前追加 `common_case_formal_lib`。
- `vc-proving-subagent` 不并发修改正式文件；脚本 worker 必须在各自 workdir 使用本地 `_CoqProject` 和 `coqc.exe` / `coqtop.exe`。Windows 下不得生成或使用 `rocq-mcp` 配置。进入串行 fallback 时，也必须保持 workdir / scratch 隔离，不得把 main 线程复核混入当前 proving loop。
- worker-local 和 merged scratch `*_proof_manual.v` 可暂存当前 case 的 manual witness theorem 及本轮 worker 合并来的 proved helper lemmas；helper-migration 后的 handoff manual 必须只保留 witness proofs。
- `task_local_scratch_lib` 在 worker proving 阶段作为只读参考；`validate_and_merge.py` 成功后，`migrate_helpers_to_lib.py` 可在保持冻结前缀不变的前提下，把 audited helper-suffix `Require Import` 行与 proved helper lemmas 迁入 `task_local_scratch_lib` 后缀。`task_local_scratch_lib` 是本轮 helper 的唯一汇总点；`common_case_formal_lib` 在整个 vc-proving round 内保持只读，避免反复触发依赖重编译。
- helper lemma 只允许是 proved `Lemma` / `Theorem` / `Fact` / `Remark` 等证明块；helper-suffix imports 只允许是脚本审计通过的 `Require Import` / `From ... Require Import` 行，禁止导入 `SimpleC.EE.*` 生成 case artifact；禁止新增顶层 `Definition` / `Fixpoint` / `Inductive` / `Notation` / `Axiom`。
- 如果证明推进需要改写 `common_case_formal_lib` 冻结前缀，或确实依赖新增上述顶层定义，则本轮必须以 `blocked` 返回。
- 本轮 `vc-proving` 一旦交给 `vc-proving-subagent`，main 线程不得因为等待较久而强行打断并自己继续证明。

## 参考文档

1. 先读 `../verification-orchestrator/SKILL.md`
2. `docs/use-notes.md`
3. `docs/separation-logic-whole-proof-tactics.md`
4. 目标涉及 `safeExec`、monad 或 refinement 时，再读 `docs/refinement-proof-tactics.md`
5. 目标涉及数组、字符数组、C 字符串或字符串字面量时，读 `../annotation-filling/docs/builtin-array-string-support.md`
6. 需要找风格对照时，读 `docs/reference-cases.md`
7. `vc-proving` 默认使用 `scripts/split_manual_goals.py`、`prepare_agent_concurrent.py`、`run_agent_concurrent.py`、`validate_and_merge.py`、`migrate_helpers_to_lib.py`、`verify_manual_goals.py`、`checkpoint_round.py` 和 `apply_partial_proof_packet.py`；若本轮已记录 Codex worker 环境不可恢复，则允许改用 proving scratch 上的串行 fallback，但不得切回 main 接管 proof search。

## 工作步骤

1. 读取当前 proving 轮次的 delegation ticket，确认目标 witness 集、`source_goal_version`、正式 proof 快照、本轮 proving scratch 路径、`protected_lib_prefix_end_line`、formal 写入合同、`timing_required` / `timing_log_path`、`previous_vc_proving_checkpoint` / `checkpoint_reuse_policy`，以及是否附带 `Re-entry Brief`；记录本轮 `phase_started_at`。
2. 若存在 `Re-entry Brief`，先根据其中的失败 witness / 文件、上一轮失败原因和本轮变化点，决定当前 proving 的优先处理顺序。
3. 若旧的 proving scratch 仍存在，先删除；随后从最新正式 `*_proof_manual.v` / `common_case_formal_lib` 复制出 fresh proving scratch pair。若当前 case 尚无 `common_case_formal_lib`，则为本轮 scratch 创建最小 `task_local_scratch_lib` 搭档。若目标中出现 `IntArray` / `UIntArray` / `CharArray` / `store_string` / `store_stringLit` / `GlobalStrings` 等 builtin 谓词，先按 `../annotation-filling/docs/builtin-array-string-support.md` 查找对应 lemma、策略触发条件和参考 proof。
4. 在 proving scratch manual 上默认运行脚本化并发流水线，并对每条 pipeline 命令记录开始/结束时间、elapsed seconds、返回结果和输出 report 路径；同时记录 phase owner 等待 worker、fallback 切换、scratch 准备/清理、失败编译重跑和手工 proof 编辑的 wall-clock activity。默认使用 `vc-checking` 输出的 `witness_group_plan` 创建 proof group：每个 group 一个 worker-local manual 和一个组内 `worker_helper_scratch_lib`，组内多个 witness 可共享 helper；如果没有 group plan，才按 witness 名称排序后用 fallback chunk-size 分组。prepare 阶段必须为 base / group workdir 创建只读 `case_deps/` overlay，把当前正式 `*_goal.v` 暴露为 manual 中已有的 canonical `SimpleC.EE...<case>_goal` 逻辑模块名，把本轮 `task_local_scratch_lib` 只暴露为当前 common_case_formal_lib 对应的 canonical `<case>_lib` 逻辑模块名；manual 额外导入的共享 `SimpleC.EE.*_lib`、其他直接 `SimpleC.EE.*` helper，以及 generated source 闭包中的 bare strategy/support imports 都应复制为只读正式依赖，不得误绑定到 `task_local_scratch_lib`。一旦 overlay 启用，worker `_CoqProject` 必须移除原仓库级 `SimpleC.EE` loadpath，由 overlay 成为 generated case artifact 的唯一解析源。随后预编译 overlay 中的 lib / goal / helper `.vo`：
   - `split_manual_goals.py <scratch_proof_manual> --goals <witness...>`
   - 若本轮有上一轮 `vc_proving_round_checkpoint.json`，`run_agent_concurrent.py` 应优先通过 `--reuse-checkpoint <checkpoint> --checkpoint-reuse-policy exact_or_pattern` 调用 proof-reuse prepass：读取 checkpoint manifest，先尝试校验 `source_goal_version` / frozen prefix line 与 hash / packet hash / helper payload。若上下文满足 direct reuse，先用 JSON packet 中的 audited helper imports / helper blocks 初始化 fresh `task_local_scratch_lib`，再用当前 fresh manual 的 lemma statement 加 packet 中的 `proof_script` 重建 candidate proof block；candidate manual 和更新后的 `task_local_scratch_lib` 通过 compile check 后，已复用 witness 才能从 worker scope 移除。若上下文不满足 direct reuse、helper payload 冲突或 candidate compile gate 失败，不应丢弃 packet，也不得保留失败写入的 helper scratch，而应生成 `proof_reuse_pattern_references.json`，列出相似 witness、旧 proof script、informal proof、依赖、helper 参考、完整 proof reference pool 和 mismatch / compile-failure 原因，交给 worker 学习证明形状；这些 pattern reference 不自动视为 solved。
   - 若只有上一轮已验证 handoff manual 的复用索引，`run_agent_concurrent.py` 可通过 `--reuse-index <reuse_index.json>` 自动执行 proof reuse prepass：先调用 `proof_reuse_index.py` 等价逻辑生成 `proof_reuse_candidate_proof_manual.v` / `proof_reuse_apply_report.json`，通过 compile check 后把已复用 witness 从 worker scope 中移除，只把仍含 `Admitted.` 的目标交给 worker。只有 `goal_body_hash`（优先）或 `statement_hash` 与 `lib_frozen_prefix_hash` / `helper_suffix_hash` 同时匹配时才允许复用。`context_mismatch` / `no_match` 的 witness 必须写 informal proof 后再证明，不能靠旧 proof block 强行续用。
   - `prepare_agent_concurrent.py <manifest> <scratch_lib> --group-plan <vc_checking_group_plan.json> [--task-local-module <canonical_lib_module>] [--worker-execution-mode rocq_mcp|coqc_only]`（无 group plan 时才用 `--chunk-size <K>` fallback；若 `task_local_scratch_lib_module` 无法唯一推断，必须传 `--task-local-module`；若 manifest 已有 `worker_execution_mode`，prepare 必须优先沿用，CLI 显式值可覆盖）
     - prepare 阶段应自动为 base / group workdir 生成 worker-local `_CoqProject`，为每个 group worker 创建 `worker_helper_scratch_lib`，把 `witness_group_plan` 中的 proof pattern notes 写入 worker `AGENTS.md`，并生成指向 group workdir 的 `.codex/config.toml`；`case_deps/` overlay 只能由脚本创建为只读 compile-only dependency，worker 不得读取、修改或手工补救其中的 `*_goal.v` / canonical `<case>_lib.v`。prepare 还必须写出 `vc_proving_preflight.json`，记录 group plan 覆盖、overlay compile、stale `.vo`、worker mode、memory guard 和 case dependency 模块；group workdir 应优先复用 base workdir 已准备并编译过的 `case_deps/` overlay cache。
   - `run_agent_concurrent.py <manifest> --skip-prepare --max-parallel <N>`；若未单独 prepare，可直接运行 `run_agent_concurrent.py <manifest> <task_local_scratch_lib> --reuse-checkpoint <checkpoint> --checkpoint-reuse-policy exact_or_pattern --max-parallel <N>` 或旧式 `--reuse-index <reuse_index.json>`。默认 `--max-parallel` 为 8；若 manifest 的 `worker_execution_mode=coqc_only`，runner 必须禁用 worker `.codex/config.toml` 并生成 coqc-only prompt；`use_rocq_mcp` 不得覆盖 `worker_execution_mode`。runner 会按 `estimated_difficulty_score` / group size 对 proof groups 做 difficulty-first 调度，让慢组更早启动。
   - `validate_and_merge.py <manifest> --output <merged_scratch_manual>`
  - `migrate_helpers_to_lib.py <manifest> --manual-output <migrated_scratch_manual> --lib-output <migrated_task_local_scratch_lib>`；该步骤会收集 `worker_helper_scratch_lib` / merged manual 中相对 seed manual 新增的 helper-suffix `Require Import` 行，并补入 seed / merged prelude 中已有但 `task_local_scratch_lib` 缺少的通用非 case imports；所有迁入 imports 都按 allowlist 审计后写入 `task_local_scratch_lib` 冻结前缀之后、helper lemmas 之前，并在 manifest 中记录 `migrated_helper_imports`
   - `verify_manual_goals.py <manifest>` 在本轮最终确认时使用；若 helper-free manual 因确无可用 compile overlay 而需要等待主 agent 把 `task_local_scratch_lib` 后缀合入 `common_case_formal_lib` 后才能编译，则 verify 阶段只做结构检查并记录 `migrated_manual_compile_deferred_until_main_lib_integration`；正常并发 worker pipeline 应使用 prepare 阶段创建的 canonical `case_deps/` overlay 完成本轮 scratch 验证。若还需主 agent 集成，不要提前删除仍需交接的 migrated manual / `task_local_scratch_lib` artifact。
  - 若 `run_agent_concurrent.py` 因 Codex CLI 缺失、认证失败、transport / backend 不可达或 worker 会话不可恢复而无法产出可用 worker 结果，则应在同一轮记录阻塞证据和已消耗时间后切换到串行 fallback：直接在 proving scratch manual 上推进证明、手动完成 helper migration 到 `task_local_scratch_lib`、并以 `coqc` / `verify` 级别验证最终 scratch 产物。串行 fallback 的每轮 proof search / `coqc` 编译也必须计时；失败的 `coqc`、超时、重新运行和“编译到下一个 witness 才失败”的时间都必须逐条保留。
  - Windows worker 已启动、worker-local manual 和 `_CoqProject` 创建后，必须直接使用生成的 `coqc` 命令继续证明；需要观察 proof state 时，可临时插入 `Show.`, `Show n.`, `Show Existentials.`, `Search`, `Check`, `Print`, `About` 等 Rocq 命令并反复运行 `coqc` / `coqtop`，完成前删除这些调试命令。不得调用 `rocq-mcp`，也不得把未使用 MCP 当成 blocker。
5. 在整个 proving 过程中都保持结构边界：
  - 并发模式下，witness theorem proof 先写在 worker-local `*_proof_manual.v`，再经 merge gate 合并进 scratch `*_proof_manual.v`
  - 串行 fallback 下，witness theorem proof 直接写在 proving scratch `*_proof_manual.v`
  - reusable helper lemmas 在并发模式下写在组内 `worker_helper_scratch_lib`，并由 merge gate 合并进 merged scratch `*_proof_manual.v`；在串行 fallback 下可暂存于 proving scratch `*_proof_manual.v`
   - helper-migration 前 `common_case_formal_lib` 和 `task_local_scratch_lib` 对 worker 均视作只读参考；helper-migration 后 audited helper-suffix imports 与 helper lemmas 只落到 `task_local_scratch_lib` 冻结前缀之后
   - 一个 worker、一个 witness 或一批局部 goals 完成时，不得把 helper lemma 追加到 `common_case_formal_lib`；必须等本轮所有目标 witness 都完成后再由主 agent 批量集成
   - 不在最终 scratch handoff manual 中留下 helper lemmas、helper definitions 或额外 `Axiom`
6. 并发模式下，如果某个 worker 在自己的 `worker_helper_scratch_lib` 中加入 helper lemma，`validate_and_merge.py` 必须检查其已证明、无 `Admitted`、无 forbidden top-level declaration，并在冲突或重复不一致时阻塞合并；worker 不应把 helper lemma 加进 worker manual。若 helper lemma 需要额外库，worker 只能在 `worker_helper_scratch_lib` 中加入最小 `Require Import` / `From ... Require Import` 行；`validate_and_merge.py` 会收集这些 imports 并拒绝 `SimpleC.EE.*` 生成 case imports。随后 `migrate_helpers_to_lib.py` 必须把 audited helper-suffix imports 和 helper lemmas 从 merged manual 移到 `task_local_scratch_lib` 并编译验证 migrated manual / `task_local_scratch_lib`。串行 fallback 下也必须达到同样的最终状态：helper imports / helper lemmas 留在 `task_local_scratch_lib`，handoff manual 只保留 witness proofs。本步骤只是生成批量集成候选，不修改 `common_case_formal_lib`。
7. 若证明推进暴露出 annotation 层或 `annotation_scratch_lib` spec 定义问题，立即停止当前 scratch proving，删除 proving scratch，并建议主 agent 回到 `annotation-filling` / `annotation-checking`。
8. 若证明推进要求改写冻结前缀，要求新增顶层 `Definition` / `Fixpoint` / `Inductive` / `Notation` / `Axiom`，或要求迁入不在 helper import allowlist 内的依赖，立即以 `blocked` 返回，并明确指出阻塞点来自 formal 文件边界，而不是继续堆 proof；如果 helper-migration 后 `task_local_scratch_lib` 无法独立编译，也应返回 `blocked` 并说明依赖问题。任何 `blocked` 返回都必须包含 `blocking_reason`、证据、已尝试路径、受影响 witness/helper/文件和建议回退 phase。
9. 如果主 agent 在 proving 期间运行 symexec，生成了新的正式 `*_proof_manual.v`，或 `common_case_formal_lib` 被改动，则立即删除旧 proving scratch，从最新正式快照重建，再开始新的 proving 轮次。
10. 不要在第一次 proof 尝试后就返回；只有当本轮已经达到 `completed`、`blocked` 或 `stale` 时，才结束本轮 proving。
11. 以 `Subagent Return Report` 的形式，把已经在 scratch 上验证过的 proof 结果、`ready_for_main_proof_manual`（helper-free witness manual）、`ready_for_main_task_local_scratch_lib_update` / `ready_for_main_common_case_formal_lib_append`（`task_local_scratch_lib` 中已迁移且已验证的 helper-suffix imports 与 helper lemmas）、worker reports、`migrated_helper_imports`、checkpoint reuse summary、round checkpoint 路径、`protected_prefix_respected`、集成顺序、stale 风险和 timing 摘要交给主 agent；timing 摘要至少包含本轮总 wall-clock、pipeline 各步骤耗时、每个 worker 或串行 fallback 的耗时、失败重跑耗时、proof/helper activity 耗时、主 agent 等待本 subagent 可计入的起止时间、最慢 witness/helper、慢 `coqc` / 慢 tactic 线索、主要 proof bottleneck 和 timing gaps。若无法精确拆分，必须提供本轮总 elapsed 和 `timing_gap_seconds`，并说明缺口来源；禁止只返回“target passed”或少数命令耗时作为 timing 摘要。若本轮 `elapsed_seconds > 600`，必须提供 `long_duration_reason`，至少说明时间花在 worker 准备、worker 等待、timeout、fallback、反复 coqc、慢 witness/helper、工具失败或人工 proof 分析中的哪些部分；若本轮 `round_outcome = blocked`，必须提供 `blocking_reason`。由主 agent 在所有目标 VC 完成后，把 helper-free manual 与 `task_local_scratch_lib` 后缀作为一个批次正式回填工程文件；当本轮结束或输入 stale 时，删除不再需要的 proving scratch 和 worker workdir，并把 phase 切换建议交回 `verification-orchestrator`。
12. 当前轮次完成或部分完成但不是 annotation-bug / stale 时，应在持久 `round_report_dir/reuse_checkpoints/<round-id>/` 中运行 `checkpoint_round.py <manifest> --output-dir <...> --lib-frozen-prefix-end-line <N>`。checkpoint builder 复用 migrated helper-free manual 与 migrated `task_local_scratch_lib`，构建 `reuse_index.json`，导出只含 solved witness proof script 与 helper payload 的 `partial_proof_packet.json`，并写出 `vc_proving_round_checkpoint.json` 作为下一轮唯一入口。checkpoint 可以包含仍未解决 witness 的 `Admitted.`，但只允许索引 / 导出无 `Admitted.` 的 proof block；JSON packet 在上下文匹配时是 direct reuse candidate 输入，在 mismatch 时是 worker proof-pattern reference 输入，二者都不能替代 Rocq `.v` 文件、`coqc`、merge、helper migration、verify 或 final-check。
