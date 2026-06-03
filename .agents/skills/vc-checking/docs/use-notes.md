# 使用注意

这个文件用于说明应用 `vc-checking` 时必须优先遵守的细节。

- phase、ledger 状态、delegation 和 stale 规则统一以 `verification-orchestrator` 为准；本文件只保留 VC 分诊相关硬规则。
- 只修改对应的 manual proof、annotation 或必要的辅助引理文件；不要修改生成的 `goal` / `proof_auto` / `goal_check` 文件。
- 在判断 VC 时，先分析其是否语义可证，再决定是修 annotation 还是修 proof。
- 当结论是 `needs-lemma` 时，指的是应先由 vc-proving proof group worker 在 `worker_helper_scratch_lib` 中证明，再由 helper-migration 迁入 `task_local_scratch_lib` 后缀的 proved helper lemma；不是修改 `common_case_formal_lib` 冻结前缀。
- `vc-checking` 返回时应给出 `witness_group_plan`：按自然语言证明模式把可共享 proof pattern / helper 的 witness 分到同一 proof group，供 `vc-proving` 并行消费。
- 每次 annotation 改动后，都必须重新生成并重新检查 VC。
- annotation 中只能使用完整的 `Assert` 或 `Inv Assert`。
- 禁止使用黑盒 entailment 自动化 tactic。
- 不要通过导入额外证明理论模块来绕过项目既有证明风格。
- 如果发现 `goal.v` 已刷新，但当前看到的 VC 与预期不一致，应先检查目标文件、编译路径和生成文件是否对应同一个 case。
