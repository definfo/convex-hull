# 自然语言证明分析指南

## 目标

`vc-checking-subagent` 的自然语言证明不是给 `vc-proving` 的一句提示，而是一个可审计的 proof contract。它必须在进入 `vc-proving` 之前说明：

1. 当前 VC 的 `P |-- Q` 是否语义成立。
2. 若成立，`Q` 中每个空间资源、纯命题和存在 witness 如何从 `P` 构造。
3. 若需要 helper lemma，lemma 的数学陈述、来源边界、每个 premise 的 discharge 依据，以及它属于哪个 proof group。
4. 若不成立，缺口属于 C annotation、`common_case_formal_lib` spec、冻结版本 stale，还是 witness 结构本身。

## 先读什么

1. 本轮 delegation ticket：确认 `target_witnesses`、`source_goal_version`、`common_case_formal_lib` 冻结信息、report 路径和 timing 要求。
2. `*_goal.v`：只读目标 witness 的 theorem 展开形状，不修改生成文件。
3. 当前 case 的 `common_case_formal_lib`：区分 annotation-approved spec 定义、已存在 helper lemma 和冻结前缀后的 helper 后缀。
4. `*_proof_manual.v`：只看已有 witness proof 的局部风格，不能把 helper lemma 写进正式 manual。
5. 参考 Rocq 风格：优先参考 `SeparationLogic/examples/LLM_bench` 和 `QCP_demos_LLM` 中已经完成的 predicate-first 证明；不要参考 `QCP_demos_human`。

## 从 Rocq 证明反推自然语言 proof pattern

LLM-friendly 的 Rocq 证明通常有稳定结构。自然语言分析应把这些结构提前说清楚。

1. 空间资源阶段：`pre_process` 后识别左侧数组段、全数组、结构谓词和右侧要求。若证明会用 `cancel`、`sep_apply`、`IntArray.*_split*` 或 `undef_seg_empty`，自然语言里要写出“哪个资源被保留、哪个资源被拆分、拆分边界为何满足”。例如 sliding window 初始化会把 `out` 的 `undef_full` 拆成 prefix seg 与剩余 undef seg，这需要 `0 <= 0 <= n - k + 1` 等边界。
2. 纯命题阶段：说明 `split_pures` 后每个纯目标来自哪里。不要写“由 invariant 显然”；要写成“展开 `SWMQueueState` 得到 `Hvalid/Hinc/Hdec/Hcover`，目标中的 index bound 由 `Hvalid pos` 和循环 guard 经 `lia` 得到”。
3. 数学 spec 阶段：对 `MaxMin`、reachability、DP table、queue coverage、subsequence、window maximum 等抽象谓词，先说明谓词含义，再说明当前 VC 需要的是 introduction、preservation、completion 还是 contradiction。
4. Helper lemma 阶段：如果现有证明会在 Rocq 中 `eapply SomeLemma`，自然语言中必须提前列出 `SomeLemma` 的结论形状和全部 premise。若 lemma 尚不存在，只能列为 `candidate_lib_lemmas`，后续由 `vc-proving` worker 在 `worker_helper_scratch_lib` 证明并迁入 `task_local_scratch_lib`。
5. 失败定位阶段：若某个目标需要“当前写入后的状态仍满足旧 progress predicate”，或者需要修改冻结前缀中的 spec 才能成立，这不是 tactic 问题。必须返回 `annotation-bug` 或 `blocked`，并给出具体冲突 witness。

## 单个 witness 的分析模板

每个 witness 至少输出以下字段。字段可以是 markdown 小节，也可以进入本轮 `vc_checking_informal_proof_report.md` / group plan JSON。

```text
witness_id:
judgment: proofable | needs-lemma | annotation-bug | blocked
vc_shape:
  pre_spatial:
  pre_pure:
  pre_exists:
  post_spatial:
  post_pure:
  post_exists:
witness_instantiation:
space_plan:
pure_plan:
used_existing_lemmas:
candidate_lib_lemmas:
premise_discharge:
failure_signal:
recommended_next_phase:
proof_group_candidate:
grouping_reason:
timing_seconds:
```

`vc_shape` 必须把 `P` 和 `Q` 分开写。`witness_instantiation` 要说明右侧 `EX` 的值来自旧 logical list、`replace_Znth`、`sublist`、`app ... :: nil`，还是某个 loop variable。`premise_discharge` 必须逐项对应到当前 VC 前条件，不允许省略。

## Lemma 审计标准

对每个 lemma，按下面格式写：

```text
lemma_name:
source: existing-library | current-case-lib | candidate_lib_lemmas
statement_shape:
used_by_witnesses:
premises:
  - premise:
    discharged_by:
    needs_unfold:
    arithmetic:
    spatial_resource:
helper_destination:
```

`source = candidate_lib_lemmas` 时，`helper_destination` 必须是 `worker_helper_scratch_lib -> task_local_scratch_lib helper suffix -> common_case_formal_lib after all VC complete`。不得建议在 `vc-checking` 或单个 witness 证明期间直接改 `common_case_formal_lib`。

## 分组原则

`witness_group_plan` 应按证明模式分组，而不是按 witness 编号机械分组。

- 同一组应共享核心 proof pattern：相同 invariant 展开、相同 helper family、相同空间 frame 结构或相同数学 recurrence。
- 每组指定一个 representative witness，并说明其他成员只差哪些局部条件。
- 可使用的组名应表达证明内容，例如 `dp_zero_and_copy_semantics`、`queue_drop_pending_pop`、`queue_push_current`、`final_answer_bridge`、`pure_bounds_safety`。
- 如果某个 witness 被判为 `annotation-bug`，不能把它混入 proving group；下游 `vc-proving` 输入必须失效，主流程应回到 annotation。

## 与工作流的连接

1. `goal-frozen` 后，主 agent 把最新 goal/lib/manual hash 和冻结前缀写入 ticket。
2. `vc-checking-subagent` 读取 ticket，按本指南为每个 witness 形成 informal proof 或失败诊断。
3. 若有 `annotation-bug`，返回主 agent；主 agent 按 orchestrator 写 re-entry brief，删除 stale proving scratch，重新进入 annotation。
4. 若所有 witness 都是 `proofable` 或 `needs-lemma`，返回 `witness_group_plan`、`candidate_lib_lemmas` 和 timing 摘要。
5. `vc-proving-subagent` 只消费这些 group：worker 在自己的 `worker_helper_scratch_lib` 证明候选 helper，在 worker-local manual 证明 witness。
6. helper migration 后，主 agent 只能在所有目标 witness 完成时一次性把 helper-free manual 和 `task_local_scratch_lib` 后缀集成回正式文件。

## 反例和红线

- 不要把 C 循环翻译成 Rocq 函数后声称 VC 可证；spec 应描述数学性质，如最大值、可达性、prefix/table relation、queue coverage。
- 不要把 `lia` 当作 proof plan。必须说明 `lia` 使用了哪些 bound、guard、length 等事实。
- 不要用“现有 invariant 足够”代替展开分析。要写出 invariant 的具体 conjunct 和实例化参数。
- 不要把缺失 lemma 直接写入 `common_case_formal_lib` 冻结前缀。
- 不要在目标 stale、hash 不匹配、manual skeleton 与 goal witness 不一致时继续分组证明。

## 简短示例

`sliding_window_maximum` 的队列 VC 可按如下方式分析：

- `P` 提供 `SWMQueueState l q_l head tail i k`、数组 frame 和循环 guard。
- `Q` 要求 drop-loop 或 pending state，同时保留相同数组 frame。
- 空间资源通过 `repeat cancel` 保留；纯目标通过展开 `SWMQueueState` 得到 entries-valid、index-increasing、value-decreasing、coverage 和 front-max。
- 若从 after-drop 转为 pending state，需要 candidate/existing lemma `SWMQueueAfterDrop_to_PendingState`；premise 是 `SWMQueueAfterDrop ...` 和 `i < Zlength l`，前者来自 loop invariant，后者来自 loop guard。
- 如果需要弹出被当前值支配的 tail，则 lemma 属于 queue pop helper family，前提包括 `head < tail`、last value dominated、pending state；这些必须分别由 branch condition、数组读取比较和 invariant 展开得到。
