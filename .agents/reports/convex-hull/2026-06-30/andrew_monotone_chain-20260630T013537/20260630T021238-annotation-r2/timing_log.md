## Timing Log

| phase | command_or_step | elapsed_seconds | result | notes |
| --- | --- | --- | --- | --- |
| annotation-r1 | subagent round | 1827 | blocked | qcp-mcp file-end yes; scratch-lib coqc blocked by stale `.vo` dependencies |
| annotation-r2-prep | `make -B -C SeparationLogic/ConvexHull -f convexhull-coq.mk` | 17.08 | passed | main-owned rebuild of stale ConvexHull dependencies |
| annotation-r2 | delegation ticket prepared | n/a | completed | fresh subagent round required |
| annotation-r2 | annotation gate validation script | n/a | passed | `validate_annotation_gate.py` report-field gate passed |
| annotation-r2 | `make andrew-symexec` | 2.34 | passed | generated official Andrew goal/auto/manual/goal_check files |
| annotation-r2 | `make andrew-build` | 25.32 | passed | compiled generated Andrew goal/check stack with current admitted stubs |
| annotation-r2 | official hash check | <1 | completed | C/lib/header/strategy hashes matched ticket |
| annotation-r2 | fresh scratch setup | <1 | completed | copied official C and lib to owned `.tmp` paths |
| annotation-r2 | scratch-only include workaround | <1 | completed | qcp loader path only; not a candidate patch |
| annotation-r2 | qcp-mcp load scratch C | 5.55 | passed | parsed scratch successfully |
| annotation-r2 | qcp-mcp symbolic to line 330 | 5.26 | passed | file-end success; loaded `point_array` |
| annotation-r2 | qcp-mcp close | 2.70 | passed | session closed |
| annotation-r2 | scratch lib coqc gate | 8.97 | passed | official ConvexHull dependency rebuild resolved r1 blocker |
| annotation-r2 | scratch cleanup | <1 | completed | deleted scratch C/lib and generated scratch Coq byproducts |

| phase | activity_kind | elapsed_seconds | source | notes |
| --- | --- | --- | --- | --- |
| annotation-r2 | subagent-wait | pending | wall-clock | starts when annotation-subagent is launched |
| annotation-r2 | integration-edit | n/a | wall-clock | no C/lib source integration; generated files refreshed by symexec |
| annotation-r2 | manual-analysis | not separately stopwatched | wall-clock | spec-first and predicate-first review |
| annotation-r2 | report-writing | not separately stopwatched | wall-clock | persistent r2 reports |

## Timing Gaps

- Exact main-thread report editing and orchestration time was not stopwatched per activity.
- Exact subagent review/report segmentation was not fully stopwatched beyond command wall times reported above.
