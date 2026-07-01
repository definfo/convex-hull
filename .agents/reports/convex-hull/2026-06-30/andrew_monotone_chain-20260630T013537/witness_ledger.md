## Witness Ledger

| witness_id | category | status | owner | source_goal_version | summary | stale_reason |
| --- | --- | --- | --- | --- | --- | --- |
| cmp_xy_return_wit_1 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Comparator equal x/y branch. |  |
| cmp_xy_return_wit_2 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Comparator equal x, greater y branch. |  |
| cmp_xy_return_wit_3 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Comparator equal x, smaller y branch. |  |
| cmp_xy_return_wit_4 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Comparator greater x branch. |  |
| cmp_xy_return_wit_5 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Comparator smaller x branch. |  |
| cross_prod_safety_wit_1 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Full cross product int safety. |  |
| cross_prod_safety_wit_2 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Product int safety. |  |
| cross_prod_safety_wit_3 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Coordinate subtraction int safety. |  |
| cross_prod_safety_wit_4 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Coordinate subtraction int safety. |  |
| cross_prod_safety_wit_5 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Product int safety. |  |
| cross_prod_safety_wit_6 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Coordinate subtraction int safety. |  |
| cross_prod_safety_wit_7 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Coordinate subtraction int safety. |  |
| cross_prod_return_wit_1 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Return expression equals point_cross_by_value. |  |
| swap_points_return_wit_1 | spatial | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Field stores implement point_swap. |  |
| partition_xy_points_entail_wit_1 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Initial partition scan invariant. |  |
| partition_xy_points_entail_wit_2_1 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Accept branch with swap. |  |
| partition_xy_points_entail_wit_2_2 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Accept branch without swap. |  |
| partition_xy_points_entail_wit_2_3 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Reject branch. |  |
| partition_xy_points_return_wit_1 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Finish partition with final swap. |  |
| partition_xy_points_return_wit_2 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Finish partition without final swap. |  |
| quicksort_xy_points_return_wit_1 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Compose partition and both recursive ranges. |  |
| quicksort_xy_points_return_wit_2 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Right recursion with pivot at left boundary. |  |
| quicksort_xy_points_return_wit_3 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Left recursion with pivot at right boundary. |  |
| quicksort_xy_points_return_wit_4 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Degenerate range sorted. |  |
| andrew_monotone_chain_entail_wit_1 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Initialize lower scan. |  |
| andrew_monotone_chain_entail_wit_2 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Enter lower inner loop and expose point bound. |  |
| andrew_monotone_chain_entail_wit_3 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Lower pop. |  |
| andrew_monotone_chain_entail_wit_4_1 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Lower push from short stack. |  |
| andrew_monotone_chain_entail_wit_4_2 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Lower push after positive cross. |  |
| andrew_monotone_chain_entail_wit_5 | pure | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Lower finished chain initializes upper scan. |  |
| andrew_monotone_chain_entail_wit_6 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Enter upper inner loop and expose capacity. |  |
| andrew_monotone_chain_entail_wit_7 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Upper pop. |  |
| andrew_monotone_chain_entail_wit_8_1 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Upper push at lower boundary. |  |
| andrew_monotone_chain_entail_wit_8_2 | spatial | needs-lemma | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Upper push after positive cross. |  |
| andrew_monotone_chain_entail_wit_9 | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Final complete hull and convex hull bridge. |  |
| andrew_monotone_chain_partial_solve_wit_8_pure | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Lower cross call arguments in bound. |  |
| andrew_monotone_chain_partial_solve_wit_21_pure | pure | proofable | vc-checking-subagent | 65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef | Upper cross call arguments in bound. |  |

