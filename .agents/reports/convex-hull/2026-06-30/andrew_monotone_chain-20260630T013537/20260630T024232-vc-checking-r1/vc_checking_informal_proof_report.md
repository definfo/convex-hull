## VC Informal Proof Provability Report

- status: passed
- source_goal_version: goal sha256:65bab7a689fe5208cdd279ea7d648e644cfd9b789803968fbf6141aa099a25ef
- checked_witness_scope: all 37 admitted witness obligations in convex-hull/ConvexHull/andrew_monotone_chain_proof_manual.v
- summary: all witnesses are semantically provable under the current annotations. No annotation-bug witness was found. Several VCs require helper lemmas that must be proved by vc-proving workers in worker_helper_scratch_lib and migrated through task_local_scratch_lib helper suffix before common_case_formal_lib integration.
- candidate_lib_lemmas: C1 point_list_not_all_same_of_points_not_all_same_permutation; C2 point_xy_partition_scan_inv_accept_swap; C3 point_xy_partition_scan_inv_accept_noswap; C4 point_xy_partition_scan_inv_reject_step; C5 point_xy_partition_scan_inv_finish_swap; C6 point_xy_partition_scan_inv_finish_noswap; C7 point_xy_sorted_range_degenerate; C8 point_xy_sorted_range_from_left_boundary; C9 point_xy_sorted_range_from_right_boundary; C10 point_xy_sorted_range_partition_merge; C11 andrew_lower_scan_inv_init; C12 andrew_lower_scan_inv_pop; C13 andrew_lower_scan_inv_push; C14 andrew_upper_scan_inv_init_from_lower_finished; C15 andrew_upper_scan_inv_pop; C16 andrew_upper_scan_inv_push. Destination for every candidate: worker_helper_scratch_lib -> task_local_scratch_lib helper suffix -> common_case_formal_lib after all VC complete.
- existing_library_lemmas: point_cmp_leftdown_eq_cmp_xy; point_cmp_xy_eq; point_cmp_xy_x_lt; point_cmp_xy_x_gt; point_cmp_xy_y_lt; point_cmp_xy_y_gt; point_mk_eta; point_eq_by_xy; Point_Order.point_bound; Point_Order.point_bound_sub; points_in_bound_Znth; points_in_bound_Znth_point_mk; points_in_bound_snoc_Znth; points_in_bound_point_swap; Zlength_point_swap; point_swap_permutation; point_same_outside_range_refl; point_same_outside_range_trans; point_same_outside_range_weaken; point_same_outside_range_point_swap_inside; point_swap_Znth_*; point_array_seg_snoc_store_undef; point_array_seg_pop_tail; point_array_store_missing_merge_to_full; store_point_fold; is_convex_hull_base_permutation.
- failed_witnesses: none
- required_annotation_rework: none
- required_lib_rework: helper lemmas only, through vc-proving helper migration
- ready_for_vc_proving: yes

| witness_id | judgment | informal_proof | used_lemmas | lemma_sources | premise_discharge | missing_or_unjustified_premises | next_action |
| --- | --- | --- | --- | --- | --- | --- | --- |
| cmp_xy_return_wit_1 | proofable | Equal x/y branch proves return 0 equals point_cmp_leftdown. | comparator lemmas | existing-library | branch inequalities yield equality by antisymmetry; emp frame unchanged | none | prove directly |
| cmp_xy_return_wit_2 | proofable | Equal x and greater y branch proves return 1. | comparator lemmas | existing-library | branch facts give x equality and y greater | none | prove directly |
| cmp_xy_return_wit_3 | proofable | Equal x and smaller y branch proves return -1. | comparator lemmas | existing-library | branch facts give x equality and y less | none | prove directly |
| cmp_xy_return_wit_4 | proofable | Greater x branch proves return 1. | comparator lemmas | existing-library | branch fact gives x greater | none | prove directly |
| cmp_xy_return_wit_5 | proofable | Smaller x branch proves return -1. | comparator lemmas | existing-library | branch fact gives x smaller | none | prove directly |
| cross_prod_safety_wit_1 | proofable | Full cross product fits signed int. | point_bound arithmetic | existing-library | point_in_bound facts give coordinate bounds | none | prove directly |
| cross_prod_safety_wit_2 | proofable | Product fits signed int. | point_bound arithmetic | existing-library | coordinate bounds imply bounded differences | none | prove directly |
| cross_prod_safety_wit_3 | proofable | c_x-a_x fits signed int. | point_bound arithmetic | existing-library | coordinate bounds imply bounded subtraction | none | prove directly |
| cross_prod_safety_wit_4 | proofable | b_y-a_y fits signed int. | point_bound arithmetic | existing-library | coordinate bounds imply bounded subtraction | none | prove directly |
| cross_prod_safety_wit_5 | proofable | Product fits signed int. | point_bound arithmetic | existing-library | coordinate bounds imply bounded differences | none | prove directly |
| cross_prod_safety_wit_6 | proofable | c_y-a_y fits signed int. | point_bound arithmetic | existing-library | coordinate bounds imply bounded subtraction | none | prove directly |
| cross_prod_safety_wit_7 | proofable | b_x-a_x fits signed int. | point_bound arithmetic | existing-library | coordinate bounds imply bounded subtraction | none | prove directly |
| cross_prod_return_wit_1 | proofable | Expression equals point_cross_by_value. | point_cross_by_value | current-case-lib | definition unfolds to same arithmetic | none | prove directly |
| swap_points_return_wit_1 | proofable | Nested field stores implement point_swap and preserve full array. | replace_Znth, point_swap lemmas | existing-library | index bounds and i <> j from VC precondition | none | prove directly |
| partition_xy_points_entail_wit_1 | proofable | Initialize partition scan invariant. | point_same_outside_range_refl, points_in_bound_Znth_point_mk | existing-library | empty ranges are vacuous; pivot fields from read point | none | prove directly |
| partition_xy_points_entail_wit_2_1 | needs-lemma | Accept branch with swap preserves scan invariant. | C2, swap/bound lemmas | candidate-lib + existing-library | retval <= 0, swap indices in range, pivot at high preserved because j < high | none beyond C2 | prove C2 |
| partition_xy_points_entail_wit_2_2 | needs-lemma | Accept branch without swap extends left partition. | C3 | candidate-lib | i+1=j and retval <= 0 from branch/precondition | none beyond C3 | prove C3 |
| partition_xy_points_entail_wit_2_3 | needs-lemma | Reject branch advances j and preserves scan invariant. | C4 | candidate-lib | retval > 0 from branch; current point enters right scan segment | none beyond C4 | prove C4 |
| partition_xy_points_return_wit_1 | needs-lemma | Final pivot swap converts scan invariant into partitioned-at. | C5, swap lemmas | candidate-lib + existing-library | loop exit gives j=high; swap bounds from invariant | none beyond C5 | prove C5 |
| partition_xy_points_return_wit_2 | needs-lemma | No-swap finish converts scan invariant directly. | C6 | candidate-lib | i+1=high and j=high from precondition | none beyond C6 | prove C6 |
| quicksort_xy_points_return_wit_1 | needs-lemma | Partition plus both recursive sorted ranges imply whole sorted range. | C10 | candidate-lib | recursive sortedness and partitioned-at facts from VC precondition | none beyond C10 | prove C10 |
| quicksort_xy_points_return_wit_2 | needs-lemma | Right recursion plus pivot at left boundary implies sorted range. | C9 | candidate-lib | right sortedness and partitioned-at facts from precondition | none beyond C9 | prove C9 |
| quicksort_xy_points_return_wit_3 | needs-lemma | Left recursion plus pivot at right boundary implies sorted range. | C8 | candidate-lib | left sortedness and partitioned-at facts from precondition | none beyond C8 | prove C8 |
| quicksort_xy_points_return_wit_4 | needs-lemma | Base case left>=right yields degenerate sorted range. | C7 | candidate-lib | range degeneracy from precondition | none beyond C7 | prove C7 |
| andrew_monotone_chain_entail_wit_1 | needs-lemma | Initialize lower scan from sorted array and empty hull segment. | C1, C11, undef facts | candidate-lib + existing-library | sortedness/permutation/not-all-same from function pre and quicksort result | none beyond C1/C11 | prove C1/C11 |
| andrew_monotone_chain_entail_wit_2 | proofable | Enter lower inner loop and expose current point bound. | points_in_bound_Znth | existing-library | 0<=i<n, Zlength=n, points_in_bound from invariant | none | prove directly |
| andrew_monotone_chain_entail_wit_3 | needs-lemma | Lower pop on non-left turn preserves lower invariant. | C12, point_array_seg_pop_tail | candidate-lib + existing-library | retval <= 0 and k>=2 from loop branch/invariant | none beyond C12 | prove C12 |
| andrew_monotone_chain_entail_wit_4_1 | needs-lemma | Lower push when stack length <2 preserves lower invariant. | C13, store_point_fold, point_array_seg_snoc_store_undef | candidate-lib + existing-library | short-stack append-ready case and spatial snoc resources from precondition | none beyond C13 | prove C13 |
| andrew_monotone_chain_entail_wit_4_2 | needs-lemma | Lower push after positive cross preserves lower invariant. | C13, cross/value lemmas, spatial snoc | candidate-lib + existing-library | retval>0 gives left turn; storage resources from precondition | none beyond C13 | prove C13 |
| andrew_monotone_chain_entail_wit_5 | needs-lemma | Finished lower chain initializes upper scan. | C14 | candidate-lib | lower final clause and 2<=k from precondition | none beyond C14 | prove C14 |
| andrew_monotone_chain_entail_wit_6 | proofable | Enter upper inner loop and expose point bound/capacity. | points_in_bound_Znth | existing-library | unfold upper invariant/capacity and use i+1>=1 | none | prove directly |
| andrew_monotone_chain_entail_wit_7 | needs-lemma | Upper pop on non-left turn preserves upper invariant. | C15, point_array_seg_pop_tail | candidate-lib + existing-library | retval<=0 and k>lower_n from branch/invariant | none beyond C15 | prove C15 |
| andrew_monotone_chain_entail_wit_8_1 | needs-lemma | Upper push at lower boundary preserves upper invariant. | C16, spatial snoc | candidate-lib + existing-library | k<=lower_n and lower_n<=k from branch/precondition | none beyond C16 | prove C16 |
| andrew_monotone_chain_entail_wit_8_2 | needs-lemma | Upper push after positive cross preserves upper invariant. | C16, cross/value lemmas, spatial snoc | candidate-lib + existing-library | retval>0 gives append-ready turn condition | none beyond C16 | prove C16 |
| andrew_monotone_chain_entail_wit_9 | proofable | Final upper invariant yields complete hull shape and convex hull over original base. | is_convex_hull_base_permutation | existing-library/current-case-lib | i<1 and 0<=i+1 imply read<=1; invariant yields complete hull shape; permutation bridges base | none | prove directly |
| andrew_monotone_chain_partial_solve_wit_8_pure | proofable | Lower cross call arguments are in point_bound. | points_in_bound_Znth | existing-library | lower invariant has points_in_bound lower and top=Zlength lower with k>=2 | none | prove directly |
| andrew_monotone_chain_partial_solve_wit_21_pure | proofable | Upper cross call arguments are in point_bound. | points_in_bound_Znth | existing-library | upper invariant has points_in_bound hull_cur and top=Zlength hull_cur with k>lower_n>=2 | none | prove directly |

### Witness Group Plan

| proof_group_id | members | representative_witness | natural_language_proof_pattern | shared_helper_candidates | proving_hints | grouping_confidence |
| --- | --- | --- | --- | --- | --- | --- |
| cmp_xy_returns | cmp_xy_return_wit_1..5 | cmp_xy_return_wit_1 | unfold comparator and use branch inequalities to prove exact return | none | destruct comparison or use existing cmp lemmas | high |
| cross_prod_arithmetic | cross_prod_safety_wit_1..7; cross_prod_return_wit_1 | cross_prod_safety_wit_1 | bounded coordinates imply int safety; return is definitional | none | unfold point_bound; arithmetic by nia/lia | high |
| swap_points_model | swap_points_return_wit_1 | swap_points_return_wit_1 | nested field stores normalize to point_swap | none | rewrite replace_Znth and use point_eq_by_xy | high |
| partition_scan | partition_xy_points_entail_wit_1; partition_xy_points_entail_wit_2_1; partition_xy_points_entail_wit_2_2; partition_xy_points_entail_wit_2_3 | partition_xy_points_entail_wit_2_1 | establish and preserve partition scan invariant across accept/reject branches | C2; C3; C4 | unfold point_xy_partition_scan_inv; use swap lookup lemmas | high |
| partition_finish | partition_xy_points_return_wit_1; partition_xy_points_return_wit_2 | partition_xy_points_return_wit_1 | convert scan invariant at loop exit into point_xy_partitioned_at | C5; C6 | derive j=high; split left/right sublists | high |
| quicksort_xy_composition | quicksort_xy_points_return_wit_1..4 | quicksort_xy_points_return_wit_1 | compose partition result and recursive sorted ranges | C7; C8; C9; C10 | use permutation transitivity and same-outside weaken/trans | high |
| andrew_lower_scan | andrew_monotone_chain_entail_wit_1..5; andrew_monotone_chain_partial_solve_wit_8_pure | andrew_monotone_chain_entail_wit_3 | initialize, pop, push, and finish lower scan invariant | C1; C11; C12; C13; C14 | use array pop/snoc spatial lemmas; unfold scan predicates | medium-high |
| andrew_upper_scan | andrew_monotone_chain_entail_wit_6..9; andrew_monotone_chain_partial_solve_wit_21_pure | andrew_monotone_chain_entail_wit_7 | expose upper loop premises, pop/push upper scan, finish complete hull | C15; C16 | final uses read<=1; convexity over base via permutation lemma | medium-high |

