Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.convex_hull Require Import andrew_monotone_chain_goal.
From SimpleC.EE.convex_hull Require Import andrew_monotone_chain_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.convex_hull.convex_hull_lib.
Local Open Scope sac.

From VCWorker Require Import worker_helper_scratch_lib.
Lemma proof_of_cmp_xy_return_wit_1_split_goal_1 : cmp_xy_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_1 : cmp_xy_return_wit_1.
Proof. Admitted. 

Lemma proof_of_cmp_xy_return_wit_2_split_goal_1 : cmp_xy_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_2 : cmp_xy_return_wit_2.
Proof. Admitted. 

Lemma proof_of_cmp_xy_return_wit_3_split_goal_1 : cmp_xy_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_3 : cmp_xy_return_wit_3.
Proof. Admitted. 

Lemma proof_of_cmp_xy_return_wit_4_split_goal_1 : cmp_xy_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_4 : cmp_xy_return_wit_4.
Proof. Admitted. 

Lemma proof_of_cmp_xy_return_wit_5_split_goal_1 : cmp_xy_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_5 : cmp_xy_return_wit_5.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_1_split_goal_1 : cross_prod_safety_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_2 : cross_prod_safety_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_2_split_goal_1 : cross_prod_safety_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_2 : cross_prod_safety_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_3_split_goal_1 : cross_prod_safety_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_2 : cross_prod_safety_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_4_split_goal_1 : cross_prod_safety_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_2 : cross_prod_safety_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_5_split_goal_1 : cross_prod_safety_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_2 : cross_prod_safety_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_6_split_goal_1 : cross_prod_safety_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_2 : cross_prod_safety_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof. Admitted. 

Lemma proof_of_cross_prod_safety_wit_7_split_goal_1 : cross_prod_safety_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_2 : cross_prod_safety_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof. Admitted. 

Lemma proof_of_cross_prod_return_wit_1_split_goal_1 : cross_prod_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  unfold swap_points_return_wit_1; try left.
  intros.
  entailer!.
  rewrite (Znth_indep pts_l i_pre __default_Point default_point) by lia.
  rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  unfold point_swap.
  repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
  repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
  repeat rewrite replace_Znth_Znth by lia.
  repeat rewrite replace_Znth_twice by (rewrite ?Zlength_replace_Znth; lia).
  rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  destruct (Znth i_pre pts_l default_point).
  destruct (Znth j_pre pts_l default_point).
  simpl.
  apply derivable1_refl.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_1 : partition_xy_points_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_2 : partition_xy_points_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_3 : partition_xy_points_entail_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_4 : partition_xy_points_entail_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_1 : partition_xy_points_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_1 : partition_xy_points_entail_wit_2_1_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_2 : partition_xy_points_entail_wit_2_1_split_goal_2.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_3 : partition_xy_points_entail_wit_2_1_split_goal_3.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_4 : partition_xy_points_entail_wit_2_1_split_goal_4.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_5 : partition_xy_points_entail_wit_2_1_split_goal_5.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_1 : partition_xy_points_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_partition_xy_points_entail_wit_2_2_split_goal_1 : partition_xy_points_entail_wit_2_2_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_partition_xy_points_entail_wit_2_3_split_goal_1 : partition_xy_points_entail_wit_2_3_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Proof. Admitted. 

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_1 : partition_xy_points_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_2 : partition_xy_points_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_3 : partition_xy_points_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_4 : partition_xy_points_return_wit_1_split_goal_4.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_5 : partition_xy_points_return_wit_1_split_goal_5.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_1 : partition_xy_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_1 : partition_xy_points_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_2 : partition_xy_points_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_3 : partition_xy_points_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_1 : quicksort_xy_points_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_2 : quicksort_xy_points_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_3 : quicksort_xy_points_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_1 : quicksort_xy_points_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_2 : quicksort_xy_points_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_3 : quicksort_xy_points_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_1 : quicksort_xy_points_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_2 : quicksort_xy_points_return_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_3 : quicksort_xy_points_return_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Proof. Admitted. 

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_1 : quicksort_xy_points_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_2 : quicksort_xy_points_return_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_3 : quicksort_xy_points_return_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_1 : andrew_monotone_chain_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_2 : andrew_monotone_chain_entail_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_spatial : andrew_monotone_chain_entail_wit_1_split_goal_spatial.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_1 : andrew_monotone_chain_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_2_split_goal_1 : andrew_monotone_chain_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_2_split_goal_spatial : andrew_monotone_chain_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_2 : andrew_monotone_chain_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_3 : andrew_monotone_chain_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_4_1 : andrew_monotone_chain_entail_wit_4_1.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_4_2 : andrew_monotone_chain_entail_wit_4_2.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_5_split_goal_1 : andrew_monotone_chain_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_5_split_goal_2 : andrew_monotone_chain_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_5_split_goal_spatial : andrew_monotone_chain_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_5 : andrew_monotone_chain_entail_wit_5.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_6_split_goal_1 : andrew_monotone_chain_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_6_split_goal_2 : andrew_monotone_chain_entail_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_6_split_goal_spatial : andrew_monotone_chain_entail_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_6 : andrew_monotone_chain_entail_wit_6.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_7 : andrew_monotone_chain_entail_wit_7.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_8_1 : andrew_monotone_chain_entail_wit_8_1.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_8_2 : andrew_monotone_chain_entail_wit_8_2.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_entail_wit_9_split_goal_1 : andrew_monotone_chain_entail_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_9_split_goal_2 : andrew_monotone_chain_entail_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_9_split_goal_spatial : andrew_monotone_chain_entail_wit_9_split_goal_spatial.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_entail_wit_9 : andrew_monotone_chain_entail_wit_9.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_1 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_2 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_3 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_4 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_5 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_5.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_6 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_6.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_7 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_7.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_8 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_8.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_9 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_9.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_10 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_10.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_11 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_11.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_12 : andrew_monotone_chain_partial_solve_wit_8_pure_split_goal_12.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_8_pure : andrew_monotone_chain_partial_solve_wit_8_pure.
Proof. Admitted. 

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_1 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_1.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_2 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_3 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_3.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_4 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_4.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_5 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_5.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_6 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_6.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_7 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_7.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_8 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_8.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_9 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_9.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_10 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_10.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_11 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_11.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_12 : andrew_monotone_chain_partial_solve_wit_21_pure_split_goal_12.
Proof. Abort.

Lemma proof_of_andrew_monotone_chain_partial_solve_wit_21_pure : andrew_monotone_chain_partial_solve_wit_21_pure.
Proof. Admitted. 
