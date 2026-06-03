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
From SimpleC.EE.Applications_human.convex_hull Require Import graham_scan_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.convex_hull.convex_hull_lib.
Local Open Scope sac.

Lemma proof_of_leftdown_return_wit_1 : leftdown_return_wit_1.
Proof.
  pre_process.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y; simpl.
  repeat
    match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    end; lia.
Qed. 

Lemma proof_of_leftdown_return_wit_2 : leftdown_return_wit_2.
Proof.
  pre_process.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y; simpl.
  repeat
    match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    end; lia.
Qed. 

Lemma proof_of_leftdown_return_wit_3 : leftdown_return_wit_3.
Proof.
  pre_process.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y; simpl.
  repeat
    match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    end; lia.
Qed. 

Lemma proof_of_leftdown_return_wit_4 : leftdown_return_wit_4.
Proof.
  pre_process.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y; simpl.
  repeat
    match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    end; lia.
Qed. 

Lemma proof_of_leftdown_return_wit_5 : leftdown_return_wit_5.
Proof.
  pre_process.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y; simpl.
  repeat
    match goal with
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    end; lia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_dot_prod_safety_wit_1 : dot_prod_safety_wit_1.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_safety_wit_2 : dot_prod_safety_wit_2.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_safety_wit_3 : dot_prod_safety_wit_3.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_safety_wit_4 : dot_prod_safety_wit_4.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_safety_wit_5 : dot_prod_safety_wit_5.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_safety_wit_6 : dot_prod_safety_wit_6.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_safety_wit_7 : dot_prod_safety_wit_7.
Proof.
  pre_process; entailer!; unfold point_bound in *; nia.
Qed. 

Lemma proof_of_dot_prod_return_wit_1 : dot_prod_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_6 : cmp_polar_safety_wit_6.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_7 : cmp_polar_safety_wit_7.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_8 : cmp_polar_safety_wit_8.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_9 : cmp_polar_safety_wit_9.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_10 : cmp_polar_safety_wit_10.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_11 : cmp_polar_safety_wit_11.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_safety_wit_12 : cmp_polar_safety_wit_12.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_bound, point_mk, x, y in *; simpl in *; nia.
Qed. 

Lemma proof_of_cmp_polar_entail_wit_2 : cmp_polar_entail_wit_2.
Proof.
  pre_process.
  subst retval.
  entailer!.
  unfold point_colinear.
  rewrite <- point_cross_by_value_point.
  unfold point_mk, x, y in *; simpl in *.
  lia.
Qed. 

Lemma proof_of_cmp_polar_entail_wit_3 : cmp_polar_entail_wit_3.
Proof.
  pre_process.
Qed. 

Lemma proof_of_cmp_polar_return_wit_1 : cmp_polar_return_wit_1.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_2 : cmp_polar_return_wit_2.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_3 : cmp_polar_return_wit_3.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_4 : cmp_polar_return_wit_4.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_5 : cmp_polar_return_wit_5.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_6 : cmp_polar_return_wit_6.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_7 : cmp_polar_return_wit_7.
Proof.
  pre_process; entailer!;
    unfold point_cmp_polar, point_cmp_xy, point_mk, x, y in *; simpl in *;
    repeat
      match goal with
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      end; lia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_8 : cmp_polar_return_wit_8.
Proof.
  pre_process; entailer!.
  unfold point_cmp_polar.
  rewrite point_cross_unfold.
  unfold point_cross_by_value, point_mk, x, y in *; simpl in *.
  repeat
    match goal with
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    end; nia.
Qed. 

Lemma proof_of_cmp_polar_return_wit_9 : cmp_polar_return_wit_9.
Proof.
  pre_process; entailer!.
  unfold point_cmp_polar.
  rewrite point_cross_unfold.
  unfold point_cross_by_value, point_mk, x, y in *; simpl in *.
  repeat
    match goal with
    | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
    | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
    end; nia.
Qed. 

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure : cmp_polar_partial_solve_wit_1_pure.
Proof.
  pre_process; entailer!;
    unfold point_in_bound, point_mk, x, y in *; simpl in *; lia.
Qed. 

Lemma proof_of_build_hull_from_sorted_tail_safety_wit_14 : build_hull_from_sorted_tail_safety_wit_14.
Proof.
  pre_process.
  prop_apply PointArray.undef_seg_valid.
  Intros.
  entailer!; lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_safety_wit_17 : build_hull_from_sorted_tail_safety_wit_17.
Proof.
  pre_process.
  prop_apply PointArray.undef_seg_valid.
  Intros.
  pose proof (Zlength_nonneg (final_hull pivot0 (rev tail_rev))).
  entailer!; lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_2 : build_hull_from_sorted_tail_entail_wit_2.
Proof.
  pre_process.
  rewrite (PointArray.undef_full_unfold hull_pre tail_n_pre nil).
  unfold StorePointAsElement.undefstoreA, undef_point.
  replace (hull_pre + 0 * 8) with hull_pre by lia.
  cancel.
  entailer!.
  lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_3 : build_hull_from_sorted_tail_entail_wit_3.
Proof.
  pre_process.
  replace (scan_hull pivot0 tail_rev (tail_n_pre - 1)) with (pivot0 :: nil).
  2: {
    replace (tail_n_pre - 1) with (Zlength tail_rev - 1) by lia.
    symmetry.
    apply scan_hull_init.
  }
  split_pure_spatial; [cancel | ].
  sep_apply_l_atomic (store_point_fold hull_pre pivot0).
  replace (0 + 1) with 1 by lia.
  sep_apply_r_atomic (PointArray.seg_single hull_pre 0 pivot0).
  unfold StorePointAsElement.storeA.
  replace (hull_pre + 0 * 8) with hull_pre by lia.
  cancel.
  entailer!.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_5 : build_hull_from_sorted_tail_entail_wit_5.
Proof.
  pre_process.
  Exists (stack_of_rev_tail pivot0 tail_rev i).
  entailer!.
  apply stack_suffix_refl.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_6 : build_hull_from_sorted_tail_entail_wit_6.
Proof.
  pre_process.
  assert (Hlen2 : 2 <= Zlength stk_2).
  { unfold stack_norm in H7.
    rewrite normalize_stack_fun_Zlength in H7.
    lia. }
  apply normalize_stack_fun_decompose in Hlen2.
  destruct Hlen2 as [prefix [prev [cur [Heq Hlen]]]].
  assert (Htop_prefix : top - 1 = Zlength prefix).
  { pose proof H7 as Htop_len.
    unfold stack_norm in Htop_len.
    rewrite Heq in Htop_len.
    rewrite Zlength_app in Htop_len.
    rewrite !Zlength_cons, Zlength_nil in Htop_len.
    lia. }
  Exists prefix prev cur stk_2.
  split_pure_spatial.
  - sep_apply_l_atomic (PointArray.full_split_to_missing_i sorted_tail_pre i tail_n tail_rev __default_Point).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic (PointArray.seg_split_to_seg hull_pre 0 (top - 1) (top + 1) (normalize_stack_fun stk_2)).
      * dump_pre_spatial. lia.
      * rewrite Heq.
        replace (top - 1 - 0) with (Zlength prefix) by lia.
        replace (top + 1 - 0) with (top + 1) by lia.
        rewrite (sublist_app_exact1 prefix (prev :: cur :: nil)).
        rewrite (sublist_split_app_r (Zlength prefix) (top + 1) (Zlength prefix) prefix (prev :: cur :: nil)) by lia.
        replace (top + 1 - Zlength prefix) with 2 by lia.
        replace (Zlength prefix - Zlength prefix) with 0 by lia.
        rewrite sublist_self by reflexivity.
        PointArray.ArraySimplify.
        unfold StorePointAsElement.storeA, store_point.
        replace (top - 1 + 1) with top by lia.
        csimpl.
        cancel.
        entailer!.
  - entailer!.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_8 : build_hull_from_sorted_tail_entail_wit_8.
Proof. Admitted. 
Lemma proof_of_build_hull_from_sorted_tail_entail_wit_9_1 : build_hull_from_sorted_tail_entail_wit_9_1.
Proof. Admitted. 
Lemma proof_of_build_hull_from_sorted_tail_entail_wit_9_2 : build_hull_from_sorted_tail_entail_wit_9_2.
Proof. Admitted. 
Lemma proof_of_build_hull_from_sorted_tail_entail_wit_12 : build_hull_from_sorted_tail_entail_wit_12.
Proof. Admitted. 
Lemma proof_of_build_hull_from_sorted_tail_entail_wit_14 : build_hull_from_sorted_tail_entail_wit_14.
Proof. Admitted. 
Lemma proof_of_build_hull_from_sorted_tail_return_wit_1 : build_hull_from_sorted_tail_return_wit_1.
Proof. Admitted. 
Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_1_pure : build_hull_from_sorted_tail_partial_solve_wit_1_pure.
Proof. Admitted. 
Lemma proof_of_swap_points_entail_wit_1 : swap_points_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_points_entail_wit_2 : swap_points_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_swap_points_return_wit_2 : swap_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_1 : partition_polar_points_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_2 : partition_polar_points_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_3 : partition_polar_points_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_4 : partition_polar_points_entail_wit_4.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_5_1 : partition_polar_points_entail_wit_5_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_5_2 : partition_polar_points_entail_wit_5_2.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_5_3 : partition_polar_points_entail_wit_5_3.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_return_wit_1 : partition_polar_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_return_wit_2 : partition_polar_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_1 : quicksort_polar_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_2 : quicksort_polar_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_3 : quicksort_polar_points_return_wit_3.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_4 : quicksort_polar_points_return_wit_4.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_2 : sort_and_build_hull_entail_wit_2.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_3 : sort_and_build_hull_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_6_1 : sort_and_build_hull_entail_wit_6_1.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_6_2 : sort_and_build_hull_entail_wit_6_2.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_7 : sort_and_build_hull_entail_wit_7.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_8 : sort_and_build_hull_entail_wit_8.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_9 : sort_and_build_hull_entail_wit_9.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_10 : sort_and_build_hull_entail_wit_10.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_11 : sort_and_build_hull_entail_wit_11.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_entail_wit_12 : sort_and_build_hull_entail_wit_12.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_return_wit_1 : sort_and_build_hull_return_wit_1.
Proof. Admitted. 

Lemma proof_of_sort_and_build_hull_partial_solve_wit_5_pure : sort_and_build_hull_partial_solve_wit_5_pure.
Proof. Admitted. 

