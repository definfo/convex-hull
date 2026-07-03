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
Require Import SimpleC.EE.QCP_demos_LLM.sll_merge_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

Lemma proof_of_cmp_xy_return_wit_1_split_goal_1 : cmp_xy_return_wit_1_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [lia |].
  entailer!.
Qed.

Lemma proof_of_cmp_xy_return_wit_1 : cmp_xy_return_wit_1.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [lia |].
  entailer!.
Qed.

Lemma proof_of_cmp_xy_return_wit_2_split_goal_1 : cmp_xy_return_wit_2_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_2 : cmp_xy_return_wit_2.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [lia |].
  destruct (Z_gt_dec a_y_pre b_y_pre) as [Hygt | Hygt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_3_split_goal_1 : cmp_xy_return_wit_3_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_3 : cmp_xy_return_wit_3.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [lia |].
  destruct (Z_lt_dec a_y_pre b_y_pre) as [Hylt | Hylt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_4_split_goal_1 : cmp_xy_return_wit_4_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_4 : cmp_xy_return_wit_4.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [lia |].
  destruct (Z_gt_dec a_x_pre b_x_pre) as [Hxgt | Hxgt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_5_split_goal_1 : cmp_xy_return_wit_5_split_goal_1.
Proof.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [entailer! | lia].
Qed.

Lemma proof_of_cmp_xy_return_wit_5 : cmp_xy_return_wit_5.
Proof.
  left.
  pre_process.
  unfold point_cmp_leftdown.
  simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre) as [Hxlt | Hxlt]; [entailer! | lia].
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_1 : cross_prod_safety_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_2 : cross_prod_safety_wit_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_2_split_goal_1 : cross_prod_safety_wit_2_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_2 : cross_prod_safety_wit_2_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_3_split_goal_1 : cross_prod_safety_wit_3_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_2 : cross_prod_safety_wit_3_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_4_split_goal_1 : cross_prod_safety_wit_4_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_2 : cross_prod_safety_wit_4_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_5_split_goal_1 : cross_prod_safety_wit_5_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_2 : cross_prod_safety_wit_5_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_6_split_goal_1 : cross_prod_safety_wit_6_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_2 : cross_prod_safety_wit_6_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_safety_wit_7_split_goal_1 : cross_prod_safety_wit_7_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_2 : cross_prod_safety_wit_7_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_bound, Point_Order.point_bound in *.
  nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  pre_process.
  left.
  intros.
  split_pures; dump_pre_spatial;
    unfold point_bound, Point_Order.point_bound in *; nia.
Qed. 

Lemma proof_of_cross_prod_return_wit_1_split_goal_1 : cross_prod_return_wit_1_split_goal_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  pre_process.
  left.
  intros.
  pre_process.
Qed. 

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_swap.
  repeat rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
  repeat rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
  repeat rewrite replace_Znth_twice by (repeat rewrite Zlength_replace_Znth; lia).
  repeat rewrite (Znth_indep pts_l i_pre __default_Point default_point) by lia.
  repeat rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
  simpl.
  replace (point_mk (Znth i_pre pts_l default_point).(x)
                    (Znth i_pre pts_l default_point).(y))
    with (Znth i_pre pts_l default_point)
    by (apply point_eq_by_xy; reflexivity).
  replace (point_mk (Znth j_pre pts_l default_point).(x)
                    (Znth j_pre pts_l default_point).(y))
    with (Znth j_pre pts_l default_point)
    by (apply point_eq_by_xy; reflexivity).
  reflexivity.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  left.
  pre_process.
  match goal with
  | |- PointArray.full _ _ ?l |-- _ =>
      replace l with (point_swap pts_l i_pre j_pre)
  end.
  - split_pure_spatial.
    + cancel (PointArray.full pts_pre n_pre (point_swap pts_l i_pre j_pre)).
    + dump_pre_spatial. exact PreH6.
  - symmetry.
    unfold point_swap.
    repeat rewrite Znth_replace_Znth_Same by (repeat rewrite Zlength_replace_Znth; lia).
    repeat rewrite Znth_replace_Znth_Diff by (repeat rewrite Zlength_replace_Znth; lia).
    repeat rewrite replace_Znth_twice by (repeat rewrite Zlength_replace_Znth; lia).
    repeat rewrite (Znth_indep pts_l i_pre __default_Point default_point) by lia.
    repeat rewrite (Znth_indep pts_l j_pre __default_Point default_point) by lia.
    simpl.
    replace (point_mk (Znth i_pre pts_l default_point).(x)
                      (Znth i_pre pts_l default_point).(y))
      with (Znth i_pre pts_l default_point)
      by (apply point_eq_by_xy; reflexivity).
    replace (point_mk (Znth j_pre pts_l default_point).(x)
                      (Znth j_pre pts_l default_point).(y))
      with (Znth j_pre pts_l default_point)
      by (apply point_eq_by_xy; reflexivity).
    reflexivity.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_1 : partition_xy_points_entail_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_partition_scan_inv_init; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_2 : partition_xy_points_entail_wit_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  apply points_in_bound_Znth_point_mk; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_3 : partition_xy_points_entail_wit_1_split_goal_3.
Proof. pre_process. Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_4 : partition_xy_points_entail_wit_1_split_goal_4.
Proof. pre_process. Qed.

Lemma proof_of_partition_xy_points_entail_wit_1 : partition_xy_points_entail_wit_1.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_init; eauto; lia.
    + dump_pre_spatial.
      apply points_in_bound_Znth_point_mk; auto; lia.
    + dump_pre_spatial; auto.
    + dump_pre_spatial; auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_1 : partition_xy_points_entail_wit_2_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_partition_scan_inv_accept_swap; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_2 : partition_xy_points_entail_wit_2_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  apply points_in_bound_point_swap; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_3 : partition_xy_points_entail_wit_2_1_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
             __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point) by lia.
  auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_4 : partition_xy_points_entail_wit_2_1_split_goal_4.
Proof.
  pre_process.
  dump_pre_spatial.
  rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
             __default_Point default_point)
    by (rewrite Zlength_point_swap; lia).
  rewrite point_swap_Znth_other_index by lia.
  rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point) by lia.
  auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_5 : partition_xy_points_entail_wit_2_1_split_goal_5.
Proof.
  pre_process.
  dump_pre_spatial.
  rewrite Zlength_point_swap; auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1 : partition_xy_points_entail_wit_2_1.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_accept_swap; eauto; lia.
    + dump_pre_spatial.
      apply points_in_bound_point_swap; auto; lia.
    + dump_pre_spatial.
      rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
                 __default_Point default_point)
        by (rewrite Zlength_point_swap; lia).
      rewrite point_swap_Znth_other_index by lia.
      rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point)
        by lia.
      auto.
    + dump_pre_spatial.
      rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre
                 __default_Point default_point)
        by (rewrite Zlength_point_swap; lia).
      rewrite point_swap_Znth_other_index by lia.
      rewrite (Znth_indep pts_cur_2 high_pre default_point __default_Point)
        by lia.
      auto.
    + dump_pre_spatial.
      rewrite Zlength_point_swap; auto.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2_split_goal_1 : partition_xy_points_entail_wit_2_2_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_partition_scan_inv_accept_noswap; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_accept_noswap; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3_split_goal_1 : partition_xy_points_entail_wit_2_3_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_partition_scan_inv_reject_step; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Proof.
  right. intros. pre_process. split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_partition_scan_inv_reject_step; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_1 : partition_xy_points_return_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply worker_partition_finish_swap_partitioned; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_2 : partition_xy_points_return_wit_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_same_outside_range_point_swap_inside.
  - destruct PreH17 as [_ [Hsame _]]. exact Hsame.
  - rewrite PreH1; lia.
  - rewrite PreH1; lia.
  - lia.
  - lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_3 : partition_xy_points_return_wit_1_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  destruct PreH17 as [Hperm _].
  unfold point_permutation in *.
  eapply Permutation_trans with (l' := pts_cur).
  - exact Hperm.
  - apply point_swap_permutation; rewrite PreH1; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_4 : partition_xy_points_return_wit_1_split_goal_4.
Proof.
  pre_process.
  dump_pre_spatial.
  apply points_in_bound_point_swap; auto; rewrite PreH1; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_5 : partition_xy_points_return_wit_1_split_goal_5.
Proof.
  pre_process.
  dump_pre_spatial.
  rewrite Zlength_point_swap; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1 : partition_xy_points_return_wit_1.
Proof.
  left.
  pre_process.
  Exists (point_swap pts_cur (i + 1) high_pre).
  split_pure_spatial.
  - cancel (PointArray.full pts_pre n_pre (point_swap pts_cur (i + 1) high_pre)).
  - repeat apply _derivable1_andp_intros;
    dump_pre_spatial;
    solve
      [ lia
      | rewrite Zlength_point_swap; lia
      | apply points_in_bound_point_swap; auto; rewrite PreH1; lia
      | destruct PreH17 as [Hperm _]; unfold point_permutation in *;
        eapply Permutation_trans with (l' := pts_cur);
        [ exact Hperm | apply point_swap_permutation; rewrite PreH1; lia ]
      | assert (Hsame : point_same_outside_range pts_l
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre)
          by (eapply point_same_outside_range_point_swap_inside;
              [ destruct PreH17 as [_ [Hsame _]]; exact Hsame
              | rewrite PreH1; lia
              | rewrite PreH1; lia
              | lia
              | lia ]);
        exact Hsame
      | assert (Hsame : point_same_outside_range pts_l
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre)
          by (eapply point_same_outside_range_point_swap_inside;
              [ destruct PreH17 as [_ [Hsame _]]; exact Hsame
              | rewrite PreH1; lia
              | rewrite PreH1; lia
              | lia
              | lia ]);
        unfold point_same_outside_range in Hsame; tauto
      | assert (Hpart : point_xy_partitioned_at
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_swap_partitioned; eauto; lia);
        exact Hpart
      | assert (Hpart : point_xy_partitioned_at
                   (point_swap pts_cur (i + 1) high_pre) low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_swap_partitioned; eauto; lia);
        unfold point_xy_partitioned_at in Hpart; tauto ].
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_1 : partition_xy_points_return_wit_2_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply worker_partition_finish_noswap_partitioned; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_2 : partition_xy_points_return_wit_2_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  destruct PreH16 as [_ [Hsame _]]. exact Hsame.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_3 : partition_xy_points_return_wit_2_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  destruct PreH16 as [Hperm _]. exact Hperm.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Proof.
  left.
  pre_process.
  Exists pts_cur.
  split_pure_spatial.
  - cancel (PointArray.full pts_pre n_pre pts_cur).
  - repeat apply _derivable1_andp_intros;
    dump_pre_spatial;
    solve
      [ lia
      | exact PreH3
      | exact PreH14
      | destruct PreH16 as [Hperm _]; exact Hperm
      | destruct PreH16 as [_ [Hsame _]]; exact Hsame
      | destruct PreH16 as [_ [Hsame _]]; unfold point_same_outside_range in Hsame; tauto
      | assert (Hpart : point_xy_partitioned_at pts_cur low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_noswap_partitioned; eauto; lia);
        exact Hpart
      | assert (Hpart : point_xy_partitioned_at pts_cur low_pre high_pre (i + 1))
          by (eapply worker_partition_finish_noswap_partitioned; eauto; lia);
        unfold point_xy_partitioned_at in Hpart; tauto ].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_1 : quicksort_xy_points_return_wit_1_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_sorted_range_partition_merge_after_subsorts
    with (base := pts_out_2) (mid := pts_out_3) (p := retval);
    try eassumption; try lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_2 : quicksort_xy_points_return_wit_1_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_same_outside_range_trans.
  - exact PreH18.
  - eapply point_same_outside_range_trans.
    + eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
        [lia | lia | exact PreH10].
    + eapply (point_same_outside_range_weaken
                pts_out_3 pts_out_4 (retval + 1) right_pre left_pre right_pre);
        [lia | lia | exact PreH4].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_3 : quicksort_xy_points_return_wit_1_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_permutation in *.
  eapply Permutation_trans.
  - exact PreH17.
  - eapply Permutation_trans.
    + exact PreH9.
    + exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_sorted_range_partition_merge_after_subsorts
        with (base := pts_out_2) (mid := pts_out_3) (p := retval);
        try eassumption; try lia.
    + dump_pre_spatial.
      eapply point_same_outside_range_trans.
      * exact PreH18.
      * eapply point_same_outside_range_trans.
        -- eapply (point_same_outside_range_weaken
                     pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
           [lia | lia | exact PreH10].
        -- eapply (point_same_outside_range_weaken
                     pts_out_3 pts_out_4 (retval + 1) right_pre left_pre right_pre);
           [lia | lia | exact PreH4].
    + dump_pre_spatial.
      unfold point_permutation in *.
      eapply Permutation_trans.
      * exact PreH17.
      * eapply Permutation_trans.
        -- exact PreH9.
        -- exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_1 : quicksort_xy_points_return_wit_2_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_sorted_range_partition_merge_after_subsorts
    with (base := pts_out_2) (mid := pts_out_2) (p := retval);
    try eassumption; try lia.
  - apply Permutation_refl.
  - apply point_same_outside_range_refl.
  - apply point_xy_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_2 : quicksort_xy_points_return_wit_2_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_same_outside_range_trans.
  - exact PreH13.
  - eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 (retval + 1) right_pre left_pre right_pre);
    [lia | lia | exact PreH4].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_3 : quicksort_xy_points_return_wit_2_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_permutation in *.
  eapply Permutation_trans.
  - exact PreH12.
  - exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_sorted_range_partition_merge_after_subsorts
        with (base := pts_out_2) (mid := pts_out_2) (p := retval);
        try eassumption; try lia.
      * apply Permutation_refl.
      * apply point_same_outside_range_refl.
      * apply point_xy_sorted_range_degenerate; lia.
    + dump_pre_spatial.
      eapply point_same_outside_range_trans.
      * exact PreH13.
      * eapply (point_same_outside_range_weaken
                  pts_out_2 pts_out_3 (retval + 1) right_pre left_pre right_pre);
        [lia | lia | exact PreH4].
    + dump_pre_spatial.
      unfold point_permutation in *.
      eapply Permutation_trans.
      * exact PreH12.
      * exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_1 : quicksort_xy_points_return_wit_3_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_xy_sorted_range_partition_merge_after_subsorts
    with (base := pts_out_2) (mid := pts_out_3) (out := pts_out_3) (p := retval);
    try eassumption; try lia.
  - apply Permutation_refl.
  - apply point_same_outside_range_refl.
  - apply point_xy_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_2 : quicksort_xy_points_return_wit_3_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  eapply point_same_outside_range_trans.
  - exact PreH13.
  - eapply (point_same_outside_range_weaken
              pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
    [lia | lia | exact PreH5].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_3 : quicksort_xy_points_return_wit_3_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_permutation in *.
  eapply Permutation_trans.
  - exact PreH12.
  - exact PreH4.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      eapply point_xy_sorted_range_partition_merge_after_subsorts
        with (base := pts_out_2) (mid := pts_out_3) (out := pts_out_3) (p := retval);
        try eassumption; try lia.
      * apply Permutation_refl.
      * apply point_same_outside_range_refl.
      * apply point_xy_sorted_range_degenerate; lia.
    + dump_pre_spatial.
      eapply point_same_outside_range_trans.
      * exact PreH13.
      * eapply (point_same_outside_range_weaken
                  pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre);
        [lia | lia | exact PreH5].
    + dump_pre_spatial.
      unfold point_permutation in *.
      eapply Permutation_trans.
      * exact PreH12.
      * exact PreH4.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_1 : quicksort_xy_points_return_wit_4_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  apply point_xy_sorted_range_degenerate; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_2 : quicksort_xy_points_return_wit_4_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  apply point_same_outside_range_refl.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_3 : quicksort_xy_points_return_wit_4_split_goal_3.
Proof.
  pre_process.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    + dump_pre_spatial.
      apply point_xy_sorted_range_degenerate; lia.
    + dump_pre_spatial.
      apply point_same_outside_range_refl.
    + dump_pre_spatial.
      unfold point_permutation.
      apply Permutation_refl.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1 : andrew_build_from_sorted_entail_wit_1_split_goal_1.
Proof.
  pre_process; dump_pre_spatial.
  unfold andrew_lower_remaining_cont.
  exists (@nil Point).
  repeat split; try reflexivity.
  - unfold andrew_lower_cont, build_hull_c_iter.
    rewrite (sublist_self pts_l_low_level_spec (Zlength pts_l_low_level_spec)) by reflexivity.
    unfold andrew_monotone_chain_m in PreH7 at 1.
    unfold Andrew_Monotone_Chain_M.andrew_monotone_chain in PreH7 at 1.
    unfold Andrew_Monotone_Chain_M.build_andrew_hull in PreH7 at 1.
    prog_nf in PreH7.
    unfold Andrew_Monotone_Chain_M.build_lower_chain in PreH7 at 1.
    prog_nf in PreH7.
    unfold Andrew_Monotone_Chain_M.build_chain in PreH7 at 1.
    prog_nf in PreH7.
    apply safeExec_update'_bind in PreH7.
    eapply (@safeExec_proequiv (list Point) unit
      (Graham_Scan_M.iter Graham_Scan_M.step_p pts_l_low_level_spec tt ;;
       lower <- (T <- get' id ;; StateRelMonad.ret (rev T)) ;;
       upper <- Andrew_Monotone_Chain_M.build_upper_chain pts_l_low_level_spec ;;
       update' (fun _ : list Point =>
         Andrew_Monotone_Chain.andrew_merge pts_l_low_level_spec lower upper))
      (Graham_Scan_M.iter Graham_Scan_M.step_p pts_l_low_level_spec tt ;;
       T <- get' id ;;
       upper <- Andrew_Monotone_Chain_M.build_upper_chain pts_l_low_level_spec ;;
       update' (fun _ : list Point =>
         Andrew_Monotone_Chain.andrew_merge pts_l_low_level_spec (rev T) upper))
      (equiv nil) X_low_level_spec).
    + apply common_step_equiv; intros [].
      etransitivity.
      * apply bind_assoc.
      * apply common_step_equiv; intro T.
        apply (@bind_ret_left (list Point) (list Point) unit (rev T)
          (fun lower =>
             upper <- Andrew_Monotone_Chain_M.build_upper_chain pts_l_low_level_spec ;;
             update' (fun _ : list Point =>
               Andrew_Monotone_Chain.andrew_merge pts_l_low_level_spec lower upper))).
    + destruct PreH7 as [st [Hst Hsafe]].
      exists st. split; [| exact Hsafe].
      destruct Hst as [s0 [Hs _]].
      subst st. reflexivity.
  - intros Hz.
    rewrite PreH3 in Hz.
    lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_2 : andrew_build_from_sorted_entail_wit_1_split_goal_2.
Proof.
  pre_process; dump_pre_spatial.
  apply andrew_lower_scan_inv_nil.
  - rewrite PreH3. exact PreH1.
  - exact PreH4.
  - exact PreH5.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_3 : andrew_build_from_sorted_entail_wit_1_split_goal_3.
Proof.
  pre_process; dump_pre_spatial.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_spatial : andrew_build_from_sorted_entail_wit_1_split_goal_spatial.
Proof.
  pre_process.
  apply PointArray.undef_full_to_undef_seg.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1 : andrew_build_from_sorted_entail_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - apply PointArray.undef_full_to_undef_seg.
  - split_pures.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1; eauto.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_2; eauto.
    + eapply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_3; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2_split_goal_1 : andrew_build_from_sorted_entail_wit_2_split_goal_1.
Proof.
  pre_process; dump_pre_spatial.
  apply points_in_bound_Znth; auto; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2_split_goal_spatial : andrew_build_from_sorted_entail_wit_2_split_goal_spatial.
Proof.
  pre_process.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2 : andrew_build_from_sorted_entail_wit_2.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - cancel.
  - split_pures.
    dump_pre_spatial.
    apply points_in_bound_Znth; auto; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_3 : andrew_build_from_sorted_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1 : andrew_build_from_sorted_entail_wit_4_1.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2 : andrew_build_from_sorted_entail_wit_4_2.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1 : andrew_build_from_sorted_entail_wit_5_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold andrew_lower_remaining_cont in PreH14.
  destruct PreH14 as [stk [Hchain [Hsafe Hupper]]].
  unfold andrew_lower_scan_inv in PreH13.
  destruct PreH13 as [_ [Htop [_ [_ [_ [_ [_ [_ Hfinished]]]]]]]].
  specialize (Hupper ltac:(rewrite PreH9; lia)).
  replace (n_pre - 2 + 1) with (Zlength pts_sorted_2 - 1) by lia.
  replace k with (Zlength lower) by lia.
  exact Hupper.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2 : andrew_build_from_sorted_entail_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3 : andrew_build_from_sorted_entail_wit_5_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold andrew_lower_scan_inv in PreH13.
  destruct PreH13 as [_ [Htop [_ [_ [_ [_ [_ [_ Hfinished]]]]]]]].
  specialize (Hfinished ltac:(rewrite PreH9; lia)).
  unfold andrew_lower_finished_chain in Hfinished.
  destruct Hfinished as [_ [_ [_ [_ [_ [_ [_ [_ Hk]]]]]]]].
  lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_spatial : andrew_build_from_sorted_entail_wit_5_split_goal_spatial.
Proof.
  pre_process.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5 : andrew_build_from_sorted_entail_wit_5.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_6_split_goal_1 : andrew_build_from_sorted_entail_wit_6_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  apply points_in_bound_Znth; auto.
  rewrite PreH10; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6_split_goal_2 : andrew_build_from_sorted_entail_wit_6_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold andrew_upper_scan_inv, andrew_upper_capacity in PreH14.
  intuition subst; rewrite PreH10 in *; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6_split_goal_spatial : andrew_build_from_sorted_entail_wit_6_split_goal_spatial.
Proof.
  pre_process.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6 : andrew_build_from_sorted_entail_wit_6.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial.
      apply points_in_bound_Znth; auto.
      rewrite PreH10; lia.
    + dump_pre_spatial.
      unfold andrew_upper_scan_inv, andrew_upper_capacity in PreH14.
      intuition subst; rewrite PreH10 in *; lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_7 : andrew_build_from_sorted_entail_wit_7.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1 : andrew_build_from_sorted_entail_wit_8_1.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2 : andrew_build_from_sorted_entail_wit_8_2.
Proof. Admitted. 

Lemma proof_of_andrew_build_from_sorted_entail_wit_9 : andrew_build_from_sorted_entail_wit_9.
Proof. Admitted.

Lemma proof_of_andrew_build_from_sorted_entail_wit_10 : andrew_build_from_sorted_entail_wit_10.
Proof. Admitted.

Lemma proof_of_andrew_build_from_sorted_entail_wit_11 : andrew_build_from_sorted_entail_wit_11.
Proof. Admitted.

Lemma proof_of_andrew_build_from_sorted_entail_wit_12 : andrew_build_from_sorted_entail_wit_12.
Proof. Admitted.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_1 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_2 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_3 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_4 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_4.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_5 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_5.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_6 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_6.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_7 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_7.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_8 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_8.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_lower_scan_inv in PreH20;
      destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength lower) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_9 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_9.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH19.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH19 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_10 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_10.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH19.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH19 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_11 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_11.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH19.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH19 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_12 : andrew_build_from_sorted_partial_solve_wit_7_pure_split_goal_12.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH19.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH19 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_7_pure : andrew_build_from_sorted_partial_solve_wit_7_pure.
Proof.
  right.
  intros.
  pre_process.
  repeat apply _derivable1_andp_intros.
  all:
    try (dump_pre_spatial;
         match goal with
         | |- context [Znth ?idx ?xs ?d] =>
             unfold andrew_lower_scan_inv in PreH20;
             destruct PreH20 as [_ [Hlen [_ [Hbound _]]]];
             pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
             assert (0 <= idx < Zlength lower) by lia;
             specialize (Hpt H);
             unfold point_in_bound, Point_Order.point_in_bound in Hpt;
             unfold point_bound, Point_Order.point_bound;
             destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
             try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
         end).
  all:
    dump_pre_spatial;
    unfold point_in_bound, Point_Order.point_in_bound in PreH19;
    unfold point_bound, Point_Order.point_bound;
    destruct PreH19 as [[Hxlo Hxhi] [Hylo Hyhi]];
    try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_1 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_1.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_2 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_2.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_3 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_3.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_4 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_4.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_5 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_5.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_6 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_6.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_7 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_7.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_8 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_8.
Proof.
  pre_process.
  dump_pre_spatial.
  match goal with
  | |- context [Znth ?idx ?xs ?d] =>
      unfold andrew_upper_scan_inv in PreH23;
      destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
      pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
      assert (0 <= idx < Zlength hull_cur) by lia;
      specialize (Hpt H);
      unfold point_in_bound, Point_Order.point_in_bound in Hpt;
      unfold point_bound, Point_Order.point_bound;
      destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
      try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
  end.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_9 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_9.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_10 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_10.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_11 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_11.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_12 : andrew_build_from_sorted_partial_solve_wit_20_pure_split_goal_12.
Proof.
  pre_process.
  dump_pre_spatial.
  unfold point_in_bound, Point_Order.point_in_bound in PreH22.
  unfold point_bound, Point_Order.point_bound.
  destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]].
  try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_build_from_sorted_partial_solve_wit_20_pure : andrew_build_from_sorted_partial_solve_wit_20_pure.
Proof.
  right.
  intros.
  pre_process.
  repeat apply _derivable1_andp_intros.
  all:
    try (dump_pre_spatial;
         match goal with
         | |- context [Znth ?idx ?xs ?d] =>
             unfold andrew_upper_scan_inv in PreH23;
             destruct PreH23 as [_ [_ [Hlen [Hbound _]]]];
             pose proof (points_in_bound_Znth xs idx d Hbound) as Hpt;
             assert (0 <= idx < Zlength hull_cur) by lia;
             specialize (Hpt H);
             unfold point_in_bound, Point_Order.point_in_bound in Hpt;
             unfold point_bound, Point_Order.point_bound;
             destruct Hpt as [[Hxlo Hxhi] [Hylo Hyhi]];
             try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi
         end).
  all:
    dump_pre_spatial;
    unfold point_in_bound, Point_Order.point_in_bound in PreH22;
    unfold point_bound, Point_Order.point_bound;
    destruct PreH22 as [[Hxlo Hxhi] [Hylo Hyhi]];
    try exact Hxlo; try exact Hxhi; try exact Hylo; try exact Hyhi.
Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_1 : andrew_monotone_chain_entail_wit_1_split_goal_1.
Proof.
  pre_process. dump_pre_spatial. unfold point_xy_sorted. rewrite PreH1. exact PreH5.
Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_2 : andrew_monotone_chain_entail_wit_1_split_goal_2.
Proof.
  pre_process. dump_pre_spatial.
  eapply points_not_all_same_permutation_worker; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1_split_goal_spatial : andrew_monotone_chain_entail_wit_1_split_goal_spatial.
Proof. pre_process. Qed.

Lemma proof_of_andrew_monotone_chain_entail_wit_1 : andrew_monotone_chain_entail_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial. unfold point_xy_sorted. rewrite PreH1. exact PreH5.
    + dump_pre_spatial. eapply points_not_all_same_permutation_worker; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1_split_goal_1 : andrew_monotone_chain_return_wit_1_split_goal_1.
Proof.
  pre_process. dump_pre_spatial.
  eapply is_convex_hull_base_permutation; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1_split_goal_2 : andrew_monotone_chain_return_wit_1_split_goal_2.
Proof.
  pre_process. dump_pre_spatial.
  eapply Permutation_trans; eauto.
Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1_split_goal_spatial : andrew_monotone_chain_return_wit_1_split_goal_spatial.
Proof. pre_process. Qed.

Lemma proof_of_andrew_monotone_chain_return_wit_1 : andrew_monotone_chain_return_wit_1.
Proof.
  right.
  pre_process.
  split_pure_spatial.
  - pre_process.
  - split_pures.
    + dump_pre_spatial. eapply is_convex_hull_base_permutation; eauto.
    + dump_pre_spatial. eapply Permutation_trans; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec : andrew_build_from_sorted_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists pts_l_high_level_spec.
  Exists (result_state (equiv empty_point_stack)
    (andrew_monotone_chain_m pts_l_high_level_spec)).
  split_pure_spatial.
  - cancel (PointArray.full pts_pre n_pre pts_l_high_level_spec).
    cancel (PointArray.undef_full hull_pre (2 * n_pre)).
    apply derivable1_wand_sepcon_adjoint.
    pre_process.
    Intros hull_out_2.
    Intros pts_out_2.
    Intros retval_2.
    pre_process.
    Exists hull_out_2.
    Exists pts_out_2.
    Exists retval_2.
    split_pure_spatial.
    + pre_process.
    + split_pures.
      * dump_pre_spatial. exact H5.
      * dump_pre_spatial. exact H6.
      * dump_pre_spatial. exact H7.
      * dump_pre_spatial. exact H8.
      * dump_pre_spatial. exact H9.
      * dump_pre_spatial. exact H10.
      * dump_pre_spatial. exact H11.
      * dump_pre_spatial. exact H12.
      * dump_pre_spatial.
        change (result_state (equiv empty_point_stack)
          (andrew_monotone_chain_m pts_l_high_level_spec))
          with (fun _ : unit => result_state (equiv empty_point_stack)
            (andrew_monotone_chain_m pts_l_high_level_spec) tt) in H13.
        destruct (safeExec_ret_tt _ _ H13) as [s [Heq Hres]].
        change (hull_out_2 = s) in Heq.
        subst s.
        pose proof (Hoare_result_state
          (fun _ : list Point =>
            Andrew_Monotone_Chain.point_xy_sorted pts_l_high_level_spec /\
            Andrew_Monotone_Chain.point_list_non_singleton pts_l_high_level_spec)
          (andrew_monotone_chain_m pts_l_high_level_spec)
          (fun (_ : unit) (T : list Point) =>
            T = Andrew_Monotone_Chain.andrew_hull pts_l_high_level_spec /\
            Graham_Scan_M.is_convex_hull pts_l_high_level_spec T)
          (Andrew_Monotone_Chain_M.andrew_monotone_chain_correct pts_l_high_level_spec)) as Hrs.
        specialize (Hrs tt hull_out_2) as Hrs.
        apply is_convex_hull_direct.
        apply Hrs.
        destruct Hres as [s0 [Hs0 Hc]].
        exists s0. split.
        -- split.
           ++ apply public_point_xy_sorted_to_andrew_worker. exact H4.
           ++ apply points_not_all_same_non_singleton_worker. exact H3.
        -- exact Hc.
  - split_pures.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H0.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. exact H4.
    + dump_pre_spatial.
      apply safeExec_result_state.
      exists empty_point_stack.
      unfold equiv.
      reflexivity.
Qed.
