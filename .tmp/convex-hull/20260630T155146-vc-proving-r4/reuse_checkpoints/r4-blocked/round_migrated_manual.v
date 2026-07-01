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

Lemma proof_of_cmp_xy_return_wit_1_split_goal_1 : cmp_xy_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_1 : cmp_xy_return_wit_1.
Proof.
  left.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk; simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre);
  destruct (Z_gt_dec a_x_pre b_x_pre);
  destruct (Z_lt_dec a_y_pre b_y_pre);
  destruct (Z_gt_dec a_y_pre b_y_pre); lia.
Qed.

Lemma proof_of_cmp_xy_return_wit_2_split_goal_1 : cmp_xy_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_2 : cmp_xy_return_wit_2.
Proof.
  left.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk; simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre);
  destruct (Z_gt_dec a_x_pre b_x_pre);
  destruct (Z_lt_dec a_y_pre b_y_pre);
  destruct (Z_gt_dec a_y_pre b_y_pre); lia.
Qed.

Lemma proof_of_cmp_xy_return_wit_3_split_goal_1 : cmp_xy_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_3 : cmp_xy_return_wit_3.
Proof.
  left.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk; simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre);
  destruct (Z_gt_dec a_x_pre b_x_pre);
  destruct (Z_lt_dec a_y_pre b_y_pre);
  destruct (Z_gt_dec a_y_pre b_y_pre); lia.
Qed.

Lemma proof_of_cmp_xy_return_wit_4_split_goal_1 : cmp_xy_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_4 : cmp_xy_return_wit_4.
Proof.
  left.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk; simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre);
  destruct (Z_gt_dec a_x_pre b_x_pre);
  destruct (Z_lt_dec a_y_pre b_y_pre);
  destruct (Z_gt_dec a_y_pre b_y_pre); lia.
Qed.

Lemma proof_of_cmp_xy_return_wit_5_split_goal_1 : cmp_xy_return_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_cmp_xy_return_wit_5 : cmp_xy_return_wit_5.
Proof.
  left.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk; simpl.
  destruct (Z_lt_dec a_x_pre b_x_pre);
  destruct (Z_gt_dec a_x_pre b_x_pre);
  destruct (Z_lt_dec a_y_pre b_y_pre);
  destruct (Z_gt_dec a_y_pre b_y_pre); lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_1 : cross_prod_safety_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_1_split_goal_2 : cross_prod_safety_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_1 : cross_prod_safety_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_2_split_goal_2 : cross_prod_safety_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_1 : cross_prod_safety_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_3_split_goal_2 : cross_prod_safety_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_1 : cross_prod_safety_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_4_split_goal_2 : cross_prod_safety_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_1 : cross_prod_safety_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_5_split_goal_2 : cross_prod_safety_wit_5_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_1 : cross_prod_safety_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_6_split_goal_2 : cross_prod_safety_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_1 : cross_prod_safety_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_7_split_goal_2 : cross_prod_safety_wit_7_split_goal_2.
Proof. Abort.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  left.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; nia.
Qed.

Lemma proof_of_cross_prod_return_wit_1_split_goal_1 : cross_prod_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  left.
  intros.
  entailer!.
Qed.

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  unfold swap_points_return_wit_1.
  left.
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
Proof.
  left.
  intros.
  Exists pts_l.
  entailer!.
  - unfold point_xy_partition_scan_inv.
    split.
    + apply Permutation_refl.
    + split.
      * apply point_same_outside_range_refl.
      * split.
        -- rewrite (Znth_indep pts_l high_pre __default_Point default_point) by lia.
           destruct (Znth high_pre pts_l default_point).
           reflexivity.
        -- split; intros k Hk; lia.
  - eapply points_in_bound_Znth_point_mk; eauto; lia.
Qed.

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
Proof.
  left.
  intros.
  Exists (point_swap pts_cur_2 (i + 1) j).
  entailer!.
  - assert (Hij : i + 1 < j) by lia.
    assert (Hi1_range : 0 <= i + 1 < Zlength pts_cur_2) by lia.
    assert (Hj_range : 0 <= j < Zlength pts_cur_2) by lia.
    assert (Hcmpj :
      point_cmp_leftdown (Znth j pts_cur_2 default_point)
                         (point_mk pivot_x pivot_y) <= 0).
    {
      pose proof PreH4 as Hret.
      rewrite (Znth_indep pts_cur_2 j __default_Point default_point) in Hret by lia.
      rewrite point_mk_eta in Hret.
      rewrite <- Hret.
      exact PreH3.
    }
    unfold point_xy_partition_scan_inv in *.
    destruct PreH19 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
    split.
    + eapply Permutation_trans.
      * exact Hperm.
      * apply point_swap_permutation; lia.
    + split.
      * eapply point_same_outside_range_point_swap_inside; eauto; lia.
      * split.
        -- rewrite point_swap_Znth_other_index by lia.
           exact Hpiv.
        -- split.
           ++ intros k Hk.
              destruct (Z.eq_dec k (i + 1)) as [-> | Hki].
              ** rewrite point_swap_Znth_left_index by lia.
                 exact Hcmpj.
              ** rewrite point_swap_Znth_other_index by lia.
                 apply Hleft; lia.
           ++ intros k Hk.
              destruct (Z.eq_dec k j) as [-> | Hkj].
              ** rewrite point_swap_Znth_right_index by lia.
                 apply Hright; lia.
              ** rewrite point_swap_Znth_other_index by lia.
                 apply Hright; lia.
  - apply points_in_bound_point_swap; lia || assumption.
  - rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
    rewrite point_swap_Znth_other_index by lia.
    rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point) by lia.
    exact PreH16.
  - rewrite (Znth_indep (point_swap pts_cur_2 (i + 1) j) high_pre __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
    rewrite point_swap_Znth_other_index by lia.
    rewrite <- (Znth_indep pts_cur_2 high_pre __default_Point default_point) by lia.
    exact PreH15.
  - rewrite Zlength_point_swap.
    exact PreH6.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2_split_goal_1 : partition_xy_points_entail_wit_2_2_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Proof.
  left.
  intros.
  Exists pts_cur_2.
  entailer!.
  assert (Hcmpj :
    point_cmp_leftdown (Znth j pts_cur_2 default_point)
                       (point_mk pivot_x pivot_y) <= 0).
  {
    pose proof PreH3 as Hret.
    rewrite (Znth_indep pts_cur_2 j __default_Point default_point) in Hret by lia.
    rewrite point_mk_eta in Hret.
    rewrite <- Hret.
    exact PreH2.
  }
  unfold point_xy_partition_scan_inv in *.
  destruct PreH18 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
  split; [exact Hperm |].
  split; [exact Hsame |].
  split; [exact Hpiv |].
  split.
  - intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hkj].
    + exact Hcmpj.
    + apply Hleft; lia.
  - intros k Hk.
    apply Hright; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3_split_goal_1 : partition_xy_points_entail_wit_2_3_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Proof.
  left.
  intros.
  Exists pts_cur_2.
  entailer!.
  assert (Hcmpj :
    point_cmp_leftdown (point_mk pivot_x pivot_y)
                       (Znth j pts_cur_2 default_point) < 0).
  {
    pose proof PreH2 as Hret.
    rewrite (Znth_indep pts_cur_2 j __default_Point default_point) in Hret by lia.
    rewrite point_mk_eta in Hret.
    destruct (Znth j pts_cur_2 default_point).
    unfold point_cmp_leftdown in *; simpl in *.
    repeat
      match goal with
      | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b)
      | H : context [Z_lt_dec ?a ?b] |- _ => destruct (Z_lt_dec a b)
      | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b)
      | H : context [Z_gt_dec ?a ?b] |- _ => destruct (Z_gt_dec a b)
      end; lia.
  }
  unfold point_xy_partition_scan_inv in *.
  destruct PreH17 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
  split; [exact Hperm |].
  split; [exact Hsame |].
  split; [exact Hpiv |].
  split.
  - intros k Hk.
    apply Hleft; lia.
  - intros k Hk.
    destruct (Z.eq_dec k j) as [-> | Hkj].
    + exact Hcmpj.
    + apply Hright; lia.
Qed.

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
Proof.
  left.
  intros.
  Exists (point_swap pts_cur (i + 1) high_pre).
  entailer!.
  - unfold point_xy_partition_scan_inv in PreH17.
    destruct PreH17 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
    unfold point_xy_partitioned_at.
    assert (Hi1 : 0 <= i + 1 < Zlength pts_cur) by lia.
    assert (Hhi : 0 <= high_pre < Zlength pts_cur) by lia.
    assert (Hpivot :
      Znth (i + 1) (point_swap pts_cur (i + 1) high_pre) default_point =
      point_mk pivot_x pivot_y).
    {
      rewrite point_swap_Znth_left_index by lia.
      exact Hpiv.
    }
    split; [lia |].
    split.
    + rewrite Hpivot.
      apply Forall_sublist_by_Znth_point; try rewrite Zlength_point_swap; try lia.
      intros k Hk.
      rewrite point_swap_Znth_other_index by lia.
      apply Hleft; lia.
    + rewrite Hpivot.
      apply Forall_sublist_by_Znth_point; try rewrite Zlength_point_swap; try lia.
      intros k Hk.
      destruct (Z.eq_dec k high_pre) as [-> | Hkhi].
      * rewrite point_swap_Znth_right_index by lia.
        apply Hright; lia.
      * rewrite point_swap_Znth_other_index by lia.
        apply Hright; lia.
  - unfold point_xy_partition_scan_inv in PreH17.
    destruct PreH17 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
    eapply point_same_outside_range_point_swap_inside; eauto; lia.
  - unfold point_xy_partition_scan_inv in PreH17.
    destruct PreH17 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
    eapply Permutation_trans.
    + exact Hperm.
    + apply point_swap_permutation; lia.
  - apply points_in_bound_point_swap; lia || assumption.
  - rewrite Zlength_point_swap.
    exact PreH4.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_1 : partition_xy_points_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_2 : partition_xy_points_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_3 : partition_xy_points_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Proof.
  left.
  intros.
  Exists pts_cur.
  unfold point_xy_partition_scan_inv in PreH16.
  destruct PreH16 as [Hperm [Hsame [Hpiv [Hleft Hright]]]].
  entailer!.
  unfold point_xy_partitioned_at.
  split; [lia |].
  split.
  - assert (Hpivot :
      Znth (i + 1) pts_cur default_point = point_mk pivot_x pivot_y).
    {
      rewrite PreH1.
      rewrite (Znth_indep pts_cur high_pre default_point __default_Point) by lia.
      destruct (Znth high_pre pts_cur __default_Point); simpl in *.
      rewrite PreH12, PreH13.
      reflexivity.
    }
    rewrite Hpivot.
    apply Forall_sublist_by_Znth_point; try lia.
    intros k Hk.
    apply Hleft; lia.
  - assert (high_pre + 1 = i + 2) by lia.
    replace (high_pre + 1) with (i + 2) by lia.
    replace (i + 1 + 1) with (i + 2) by lia.
    rewrite (@Zsublist_nil Point pts_cur (i + 2) (i + 2)) by lia.
    constructor.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_1 : quicksort_xy_points_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_2 : quicksort_xy_points_return_wit_1_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_3 : quicksort_xy_points_return_wit_1_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Proof.
  left.
  intros.
  Exists pts_out_4.
  entailer!.
  - assert (Hleft_sorted4 :
      point_xy_sorted_range pts_out_4 left_pre (retval - 1)).
    {
      intros i j Hi Hij Hj.
      assert (Hsame34 :
          point_same_outside_range pts_out_3 pts_out_4
            (retval + 1) right_pre) by assumption.
      destruct Hsame34 as [_ Hsame34].
      rewrite (Hsame34 i) by (lia || left; lia).
      rewrite (Hsame34 j) by (lia || left; lia).
      apply PreH11; lia.
    }
    assert (Hpart3 :
      point_xy_partitioned_at pts_out_3 left_pre right_pre retval).
    {
      eapply point_xy_partitioned_at_preserved_by_left;
        [eassumption | lia | eassumption | lia | eassumption].
    }
    assert (Hpart4 :
      point_xy_partitioned_at pts_out_4 left_pre right_pre retval).
    {
      eapply point_xy_partitioned_at_preserved_by_right;
        [eassumption | lia | eassumption | lia | exact Hpart3].
    }
    eapply point_xy_sorted_range_partition_merge with (p := retval);
      try eassumption; try exact Hpart4; lia.
  - assert (Hsame23_full :
      point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 left_pre (retval - 1)
        left_pre right_pre);
        [lia | lia | assumption].
    }
    assert (Hsame34_full :
      point_same_outside_range pts_out_3 pts_out_4 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_3 pts_out_4 (retval + 1) right_pre
        left_pre right_pre);
        [lia | lia | assumption].
    }
    eapply (point_same_outside_range_trans
              pts_l pts_out_3 pts_out_4 left_pre right_pre);
      [| exact Hsame34_full].
    eapply (point_same_outside_range_trans
              pts_l pts_out_2 pts_out_3 left_pre right_pre);
      [assumption | exact Hsame23_full].
  - unfold point_permutation in *.
    eapply Permutation_trans; [eassumption |].
    eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_1 : quicksort_xy_points_return_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_2 : quicksort_xy_points_return_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_3 : quicksort_xy_points_return_wit_2_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Proof.
  left.
  intros.
  Exists pts_out_3.
  entailer!.
  - assert (Hpart3 :
      point_xy_partitioned_at pts_out_3 left_pre right_pre retval).
    {
      eapply point_xy_partitioned_at_preserved_by_right;
        [eassumption | lia | eassumption | lia | eassumption].
    }
    eapply point_xy_sorted_range_from_right_boundary with (p := retval);
      [lia | lia | lia | exact Hpart3 | assumption].
  - assert (Hsame23_full :
      point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 (retval + 1) right_pre
        left_pre right_pre);
        [lia | lia | assumption].
    }
    eapply (point_same_outside_range_trans
              pts_l pts_out_2 pts_out_3 left_pre right_pre);
      [assumption | exact Hsame23_full].
  - unfold point_permutation in *.
    eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_1 : quicksort_xy_points_return_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_2 : quicksort_xy_points_return_wit_3_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_3 : quicksort_xy_points_return_wit_3_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Proof.
  left.
  intros.
  Exists pts_out_3.
  entailer!.
  - assert (Hpart3 :
      point_xy_partitioned_at pts_out_3 left_pre right_pre retval).
    {
      eapply point_xy_partitioned_at_preserved_by_left;
        [eassumption | lia | eassumption | lia | eassumption].
    }
    eapply point_xy_sorted_range_from_left_boundary with (p := retval);
      [lia | lia | lia | exact Hpart3 | assumption].
  - assert (Hsame23_full :
      point_same_outside_range pts_out_2 pts_out_3 left_pre right_pre).
    {
      eapply (point_same_outside_range_weaken
                pts_out_2 pts_out_3 left_pre (retval - 1)
        left_pre right_pre);
        [lia | lia | assumption].
    }
    eapply (point_same_outside_range_trans
              pts_l pts_out_2 pts_out_3 left_pre right_pre);
      [assumption | exact Hsame23_full].
  - unfold point_permutation in *.
    eapply Permutation_trans; [eassumption | eassumption].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_1 : quicksort_xy_points_return_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_2 : quicksort_xy_points_return_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_3 : quicksort_xy_points_return_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Proof.
  left.
  intros.
  Exists pts_l.
  entailer!.
  - apply point_xy_sorted_range_degenerate.
    lia.
  - apply point_same_outside_range_refl.
Qed.

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
Proof.
  left.
  intros.
  Exists lower_2 pts_sorted_2.
  entailer!.
  eapply points_in_bound_Znth; eauto; lia.
Qed.

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
Proof.
  left.
  intros.
  Exists hull_cur_2 pts_sorted_2.
  entailer!.
  - eapply points_in_bound_Znth; eauto; lia.
  - unfold andrew_upper_scan_inv in PreH14.
    destruct PreH14 as
      [Hread [Htop_bounds [Htop_eq [Hbounds [Hforall [Hnot_all
       [Hlower_finished [Hsuffix [Hcap [Hready Hfinal]]]]]]]]]].
    unfold andrew_upper_capacity in Hcap.
    destruct Hcap as [_ [_ Hcap]].
    specialize (Hcap ltac:(lia)).
    lia.
Qed.

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
Proof.
  left.
  intros.
  Exists hull_cur pts_sorted_2.
  entailer!.
  - unfold andrew_upper_scan_inv in PreH14.
    destruct PreH14 as
      [Hread [Htop_bounds [Htop_eq [Hbounds [Hforall [Hnot_all
       [Hlower_finished [Hsuffix [Hcap [Hready Hfinal]]]]]]]]]].
    eapply is_convex_hull_base_permutation.
    + exact PreH12.
    + destruct (Hfinal ltac:(lia)) as [_ [_ [_ Hhull]]].
      exact Hhull.
  - unfold andrew_upper_scan_inv in PreH14.
    destruct PreH14 as
      [Hread [Htop_bounds [Htop_eq [Hbounds [Hforall [Hnot_all
       [Hlower_finished [Hsuffix [Hcap [Hready Hfinal]]]]]]]]]].
    apply Hfinal; lia.
  - unfold andrew_upper_scan_inv in PreH14.
    destruct PreH14 as
      [Hread [Htop_bounds [Htop_eq [Hbounds [Hforall [Hnot_all
       [Hlower_finished [Hsuffix [Hcap [Hready Hfinal]]]]]]]]]].
    symmetry.
    exact Htop_eq.
Qed.

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
Proof.
  right.
  intros.
  unfold andrew_lower_scan_inv in PreH20.
  destruct PreH20 as [_ [Htop_eq [_ [Hbound_lower _]]]].
  assert (Hi_bound :
    point_in_bound (Znth i pts_sorted __default_Point)).
  { eapply points_in_bound_Znth; eauto; lia. }
  assert (Hk1_bound :
    point_in_bound (Znth (k - 1 - 0) lower __default_Point)).
  { eapply points_in_bound_Znth; eauto; rewrite Htop_eq; lia. }
  assert (Hk2_bound :
    point_in_bound (Znth (k - 2 - 0) lower __default_Point)).
  { eapply points_in_bound_Znth; eauto; rewrite Htop_eq; lia. }
  unfold point_in_bound, Point_Order.point_in_bound in Hi_bound.
  unfold point_in_bound, Point_Order.point_in_bound in Hk1_bound.
  unfold point_in_bound, Point_Order.point_in_bound in Hk2_bound.
  destruct Hi_bound as [[Hix_lo Hix_hi] [Hiy_lo Hiy_hi]].
  destruct Hk1_bound as [[Hk1x_lo Hk1x_hi] [Hk1y_lo Hk1y_hi]].
  destruct Hk2_bound as [[Hk2x_lo Hk2x_hi] [Hk2y_lo Hk2y_hi]].
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

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
Proof.
  right.
  intros.
  unfold andrew_upper_scan_inv in PreH23.
  destruct PreH23 as [_ [_ [Htop_eq [Hbound_hull _]]]].
  assert (Hi_bound :
    point_in_bound (Znth i pts_sorted __default_Point)).
  { eapply points_in_bound_Znth; eauto; lia. }
  assert (Hk1_bound :
    point_in_bound (Znth (k - 1 - 0) hull_cur __default_Point)).
  { eapply points_in_bound_Znth; eauto; rewrite Htop_eq; lia. }
  assert (Hk2_bound :
    point_in_bound (Znth (k - 2 - 0) hull_cur __default_Point)).
  { eapply points_in_bound_Znth; eauto; rewrite Htop_eq; lia. }
  unfold point_in_bound, Point_Order.point_in_bound in Hi_bound.
  unfold point_in_bound, Point_Order.point_in_bound in Hk1_bound.
  unfold point_in_bound, Point_Order.point_in_bound in Hk2_bound.
  destruct Hi_bound as [[Hix_lo Hix_hi] [Hiy_lo Hiy_hi]].
  destruct Hk1_bound as [[Hk1x_lo Hk1x_hi] [Hk1y_lo Hk1y_hi]].
  destruct Hk2_bound as [[Hk2x_lo Hk2x_hi] [Hk2y_lo Hk2y_hi]].
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.
