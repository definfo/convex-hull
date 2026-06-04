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
From SimpleC.EE.convex_hull Require Import graham_scan_goal.
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

Lemma proof_of_leftdown_return_wit_1 : leftdown_return_wit_1.
Proof.
  unfold leftdown_return_wit_1.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_2 : leftdown_return_wit_2.
Proof.
  unfold leftdown_return_wit_2.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_3 : leftdown_return_wit_3.
Proof.
  unfold leftdown_return_wit_3.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_4 : leftdown_return_wit_4.
Proof.
  unfold leftdown_return_wit_4.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_leftdown_return_wit_5 : leftdown_return_wit_5.
Proof.
  unfold leftdown_return_wit_5.
  intros.
  entailer!.
  unfold point_cmp_leftdown, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cross_prod_safety_wit_1 : cross_prod_safety_wit_1.
Proof.
  unfold cross_prod_safety_wit_1.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_2 : cross_prod_safety_wit_2.
Proof.
  unfold cross_prod_safety_wit_2.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_3 : cross_prod_safety_wit_3.
Proof.
  unfold cross_prod_safety_wit_3.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_4 : cross_prod_safety_wit_4.
Proof.
  unfold cross_prod_safety_wit_4.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_5 : cross_prod_safety_wit_5.
Proof.
  unfold cross_prod_safety_wit_5.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_6 : cross_prod_safety_wit_6.
Proof.
  unfold cross_prod_safety_wit_6.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_safety_wit_7 : cross_prod_safety_wit_7.
Proof.
  unfold cross_prod_safety_wit_7.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_cross_prod_return_wit_1 : cross_prod_return_wit_1.
Proof.
  unfold cross_prod_return_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_dot_prod_safety_wit_1 : dot_prod_safety_wit_1.
Proof.
  unfold dot_prod_safety_wit_1.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_2 : dot_prod_safety_wit_2.
Proof.
  unfold dot_prod_safety_wit_2.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= c_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (c_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (c_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_3 : dot_prod_safety_wit_3.
Proof.
  unfold dot_prod_safety_wit_3.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_4 : dot_prod_safety_wit_4.
Proof.
  unfold dot_prod_safety_wit_4.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_5 : dot_prod_safety_wit_5.
Proof.
  unfold dot_prod_safety_wit_5.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= c_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (c_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (c_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_6 : dot_prod_safety_wit_6.
Proof.
  unfold dot_prod_safety_wit_6.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_safety_wit_7 : dot_prod_safety_wit_7.
Proof.
  unfold dot_prod_safety_wit_7.
  intros.
  entailer!.
  all: unfold point_bound, Point_Order.point_bound in *; simpl in *; lia.
Qed.

Lemma proof_of_dot_prod_return_wit_1 : dot_prod_return_wit_1.
Proof.
  unfold dot_prod_return_wit_1.
  intros.
  entailer!.
Qed.

Lemma proof_of_cmp_polar_safety_wit_6 : cmp_polar_safety_wit_6.
Proof.
  unfold cmp_polar_safety_wit_6.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= gp_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= gp_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (gp_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (gp_x_pre - a_x_pre)); nia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (gp_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (gp_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_7 : cmp_polar_safety_wit_7.
Proof.
  unfold cmp_polar_safety_wit_7.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assert (-20000 <= b_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-20000 <= gp_y_pre - a_y_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_y_pre - a_y_pre) * (gp_y_pre - a_y_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_y_pre - a_y_pre));
     destruct (Z_le_gt_dec 0 (gp_y_pre - a_y_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_8 : cmp_polar_safety_wit_8.
Proof.
  unfold cmp_polar_safety_wit_8.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_9 : cmp_polar_safety_wit_9.
Proof.
  unfold cmp_polar_safety_wit_9.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_10 : cmp_polar_safety_wit_10.
Proof.
  unfold cmp_polar_safety_wit_10.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: assert (-20000 <= b_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-20000 <= gp_x_pre - a_x_pre <= 20000); [lia |].
  all: assert (-400000000 <=
      (b_x_pre - a_x_pre) * (gp_x_pre - a_x_pre) <= 400000000);
    [destruct (Z_le_gt_dec 0 (b_x_pre - a_x_pre));
     destruct (Z_le_gt_dec 0 (gp_x_pre - a_x_pre)); nia |].
  all: lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_11 : cmp_polar_safety_wit_11.
Proof.
  unfold cmp_polar_safety_wit_11.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_cmp_polar_safety_wit_12 : cmp_polar_safety_wit_12.
Proof.
  unfold cmp_polar_safety_wit_12.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_2 : cmp_polar_entail_wit_2.
Proof.
  unfold cmp_polar_entail_wit_2.
  intros.
  entailer!.
  all: unfold point_colinear in *.
  all: rewrite <- point_cross_by_value_point; simpl in *; nia.
Qed.

Lemma proof_of_cmp_polar_entail_wit_3 : cmp_polar_entail_wit_3.
Proof.
  unfold cmp_polar_entail_wit_3.
  intros.
  entailer!.
  all: try (apply point_at_mid_by_value; reflexivity).
Qed.

Lemma proof_of_cmp_polar_return_wit_1 : cmp_polar_return_wit_1.
Proof.
  unfold cmp_polar_return_wit_1.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_2 : cmp_polar_return_wit_2.
Proof.
  unfold cmp_polar_return_wit_2.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_3 : cmp_polar_return_wit_3.
Proof.
  unfold cmp_polar_return_wit_3.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_4 : cmp_polar_return_wit_4.
Proof.
  unfold cmp_polar_return_wit_4.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_5 : cmp_polar_return_wit_5.
Proof.
  unfold cmp_polar_return_wit_5.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); [nia |].
  unfold point_cmp_xy, point_mk, x, y.
  simpl.
  repeat match goal with
  | |- context [Z_lt_dec ?a ?b] => destruct (Z_lt_dec a b); try nia
  | |- context [Z_gt_dec ?a ?b] => destruct (Z_gt_dec a b); try nia
  end.
Qed.

Lemma proof_of_cmp_polar_return_wit_6 : cmp_polar_return_wit_6.
Proof.
  unfold cmp_polar_return_wit_6.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); [nia |].
  destruct (Z_lt_dec mid 0); nia.
Qed.

Lemma proof_of_cmp_polar_return_wit_7 : cmp_polar_return_wit_7.
Proof.
  unfold cmp_polar_return_wit_7.
  intros.
  entailer!.
  unfold point_cmp_polar.
  match goal with H : ?cr = point_cross _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec cr 0); [nia |].
  destruct (Z_lt_dec cr 0); [nia |].
  match goal with H : ?mid = point_at_mid _ _ _ |- _ => rewrite <- H end.
  destruct (Z_gt_dec mid 0); nia.
Qed.

Lemma proof_of_cmp_polar_return_wit_8 : cmp_polar_return_wit_8.
Proof.
  unfold cmp_polar_return_wit_8.
  intros.
  entailer!.
  unfold point_cmp_polar.
  replace (point_cross (point_mk gp_x_pre gp_y_pre)
             (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre))
    with retval.
  - destruct (Z_gt_dec retval 0); [nia |].
    destruct (Z_lt_dec retval 0); nia.
  - rewrite <- point_cross_by_value_point.
    simpl.
    nia.
Qed.

Lemma proof_of_cmp_polar_return_wit_9 : cmp_polar_return_wit_9.
Proof.
  unfold cmp_polar_return_wit_9.
  intros.
  entailer!.
  unfold point_cmp_polar.
  replace (point_cross (point_mk gp_x_pre gp_y_pre)
             (point_mk a_x_pre a_y_pre) (point_mk b_x_pre b_y_pre))
    with retval.
  - destruct (Z_gt_dec retval 0); nia.
  - rewrite <- point_cross_by_value_point.
    simpl.
    nia.
Qed.

Lemma proof_of_cmp_polar_partial_solve_wit_1_pure : cmp_polar_partial_solve_wit_1_pure.
Proof.
  unfold cmp_polar_partial_solve_wit_1_pure.
  intros.
  entailer!.
  all: unfold point_in_bound, Point_Order.point_in_bound,
    point_mk, x, y, point_bound, Point_Order.point_bound in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_1 : build_hull_from_sorted_tail_entail_wit_1.
Proof.
  unfold build_hull_from_sorted_tail_entail_wit_1.
  intros.
  Exists (pivot0_low_level_spec :: nil).
  entailer!.
  - simpl.
    replace (hull_pre + 0 * 8) with hull_pre.
    2: lia.
    change (0 + 1) with 1.
    sep_apply_r_atomic (PointArray.seg_single hull_pre 0 pivot0_low_level_spec).
    unfold StorePointAsElement.storeA, store_point.
    replace (hull_pre + 0 * 8) with hull_pre.
    2: lia.
    repeat match goal with
    | |- context [hull_pre + 0] => replace (hull_pre + 0) with hull_pre; [|lia]
    end.
    entailer!.
  - match goal with
    | Hsafe : safeExec _ (build_hull _ _) _ |- _ =>
        unfold build_hull in Hsafe at 1;
        unfold Graham_Scan_M.build_hull in Hsafe
    end.
    unfold build_hull_c_iter.
    rewrite sublist_self.
    2: reflexivity.
    match goal with
    | Hsafe : safeExec _ (_ ;; _) _ |- _ =>
        eapply safeExec_update'_bind in Hsafe
    end.
    eapply safeExec_conseq.
    + match goal with
      | Hsafe : safeExec _ _ _ |- _ => exact Hsafe
      end.
    + intros s [s0 [Hs _]]. subst s. reflexivity.
  - simpl. unfold PointCoordsBound. constructor; auto.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_2 : build_hull_from_sorted_tail_entail_wit_2.
Proof.
  unfold build_hull_from_sorted_tail_entail_wit_2.
  intros.
  Exists stk_2.
  entailer!.
  match goal with
  | Hsafe : safeExec _ (build_hull_c_iter _ _) _ |- _ =>
      unfold build_hull_c_iter in Hsafe at 1;
      rewrite (sublist_split i (Zlength l_low_level_spec) (i + 1) l_low_level_spec) in Hsafe
  end.
  2: lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      rewrite (sublist_single default_point i l_low_level_spec) in Hsafe
  end.
  2: lia.
  all: try lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      simpl in Hsafe;
      unfold Graham_Scan_M.step_p at 1 in Hsafe
  end.
  unfold build_hull_c_step, build_hull_c_next, build_hull_c_iter.
  eapply safeExec_proequiv.
  - eapply bind_equiv.
    + reflexivity.
    + intros []. reflexivity.
  - match goal with
    | Hsafe : safeExec _ _ _ |- _ => exact Hsafe
    end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_3 : build_hull_from_sorted_tail_entail_wit_3.
Proof. Admitted. 

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_4_1 : build_hull_from_sorted_tail_entail_wit_4_1.
Proof. Admitted. 

Lemma proof_of_build_hull_from_sorted_tail_entail_wit_4_2 : build_hull_from_sorted_tail_entail_wit_4_2.
Proof. Admitted. 

Lemma proof_of_build_hull_from_sorted_tail_return_wit_1 : build_hull_from_sorted_tail_return_wit_1.
Proof.
  unfold build_hull_from_sorted_tail_return_wit_1.
  intros.
  Exists stk_2.
  entailer!.
  match goal with
  | Hsafe : safeExec _ (build_hull_c_iter _ _) _ |- _ =>
      unfold build_hull_c_iter in Hsafe at 1;
      replace i with (Zlength l_low_level_spec) in Hsafe
  end.
  2: lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      rewrite (@Zsublist_nil Point l_low_level_spec
                 (Zlength l_low_level_spec) (Zlength l_low_level_spec)) in Hsafe
  end.
  2: lia.
  match goal with
  | Hsafe : safeExec _ _ _ |- _ =>
      simpl in Hsafe;
      exact Hsafe
  end.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_partial_solve_wit_8_pure : build_hull_from_sorted_tail_partial_solve_wit_8_pure.
Proof.
  unfold build_hull_from_sorted_tail_partial_solve_wit_8_pure.
  intros.
  entailer!.
  all: unfold points_in_bound in *.
  all: match goal with
  | Hbound : PointCoordsBound ?l |- context [Znth ?idx ?l ?d] =>
      pose proof (PointCoordsBound_Znth l idx d Hbound ltac:(lia)) as H_pt_bound
  end.
  all: unfold point_in_bound, Point_Order.point_in_bound, point_bound, Point_Order.point_bound,
    Point_Order.x, Point_Order.y in *; simpl in *.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: lia.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_1 : partition_polar_points_entail_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_2_1 : partition_polar_points_entail_wit_2_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_2_2 : partition_polar_points_entail_wit_2_2.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_entail_wit_2_3 : partition_polar_points_entail_wit_2_3.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_return_wit_1 : partition_polar_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_return_wit_2 : partition_polar_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_partition_polar_points_partial_solve_wit_5_pure : partition_polar_points_partial_solve_wit_5_pure.
Proof.
  unfold partition_polar_points_partial_solve_wit_5_pure.
  intros.
  entailer!.
  eapply PointCoordsBound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_quicksort_polar_points_return_wit_1 : quicksort_polar_points_return_wit_1.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_2 : quicksort_polar_points_return_wit_2.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_3 : quicksort_polar_points_return_wit_3.
Proof. Admitted. 

Lemma proof_of_quicksort_polar_points_return_wit_4 : quicksort_polar_points_return_wit_4.
Proof.
  unfold quicksort_polar_points_return_wit_4.
  intros.
  Exists pts_l.
  entailer!.
  - unfold point_sorted_range, PointSortedRange_Point. intros.
    assert (i = j) as Hij.
    { lia. }
    subst.
    rewrite point_cmp_polar_refl. lia.
  - unfold point_same_outside_range, PointSameOutsideRange.
    split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma proof_of_graham_scan_entail_wit_1 : graham_scan_entail_wit_1.
Proof.
  unfold graham_scan_entail_wit_1.
  intros.
  entailer!.
  unfold point_leftmost_prefix.
  apply PointLeftmostPrefix_init.
  lia.
Qed.

Lemma proof_of_graham_scan_entail_wit_2_1 : graham_scan_entail_wit_2_1.
Proof.
  unfold graham_scan_entail_wit_2_1.
  intros.
  entailer!.
  unfold point_leftmost_prefix in *.
  eapply PointLeftmostPrefix_step_update; eauto; try lia.
  apply point_cmp_leftdown_lt_point_leftdown.
  rewrite <- (point_mk_eta (Znth i pts_l default_point)).
  rewrite <- (point_mk_eta (Znth pivot_idx pts_l default_point)).
  rewrite (Znth_indep pts_l i default_point __default_Point) by lia.
  rewrite (Znth_indep pts_l pivot_idx default_point __default_Point) by lia.
  match goal with
  | Hlt : ?retval < 0,
    Heq : ?retval = point_cmp_leftdown _ _ |- point_cmp_leftdown _ _ < 0 =>
      rewrite <- Heq; exact Hlt
  end.
Qed.

Lemma proof_of_graham_scan_entail_wit_2_2 : graham_scan_entail_wit_2_2.
Proof.
  unfold graham_scan_entail_wit_2_2.
  intros.
  entailer!.
  unfold point_leftmost_prefix in *.
  eapply PointLeftmostPrefix_step_keep; eauto; try lia.
  apply point_cmp_leftdown_nonneg_point_leftdown_flip.
  rewrite <- (point_mk_eta (Znth i pts_l default_point)).
  rewrite <- (point_mk_eta (Znth pivot_idx pts_l default_point)).
  rewrite (Znth_indep pts_l i default_point __default_Point) by lia.
  rewrite (Znth_indep pts_l pivot_idx default_point __default_Point) by lia.
  match goal with
  | Hge : 0 <= ?retval,
    Heq : ?retval = point_cmp_leftdown _ _ |- _ =>
      rewrite <- Heq; lia
  | Hge : ?retval >= 0,
    Heq : ?retval = point_cmp_leftdown _ _ |- _ =>
      rewrite <- Heq; lia
  | Hge : 0 <= ?retval,
    Heq : point_cmp_leftdown _ _ = ?retval |- _ =>
      rewrite Heq; lia
  | Hge : ?retval >= 0,
    Heq : point_cmp_leftdown _ _ = ?retval |- _ =>
      rewrite Heq; lia
  end.
Qed.

Lemma proof_of_graham_scan_entail_wit_3_1 : graham_scan_entail_wit_3_1.
Proof.
  unfold graham_scan_entail_wit_3_1.
  pre_process.
  set (pts_pivot := point_swap pts_l 0 pivot_idx).
  set (pivot0 :=
         point_mk (point_x (Znth 0 pts_pivot __default_Point))
                  (point_y (Znth 0 pts_pivot __default_Point))).
  set (tail_sorted := sublist 1 n_pre pts_out).
  Exists tail_sorted pts_out pts_pivot pivot0.
  assert (Hpivot_out :
            Znth 0 pts_out default_point = Znth 0 pts_pivot default_point).
  {
    subst pts_pivot.
    match goal with
    | Hsame : point_same_outside_range _ pts_out 1 (n_pre - 1) |- _ =>
        unfold point_same_outside_range, PointSameOutsideRange in Hsame;
        destruct Hsame as [_ Hsame];
        apply Hsame
    end.
    - rewrite Zlength_point_swap. lia.
    - left. lia.
  }
  assert (Hpivot0_out : pivot0 = Znth 0 pts_out default_point).
  {
    subst pivot0 pts_pivot.
    rewrite (Znth_indep (point_swap pts_l 0 pivot_idx) 0 __default_Point default_point)
      by (rewrite Zlength_point_swap; lia).
    rewrite <- Hpivot_out.
    destruct (Znth 0 pts_out default_point).
    reflexivity.
  }
  assert (Hpts_out_cons : pts_out = pivot0 :: tail_sorted).
  {
    subst tail_sorted.
    eapply point_list_cons_sublist_1_by_fields
      with (d := default_point); eauto; try lia.
    - subst pivot0. rewrite <- Hpivot0_out. reflexivity.
    - subst pivot0. rewrite <- Hpivot0_out. reflexivity.
  }
  assert (Hperm_point : PointPermutation pts_pivot pts_out).
  {
    subst pts_pivot.
    match goal with
    | Hperm : point_permutation (point_swap pts_l 0 pivot_idx) pts_out |- _ =>
        exact Hperm
    end.
  }
  entailer!.
  - rewrite Hpts_out_cons.
    sep_apply_l_atomic
      (PointArray.full_split_to_missing_i pts_pre 0 n_pre
         (pivot0 :: tail_sorted) default_point).
    + dump_pre_spatial. lia.
    + simpl.
      sep_apply_l_atomic (PointArray.missing_i_to_seg_head pts_pre 0 n_pre pivot0 tail_sorted).
      sep_apply_l_atomic (PointArray.seg_to_full pts_pre 1 n_pre tail_sorted).
      replace ((n_pre - 1) + 1) with n_pre by lia.
      unfold StorePointAsElement.storeA, store_point.
      replace (pts_pre + 0) with pts_pre by lia.
      replace (pts_pre + 1 * 8) with (pts_pre + 8) by lia.
      subst pivot0.
      simpl.
      cancel.
      apply derivable1_refl.
  - rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
    rewrite (Znth_indep pts_pivot 0 __default_Point default_point)
      by (subst pts_pivot; rewrite Zlength_point_swap; lia).
    rewrite Hpivot_out.
    reflexivity.
  - rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
    rewrite (Znth_indep pts_pivot 0 __default_Point default_point)
      by (subst pts_pivot; rewrite Zlength_point_swap; lia).
    rewrite Hpivot_out.
    reflexivity.
  - eapply PointLeftmostPrefix_sorted_tail_leftmost
      with (l := pts_l) (pivot_idx := pivot_idx) (n := n_pre)
           (pts_pivot := pts_pivot) (pts_sorted := pts_out).
    + lia.
    + match goal with
      | Hprefix : point_leftmost_prefix pts_l pivot_idx i |- _ =>
          unfold point_leftmost_prefix in Hprefix;
          replace i with n_pre in Hprefix by lia;
          exact Hprefix
      end.
    + subst pts_pivot. reflexivity.
    + rewrite Hpivot0_out. rewrite Hpivot_out. reflexivity.
    + lia.
    + subst tail_sorted. reflexivity.
    + exact Hperm_point.
  - subst tail_sorted.
    eapply point_sorted_range_tail_point_polar_sorted.
    + reflexivity.
    + lia.
    + lia.
    + subst pivot0. exact H3.
  - match goal with
    | Hprefix : point_leftmost_prefix pts_l pivot_idx i |- _ =>
        unfold point_leftmost_prefix in Hprefix;
        replace i with n_pre in Hprefix by lia;
        exact Hprefix
    end.
  - rewrite Hpivot0_out.
    unfold points_in_bound in *.
    eapply PointCoordsBound_Znth; eauto; lia.
  - subst tail_sorted.
    eapply points_in_bound_sublist; eauto; lia.
  - subst tail_sorted. rewrite Zlength_sublist; lia.
Qed.

Lemma proof_of_graham_scan_entail_wit_3_2 : graham_scan_entail_wit_3_2.
Proof.
  unfold graham_scan_entail_wit_3_2.
  pre_process.
  set (pts_pivot := point_swap pts_l 0 pivot_idx).
  set (pivot0 :=
         point_mk (point_x (Znth 0 pts_l __default_Point))
                  (point_y (Znth 0 pts_l __default_Point))).
  set (tail_sorted := sublist 1 n_pre pts_out).
  Exists tail_sorted pts_out pts_pivot pivot0.
  assert (Hpivot0 : pivot0 = Znth 0 pts_l default_point).
  {
    subst pivot0.
    rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
    destruct (Znth 0 pts_l default_point).
    reflexivity.
  }
  assert (Hpivot_out :
            Znth 0 pts_out default_point = Znth 0 pts_l default_point).
  {
    match goal with
    | Hsame : point_same_outside_range pts_l pts_out 1 (n_pre - 1) |- _ =>
        unfold point_same_outside_range, PointSameOutsideRange in Hsame;
        destruct Hsame as [_ Hsame];
        apply Hsame
    end.
    - lia.
    - left. lia.
  }
  assert (Hpts_out_cons : pts_out = pivot0 :: tail_sorted).
  {
    subst tail_sorted.
    eapply point_list_cons_sublist_1_by_fields
      with (d := default_point); eauto; try lia.
    - subst pivot0. rewrite Hpivot_out.
      rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
      reflexivity.
    - subst pivot0. rewrite Hpivot_out.
      rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
      reflexivity.
  }
  assert (Hperm_point : PointPermutation pts_pivot pts_out).
  {
    subst pts_pivot.
    match goal with
    | Hperm : point_permutation pts_l pts_out,
      Hidx : pivot_idx = 0 |- _ =>
        rewrite Hidx; rewrite point_swap_0_0; exact Hperm
    end.
  }
  entailer!.
  - rewrite Hpts_out_cons.
    sep_apply_l_atomic
      (PointArray.full_split_to_missing_i pts_pre 0 n_pre
         (pivot0 :: tail_sorted) default_point).
    + dump_pre_spatial. lia.
    + simpl.
      sep_apply_l_atomic (PointArray.missing_i_to_seg_head pts_pre 0 n_pre pivot0 tail_sorted).
      sep_apply_l_atomic (PointArray.seg_to_full pts_pre 1 n_pre tail_sorted).
      replace ((n_pre - 1) + 1) with n_pre by lia.
      unfold StorePointAsElement.storeA, store_point.
      replace (pts_pre + 0) with pts_pre by lia.
      replace (pts_pre + 1 * 8) with (pts_pre + 8) by lia.
      subst pivot0.
      simpl.
      cancel.
      apply derivable1_refl.
  - rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
    rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
    rewrite Hpivot_out.
    reflexivity.
  - rewrite (Znth_indep pts_out 0 __default_Point default_point) by lia.
    rewrite (Znth_indep pts_l 0 __default_Point default_point) by lia.
    rewrite Hpivot_out.
    reflexivity.
  - eapply PointLeftmostPrefix_sorted_tail_leftmost
      with (l := pts_l) (pivot_idx := pivot_idx) (n := n_pre)
           (pts_pivot := pts_pivot) (pts_sorted := pts_out).
    + lia.
    + match goal with
      | Hprefix : point_leftmost_prefix pts_l pivot_idx i |- _ =>
          unfold point_leftmost_prefix in Hprefix;
          replace i with n_pre in Hprefix by lia;
          exact Hprefix
      end.
    + subst pts_pivot. reflexivity.
    + subst pts_pivot.
      match goal with
      | Hidx : pivot_idx = 0 |- _ =>
          rewrite Hidx; rewrite point_swap_0_0; exact Hpivot0
      end.
    + lia.
    + subst tail_sorted. reflexivity.
    + exact Hperm_point.
  - subst tail_sorted.
    eapply point_sorted_range_tail_point_polar_sorted.
    + reflexivity.
    + lia.
    + lia.
    + subst pivot0. exact H3.
  - match goal with
    | Hprefix : point_leftmost_prefix pts_l pivot_idx i |- _ =>
        unfold point_leftmost_prefix in Hprefix;
        replace i with n_pre in Hprefix by lia;
        exact Hprefix
    end.
  - rewrite Hpivot0.
    unfold points_in_bound in *.
    eapply PointCoordsBound_Znth; eauto; lia.
  - subst tail_sorted.
    eapply points_in_bound_sublist; eauto; lia.
  - subst tail_sorted. rewrite Zlength_sublist; lia.
Qed.

Lemma proof_of_graham_scan_return_wit_1 : graham_scan_return_wit_1.
Proof.
  unfold graham_scan_return_wit_1.
  pre_process.
  replace ((n_pre - 1) + 1) with n_pre by lia.
  prop_apply (PointArray.undef_seg_valid hull_pre retval n_pre).
  Intros.
  Exists hull_out_2 pts_sorted.
  assert (Hpts_sorted_cons : pts_sorted = pivot0 :: tail_sorted).
  {
    eapply point_list_cons_sublist_1_by_fields
      with (n := n_pre) (d := __default_Point); eauto; try lia.
    - match goal with
      | Hx0 : (Znth 0 pts_sorted __default_Point).(x) = gx,
        Hpivot : pivot0 = point_mk gx gy |- _ =>
          rewrite Hpivot; exact Hx0
      end.
    - match goal with
      | Hy0 : (Znth 0 pts_sorted __default_Point).(y) = gy,
        Hpivot : pivot0 = point_mk gx gy |- _ =>
          rewrite Hpivot; exact Hy0
      end.
  }
  assert (Hperm_l_pivot : point_permutation pts_l pts_pivot).
  {
    subst pts_pivot.
    apply point_swap_permutation;
      unfold point_leftmost_prefix, PointLeftmostPrefix in *; lia.
  }
  assert (Hperm_l_sorted : point_permutation pts_l pts_sorted).
  {
    unfold point_permutation, PointPermutation in *.
    eapply Permutation_trans; eauto.
  }
  assert (Hhull_l : is_convex_hull pts_l hull_out_2).
  {
    eapply is_convex_hull_base_permutation.
    - exact Hperm_l_sorted.
    - rewrite Hpts_sorted_cons.
      match goal with
      | Hhull : is_convex_hull (pivot0 :: tail_sorted) hull_out_2 |- _ =>
          exact Hhull
      end.
  }
  assert (Hhull_nonempty : 1 <= Zlength hull_out_2).
  {
    eapply is_convex_hull_base_nonempty_hull_nonempty
      with (base := pivot0 :: tail_sorted) (p := pivot0).
    - simpl. auto.
    - match goal with
      | Hhull : is_convex_hull (pivot0 :: tail_sorted) hull_out_2 |- _ =>
          exact Hhull
      end.
  }
  entailer!.
  - rewrite Hpts_sorted_cons.
    match goal with
    | Htail : tail = pts_pre + sizeof("Point") |- _ =>
        rewrite Htail
    end.
    sep_apply_l_atomic (store_point_fold pts_pre pivot0).
    sep_apply_l_atomic (point_array_cons_full pts_pre n_pre pivot0 tail_sorted).
    + dump_pre_spatial. lia.
    + cancel.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_11_pure : graham_scan_partial_solve_wit_11_pure.
Proof.
  unfold graham_scan_partial_solve_wit_11_pure.
  intros.
  entailer!.
  unfold points_in_bound in *.
  eapply PointCoordsBound_Znth_point_mk; eauto; lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_12_pure : graham_scan_partial_solve_wit_12_pure.
Proof.
  unfold graham_scan_partial_solve_wit_12_pure.
  intros.
  entailer!.
  - rewrite Zlength_point_swap; lia.
  - unfold points_in_bound in *.
    apply PointCoordsBound_point_swap; eauto; lia.
  - eapply PointCoordsBound_Znth_point_mk.
    + unfold points_in_bound in *.
      apply PointCoordsBound_point_swap; eauto; lia.
    + rewrite Zlength_point_swap; lia.
Qed.

Lemma proof_of_graham_scan_partial_solve_wit_13_pure : graham_scan_partial_solve_wit_13_pure.
Proof.
  unfold graham_scan_partial_solve_wit_13_pure.
  intros.
  entailer!.
  rewrite Zlength_sublist; lia.
Qed.

Lemma proof_of_build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec : build_hull_from_sorted_tail_derive_high_level_spec_by_low_level_spec.
Proof. Admitted. 
