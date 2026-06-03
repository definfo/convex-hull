Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From compcert.lib Require Import Integers.
From AUXLib Require Import int_auto Feq Idents VMap relations Axioms.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
From ConvexHull Require Export Record_Geo_Point.
From ConvexHull Require Import Record_Geo_Vec Graham_Scan Hull_Equiv.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope sac.

Definition x : Point -> Z := point_x.
Definition y : Point -> Z := point_y.

Notation "p '.(x)'" := (point_x p) (at level 1).
Notation "p '.(y)'" := (point_y p) (at level 1).
Notation "'sizeof' ( ""Point"" )" := (8%Z) (at level 1).

Definition store_point (p : addr) (pt : Point) : Assertion :=
  (&((p) # "Point" ->ₛ "x") # Int |-> pt.(x)) **
  (&((p) # "Point" ->ₛ "y") # Int |-> pt.(y)).

Definition undef_point (p : addr) : Assertion :=
  (&((p) # "Point" ->ₛ "x") # Int |->_) **
  (&((p) # "Point" ->ₛ "y") # Int |->_).
  


Definition point_cmp_xy (a b : Point) : Z :=
  if Z_lt_dec (x a) (x b) then -1 else
  if Z_gt_dec (x a) (x b) then 1 else
  if Z_lt_dec (y a) (y b) then -1 else
  if Z_gt_dec (y a) (y b) then 1 else
  0.

Definition point_leftdown (a b : Point) : Prop :=
  x a < x b \/ (x a = x b /\ y a <= y b).

Definition point_cmp_leftdown (a b : Point) : Z :=
  if Z_lt_dec (x a) (x b) then -1 else
  if Z_gt_dec (x a) (x b) then 1 else
  if Z_lt_dec (y a) (y b) then -1 else
  if Z_gt_dec (y a) (y b) then 1 else
  0.

Definition default_point : Point := {| point_x := 0; point_y := 0 |}.

Lemma point_cmp_leftdown_eq_cmp_xy : forall a b,
  point_cmp_leftdown a b = point_cmp_xy a b.
Proof.
  intros a b.
  unfold point_cmp_leftdown, point_cmp_xy.
  reflexivity.
Qed.

Lemma point_leftdown_refl : forall a,
  point_leftdown a a.
Proof.
  intros a.
  unfold point_leftdown.
  right; nia.
Qed.

Lemma point_leftdown_trans : forall a b c,
  point_leftdown a b ->
  point_leftdown b c ->
  point_leftdown a c.
Proof.
  intros a b c H1 H2.
  unfold point_leftdown in *.
  destruct H1 as [H1|[H1x H1y]].
  - destruct H2 as [H2|[H2x H2y]]; nia.
  - destruct H2 as [H2|[H2x H2y]].
    + left; nia.
    + right; subst; nia.
Qed.

Lemma point_leftdown_total : forall a b,
  point_leftdown a b \/ point_leftdown b a.
Proof.
  intros a b.
  unfold point_leftdown.
  destruct (Z_lt_dec (x a) (x b)).
  { left; left; nia. }
  destruct (Z_gt_dec (x a) (x b)).
  { right; left; nia. }
  destruct (Z_lt_dec (y a) (y b)).
  { left; right; nia. }
  destruct (Z_gt_dec (y a) (y b)).
  { right; right; nia. }
  left; right; nia.
Qed.

Lemma point_leftdown_antitrans : forall a b,
  point_leftdown a b /\ point_leftdown b a <-> x a = x b /\ y a = y b.
Proof.
  intros a b.
  unfold point_leftdown.
  split.
  - intros [[H1|[H1x H1y]] [H2|[H2x H2y]]]; nia.
  - intros [Hx Hy]; subst.
    split; right; nia.
Qed.

Lemma point_leftdown_lt_impl : forall a b,
  point_leftdown a b -> ~ point_leftdown b a ->
  x a < x b \/ (x a = x b /\ y a < y b).
Proof.
  intros a b H Hnot.
  unfold point_leftdown in *.
  destruct H as [H|[Hx Hy]].
  - left; nia.
  - destruct (Z_lt_dec (y a) (y b)).
    + right; nia.
    + assert (y a = y b) by nia.
      subst.
      exfalso. apply Hnot. right; nia.
Qed.

Lemma point_leftdown_gt_impl : forall a b,
  ~ point_leftdown a b -> point_leftdown b a ->
  x a > x b \/ (x a = x b /\ y a > y b).
Proof.
  intros a b Hnot H.
  unfold point_leftdown in *.
  destruct H as [H|[Hx Hy]].
  - left; nia.
  - destruct (Z_gt_dec (y a) (y b)).
    + right; nia.
    + assert (y a = y b) by nia.
      subst.
      exfalso. apply Hnot. right; nia.
Qed.

Lemma derivable1_orp_intros_left : forall (A B C S : Assertion),
  S |-- A -> S |-- A || B || C.
Proof.
  intros A B C S HSA.
  eapply derivable1_trans.
  { exact HSA. }
  eapply derivable1_trans.
  { apply (derivable1_orp_intros1 A B). }
  apply (derivable1_orp_intros1 (A || B) C).
Qed.

Lemma derivable1_orp_intros_mid : forall (A B C S : Assertion),
  S |-- B -> S |-- A || B || C.
Proof.
  intros A B C S HSB.
  pose proof (logic_equiv_orp_assoc A B C) as [Heq1 Heq2].
  eapply derivable1_trans.
  2: { apply Heq2. }
  eapply derivable1_trans.
  2: { apply (derivable1_orp_intros2 A (B || C)). }
  eapply derivable1_trans.
  2: { apply (derivable1_orp_intros1 B C). }
  exact HSB.
Qed.

Lemma derivable1_orp_intros_right : forall (A B C S : Assertion),
  S |-- C -> S |-- A || B || C.
Proof.
  intros A B C S HSC.
  eapply derivable1_trans.
  { exact HSC. }
  apply derivable1_orp_intros2.
Qed.

Lemma emp_derives_pure : forall (P : Prop), P -> emp |-- “ P ”.
Proof.
  intros P HP.
  apply (derivable1s_coq_prop_r P emp).
  exact HP.
Qed.

Lemma emp_derives_pure_or3 : forall (P Q R : Prop),
  (P \/ Q \/ R) -> emp |-- “ P ” || “ Q ” || “ R ”.
Proof.
  intros P Q R Hor.
  destruct Hor as [HP | [HQ | HR]].
  - apply emp_derives_pure in HP.
    transitivity (“ P ”).
    { exact HP. }
    transitivity (“ P ” || “ Q ”).
    { apply derivable1_orp_intros1. }
    apply derivable1_orp_intros1.
  - apply emp_derives_pure in HQ.
    transitivity (“ Q ”).
    { exact HQ. }
    transitivity (“ P ” || “ Q ”).
    { apply derivable1_orp_intros2. }
    apply derivable1_orp_intros1.
  - apply emp_derives_pure in HR.
    transitivity (“ R ”).
    { exact HR. }
    apply derivable1_orp_intros2.
Qed.

Lemma andp_derives_coq_prop_and : forall (P Q R : Prop),
  “ P /\ Q /\ R ” |-- “ P ” && “ Q ” && “ R ”.
Proof.
  intros P Q R.
  apply derivable1s_coq_prop_l.
  intros [HP [HQ HR]].
  pose proof (derivable1s_coq_prop_r P truep HP) as HP'.
  pose proof (derivable1s_coq_prop_r Q truep HQ) as HQ'.
  pose proof (derivable1s_coq_prop_r R truep HR) as HR'.
  assert (HPQ : derivable1 truep (“ P ” && “ Q ”)).
  { eapply derivable1s_truep_intros; eauto. }
  eapply derivable1s_truep_intros; eauto.
Qed.

Lemma derivable1_trans : forall x y z,
  derivable1 x y -> derivable1 y z -> derivable1 x z.
Proof.
  intros x y z H1 H2 m H.
  apply H2.
  apply H1.
  exact H.
Qed.

Lemma emp_derives_or3_and : forall (P1 Q1 R1 P2 Q2 R2 P3 Q3 R3 : Prop),
  ((P1 /\ Q1 /\ R1) \/ (P2 /\ Q2 /\ R2) \/ (P3 /\ Q3 /\ R3)) ->
  emp |-- (“ P1 ” && “ Q1 ” && “ R1 ”) ||
          (“ P2 ” && “ Q2 ” && “ R2 ”) ||
          (“ P3 ” && “ Q3 ” && “ R3 ”).
Proof.
  intros P1 Q1 R1 P2 Q2 R2 P3 Q3 R3 Hor.
  destruct Hor as [[HP1 [HQ1 HR1]] | [[HP2 [HQ2 HR2]] | [HP3 [HQ3 HR3]]]].
  - (* branch 1: A1 *)
    apply emp_derives_pure in HP1. apply emp_derives_pure in HQ1. apply emp_derives_pure in HR1.
    assert (Hgoal1 : emp |-- “ P1 ” && “ Q1 ” && “ R1 ”).
    { assert (HPQ : emp |-- “ P1 ” && “ Q1 ”).
      { eapply derivable1s_truep_intros; eauto. }
      eapply derivable1s_truep_intros; eauto. }
    eapply derivable1_trans.
    { exact Hgoal1. }
    eapply derivable1_trans.
    { apply derivable1_orp_intros1. }
    apply derivable1_orp_intros1.
  - (* branch 2: A2 *)
    apply emp_derives_pure in HP2. apply emp_derives_pure in HQ2. apply emp_derives_pure in HR2.
    assert (Hgoal2 : emp |-- “ P2 ” && “ Q2 ” && “ R2 ”).
    { assert (HPQ : emp |-- “ P2 ” && “ Q2 ”).
      { eapply derivable1s_truep_intros; eauto. }
      eapply derivable1s_truep_intros; eauto. }
    eapply derivable1_trans.
    { exact Hgoal2. }
    eapply derivable1_trans.
    { apply derivable1_orp_intros2. }
    apply derivable1_orp_intros1.
  - (* branch 3: A3 *)
    apply emp_derives_pure in HP3. apply emp_derives_pure in HQ3. apply emp_derives_pure in HR3.
    assert (Hgoal3 : emp |-- “ P3 ” && “ Q3 ” && “ R3 ”).
    { assert (HPQ : emp |-- “ P3 ” && “ Q3 ”).
      { eapply derivable1s_truep_intros; eauto. }
      eapply derivable1s_truep_intros; eauto. }
    eapply derivable1_trans.
    { exact Hgoal3. }
    apply derivable1_orp_intros2.
Qed.

Definition point_cross (a b c : Point) : Z :=
  cross_prod (build_vec a b) (build_vec a c).

Definition point_cross_by_value
    (a_x a_y b_x b_y c_x c_y : Z) : Z :=
  (b_x - a_x) * (c_y - a_y) - (b_y - a_y) * (c_x - a_x).

Definition point_dot_by_value
    (a_x a_y b_x b_y c_x c_y : Z) : Z :=
  (b_x - a_x) * (c_x - a_x) + (b_y - a_y) * (c_y - a_y).

Definition point_dot (a b c : Point) : Z :=
  dot_prod (build_vec a b) (build_vec a c).

Definition point_colinear (pivot a b : Point) : Prop :=
  point_cross pivot a b = 0.

Definition point_at_mid (pivot a b : Point) : Z :=
  point_dot a b pivot.

(* [point_dist2 a b] — squared Euclidean distance; kept for
   compatibility with generated proofs, but no longer used in
   [point_cmp_polar] which prefers [point_at_mid]. *)
Definition point_dist2 (a b : Point) : Z :=
  dot_prod (build_vec a b) (build_vec a b).
Definition point_cmp_polar (pivot a b : Point) : Z :=
  let cr := point_cross pivot a b in
  if Z_gt_dec cr 0 then -1 else
  if Z_lt_dec cr 0 then 1 else
  let mid := point_at_mid pivot a b in
  if Z_gt_dec mid 0 then  1 else
  if Z_lt_dec mid 0 then -1 else
  point_cmp_xy a b.

Definition sort (pivot : Point) (l : list Point) : Prop :=
  forall i j d,
    0 <= i < j ->
    j < Zlength l ->
    point_cmp_polar pivot (Znth i l d) (Znth j l d) <= 0.

Lemma point_cross_unfold : forall a b c,
  point_cross a b c =
  (x b - x a) * (y c - y a) - (y b - y a) * (x c - x a).
Proof.
  intros.
  unfold point_cross, x, y, cross_prod, build_vec.
  simpl.
  nia.
Qed.

Lemma point_cross_by_value_point : forall a b c,
  point_cross_by_value (x a) (y a) (x b) (y b) (x c) (y c) =
  point_cross a b c.
Proof.
  intros.
  unfold point_cross_by_value.
  symmetry.
  apply point_cross_unfold.
Qed.

Lemma point_dot_unfold : forall a b c,
  point_dot a b c =
  (x b - x a) * (x c - x a) + (y b - y a) * (y c - y a).
Proof.
  intros.
  unfold point_dot, x, y, dot_prod, build_vec.
  simpl.
  nia.
Qed.

Lemma point_dot_by_value_point : forall a b c,
  point_dot_by_value (x a) (y a) (x b) (y b) (x c) (y c) =
  point_dot a b c.
Proof.
  intros.
  unfold point_dot_by_value.
  symmetry.
  apply point_dot_unfold.
Qed.

Lemma point_cross_zero_point_colinear : forall gp pa pb,
  point_cross gp pa pb = 0 ->
  point_colinear gp pa pb.
Proof.
  intros.
  unfold point_colinear.
  assumption.
Qed.

Lemma point_at_mid_by_value : forall gp pa pb gp_x gp_y a_x a_y b_x b_y,
  gp_x = x gp -> gp_y = y gp ->
  a_x = x pa -> a_y = y pa ->
  b_x = x pb -> b_y = y pb ->
  (b_x - a_x) * (gp_x - a_x) + (b_y - a_y) * (gp_y - a_y) = point_at_mid gp pa pb.
Proof.
  intros. subst.
  unfold point_at_mid.
  rewrite point_dot_unfold.
  unfold x, y.
  reflexivity.
Qed.

Lemma point_dist2_unfold : forall a b,
  point_dist2 a b =
  (x a - x b) * (x a - x b) + (y a - y b) * (y a - y b).
Proof.
  intros.
  unfold point_dist2, x, y, dot_prod, build_vec.
  simpl.
  nia.
Qed.

Lemma store_point_fold : forall p pt,
  (&((p) # "Point" ->ₛ "x") # Int |-> point_x pt) **
  (&((p) # "Point" ->ₛ "y") # Int |-> point_y pt)
  |-- store_point p pt.
Proof.
  intros.
  unfold store_point.
  apply derivable1_refl.
Qed.

Lemma g_pivot_store_point_fold : forall pt,
  (&(( &( "g_pivot" ) )->ₛ "x") # Int |-> pt.(x)) **
  (&(( &( "g_pivot" ) )->ₛ "y") # Int |-> pt.(y))
  |-- store_point (&( "g_pivot" )) pt.
Proof.
  intros.
  unfold store_point.
  csimpl.
  apply derivable1_refl.
Qed.

Lemma store_point_to_undef_point : forall p pt,
  store_point p pt |-- undef_point p.
Proof.
  intros.
  unfold store_point, undef_point.
  apply derivable1_sepcon_mono.
  - apply store_int_undef_store_int.
  - apply store_int_undef_store_int.
Qed.

Lemma point_cmp_xy_range : forall a b,
  point_cmp_xy a b = -1 \/ point_cmp_xy a b = 0 \/ point_cmp_xy a b = 1.
Proof.
  intros a b.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); nia.
Qed.

Lemma point_cmp_xy_eq_0 : forall a b,
  point_cmp_xy a b = 0 ->
  x a = x b /\ y a = y b.
Proof.
  intros a b Hcmp.
  unfold point_cmp_xy in Hcmp.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); nia.
Qed.

Lemma point_cmp_xy_x_lt : forall a b,
  x a < x b ->
  point_cmp_xy a b = -1.
Proof.
  intros a b Hlt.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_x_gt : forall a b,
  x a > x b ->
  point_cmp_xy a b = 1.
Proof.
  intros a b Hgt.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_y_lt : forall a b,
  x a = x b ->
  y a < y b ->
  point_cmp_xy a b = -1.
Proof.
  intros a b Hx Hy.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_y_gt : forall a b,
  x a = x b ->
  y a > y b ->
  point_cmp_xy a b = 1.
Proof.
  intros a b Hx Hy.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_cmp_xy_eq : forall a b,
  x a = x b ->
  y a = y b ->
  point_cmp_xy a b = 0.
Proof.
  intros a b Hx Hy.
  unfold point_cmp_xy.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b)); lia.
Qed.

Lemma point_eq_by_xy : forall a b,
  x a = x b ->
  y a = y b ->
  a = b.
Proof.
  intros a b Hx Hy.
  destruct a.
  destruct b.
  simpl in *.
  subst.
  reflexivity.
Qed.

Lemma point_cross_same_right : forall a b,
  point_cross a b b = 0.
Proof.
  intros.
  unfold point_cross.
  rewrite cross_prod_self.
  reflexivity.
Qed.

Lemma point_dist2_nonneg : forall a b,
  0 <= point_dist2 a b.
Proof.
  intros.
  unfold point_dist2.
  pose proof (metric_nonneg (build_vec a b)).
  nia.
Qed.

Module StorePointAsElement <: ELEMENT_STORE.
  Definition A := Point.

  Definition storeA (base : addr) (lo : Z) (a : Point) : Assertion :=
    store_point (base + lo * 8) a.

  Definition undefstoreA (base : addr) (lo : Z) : Assertion :=
    undef_point (base + lo * 8).

  Definition sizeA := 8%Z.

  Lemma store_point_to_align : forall p pt,
    store_point p pt |-- store_align_n sizeA.
  Proof.
    intros.
    unfold store_point, sizeA.
    sep_apply (store_int_align4
      (&((p) # "Point" ->ₛ "x")) (point_x pt)).
    sep_apply (store_int_align4
      (&((p) # "Point" ->ₛ "y")) (point_y pt)).
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma undef_point_to_align : forall p,
    undef_point p |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undef_point, sizeA.
    sep_apply (undef_store_int_align4
      (&((p) # "Point" ->ₛ "x"))).
    sep_apply (undef_store_int_align4
      (&((p) # "Point" ->ₛ "y"))).
    sep_apply (store_align4_merge 1 1).
    replace (1 + 1) with 2 by lia.
    sep_apply (store_align4_to_store_align 2).
    replace (4 * 2) with 8 by lia.
    reflexivity.
  Qed.

  Lemma store_to_undefstore : forall base lo a,
    storeA base lo a |-- undefstoreA base lo.
  Proof.
    intros.
    apply store_point_to_undef_point.
  Qed.

  Lemma storeA_shift : forall base n lo a,
    storeA (base + n * sizeA) lo a --||-- storeA base (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (base + n * 8 + lo * 8) with (base + (lo + n) * 8) by lia.
    split; apply derivable1_refl.
  Qed.

  Lemma undefstoreA_shift : forall base n lo,
    undefstoreA (base + n * sizeA) lo --||-- undefstoreA base (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (base + n * 8 + lo * 8) with (base + (lo + n) * 8) by lia.
    split; apply derivable1_refl.
  Qed.

  Lemma store_to_align : forall base lo a, storeA base lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    apply store_point_to_align.
  Qed.

  Lemma undefstore_to_align : forall base lo, undefstoreA base lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    apply undef_point_to_align.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
    unfold sizeA.
    replace Int.max_unsigned with 4294967295 by reflexivity.
    lia.
  Qed.
End StorePointAsElement.

Module PointArray := ArrayLib (StorePointAsElement).

Lemma point_array_store_missing_merge_to_full : forall base i n l d,
  0 <= i < n ->
  store_point (base + i * sizeof("Point")) (Znth i l d) **
  PointArray.missing_i base i 0 n l |--
  PointArray.full base n l.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + unfold StorePointAsElement.storeA.
      apply derivable1_refl.
    + apply derivable1_refl.
  - eapply derivable1_trans.
    + apply (PointArray.missing_i_merge_to_full base i n (Znth i l d) l); lia.
    + rewrite replace_Znth_Znth.
      apply derivable1_refl.
Qed.

Lemma point_array_seg_snoc_store : forall base lo hi l a,
  lo <= hi ->
  PointArray.seg base lo hi l **
  store_point (base + hi * sizeof("Point")) a |--
  PointArray.seg base lo (hi + 1) (l ++ a :: nil).
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + apply derivable1_refl.
    + unfold StorePointAsElement.storeA.
      apply derivable1_refl.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * apply derivable1_refl.
      * apply PointArray.seg_single.
    + apply (PointArray.seg_merge_to_seg base lo hi (hi + 1) l (a :: nil)); lia.
Qed.

Lemma point_array_store_undef_tail_to_undef_seg : forall base lo hi a,
  lo < hi ->
  store_point (base + lo * sizeof("Point")) a **
  PointArray.undef_seg base (lo + 1) hi |--
  PointArray.undef_seg base lo hi.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + apply store_point_to_undef_point.
    + apply derivable1_refl.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * unfold StorePointAsElement.undefstoreA.
        apply derivable1_refl.
      * apply derivable1_refl.
    + eapply derivable1_trans.
      * apply derivable1_sepcon_mono.
        -- apply PointArray.undef_seg_single.
        -- apply derivable1_refl.
      * apply (PointArray.undef_seg_merge_to_undef_seg base lo (lo + 1) hi); lia.
Qed.

Definition rev_ccw_convex (T : list Point) : Prop :=
  forall l1 q l2 r l3 s l4,
    T = l1 ++ q :: l2 ++ r :: l3 ++ s :: l4 ->
    ccw s r q.

Definition is_convex_hull (base T : list Point) : Prop :=
  rev_ccw_convex T /\
  is_max_hull'_edges T base.

Fixpoint pop_fun (p : Point) (T : list Point) : list Point :=
  match T with
  | t :: T' =>
      match T' with
      | s :: T'' =>
          match ccw_dec s t p with
          | left _ => T
          | right _ => pop_fun p T'
          end
      | _ => T
      end
  | _ => T
  end.

Definition step_fun (p : Point) (T : list Point) : list Point :=
  p :: pop_fun p T.

Fixpoint run_tail (T : list Point) (l : list Point) : list Point :=
  match l with
  | [] => T
  | p :: l' => run_tail (step_fun p T) l'
  end.

Definition normalize_stack_fun (T : list Point) : list Point :=
  match rev T with
  | [] => []
  | p :: T' => p :: rev T'
  end.

Definition run_fun (p : Point) (l : list Point) : list Point :=
  normalize_stack_fun (run_tail [p] (rev l)).

Definition processed_of_rev_tail (tail_rev : list Point) (i : Z) : list Point :=
  rev (sublist (i + 1) (Zlength tail_rev) tail_rev).

Definition stack_of_rev_tail (pivot : Point) (tail_rev : list Point) (i : Z) : list Point :=
  run_tail [pivot] (processed_of_rev_tail tail_rev i).

Definition hull_of_rev_tail (pivot : Point) (tail_rev : list Point) (i : Z) : list Point :=
  normalize_stack_fun (stack_of_rev_tail pivot tail_rev i).

Definition stack_suffix (stk0 stk : list Point) : Prop :=
  exists dropped, normalize_stack_fun stk0 = normalize_stack_fun stk ++ dropped.

Definition stack_pop_cursor (next : Point) (base cur : list Point) : Prop :=
  normalize_stack_fun (step_fun next base) =
  normalize_stack_fun (step_fun next cur).

Definition stack_pop_ready (next : Point) (cur : list Point) : Prop :=
  normalize_stack_fun (step_fun next cur) =
  normalize_stack_fun cur ++ next :: nil.

Lemma stack_suffix_refl : forall stk,
  stack_suffix stk stk.
Proof.
  intros stk.
  exists nil.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma stack_suffix_trans : forall stk0 stk1 stk2,
  stack_suffix stk0 stk1 ->
  stack_suffix stk1 stk2 ->
  stack_suffix stk0 stk2.
Proof.
  intros stk0 stk1 stk2 [d1 H1] [d2 H2].
  exists (d2 ++ d1).
  rewrite H1, H2, app_assoc.
  reflexivity.
Qed.

Lemma normalize_stack_fun_surjective : forall l,
  exists stk, normalize_stack_fun stk = l.
Proof.
  intros l.
  destruct l as [| p rest].
  - exists nil.
    reflexivity.
  - exists (rest ++ p :: nil).
    unfold normalize_stack_fun.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_involutive.
    reflexivity.
Qed.

Lemma stack_suffix_pop_norm_last : forall stk0 stk prefix prev cur,
  stack_suffix stk0 stk ->
  normalize_stack_fun stk = prefix ++ prev :: cur :: nil ->
  exists stk',
    stack_suffix stk0 stk' /\
    normalize_stack_fun stk' = prefix ++ prev :: nil.
Proof.
  intros stk0 stk prefix prev cur [dropped Hsuffix] Hnorm.
  destruct (normalize_stack_fun_surjective (prefix ++ prev :: nil)) as [stk' Hstk'].
  exists stk'.
  split.
  - exists (cur :: dropped).
    rewrite Hsuffix, Hnorm, Hstk'.
    repeat rewrite <- app_assoc.
    simpl.
    reflexivity.
  - exact Hstk'.
Qed.

Lemma normalize_stack_fun_Zlength : forall stk,
  Zlength (normalize_stack_fun stk) = Zlength stk.
Proof.
  intros stk.
  unfold normalize_stack_fun.
  destruct (rev stk) eqn:Hrev.
  - apply f_equal with (f := @length Point) in Hrev.
    simpl in Hrev.
    rewrite length_rev in Hrev.
    destruct stk; simpl in *; lia.
  - apply f_equal with (f := @length Point) in Hrev.
    rewrite !Zlength_correct.
    simpl.
    rewrite length_rev.
    simpl in Hrev.
    rewrite length_rev in Hrev.
	    lia.
Qed.

Lemma pop_fun_Zlength_le : forall p stk,
  Zlength (pop_fun p stk) <= Zlength stk.
Proof.
  intros p stk.
  induction stk as [| a stk IH]; simpl; try lia.
  destruct stk as [| b stk']; simpl; try lia.
  destruct (ccw_dec b a p); simpl; try lia.
  specialize (IH).
  simpl in IH.
  eapply Z.le_trans.
  - exact IH.
  - rewrite !Zlength_cons.
    lia.
Qed.

Lemma step_fun_Zlength_le : forall p stk,
  Zlength (step_fun p stk) <= Zlength stk + 1.
Proof.
  intros p stk.
  unfold step_fun.
  rewrite Zlength_cons.
  pose proof (pop_fun_Zlength_le p stk).
  lia.
Qed.

Lemma run_tail_Zlength_le : forall T l,
  Zlength (run_tail T l) <= Zlength T + Zlength l.
Proof.
  intros T l.
  revert T.
  induction l as [| p l IH]; intros T.
  - simpl.
    rewrite Zlength_nil.
    lia.
  - simpl.
    rewrite Zlength_cons.
    pose proof (IH (step_fun p T)).
    pose proof (step_fun_Zlength_le p T).
    lia.
Qed.

Lemma processed_of_rev_tail_Zlength : forall tail_rev i,
  0 <= i < Zlength tail_rev ->
  Zlength (processed_of_rev_tail tail_rev i) = Zlength tail_rev - (i + 1).
Proof.
  intros tail_rev i Hrange.
  unfold processed_of_rev_tail.
  rewrite Zlength_correct.
  rewrite length_rev.
  rewrite <- Zlength_correct.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma stack_of_rev_tail_Zlength_le : forall pivot tail_rev i,
  0 <= i < Zlength tail_rev ->
  Zlength (stack_of_rev_tail pivot tail_rev i) <= Zlength tail_rev - i.
Proof.
  intros pivot tail_rev i Hrange.
  unfold stack_of_rev_tail.
  pose proof (run_tail_Zlength_le (pivot :: nil)
    (processed_of_rev_tail tail_rev i)) as Hrun.
  rewrite Zlength_cons, Zlength_nil in Hrun.
  rewrite processed_of_rev_tail_Zlength in Hrun by exact Hrange.
  lia.
Qed.

Lemma stack_suffix_norm_Zlength_le : forall stk0 stk,
  stack_suffix stk0 stk ->
  Zlength (normalize_stack_fun stk) <= Zlength (normalize_stack_fun stk0).
Proof.
  intros stk0 stk [dropped Hsuffix].
  rewrite Hsuffix.
  rewrite Zlength_app.
  pose proof (Zlength_nonneg dropped).
  lia.
Qed.

Lemma stack_suffix_scan_stack_Zlength_le_tail : forall pivot tail_rev i stk,
  0 <= i < Zlength tail_rev ->
  stack_suffix (stack_of_rev_tail pivot tail_rev i) stk ->
  Zlength (normalize_stack_fun stk) <= Zlength tail_rev.
Proof.
  intros pivot tail_rev i stk Hrange Hsuffix.
  pose proof (stack_suffix_norm_Zlength_le
    (stack_of_rev_tail pivot tail_rev i) stk Hsuffix) as Hsuffix_len.
  rewrite normalize_stack_fun_Zlength.
  rewrite normalize_stack_fun_Zlength in Hsuffix_len.
  rewrite (normalize_stack_fun_Zlength (stack_of_rev_tail pivot tail_rev i)) in Hsuffix_len.
  pose proof (stack_of_rev_tail_Zlength_le pivot tail_rev i Hrange).
  lia.
Qed.

Lemma point_list_split_last_two : forall (l : list Point),
  2 <= Zlength l ->
  exists (prefix : list Point) (prev cur : Point),
    l = prefix ++ prev :: cur :: nil /\
    Zlength prefix = Zlength l - 2.
Proof.
  intros l Hlen.
  destruct (rev l) eqn:Hrev.
  - apply f_equal with (f := @length Point) in Hrev.
    rewrite !Zlength_correct in Hlen.
    simpl in Hrev.
    rewrite length_rev in Hrev.
    lia.
  - destruct l0 eqn:Hrev1.
    + apply f_equal with (f := @length Point) in Hrev.
      rewrite !Zlength_correct in Hlen.
      simpl in Hrev.
      rewrite length_rev in Hrev.
      lia.
    + exists (rev l1), p0, p.
      split.
      * rewrite <- (rev_involutive l).
        rewrite Hrev.
        simpl.
        rewrite <- app_assoc.
        reflexivity.
      * apply f_equal with (f := @length Point) in Hrev.
        rewrite !Zlength_correct.
        rewrite length_rev.
        simpl in Hrev.
        rewrite length_rev in Hrev.
        lia.
Qed.

Lemma hull_of_rev_tail_init : forall pivot tail_rev,
  hull_of_rev_tail pivot tail_rev (Zlength tail_rev - 1) = pivot :: nil.
Proof.
  intros.
  unfold hull_of_rev_tail, stack_of_rev_tail, processed_of_rev_tail.
  rewrite Zsublist_nil by lia.
  simpl.
  reflexivity.
Qed.

Lemma hull_of_rev_tail_init_length : forall pivot tail_rev,
  Zlength (hull_of_rev_tail pivot tail_rev (Zlength tail_rev - 1)) = 1.
Proof.
  intros.
  rewrite hull_of_rev_tail_init.
  rewrite Zlength_cons, Zlength_nil.
  lia.
Qed.

(** ** Bridge between C-level cross and Coq ccw *)

Lemma point_cross_gt_0_ccw : forall a b c,
  point_cross a b c > 0 <-> ccw a b c.
Proof.
  intros a b c.
  unfold point_cross, ccw, left_than.
  rewrite cross_prod_comm.
  split; lia.
Qed.

Lemma point_cross_le_0_not_ccw : forall a b c,
  point_cross a b c <= 0 <-> ~ ccw a b c.
Proof.
  intros a b c.
  unfold point_cross, ccw, left_than.
  rewrite cross_prod_comm.
  split; lia.
Qed.

(** ** normalize_stack_fun decomposition *)

Lemma normalize_stack_fun_decompose : forall stk,
  2 <= Zlength stk ->
  exists prefix prev cur,
    normalize_stack_fun stk = prefix ++ prev :: cur :: nil /\
    Zlength prefix = Zlength stk - 2.
Proof.
  intros stk Hlen.
  rewrite <- normalize_stack_fun_Zlength in Hlen.
  apply point_list_split_last_two in Hlen.
  destruct Hlen as [prefix [prev [cur [Heq Hlen']]]].
  exists prefix, prev, cur.
  split.
  - exact Heq.
  - rewrite normalize_stack_fun_Zlength in Hlen'.
    exact Hlen'.
Qed.

(** ** processed_of_rev_tail step lemma *)

Lemma processed_of_rev_tail_step : forall tail_rev i d,
  0 <= i < Zlength tail_rev ->
  processed_of_rev_tail tail_rev (i - 1) =
  processed_of_rev_tail tail_rev i ++ [Znth i tail_rev d].
Proof.
  intros tail_rev i d Hrange.
  unfold processed_of_rev_tail.
  replace (i - 1 + 1) with i by lia.
  assert (Hlo : 0 <= i <= i + 1) by lia.
  assert (Hhi : i + 1 <= Zlength tail_rev <= Zlength tail_rev) by lia.
  rewrite (sublist_split i (Zlength tail_rev) (i + 1) tail_rev Hlo Hhi).
  rewrite Zlength_correct in Hrange.
  rewrite (sublist_single d i tail_rev) by lia.
  rewrite rev_app_distr.
  reflexivity.
Qed.

(** ** run_tail distributes over app *)

Lemma run_tail_app : forall T l1 l2,
  run_tail T (l1 ++ l2) = run_tail (run_tail T l1) l2.
Proof.
  intros T l1 l2.
  revert T.
  induction l1; intros T.
  - reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Qed.

(** ** Relationship between stack_of_rev_tail at consecutive i *)

Lemma stack_of_rev_tail_step : forall pivot tail_rev i d,
  0 <= i < Zlength tail_rev ->
  stack_of_rev_tail pivot tail_rev (i - 1) =
  step_fun (Znth i tail_rev d) (stack_of_rev_tail pivot tail_rev i).
Proof.
  intros pivot tail_rev i d Hrange.
  unfold stack_of_rev_tail.
  rewrite (processed_of_rev_tail_step tail_rev i d) by auto.
  rewrite run_tail_app.
  simpl.
  reflexivity.
Qed.

(** ** hull_of_rev_tail step lemma *)

Lemma hull_of_rev_tail_step : forall pivot tail_rev i d,
  0 <= i < Zlength tail_rev ->
  hull_of_rev_tail pivot tail_rev (i - 1) =
  normalize_stack_fun (step_fun (Znth i tail_rev d) (stack_of_rev_tail pivot tail_rev i)).
Proof.
  intros pivot tail_rev i d Hrange.
  unfold hull_of_rev_tail.
  rewrite (stack_of_rev_tail_step pivot tail_rev i d) by auto.
  reflexivity.
Qed.

Lemma stack_pop_cursor_ready_hull : forall pivot tail_rev i stk d,
  0 <= i < Zlength tail_rev ->
  stack_pop_cursor (Znth i tail_rev d) (stack_of_rev_tail pivot tail_rev i) stk ->
  stack_pop_ready (Znth i tail_rev d) stk ->
  hull_of_rev_tail pivot tail_rev (i - 1) =
  normalize_stack_fun stk ++ Znth i tail_rev d :: nil.
Proof.
  intros pivot tail_rev i stk d Hrange Hcursor Hready.
  rewrite (hull_of_rev_tail_step pivot tail_rev i d) by exact Hrange.
  unfold stack_pop_cursor in Hcursor.
  unfold stack_pop_ready in Hready.
  rewrite Hcursor.
  exact Hready.
Qed.

(** ** hull_of_rev_tail final expansion *)

Lemma hull_of_rev_tail_final : forall pivot tail_rev,
  hull_of_rev_tail pivot tail_rev (-1) =
  normalize_stack_fun (run_tail [pivot] (rev tail_rev)).
Proof.
  intros pivot tail_rev.
  unfold hull_of_rev_tail, stack_of_rev_tail.
  unfold processed_of_rev_tail.
  replace (-1 + 1) with 0 by lia.
  rewrite (sublist_self tail_rev (Zlength tail_rev)) by reflexivity.
  reflexivity.
Qed.

(** ** Point bound for integer overflow safety *)

Definition point_bound : Z := 10000.

Definition point_in_bound (p : Point) : Prop :=
  -point_bound <= x p <= point_bound /\ -point_bound <= y p <= point_bound.

Lemma point_bound_sub : forall a b,
  point_in_bound a -> point_in_bound b ->
  -20000 <= x a - x b <= 20000 /\ -20000 <= y a - y b <= 20000.
Proof.
  intros a b Ha Hb.
  unfold point_in_bound, point_bound in *.
  destruct Ha as [[Haxl Haxr] [Hayl Hayr]].
  destruct Hb as [[Hbxl Hbxr] [Hbyl Hbyr]].
  split; split; nia.
Qed.

(** * Essay-based aliases (refinement proof §4 naming) *)

Definition scan_stack := stack_of_rev_tail.
Definition scan_hull := hull_of_rev_tail.
Definition stack_norm := normalize_stack_fun.
Definition final_hull := run_fun.
Definition cseq (T : list Point) : list Point := rev T.
Definition pop (T : list Point) : list Point :=
  match T with
  | _ :: T' => T'
  | nil => nil
  end.
Definition left_turn_or_small (T : list Point) (p : Point) : Prop :=
  match T with
  | cur :: prev :: _ => ccw prev cur p
  | _ => True
  end.

Lemma scan_hull_init : forall pivot tail_rev,
  scan_hull pivot tail_rev (Zlength tail_rev - 1) = [pivot].
Proof.
  intros. unfold scan_hull. rewrite hull_of_rev_tail_init. reflexivity.
Qed.

Lemma scan_hull_init_length : forall pivot tail_rev,
  Zlength (scan_hull pivot tail_rev (Zlength tail_rev - 1)) = 1.
Proof.
  intros. rewrite scan_hull_init. reflexivity.
Qed.

Lemma cseq_length : forall T, Zlength (cseq T) = Zlength T.
Proof.
  intros T.
  unfold cseq.
  rewrite !Zlength_correct.
  rewrite length_rev.
  reflexivity.
Qed.

(** * PointCoordsBound — every point in the list satisfies point_in_bound *)

Definition PointCoordsBound (l : list Point) : Prop :=
  Forall (fun p => point_in_bound p) l.

(** * point_swap — swap two elements in a Point list *)

Definition point_swap (l : list Point) (i j : Z) : list Point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

(** * point_mk — Point constructor from coordinates *)

Definition point_mk (x y : Z) : Point :=
  {| point_x := x; point_y := y |}.

(** * PointPermutation — permutation of Point lists *)

Definition PointPermutation : list Point -> list Point -> Prop :=
  @Permutation Point.

(** * PointSameOutsideRange — elements outside [left, right] are identical *)

Definition PointSameOutsideRange (l l1 : list Point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

(** * PointSortedRange — a subrange sorted by polar angle around gp *)

Definition PointSortedRange_Point
    (gp : Point) (l : list Point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_polar gp (Znth i l default_point) (Znth j l default_point) <= 0.

(** * PointTailReverseState — progress of in-place reversal of [1, n) *)

Definition PointTailReverseState
    (before cur : list Point) (n rev_i rev_j : Z) : Prop :=
  Zlength cur = Zlength before /\
  0 <= n <= Zlength before /\
  1 <= rev_i <= n /\
  0 <= rev_j < n /\
  rev_j = n - rev_i /\
  rev_i <= rev_j + 1 /\
  (forall k, 0 <= k < Zlength before -> (k = 0 \/ n <= k) ->
     Znth k cur default_point = Znth k before default_point) /\
  (forall k, 1 <= k < rev_i ->
     Znth k cur default_point = Znth (n - k) before default_point) /\
  (forall k, rev_i <= k <= rev_j ->
     Znth k cur default_point = Znth k before default_point) /\
  (forall k, rev_j < k < n ->
     Znth k cur default_point = Znth (n - k) before default_point).

(** * PointPolarPartitionedAt — polar partition invariant *)

Definition PointPolarPartitionedAt
    (gp : Point) (l : list Point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => point_cmp_polar gp x (Znth p l default_point) <= 0)
         (sublist low p l) /\
  Forall (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
         (sublist (p + 1) (high + 1) l).

(** * PointPolarPartitionScanInv — partition loop invariant *)

Definition PointPolarPartitionScanInv
    (gp : Point) (before cur : list Point)
    (low high : Z) (pivot : Point) (i j : Z) : Prop :=
  PointPermutation before cur /\
  PointSameOutsideRange before cur low high /\
  Znth high cur default_point = pivot /\
  (forall k, low <= k <= i ->
     point_cmp_polar gp (Znth k cur default_point) pivot <= 0) /\
  (forall k, i < k < j ->
     point_cmp_polar gp pivot (Znth k cur default_point) < 0).
