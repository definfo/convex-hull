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
From ConvexHull Require Import Record_Geo_Vec Point_Order Graham_Scan Hull_Equiv Graham_Scan_M.
From FP Require Import PartialOrder_Setoid.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad.
Import naive_C_Rules.
Local Open Scope sac.
Local Open Scope monad_scope.

Notation Point := point.

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

Definition empty_point_stack : list Point := nil.

#[export] Instance point_list_equiv : Equiv (list Point) := eq.

#[export] Instance point_list_equiv_equivalence :
  Equivalence (@equiv (list Point) point_list_equiv).
Proof.
  constructor; congruence.
Qed.

Definition point_mk (x y : Z) : Point :=
  {| point_x := x; point_y := y |}.

Definition point_bound : Z := Point_Order.point_bound.

Definition point_in_bound : Point -> Prop := Point_Order.point_in_bound.

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

Definition point_polar_sorted (pivot : Point) (l : list Point) : Prop :=
  forall i j d,
    0 <= i < j ->
    j < Zlength l ->
    point_cmp_polar pivot (Znth i l d) (Znth j l d) <= 0.

Definition sort : Point -> list Point -> Prop := point_polar_sorted.

Definition build_hull : Point -> list Point -> program (list Point) unit :=
  Graham_Scan_M.build_hull.

Definition is_convex_hull : list Point -> list Point -> Prop :=
  Graham_Scan_M.is_convex_hull.

Definition PointCoordsBound (l : list Point) : Prop :=
  Forall (fun p => point_in_bound p) l.

Definition point_swap (l : list Point) (i j : Z) : list Point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Definition PointPermutation : list Point -> list Point -> Prop :=
  @Permutation Point.

Definition PointSameOutsideRange (l l1 : list Point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

Definition PointSortedRange_Point
    (gp : Point) (l : list Point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_polar gp (Znth i l default_point) (Znth j l default_point) <= 0.

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

Definition PointPolarPartitionedAt
    (gp : Point) (l : list Point) (low high p : Z) : Prop :=
  low <= p <= high /\
  Forall (fun x => point_cmp_polar gp x (Znth p l default_point) <= 0)
         (sublist low p l) /\
  Forall (fun x => point_cmp_polar gp (Znth p l default_point) x < 0)
         (sublist (p + 1) (high + 1) l).

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

Definition build_hull_c_iter (l : list Point) (i : Z)
  : program (list Point) unit :=
  iter step_p (sublist i (Zlength l) l) tt.

Definition build_hull_c_next (l : list Point) (i : Z) (_ : unit)
  : program (list Point) unit :=
  build_hull_c_iter l (i + 1).

Definition build_hull_c_step (l : list Point) (i : Z)
  : program (list Point) unit :=
  bind (step_fun (Znth i l default_point))
       (build_hull_c_next l i).

Definition build_hull_c_push (l : list Point) (i : Z)
  : program (list Point) unit :=
  T <- get' id ;;
  update' (fun _ => Znth i l default_point :: T) ;;
  build_hull_c_iter l (i + 1).

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
