Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import ListLib.Base.Positional.
Require Import ListLib.General.Length.
From compcert.lib Require Import Integers.
From AUXLib Require Import int_auto Feq Idents ListLib VMap relations Axioms.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
From ConvexHull Require Export Record_Geo_Point.
From ConvexHull Require Import Record_Geo_Vec Point_Order Graham_Scan Hull_Equiv Graham_Scan_M.
From FP Require Import PartialOrder_Setoid.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad.
From MonadLib.StateRelMonad Require Import StateRelHoare.
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

Definition PointLeftmostPrefix (l : list Point) (pivot_idx i : Z) : Prop :=
  0 <= pivot_idx < i /\
  i <= Zlength l /\
  forall k,
    0 <= k < i ->
    point_leftdown (Znth pivot_idx l default_point)
                   (Znth k l default_point).

Definition point_leftmost_prefix : list Point -> Z -> Z -> Prop :=
  PointLeftmostPrefix.

Definition empty_point_stack : list Point := nil.

#[export] Instance point_list_equiv : Equiv (list Point) := eq.

#[export] Instance point_list_equiv_equivalence :
  Equivalence (@equiv (list Point) point_list_equiv).
Proof.
  constructor; congruence.
Qed.

Definition point_mk (x y : Z) : Point :=
  {| point_x := x; point_y := y |}.

Lemma point_mk_eta : forall p,
  point_mk (point_x p) (point_y p) = p.
Proof.
  intros [px py].
  reflexivity.
Qed.

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

Lemma point_cmp_leftdown_lt_point_leftdown : forall a b,
  point_cmp_leftdown a b < 0 ->
  point_leftdown a b.
Proof.
  intros a b Hcmp.
  unfold point_cmp_leftdown, point_leftdown, x, y in *.
  destruct (Z_lt_dec (point_x a) (point_x b)) as [Hxlt | Hxnlt].
  - left; lia.
  - destruct (Z_gt_dec (point_x a) (point_x b)) as [Hxgt | Hxngt].
    + lia.
    + destruct (Z_lt_dec (point_y a) (point_y b)) as [Hylt | Hynlt].
      * right; split; lia.
      * destruct (Z_gt_dec (point_y a) (point_y b)); lia.
Qed.

Lemma point_cmp_leftdown_nonneg_point_leftdown_flip : forall a b,
  0 <= point_cmp_leftdown a b ->
  point_leftdown b a.
Proof.
  intros a b Hcmp.
  unfold point_cmp_leftdown, point_leftdown, x, y in *.
  destruct (Z_lt_dec (point_x a) (point_x b)) as [Hxlt | Hxnlt].
  - lia.
  - destruct (Z_gt_dec (point_x a) (point_x b)) as [Hxgt | Hxngt].
    + left; lia.
    + destruct (Z_lt_dec (point_y a) (point_y b)) as [Hylt | Hynlt].
      * lia.
      * destruct (Z_gt_dec (point_y a) (point_y b)) as [Hygt | Hyngt].
        -- right; split; lia.
        -- right; split; lia.
Qed.

Lemma PointLeftmostPrefix_init : forall l,
  1 <= Zlength l ->
  PointLeftmostPrefix l 0 1.
Proof.
  intros l Hlen.
  unfold PointLeftmostPrefix.
  split; [lia |].
  split; [lia |].
  intros k Hk.
  replace k with 0 by lia.
  apply point_leftdown_refl.
Qed.

Lemma PointLeftmostPrefix_step_keep : forall l pivot_idx i,
  PointLeftmostPrefix l pivot_idx i ->
  i < Zlength l ->
  point_leftdown (Znth pivot_idx l default_point)
                 (Znth i l default_point) ->
  PointLeftmostPrefix l pivot_idx (i + 1).
Proof.
  intros l pivot_idx i Hprefix Hlen Hcur.
  unfold PointLeftmostPrefix in *.
  destruct Hprefix as [Hidx [Hi Hmin]].
  split; [lia |].
  split; [lia |].
  intros k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - exact Hcur.
  - apply Hmin.
    lia.
Qed.

Lemma PointLeftmostPrefix_step_update : forall l pivot_idx i,
  PointLeftmostPrefix l pivot_idx i ->
  i < Zlength l ->
  point_leftdown (Znth i l default_point)
                 (Znth pivot_idx l default_point) ->
  PointLeftmostPrefix l i (i + 1).
Proof.
  intros l pivot_idx i Hprefix Hlen Hnew.
  unfold PointLeftmostPrefix in *.
  destruct Hprefix as [Hidx [Hi Hmin]].
  split; [lia |].
  split; [lia |].
  intros k Hk.
  destruct (Z.eq_dec k i) as [-> | Hneq].
  - apply point_leftdown_refl.
  - eapply point_leftdown_trans.
    + exact Hnew.
    + apply Hmin.
      lia.
Qed.

Lemma leftmost_refl_single : forall p,
  leftmost p [p].
Proof.
  intros p.
  unfold leftmost.
  rewrite Forall_cons_iff.
  split.
  - unfold x, y.
    right; split; lia.
  - apply Forall_nil.
Qed.

Lemma point_leftdown_leftmost_cons : forall p q l,
  point_leftdown p q ->
  leftmost p l ->
  leftmost p (q :: l).
Proof.
  intros p q l Hpq Hleft.
  unfold leftmost in *.
  rewrite Forall_cons_iff.
  split.
  - unfold point_leftdown, x, y in Hpq.
    exact Hpq.
  - exact Hleft.
Qed.

Lemma leftmost_rev : forall p l,
  leftmost p l ->
  leftmost p (rev l).
Proof.
  intros p l Hleft.
  unfold leftmost in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hleft.
  rewrite in_rev.
  exact Hq.
Qed.

Lemma leftmost_permutation : forall p l1 l2,
  Permutation l1 l2 ->
  leftmost p l1 ->
  leftmost p l2.
Proof.
  intros p l1 l2 Hperm Hleft.
  unfold leftmost in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hleft.
  eapply Permutation_in.
  - symmetry.
    exact Hperm.
  - exact Hq.
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

Definition point_weak_rev_ccw (pivot a b : Point) : Prop :=
  ccw a pivot b \/
  (point_colinear pivot a b /\ at_mid b a pivot).

Fixpoint point_weak_rev_ccw_list (pivot : Point) (l : list Point) : Prop :=
  match l with
  | a :: rest =>
      Forall (point_weak_rev_ccw pivot a) rest /\
      point_weak_rev_ccw_list pivot rest
  | nil => True
  end.

Definition point_weak_polar_le (pivot a b : Point) : Prop :=
  point_weak_rev_ccw pivot b a.

Definition point_weak_polar_sorted (pivot : Point) (l : list Point) : Prop :=
  forall i j d,
    0 <= i < j ->
    j < Zlength l ->
    point_weak_polar_le pivot (Znth i l d) (Znth j l d).

Definition build_hull : Point -> list Point -> program (list Point) unit :=
  Graham_Scan_M.build_hull.

Definition is_convex_hull : list Point -> list Point -> Prop :=
  Graham_Scan_M.is_convex_hull.

Definition PointCoordsBound (l : list Point) : Prop :=
  Forall (fun p => point_in_bound p) l.

Definition points_in_bound : list Point -> Prop :=
  PointCoordsBound.

Definition point_swap (l : list Point) (i j : Z) : list Point :=
  replace_Znth j (Znth i l default_point)
    (replace_Znth i (Znth j l default_point) l).

Lemma point_swap_0_0 : forall l,
  point_swap l 0 0 = l.
Proof.
  intros l.
  unfold point_swap.
  rewrite replace_Znth_Znth.
  rewrite replace_Znth_Znth.
  reflexivity.
Qed.

Definition PointPermutation : list Point -> list Point -> Prop :=
  @Permutation Point.

Definition point_permutation : list Point -> list Point -> Prop :=
  PointPermutation.

Lemma replace_znth_swap_form : forall {A : Type} (l1 l2 l3 : list A) (xi xj : A),
  replace_Znth (Zlength l1 + 1 + Zlength l2) xi
    (replace_Znth (Zlength l1) xj (l1 ++ xi :: l2 ++ xj :: l3)) =
  l1 ++ xj :: l2 ++ xi :: l3.
Proof.
  intros.
  pose proof (Zlength_nonneg l2) as Hlen2.
  set (n1 := Zlength l1).
  set (n2 := Zlength l1 + 1 + Zlength l2).
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xi :: l2 ++ xj :: l3))
    by (subst n1; lia).
  rewrite (replace_Znth_nothing (A := A) n1 l1 xj) by (subst n1; lia).
  replace (n1 - Zlength l1) with 0 by (subst n1; lia).
  assert (H0 : replace_Znth 0 xj (xi :: l2 ++ xj :: l3) =
               xj :: l2 ++ xj :: l3) by reflexivity.
  rewrite H0.
  rewrite replace_Znth_app_r with (l1 := l1) (l2 := (xj :: l2 ++ xj :: l3))
    by (subst n2; lia).
  rewrite (replace_Znth_nothing (A := A) (n1 + 1 + Zlength l2) l1 xi)
    by (subst n1; lia).
  replace (n1 + 1 + Zlength l2 - Zlength l1) with (1 + Zlength l2)
    by (subst n1; lia).
  rewrite replace_Znth_cons by lia.
  replace (1 + Zlength l2 - 1) with (Zlength l2) by lia.
  rewrite replace_Znth_app_r with (l1 := l2) (l2 := (xj :: l3)) by lia.
  rewrite (replace_Znth_nothing (A := A) (Zlength l2) l2 xi) by lia.
  replace (Zlength l2 - Zlength l2) with 0 by lia.
  assert (H1 : replace_Znth 0 xi (xj :: l3) = xi :: l3) by reflexivity.
  rewrite H1.
  reflexivity.
Qed.

Lemma permutation_swap_znth_lt : forall {A : Type} (l : list A) i j (d : A),
  0 <= i /\ i < j /\ j < Zlength l ->
  Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hrange.
  destruct Hrange as [Hi [Hij Hj]].
  remember (Znth i l d) as xi0.
  remember (Znth j l d) as xj0.
  set (ni := Z.to_nat i).
  set (nj := Z.to_nat (j - i - 1)).
  set (l1 := firstn ni l).
  set (lr := skipn (S ni) l).
  set (l2 := firstn nj lr).
  set (l3 := skipn (S nj) lr).
  assert (Hsplit_i : l = l1 ++ xi0 :: lr).
  {
    subst l1 lr ni.
    rewrite (list_split_nth _ (Z.to_nat i) l d) at 1.
    2:{ rewrite Zlength_correct in Hj. lia. }
    rewrite Heqxi0.
    reflexivity.
  }
  assert (Hj_lr : (nj < List.length lr)%nat).
  {
    subst nj lr ni.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  assert (Hsplit_j : lr = l2 ++ xj0 :: l3).
  {
    subst l2 l3.
    rewrite (list_split_nth _ nj lr d) at 1 by exact Hj_lr.
    replace xj0 with (nth nj lr d).
    2:{
      subst nj lr ni.
      rewrite Heqxj0.
      unfold Znth.
      rewrite nth_skipn.
      assert (Hnat : (Z.to_nat (j - i - 1) + S (Z.to_nat i))%nat = Z.to_nat j).
      {
        apply Nat2Z.inj.
        rewrite Nat2Z.inj_add.
        rewrite Nat2Z.inj_succ.
        repeat rewrite Z2Nat.id by lia.
        lia.
      }
      rewrite Nat.add_comm.
      rewrite Hnat.
      reflexivity.
    }
    reflexivity.
  }
  assert (Hl : l = l1 ++ xi0 :: l2 ++ xj0 :: l3).
  {
    rewrite Hsplit_j in Hsplit_i.
    exact Hsplit_i.
  }
  replace l with (l1 ++ xi0 :: l2 ++ xj0 :: l3) by (symmetry; exact Hl).
  replace i with (Zlength l1).
  2:{
    subst l1 ni.
    rewrite Zlength_correct, length_firstn.
    rewrite Zlength_correct in Hj.
    rewrite Nat.min_l by lia.
    lia.
  }
  replace j with (Zlength l1 + 1 + Zlength l2).
  2:{
    subst l1 l2 lr ni nj.
    rewrite !Zlength_correct.
    rewrite !length_firstn.
    rewrite length_skipn.
    rewrite Zlength_correct in Hj.
    lia.
  }
  rewrite replace_znth_swap_form.
  eapply Permutation_trans.
  2:{ reflexivity. }
  apply Permutation_app_head.
  eapply Permutation_trans.
  - apply Permutation_middle.
  - eapply Permutation_trans.
    + apply Permutation_app_head.
      apply perm_swap.
    + apply Permutation_sym.
      apply Permutation_middle.
Qed.

Lemma replace_nth_comm_any : forall {A : Type} ni nj (l : list A) (a b : A),
  ni <> nj ->
  replace_nth nj (replace_nth ni l a) b =
  replace_nth ni (replace_nth nj l b) a.
Proof.
  intros A ni nj l a b Hneq.
  revert nj l Hneq.
  induction ni; intros nj l Hneq; destruct l as [| x xs]; simpl.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + contradiction Hneq; reflexivity.
    + reflexivity.
  - destruct nj; reflexivity.
  - destruct nj; simpl.
    + reflexivity.
    + f_equal.
      apply IHni.
      intros Heq.
      apply Hneq.
      now f_equal.
Qed.

Lemma replace_znth_comm : forall {A : Type} (l : list A) i j (a b : A),
  0 <= i ->
  0 <= j ->
  i <> j ->
  replace_Znth j b (replace_Znth i a l) =
  replace_Znth i a (replace_Znth j b l).
Proof.
  intros A l i j a b Hi Hj Hneq.
  unfold replace_Znth.
  apply replace_nth_comm_any.
  intro Heq.
  apply Hneq.
  apply Z2Nat.inj in Heq; lia.
Qed.

Lemma replace_Znth_twice : forall {A : Type} (l : list A) i (a b : A),
  0 <= i < Zlength l ->
  replace_Znth i a (replace_Znth i b l) = replace_Znth i a l.
Proof.
  intros A l i a b Hi.
  unfold replace_Znth.
  assert (Htwice : forall n l,
    replace_nth n (replace_nth n l b) a = replace_nth n l a).
  {
    induction n as [| n IHn]; intros [| x xs]; simpl; auto.
    f_equal. apply IHn.
  }
  apply Htwice.
Qed.

Lemma permutation_swap_znth : forall {A : Type} (l : list A) i j (d : A),
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  Permutation l (replace_Znth j (Znth i l d) (replace_Znth i (Znth j l d) l)).
Proof.
  intros A l i j d Hi Hj.
  destruct (Z_lt_ge_dec i j) as [Hij | Hge].
  - apply permutation_swap_znth_lt.
    lia.
  - destruct (Z_lt_ge_dec j i) as [Hji | Heq].
    + rewrite replace_znth_comm by lia.
      apply permutation_swap_znth_lt.
      lia.
    + assert (i = j) by lia.
      subst j.
      rewrite replace_Znth_Znth by lia.
      rewrite replace_Znth_Znth by lia.
      apply Permutation_refl.
Qed.

Lemma point_swap_permutation : forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  point_permutation l (point_swap l i j).
Proof.
  intros l i j Hi Hj.
  unfold point_permutation, PointPermutation, point_swap.
  apply permutation_swap_znth; assumption.
Qed.

Definition PointSameOutsideRange (l l1 : list Point) (left right : Z) : Prop :=
  Zlength l = Zlength l1 /\
  forall k,
    0 <= k < Zlength l ->
    k < left \/ right < k ->
    Znth k l1 default_point = Znth k l default_point.

Definition point_same_outside_range
    (l l1 : list Point) (left right : Z) : Prop :=
  PointSameOutsideRange l l1 left right.

Lemma point_swap_Znth_left_index : forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  Znth i (point_swap l i j) default_point = Znth j l default_point.
Proof.
  intros l i j Hi Hj.
  unfold point_swap.
  destruct (Z.eq_dec j i) as [-> | Hji].
  - rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
    reflexivity.
  - rewrite Znth_replace_Znth_Diff with (i := j) (j := i)
      by (try rewrite Zlength_replace_Znth; lia).
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
Qed.

Lemma point_swap_Znth_right_index : forall l i j,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  Znth j (point_swap l i j) default_point = Znth i l default_point.
Proof.
  intros l i j Hi Hj.
  unfold point_swap.
  rewrite Znth_replace_Znth_Same by (rewrite Zlength_replace_Znth; lia).
  reflexivity.
Qed.

Lemma point_swap_Znth_other_index : forall l i j k,
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  0 <= k < Zlength l ->
  k <> i ->
  k <> j ->
  Znth k (point_swap l i j) default_point = Znth k l default_point.
Proof.
  intros l i j k Hi Hj Hk Hki Hkj.
  unfold point_swap.
  rewrite Znth_replace_Znth_Diff with (i := j) (j := k)
    by (try rewrite Zlength_replace_Znth; lia).
  rewrite Znth_replace_Znth_Diff with (i := i) (j := k)
    by lia.
  reflexivity.
Qed.

Lemma PointSameOutsideRange_point_swap_inside : forall base cur left right i j,
  PointSameOutsideRange base cur left right ->
  0 <= i < Zlength cur ->
  0 <= j < Zlength cur ->
  left <= i <= right ->
  left <= j <= right ->
  PointSameOutsideRange base (point_swap cur i j) left right.
Proof.
  intros base cur left right i j Hsame Hi_range Hj_range Hi Hj.
  destruct Hsame as [Hlen Hsame].
  split.
  - unfold point_swap. repeat rewrite Zlength_replace_Znth. exact Hlen.
  - intros k Hk Hout.
    rewrite point_swap_Znth_other_index; try lia.
    apply Hsame; assumption.
Qed.

Definition PointSortedRange_Point
    (gp : Point) (l : list Point) (left right : Z) : Prop :=
  forall i j,
    left <= i -> i <= j -> j <= right ->
    point_cmp_polar gp (Znth i l default_point) (Znth j l default_point) <= 0.

Definition point_sorted_range
    (gp : Point) (l : list Point) (left right : Z) : Prop :=
  PointSortedRange_Point gp l left right.

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

Definition point_polar_partitioned_at
    (gp : Point) (l : list Point) (low high p : Z) : Prop :=
  PointPolarPartitionedAt gp l low high p.

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

Definition point_polar_partition_scan_inv
    (gp : Point) (before cur : list Point)
    (low high : Z) (pivot : Point) (i j : Z) : Prop :=
  PointPolarPartitionScanInv gp before cur low high pivot i j.

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

Lemma point_cross_gt_0_ccw_local : forall a b c,
  point_cross a b c > 0 ->
  ccw a b c.
Proof.
  intros a b c H.
  unfold point_cross, ccw, left_than, cross_prod, build_vec in *.
  simpl in *.
  lia.
Qed.

Lemma point_cross_zero_point_colinear_swap : forall gp pa pb,
  point_cross gp pa pb = 0 ->
  point_colinear gp pb pa.
Proof.
  intros gp pa pb H.
  unfold point_colinear, point_cross in *.
  rewrite cross_prod_comm.
  lia.
Qed.

Lemma point_at_mid_le_at_mid : forall gp pa pb,
  point_at_mid gp pa pb <= 0 ->
  at_mid pa pb gp.
Proof.
  intros gp pa pb H.
  unfold point_at_mid, point_dot in H.
  unfold at_mid, backward_or_perp.
  unfold dot_prod, build_vec, x, y in *.
  simpl in *.
  lia.
Qed.

Lemma point_cmp_polar_le_point_weak_polar_le : forall gp pa pb,
  point_cmp_polar gp pa pb <= 0 ->
  point_weak_polar_le gp pa pb.
Proof.
  intros gp pa pb Hle.
  unfold point_cmp_polar in Hle.
  unfold point_weak_polar_le, point_weak_rev_ccw.
  destruct (Z_gt_dec (point_cross gp pa pb) 0) as [Hcr_pos | Hcr_not_pos].
  - left.
    apply ccw_cyclicity_2.
    apply point_cross_gt_0_ccw_local.
    exact Hcr_pos.
  - destruct (Z_lt_dec (point_cross gp pa pb) 0) as [Hcr_neg | Hcr_not_neg].
    + lia.
    + assert (Hcr_zero : point_cross gp pa pb = 0) by lia.
      destruct (Z_gt_dec (point_at_mid gp pa pb) 0) as [Hmid_pos | Hmid_not_pos].
      * lia.
      * right.
        split.
        -- apply point_cross_zero_point_colinear_swap.
           exact Hcr_zero.
        -- apply point_at_mid_le_at_mid.
           lia.
Qed.

Lemma point_polar_sorted_point_weak_polar_sorted : forall gp l,
  point_polar_sorted gp l ->
  point_weak_polar_sorted gp l.
Proof.
  unfold point_polar_sorted, point_weak_polar_sorted.
  intros gp l Hsorted i j d Hij Hj.
  apply point_cmp_polar_le_point_weak_polar_le.
  apply Hsorted; assumption.
Qed.

Lemma point_colinear_colinear : forall pivot a b,
  point_colinear pivot a b <-> colinear pivot a b.
Proof.
  intros.
  unfold point_colinear, point_cross, colinear, parallel.
  reflexivity.
Qed.

Lemma point_weak_rev_ccw_g_rev_ccw : forall pivot a b,
  point_weak_rev_ccw pivot a b <-> g_rev_ccw pivot a b.
Proof.
  intros pivot a b.
  unfold point_weak_rev_ccw, g_rev_ccw, weak_rev_ccw.
  split; intros [Hccw | [Hcol Hmid]].
  - left.
    exact Hccw.
  - right.
    split.
    + apply point_colinear_colinear.
      exact Hcol.
    + exact Hmid.
  - left.
    exact Hccw.
  - right.
    split.
    + apply point_colinear_colinear.
      exact Hcol.
    + exact Hmid.
Qed.

Lemma point_weak_rev_ccw_list_g_rev_ccw_list : forall pivot l,
  point_weak_rev_ccw_list pivot l ->
  g_rev_ccw_list pivot l.
Proof.
  intros pivot l.
  induction l as [| a l IH]; simpl; intros Hweak.
  - exact I.
  - destruct Hweak as [Hall Htail].
    split.
    + rewrite Forall_g_rev_ccw_forall.
      intros b Hb.
      apply point_weak_rev_ccw_g_rev_ccw.
      rewrite Forall_forall in Hall.
      exact (Hall b Hb).
    + apply IH.
      exact Htail.
Qed.

Lemma In_Znth_Zlength : forall {A : Type} (l : list A) (x d : A),
  In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  pose proof (@In_nth A l x d Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n).
  split.
  - rewrite Zlength_correct.
    lia.
  - unfold Znth.
    rewrite Nat2Z.id.
    exact Hnth.
Qed.

Lemma Forall_Znth_intro : forall {A : Type} (P : A -> Prop) l d,
  (forall i, 0 <= i < Zlength l -> P (Znth i l d)) ->
  Forall P l.
Proof.
  intros A P l d Hnth.
  rewrite Forall_forall.
  intros x Hin.
  destruct (In_Znth_Zlength l x d Hin) as [i [Hi Hx]].
  rewrite <- Hx.
  apply Hnth.
  exact Hi.
Qed.

Lemma PointLeftmostPrefix_leftmost : forall l pivot_idx,
  PointLeftmostPrefix l pivot_idx (Zlength l) ->
  leftmost (Znth pivot_idx l default_point) l.
Proof.
  intros l pivot_idx Hprefix.
  unfold PointLeftmostPrefix in Hprefix.
  destruct Hprefix as [_ [_ Hmin]].
  unfold leftmost.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  specialize (Hmin i Hi).
  unfold point_leftdown, x, y in Hmin.
  exact Hmin.
Qed.

Lemma leftmost_sublist : forall p l lo hi,
  0 <= lo <= hi ->
  hi <= Zlength l ->
  leftmost p l ->
  leftmost p (sublist lo hi l).
Proof.
  intros p l lo hi Hlohi Hhi Hleft.
  unfold leftmost in *.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia.
  rewrite Forall_forall in Hleft.
  apply Hleft.
  unfold Znth.
  apply nth_In.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma point_weak_polar_sorted_cons_tail : forall pivot a l,
  point_weak_polar_sorted pivot (a :: l) ->
  point_weak_polar_sorted pivot l.
Proof.
  unfold point_weak_polar_sorted.
  intros pivot a l Hsorted i j d Hij Hj.
  specialize (Hsorted (i + 1) (j + 1) d).
  rewrite !Znth_cons in Hsorted by lia.
  replace (i + 1 - 1) with i in Hsorted by lia.
  replace (j + 1 - 1) with j in Hsorted by lia.
  apply Hsorted.
  - lia.
  - rewrite Zlength_cons.
    lia.
Qed.

Lemma point_weak_polar_sorted_cons_head : forall pivot a l,
  point_weak_polar_sorted pivot (a :: l) ->
  Forall (fun q => point_weak_rev_ccw pivot q a) l.
Proof.
  unfold point_weak_polar_sorted, point_weak_polar_le.
  intros pivot a l Hsorted.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  specialize (Hsorted 0 (i + 1) default_point).
  rewrite Znth0_cons in Hsorted.
  rewrite Znth_cons in Hsorted by lia.
  replace (i + 1 - 1) with i in Hsorted by lia.
  apply Hsorted.
  - lia.
  - rewrite Zlength_cons.
    lia.
Qed.

Lemma point_weak_polar_sorted_g_rev_ccw_list_rev : forall pivot l,
  point_weak_polar_sorted pivot l ->
  g_rev_ccw_list pivot (rev l).
Proof.
  intros pivot l.
  induction l as [| a l IH]; simpl; intros Hsorted.
  - exact I.
  - rewrite g_rev_ccw_list_app_iff.
    repeat split.
    + apply IH.
      eapply point_weak_polar_sorted_cons_tail.
      exact Hsorted.
    + apply Forall_nil.
    + intros q r Hq Hr.
      simpl in Hr.
      destruct Hr as [Hr | []].
      subst r.
      apply point_weak_rev_ccw_g_rev_ccw.
      pose proof (point_weak_polar_sorted_cons_head pivot a l Hsorted) as Hall.
      rewrite Forall_forall in Hall.
      apply Hall.
      rewrite in_rev.
      exact Hq.
Qed.

Lemma point_polar_sorted_g_rev_ccw_list_rev : forall pivot l,
  point_polar_sorted pivot l ->
  g_rev_ccw_list pivot (rev l).
Proof.
  intros pivot l Hsorted.
  apply point_weak_polar_sorted_g_rev_ccw_list_rev.
  apply point_polar_sorted_point_weak_polar_sorted.
  exact Hsorted.
Qed.

Lemma point_weak_polar_sorted_pure_sort_rev : forall pivot l,
  leftmost pivot (rev l) ->
  point_weak_polar_sorted pivot l ->
  Record_Geo_Point.sort pivot (rev l).
Proof.
  intros pivot l Hleft Hsorted.
  split.
  - exact Hleft.
  - apply point_weak_polar_sorted_g_rev_ccw_list_rev.
    exact Hsorted.
Qed.

Lemma point_polar_sorted_pure_sort_rev : forall pivot l,
  leftmost pivot (rev l) ->
  point_polar_sorted pivot l ->
  Record_Geo_Point.sort pivot (rev l).
Proof.
  intros pivot l Hleft Hsorted.
  apply point_weak_polar_sorted_pure_sort_rev.
  - exact Hleft.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma point_weak_polar_sorted_graham_scan_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_weak_polar_sorted pivot l ->
  is_convex_hull (pivot :: l) (graham_scan (rev (pivot :: l))).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply graham_scan_closed_convex_hull_final.
  - apply point_weak_polar_sorted_pure_sort_rev; assumption.
  - exact Hne.
Qed.

Lemma point_polar_sorted_graham_scan_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_polar_sorted pivot l ->
  is_convex_hull (pivot :: l) (graham_scan (rev (pivot :: l))).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply point_weak_polar_sorted_graham_scan_convex_hull.
  - exact Hleft.
  - exact Hne.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma point_weak_polar_sorted_build_hull_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_weak_polar_sorted pivot l ->
  Hoare (equiv empty_point_stack)
        (build_hull pivot l)
        (fun _ T => is_convex_hull (pivot :: l) T).
Proof.
  intros pivot l Hleft Hne Hsorted.
  unfold build_hull, is_convex_hull.
  eapply Hoare_conseq_pre.
  2: {
    apply Graham_Scan_M.build_hull_convex_hull_final.
    - apply point_weak_polar_sorted_pure_sort_rev; assumption.
    - exact Hne.
  }
  intros T HT.
  unfold empty_point_stack in HT.
  symmetry.
  exact HT.
Qed.

Lemma point_polar_sorted_build_hull_convex_hull : forall pivot l,
  leftmost pivot (rev l) ->
  l <> [] ->
  point_polar_sorted pivot l ->
  Hoare (equiv empty_point_stack)
        (build_hull pivot l)
        (fun _ T => is_convex_hull (pivot :: l) T).
Proof.
  intros pivot l Hleft Hne Hsorted.
  apply point_weak_polar_sorted_build_hull_convex_hull.
  - exact Hleft.
  - exact Hne.
  - apply point_polar_sorted_point_weak_polar_sorted.
    exact Hsorted.
Qed.

Lemma is_convex_hull_base_permutation : forall base1 base2 hull,
  point_permutation base1 base2 ->
  is_convex_hull base2 hull ->
  is_convex_hull base1 hull.
Proof.
  intros base1 base2 hull Hperm Hhull.
  unfold point_permutation, PointPermutation in Hperm.
  unfold is_convex_hull, Graham_Scan_M.is_convex_hull in *.
  destruct Hhull as [Hconv Hmax].
  split; [exact Hconv |].
  unfold is_max_hull'_edges in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hmax.
  eapply Permutation_in; eauto.
Qed.

Lemma is_convex_hull_base_nonempty_hull_nonempty : forall base hull p,
  In p base ->
  is_convex_hull base hull ->
  1 <= Zlength hull.
Proof.
  intros base hull p Hin Hhull.
  destruct hull as [| h hull_tail].
  - unfold is_convex_hull, Graham_Scan_M.is_convex_hull in Hhull.
    destruct Hhull as [_ Hmax].
    unfold is_max_hull'_edges in Hmax.
    rewrite Forall_forall in Hmax.
    specialize (Hmax p Hin).
    simpl in Hmax.
    contradiction.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg hull_tail).
    lia.
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

Lemma point_cmp_xy_gt_flip_lt : forall a b,
  point_cmp_xy a b > 0 ->
  point_cmp_xy b a < 0.
Proof.
  intros a b Hgt.
  unfold point_cmp_xy in *.
  destruct (Z_lt_dec (x a) (x b));
  destruct (Z_gt_dec (x a) (x b));
  destruct (Z_lt_dec (y a) (y b));
  destruct (Z_gt_dec (y a) (y b));
  destruct (Z_lt_dec (x b) (x a));
  destruct (Z_gt_dec (x b) (x a));
  destruct (Z_lt_dec (y b) (y a));
  destruct (Z_gt_dec (y b) (y a)); lia.
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

Lemma point_list_cons_sublist_1_by_fields : forall l n tail p d,
  Zlength l = n ->
  1 <= n ->
  tail = sublist 1 n l ->
  x (Znth 0 l d) = x p ->
  y (Znth 0 l d) = y p ->
  l = p :: tail.
Proof.
  intros l n tail p d Hlen Hn Htail Hx Hy.
  subst tail.
  assert (Hzero : 0 <= 0 < Zlength l) by lia.
  assert (Hdecomp : l = sublist 0 1 l ++ sublist 1 n l).
  {
    rewrite <- (sublist_split 0 n 1 l) by lia.
    symmetry.
    apply sublist_self.
    lia.
  }
  rewrite Hdecomp at 1.
  replace (sublist 0 1 l) with (Znth 0 l d :: nil).
  2:{
    replace (sublist 0 1 l) with (sublist 0 (0 + 1) l) by reflexivity.
    symmetry.
    apply sublist_single.
    exact Hzero.
  }
  simpl.
  replace (Znth 0 l d) with p.
  - reflexivity.
  - symmetry.
    apply point_eq_by_xy; assumption.
Qed.

Lemma point_cross_same_right : forall a b,
  point_cross a b b = 0.
Proof.
  intros.
  unfold point_cross.
  rewrite cross_prod_self.
  reflexivity.
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

Lemma point_array_cons_full : forall base n p tail,
  1 <= n ->
  store_point base p **
  PointArray.full (base + 8) (n - 1) tail |--
  PointArray.full base n (p :: tail).
Proof.
  intros base n p tail Hn.
  replace base with (base + 0 * 8) at 1 by lia.
  change (store_point (base + 0 * 8) p)
    with (StorePointAsElement.storeA base 0 p).
  sep_apply (PointArray.seg_single base 0 p).
  sep_apply (PointArray.seg_to_full base 0 1 (p :: nil)).
  replace (base + 0 * 8) with base by lia.
  replace (base + 1 * 8) with (base + 8) by lia.
  sep_apply (PointArray.full_merge_to_full base 1 n (p :: nil) tail).
  - simpl. apply derivable1_refl.
  - lia.
Qed.

Lemma PointCoordsBound_Znth : forall l i d,
  PointCoordsBound l ->
  0 <= i < Zlength l ->
  point_in_bound (Znth i l d).
Proof.
  unfold PointCoordsBound.
  intros l i d Hbound Hi.
  apply Forall_forall with (x := Znth i l d) in Hbound.
  - exact Hbound.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma point_in_bound_point_mk_fields : forall p,
  point_in_bound p ->
  point_in_bound (point_mk (point_x p) (point_y p)).
Proof.
  intros [px py] H.
  exact H.
Qed.

Lemma PointCoordsBound_Znth_point_mk : forall l i d,
  PointCoordsBound l ->
  0 <= i < Zlength l ->
  point_in_bound (point_mk (point_x (Znth i l d)) (point_y (Znth i l d))).
Proof.
  intros.
  apply point_in_bound_point_mk_fields.
  eapply PointCoordsBound_Znth; eauto.
Qed.

Lemma points_in_bound_sublist : forall l lo hi,
  points_in_bound l ->
  0 <= lo <= hi ->
  hi <= Zlength l ->
  points_in_bound (sublist lo hi l).
Proof.
  intros l lo hi Hbound Hlohi Hhi.
  unfold points_in_bound, PointCoordsBound in *.
  apply Forall_Znth_intro with (d := default_point).
  intros i Hi.
  rewrite Zlength_sublist in Hi by lia.
  rewrite Znth_sublist by lia.
  eapply PointCoordsBound_Znth; eauto.
  lia.
Qed.

Lemma point_sorted_range_sublist_point_polar_sorted : forall gp l lo hi tail,
  tail = sublist lo hi l ->
  0 <= lo <= hi ->
  hi <= Zlength l ->
  point_sorted_range gp l lo (hi - 1) ->
  point_polar_sorted gp tail.
Proof.
  intros gp l lo hi tail Htail Hlohi Hhi Hsorted.
  subst tail.
  unfold point_polar_sorted.
  intros i j d Hij Hj.
  rewrite Zlength_sublist in Hj by lia.
  rewrite !Znth_sublist by lia.
  rewrite (Znth_indep l (i + lo) d default_point) by lia.
  rewrite (Znth_indep l (j + lo) d default_point) by lia.
  unfold point_sorted_range, PointSortedRange_Point in Hsorted.
  apply Hsorted; lia.
Qed.

Lemma point_sorted_range_tail_point_polar_sorted : forall gp l n tail,
  tail = sublist 1 n l ->
  Zlength l = n ->
  2 <= n ->
  point_sorted_range gp l 1 (n - 1) ->
  point_polar_sorted gp tail.
Proof.
  intros gp l n tail Htail Hlen Hn Hsorted.
  eapply point_sorted_range_sublist_point_polar_sorted; eauto; lia.
Qed.

Lemma Forall_replace_Znth_preserve : forall {A : Type} (P : A -> Prop) l i v,
  Forall P l ->
  P v ->
  Forall P (replace_Znth i v l).
Proof.
  intros A P l i v Hforall Hv.
  unfold replace_Znth.
  remember (Z.to_nat i) as n eqn:Hn.
  clear i Hn.
  revert n.
  induction Hforall as [| a l Ha Htail IH]; intros n; simpl.
  - constructor.
  - destruct n; simpl.
    + constructor; auto.
    + constructor; auto.
Qed.

Lemma Zlength_point_swap : forall l i j,
  Zlength (point_swap l i j) = Zlength l.
Proof.
  intros.
  unfold point_swap.
  repeat rewrite Zlength_replace_Znth.
  reflexivity.
Qed.

Lemma PointCoordsBound_point_swap : forall l i j,
  PointCoordsBound l ->
  0 <= i < Zlength l ->
  0 <= j < Zlength l ->
  PointCoordsBound (point_swap l i j).
Proof.
  unfold PointCoordsBound, point_swap.
  intros l i j Hbound Hi Hj.
  apply Forall_replace_Znth_preserve.
  - apply Forall_replace_Znth_preserve.
    + exact Hbound.
    + eapply PointCoordsBound_Znth; eauto.
  - eapply PointCoordsBound_Znth; eauto.
Qed.

Lemma point_swap_Znth_left : forall l j,
  0 <= j < Zlength l ->
  Znth 0 (point_swap l 0 j) default_point = Znth j l default_point.
Proof.
  intros l j Hj.
  assert (H0 : 0 <= 0 < Zlength l) by lia.
  unfold point_swap.
  destruct (Z.eq_dec j 0) as [-> | Hj0].
  - assert (Hlen_inner :
        Zlength (replace_Znth 0 (Znth 0 l default_point) l) = Zlength l).
    { rewrite Zlength_replace_Znth; reflexivity. }
    rewrite Znth_replace_Znth_Same by (rewrite Hlen_inner; lia).
    reflexivity.
  - assert (Hlen_inner :
        Zlength (replace_Znth 0 (Znth j l default_point) l) = Zlength l).
    { rewrite Zlength_replace_Znth; reflexivity. }
    rewrite Znth_replace_Znth_Diff.
    rewrite Znth_replace_Znth_Same by lia.
    reflexivity.
    + rewrite Hlen_inner; lia.
    + rewrite Hlen_inner; lia.
    + lia.
Qed.

Lemma point_swap_Znth_right : forall l j,
  0 <= j < Zlength l ->
  Znth j (point_swap l 0 j) default_point = Znth 0 l default_point.
Proof.
  intros l j Hj.
  unfold point_swap.
  assert (Hlen_inner :
      Zlength (replace_Znth 0 (Znth j l default_point) l) = Zlength l).
  { rewrite Zlength_replace_Znth; reflexivity. }
  rewrite Znth_replace_Znth_Same by (rewrite Hlen_inner; lia).
  reflexivity.
Qed.

Lemma point_swap_Znth_other : forall l j k,
  0 <= j < Zlength l ->
  0 <= k < Zlength l ->
  k <> 0 ->
  k <> j ->
  Znth k (point_swap l 0 j) default_point = Znth k l default_point.
Proof.
  intros l j k Hj Hk Hk0 Hkj.
  unfold point_swap.
  assert (Hlen_inner :
      Zlength (replace_Znth 0 (Znth j l default_point) l) = Zlength l).
  { rewrite Zlength_replace_Znth; reflexivity. }
  rewrite Znth_replace_Znth_Diff.
  rewrite Znth_replace_Znth_Diff by lia.
  reflexivity.
  - rewrite Hlen_inner; lia.
  - rewrite Hlen_inner; lia.
  - lia.
Qed.

Lemma PointLeftmostPrefix_leftmost_point_swap : forall l pivot_idx n,
  Zlength l = n ->
  PointLeftmostPrefix l pivot_idx n ->
  leftmost (Znth 0 (point_swap l 0 pivot_idx) default_point)
           (point_swap l 0 pivot_idx).
Proof.
  intros l pivot_idx n Hlen Hprefix.
  unfold PointLeftmostPrefix in Hprefix.
  destruct Hprefix as [Hidx [Hin Hmin]].
  assert (Hpivot : 0 <= pivot_idx < Zlength l) by lia.
  rewrite point_swap_Znth_left by exact Hpivot.
  unfold leftmost.
  apply Forall_Znth_intro with (d := default_point).
  intros k Hk.
  rewrite Zlength_point_swap in Hk.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - rewrite point_swap_Znth_left by exact Hpivot.
    unfold point_leftdown, x, y in Hmin.
    specialize (Hmin pivot_idx).
    apply Hmin.
    lia.
  - destruct (Z.eq_dec k pivot_idx) as [-> | Hkp].
    + rewrite point_swap_Znth_right by exact Hpivot.
      specialize (Hmin 0).
      unfold point_leftdown, x, y in Hmin.
      apply Hmin.
      lia.
    + rewrite point_swap_Znth_other by (try exact Hpivot; try exact Hk; lia).
      specialize (Hmin k).
      unfold point_leftdown, x, y in Hmin.
      apply Hmin.
      lia.
Qed.

Lemma PointLeftmostPrefix_sorted_tail_leftmost : forall l pivot_idx n pts_pivot pts_sorted tail_sorted pivot0,
  Zlength l = n ->
  PointLeftmostPrefix l pivot_idx n ->
  pts_pivot = point_swap l 0 pivot_idx ->
  pivot0 = Znth 0 pts_pivot default_point ->
  Zlength pts_sorted = n ->
  tail_sorted = sublist 1 n pts_sorted ->
  PointPermutation pts_pivot pts_sorted ->
  leftmost pivot0 (rev tail_sorted).
Proof.
  intros l pivot_idx n pts_pivot pts_sorted tail_sorted pivot0
         Hlen Hprefix Hpivot_list Hpivot0 Hsorted_len Htail Hperm.
  subst pts_pivot pivot0 tail_sorted.
  assert (Hn_pos : 1 <= n).
  { unfold PointLeftmostPrefix in Hprefix; lia. }
  apply leftmost_rev.
  apply leftmost_sublist.
  - lia.
  - lia.
  - eapply leftmost_permutation.
    + exact Hperm.
    + eapply PointLeftmostPrefix_leftmost_point_swap; eauto.
Qed.

Lemma point_cmp_polar_refl : forall gp a,
  point_cmp_polar gp a a = 0.
Proof.
  intros gp a.
  unfold point_cmp_polar.
  rewrite point_cross_same_right.
  destruct (Z_gt_dec 0 0); [lia |].
  destruct (Z_lt_dec 0 0); [lia |].
  unfold point_at_mid, point_dot, dot_prod, build_vec, x, y.
  simpl.
  replace ((point_x a - point_x a) * (point_x gp - point_x a) +
           (point_y a - point_y a) * (point_y gp - point_y a)) with 0.
  2: lia.
  destruct (Z_gt_dec 0 0); [lia |].
  destruct (Z_lt_dec 0 0); [lia |].
  apply point_cmp_xy_eq; reflexivity.
Qed.
