Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.convex_hull Require Import point_array_strategy_goal.
Import naive_C_Rules.
Require Import SimpleC.EE.convex_hull.convex_hull_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma point_array_strategy0_correctness : point_array_strategy0.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l2.
  cancel.
Qed.

Lemma point_array_strategy1_correctness : point_array_strategy1.
Proof.
  pre_process_default.
  Intros_p H1.
  subst l2.
  cancel.
Qed.

Lemma point_array_strategy2_correctness : point_array_strategy2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PointArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + cancel (PointArray.undef_seg p (x + 1) y).
      apply_sepcon_adjoint.
      elim_emp.
      unfold StorePointAsElement.undefstoreA, undef_point.
      cancel.
Qed.

Lemma point_array_strategy3_correctness : point_array_strategy3.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PointArray.undef_seg_split_to_undef_missing_i p x x y).
  - dump_pre_spatial.
    lia.
  - sep_apply_l_atomic (PointArray.undef_missing_i_to_undef_seg_head p x y).
    + dump_pre_spatial.
      lia.
    + unfold StorePointAsElement.undefstoreA, undef_point.
      cancel (PointArray.undef_seg p (x + 1) y).
      cancel (((&(((p + (x * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |->_)).
      apply_sepcon_adjoint.
      elim_emp.
      cancel.
Qed.

Lemma point_array_strategy4_correctness : point_array_strategy4.
Proof.
  pre_process_default.
  subst y.
  sep_apply_l_atomic (point_array_store_undef_tail_to_undef_seg p x z a).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy5_correctness : point_array_strategy5.
Proof.
  pre_process_default.
  sep_apply_l_atomic (point_array_seg_snoc_store p x y l a).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy6_correctness : point_array_strategy6.
Proof.
  pre_process_default.
Qed.

Lemma point_array_strategy7_correctness : point_array_strategy7.
Proof.
  pre_process_default.
Qed.

Lemma point_array_strategy8_correctness : point_array_strategy8.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PointArray.full_split_to_missing_i p i n l default_point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i 0 n l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> point_y (Znth i l default_point))).
    apply_sepcon_adjoint.
    Intros_p Hvx.
    subst vx.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy9_correctness : point_array_strategy9.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PointArray.full_split_to_missing_i p i n l default_point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i 0 n l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> point_x (Znth i l default_point))).
    apply_sepcon_adjoint.
    Intros_p Hvy.
    subst vy.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy10_correctness : point_array_strategy10.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PointArray.seg_split_to_missing_i p x i y l default_point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i x y l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "y")) # Int |-> point_y (Znth (i - x) l default_point))).
    apply_sepcon_adjoint.
    Intros_p Hvx.
    subst vx.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy11_correctness : point_array_strategy11.
Proof.
  pre_process_default.
  sep_apply_l_atomic (PointArray.seg_split_to_missing_i p x i y l default_point).
  - dump_pre_spatial.
    lia.
  - unfold StorePointAsElement.storeA, store_point.
    cancel (PointArray.missing_i p i x y l).
    cancel (((&(((p + (i * sizeof( "Point" ) ) )) # "Point" ->ₛ "x")) # Int |-> point_x (Znth (i - x) l default_point))).
    apply_sepcon_adjoint.
    Intros_p Hvy.
    subst vy.
    elim_emp.
    cancel.
Qed.

Lemma point_array_strategy12_correctness : point_array_strategy12.
Proof.
  pre_process_default.
  assert (Heta :
    point_mk (point_x (Znth i l default_point))
             (point_y (Znth i l default_point)) =
    Znth i l default_point).
  { destruct (Znth i l default_point); reflexivity. }
  rewrite Heta.
  sep_apply_l_atomic (point_array_store_missing_merge_to_full p i n l default_point).
  - dump_pre_spatial.
    lia.
  - cancel.
Qed.

Lemma point_array_strategy13_correctness : point_array_strategy13.
Proof.
  pre_process_default.
  assert (Heta :
    point_mk (point_x (Znth (i - x) l default_point))
             (point_y (Znth (i - x) l default_point)) =
    Znth (i - x) l default_point).
  { destruct (Znth (i - x) l default_point); reflexivity. }
  rewrite Heta.
  eapply derivable1_trans.
  - apply derivable1_sepcon_comm.
  - eapply derivable1_trans.
    + apply derivable1_sepcon_mono.
      * unfold StorePointAsElement.storeA.
        apply derivable1_refl.
      * apply derivable1_refl.
    + eapply derivable1_trans.
      * apply (PointArray.missing_i_merge_to_seg p x i y (Znth (i - x) l default_point) l).
        lia.
      * rewrite replace_Znth_Znth by lia.
        apply derivable1_refl.
Qed.

Lemma point_array_strategy14_correctness : point_array_strategy14.
Proof.
  pre_process_default.
Qed.

Lemma point_array_strategy15_correctness : point_array_strategy15.
Proof.
  pre_process_default.
Qed.
