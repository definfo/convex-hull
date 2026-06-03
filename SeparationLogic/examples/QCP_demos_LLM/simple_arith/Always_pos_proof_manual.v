Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import Always_pos_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import Apos_lib.
Local Open Scope sac.

Lemma proof_of_Always_positive_simple_return_wit_1 : Always_positive_simple_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * reflexivity.
      * destruct (Z_gt_le_dec a_pre 0).
        -- lia.
        -- reflexivity.
Qed.

Lemma proof_of_Always_positive_simple_return_wit_2 : Always_positive_simple_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * assert (0 <= b_pre * b_pre) as Hsq.
        { destruct (Z_le_gt_dec 0 b_pre).
          - apply Z.mul_nonneg_nonneg; lia.
          - apply Z.mul_nonpos_nonpos; lia.
        }
        pose proof (Z.quot_rem (b_pre * b_pre) 4 ltac:(lia)) as Hqr.
        pose proof (Z.rem_bound_pos (b_pre * b_pre) 4 Hsq ltac:(lia)) as Hrem.
        assert (b_pre * b_pre - 4 * a_pre * c_pre < 0) by lia.
        lia.
      * destruct (Z_gt_le_dec a_pre 0).
        -- reflexivity.
        -- lia.
Qed.

Lemma proof_of_Always_positive_simple_return_wit_3 : Always_positive_simple_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * reflexivity.
      * assert (0 <= b_pre * b_pre) as Hsq.
        { destruct (Z_le_gt_dec 0 b_pre).
          - apply Z.mul_nonneg_nonneg; lia.
          - apply Z.mul_nonpos_nonpos; lia.
        }
        pose proof (Z.quot_rem (b_pre * b_pre) 4 ltac:(lia)) as Hqr.
        pose proof (Z.rem_bound_pos (b_pre * b_pre) 4 Hsq ltac:(lia)) as Hrem.
        assert (b_pre * b_pre - 4 * a_pre * c_pre >= 0) by lia.
        lia.
Qed.

Lemma proof_of_Always_positive_simple_return_wit_4 : Always_positive_simple_return_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + reflexivity.
    + lia.
Qed.

Lemma proof_of_Always_positive_simple_safety_wit_4 : Always_positive_simple_safety_wit_4.
Proof.
  pre_process.
Qed. 

Lemma proof_of_Always_positive_simple_safety_wit_6 : Always_positive_simple_safety_wit_6.
Proof. pre_process. Qed.  

Lemma proof_of_Always_positive_entail_wit_2 : Always_positive_entail_wit_2.
Proof. 
  pre_process.
Qed.  

Lemma proof_of_Always_positive_return_wit_1 : Always_positive_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * reflexivity.
      * destruct (Z_gt_le_dec a_pre 0).
        -- lia.
        -- reflexivity.
Qed.

Lemma proof_of_Always_positive_return_wit_2 : Always_positive_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * assert (0 < delta2) by lia.
        assert (1 <= d) by lia.
        assert (1 * delta2 <= d * delta2) as Hd2 by (apply Z.mul_le_mono_nonneg_r; lia).
        assert (delta1 < d * delta2) by lia.
        assert (b_pre * b_pre - 4 * a_pre * c_pre = delta0 - 4 * delta2) as Heq0.
        { rewrite H11, H12. ring. }
        assert (delta0 - 4 * delta2 = delta1 - d * delta2) as Heq1.
        { rewrite H13. ring. }
        lia.
      * destruct (Z_gt_le_dec a_pre 0).
        -- reflexivity.
        -- lia.
Qed.

Lemma proof_of_Always_positive_return_wit_3 : Always_positive_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * reflexivity.
      * assert (b_pre * b_pre - 4 * a_pre * c_pre = delta0 - 4 * delta2) as Heq0.
        { rewrite H11, H12. ring. }
        assert (delta0 - 4 * delta2 = delta1 - d * delta2) as Heq1.
        { rewrite H13. ring. }
        lia.
Qed.

Lemma proof_of_Always_positive_return_wit_4 : Always_positive_return_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + lia.
    + destruct (Z_ge_lt_dec (b_pre * b_pre - 4 * a_pre * c_pre) 0).
      * reflexivity.
      * assert (0 <= b_pre * b_pre) as Hsq.
        { destruct (Z_le_gt_dec 0 b_pre).
          - apply Z.mul_nonneg_nonneg; lia.
          - apply Z.mul_nonpos_nonpos; lia.
        }
        assert (b_pre * b_pre - 4 * a_pre * c_pre >= 0) as Hdisc by lia.
        lia.
Qed.

Lemma proof_of_Always_positive_return_wit_5 : Always_positive_return_wit_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    unfold Always_pos.
    destruct (Z.eq_dec a_pre 0).
    + reflexivity.
    + lia.
Qed.

Lemma proof_of_Always_positive_safety_wit_3 : Always_positive_safety_wit_3.
Proof. pre_process. Qed. 

Lemma proof_of_Always_positive_safety_wit_4 : Always_positive_safety_wit_4.
Proof. pre_process. Qed. 

Lemma proof_of_Always_positive_safety_wit_8 : Always_positive_safety_wit_8.
Proof. pre_process. Qed. 