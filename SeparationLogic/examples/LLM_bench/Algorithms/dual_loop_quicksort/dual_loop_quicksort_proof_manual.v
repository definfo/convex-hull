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
From SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort Require Import dual_loop_quicksort_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.dual_loop_quicksort.dual_loop_quicksort_lib.
Local Open Scope sac.

Lemma proof_of_swap_return_wit_1 : swap_return_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_1 : partition_two_loop_entail_wit_1.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_outer_inv, same_outside_range.
    repeat split; try lia; try reflexivity.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_2 : partition_two_loop_entail_wit_2.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_3 : partition_two_loop_entail_wit_3.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_right_scan_inv in *.
    destruct H11 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hile [Hmid Hright]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
    intros k Hk.
    assert (j <= k) by lia.
    destruct (Z.eq_dec k j) as [-> | Hneq].
    + lia.
    + apply Hright. lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_4_1 : partition_two_loop_entail_wit_4_1.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv, partition_right_scan_inv in *.
    destruct H11 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hile [Hmid Hright]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_4_2 : partition_two_loop_entail_wit_4_2.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv, partition_right_scan_inv in *.
    destruct H10 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hile [Hmid Hright]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_5 : partition_two_loop_entail_wit_5.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv in *.
    destruct H11 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hmid [Hright [Hjlt Hieq]]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
    + intros k Hk.
      assert (k < i \/ k = i) as [Hlt | ->] by lia.
      * apply Hmid. lia.
      * exact H.
    + intros Heq.
      subst.
      pose proof (Hjlt H0).
      lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_6_1 : partition_two_loop_entail_wit_6_1.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    unfold partition_left_scan_inv, partition_outer_inv in *.
    destruct H11 as [HPerm [Hsame [Hzlow [[Hloi Hij] [Hjhi [Hmid [Hright [Hjlt Hieq]]]]]]]].
    destruct Hsame as [Hlen Hsame].
    repeat split; try assumption; try lia.
Qed.

Lemma proof_of_partition_two_loop_entail_wit_6_2 : partition_two_loop_entail_wit_6_2.
Proof.
  pre_process.
  Exists (replace_Znth j (Znth i l1_2 0)
            (replace_Znth i (Znth j l1_2 0) l1_2)).
  split_pure_spatial.
  - cancel.
  - entailer!.
    lazymatch goal with
    | Hinv : partition_left_scan_inv _ _ _ _ _ _ _ |- _ =>
        let Hhigh1 := fresh "Hhigh1" in
        assert (Hhigh1 : high_pre < Zlength l) by
          match goal with
          | Hlenl : Zlength l = n_pre |- _ => rewrite Hlenl; lia
          end;
        eapply partition_swap_left_scan_to_outer_inv; eauto
    end.
Qed.

Lemma proof_of_partition_two_loop_return_wit_1 : partition_two_loop_return_wit_1.
Proof.
  pre_process.
  Exists (replace_Znth i (Znth low_pre l1_2 0)
            (replace_Znth low_pre (Znth i l1_2 0) l1_2)).
  split_pure_spatial.
  - cancel.
  - entailer!.
    + lazymatch goal with
      | Hinv : partition_outer_inv _ _ _ _ _ _ _ |- _ =>
          let Hhigh1 := fresh "Hhigh1" in
          assert (Hhigh1 : high_pre < Zlength l) by
            match goal with
            | Hlenl : Zlength l = n_pre |- _ => rewrite Hlenl; lia
            end;
          eapply partition_outer_exit_swap_yields_partitioned_at; eauto
      end.
    + lazymatch goal with
      | Hinv : partition_outer_inv _ _ _ _ _ _ _ |- _ =>
          let Htmp := fresh "Htmp" in
          pose proof Hinv as Htmp;
          destruct Htmp as [_ [Hsame _]];
          let Hsame0 := fresh "Hsame0" in
          pose proof Hsame as Hsame0;
          destruct Hsame as [Hlen _];
          eapply same_outside_range_trans_local;
          [ exact Hsame0
          | apply same_outside_range_swap_inside_local;
            try lia;
            rewrite <- Hlen;
            match goal with
            | Hlenl : Zlength l = n_pre |- _ => rewrite Hlenl; lia
            end ]
      end.
    + let Htmp := fresh "Htmp" in
      lazymatch goal with
      | Hinv : partition_outer_inv _ _ _ _ _ _ _ |- _ => pose proof Hinv as Htmp
      end;
      destruct Htmp as [Hperm [Hsame _]];
      destruct Hsame as [Hlen _];
      destruct (Z.eq_dec low_pre i) as [Heq | Hneq].
      * subst i.
        rewrite replace_Znth_Znth by (rewrite Zlength_replace_Znth; rewrite <- Hlen; lia).
        rewrite replace_Znth_Znth by (rewrite <- Hlen; lia).
        exact Hperm.
      * eapply Permutation_trans.
        -- exact Hperm.
        -- apply swap_Znth_perm_local.
           rewrite <- Hlen.
           lia.
Qed.

Lemma proof_of_quicksort_range_return_wit_1 : quicksort_range_return_wit_1.
Proof.
  pre_process.
  Exists l1_4.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_4).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact H9.
      * eapply Permutation_trans.
        -- exact H3.
        -- exact H.
    + dump_pre_spatial.
      destruct H10 as [Hlen12 Heq12].
      destruct H4 as [Hlen23 Heq23].
      destruct H0 as [Hlen34 Heq34].
      assert (Hsame23_full : same_outside_range l1_2 l1_3 left_pre right_pre).
      {
        split.
        - exact Hlen23.
        - intros k Hk Hout.
          apply Heq23.
          + exact Hk.
          + destruct Hout as [Hlt | Hgt].
            * left. lia.
            * right. lia.
      }
      assert (Hsame34_full : same_outside_range l1_3 l1_4 left_pre right_pre).
      {
        split.
        - exact Hlen34.
        - intros k Hk Hout.
          apply Heq34.
          + exact Hk.
          + destruct Hout as [Hlt | Hgt].
            * left. lia.
            * right. lia.
      }
      eapply same_outside_range_trans_local.
      * exact (conj Hlen12 Heq12).
      * eapply same_outside_range_trans_local.
        -- exact Hsame23_full.
        -- exact Hsame34_full.
    + dump_pre_spatial.
      destruct H10 as [Hlen12 Heq12].
      destruct H4 as [Hlen23 Heq23].
      destruct H0 as [Hlen34 Heq34].
      assert (Hlen2 : Zlength l1_2 = n_pre).
      { rewrite <- Hlen12. exact H13. }
      assert (Hlen3 : Zlength l1_3 = n_pre).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hlen4 : Zlength l1_4 = n_pre).
      { rewrite <- Hlen34. exact Hlen3. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_left_local.
        - exact H3.
        - exact H16.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact H18.
        - exact H11.
      }
      assert (Hpart4 : partitioned_at l1_4 left_pre right_pre retval).
      {
        eapply partitioned_at_preserved_by_right_local.
        - exact H.
        - exact H16.
        - exact (conj Hlen34 Heq34).
        - rewrite Hlen3. exact H18.
        - exact Hpart3.
      }
      assert (Hleft4 : range_nondecreasing l1_4 left_pre (retval - 1)).
      {
        eapply range_nondecreasing_ext_local.
        - exact Hlen34.
        - intros k Hk.
          assert (Hklen : 0 <= k < Zlength l1_3).
          { rewrite Hlen3. lia. }
          apply Heq34.
          + exact Hklen.
          + left. lia.
        - exact H5.
      }
      eapply quicksort_partition_combine_both_sides_local.
      * exact H16.
      * rewrite Hlen4. exact H18.
      * split; [exact H7 | exact H8].
      * exact Hpart4.
      * exact Hleft4.
      * exact H1.
Qed.

Lemma proof_of_quicksort_range_return_wit_2 : quicksort_range_return_wit_2.
Proof.
  pre_process.
  Exists l1_3.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_3).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact H6.
      * exact H.
    + dump_pre_spatial.
      assert (Heqret : retval = left_pre) by lia.
      subst retval.
      destruct H7 as [Hlen12 Heq12].
      destruct H0 as [Hlen23 Heq23].
      split.
      * rewrite Hlen12. exact Hlen23.
      * intros k Hk Hout.
        rewrite (Heq23 k).
        -- apply Heq12. exact Hk. exact Hout.
        -- rewrite <- Hlen12. exact Hk.
        -- destruct Hout as [Hlt | Hgt].
           ++ left. lia.
           ++ right. lia.
    + dump_pre_spatial.
      assert (Heqret : retval = left_pre) by lia.
      subst retval.
      destruct H7 as [Hlen12 Heq12].
      destruct H0 as [Hlen23 Heq23].
      assert (Hlen2 : Zlength l1_2 = n_pre).
      { rewrite <- Hlen12. exact H10. }
      assert (Hlen3 : Zlength l1_3 = n_pre).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre left_pre).
      {
        eapply partitioned_at_preserved_by_right_local.
        - exact H.
        - exact H13.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact H15.
        - exact H8.
      }
      eapply quicksort_partition_combine_right_only_local.
      * exact H13.
      * rewrite Hlen3. exact H15.
      * reflexivity.
      * exact Hpart3.
      * exact H1.
Qed.

Lemma proof_of_quicksort_range_return_wit_3 : quicksort_range_return_wit_3.
Proof.
  pre_process.
  Exists l1_3.
  split_pure_spatial.
  - cancel (IntArray.full arr_pre n_pre l1_3).
  - split_pures.
    + dump_pre_spatial.
      eapply Permutation_trans.
      * exact H6.
      * exact H0.
    + dump_pre_spatial.
      assert (Heqret : retval = right_pre) by lia.
      subst retval.
      destruct H7 as [Hlen12 Heq12].
      destruct H1 as [Hlen23 Heq23].
      split.
      * rewrite Hlen12. exact Hlen23.
      * intros k Hk Hout.
        rewrite (Heq23 k).
        -- apply Heq12. exact Hk. exact Hout.
        -- rewrite <- Hlen12. exact Hk.
        -- destruct Hout as [Hlt | Hgt].
           ++ left. lia.
           ++ right. lia.
    + dump_pre_spatial.
      assert (Heqret : retval = right_pre) by lia.
      subst retval.
      destruct H7 as [Hlen12 Heq12].
      destruct H1 as [Hlen23 Heq23].
      assert (Hlen2 : Zlength l1_2 = n_pre).
      { rewrite <- Hlen12. exact H10. }
      assert (Hlen3 : Zlength l1_3 = n_pre).
      { rewrite <- Hlen23. exact Hlen2. }
      assert (Hpart3 : partitioned_at l1_3 left_pre right_pre right_pre).
      {
        eapply partitioned_at_preserved_by_left_local.
        - exact H0.
        - exact H13.
        - exact (conj Hlen23 Heq23).
        - rewrite Hlen2. exact H15.
        - exact H8.
      }
      eapply quicksort_partition_combine_left_only_local.
      * exact H13.
      * rewrite Hlen3. exact H15.
      * reflexivity.
      * exact Hpart3.
      * exact H2.
Qed.

Lemma proof_of_quicksort_range_return_wit_4 : quicksort_range_return_wit_4.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  cancel (IntArray.full arr_pre n_pre l).
  split_pures.
  - dump_pre_spatial.
    apply Permutation_refl.
  - dump_pre_spatial.
    unfold same_outside_range.
    split; [reflexivity|intros; reflexivity].
  - dump_pre_spatial.
    unfold range_nondecreasing.
    intros i j Hi Hij Hj.
    assert (i = j) by lia.
    subst.
    apply Z.le_refl.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_2_pure : quicksort_range_partial_solve_wit_2_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    pose proof (Permutation_length H2) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_3_pure : quicksort_range_partial_solve_wit_3_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    pose proof (Permutation_trans H6 H0) as Hperm.
    pose proof (Permutation_length Hperm) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_quicksort_range_partial_solve_wit_4_pure : quicksort_range_partial_solve_wit_4_pure.
Proof.
  pre_process.
  split_pures.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    lia.
  - dump_pre_spatial.
    pose proof (Permutation_length H3) as Hlen.
    rewrite !Zlength_correct in *.
    lia.
Qed.

Lemma proof_of_dual_loop_quicksort_return_wit_1 : dual_loop_quicksort_return_wit_1.
Proof.
  pre_process.
  Exists l1_2.
  split_pure_spatial.
  - cancel.
  - assert (Hlen1_2 : Zlength l1_2 = n_pre).
    {
      match goal with
      | Hperm : Permutation l l1_2, Hlenl : Zlength l = n_pre |- _ =>
          pose proof (Permutation_length Hperm) as Hperm_len;
          rewrite !Zlength_correct in *;
          lia
      end.
    }
    split_pures.
    + dump_pre_spatial.
      match goal with
      | Hperm : Permutation l l1_2 |- _ => exact Hperm
      end.
    + dump_pre_spatial.
      match goal with
      | Hrange : range_nondecreasing l1_2 0 (n_pre - 1) |- _ =>
          rewrite <- Hlen1_2 in Hrange;
          apply range_nondecreasing_full_to_Nondecreasing;
          exact Hrange
      end.
    + dump_pre_spatial.
      exact Hlen1_2.
Qed.

Lemma proof_of_dual_loop_quicksort_return_wit_2 : dual_loop_quicksort_return_wit_2.
Proof.
  pre_process.
  Exists l.
  split_pure_spatial.
  cancel (IntArray.full arr_pre n_pre l).
  split_pures.
  - dump_pre_spatial.
    apply Permutation_refl.
  - dump_pre_spatial.
    assert (n_pre = 0) by lia.
    rewrite H3 in H0.
    apply Zlength_nil_inv in H0.
    subst.
    unfold Nondecreasing.
    auto.
  - dump_pre_spatial.
    exact H0.
Qed.
