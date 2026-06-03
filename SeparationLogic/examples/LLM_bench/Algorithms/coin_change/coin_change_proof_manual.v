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
From SimpleC.EE.LLM_bench.Algorithms.coin_change Require Import coin_change_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_lib.
Local Open Scope sac.

Lemma proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - sep_apply (IntArray.seg_single dp_pre 0 1).
    replace (0 + 1) with 1 by lia.
    cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.seg dp_pre 0 1 (1 :: nil)).
    cancel (IntArray.undef_seg dp_pre 1 (amount_pre + 1)).
  - split_pures; dump_pre_spatial; auto.
Qed.

Lemma proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2.
Proof.
  pre_process.
  Exists (1 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.seg dp_pre 0 1 (1 :: nil)).
    cancel (IntArray.undef_seg dp_pre 1 (amount_pre + 1)).
  - split_pures.
    all: try (dump_pre_spatial; auto; try lia).
    unfold DpPrefixZeroed.
    repeat split; try lia.
    rewrite Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3.
Proof.
  pre_process.
  Exists (dp_l_2 ++ 0 :: nil).
  split_pure_spatial.
  - cancel.
    reflexivity.
  - prop_apply_p (store_array_rec_Zlength Z
      (fun (x lo a : Z) => (x + lo * sizeof( INT )) # Int |-> a)
      dp_pre 0 (j + 1) (dp_l_2 ++ 0 :: nil)).
    Intros.
    entailer!.
    eapply DpPrefixZeroed_snoc_zero; eauto; lia.
Qed. 

Lemma proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4.
Proof.
  pre_process.
  assert (j = amount_pre + 1) by lia.
  subst j.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel.
    unfold IntArray.full, IntArray.undef_seg, store_array.
    replace (Z.to_nat (amount_pre + 1 - (amount_pre + 1))) with O by lia.
    simpl.
    Intros.
    reflexivity.
  - entailer!.
    apply DpPrefixZeroed_to_DpReachableTable_nil; auto.
Qed. 

Lemma proof_of_coinChange_entail_wit_5 : coinChange_entail_wit_5.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - reflexivity.
  - entailer!.
Qed. 

Lemma proof_of_coinChange_entail_wit_6 : coinChange_entail_wit_6.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures.
    all: dump_pre_spatial;
      try solve [auto | lia | specialize (H8 i ltac:(lia)); lia].
Qed. 

Lemma proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures.
    all: dump_pre_spatial;
      try solve [auto | lia].
    unfold DpCoinInnerProgress, DpReachableTable in *.
    destruct H10 as [_ [Hlen Hreach]].
    repeat split; try lia.
    + intro Hz.
      pose proof (ReachableAmount_app_single_below
                    (sublist 0 i coins_l) coin k ltac:(lia) H10)
        as [_ Hold_new].
      apply Hold_new.
      apply (proj1 (Hreach k ltac:(lia))).
      exact Hz.
    + intro Hnew.
      pose proof (ReachableAmount_app_single_below
                    (sublist 0 i coins_l) coin k ltac:(lia) H10)
        as [Hnew_old _].
      apply (proj2 (Hreach k ltac:(lia))).
      apply Hnew_old.
      exact Hnew.
    + intro Hz.
      apply (proj1 (Hreach k ltac:(lia))).
      exact Hz.
    + intro Hr.
      apply (proj2 (Hreach k ltac:(lia))).
      exact Hr.
Qed. 

Lemma proof_of_coinChange_entail_wit_8_1 : coinChange_entail_wit_8_1.
Proof.
  pre_process.
  Exists (replace_Znth j 1 dp_l_2).
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1)
              (replace_Znth j 1 dp_l_2)).
  - split_pures.
    all: dump_pre_spatial;
      try solve [auto | lia].
    eapply DpCoinInnerProgress_replace_current; eauto; lia.
Qed. 

Lemma proof_of_coinChange_entail_wit_8_2 : coinChange_entail_wit_8_2.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
    cancel (IntArray.full coins_pre coinsSize_pre coins_l).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    unfold DpCoinInnerProgress in *.
    destruct H13 as
      (Hcoin_pos & Hcoin_le_j & Hj_le_amount & Hdp_len &
       Hprefix & Hsuffix).
    repeat split; try lia; try exact Hdp_len.
    + assert (Hk_case : k < j \/ k = j) by lia.
      destruct Hk_case as [Hk_lt | Hk_eq].
      * apply (proj1 (Hprefix k ltac:(lia))).
      * subst k.
        intro Hcell_j.
        apply ReachableAmount_app_l.
        apply (proj1 (Hsuffix j ltac:(lia))); assumption.
    + assert (Hk_case : k < j \/ k = j) by lia.
      destruct Hk_case as [Hk_lt | Hk_eq].
      * apply (proj2 (Hprefix k ltac:(lia))).
      * subst k.
        intro Hreach_j.
        pose proof (Hprefix (j - coin)) as Hprefix_minus.
        assert (Hminus_range : 0 <= j - coin < j) by lia.
        specialize (Hprefix_minus Hminus_range).
        assert (Hnot_minus :
          ~ ReachableAmount (app (sublist 0 i coins_l) (cons coin nil))
              (j - coin)).
        {
          intro Hreach_minus.
          apply (proj2 Hprefix_minus) in Hreach_minus.
          rewrite H in Hreach_minus.
          contradiction Hreach_minus; reflexivity.
        }
        pose proof
          (ReachableAmount_app_single_inv
             (sublist 0 i coins_l) coin j Hcoin_pos Hreach_j)
          as [Hprev_j | [_ Hminus]].
        -- apply (proj2 (Hsuffix j ltac:(lia))); assumption.
        -- exfalso; apply Hnot_minus; assumption.
    + apply (proj1 (Hsuffix k ltac:(lia))).
    + apply (proj2 (Hsuffix k ltac:(lia))).
Qed. 

Lemma proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + assert (j = amount_pre + 1) by lia.
      subst j.
      rewrite (sublist_0_succ_app 0 coins_l i) by lia.
      rewrite <- H7.
      unfold DpReachableTable, DpCoinInnerProgress in *.
      destruct H12 as
        (Hcoin_pos & Hcoin_le_j & Hj_le_amount & Hdp_len &
         Hprefix & Hsuffix).
      repeat split; try lia; try exact Hdp_len.
      * apply (proj1 (Hprefix k ltac:(lia))).
      * apply (proj2 (Hprefix k ltac:(lia))).
Qed. 

Lemma proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + rewrite (sublist_0_succ_app 0 coins_l i) by lia.
      rewrite <- H7.
      unfold DpReachableTable in *.
      destruct H10 as (Hhi_nonneg & Hdp_len & Htable).
      repeat split; try lia; try exact Hdp_len.
      * specialize (Htable k ltac:(lia)).
        intro Hcell.
        apply ReachableAmount_app_l.
        apply (proj1 Htable); assumption.
      * specialize (Htable k ltac:(lia)).
        intro Hreach.
        apply (proj2 Htable).
        eapply ReachableAmount_app_single_lt; eauto; lia.
Qed. 

Lemma proof_of_coinChange_entail_wit_11 : coinChange_entail_wit_11.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures; dump_pre_spatial; try lia; auto.
    + assert (i = coinsSize_pre) by lia.
      subst i.
      rewrite (sublist_self coins_l coinsSize_pre (eq_sym H4)) in H7.
      exact H7.
    + unfold NoReachableAbove.
      split; [lia | intros k Hk HR; lia].
Qed.

Lemma proof_of_coinChange_entail_wit_12 : coinChange_entail_wit_12.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures; dump_pre_spatial; try lia; auto.
    unfold NoReachableAbove in *.
    destruct H9 as [Hbounds Hno].
    split; [lia |].
    intros k Hk HR.
    destruct (Z.eq_dec k res) as [Heq | Hneq].
    + subst k.
      unfold DpReachableTable in H8.
      destruct H8 as [_ [_ Htab]].
      pose proof (proj2 (Htab res ltac:(lia)) HR) as Hnz.
      rewrite H in Hnz.
      contradiction.
    + apply (Hno k); lia || exact HR.
Qed.

Lemma proof_of_coinChange_entail_wit_13_1 : coinChange_entail_wit_13_1.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures.
    all: try (dump_pre_spatial; auto).
    apply MaxReachableAmount_intro_no_above.
    + replace res with 0 by lia; constructor.
    + lia.
    + lia.
    + exact H8.
Qed.

Lemma proof_of_coinChange_entail_wit_13_2 : coinChange_entail_wit_13_2.
Proof.
  pre_process.
  Exists dp_l_2.
  split_pure_spatial.
  - cancel (IntArray.full coins_pre coinsSize_pre coins_l).
    cancel (IntArray.full dp_pre (amount_pre + 1) dp_l_2).
  - split_pures.
    all: try (dump_pre_spatial; auto).
    apply MaxReachableAmount_intro_no_above.
    + unfold DpReachableTable in H8.
      destruct H8 as [_ [_ Htable]].
      apply (proj1 (Htable res ltac:(lia))); exact H.
    + lia.
    + lia.
    + exact H9.
Qed.
