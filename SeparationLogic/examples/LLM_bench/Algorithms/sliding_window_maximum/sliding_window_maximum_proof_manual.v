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
From SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum Require Import sliding_window_maximum_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sliding_window_maximum.sliding_window_maximum_lib.
Local Open Scope sac.

Lemma proof_of_maxSlidingWindow_entail_wit_1 : maxSlidingWindow_entail_wit_1.
Proof.
  pre_process.
  Exists nil.
  Exists q0.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.full q_pre n_pre q0).
    sep_apply (IntArray.undef_full_split_to_undef_seg out_pre 0 (n_pre - k_pre + 1)).
    + cancel (IntArray.undef_seg out_pre 0 (n_pre - k_pre + 1)).
      rewrite (IntArray.undef_seg_empty out_pre 0).
      rewrite (IntArray.seg_empty out_pre 0 0).
      entailer!.
    + lia.
  - entailer!.
    + unfold SWMQueueState, SWMQueueEntriesValid, SWMQueueIndexIncreasing,
        SWMQueueValueDecreasing, SWMQueueCoversWindow.
      repeat split; intros; try lia.
    + unfold SWMOutputPrefix.
      repeat split; try lia; simpl; intros; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_2 : maxSlidingWindow_entail_wit_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + unfold SWMQueueState in H16.
      destruct H16 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      intros p r Hp. apply Hdec. lia.
    + unfold SWMQueueState in H16.
      destruct H16 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      intros p r Hp. apply Hinc. lia.
    + unfold SWMQueueState in H16.
      destruct H16 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      intros pos Hpos.
      unfold SWMQueueEntriesValid in Hvalid.
      specialize (Hvalid pos Hpos) as (? & ? & ?). lia.
    + unfold SWMQueueState in H16.
      unfold SWMQueueDropLoopState.
      destruct H16 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover & Hfront).
      repeat split; try lia; try assumption.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueCoversAfterDrop.
        intros idx Hidx0 HidxLen Hrange.
        unfold SWMQueueCoversWindow in Hcover.
        apply Hcover; lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_3 : maxSlidingWindow_entail_wit_3.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + intros p r Hp. apply H20. lia.
    + intros p r Hp. apply H19. lia.
    + intros pos Hpos. apply H18. lia.
    + intros pos Hpos. apply H17. lia.
    + unfold SWMQueueDropLoopState in *.
      destruct H16 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover).
      repeat split; try lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueIndexIncreasing in *.
        intros p r Hp. apply Hinc. lia.
      * unfold SWMQueueValueDecreasing in *.
        intros p r Hp. apply Hdec. lia.
      * unfold SWMQueueCoversAfterDrop in *.
        intros idx Hidx0 HidxLen Hrange.
        destruct (Hcover idx Hidx0 HidxLen Hrange) as
          [pos0 [[HposHead HposTail] [HidxLe [HposI Hval]]]].
        assert (pos0 <> head) by (intro Heq; subst; lia).
        exists pos0. repeat split; try lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_1 : maxSlidingWindow_entail_wit_4_1.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    unfold SWMQueueAfterDrop, SWMQueueDropLoopState in *.
    destruct H15 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
      HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover).
    repeat split; try lia; try assumption.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_4_2 : maxSlidingWindow_entail_wit_4_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + intros pos Hpos.
      specialize (H18 pos Hpos) as Hrange.
      assert (pos = head \/ head < pos) as [-> | Hgt] by lia.
      * lia.
      * specialize (H19 head pos ltac:(lia)) as Hinc. lia.
    + intro Hnonempty.
      assert (Hpos : head <= tail - 1 < tail) by lia.
      specialize (H17 (tail - 1) Hpos) as Hlast. lia.
    + unfold SWMQueueAfterDrop, SWMQueueDropLoopState in *.
      destruct H16 as (HK1 & HK2 & HI0 & HIle & HH0 & HHtail &
        HtailLen & HtailI & Hvalid & Hinc & Hdec & Hcover).
      repeat split; try lia; try assumption.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
      * assert (pos = head \/ head < pos) as [-> | Hgt] by lia.
        -- lia.
        -- unfold SWMQueueIndexIncreasing in Hinc.
           specialize (Hinc head pos ltac:(lia)) as HincHead. lia.
      * unfold SWMQueueEntriesValid in Hvalid.
        specialize (Hvalid pos ltac:(lia)) as (? & ? & ?). lia.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_5 : maxSlidingWindow_entail_wit_5.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
    cancel (IntArray.full q_pre n_pre q_l_2).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial;
                  eapply SWMQueueAfterDrop_to_PendingState; eauto;
                  rewrite H2; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_6 : maxSlidingWindow_entail_wit_6.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.full q_pre n_pre q_l_2).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial;
                  eapply SWMQueuePendingState_pop_back_dominated; eauto
                | dump_pre_spatial; intros;
                  specialize (H17 (tail - 1 - 1) ltac:(lia)); lia
                | dump_pre_spatial; intros; eapply H17; lia
                | dump_pre_spatial; intros; eapply H19; lia
                | dump_pre_spatial; intros; eapply H20; lia
                | dump_pre_spatial; intros; eapply H21; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_7_1 : maxSlidingWindow_entail_wit_7_1.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
    cancel (IntArray.full q_pre n_pre q_l_2).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial; intros; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_7_2 : maxSlidingWindow_entail_wit_7_2.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.full q_pre n_pre q_l_2).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
  - split_pures;
      try solve [dump_pre_spatial; eauto; try lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_8 : maxSlidingWindow_entail_wit_8.
Proof.
  pre_process.
  Exists out_l_2. Exists (replace_Znth tail i q_l_2).
  split_pure_spatial.
  - cancel (IntArray.full q_pre n_pre (replace_Znth tail i q_l_2)).
    cancel (IntArray.full nums_pre n_pre l).
    cancel (IntArray.seg out_pre 0 out_idx out_l_2).
    cancel (IntArray.undef_seg out_pre out_idx (n_pre - k_pre + 1)).
  - assert (Hpush :
        SWMQueueState l (replace_Znth tail i q_l_2) head (tail + 1) (i + 1) k_pre).
    {
      eapply SWMQueuePendingState_push_current; eauto.
      - rewrite H3, H2. reflexivity.
      - rewrite H2. lia.
    }
    pose proof Hpush as Hpush_components.
    unfold SWMQueueState in Hpush_components.
    destruct Hpush_components as
      [_ [_ [_ [_ [_ [_ [_ [_ [Hnew_valid _]]]]]]]]].
    split_pures;
      try solve [dump_pre_spatial; eauto; try lia
                | dump_pre_spatial; rewrite Zlength_replace_Znth; eauto
                | dump_pre_spatial; exact Hpush
                | dump_pre_spatial; intros pos Hpos;
                  specialize (Hnew_valid pos Hpos); rewrite H2 in Hnew_valid; lia].
Qed. 

Lemma proof_of_maxSlidingWindow_entail_wit_9 : maxSlidingWindow_entail_wit_9.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    + replace (i - k_pre + 1) with (i + 1 - k_pre) by lia.
      eapply SWMQueueState_window_max; [exact H15 | exact H8 | lia].
    + destruct (H16 head ltac:(lia)) as [_ Hq]; exact Hq.
    + destruct (H16 head ltac:(lia)) as [Hq _]; exact Hq.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_10 : maxSlidingWindow_entail_wit_10.
Proof.
  pre_process.
  Exists (out_l_2 ++ Znth (Znth head q_l_2 0) l 0 :: nil). Exists q_l_2.
  split_pure_spatial.
  - repeat cancel.
  - entailer!.
    apply SWMOutputPrefix_snoc; [exact H15 | lia |].
    replace out_idx with (i - k_pre + 1) by lia.
    replace (i - k_pre + 1 + k_pre) with (i + 1) by lia.
    exact H18.
Qed.

Lemma proof_of_maxSlidingWindow_entail_wit_13 : maxSlidingWindow_entail_wit_13.
Proof.
  pre_process.
  Exists out_l_2. Exists q_l_2.
  split_pure_spatial.
  - assert (Hi : i = n_pre) by lia; subst i.
    assert (Houtidx : out_idx = n_pre - k_pre + 1) by (apply H13; lia).
    rewrite Houtidx.
    repeat cancel.
    unfold IntArray.full, IntArray.seg, IntArray.undef_seg.
    replace (Z.to_nat (n_pre - k_pre + 1 - (n_pre - k_pre + 1))) with O by lia.
    simpl; entailer!.
  - entailer!.
    apply SWMOutputPrefix_complete with (out_idx := out_idx).
    + exact H15.
    + rewrite H3.
      assert (Hi : i = n_pre) by lia; subst i.
      apply H13; lia.
Qed.
