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

(* worker_helper_scratch_lib helper lemmas go below. *)

Lemma point_list_not_all_same_of_points_not_all_same_permutation_worker :
  forall base out,
    point_permutation base out ->
    points_not_all_same base ->
    point_list_not_all_same out.
Proof.
  intros base out Hperm Hnot.
  destruct Hnot as [i [j [Hi [Hj [_ Hdiff]]]]].
  assert (Hin_i_base : In (Znth i base default_point) base)
    by (apply Znth_In_range; lia).
  assert (Hin_j_base : In (Znth j base default_point) base)
    by (apply Znth_In_range; lia).
  assert (Hin_i_out : In (Znth i base default_point) out).
  { eapply Permutation_in; eauto. }
  assert (Hin_j_out : In (Znth j base default_point) out).
  { eapply Permutation_in; eauto. }
  destruct (In_Znth_Zlength out (Znth i base default_point) default_point
              Hin_i_out) as [oi [Hoi Hoi_eq]].
  destruct (In_Znth_Zlength out (Znth j base default_point) default_point
              Hin_j_out) as [oj [Hoj Hoj_eq]].
  exists oi, oj.
  split; [exact Hoi|].
  split; [exact Hoj|].
  intros Hsame.
  apply Hdiff.
  rewrite <- Hoi_eq.
  rewrite <- Hoj_eq.
  exact Hsame.
Qed.

Lemma andrew_lower_scan_inv_init_worker :
  forall sorted,
    1 <= Zlength sorted ->
    points_in_bound sorted ->
    point_list_not_all_same sorted ->
    andrew_lower_scan_inv sorted nil 0 0.
Proof.
  intros sorted Hlen Hbound Hnot.
  unfold andrew_lower_scan_inv.
  split; [split; lia|].
  split; [reflexivity|].
  split; [split; simpl; lia|].
  split; [constructor|].
  split; [constructor|].
  split; [exact Hnot|].
  split.
  {
    unfold andrew_lower_chain_geometry.
    split.
    {
      unfold point_chain_uses_range.
      repeat split; try lia.
      constructor.
    }
    split.
    {
      unfold point_chain_strictly_uses_range.
      exists (@nil Z).
      split.
      - unfold point_chain_indexed_by_range.
        split; [reflexivity|].
        intros pos Hpos.
        change (Zlength (@nil Point)) with 0 in Hpos.
        lia.
      - unfold point_indices_strict_increasing.
        intros a b Ha Hab Hb.
        change (Zlength (@nil Z)) with 0 in Hb.
        lia.
    }
    split.
    {
      unfold point_chain_starts_at.
      intros Hnil.
      change (Zlength (@nil Point)) with 0 in Hnil.
      lia.
    }
    split.
    {
      unfold point_chain_left_turns.
      intros idx Hidx Hidx2.
      change (Zlength (@nil Point)) with 0 in Hidx2.
      lia.
    }
    {
      unfold point_chain_left_envelope.
      intros edge_idx point_idx Hedge Hedge2 Hpoint.
      change (Zlength (@nil Point)) with 0 in Hedge2.
      lia.
    }
  }
  split.
  {
    unfold andrew_lower_append_ready.
    intros Hread _.
    unfold andrew_lower_chain_geometry.
    split.
    {
      unfold point_chain_uses_range.
      repeat split; try lia.
      constructor.
      - unfold point_from_sorted_range.
        exists 0.
        split; [lia | simpl; reflexivity].
      - constructor.
    }
    split.
    {
      unfold point_chain_strictly_uses_range.
      exists (0 :: nil).
      split.
      - unfold point_chain_indexed_by_range.
        split; [reflexivity|].
        intros pos Hpos.
        change (Zlength (nil ++ Znth 0 sorted default_point :: nil)) with 1 in Hpos.
        assert (pos = 0) by lia.
        subst pos.
        split.
        + change (Znth 0 (0 :: nil) 0) with 0.
          lia.
        + change (Znth 0 (nil ++ Znth 0 sorted default_point :: nil) default_point)
            with (Znth 0 sorted default_point).
          change (Znth 0 (0 :: nil) 0) with 0.
          reflexivity.
      - unfold point_indices_strict_increasing.
        intros a b Ha Hab Hb.
        change (Zlength (0 :: nil)) with 1 in Hb.
        lia.
    }
    split.
    {
      unfold point_chain_starts_at.
      intros _.
      simpl.
      reflexivity.
    }
    split.
    {
      unfold point_chain_left_turns.
      intros idx Hidx Hidx2.
      change (Zlength (nil ++ Znth 0 sorted default_point :: nil)) with 1 in Hidx2.
      lia.
    }
    {
      unfold point_chain_left_envelope.
      intros edge_idx point_idx Hedge Hedge2 Hpoint.
      change (Zlength (nil ++ Znth 0 sorted default_point :: nil)) with 1 in Hedge2.
      lia.
    }
  }
  intros Hdone.
  lia.
Qed.
