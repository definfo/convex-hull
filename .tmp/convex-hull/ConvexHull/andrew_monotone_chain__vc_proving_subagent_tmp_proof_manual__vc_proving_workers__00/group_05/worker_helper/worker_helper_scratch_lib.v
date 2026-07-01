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

Lemma point_cmp_leftdown_refl_worker : forall a,
  point_cmp_leftdown a a = 0.
Proof.
  intros a.
  rewrite point_cmp_leftdown_eq_cmp_xy.
  apply point_cmp_xy_eq; reflexivity.
Qed.

Lemma point_cmp_leftdown_lt_le_worker : forall a b,
  point_cmp_leftdown a b < 0 ->
  point_cmp_leftdown a b <= 0.
Proof.
  intros; lia.
Qed.

Lemma point_cmp_leftdown_le_lt_trans_worker : forall a b c,
  point_cmp_leftdown a b <= 0 ->
  point_cmp_leftdown b c < 0 ->
  point_cmp_leftdown a c <= 0.
Proof.
  intros a b c Hab Hbc.
  unfold point_cmp_leftdown, point_cmp_xy in *.
  repeat match goal with
  | |- context [Z_lt_dec ?x ?y] => destruct (Z_lt_dec x y)
  | |- context [Z_gt_dec ?x ?y] => destruct (Z_gt_dec x y)
  | H : context [Z_lt_dec ?x ?y] |- _ => destruct (Z_lt_dec x y)
  | H : context [Z_gt_dec ?x ?y] |- _ => destruct (Z_gt_dec x y)
  end; lia.
Qed.

Lemma point_xy_partitioned_at_preserved_by_left_worker :
  forall l l1 left right p,
    point_permutation l l1 ->
    0 <= left ->
    point_same_outside_range l l1 left (p - 1) ->
    right < Zlength l ->
    point_xy_partitioned_at l left right p ->
    point_xy_partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hperm Hleft0 Hsame Hrightlen Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 default_point = Znth p l default_point).
  {
    apply Heq.
    - lia.
    - right. lia.
  }
  split; [lia|].
  split.
  - rewrite Hpiv.
    eapply (Forall_permutation_point
              (fun x => point_cmp_leftdown x (Znth p l default_point) <= 0)
              (sublist left p l)
              (sublist left p l1)).
    + assert (Hmid :
          point_permutation (sublist left (p - 1 + 1) l)
                           (sublist left (p - 1 + 1) l1)).
      {
        eapply point_permutation_middle_of_same_outside
          with (left := left) (right := p - 1).
        - exact Hperm.
        - exact (conj Hlen Heq).
        - lia.
        - lia.
      }
      replace (p - 1 + 1) with p in Hmid by lia.
      exact Hmid.
    + exact Hleft.
  - rewrite Hpiv.
    apply Forall_sublist_by_Znth_point; try lia.
    intros k Hk.
    rewrite Heq by (try lia; right; lia).
    eapply (Forall_sublist_lookup_point
              (fun x => point_cmp_leftdown (Znth p l default_point) x < 0)
              l (p + 1) (right + 1) k); try eassumption; lia.
Qed.

Lemma point_xy_partitioned_at_preserved_by_right_worker :
  forall l l1 left right p,
    point_permutation l l1 ->
    0 <= left ->
    point_same_outside_range l l1 (p + 1) right ->
    right < Zlength l ->
    point_xy_partitioned_at l left right p ->
    point_xy_partitioned_at l1 left right p.
Proof.
  intros l l1 left right p Hperm Hleft0 Hsame Hrightlen Hpart.
  destruct Hsame as [Hlen Heq].
  destruct Hpart as [Hrange [Hleft Hright]].
  assert (Hpiv : Znth p l1 default_point = Znth p l default_point).
  {
    apply Heq.
    - lia.
    - left. lia.
  }
  split; [lia|].
  split.
  - rewrite Hpiv.
    assert (Hsub : sublist left p l1 = sublist left p l).
    {
      apply sublist_eq_from_Znth_point.
      - symmetry. exact Hlen.
      - lia.
      - lia.
      - intros k Hk.
        apply Heq.
        + lia.
        + left. lia.
    }
    rewrite Hsub.
    exact Hleft.
  - rewrite Hpiv.
    eapply (Forall_permutation_point
              (fun x => point_cmp_leftdown (Znth p l default_point) x < 0)
              (sublist (p + 1) (right + 1) l)
              (sublist (p + 1) (right + 1) l1)).
    + eapply point_permutation_middle_of_same_outside
        with (left := p + 1) (right := right).
      * exact Hperm.
      * exact (conj Hlen Heq).
      * lia.
      * lia.
    + exact Hright.
Qed.

Lemma point_xy_sorted_range_degenerate_worker :
  forall l left right,
    left >= right ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right Hge i j Hi Hij Hj.
  assert (i = j) by lia.
  subst j.
  rewrite point_cmp_leftdown_refl_worker.
  lia.
Qed.

Lemma point_xy_sorted_range_from_left_boundary_worker :
  forall l left right p,
    0 <= left ->
    p >= right ->
    right < Zlength l ->
    point_xy_partitioned_at l left right p ->
    point_xy_sorted_range l left (p - 1) ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right p Hleft0 Hp Hrightlen Hpart Hsorted.
  intros i j Hi Hij Hj.
  destruct Hpart as [Hbounds [Hleftpart _]].
  assert (p = right) by lia.
  subst p.
  destruct (Z.eq_dec j right) as [-> | Hjneq].
  - destruct (Z.eq_dec i right) as [-> | Hineq].
    + rewrite point_cmp_leftdown_refl_worker. lia.
    + eapply Forall_sublist_lookup_point
        with (lo := left) (hi := right); try eassumption; lia.
  - apply Hsorted; lia.
Qed.

Lemma point_xy_sorted_range_from_right_boundary_worker :
  forall l left right p,
    0 <= left ->
    p <= left ->
    right < Zlength l ->
    point_xy_partitioned_at l left right p ->
    point_xy_sorted_range l (p + 1) right ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right p Hleft0 Hp Hrightlen Hpart Hsorted.
  intros i j Hi Hij Hj.
  destruct Hpart as [Hbounds [_ Hrightpart]].
  assert (p = left) by lia.
  subst p.
  destruct (Z.eq_dec i left) as [-> | Hineq].
  - destruct (Z.eq_dec j left) as [-> | Hjneq].
    + rewrite point_cmp_leftdown_refl_worker. lia.
    + apply point_cmp_leftdown_lt_le_worker.
      eapply (Forall_sublist_lookup_point
                (fun x => point_cmp_leftdown (Znth left l default_point) x < 0)
                l (left + 1) (right + 1) j); try eassumption; lia.
  - apply Hsorted; lia.
Qed.

Lemma point_xy_sorted_range_ext_worker :
  forall l l1 left right,
    0 <= left ->
    right < Zlength l ->
    Zlength l = Zlength l1 ->
    (forall k, left <= k <= right ->
       Znth k l1 default_point = Znth k l default_point) ->
    point_xy_sorted_range l left right ->
    point_xy_sorted_range l1 left right.
Proof.
  intros l l1 left right Hleft0 Hrightlen Hlen Heq Hsorted i j Hi Hij Hj.
  rewrite (Heq i) by lia.
  rewrite (Heq j) by lia.
  apply Hsorted; lia.
Qed.

Lemma point_xy_sorted_range_partition_merge_worker :
  forall l left right p,
    0 <= left ->
    right < Zlength l ->
    left <= p <= right ->
    point_xy_partitioned_at l left right p ->
    point_xy_sorted_range l left (p - 1) ->
    point_xy_sorted_range l (p + 1) right ->
    point_xy_sorted_range l left right.
Proof.
  intros l left right p Hleft0 Hrightlen Hp_range Hpart
    Hsorted_left Hsorted_right.
  intros i j Hi Hij Hj.
  destruct (Z_lt_ge_dec j p) as [Hj_left | Hj_not_left].
  - apply Hsorted_left; lia.
  - destruct (Z_le_gt_dec i p) as [Hi_not_right | Hi_right].
    + destruct Hpart as [_ [Hleftpart Hrightpart]].
      destruct (Z.eq_dec i p) as [-> | Hi_neq].
      * destruct (Z.eq_dec j p) as [-> | Hj_neq].
        -- rewrite point_cmp_leftdown_refl_worker. lia.
        -- apply point_cmp_leftdown_lt_le_worker.
           eapply (Forall_sublist_lookup_point
                     (fun x => point_cmp_leftdown (Znth p l default_point) x < 0)
                     l (p + 1) (right + 1) j);
             try eassumption; lia.
      * assert (Hip :
          point_cmp_leftdown (Znth i l default_point)
            (Znth p l default_point) <= 0).
        {
          eapply (Forall_sublist_lookup_point
                    (fun x => point_cmp_leftdown x
                       (Znth p l default_point) <= 0)
                    l left p i);
            try eassumption; lia.
        }
        destruct (Z.eq_dec j p) as [-> | Hj_neq].
        -- exact Hip.
        -- assert (Hpj :
             point_cmp_leftdown (Znth p l default_point)
               (Znth j l default_point) < 0).
           {
             eapply (Forall_sublist_lookup_point
                       (fun x =>
                          point_cmp_leftdown (Znth p l default_point) x < 0)
                       l (p + 1) (right + 1) j);
               try eassumption; lia.
           }
           eapply point_cmp_leftdown_le_lt_trans_worker; eassumption.
    + apply Hsorted_right; lia.
Qed.
