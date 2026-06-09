(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Point Record_Geo_Vec.
Local Open Scope Z.
Import ListNotations.
(* /COQ-HEAD *)

(*** ========== Definition ========== ***)

(** Auxiliary recursive function to traverse each edge of hull *)
(* split first point `p0` from the hull *)
(* record two leading hull vertices as `p1` `p2` *)
Fixpoint point_in_hull_edges_aux_ (p p0 p1: point) (CH: list point) :=
  match CH with
  (** hull is not empty, proceed from `p1->p2` to `p2->p3` *)
  | p2 :: l => point_in_hull_edges_aux_ p p0 p2 l /\
               left_equal (build_vec p1 p2) (build_vec p1 p)
  (** `p2` is last point, add the last edge `p2->p0` *)
  | nil => left_equal (build_vec p1 p0) (build_vec p1 p)
  end.

(** Define if point `p` sets inside the hull `CH`. *)
(* split first point `p0` from the hull *)
(* in order to facilitate recursion. *)
Definition point_in_hull_edges (p : point) (CH: list point) :=
  match CH with
  (** hull := `p0 p1 ...`, recurse into _aux *)
  | p0 :: p1 :: p2 :: l => left_equal (build_vec p0 p1) (build_vec p0 p) /\
                     point_in_hull_edges_aux_ p p0 p1 (p2 :: l)
  (** hull := `p0 p1`, check if p is on segment `p0->p1` *)
  | p0 :: p1 :: nil => colinear p p0 p1 /\ at_mid p p0 p1
  (** hull := `p0`, simply eliminate this case *)
  | _ => False
  end.

Definition is_max_hull'_edges (CH l: list point) :=
  Forall (fun q => point_in_hull_edges q CH) l.


(*** ========== Proof ========== ***)

Lemma point_in_triangle_halfplane : forall p a b c u v,
  point_in_triangle p a b c ->
  ccw c b a ->
  left_equal (build_vec u v) (build_vec u a) ->
  left_equal (build_vec u v) (build_vec u b) ->
  left_equal (build_vec u v) (build_vec u c) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p a b c u v Htri Hccw Hla Hlb Hlc.
  unfold point_in_triangle in Htri.
  destruct Htri as [Htri | Htri].
  - unfold ccw, left_equal, left_than, cross_prod, build_vec in *.
    simpl in *.
    nia.
  - destruct Htri as [Hcol _].
    unfold ccw, colinear, parallel, left_than, cross_prod, build_vec in *.
    simpl in *.
    nia.
Qed.

Lemma point_in_hull_equiv_two_points : forall p p0 p1,
  point_in_hull p (p0 :: p1 :: nil) <->
  point_in_hull_edges p (p0 :: p1 :: nil).
Proof.
  intros.
  simpl.
  tauto.
Qed.

Lemma point_in_hull_equiv_three_points : forall p p0 p1 p2,
  ccw p1 p0 p2 ->
  point_in_hull p (p0 :: p1 :: p2 :: nil) <->
  point_in_hull_edges p (p0 :: p1 :: p2 :: nil).
Proof.
  intros p p0 p1 p2 Hccw.
  simpl.
  split; intros H.
  - unfold point_in_triangle in H.
    destruct H as [[H | H] | Hfalse].
    + destruct H as [_ [H12 [H20 H01]]].
      repeat split; tauto.
    + destruct H as [Hcol _].
      unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *.
      simpl in *.
      nia.
    + contradiction.
  - unfold point_in_triangle.
    destruct H as [H01 [H20 H12]].
    left.
    left.
    repeat split; try tauto.
    apply ccw_cyclicity; exact Hccw.
Qed.

Lemma edge_side_propagate : forall p0 p1 p2 p3 q,
  ccw p1 p0 p2 ->
  ccw p1 p0 p3 ->
  ccw p1 p0 q ->
  ccw p2 p0 p3 ->
  ccw p2 p0 q ->
  ccw p3 p0 q ->
  ccw p2 p1 p3 ->
  left_equal (build_vec p2 p3) (build_vec p2 q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma edge_side_backward : forall p0 q prev p1 p2,
  ccw q p0 prev ->
  ccw q p0 p1 ->
  ccw q p0 p2 ->
  ccw prev p0 p1 ->
  ccw prev p0 p2 ->
  ccw p1 p0 p2 ->
  ccw p1 prev p2 ->
  left_equal (build_vec prev p1) (build_vec prev q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma edge_side_backward_pivot : forall p0 prev p1 p2,
  ccw prev p0 p1 ->
  ccw prev p0 p2 ->
  ccw p1 p0 p2 ->
  ccw p1 prev p2 ->
  left_equal (build_vec prev p1) (build_vec prev p0) ->
  left_equal (build_vec p1 p2) (build_vec p1 p0).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma edge_prev_endpoint_left : forall a prev p1,
  ccw prev a p1 ->
  left_equal (build_vec prev p1) (build_vec prev a).
Proof.
  unfold ccw, left_equal, left_than, cross_prod, build_vec.
  simpl.
  intros.
  nia.
Qed.

Lemma rev_consec_ccw_app_inv2 : forall l1 l2,
  rev_consec_ccw (l1 ++ l2) ->
  rev_consec_ccw l2.
Proof.
  intros l1 l2 H.
  induction l1 as [| a l1 IH].
  - exact H.
  - simpl in H.
    destruct H as [_ H].
    apply IH.
    exact H.
Qed.

Lemma rev_consec_ccw_edge_at : forall p0 pre prev p1 p2 post,
  rev_consec_ccw (p0 :: pre ++ prev :: p1 :: p2 :: post) ->
  ccw p1 prev p2.
Proof.
  intros p0 pre prev p1 p2 post H.
  assert (rev_consec_ccw (prev :: p1 :: p2 :: post)).
  {
    apply (rev_consec_ccw_app_inv2 (p0 :: pre)).
    exact H.
  }
  simpl in H0.
  tauto.
Qed.

Lemma rev_consec_ccw_edge_at_tail : forall pre prev p1 p2 post,
  rev_consec_ccw (pre ++ prev :: p1 :: p2 :: post) ->
  ccw p1 prev p2.
Proof.
  intros pre prev p1 p2 post H.
  assert (rev_consec_ccw (prev :: p1 :: p2 :: post)).
  {
    apply (rev_consec_ccw_app_inv2 pre).
    exact H.
  }
  simpl in H0.
  tauto.
Qed.

Lemma point_in_hull_halfplane3_weak : forall p u v p0 p1 p2 CH,
  weak_rev_ccw_list p0 (p1 :: p2 :: CH) ->
  rev_consec_ccw (p1 :: p2 :: CH) ->
  (forall q, In q (p0 :: p1 :: p2 :: CH) ->
    left_equal (build_vec u v) (build_vec u q)) ->
  point_in_hull p (p0 :: p1 :: p2 :: CH) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p u v p0 p1 p2 CH Hrev Htail Hall Hhull.
  revert p1 p2 Hrev Htail Hall Hhull.
  induction CH as [| p3 CH IH]; intros p1 p2 Hrev Htail Hall Hhull.
  - simpl in Hhull.
    destruct Hhull as [Htri | Hfalse]; [| contradiction].
    eapply point_in_triangle_halfplane_weak; try exact Htri;
      apply Hall; simpl; tauto.
  - pose proof (point_in_hull_cons_iff_weak p p0 p2 p1 (p3 :: CH) Hrev)
      as [Hiff _].
    specialize (Hiff Hhull).
    destruct Hiff as [Hsmall | Htri].
    + assert (Hrev' : weak_rev_ccw_list p0 (p2 :: p3 :: CH)).
      {
        apply (weak_rev_ccw_list_ind' p0 [p1] (p2 :: p3 :: CH)).
        exact Hrev.
      }
      apply (IH p2 p3 Hrev').
      * simpl in Htail.
        destruct Htail as [_ Htail].
        exact Htail.
      * intros q HIn.
        apply Hall.
        simpl in *.
        tauto.
      * exact Hsmall.
    + eapply point_in_triangle_halfplane_weak; try exact Htri;
        apply Hall; simpl; tauto.
Qed.

Lemma point_in_hull_halfplane_general_weak : forall p u v p0 pre p1 p2 post,
  weak_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  (forall q, In q (p0 :: pre ++ p1 :: p2 :: post) ->
    left_equal (build_vec u v) (build_vec u q)) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros p u v p0 pre.
  induction pre as [| x pre IH]; intros p1 p2 post Hrev Hconsec Hall Hhull.
  - simpl in Hrev, Hconsec, Hall, Hhull.
    eapply (point_in_hull_halfplane3_weak p u v p0 p1 p2 post Hrev).
    + exact Hconsec.
    + intros q HIn.
      apply Hall.
      simpl.
      tauto.
    + exact Hhull.
  - destruct pre as [| y pre'].
    + simpl in Hrev, Hconsec, Hall, Hhull.
      pose proof (point_in_hull_cons_iff_weak p p0 p1 x (p2 :: post) Hrev)
        as [Hiff _].
      specialize (Hiff Hhull).
      destruct Hiff as [Hsmall | Htri].
      * assert (Hrev' : weak_rev_ccw_list p0 (p1 :: p2 :: post)).
        {
          apply (weak_rev_ccw_list_ind' p0 [x] (p1 :: p2 :: post)).
          exact Hrev.
        }
        eapply (point_in_hull_halfplane3_weak p u v p0 p1 p2 post Hrev').
        -- destruct Hconsec as [_ Hconsec'].
           exact Hconsec'.
        -- intros q HIn.
           apply Hall.
           simpl in *.
           tauto.
        -- exact Hsmall.
      * eapply point_in_triangle_halfplane_weak; try exact Htri;
          apply Hall; simpl; tauto.
    + simpl in Hrev, Hconsec, Hall, Hhull.
      pose proof (point_in_hull_cons_iff_weak p p0 y x (pre' ++ p1 :: p2 :: post) Hrev)
        as [Hiff _].
      specialize (Hiff Hhull).
      destruct Hiff as [Hsmall | Htri].
      * eapply IH.
        -- apply (weak_rev_ccw_list_ind' p0 [x] (y :: pre' ++ p1 :: p2 :: post)).
           exact Hrev.
        -- destruct Hconsec as [_ Hconsec'].
           exact Hconsec'.
        -- intros q HIn.
           apply Hall.
           simpl in *.
           tauto.
        -- exact Hsmall.
      * eapply point_in_triangle_halfplane_weak; try exact Htri;
          apply Hall; simpl; tauto.
Qed.

Lemma weak_rev_ccw_first_edge_halfplane : forall p q r,
  weak_rev_ccw p q r ->
  left_equal (build_vec p q) (build_vec p r).
Proof.
  intros p q r H.
  destruct H as [H | [Hcol Hmid]];
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
Qed.

Lemma weak_rev_ccw_final_edge_halfplane : forall p q r,
  weak_rev_ccw p q r ->
  left_equal (build_vec r p) (build_vec r q).
Proof.
  intros p q r H.
  destruct H as [H | [Hcol Hmid]];
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
Qed.

Lemma weak_rev_ccw_edge_to_pivot_halfplane : forall p q r,
  weak_rev_ccw p q r ->
  left_equal (build_vec q r) (build_vec q p).
Proof.
  intros p q r H.
  destruct H as [H | [Hcol Hmid]];
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
Qed.

Lemma edge_ray_extend : forall q prev p1 p2,
  ccw p1 prev p2 ->
  colinear q prev p1 ->
  forward_or_perp (build_vec p1 prev) (build_vec p1 q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros q prev p1 p2 Hedge Hcol Hfwd.
  assert (Hnz : dot_prod (build_vec p1 prev) (build_vec p1 prev) > 0).
  {
    pose proof left_than_nonzero2 _ _ Hedge as Hnz.
    rewrite nonzero_iff in Hnz.
    exact Hnz.
  }
  pose proof aux2 (build_vec p1 prev) (build_vec p1 p2) (build_vec p1 q)
    as Haux.
  assert (Hcross : cross_prod (build_vec p1 q) (build_vec p1 prev) = 0).
  {
    unfold colinear, parallel, build_vec, cross_prod in *.
    simpl in *.
    nia.
  }
  unfold ccw, left_equal, left_than, forward_or_perp in *.
  rewrite dot_prod_comm with (v1 := build_vec p1 q) (v2 := build_vec p1 prev)
    in Haux.
  nia.
Qed.

Lemma nested_mid_previous : forall p0 q prev p1,
  colinear prev q p0 ->
  at_mid prev q p0 ->
  colinear p1 q p0 ->
  at_mid p1 q p0 ->
  colinear p1 prev p0 ->
  at_mid p1 prev p0 ->
  at_mid prev q p1.
Proof.
  intros.
  pose proof metric_nonneg (build_vec prev q).
  pose proof metric_nonneg (build_vec prev p1).
  pose proof metric_nonneg (build_vec q p0).
  pose proof metric_nonneg (build_vec q p1).
  pose proof metric_nonneg (build_vec prev p0).
  pose proof metric_nonneg (build_vec p1 p0).
  pose proof metric_nonneg (build_vec p1 prev).
  unfold colinear, at_mid, parallel, backward_or_perp,
         build_vec, cross_prod, dot_prod in *.
  simpl in *.
  nia.
Qed.

Lemma weak_previous_forward : forall p0 q prev p1,
  colinear p0 q prev ->
  at_mid prev q p0 ->
  colinear p0 q p1 ->
  at_mid p1 q p0 ->
  colinear p0 prev p1 ->
  at_mid p1 prev p0 ->
  forward_or_perp (build_vec p1 prev) (build_vec p1 q).
Proof.
  intros p0 q prev p1 Hqprev Hqprev_mid Hqp1 Hqp1_mid
    Hprevp1 Hprevp1_mid.
  apply at_mid_fwd2.
  pose proof (nested_mid_previous p0 q prev p1
    (colinear_perm321 _ _ _ Hqprev) Hqprev_mid
    (colinear_perm321 _ _ _ Hqp1) Hqp1_mid
    (colinear_perm321 _ _ _ Hprevp1) Hprevp1_mid) as Hmid.
  exact Hmid.
Qed.

Lemma edge_side_backward_weak : forall p0 q prev p1 p2,
  weak_rev_ccw p0 q prev ->
  weak_rev_ccw p0 q p1 ->
  weak_rev_ccw p0 q p2 ->
  weak_rev_ccw p0 prev p1 ->
  weak_rev_ccw p0 prev p2 ->
  weak_rev_ccw p0 p1 p2 ->
  ccw p1 prev p2 ->
  left_equal (build_vec prev p1) (build_vec prev q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 q prev p1 p2 Hqprev Hqp1 Hqp2 Hprevp1 Hprevp2
    Hp1p2 Hedge Hprev.
  destruct Hqprev as [Hqprev | [Hqprev_col Hqprev_mid]];
  destruct Hqp1 as [Hqp1 | [Hqp1_col Hqp1_mid]];
  destruct Hqp2 as [Hqp2 | [Hqp2_col Hqp2_mid]];
  destruct Hprevp1 as [Hprevp1 | [Hprevp1_col Hprevp1_mid]];
  destruct Hprevp2 as [Hprevp2 | [Hprevp2_col Hprevp2_mid]];
  destruct Hp1p2 as [Hp1p2 | [Hp1p2_col Hp1p2_mid]];
  try (unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
              parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
       simpl in *; nia).
  - eapply edge_ray_extend; try exact Hedge.
    + unfold colinear, parallel, build_vec, cross_prod in *.
      simpl in *.
      nia.
    + eapply weak_previous_forward; eauto.
  - eapply edge_ray_extend; try exact Hedge.
    + unfold colinear, parallel, build_vec, cross_prod in *.
      simpl in *.
      nia.
    + eapply weak_previous_forward; eauto.
Qed.

Lemma edge_side_propagate_weak : forall p0 p1 p2 p3 q,
  weak_rev_ccw p0 p1 p2 ->
  weak_rev_ccw p0 p1 p3 ->
  weak_rev_ccw p0 p1 q ->
  weak_rev_ccw p0 p2 p3 ->
  weak_rev_ccw p0 p2 q ->
  weak_rev_ccw p0 p3 q ->
  ccw p2 p1 p3 ->
  left_equal (build_vec p2 p3) (build_vec p2 q) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 p1 p2 p3 q H12 H13 H1q H23 H2q H3q Hedge Hlater.
  destruct H23 as [H23 | [H23col H23mid]].
  - repeat match goal with
    | H : weak_rev_ccw _ _ _ |- _ => destruct H as [H | [H ?]]
    end;
    unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
           parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
    simpl in *; nia.
  - destruct H2q as [H2q | [H2qcol H2qmid]].
    + repeat match goal with
      | H : weak_rev_ccw _ _ _ |- _ => destruct H as [H | [H ?]]
      end;
      unfold weak_rev_ccw, ccw, colinear, at_mid, left_equal, left_than,
             parallel, backward_or_perp, build_vec, cross_prod, dot_prod in *;
      simpl in *; nia.
    + exact (left_equal_segment p1 p2 p2 p0 q
        ltac:(unfold left_equal, cross_prod, build_vec; simpl; nia)
        (weak_rev_ccw_edge_to_pivot_halfplane p0 p1 p2 H12)
        (colinear_perm321 _ _ _ H2qcol)
        H2qmid).
Qed.

Lemma first_edge_vertices_halfplane_weak : forall p0 p1 CH q,
  weak_rev_ccw_list p0 (p1 :: CH) ->
  In q (p0 :: p1 :: CH) ->
  left_equal (build_vec p0 p1) (build_vec p0 q).
Proof.
  intros p0 p1 CH q Hrev HIn.
  simpl in HIn.
  destruct HIn as [-> | [-> | HIn]].
  - unfold left_equal, cross_prod, build_vec.
    simpl.
    nia.
  - unfold left_equal, cross_prod, build_vec.
    simpl.
    nia.
  - simpl in Hrev.
    destruct Hrev as [Hfor _].
    rewrite Forall_weak_rev_ccw_forall in Hfor.
    exact (weak_rev_ccw_first_edge_halfplane p0 p1 q (Hfor q HIn)).
Qed.

Lemma hull_edge_later_halfplane_weak : forall p0 p1 p2 CH q,
  weak_rev_ccw_list p0 (p1 :: p2 :: CH) ->
  rev_consec_ccw (p1 :: p2 :: CH) ->
  In q CH ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 p1 p2 CH q Hrev Hconsec HIn.
  revert p1 p2 q Hrev Hconsec HIn.
  induction CH as [| p3 CH IH]; intros p1 p2 q Hrev Hconsec HIn.
  - contradiction.
  - simpl in HIn.
    destruct HIn as [-> | HIn].
    + simpl in Hconsec.
      destruct Hconsec as [Hedge _].
      unfold ccw, left_equal, left_than, cross_prod, build_vec in *.
      simpl in *.
      nia.
    + assert (Hrev' : weak_rev_ccw_list p0 (p2 :: p3 :: CH)).
      {
        apply (weak_rev_ccw_list_ind' p0 [p1] (p2 :: p3 :: CH)).
        exact Hrev.
      }
      assert (Hlater : left_equal (build_vec p2 p3) (build_vec p2 q)).
      {
        apply (IH p2 p3 q Hrev').
        - simpl in Hconsec.
          destruct Hconsec as [_ Htail].
          exact Htail.
        - exact HIn.
      }
      eapply (edge_side_propagate_weak p0 p1 p2 p3 q); try exact Hlater.
      * simpl in Hrev.
        destruct Hrev as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev.
        destruct Hrev as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev.
        destruct Hrev as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev'.
        destruct Hrev' as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev'.
        destruct Hrev' as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        simpl.
        tauto.
      * simpl in Hrev'.
        destruct Hrev' as [_ Hrev''].
        simpl in Hrev''.
        destruct Hrev'' as [Hfor _].
        rewrite Forall_weak_rev_ccw_forall in Hfor.
        apply Hfor.
        exact HIn.
      * simpl in Hconsec.
        tauto.
Qed.


Lemma hull_edge_previous_halfplane_weak : forall p0 pre prev p1 p2 post q,
  weak_rev_ccw_list p0 (pre ++ prev :: p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ prev :: p1 :: p2 :: post) ->
  In q (p0 :: pre) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 pre.
  pattern pre.
  apply rev_ind.
  - intros prev p1 p2 post q Hrev _ HIn.
    simpl in HIn.
    destruct HIn as [Hq | []].
    subst q.
    simpl in Hrev.
    destruct Hrev as [_ Hrev'].
    simpl in Hrev'.
    destruct Hrev' as [Hp1 _].
    rewrite Forall_weak_rev_ccw_forall in Hp1.
    apply weak_rev_ccw_edge_to_pivot_halfplane.
    apply Hp1.
    simpl.
    tauto.
  - intros x l IH prev p1 p2 post q Hrev Hconsec HIn.
    rewrite <- app_assoc in Hrev, Hconsec.
    pose proof (weak_rev_ccw_list_ind' p0 l (x :: prev :: p1 :: p2 :: post)
      Hrev) as Htail.
    pose proof (proj1 (weak_rev_ccw_list_app_iff p0 l
      (x :: prev :: p1 :: p2 :: post)) Hrev) as [_ [_ Hbetween]].
    simpl in Htail.
    destruct Htail as [Hx Hrest].
    rewrite Forall_weak_rev_ccw_forall in Hx.
    simpl in Hrest.
    destruct Hrest as [Hprev Hrest].
    rewrite Forall_weak_rev_ccw_forall in Hprev.
    simpl in Hrest.
    destruct Hrest as [Hp1 _].
    rewrite Forall_weak_rev_ccw_forall in Hp1.
    assert (Hconsec' : rev_consec_ccw
      ((l ++ [x]) ++ prev :: p1 :: p2 :: post)).
    {
      replace (l ++ [x] ++ prev :: p1 :: p2 :: post)
        with ((l ++ [x]) ++ prev :: p1 :: p2 :: post) in Hconsec
        by (rewrite <- app_assoc; reflexivity).
      exact Hconsec.
    }
    assert (Hconsec_tail : rev_consec_ccw
      (l ++ x :: prev :: p1 :: p2 :: post)).
    {
      replace (l ++ x :: prev :: p1 :: p2 :: post)
        with ((l ++ [x]) ++ prev :: p1 :: p2 :: post)
        by (rewrite <- app_assoc; reflexivity).
      exact Hconsec'.
    }
    simpl in HIn.
    destruct HIn as [Hq0 | HIn].
    + subst q.
      apply weak_rev_ccw_edge_to_pivot_halfplane.
      apply Hp1.
      simpl.
      tauto.
    + rewrite in_app_iff in HIn.
      destruct HIn as [HIn | HIn].
      * assert (Hprevedge : left_equal (build_vec prev p1) (build_vec prev q)).
        {
          apply (IH x prev p1 (p2 :: post) q);
            try exact Hrev; try exact Hconsec_tail.
          simpl.
          tauto.
        }
        eapply edge_side_backward_weak; eauto.
        -- apply Hbetween; try exact HIn.
           simpl.
           tauto.
        -- apply Hbetween; try exact HIn.
           simpl.
           tauto.
        -- apply Hbetween; try exact HIn.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hp1.
           simpl.
           tauto.
        -- apply (rev_consec_ccw_edge_at_tail (l ++ [x]) prev p1 p2 post).
           exact Hconsec'.
      * simpl in HIn.
        destruct HIn as [Hqx | []].
        subst q.
        eapply edge_side_backward_weak; eauto.
        -- apply Hx.
           simpl.
           tauto.
        -- apply Hx.
           simpl.
           tauto.
        -- apply Hx.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hprev.
           simpl.
           tauto.
        -- apply Hp1.
           simpl.
           tauto.
        -- apply (rev_consec_ccw_edge_at_tail (l ++ [x]) prev p1 p2 post).
           exact Hconsec'.
        -- apply edge_prev_endpoint_left.
           apply (rev_consec_ccw_edge_at_tail l x prev p1 (p2 :: post)).
           exact Hconsec_tail.
Qed.

Lemma final_edge_vertices_halfplane_weak : forall p0 pre plast q,
  weak_rev_ccw_list p0 (pre ++ plast :: nil) ->
  In q (p0 :: pre ++ plast :: nil) ->
  left_equal (build_vec plast p0) (build_vec plast q).
Proof.
  intros p0 pre plast q Hrev HIn.
  simpl in HIn.
  destruct HIn as [Hq | HIn].
  - subst q.
    unfold left_equal, cross_prod, build_vec.
    simpl.
    nia.
  - rewrite in_app_iff in HIn.
    simpl in HIn.
    destruct HIn as [HIn | [Hq | []]].
    + rewrite (weak_rev_ccw_list_app_iff p0 pre (plast :: nil)) in Hrev.
      destruct Hrev as [_ [_ Hbetween]].
      apply weak_rev_ccw_final_edge_halfplane.
      apply Hbetween; try exact HIn.
      simpl.
      tauto.
    + subst q.
      unfold left_equal, cross_prod, build_vec.
      simpl.
      nia.
Qed.

Lemma edge_all_vertices_halfplane_weak : forall p0 pre p1 p2 post q,
  weak_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  In q (p0 :: pre ++ p1 :: p2 :: post) ->
  left_equal (build_vec p1 p2) (build_vec p1 q).
Proof.
  intros p0 pre p1 p2 post q Hrev Hconsec HIn.
  simpl in HIn.
  destruct HIn as [Hq | HIn].
  - subst q.
    assert (Htail : weak_rev_ccw_list p0 (p1 :: p2 :: post)).
    {
      apply (weak_rev_ccw_list_ind' p0 pre (p1 :: p2 :: post) Hrev).
    }
    simpl in Htail.
    destruct Htail as [Hfor _].
    rewrite Forall_weak_rev_ccw_forall in Hfor.
    apply weak_rev_ccw_edge_to_pivot_halfplane.
    apply Hfor.
    simpl.
    tauto.
  - rewrite in_app_iff in HIn.
    simpl in HIn.
    destruct HIn as [Hpre | [Hq1 | [Hq2 | Hpost]]].
    + destruct (destruct_tail pre) as [Hpre_nil | [prev [pre' Hpre_eq]]].
      * rewrite Hpre_nil in Hpre.
        contradiction.
      * subst pre.
        rewrite in_app_iff in Hpre.
        simpl in Hpre.
        destruct Hpre as [Hpre | [Hqprev | []]].
        -- assert (Hrev' : weak_rev_ccw_list p0
             (pre' ++ prev :: p1 :: p2 :: post)).
           { replace (pre' ++ prev :: p1 :: p2 :: post)
               with ((pre' ++ [prev]) ++ p1 :: p2 :: post)
               by (rewrite <- app_assoc; reflexivity).
             exact Hrev. }
           assert (Hconsec' : rev_consec_ccw
             (pre' ++ prev :: p1 :: p2 :: post)).
           { replace (pre' ++ prev :: p1 :: p2 :: post)
               with ((pre' ++ [prev]) ++ p1 :: p2 :: post)
               by (rewrite <- app_assoc; reflexivity).
             exact Hconsec. }
           eapply hull_edge_previous_halfplane_weak.
           ++ exact Hrev'.
           ++ exact Hconsec'.
           ++ exact (or_intror Hpre).
        -- subst q.
           assert (Hconsec' : rev_consec_ccw
             (pre' ++ prev :: p1 :: p2 :: post)).
           { replace (pre' ++ prev :: p1 :: p2 :: post)
               with ((pre' ++ [prev]) ++ p1 :: p2 :: post)
               by (rewrite <- app_assoc; reflexivity).
             exact Hconsec. }
           apply edge_prev_endpoint_left.
           apply (rev_consec_ccw_edge_at_tail pre' prev p1 p2 post).
           exact Hconsec'.
    + subst q.
      unfold left_equal, cross_prod, build_vec.
      simpl.
      nia.
    + subst q.
      unfold left_equal, cross_prod, build_vec.
      simpl.
      nia.
    + assert (Htail : weak_rev_ccw_list p0 (p1 :: p2 :: post)).
      {
        apply (weak_rev_ccw_list_ind' p0 pre (p1 :: p2 :: post) Hrev).
      }
      assert (Hconsec_tail : rev_consec_ccw (p1 :: p2 :: post)).
      {
        apply (rev_consec_ccw_app_inv2 pre).
        exact Hconsec.
      }
      eapply hull_edge_later_halfplane_weak; eauto.
Qed.
Lemma point_in_hull_edges_aux_from_hull_weak : forall p p0 pre p1 p2 post,
  weak_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  point_in_hull_edges_aux_ p p0 p1 (p2 :: post).
Proof.
  intros p p0 pre p1 p2 post Hrev Hconsec Hhull.
  revert pre p1 p2 Hrev Hconsec Hhull.
  induction post as [| p3 post IH]; intros pre p1 p2 Hrev Hconsec Hhull.
  - simpl.
    assert (Hconsec_tail : rev_consec_ccw (pre ++ p1 :: p2 :: nil)).
    {
      exact Hconsec.
    }
    assert (Hrev_final : weak_rev_ccw_list p0 ((pre ++ [p1]) ++ p2 :: nil)).
    {
      replace ((pre ++ [p1]) ++ p2 :: nil) with (pre ++ p1 :: p2 :: nil)
        by (rewrite <- app_assoc; reflexivity).
      exact Hrev.
    }
    split.
    + eapply (point_in_hull_halfplane_general_weak p p2 p0 p0 pre p1 p2 nil).
      * exact Hrev.
      * exact Hconsec_tail.
      * intros q HIn.
        eapply final_edge_vertices_halfplane_weak.
        -- exact Hrev_final.
        -- replace (p0 :: (pre ++ [p1]) ++ p2 :: nil)
             with (p0 :: pre ++ p1 :: p2 :: nil)
             by (simpl; rewrite <- app_assoc; reflexivity).
           exact HIn.
      * exact Hhull.
    + eapply (point_in_hull_halfplane_general_weak p p1 p2 p0 pre p1 p2 nil).
      * exact Hrev.
      * exact Hconsec_tail.
      * intros q HIn.
        eapply (edge_all_vertices_halfplane_weak p0 pre p1 p2 nil q).
        -- exact Hrev.
        -- exact Hconsec.
        -- exact HIn.
      * exact Hhull.
  - simpl.
    assert (Hconsec_tail : rev_consec_ccw (pre ++ p1 :: p2 :: p3 :: post)).
    {
      exact Hconsec.
    }
    assert (Hrev' : weak_rev_ccw_list p0 ((pre ++ [p1]) ++ p2 :: p3 :: post)).
    {
      replace ((pre ++ [p1]) ++ p2 :: p3 :: post)
        with (pre ++ p1 :: p2 :: p3 :: post)
        by (rewrite <- app_assoc; reflexivity).
      exact Hrev.
    }
    assert (Hconsec' : rev_consec_ccw
      ((pre ++ [p1]) ++ p2 :: p3 :: post)).
    {
      replace ((pre ++ [p1]) ++ p2 :: p3 :: post)
        with (pre ++ p1 :: p2 :: p3 :: post)
        by (rewrite <- app_assoc; reflexivity).
      exact Hconsec.
    }
    assert (Hhull' : point_in_hull p
      (p0 :: (pre ++ [p1]) ++ p2 :: p3 :: post)).
    {
      replace (p0 :: (pre ++ [p1]) ++ p2 :: p3 :: post)
        with (p0 :: pre ++ p1 :: p2 :: p3 :: post)
        by (simpl; rewrite <- app_assoc; reflexivity).
      exact Hhull.
    }
    split.
    + eapply (IH (pre ++ [p1]) p2 p3 Hrev' Hconsec' Hhull').
    + eapply (point_in_hull_halfplane_general_weak p p1 p2 p0 pre p1 p2
        (p3 :: post)).
      * exact Hrev.
      * exact Hconsec_tail.
      * intros q HIn.
        eapply (edge_all_vertices_halfplane_weak p0 pre p1 p2 (p3 :: post) q).
        -- exact Hrev.
        -- exact Hconsec.
        -- exact HIn.
	      * exact Hhull.
Qed.

Lemma point_in_hull_halfplane_general_g : forall p u v p0 pre p1 p2 post,
  g_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  (forall q, In q (p0 :: pre ++ p1 :: p2 :: post) ->
    left_equal (build_vec u v) (build_vec u q)) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  left_equal (build_vec u v) (build_vec u p).
Proof.
  intros.
  eapply point_in_hull_halfplane_general_weak; eauto.
Qed.

Lemma first_edge_vertices_halfplane_g : forall p0 p1 CH q,
  g_rev_ccw_list p0 (p1 :: CH) ->
  In q (p0 :: p1 :: CH) ->
  left_equal (build_vec p0 p1) (build_vec p0 q).
Proof.
  intros.
  eapply first_edge_vertices_halfplane_weak; eauto.
Qed.

Lemma point_in_hull_edges_aux_from_hull_g : forall p p0 pre p1 p2 post,
  g_rev_ccw_list p0 (pre ++ p1 :: p2 :: post) ->
  rev_consec_ccw (pre ++ p1 :: p2 :: post) ->
  point_in_hull p (p0 :: pre ++ p1 :: p2 :: post) ->
  point_in_hull_edges_aux_ p p0 p1 (p2 :: post).
Proof.
  intros.
  eapply point_in_hull_edges_aux_from_hull_weak; eauto.
Qed.

Theorem point_in_hull_equiv : forall p p0 CH,
  sort p0 CH ->
  rev_consec_ccw CH ->
  point_in_hull p (p0 :: CH) ->
  point_in_hull_edges p (p0 :: CH).
Proof.
  intros p p0 CH Hsort Hconsec Hhull.
  destruct Hsort as [_ Hrev].
  destruct CH as [| p1 CH'].
  - simpl in Hhull.
    contradiction.
  - destruct CH' as [| p2 post].
    + apply point_in_hull_equiv_two_points.
      exact Hhull.
    + simpl.
      split.
      * assert (Hconsec_tail : rev_consec_ccw (p1 :: p2 :: post)).
        {
          exact Hconsec.
        }
        eapply (point_in_hull_halfplane_general_g p p0 p1 p0 nil p1 p2 post).
        -- exact Hrev.
        -- exact Hconsec_tail.
        -- intros q HIn.
           eapply (first_edge_vertices_halfplane_g p0 p1 (p2 :: post) q).
           ++ exact Hrev.
           ++ exact HIn.
        -- exact Hhull.
      * eapply (point_in_hull_edges_aux_from_hull_g p p0 nil p1 p2 post); eauto.
Qed.

Theorem is_max_hull'_edges_of_max_hull : forall p CH l,
  sort p CH ->
  rev_consec_ccw CH ->
  is_max_hull' p CH l ->
  is_max_hull'_edges (p :: CH) l.
Proof.
  intros p CH l Hsort Hcon Hmax.
  destruct Hsort as [Hleft Hrev].
  unfold is_max_hull'_edges, is_max_hull' in *.
  rewrite !Forall_forall in *.
  intros q HIn.
  eapply point_in_hull_equiv.
  - split; [exact Hleft | exact Hrev].
  - exact Hcon.
  - apply Hmax.
    exact HIn.
Qed.
