(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Point Record_Geo_Vec Graham_Scan Hull_Equiv Graham_Scan_M.
Local Open Scope Z.
Import ListNotations.
(* /COQ-HEAD *)

(** * Reversal preservation for convex hulls *)

(** Disjunctive convex hull definition accepting both orientations.
    Second disjunct uses (rev T) for the containment check since
    point_in_hull_edges is direction-dependent (left-of-edge). *)
Definition is_convex_hull' (base T : list point) : Prop :=
  (ccw_convex T /\ is_max_hull'_edges T base) \/
  (rev_ccw_convex T /\ is_max_hull'_edges (rev T) base).

Lemma ccw_convex_forall3_inv : forall l,
  ccw_convex l ->
  forall l1 p l2 q l3 r l4,
    l = l1 ++ p :: l2 ++ q :: l3 ++ r :: l4 ->
    ccw p q r.
Proof.
  intros l Hconv l1 p l2 q l3 r l4 Heq.
  subst l.
  pose proof (ccw_convex_app_comm l1 (p :: l2 ++ q :: l3 ++ r :: l4) Hconv)
    as Hrot.
  simpl in Hrot.
  destruct Hrot as [Hlist _].
  rewrite ccw_list_app_iff in Hlist.
  destruct Hlist as [Hprefix _].
  rewrite ccw_list_app_iff in Hprefix.
  destruct Hprefix as [_ [Htail _]].
  simpl in Htail.
  destruct Htail as [Hforall _].
  rewrite Forall_ccw_forall in Hforall.
  apply Hforall.
  rewrite in_app_iff.
  right; simpl; auto.
Qed.

(** ccw_convex (CCW order) is preserved under reversal *)
Lemma ccw_convex_rev : forall T,
  ccw_convex T ->
  rev_ccw_convex (rev T).
Proof.
  intros T Hconv.
  unfold rev_ccw_convex.
  intros l1 q l2 r l3 s l4 Heq.
  assert (HeqT : T = rev (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)).
  { apply rev_inj. rewrite Heq. rewrite rev_involutive. reflexivity. }
  eapply (ccw_convex_forall3_inv T Hconv
            (rev l4) s (rev l3) r (rev l2) q (rev l1)).
  rewrite HeqT.
  change (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)
    with (l1 ++ [q] ++ l2 ++ [r] ++ l3 ++ [s] ++ l4).
  repeat rewrite rev_app_distr.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

(** rev_ccw_convex (CW order) is preserved under reversal *)
Lemma rev_ccw_convex_rev : forall T,
  rev_ccw_convex T ->
  ccw_convex (rev T).
Proof.
  intros T Hrev.
  unfold rev_ccw_convex in Hrev.
  apply ccw_convex_forall3.
  intros l1 p l2 q l3 r l4 Heq.
  assert (HeqT : T = rev (l1 ++ p :: l2 ++ q :: l3 ++ r :: l4)).
  { apply rev_inj. rewrite <- Heq. rewrite rev_involutive. reflexivity. }
  eapply Hrev.
  rewrite HeqT.
  change (l1 ++ p :: l2 ++ q :: l3 ++ r :: l4)
    with (l1 ++ [p] ++ l2 ++ [q] ++ l3 ++ [r] ++ l4).
  repeat rewrite rev_app_distr.
  simpl.
  do 5 rewrite <- app_assoc. simpl.
  reflexivity.
Qed.

(** is_max_hull'_edges is preserved under base reversal *)
Lemma is_max_hull'_edges_rev_base : forall T base,
  is_max_hull'_edges T base ->
  is_max_hull'_edges T (rev base).
Proof.
  intros T base Hall.
  unfold is_max_hull'_edges in *.
  apply Forall_rev.
  exact Hall.
Qed.

(** ** Main reversal theorem *)
Theorem is_convex_hull'_rev : forall base T,
  is_convex_hull' base T ->
  is_convex_hull' (rev base) (rev T).
Proof.
  intros base T [H | H].
  - (* Case 1: ccw_convex T /\ is_max_hull'_edges T base *)
    destruct H as [Hconv Hmax].
    right; split.
    + apply ccw_convex_rev; exact Hconv.
    + rewrite rev_involutive. apply is_max_hull'_edges_rev_base; exact Hmax.
  - (* Case 2: rev_ccw_convex T /\ is_max_hull'_edges (rev T) base *)
    destruct H as [Hrev Hmax].
    left; split.
    + apply rev_ccw_convex_rev; exact Hrev.
    + apply is_max_hull'_edges_rev_base; exact Hmax.
Qed.
