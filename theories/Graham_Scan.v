(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point.
Local Open Scope Z.
Import ListNotations.
(* /COQ-HEAD *)

(* Gift-wrapping / Jarvis' march / Graham Scan *)
(* 每步查找最外侧点
   leftmost point, -y orientation =>
   append the point with minimum polar angle =>
   exit until the initial point *)
(*
Graham(x[1..n], y[1..n]):
  // find leftmost point
  l = 1
  for i from 2 to n:
    if x[i] < x[l]:
      l = i
  p = l
  // search next point
  // p := endpoint in convex hull
  // q := next point (different from p, determined by ccw)
  repeat:
    q = p + 1 // sing with an arbitary point
    for r from 1 to n:
      if p != r and ccw(p,r,q): // ccw_transitivity
        q = r // final q ensures that forall r != p, ccw(p,r,q).
    // append q in convex hull
    next[p] = q
    prev[q] = p
    p = q
  // terminate when convex hull close
  until p = l *)

(* ========================== *)
(*      Main Algorithm        *)
(* ========================== *)

Fixpoint graham_scan_inc (p : point) (T : list point) : list point :=
  match T with
  | t :: T' =>
    match T' with
    (* T = t :: s :: T'' *)
    | s :: T'' =>
      match (ccw_dec s t p) with
      (* ccw s t p, push stack *)
      | left _ => p :: T
      (* ~ ccw s t p, pop stack & recursion *)
      | right _ => graham_scan_inc p T'
      end
    (* T = [t], push stack *)
    | _ => p :: T
    end
  (* T = [], untouched *)
  | _ => p :: T
  end.

Fixpoint graham_scan (l: list point) : list point :=
  (* fold_right graham_scan_inc nil l *)
  match l with
  | p :: l' => graham_scan_inc p (graham_scan l')
  | _ => nil
  end.

(** Simple case *)
(*  After init,
the vertices on T are the vertices of C_2
in clockwise order. *)
Theorem graham_convex_0 : forall (p q r : point),
  sort_aux p [p ; q ; r] -> is_convex p (graham_scan [p ; q ; r]).
Proof.
  simpl; intros.
  rewrite !Forall_ccw_cons_iff in H.
  destruct H as [[H _] [_ _]].
  destruct (ccw_dec r q p); simpl.
  + elim_ccw_rep H.
  + tauto.
Qed.

(** Proof *)
(*  After the i’th iteration,
the vertices on the stack are the vertices of C_i
in clockwise order.  *)
(* Prove that [graham_scan T] is subset of T while preserving order *)
Lemma succ_stack : forall (a : point) (T : list point),
  exists T0 T', T = T0 ++ T' /\ graham_scan_inc a T = a :: T'.
Proof.
  intros; destruct T.
  - exists [], []. split; reflexivity.
  - destruct T.
    + exists [], [p]. split; reflexivity.
    + revert a p p0.
      induction T; intros.
      * simpl; destruct (ccw_dec p0 p a).
        exists [], [p ; p0]. split; reflexivity.
        exists [p], [p0]. split; reflexivity.
      * pose proof IHT a0 p0 a. 
        pose proof IHT a0 p p0.
        destruct H as [T0 [T' [H1 H2]]].
        destruct H0 as [T1 [T'' [H3 H4]]].
        simpl in H4. simpl. destruct (ccw_dec p0 p a0).
        exists [], (p :: p0 :: a :: T). split; reflexivity.
        simpl in H2. destruct (ccw_dec a p0 a0).
        exists [p], (p0 :: a :: T). split; reflexivity.
        exists (p :: T0), T'.
        split.
        rewrite H1. reflexivity.
        assumption.
Qed.

Theorem Forall_ccw_conv : forall (p q : point) (T : list point),
  Forall_ccw p q T -> Forall_ccw p q (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof Forall_ccw_ind p q a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; rewrite H1 in *; rewrite H2.
  - rewrite Forall_ccw_cons_iff in H |- *.
    tauto.
  - simpl in IHT.
    rewrite Forall_ccw_cons_iff in H, IHT |- *.
    pose proof Forall_ccw_ind' p q T0 T'.
    tauto.
Qed.

Theorem sort_aux_conv : forall (p : point) (T : list point),
  sort_aux p T -> sort_aux p (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof sort_aux_ind p a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; simpl in H1; rewrite H1 in *; rewrite H2;
  destruct H; split.
  - pose proof Forall_ccw_conv a p T H.
    rewrite <- H1. assumption.
  - assumption.
  - pose proof Forall_ccw_conv a p T H.
    rewrite H1 in H4.
    pose proof Forall_ccw_ind' a p (a0 :: T0) T'.
    apply (H5 H4).
  - destruct IHT.
    pose proof sort_aux_ind' p T0 T'.
    apply (H6 H5).
Qed.

Theorem sort_aux_convex_ind : forall (p q : point) (T : list point),
  sort_aux p (q :: T) -> is_convex p T -> is_convex p (graham_scan_inc q T).
Proof.
  intros. destruct H.
  destruct T; try eauto.
  generalize dependent p0.
  induction T; intros; simpl; try eauto.
  destruct (ccw_dec a p0 q).
  - rewrite Forall_ccw_cons_iff in H.
    destruct H as [H _].
    repeat split; try assumption;
    try (apply ccw_cyclicity; assumption);
    try (apply ccw_cyclicity_2; assumption).
  - pose proof IHT a.
    pose proof Forall_ccw_ind q p p0 [] (a :: T) H.
    pose proof sort_aux_ind p p0 [] (a :: T) H1.
    pose proof convex_ind p p0 (a :: T) H0.
    specialize (H2 H3 H4 H5). assumption.
Qed.


(** Prove that if a list of point is sorted by p, then it will be convex after applying graham_scan. *)
Theorem graham_convex_1 : forall (p : point) (T : list point),
  sort p T -> is_convex p (graham_scan T).
Proof.
  unfold sort, sort_aux; intros. destruct H as [_ H].
  induction T; simpl; try eauto.
  pose proof sort_aux_ind p a [] T H. specialize (IHT H0).
  pose proof sort_aux_convex_ind p a (graham_scan T).
  apply H1; try assumption. clear H0 H1.
  simpl in *. destruct H. split.
  - apply Forall_ccw_conv. assumption.
  - apply sort_aux_conv. assumption.
Qed.

(* ===================== *)

(* (* TODO: check predicate *)
(** sort -> g_ccw_list /\ consec_ccw ? *)
Lemma sort_pred : forall p T,
  sort p T -> g_ccw_list p T /\ consec_ccw (p :: T).
Proof.
  destruct T; intros.
  - unfold g_ccw_list, consec_ccw. tauto.
  - split.
    + induction T; simpl; split; try tauto.
      * rewrite Forall_nil_iff. tauto.
      * pose proof sort_aux_ind p a nil (p0 :: T).
        pose proof sort_ind p [a] (p0 :: T).
(*       * rewrite consec_ccw_cons_iff in H. *)
Abort. *)

Lemma in_hull_0 : forall p T a0,
  sort_aux p (a0 :: T) -> point_in_hull a0 p (a0 :: T).
Proof.
  intros.
  destruct T; simpl; try eauto.
  left.
  unfold point_in_triangle. right.
  repeat split; try apply g_ccw_rep.
  destruct H as [? [_]]. unfold Forall_ccw in H.
  apply Forall_cons_iff in H. destruct H as [? _].
  apply ccw_g_ccw. apply ccw_cyclicity_2. eauto.
Qed.

(** False *)
(* Lemma in_hull_rec : forall p T a0 q,
  sort_aux p (a0 :: T) ->
  point_in_hull q p (graham_scan T) ->
  point_in_hull q p (graham_scan (a0 :: T)).
Proof.
  intros; simpl.
  induction T; simpl; try eauto.
  destruct H as [? [? ?]].
  simpl in IHT.
  assert (Forall_ccw a0 p T /\ sort_aux p T).
  {
    split; try assumption.
    pose proof Forall_ccw_app a0 p [a] T as [? _].
    specialize (H3 H). destruct H3 as [_ ?]; eauto.
  }
  specialize (IHT H3).
  pose proof succ_stack a (graham_scan T) as [T0 [T1 [Hsp Hs]]].
Abort. *)

Lemma hull_inc : forall p a T,
  sort_aux p (a :: T) ->
  is_max_hull' p (graham_scan T) T ->
  is_max_hull' p (graham_scan (a :: T)) (a :: T).
Proof.
  unfold is_max_hull'; intros.
  induction T. 1: { simpl. eauto. }
  destruct H as [? [? ?]].
  - (* ccw a0 p0 a *)

(*   (*
  IHT: Forall
        (fun q : point =>
         point_in_hull q p (graham_scan T)) T ->
      Forall
        (fun q : point =>
         point_in_hull q p
           (graham_scan_inc a (graham_scan T)))
        (a :: T)
  H3: Forall_ccw a p T
  H4: sort_aux p (a :: T)
  1/1
  Forall
    (fun q : point =>
    point_in_hull q p
      (graham_scan_inc a
          (graham_scan_inc a0 (graham_scan T))))
    (a :: a0 :: T) *)
  (** foldr ? *)
  assert (Forall_ccw a p T). { pose proof Forall_inv_tail H. eauto. }
  assert (sort_aux p (a :: T)). { simpl. eauto. }
  rewrite Forall_cons_iff in H0; destruct H0.
  apply Forall_cons_iff; split. clear H3.
  2: {
    pose proof succ_stack a (graham_scan_inc a0 (graham_scan T)) as [T1 [T2 [Hsp Hi]]].
    pose proof succ_stack a0 (graham_scan T) as [T1' [T2' [Hsp' Hi']]].
    simpl in *.
    apply Forall_cons_iff; split.
    -  *)
Admitted.

Theorem graham_convex_2 : forall p T,
  sort p T -> is_max_hull' p (graham_scan T) T.
Proof.
  unfold sort; intros. destruct H as [_ H].
  induction T; simpl; try eauto.
  - unfold is_max_hull'; eauto.
  - pose proof sort_aux_ind p a [] T H. specialize (IHT H0).
    clear H0.
    apply hull_inc; assumption.
Admitted.
