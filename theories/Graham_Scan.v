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
    | s :: _ =>
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

(** append point AFTER pop several points *)

Fixpoint graham_scan (l: list point) : list point :=
  (* fold_right graham_scan_inc nil l *)
  match l with
  | p :: l' => graham_scan_inc p (graham_scan l')
  | _ => nil
  end.

Fixpoint graham_scan_inc' (p : point) (T : list point) : list point :=
  match T with
  | p1 :: T' =>
    match T' with
    | p0 :: _ =>
      match (ccw_dec p0 p1 p) with
      | left _ => T
      | right _ => graham_scan_inc' p T'
      end
    | _ => T
    end
  | _ => T
  end.

Definition graham_scan' (l : list point) : list point :=
  match l with
  | p :: l' => p :: (graham_scan_inc' p l')
  | _ => nil
  end.

(** Simple case *)
(*  After init,
the vertices on T are the vertices of C_2
in clockwise order. *)
Theorem graham_convex_0 : forall (p q r : point),
  rev_ccw_list p [p ; q ; r] -> is_convex p (graham_scan [p ; q ; r]).
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

Lemma graham_scan_subset : forall p T,
  sort p T ->
  (forall x,
  In x (graham_scan T) ->
  In x T).
Proof.
  induction T; [tauto| ].
  intros. simpl in H0.
  pose proof succ_stack a (graham_scan T) as [? [? [? ?]]].
  rewrite H1, H2 in *.
  destruct H0; [ left; tauto| ].
  right. apply IHT.
  - pose proof sort_ind p [a] T H. tauto.
  - pose proof in_or_app x0 x1 x as H3.
    apply H3. tauto.
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

Theorem rev_ccw_list_conv : forall (p : point) (T : list point),
  rev_ccw_list p T -> rev_ccw_list p (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof rev_ccw_list_ind p a [] T H.
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
    pose proof rev_ccw_list_ind' p T0 T'.
    apply (H6 H5).
Qed.

Theorem rev_ccw_list_convex_ind : forall (p q : point) (T : list point),
  rev_ccw_list p (q :: T) -> is_convex p T -> is_convex p (graham_scan_inc q T).
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
    pose proof rev_ccw_list_ind p p0 [] (a :: T) H1.
    pose proof convex_ind p p0 (a :: T) H0.
    specialize (H2 H3 H4 H5). assumption.
Qed.


(** Prove that if a list of point is sorted by p, then it will be convex after applying graham_scan. *)
Theorem graham_convex_1 : forall (p : point) (T : list point),
  sort p T -> is_convex p (graham_scan T).
Proof.
  unfold sort, rev_ccw_list; intros. destruct H as [_ H].
  induction T; simpl; try eauto.
  pose proof rev_ccw_list_ind p a [] T H. specialize (IHT H0).
  pose proof rev_ccw_list_convex_ind p a (graham_scan T).
  apply H1; try assumption. clear H0 H1.
  simpl in *. destruct H. split.
  - apply Forall_ccw_conv. assumption.
  - apply rev_ccw_list_conv. assumption.
Qed.

(* ===================== *)

Lemma sort_rev_ccw_list : forall p T,
  sort p T ->
  rev_ccw_list p T.
Proof.
  intros. destruct H as [_ ?]. revert p H.
  induction T; intros.
  - simpl; eauto.
  - pose proof rev_ccw_list_ind p a nil T H as H_.
    specialize (IHT p H_); clear H_.
    split; destruct H; eauto.
Qed.

Lemma sort_gs_ccw_list : forall p T,
  sort p T ->
  rev_ccw_list p (graham_scan T).
Proof.
  intros.
  pose proof sort_rev_ccw_list _ _ H as H0.
  induction T; intros.
  - tauto.
  - simpl.
    pose proof rev_ccw_list_app_iff p [a] T as [Hs1 _]. 
    pose proof sort_ind p [a] T H as Hs0.
    specialize (Hs1 H0) as [_ [Hs1 _]].
    specialize (IHT Hs0 Hs1). clear Hs0 Hs1.
    pose proof rev_ccw_list_app_iff p [a] (graham_scan T) as [_ ?].
    assert (rev_ccw_list p (a :: (graham_scan T))).
    {
      apply H1. split.
      - simpl; split; [apply Forall_nil | tauto].
      - split; [tauto| ].
        simpl; intros.
        destruct H2; [| tauto].
        subst. clear H1.
        pose proof graham_scan_subset p T (sort_ind p [q] T H).
        assert (In r T). { apply H1. eauto. }
        destruct H0 as [? _].
        unfold Forall_ccw in H0.
        rewrite Forall_forall in H0. apply H0. eauto.
    }
    pose proof succ_stack a (graham_scan T) as [? [? [? ?]]].
    rewrite H4. rewrite H3 in IHT, H2.
    pose proof rev_ccw_list_remove_middle p [a] x x0 H2.
    eauto.
Qed.

(* Print graham_convex_1. *)
(* forall (p : point) (T : list point),
   sort p T -> is_convex p (graham_scan T) *)

Lemma sort_gs_consec_ccw : forall p T,
  sort p T ->
  rev_consec_ccw (graham_scan T).
Proof.
  intros.
  pose proof graham_convex_1 p T H.
  remember (graham_scan T) as l.
  clear Heql.
  induction l; eauto.
  destruct l; [ simpl; tauto |].
  destruct l; [ simpl; tauto |].
  destruct H0 as [? [? ?]].
  specialize (IHl H2).
  split.
  - apply ccw_cyclicity. tauto.
  - tauto.
Qed.

(* TODO *)
Lemma is_max_hull'_pop : forall p a b c l T,
  rev_ccw_list p (c :: b :: a :: l) ->
  rev_consec_ccw (b :: a :: l) ->
  ~ ccw a b c ->
  is_max_hull' p (b :: a :: l) T ->
  is_max_hull' p (c :: a :: l) T.
Proof.
  unfold is_max_hull'; intros.
  simpl; simpl in H2.
  assert (point_in_triangle b c a p).
  {
    pose proof rev_ccw_list_remove_middle p [c] [b] (a :: l) H as [Hac _].
    destruct H as [Hbc [Hab _]]. unfold Forall_ccw in Hbc, Hab, Hac. simpl in Hac.
    rewrite !Forall_cons_iff in Hbc, Hab, Hac. destruct Hbc, Hab, Hac.
    clear H3 H5.
    assert (point_in_triangle b p c a). { apply point_in_tri_general; tauto. }
    do 2 apply point_in_tri_cyclicity in H3. tauto.
  }
  assert (forall q, point_in_triangle q b a p ->
                    point_in_triangle q c a p).
  {
    intros.
    pose proof rev_ccw_list_remove_middle p [c] [b] (a :: l) H as [Hac _].
    destruct H as [Hbc [Hab _]]. unfold Forall_ccw in Hbc, Hab, Hac. simpl in Hac.
    rewrite !Forall_cons_iff in Hbc, Hab, Hac. destruct Hbc, Hab, Hac.
    assert (~ ccw c a p). { apply ccw_anti_symmetry in H8. tauto. }
    pose proof point_in_tri_incl _ _ _ _ H10 H3 _ H4.
    tauto.
  }
  rewrite Forall_forall in H2. rewrite Forall_forall.
  intros. specialize (H2 x H5).
  destruct H2.
  - left. apply (H4 x). tauto.
  - right. tauto.
Qed.

(** Prove that stack incrementation preserves is_max_hull' *)
Lemma hull_inc : forall p a T,
  sort p (a :: T) ->
  is_max_hull' p (graham_scan T) T ->
  is_max_hull' p (graham_scan (a :: T)) T.
Proof.
  intros. simpl.
  pose proof sort_gs_consec_ccw p (a :: T) H as Hconsec.
  pose proof sort_ind p [a] T H as H_.
  pose proof sort_gs_consec_ccw p T H_.
  pose proof sort_gs_ccw_list p (a :: T) H as Hcl. clear H_.
  pose proof H as H_. destruct H_ as [_ Hcl0].
  simpl in Hconsec, Hcl, H1.
  remember (graham_scan T) as l. clear Heql.
  destruct l. 1: { unfold is_max_hull'. simpl. eauto. }
  revert p0 H H0 H1 Hconsec Hcl.
  induction l. 1: {
    unfold is_max_hull' in *.
    simpl; intros.
    destruct T.
    - apply Forall_nil.
    - pose proof (forall_false_elim _ _ H0). tauto.
  }

  intros. simpl. simpl in Hconsec, Hcl.
  (** is_max_hull' p (graham_scan_inc a (p0 :: a0 :: l)) T *)
  destruct (ccw_dec a0 p0 a). 1: { apply is_max_hull'_cons. tauto. }
  (** (1/1): is_max_hull' p (graham_scan_inc a (a0 :: l)) T *)
  apply (IHl a0); try tauto.
  - (** Hconsec : rev_consec_ccw (graham_scan_inc a (a0 :: l))*)
    (** Hcl: rev_ccw_list p (graham_scan_inc a (a0 :: l)) *)
    give_up.
  - apply rev_consec_ccw_cons_iff in H1 as [? _]. eauto.
Admitted.

Theorem graham_convex_2 : forall p T,
  sort p T -> is_max_hull' p (graham_scan T) T.
Proof.
  induction T; [unfold is_max_hull'; eauto|].
  intros.
  pose proof sort_ind _ [a] _ H as H_.
  specialize (IHT H_); clear H_.
  unfold is_max_hull'. rewrite Forall_cons_iff; split.
  - simpl.
    pose proof succ_stack a (graham_scan T) as [? [? [? ?]]].
    rewrite H1.
    destruct x0.
    + (** point_in_hull 2-point *)
      admit.
    + left. admit.
  - apply hull_inc; tauto.
Admitted.
