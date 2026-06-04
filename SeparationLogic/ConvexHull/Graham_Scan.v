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

Theorem Forall_g_rev_ccw_conv : forall (p q : point) (T : list point),
  Forall_g_rev_ccw p q T -> Forall_g_rev_ccw p q (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof Forall_g_rev_ccw_ind p q a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; rewrite H1 in *; rewrite H2.
  - rewrite Forall_g_rev_ccw_cons_iff in H |- *.
    tauto.
  - simpl in IHT.
    rewrite Forall_g_rev_ccw_cons_iff in H, IHT |- *.
    pose proof Forall_g_rev_ccw_ind' p q T0 T'.
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

Theorem g_rev_ccw_list_conv : forall (p : point) (T : list point),
  g_rev_ccw_list p T -> g_rev_ccw_list p (graham_scan T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof g_rev_ccw_list_ind' p [a] T H.
  specialize (IHT H0).
  pose proof succ_stack a (graham_scan T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; simpl in H1; rewrite H1 in *; rewrite H2;
  destruct H; split.
  - pose proof Forall_g_rev_ccw_conv p a T H.
    rewrite <- H1. assumption.
  - assumption.
  - pose proof Forall_g_rev_ccw_conv p a T H.
    rewrite H1 in H4.
    pose proof Forall_g_rev_ccw_ind' p a (a0 :: T0) T'.
    apply (H5 H4).
  - destruct IHT.
    pose proof g_rev_ccw_list_ind' p T0 T'.
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

Theorem g_rev_ccw_list_convex_ind : forall (p q : point) (T : list point),
  g_rev_ccw_list p (q :: T) -> is_convex p T -> is_convex p (graham_scan_inc q T).
Proof.
  intros. destruct H.
  destruct T; try eauto.
  generalize dependent p0.
  induction T; intros; simpl; try eauto.
  destruct (ccw_dec a p0 q).
  - rewrite Forall_g_rev_ccw_cons_iff in H.
    destruct H as [Hqp0 Hqa].
    repeat split; try assumption;
    try (apply ccw_cyclicity; assumption);
    try (apply ccw_cyclicity_2; assumption).
    rewrite Forall_g_rev_ccw_cons_iff in Hqa.
    destruct Hqa as [Hqa _].
    exact (g_rev_ccw_head_strict p q p0 a Hqp0 Hqa c).
  - pose proof IHT a.
    pose proof Forall_g_rev_ccw_ind p q p0 [] (a :: T) H.
    pose proof g_rev_ccw_list_ind' p [p0] (a :: T) H1.
    pose proof convex_ind p p0 (a :: T) H0.
    specialize (H2 H3 H4 H5). assumption.
Qed.


(** Prove that if a list of point is sorted by p, then it will be convex after applying graham_scan. *)
Theorem graham_convex_1 : forall (p : point) (T : list point),
  sort p T -> is_convex p (graham_scan T).
Proof.
  unfold sort; intros. destruct H as [_ H].
  induction T; simpl; try eauto.
  pose proof g_rev_ccw_list_ind' p [a] T H. specialize (IHT H0).
  pose proof g_rev_ccw_list_convex_ind p a (graham_scan T) as H1.
  apply H1; try assumption. clear H0 H1.
  simpl in *. destruct H. split.
  - apply Forall_g_rev_ccw_conv. assumption.
  - apply g_rev_ccw_list_conv. assumption.
Qed.

(* ===================== *)

Lemma sort_g_rev_ccw_list : forall p T,
  sort p T ->
  g_rev_ccw_list p T.
Proof.
  intros. destruct H as [_ ?]. tauto.
Qed.

Lemma sort_gs_g_rev_ccw_list : forall p T,
  sort p T ->
  g_rev_ccw_list p (graham_scan T).
Proof.
  intros.
  destruct H as [_ H].
  apply g_rev_ccw_list_conv.
  exact H.
Qed.

Lemma sort_gs_g_rev_ccw_list' : forall p a T,
  sort p (a :: T) ->
  g_rev_ccw_list p (a :: graham_scan T).
Proof.
  intros.
  destruct H as [_ [? ?]].
  split.
  - apply Forall_g_rev_ccw_conv; tauto.
  - apply g_rev_ccw_list_conv; tauto.
Qed.

(* Print graham_convex_1. *)
(* forall (p : point) (T : list point),
   sort p T -> is_convex p (graham_scan T) *)

Lemma is_convex_rev_consec : forall p T,
  is_convex p T ->
  rev_consec_ccw T.
Proof.
  intros p T.
  induction T as [| a T IH]; intros Hconv; simpl in *; try tauto.
  destruct T as [| b T']; simpl in *; try tauto.
  destruct T' as [| c T'']; simpl in *; try tauto.
  destruct Hconv as [Habc [_ Htail]].
  split.
  - apply ccw_cyclicity.
    exact Habc.
  - apply IH.
    exact Htail.
Qed.

Lemma sort_gs_consec_ccw : forall p T,
  sort p T ->
  rev_consec_ccw (graham_scan T).
Proof.
  intros p T Hsort.
  apply (is_convex_rev_consec p (graham_scan T)).
  apply graham_convex_1.
  exact Hsort.
Qed.

(* TODO *)
Lemma is_max_hull'_pop : forall p a b c l T,
  rev_ccw_list p (c :: b :: a :: l) -> (** well formed *)
  rev_consec_ccw (b :: a :: l) -> (** convex *)
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
    destruct H as [Hbc [Hab _]].
    rewrite Forall_ccw_forall in Hbc, Hab.
    assert (ccw c p a) as Hcpa.
    { apply Hbc. simpl. tauto. }
    assert (ccw b p a) as Hbpa.
    { apply Hab. simpl. tauto. }
    pose proof (point_in_tri_incl p a b c H3
      (ccw_cyclicity _ _ _ Hcpa) Hbpa q H4).
    tauto.
  }
  rewrite Forall_forall in H2. rewrite Forall_forall.
  intros. specialize (H2 x H5).
  destruct H2.
  - left. apply (H4 x). tauto.
  - right. tauto.
Qed.

Lemma is_max_hull'_pop' : forall p a b c l T,
  (** should `rev_ccw_list` be included in `is_max_hull'` ? *)
  rev_ccw_list p (c :: b :: a :: l) ->
  rev_consec_ccw (b :: a :: l) ->
  ~ ccw a b c ->
  is_max_hull' p (c :: b :: a :: l) T ->
  is_max_hull' p (c :: a :: l) T.
Proof.
  unfold is_max_hull' in *; intros.
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
    destruct H as [Hbc [Hab _]].
    rewrite Forall_ccw_forall in Hbc, Hab.
    assert (ccw c p a) as Hcpa.
    { apply Hbc. simpl. tauto. }
    assert (ccw b p a) as Hbpa.
    { apply Hab. simpl. tauto. }
    pose proof (point_in_tri_incl p a b c H3
      (ccw_cyclicity _ _ _ Hcpa) Hbpa q H4).
    tauto.
  }
  assert (forall q, point_in_triangle q c b p ->
                    point_in_triangle q c a p).
  {
    intros.
    destruct H as [Hbc [_ _]].
    rewrite Forall_ccw_forall in Hbc.
    assert (ccw c p a) as Hcpa.
    { apply Hbc. simpl. tauto. }
    assert (ccw c p b) as Hcpb.
    { apply Hbc. simpl. tauto. }
    eapply point_in_tri_incl'; eauto.
  }
  rewrite Forall_forall in H2; rewrite Forall_forall.
  intros x _H; specialize (H2 x _H); clear _H.
  destruct H2 as [? | [? | ?]].
  - (** x ∈ Δcbp -> x ∈ Δcap *)
    left.
    apply H5. tauto.
  - (** x ∈ Δbap -> x ∈ Δcap *)
    left.
    apply H4. tauto.
  - (** x ∈ [a :: l] -> x ∈ [a :: l] *)
    right; tauto.
Qed.

Lemma is_max_hull'_pop'_g : forall p a b c l T,
  g_rev_ccw_list p (c :: b :: a :: l) ->
  ~ ccw a b c ->
  is_max_hull' p (c :: b :: a :: l) T ->
  is_max_hull' p (c :: a :: l) T.
Proof.
  unfold is_max_hull' in *.
  intros p a b c l T Hg Hn Hmax.
  simpl in Hg.
  destruct Hg as [Hc [Hb _]].
  rewrite Forall_g_rev_ccw_cons_iff in Hc.
  destruct Hc as [Hcb Hc].
  rewrite Forall_g_rev_ccw_cons_iff in Hc.
  destruct Hc as [Hca _].
  rewrite Forall_g_rev_ccw_cons_iff in Hb.
  destruct Hb as [Hba _].
  apply g_rev_ccw_iff_weak_rev_ccw in Hcb.
  apply g_rev_ccw_iff_weak_rev_ccw in Hca.
  apply g_rev_ccw_iff_weak_rev_ccw in Hba.
  rewrite Forall_forall in Hmax.
  rewrite Forall_forall.
  intros x HIn.
  specialize (Hmax x HIn).
  simpl in Hmax |- *.
  destruct Hmax as [Hcbp | [Hbap | Htail]].
  - left.
    exact (point_in_tri_pop_right_weak p a b c x Hcb Hca Hba Hn Hcbp).
  - left.
    exact (point_in_tri_pop_left_weak p a b c x Hcb Hca Hba Hn Hbap).
  - right. exact Htail.
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
  pose proof sort_gs_g_rev_ccw_list' p a T H as Hcl.
  clear H_.
  (** assert (is_max_hull' p (a :: graham_scan T) T) *)
  simpl in Hconsec, Hcl, H1.
  remember (graham_scan T) as l. clear Heql.
  assert (is_max_hull' p (a :: l) T).
    {
      destruct l.
      - unfold is_max_hull' in *. simpl in *.
        destruct T; [apply Forall_nil|].
        pose proof (forall_false_elim _ _ H0). tauto.
      - destruct l.
        + unfold is_max_hull' in *. simpl in *.
          destruct Hcl as [Hcl _];
          rewrite Forall_g_rev_ccw_cons_iff in Hcl;
          destruct Hcl as [Hcl _].
          rewrite Forall_forall in H0; rewrite Forall_forall.
          intros.
          pose proof (H0 x) H2. left.
          destruct H3 as [Hcol Hmid].
          exact (point_in_tri_weak_edge p x a p0 Hcl Hcol Hmid).
        +
          unfold is_max_hull' in *.
          rewrite Forall_forall in H0. rewrite Forall_forall.
          intros x HIn. specialize (H0 x HIn).
          simpl in H0 |- *.
          right. exact H0.
    }
  destruct l. 1: { unfold is_max_hull'. simpl. tauto. }
  clear H0.
  revert p0 H1 H2 Hconsec Hcl.
  induction l. 1: {
    unfold is_max_hull' in *.
    simpl; intros.
    destruct T; tauto.
  }
  intros.
  simpl. simpl in Hconsec.
  (** is_max_hull' p (graham_scan_inc a (p0 :: a0 :: l)) T *)
  destruct (ccw_dec a0 p0 a). 1: { tauto. }
  (** Hconsec : rev_consec_ccw (graham_scan_inc a (a0 :: l))*)
  (** Hcl: g_rev_ccw_list p (graham_scan_inc a (a0 :: l)) *)
  (** (1/1): is_max_hull' p (graham_scan_inc a (a0 :: l)) T *)
  (* ? *)
  apply (IHl a0); try tauto.
  - apply rev_consec_ccw_cons_iff in H1 as [? _]. tauto.
  (** is_max_hull' p (a :: p0 :: a0 :: l) T -> is_max_hull' p (a :: a0 :: l) T *)
  - apply (is_max_hull'_pop'_g p a0 p0 a l T).
    + exact Hcl.
    + assumption.
    + assumption.
  - pose proof g_rev_ccw_list_remove_middle p [a] [p0] (a0 :: l) Hcl as Hcl'.
    exact Hcl'.
Qed.

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
    + (** point_in_hull 2point *)
      simpl;
      unfold colinear, parallel, at_mid, backward_or_perp;
      unfold cross_prod, dot_prod;
      simpl; split; lia.
    + left.
      apply point_in_tri_1.
      pose proof sort_gs_g_rev_ccw_list' p a T H as Hcl.
      rewrite H0 in *.
      simpl in Hcl.
      destruct Hcl as [Ha _].
      rewrite Forall_g_rev_ccw_forall in Ha.
      specialize (Ha p0 ltac:(rewrite in_app_iff; simpl; tauto)).
      destruct Ha as [Hap0 | [Hcol Hmid]].
      * exact (ccw_anti_symmetry _ _ _ Hap0).
      * unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *;
        simpl in *; nia.
  - apply hull_inc; tauto.
Qed.
