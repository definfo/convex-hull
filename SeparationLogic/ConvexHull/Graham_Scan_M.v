(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point Graham_Scan Hull_Equiv.
From SetsClass Require Import SetsClass.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad StateRelHoare FixpointLib.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad StateRelHoare FixpointLib.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
(* /COQ-HEAD *)

Definition rev_ccw_convex (T : list point) : Prop :=
  forall l1 q l2 r l3 s l4,
    T = l1 ++ q :: l2 ++ r :: l3 ++ s :: l4 ->
    ccw s r q.

Definition is_convex_hull (base T : list point) : Prop :=
  rev_ccw_convex T /\
  is_max_hull'_edges T base.




Fixpoint iter
           {A B: Type}
           (f: A -> B -> program (list A) B)
           (l: list A)
           (b: B): program (list A) B :=
  match l with
  | nil => ret b
  | a :: l0 =>
    b0 <- f a b ;;
    iter f l0 b0
  end.


(** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) **)
Definition pop_fun (p: point) : program (list point) (CntOrBrk unit unit) :=
  T <- get' id ;;
  match T with
  | t :: s :: T' =>
      choice
        (assume!! (ccw s t p) ;;
         ret (by_break tt))
        (assume!! (~ ccw s t p) ;;
         update' (fun _ => s :: T') ;;
         ret (by_continue tt))
  (* Less than 2 elements in stack: break out of the loop *)
  | _ =>
      ret (by_break tt)
  end.
  
(** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) { pop(&T); }; push(p);  **)
Definition step_fun (p : point) : program (list point) unit :=
  repeat_break (fun _ => pop_fun p) tt ;;
  T <- get' id ;;
  update' (fun _ => p :: T).

Definition step_p (p: point) (_: unit) : program (list point) unit :=
  step_fun p.

Definition build_hull (p: point) (l: list point) : program (list point) unit :=
  update' (fun _ => (p :: nil)) ;;
  iter step_p l tt.


Lemma pop_fun_preserves_graham_scan_inc : forall p T0,
  Hoare
    (fun T => graham_scan_inc p T0 = graham_scan_inc p T)
    (pop_fun p)
    (fun x T =>
       match x with
       | by_continue _ => graham_scan_inc p T0 = graham_scan_inc p T
       | by_break _ => graham_scan_inc p T0 = p :: T
       end).
Proof.
  intros p T0.
  unfold pop_fun.
  intro_state.
  destruct s0 as [| t [| s T]]; simpl in *.
  - hoare_auto_s; subst; simpl in *.
    apply Hoare_ret'; intros T' ->.
    exact H.
  - hoare_auto_s; subst; simpl in *.
    apply Hoare_ret'; intros T' ->.
    exact H.
  - destruct (ccw_dec s t p) as [Hccw | Hnccw].
    + hoare_auto_s; subst; simpl.
      apply Hoare_choice.
      * apply Hoare_assume_bind'. intros _.
        apply Hoare_ret'. intros T' ->.
        exact H.
      * apply Hoare_assume_bind'. intros Hbad.
        contradiction.
    + hoare_auto_s; subst; simpl.
      apply Hoare_choice.
      * apply Hoare_assume_bind'. intros Hbad.
        contradiction.
      * apply Hoare_assume_bind'. intros _.
        eapply Hoare_bind.
        -- apply Hoare_update'.
        -- intros [].
           apply Hoare_ret'. intros T' ->.
           exact H.
Qed.

Lemma repeat_pop_fun_correct : forall p T0,
  Hoare
    (fun T => T = T0)
    (repeat_break (fun _ : unit => pop_fun p) tt)
    (fun _ T => graham_scan_inc p T0 = p :: T).
Proof.
  intros p T0.
  eapply Hoare_conseq_pre.
  2: {
    eapply (@Hoare_repeat_break (list point) unit unit
      (fun _ : unit => pop_fun p)
      (fun _ T => graham_scan_inc p T0 = graham_scan_inc p T)
      (fun _ T => graham_scan_inc p T0 = p :: T)).
    intros [].
    apply pop_fun_preserves_graham_scan_inc.
  }
  simpl.
  intros T ->.
  reflexivity.
Qed.

Lemma step_fun_correct : forall p T0,
  Hoare
    (fun T => T = T0)
    (step_fun p)
    (fun _ T => T = graham_scan_inc p T0).
Proof.
  intros p T0.
  unfold step_fun.
  eapply Hoare_bind.
  - apply repeat_pop_fun_correct.
  - intros [].
    eapply Hoare_bind.
    + eapply Hoare_get.
    + intros T.
      eapply Hoare_conseq_post.
      2: eapply Hoare_update.
      simpl.
      intros [] T' [Told [HT' [HTold Hpre]]].
      subst T' T.
      symmetry.
      exact Hpre.
Qed.

Lemma iter_step_p_correct : forall l T0,
  Hoare
    (fun T => T = T0)
    (iter step_p l tt)
    (fun _ T => T = fold_left (fun T p => graham_scan_inc p T) l T0).
Proof.
  induction l as [| p l IH]; intros T0; simpl.
  - apply Hoare_ret'.
    intros T ->.
    reflexivity.
  - eapply Hoare_bind.
    + unfold step_p.
      apply step_fun_correct.
    + intros [].
      apply IH.
Qed.

Lemma build_hull_stack_correct : forall p l,
  Hoare
    (fun T => T = [])
    (build_hull p l)
    (fun _ T => T = fold_left (fun T p => graham_scan_inc p T) l [p]).
Proof.
  intros p l.
  unfold build_hull.
  eapply Hoare_bind.
  - eapply Hoare_update'.
  - intros [].
    eapply Hoare_conseq_pre.
    2: apply iter_step_p_correct.
    simpl.
    intros T ->.
    reflexivity.
Qed.

Lemma fold_left_graham_scan_inc_cons : forall p l,
  fold_left (fun T q => graham_scan_inc q T) l [p] =
  graham_scan (rev (p :: l)).
Proof.
  assert (Hfold : forall l,
    graham_scan l = fold_right graham_scan_inc [] l).
  {
    induction l as [| q l IH]; simpl.
    - reflexivity.
    - f_equal.
  }
  intros p l.
  rewrite Hfold.
  rewrite fold_left_rev_right.
  simpl.
  reflexivity.
Qed.

Theorem build_hull_hoare_final : forall p l,
  Hoare (fun T0 => T0 = [])
        (build_hull p l)
        (fun _ T' => T' = graham_scan (rev (p :: l))).
Proof.
  intros p l.
  eapply Hoare_conseq_post.
  2: apply build_hull_stack_correct.
  intros [] T HT.
  rewrite HT.
  apply fold_left_graham_scan_inc_cons.
Qed.

Lemma gs_rev_ccw_list_rev_ccw_list : forall p l,
  rev_ccw_list p l ->
  ccw_list p (rev l).
Proof.
  intros p l.
  induction l as [| a l IH]; simpl; intros Hrev.
  - exact I.
  - destruct Hrev as [Ha Htail].
    rewrite ccw_list_app_iff.
    repeat split.
    + apply IH.
      exact Htail.
    + rewrite Forall_ccw_nil_iff.
      exact I.
    + intros q r Hq Hr.
      simpl in Hr.
      destruct Hr as [Hr | []].
      subst r.
      rewrite Forall_ccw_forall in Ha.
      apply ccw_cyclicity.
      apply Ha.
      rewrite in_rev.
      exact Hq.
Qed.

Definition first_anchor_strict (p : point) (l : list point) : Prop :=
  match l with
  | a :: b :: _ => ccw p a b
  | _ => True
  end.

Lemma g_rev_ccw_to_g_ccw_rev : forall p q r,
  g_rev_ccw p r q ->
  g_ccw p q r.
Proof.
  intros p q r H.
  rewrite g_rev_ccw_iff_g_ccw_rev in H.
  exact H.
Qed.

Lemma g_rev_ccw_list_to_g_ccw_list_rev : forall p l,
  g_rev_ccw_list p l ->
  g_ccw_list p (rev l).
Proof.
  intros p l.
  induction l as [| a l IH]; simpl; intros Hrev.
  - exact I.
  - destruct Hrev as [Ha Htail].
    rewrite g_ccw_list_app_iff.
    repeat split.
    + apply IH.
      exact Htail.
    + simpl.
      apply Forall_nil.
    + intros q r Hq Hr.
      simpl in Hr.
      destruct Hr as [Hr | []].
      subst r.
      rewrite Forall_g_rev_ccw_forall in Ha.
      apply g_rev_ccw_to_g_ccw_rev.
      apply Ha.
      rewrite in_rev.
      exact Hq.
Qed.

Lemma gs_rev_consec_ccw_rev_consec : forall l,
  rev_consec_ccw l ->
  consec_ccw (rev l).
Proof.
  intros l.
  pattern l.
  apply rev_ind.
  - simpl.
    tauto.
  - intros a l0 IH Hrev.
    rewrite rev_app_distr.
    change (rev [a]) with [a].
    change ([a] ++ rev l0) with (a :: rev l0).
    rewrite consec_ccw_cons_iff.
    rewrite rev_consec_ccw_snoc_iff in Hrev.
    destruct Hrev as [Hrev Hlast].
    split.
    + apply IH.
      exact Hrev.
    + intros b c l1 Hshape.
      apply Hlast with (l0 := rev l1).
      apply (f_equal (@rev point)) in Hshape.
      rewrite rev_involutive in Hshape.
      simpl in Hshape.
      rewrite <- app_assoc in Hshape.
      exact Hshape.
Qed.

Lemma gs_rev_consec_ccw_anchor_consec : forall p CH,
  rev_consec_ccw CH ->
  first_anchor_strict p (rev CH) ->
  consec_ccw (p :: rev CH).
Proof.
  intros p CH Hconsec Hanchor.
  rewrite consec_ccw_cons_iff.
  split.
  - apply gs_rev_consec_ccw_rev_consec.
    exact Hconsec.
  - intros b c l0 Hshape.
    destruct (rev CH) as [| a [| d l]] eqn:Hrev; try discriminate.
    inversion Hshape; subst.
    simpl in Hanchor.
    exact Hanchor.
Qed.

Lemma gs_ccw_convex_forall3_inv : forall l,
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

Lemma gs_ccw_convex_rev_to_rev_ccw_convex : forall T,
  ccw_convex (rev T) ->
  rev_ccw_convex T.
Proof.
  intros T Hconv.
  unfold rev_ccw_convex.
  intros l1 q l2 r l3 s l4 Heq.
  assert (HeqT : rev T = rev (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)).
  { rewrite Heq. reflexivity. }
  eapply (gs_ccw_convex_forall3_inv (rev T) Hconv
            (rev l4) s (rev l3) r (rev l2) q (rev l1)).
  rewrite HeqT.
  change (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)
    with (l1 ++ [q] ++ l2 ++ [r] ++ l3 ++ [s] ++ l4).
  repeat rewrite rev_app_distr.
  simpl.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma gs_rev_ccw_convex_anchor : forall p CH,
  sort p CH ->
  rev_consec_ccw CH ->
  first_anchor_strict p (rev CH) ->
  rev_ccw_convex (p :: CH).
Proof.
  intros p CH Hsort Hconsec Hanchor.
  destruct Hsort as [_ Hrev].
  apply gs_ccw_convex_rev_to_rev_ccw_convex.
  simpl.
  apply (ccw_convex_app_comm [p] (rev CH)).
  simpl.
  apply ccw_convex_spec.
  - apply g_rev_ccw_list_to_g_ccw_list_rev.
    exact Hrev.
  - apply gs_rev_consec_ccw_anchor_consec; assumption.
Qed.

Lemma gs_sort_graham_scan : forall p l,
  sort p l ->
  sort p (graham_scan l).
Proof.
  intros p l Hsort.
  assert (Hsort_copy : sort p l) by exact Hsort.
  destruct Hsort as [Hleft Hrev].
  split.
  - unfold leftmost in *.
    rewrite Forall_forall in *.
    intros q Hq.
    apply Hleft.
    eapply graham_scan_subset.
    + exact Hsort_copy.
    + exact Hq.
  - apply sort_gs_g_rev_ccw_list.
    split; [exact Hleft | exact Hrev].
Qed.

Lemma gs_graham_scan_inc_nonempty : forall a T,
  graham_scan_inc a T <> [].
Proof.
  intros a T.
  induction T as [| b T IH]; simpl; try discriminate.
  destruct T as [| c T']; simpl; try discriminate.
  destruct (ccw_dec c b a); [discriminate |].
  exact IH.
Qed.

Lemma gs_graham_scan_nonempty : forall l,
  l <> [] ->
  graham_scan l <> [].
Proof.
  intros l Hne.
  destruct l as [| a l]; [contradiction |].
  simpl.
  apply gs_graham_scan_inc_nonempty.
Qed.

Lemma gs_point_in_hull_anchor : forall p CH,
  CH <> [] ->
  g_rev_ccw_list p CH ->
  point_in_hull p (p :: CH).
Proof.
  intros p CH Hne Hrev.
  destruct CH as [| q CH].
  - contradiction.
  - destruct CH as [| r CH'].
    + simpl.
      split.
      * unfold colinear, parallel, cross_prod, build_vec.
        simpl.
        nia.
      * unfold at_mid, backward_or_perp, dot_prod, build_vec.
        simpl.
        nia.
    + simpl.
      left.
      simpl in Hrev.
      destruct Hrev as [Hfor _].
      rewrite Forall_g_rev_ccw_forall in Hfor.
      apply (point_in_tri_weak_edge p p q r).
      * apply g_rev_ccw_iff_weak_rev_ccw.
        apply Hfor.
        simpl.
        tauto.
      * unfold colinear, parallel, cross_prod, build_vec.
        simpl.
        nia.
      * unfold at_mid, backward_or_perp, dot_prod, build_vec.
        simpl.
        nia.
Qed.

Lemma gs_point_in_hull_edges_anchor : forall p CH,
  sort p CH ->
  rev_consec_ccw CH ->
  CH <> [] ->
  point_in_hull_edges p (p :: CH).
Proof.
  intros p CH Hsort Hconsec Hne.
  destruct Hsort as [Hleft Hrev].
  eapply point_in_hull_equiv.
  - split; [exact Hleft | exact Hrev].
  - exact Hconsec.
  - apply gs_point_in_hull_anchor; assumption.
Qed.

Lemma gs_is_max_hull'_edges_with_anchor : forall p CH l,
  sort p CH ->
  rev_consec_ccw CH ->
  CH <> [] ->
  is_max_hull' p CH l ->
  is_max_hull'_edges (p :: CH) (p :: l).
Proof.
  intros p CH l Hsort Hconsec Hne Hmax.
  unfold is_max_hull'_edges.
  rewrite Forall_cons_iff.
  split.
  - apply gs_point_in_hull_edges_anchor; assumption.
  - eapply is_max_hull'_edges_of_max_hull; eauto.
Qed.

Lemma gs_point_in_hull_edges_aux_snoc_final : forall q p0 p1 l p2,
  point_in_hull_edges_aux_ q p0 p1 l ->
  left_equal (build_vec p0 p2) (build_vec p0 q) ->
  point_in_hull_edges_aux_ q p2 p1 (l ++ [p0]).
Proof.
  intros q p0 p1 l.
  revert p0 p1.
  induction l as [| x l IH]; intros p0 p1 p2 Haux Hlast; simpl in *.
  - split; assumption.
  - destruct Haux as [Haux Hedge].
    split.
    + apply IH; assumption.
    + exact Hedge.
Qed.

Lemma gs_point_in_hull_edges_rotate1 : forall q p0 CH,
  point_in_hull_edges q (p0 :: CH) ->
  point_in_hull_edges q (CH ++ [p0]).
Proof.
  intros q p0 CH Hedges.
  destruct CH as [| p1 CH].
  - simpl in Hedges.
    contradiction.
  - destruct CH as [| p2 post].
    + simpl in *.
      destruct Hedges as [Hcol Hmid].
      split.
      * rewrite colinear_comm.
        exact Hcol.
      * rewrite at_mid_comm.
        exact Hmid.
    + simpl in Hedges.
      destruct Hedges as [Hfirst Haux].
      destruct post as [| p3 post].
      * simpl in *.
        destruct Haux as [Haux Hnext].
        split.
        -- exact Hnext.
        -- split; assumption.
      * simpl in *.
        destruct Haux as [Haux Hnext].
        split.
        -- exact Hnext.
        -- destruct Haux as [Haux Hnext'].
           split.
           ++ apply gs_point_in_hull_edges_aux_snoc_final; assumption.
           ++ exact Hnext'.
Qed.

Lemma gs_is_max_hull'_edges_rotate1 : forall p CH l,
  is_max_hull'_edges (p :: CH) l ->
  is_max_hull'_edges (CH ++ [p]) l.
Proof.
  intros p CH l Hmax.
  unfold is_max_hull'_edges in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply gs_point_in_hull_edges_rotate1.
  apply Hmax.
  exact Hq.
Qed.

Lemma gs_is_max_hull'_edges_cons_rev_tail : forall T p l,
  is_max_hull'_edges T (p :: rev l) ->
  is_max_hull'_edges T (p :: l).
Proof.
  intros T p l Hedges.
  unfold is_max_hull'_edges in *.
  rewrite Forall_cons_iff in *.
  destruct Hedges as [Hp Htail].
  split; [exact Hp |].
  rewrite <- (rev_involutive l).
  apply Forall_rev.
  exact Htail.
Qed.

Lemma gs_rev_ccw_convex_to_ccw_convex_rev : forall T,
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
  do 5 rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Lemma gs_rev_ccw_convex_rotate1 : forall p CH,
  rev_ccw_convex (p :: CH) ->
  rev_ccw_convex (CH ++ [p]).
Proof.
  intros p CH Hconv.
  apply gs_ccw_convex_rev_to_rev_ccw_convex.
  rewrite rev_app_distr.
  change (rev [p]) with [p].
  change ([p] ++ rev CH) with ([p] ++ rev CH).
  apply ccw_convex_app_comm.
  change (rev CH ++ [p]) with (rev (p :: CH)).
  apply gs_rev_ccw_convex_to_ccw_convex_rev.
  exact Hconv.
Qed.

Lemma gs_g_rev_ccw_not_ccw_tail : forall p a b,
  g_rev_ccw p a b ->
  ~ ccw a b p.
Proof.
  intros p a b H.
  apply g_rev_ccw_iff_weak_rev_ccw in H.
  destruct H as [Hccw | [Hcol _]].
  - apply ccw_anti_symmetry.
    exact Hccw.
  - unfold ccw, colinear, left_than, parallel, cross_prod, build_vec in *.
    simpl in *.
    nia.
Qed.

Lemma gs_point_in_hull_self_edge : forall p a,
  point_in_hull a (p :: a :: nil).
Proof.
  intros p a.
  simpl.
  split.
  - unfold colinear, parallel, cross_prod, build_vec.
    simpl.
    nia.
  - unfold at_mid, backward_or_perp, dot_prod, build_vec.
    simpl.
    nia.
Qed.

Lemma gs_point_in_hull_new_head : forall p a C,
  g_rev_ccw_list p (a :: C) ->
  point_in_hull a (p :: a :: C).
Proof.
  intros p a C Hweak.
  destruct C as [| b C].
  - apply gs_point_in_hull_self_edge.
  - simpl.
    left.
    apply point_in_tri_1.
    simpl in Hweak.
    destruct Hweak as [Ha _].
    rewrite Forall_g_rev_ccw_cons_iff in Ha.
    destruct Ha as [Hab _].
    apply gs_g_rev_ccw_not_ccw_tail.
    exact Hab.
Qed.

Lemma gs_is_max_hull'_push : forall p a C L,
  g_rev_ccw_list p (a :: C) ->
  (C = [] -> L = []) ->
  is_max_hull' p C L ->
  is_max_hull' p (a :: C) (a :: L).
Proof.
  intros p a C L Hweak Hempty Hmax.
  unfold is_max_hull' in *.
  rewrite Forall_cons_iff.
  split.
  - apply gs_point_in_hull_new_head.
    exact Hweak.
  - destruct C as [| b C].
    + specialize (Hempty eq_refl).
      subst L.
      apply Forall_nil.
    + rewrite Forall_forall in *.
      intros q Hq.
      pose proof (Hmax q Hq) as Hq_old.
      pose proof (proj2 (point_in_hull_cons_iff_weak q p b a C Hweak)) as Hlift.
      apply Hlift.
      left.
      exact Hq_old.
Qed.

Lemma gs_point_in_hull_pop_single : forall p a b q,
  g_rev_ccw p a b ->
  ~ ccw p b a ->
  point_in_hull q (p :: a :: b :: nil) ->
  point_in_hull q (p :: a :: nil).
Proof.
  intros p a b q Hweak Hnccw Hhull.
  destruct Hweak as [Hstrict | [Hcol Hmid]].
  - exfalso.
    apply Hnccw.
    apply ccw_cyclicity.
    exact Hstrict.
  - simpl in Hhull |- *.
    destruct Hhull as [Hhull | []].
    unfold point_in_triangle in Hhull.
    destruct Hhull as [Htri | [Htri_col Hseg]].
    + destruct Htri as [Hccw [He1 [He2 He3]]].
      unfold ccw, colinear, at_mid, left_equal, left_than, parallel,
             backward_or_perp, build_vec, cross_prod, dot_prod in *.
      simpl in *.
      nia.
    + destruct Hseg as [[Hqcol Hqmid] |
                        [[Hqcol Hqmid] |
                         [Hqcol Hqmid]]].
      * pose proof (segment_mid_trans_left q b a p
          (colinear_perm321 _ _ _ Hcol) Hmid Hqcol Hqmid)
          as [Hqap_col Hqap_mid].
        split.
        -- apply colinear_perm132.
           exact Hqap_col.
        -- apply at_mid_comm.
           exact Hqap_mid.
      * pose proof (segment_mid_trans_right q b a p
          (colinear_perm321 _ _ _ Hcol) Hmid Hqcol Hqmid)
          as [Hqap_col Hqap_mid].
        split.
        -- apply colinear_perm132.
           exact Hqap_col.
        -- apply at_mid_comm.
           exact Hqap_mid.
      * split; assumption.
Qed.

Lemma gs_leftmost_subset : forall p C L,
  leftmost p L ->
  (forall q, In q C -> In q L) ->
  leftmost p C.
Proof.
  intros p C L Hleft Hsub.
  unfold leftmost in *.
  rewrite Forall_forall in *.
  intros q Hq.
  apply Hleft.
  apply Hsub.
  exact Hq.
Qed.

Lemma gs_sort_cons_subset : forall p a C L,
  sort p (a :: L) ->
  sort p C ->
  (forall q, In q C -> In q L) ->
  sort p (a :: C).
Proof.
  intros p a C L Hsort_new Hsort_C Hsub.
  destruct Hsort_new as [Hleft_new [HaL _]].
  destruct Hsort_C as [Hleft_C Hweak_C].
  split.
  - unfold leftmost in *.
    rewrite Forall_cons_iff in *.
    rewrite Forall_forall in *.
    destruct Hleft_new as [Ha Hleft_L].
    split.
    + exact Ha.
    + intros q Hq.
      apply Hleft_L.
      apply Hsub.
      exact Hq.
  - split.
    + rewrite Forall_g_rev_ccw_forall in *.
      intros q Hq.
      apply HaL.
      apply Hsub.
      exact Hq.
    + exact Hweak_C.
Qed.

Lemma gs_rev_consec_ccw_tail : forall b C,
  rev_consec_ccw (b :: C) ->
  rev_consec_ccw C.
Proof.
  intros b C Hcon.
  apply rev_consec_ccw_cons_iff in Hcon.
  tauto.
Qed.

Lemma gs_first_anchor_tail : forall p b C,
  first_anchor_strict p (rev (b :: C)) ->
  first_anchor_strict p (rev C).
Proof.
  intros p b C Hanchor.
  destruct C as [| c C].
  - simpl.
    exact I.
  - destruct C as [| d C'].
    + simpl.
      exact I.
    + simpl in Hanchor |- *.
      remember (rev C') as R.
      destruct R as [| x [| y R]]; simpl in *; exact Hanchor.
Qed.

Lemma gs_sort_tail_from_cons : forall p a b C,
  sort p (a :: b :: C) ->
  sort p (a :: C).
Proof.
  intros p a b C Hsort.
  destruct Hsort as [Hleft Hweak].
  split.
  - unfold leftmost in *.
    rewrite !Forall_cons_iff in *.
    tauto.
  - pose proof (g_rev_ccw_list_remove_middle p [a] [b] C Hweak) as Hweak'.
    simpl in Hweak'.
    exact Hweak'.
Qed.

Lemma gs_cleanup_closed_stack : forall p a C L,
  sort p (a :: C) ->
  rev_consec_ccw C ->
  first_anchor_strict p (rev C) ->
  is_max_hull' p (a :: C) (a :: L) ->
  (forall q, In q C -> In q L) ->
  exists C',
    graham_scan_inc a (C ++ [p]) = C' ++ [p] /\
    sort p C' /\
    rev_consec_ccw C' /\
    first_anchor_strict p (rev C') /\
    is_max_hull' p C' (a :: L) /\
    (forall q, In q C' -> In q (a :: L)).
Proof.
  intros p a C.
  induction C as [| b C IH]; intros L Hsort Hcon Hanchor Hmax Hsub.
  - simpl.
    exists [a].
    split; [reflexivity |].
    split; [exact Hsort |].
    split; [simpl; tauto |].
    split; [simpl; exact I |].
    split; [exact Hmax |].
    intros q [Hq | []].
    subst q; simpl; tauto.
  - destruct C as [| c C'].
    + simpl.
      destruct (ccw_dec p b a) as [Hccw | Hnccw].
      * exists [a; b].
        split; [reflexivity |].
        split; [exact Hsort |].
        split; [simpl; tauto |].
        split.
        -- simpl.
           exact Hccw.
        -- split; [exact Hmax |].
           intros q Hq.
           simpl in Hq |- *.
           destruct Hq as [Hq | [Hq | []]]; subst.
           ++ tauto.
           ++ right. apply Hsub. simpl. tauto.
      * exists [a].
        destruct Hsort as [Hleft Hweak].
        assert (Hsort_a : sort p [a]).
        {
          split.
          - unfold leftmost in *.
            rewrite Forall_cons_iff in *.
            destruct Hleft as [Ha _].
            split; [exact Ha | apply Forall_nil].
          - simpl.
            split; [apply Forall_nil | exact I].
        }
        split; [reflexivity |].
        split; [exact Hsort_a |].
        split; [simpl; tauto |].
        split; [simpl; exact I |].
        split.
        -- unfold is_max_hull' in *.
           rewrite Forall_forall in *.
           intros q Hq.
           destruct Hweak as [Hab _].
           rewrite Forall_g_rev_ccw_cons_iff in Hab.
           destruct Hab as [Hab _].
           eapply gs_point_in_hull_pop_single.
           ++ exact Hab.
           ++ exact Hnccw.
           ++ apply Hmax.
              exact Hq.
        -- intros q Hq.
           simpl in Hq |- *.
           destruct Hq as [Hq | []].
           subst q; tauto.
    + simpl.
      destruct (ccw_dec c b a) as [Hccw | Hnccw].
      * exists (a :: b :: c :: C').
        split; [reflexivity |].
        split; [exact Hsort |].
        split.
        -- simpl.
           split.
           ++ apply ccw_cyclicity.
              exact Hccw.
           ++ exact Hcon.
        -- split.
           ++ simpl in Hanchor |- *.
              remember (rev C') as R.
              destruct R as [| x [| y R]]; simpl in *; exact Hanchor.
           ++ split; [exact Hmax |].
              intros q Hq.
              simpl in Hq |- *.
              destruct Hq as [Hq | Hq]; subst.
              ** tauto.
              ** right. apply Hsub. simpl. exact Hq.
      * assert (Hsort_tail : sort p (a :: c :: C')).
        {
          apply gs_sort_tail_from_cons with (b := b).
          exact Hsort.
        }
        assert (Hcon_tail : rev_consec_ccw (c :: C')).
        {
          apply gs_rev_consec_ccw_tail with (b := b).
          exact Hcon.
        }
        assert (Hanchor_tail : first_anchor_strict p (rev (c :: C'))).
        {
          apply gs_first_anchor_tail with (b := b).
          exact Hanchor.
        }
        assert (Hmax_tail : is_max_hull' p (a :: c :: C') (a :: L)).
        {
          eapply is_max_hull'_pop'_g.
          - destruct Hsort as [_ Hweak].
            exact Hweak.
          - exact Hnccw.
          - exact Hmax.
        }
        assert (Hsub_tail : forall q, In q (c :: C') -> In q L).
        {
          intros q Hq.
          apply Hsub.
          simpl.
          right.
          exact Hq.
        }
        specialize (IH L Hsort_tail Hcon_tail Hanchor_tail Hmax_tail Hsub_tail)
          as [Cfinal [Hscan [Hsort_final [Hcon_final [Hanchor_final [Hmax_final Hsub_final]]]]]].
        exists Cfinal.
        split.
        -- simpl.
           destruct (ccw_dec c b a) as [Hbad | _].
           ++ contradiction.
           ++ exact Hscan.
        -- split; [exact Hsort_final |].
           split; [exact Hcon_final |].
           split; [exact Hanchor_final |].
           split; [exact Hmax_final |].
           exact Hsub_final.
Qed.

Lemma gs_closed_scan_fold_spec : forall p W,
  sort p W ->
  exists C,
    fold_left (fun T q => graham_scan_inc q T) (rev W) [p] = C ++ [p] /\
    sort p C /\
    rev_consec_ccw C /\
    first_anchor_strict p (rev C) /\
    is_max_hull' p C W /\
    (forall q, In q C -> In q W) /\
    (W <> [] -> C <> []).
Proof.
  intros p W.
  induction W as [| a W IH]; intros Hsort.
  - exists [].
    simpl.
    split; [reflexivity |].
    split.
    + split.
      * unfold leftmost.
        apply Forall_nil.
      * exact I.
    + split; [exact I |].
      split; [exact I |].
      split.
      * unfold is_max_hull'.
        apply Forall_nil.
      * split.
        -- intros q Hq.
           contradiction.
        -- intros Hbad.
           contradiction Hbad.
           reflexivity.
  - assert (Hsort_W : sort p W).
    {
      apply (sort_ind p [a] W).
      exact Hsort.
    }
    specialize (IH Hsort_W)
      as [C [Hfold [Hsort_C [Hcon_C [Hanchor_C [Hmax_C [Hsub_C Hnonempty_C]]]]]]].
    simpl rev.
    rewrite fold_left_app.
    simpl.
    rewrite Hfold.
    assert (Hsort_aC : sort p (a :: C)).
    {
      eapply gs_sort_cons_subset; eauto.
    }
    assert (Hpush : is_max_hull' p (a :: C) (a :: W)).
    {
      apply gs_is_max_hull'_push.
      - destruct Hsort_aC as [_ Hweak].
        exact Hweak.
      - intros HCnil.
        destruct W as [| w W']; [reflexivity |].
        exfalso.
        apply (Hnonempty_C ltac:(discriminate)).
        exact HCnil.
      - exact Hmax_C.
    }
	    destruct (gs_cleanup_closed_stack p a C W Hsort_aC Hcon_C Hanchor_C Hpush Hsub_C)
	      as [C' [Hscan [Hsort_C' [Hcon_C' [Hanchor_C' [Hmax_C' Hsub_C']]]]]].
	    exists C'.
	    split.
	    + rewrite Hscan.
	      reflexivity.
	    + split; [exact Hsort_C' |].
	      split; [exact Hcon_C' |].
	      split; [exact Hanchor_C' |].
	      split; [exact Hmax_C' |].
	      split; [exact Hsub_C' |].
	      intros _.
	      destruct C' as [| x C'']; [| discriminate].
	      unfold is_max_hull' in Hmax_C'.
	      rewrite Forall_cons_iff in Hmax_C'.
	      destruct Hmax_C' as [Ha _].
	      simpl in Ha.
	      contradiction.
Qed.

Theorem graham_scan_closed_convex_hull_final : forall p l,
  sort p (rev l) ->
  l <> [] ->
  is_convex_hull (p :: l) (graham_scan (rev (p :: l))).
Proof.
  intros p l Hsort Hne.
  pose proof (gs_closed_scan_fold_spec p (rev l) Hsort)
    as [C [Hfold [Hsort_C [Hcon_C [Hanchor_C [Hmax_C [Hsub_C Hnonempty_C]]]]]]].
  rewrite rev_involutive in Hfold.
  assert (Hstack : graham_scan (rev (p :: l)) = C ++ [p]).
  {
    rewrite <- fold_left_graham_scan_inc_cons.
    exact Hfold.
  }
  rewrite Hstack.
  split.
  - apply gs_rev_ccw_convex_rotate1.
    apply gs_rev_ccw_convex_anchor; assumption.
  - apply gs_is_max_hull'_edges_rotate1.
    apply gs_is_max_hull'_edges_cons_rev_tail.
    apply gs_is_max_hull'_edges_with_anchor; try assumption.
    + apply Hnonempty_C.
      intro Hrev_nil.
      apply Hne.
      apply (f_equal (@rev point)) in Hrev_nil.
      rewrite rev_involutive in Hrev_nil.
      exact Hrev_nil.
Qed.

Theorem build_hull_convex_hull_final : forall p l,
  sort p (rev l) ->
  l <> [] ->
  Hoare (fun T0 => T0 = [])
        (build_hull p l)
        (fun _ T => is_convex_hull (p :: l) T).
Proof.
  intros p l Hsort Hne.
  eapply Hoare_conseq_post.
  2: apply build_hull_hoare_final.
  intros [] T HT.
  rewrite HT.
  apply graham_scan_closed_convex_hull_final; assumption.
Qed.
