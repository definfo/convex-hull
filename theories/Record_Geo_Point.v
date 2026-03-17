(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec.
Local Open Scope Z.
Import ListNotations.
(* /COQ-HEAD *)

Record point: Type := {
  point_x: Z;
  point_y: Z;
}.

Module GeoNotations.

Notation "p '.(x)'" := (point_x p) (at level 1, only printing).
Notation "p '.(y)'" := (point_y p) (at level 1, only printing).
Notation "p '.(x)'" := (vec_x p) (at level 1, only printing).
Notation "p '.(y)'" := (vec_y p) (at level 1, only printing).

Ltac get_x p :=
  match type of p with
  | point => exact (point_x p)
  | vec => exact (vec_x p)
  end.

Ltac get_y p :=
  match type of p with
  | point => exact (point_y p)
  | vec => exact (vec_y p)
  end.

Notation "p '.(x)'" := (ltac:(get_x p)) (at level 1, only parsing).
Notation "p '.(y)'" := (ltac:(get_y p)) (at level 1, only parsing).

End GeoNotations.

Import GeoNotations.

Definition build_vec (p_from p_to: point): vec := {|
  vec_x := p_to.(x) - p_from.(x);
  vec_y := p_to.(y) - p_from.(y);
|}.

Lemma nonzero_sym: forall p q,
  nonzero (build_vec p q) ->
  nonzero (build_vec q p).
Proof. unfold nonzero, dot_prod, build_vec; simpl; nia. Qed.

Definition ccw (p q r: point): Prop :=
  left_than (build_vec p r) (build_vec p q).

Definition colinear (p q r: point): Prop :=
  parallel (build_vec p q) (build_vec p r).

Definition at_mid (p q r: point): Prop :=
  backward_or_perp (build_vec p q) (build_vec p r).

Lemma colinear_comm : forall p q r,
  colinear p q r <-> colinear p r q.
Proof.
  unfold colinear, parallel, cross_prod; simpl; nia.
Qed.

Lemma at_mid_comm : forall p q r,
  at_mid p q r <-> at_mid p r q.
Proof.
  unfold at_mid, backward_or_perp, dot_prod; simpl; nia.
Qed.

Ltac into_vec_prod :=
  unfold colinear, parallel in *;
  unfold at_mid, backward_or_perp in *;
  unfold ccw, left_than in *;
  unfold left_equal in *.

Definition g_ccw (p q r: point): Prop :=
  ccw p q r \/ (* ccw *)
  colinear p q r /\ at_mid q p r. (* or colinear p - q - r *)

Lemma ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ ccw p q r}.
Proof.
  unfold ccw, left_than; intros.
  remember (cross_prod (build_vec p r) (build_vec p q)) as a.
  pose proof Ztrichotomy_inf a 0as [[H | H] | H];
  try (left; nia);
  try (right; nia).
Qed.

Lemma ccw_g_ccw: forall (p q r: point),
  ccw p q r -> g_ccw p q r.
Proof. unfold ccw, g_ccw. tauto. Qed.

Lemma ccw_cyclicity: forall (p q r: point),
  ccw p q r -> ccw q r p.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_cyclicity_2: forall (p q r: point),
  ccw p q r -> ccw r p q.
Proof. intros. do 2 apply ccw_cyclicity. tauto. Qed.

Lemma ccw_anti_symmetry: forall (p q r: point),
  ccw p q r -> ~ ccw p r q.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_non_degeneracy: forall (p q r: point),
  ~ colinear p q r -> ccw p q r \/ ccw p r q.
Proof. unfold ccw, colinear, left_than, parallel, cross_prod, build_vec; simpl; intros. nia. Qed.

Ltac elim_ccw_rep H :=
  unfold ccw, left_than, cross_prod, build_vec in H;
  simpl in H; nia.

Lemma colinear_perm132: forall (p q r: point),
  colinear p q r -> colinear p r q.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm231: forall (p q r: point),
  colinear p q r -> colinear q r p.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm213: forall (p q r: point),
  colinear p q r -> colinear q p r.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm312: forall (p q r: point),
  colinear p q r -> colinear r p q.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_perm321: forall (p q r: point),
  colinear p q r -> colinear r q p.
Proof. unfold colinear, parallel, cross_prod, build_vec; simpl. nia. Qed.

Lemma colinear_4p: forall (p q r s: point),
  colinear p q r ->
  colinear p q s ->
  nonzero (build_vec p q) ->
  colinear q r s.
Proof.
  intros.
  apply colinear_perm213 in H.
  apply colinear_perm231 in H0.
  unfold colinear in *.
  apply nonzero_sym in H1.
  pose proof parallel_trans _ _ _ H0 H H1.
  apply parallel_sym.
  tauto.
Qed.

Lemma at_mid_fwd1: forall (p q r: point),
  at_mid q p r ->
  forward_or_perp (build_vec p q) (build_vec p r).
Proof.
  intros.
  pose proof metric_nonneg (build_vec p q).
  unfold at_mid, backward_or_perp, forward_or_perp, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma at_mid_fwd2: forall (p q r: point),
  at_mid q p r ->
  forward_or_perp (build_vec r q) (build_vec r p).
Proof.
  intros.
  pose proof metric_nonneg (build_vec r q).
  unfold at_mid, backward_or_perp, forward_or_perp, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma ccw_interiority: forall (p q r t: point),
  ccw t q r -> ccw p t r -> ccw p q t -> ccw p q r.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_transitivity: forall (p q r s t: point),
  ccw t s p -> ccw t s q -> ccw t s r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_dual_transitivity: forall (p q r s t: point),
  ccw s t p -> ccw s t q -> ccw s t r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof. unfold ccw, left_than, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_skip_head_simple: forall (p q r s t: point),
  ccw p q s \/ colinear p q s ->
  ccw p r s ->
  ccw p s t ->
  ccw q r s ->
  ccw r s t ->
  ccw q s t.
Proof. unfold ccw, colinear, left_than, parallel, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma at_mid_nonzero1: forall p q r,
  at_mid q p r ->
  nonzero (build_vec p q) ->
  nonzero (build_vec p r).
Proof.
  intros.
  rewrite nonzero_iff in H0 |- *.
  pose proof metric_nonneg (build_vec q r).
  unfold at_mid, backward_or_perp, nonzero, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma at_mid_nonzero2: forall p q r,
  at_mid q p r ->
  nonzero (build_vec q r) ->
  nonzero (build_vec p r).
Proof.
  intros.
  rewrite nonzero_iff in H0 |- *.
  pose proof metric_nonneg (build_vec p q).
  unfold at_mid, backward_or_perp, nonzero, dot_prod, build_vec in *.
  simpl in *.
  nia.
Qed.

Lemma ccw_ccw_colinear_shorter_impossible: forall p q r s,
  ccw p q r -> ccw p r s ->
  colinear p q s ->
  at_mid q p s ->
  False.
Proof.
  intros.
  apply at_mid_fwd1 in H2.
  unfold colinear in H1.
  rewrite forward_or_perp_iff in H2.
  destruct H2.
  + unfold ccw in *.
    pose proof left_than_same_dir_r _ _ _ H1 H2 H.
    clear - H0 H3.
    unfold left_than, cross_prod in *.
    lia.
  + pose proof left_than_nonzero2 _ _ H.
    pose proof left_than_nonzero1 _ _ H0.
    pose proof perp_parallel _ _ H2 H1 ltac:(tauto) ltac:(tauto).
    tauto.
Qed.

Lemma ccw_colinear_shorter_impossible: forall p q r s,
  ccw p q r ->
  colinear p r s ->
  at_mid r p s ->
  ccw q r s ->
  False.
Proof.
  intros p q r s ? Hp_par Hmid ?.
  pose proof colinear_perm312 _ _ _ Hp_par as Hs_par.
  unfold ccw in H.
  pose proof left_than_nonzero1 _ _ H as Hnz_pr.
  pose proof at_mid_nonzero1 _ _ _ Hmid Hnz_pr as Hnz_ps.
  assert (nonzero (build_vec s p)) as Hnz_sp
    by (revert Hnz_ps; unfold nonzero, dot_prod, build_vec; simpl; nia).
  pose proof at_mid_fwd1 _ _ _ Hmid as Hp.
  rewrite forward_or_perp_iff in Hp.
  destruct Hp as [Hp | Hp].
  2: {
    pose proof perp_parallel _ _ Hp Hp_par ltac:(tauto) ltac:(tauto).
    tauto.
  }
  pose proof at_mid_fwd2 _ _ _ Hmid as Hs.
  apply forward_or_perp_symm in Hs.
  pose proof left_than_same_dir_l _ _ _ Hp_par Hp H.
  fold (ccw p q s) in H1.
  apply ccw_cyclicity_2 in H1.
  unfold ccw in H1.
  pose proof left_equal_same_dir_r' _ _ _ Hs_par Hs H1.
  clear - H0 H2.
  apply ccw_cyclicity_2 in H0.
  unfold ccw in H0.
  unfold left_than, left_equal, cross_prod in *.
  lia.
Qed.

Lemma ccw_skip_head: forall (p q r s t: point),
  g_ccw p q r -> g_ccw p q s -> g_ccw p q t ->
  g_ccw p r s -> g_ccw p r t -> g_ccw p s t ->
  ccw q r s -> ccw r s t -> ccw q s t.
Proof.
  unfold ccw, g_ccw.
  intros p q r s t Hqr Hqs Hqt Hrs Hrt Hst Hqrs Hrst.
  destruct Hrs as [Hrs | [Hrs0 Hrs]].
  + destruct Hst as [Hst | [Hst0 Hst]].
    - apply (ccw_skip_head_simple p q r s t); unfold ccw, colinear; tauto.
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hrs Hst0 Hst Hrst.
      tauto.
  + destruct Hqr as [Hqr | [Hqr0 Hqr]].
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hqr Hrs0 Hrs Hqrs.
      tauto.
    - pose proof left_than_nonzero2 _ _ Hqrs.
      pose proof at_mid_nonzero2 _ _ _ Hqr H.
      pose proof colinear_perm132 _ _ _ Hqr0.
      pose proof colinear_4p _ _ _ _ H1 Hrs0 H0.
      clear - H2 Hqrs.
      apply colinear_perm231 in H2.
      unfold colinear, left_than, parallel, cross_prod in *.
      lia.
Qed.

(* p q r
   p q s
   p q t
   p r t *)
Lemma ccw_skip_tail_simple: forall (p q r s t: point),
  ccw p q r \/ colinear p q r ->
  ccw p r s -> ccw p r t -> ccw p s t ->
  ccw q r s -> ccw r s t -> ccw q r t.
Proof. unfold ccw, colinear, left_than, parallel, cross_prod, build_vec; simpl; intros. nia. Qed.

Lemma ccw_skip_tail: forall (p q r s t: point),
  g_ccw p q r -> g_ccw p q s -> g_ccw p q t ->
  g_ccw p r s -> g_ccw p r t -> g_ccw p s t ->
  ccw q r s -> ccw r s t -> ccw q r t.
Proof.
  unfold ccw, g_ccw.
  intros p q r s t Hqr Hqs Hqt Hrs Hrt Hst Hqrs Hrst.
  destruct Hrs as [Hrs | [Hrs0 Hrs]].
  + destruct Hst as [Hst | [Hst0 Hst]].
    - destruct Hrt as [Hrt | [Hrt0 Hrt]].
      * apply (ccw_skip_tail_simple p q r s t); try tauto.
      * pose proof ccw_ccw_colinear_shorter_impossible p r s t.
        tauto.
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hrs Hst0 Hst Hrst.
      tauto.
  + destruct Hqr as [Hqr | [Hqr0 Hqr]].
    - pose proof ccw_colinear_shorter_impossible _ _ _ _
                 Hqr Hrs0 Hrs Hqrs.
      tauto.
    - pose proof left_than_nonzero2 _ _ Hqrs.
      pose proof at_mid_nonzero2 _ _ _ Hqr H.
      pose proof colinear_perm132 _ _ _ Hqr0.
      pose proof colinear_4p _ _ _ _ H1 Hrs0 H0.
      clear - H2 Hqrs.
      apply colinear_perm231 in H2.
      unfold colinear, left_than, parallel, cross_prod in *.
      lia.
Qed.

Lemma ccw_trichotomy : forall (p q r : point),
  {ccw p q r} + {colinear p q r} + {ccw p r q}.
Proof.
  intros.
  destruct (ccw_dec p q r) as [H0 | H0].
  - left. left. assumption.
  - assert ({colinear p q r} + {~ colinear p q r}) as [Hcol | Hncol].
    { unfold colinear, parallel.
      remember (cross_prod (build_vec p q) (build_vec p r)) as a.
      pose proof Z_dec a 0 as [[Hlt | Heq] | Hgt];
      try (left; assumption);
      try (right; intros H'; nia). }
    + left. right. assumption.
    + right. pose proof (ccw_non_degeneracy p q r Hncol).
      destruct H; try contradiction; try assumption.
Qed.

(** Properties *)
(* all point in P are right to p->q *)
Definition Forall_ccw (p q: point) (P: list point): Prop :=
  Forall (ccw p q) P.

Lemma Forall_ccw_g_ccw: forall p q l,
  Forall_ccw p q l ->
  Forall (g_ccw p q) l.
Proof.
  intros p q l.
  apply Forall_impl.
  intros a.
  apply ccw_g_ccw.
Qed.

Lemma Forall_ccw_cons_iff:
  forall p q a l,
    Forall_ccw p q (a :: l) <->
    ccw p q a /\ Forall_ccw p q l.
Proof. intros. apply Forall_cons_iff. Qed.

Lemma Forall_ccw_nil_iff:
  forall p q,
    Forall_ccw p q nil <-> True.
Proof. intros. apply Forall_nil_iff. Qed.

Lemma Forall_ccw_app:
  forall p q l1 l2,
    Forall_ccw p q (l1 ++ l2) <->
    Forall_ccw p q l1 /\ Forall_ccw p q l2.
Proof. intros. apply Forall_app. Qed.

Lemma Forall_ccw_forall:
  forall p q l,
    Forall_ccw p q l <-> forall r, In r l -> ccw p q r.
Proof. intros. apply Forall_forall. Qed.

Lemma Forall_ccw_ind : forall (p q r : point) (P P' : list point),
  Forall_ccw p q (P ++ r :: P') -> Forall_ccw p q (P ++ P').
Proof.
  intros p q ? ? ?.
  rewrite !Forall_ccw_app.
  rewrite Forall_ccw_cons_iff.
  tauto.
Qed.

Lemma Forall_ccw_ind' : forall (p q : point) (T0 T : list point),
  Forall_ccw p q (T0 ++ T) -> Forall_ccw p q T.
Proof.
  intros p q ? ? .
  rewrite !Forall_ccw_app.
  tauto.
Qed.

Fixpoint ccw_list (p: point) (l: list point): Prop :=
  match l with
  | cons q l0 => Forall_ccw p q l0 /\ ccw_list p l0
  | nil => True
  end.

Fixpoint g_ccw_list (p: point) (l: list point): Prop :=
  match l with
  | cons q l0 => Forall (g_ccw p q) l0 /\ g_ccw_list p l0
  | nil => True
  end.

Lemma g_ccw_ccw_list: forall p l,
  ccw_list p l ->
  g_ccw_list p l.
Proof.
  intros.
  induction l; simpl in *.
  + tauto.
  + destruct H.
    pose proof Forall_ccw_g_ccw p a l.
    tauto.
Qed.

Lemma ccw_list_app_iff: forall p l1 l2,
  ccw_list p (l1 ++ l2) <->
    ccw_list p l1 /\
    ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> ccw p q r).
Proof.
  intros.
  split; induction l1; simpl.
  + tauto.
  + intros.
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_ccw_app in H.
    destruct IHl1 as [? [? ?]], H as [[? ?] ?].
    repeat split; try tauto.
    intros.
    destruct H5; [| apply H2; tauto].
    subst q.
    rewrite Forall_ccw_forall in H3.
    apply H3; tauto.
  + tauto.
  + intros [[? ?] [? ?]].
    assert (forall q r, In q l1 -> In r l2 -> ccw p q r)
      by (intros; apply H2; tauto).
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_ccw_app.
    repeat split; try tauto.
    rewrite Forall_ccw_forall.
    intros; apply H2; tauto.
Qed.

Lemma g_ccw_list_app_iff: forall p l1 l2,
  g_ccw_list p (l1 ++ l2) <->
    g_ccw_list p l1 /\
    g_ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> g_ccw p q r).
Proof.
  intros.
  split; induction l1; simpl.
  + tauto.
  + intros.
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_app in H.
    destruct IHl1 as [? [? ?]], H as [[? ?] ?].
    repeat split; try tauto.
    intros.
    destruct H5; [| apply H2; tauto].
    subst q.
    rewrite Forall_forall in H3.
    apply H3; tauto.
  + tauto.
  + intros [[? ?] [? ?]].
    assert (forall q r, In q l1 -> In r l2 -> g_ccw p q r)
      by (intros; apply H2; tauto).
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_app.
    repeat split; try tauto.
    rewrite Forall_forall.
    intros; apply H2; tauto.
Qed.

Lemma g_ccw_list_snoc_iff: forall p l q,
  g_ccw_list p (l ++ q :: nil) <->
  g_ccw_list p l /\ Forall (fun r => g_ccw p r q) l.
Proof.
  intros.
  induction l.
  + simpl.
    rewrite !Forall_nil_iff.
    tauto.
  + simpl.
    rewrite Forall_cons_iff.
    rewrite Forall_app, Forall_cons_iff, Forall_nil_iff.
    tauto.
Qed.

Lemma g_ccw_list_remove_middle: forall p l1 l2 l3,
  g_ccw_list p (l1 ++ l2 ++ l3) ->
  g_ccw_list p (l1 ++ l3).
Proof.
  intros.
  rewrite g_ccw_list_app_iff.
  rewrite !g_ccw_list_app_iff in H.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  split; [| split]; try tauto.
  intros.
  apply H1; try tauto.
  rewrite in_app_iff.
  tauto.
Qed.

Fixpoint ccw_convex (l: list point): Prop :=
  match l with
  | cons p l0 => ccw_list p l0 /\ ccw_convex l0
  | nil => True
  end.

Lemma ccw_convex_rotate1: forall p l,
  ccw_convex (p :: l) ->
  ccw_convex (l ++ p :: nil).
Proof.
  intros.
  simpl in H.
  destruct H.
  induction l; simpl in *.
  + tauto.
  + split; [| tauto].
    apply ccw_list_app_iff.
    simpl.
    rewrite Forall_ccw_nil_iff.
    repeat split; try tauto.
    intros ? ? ? [? |[]].
    subst r.
    destruct H.
    rewrite Forall_ccw_forall in H.
    apply ccw_cyclicity.
    apply H; tauto.
Qed.

Lemma ccw_convex_app_comm: forall l1 l2,
  ccw_convex (l1 ++ l2) ->
  ccw_convex (l2 ++ l1).
Proof.
  intros.
  revert l2 H; induction l1; simpl app; intros.
  + rewrite app_nil_r.
    tauto.
  + specialize (IHl1 (l2 ++ a :: nil)).
    rewrite <- app_assoc in IHl1.
    simpl app in IHl1.
    apply IHl1.
    rewrite app_assoc.
    apply ccw_convex_rotate1.
    tauto.
Qed.

Lemma ccw_list_forall2: forall p l,
  (forall l1 q l2 r l3, l = l1 ++ q :: l2 ++ r :: l3 -> ccw p q r) ->
  ccw_list p l.
Proof.
  intros.
  induction l; [simpl; tauto |].
  simpl.
  split.
  - clear IHl.
    rewrite Forall_ccw_forall.
    intros r ?.
    apply in_split in H0.
    destruct H0 as [l1 [l2 ?]].
    specialize (H nil a l1 r l2).
    rewrite H0 in H.
    apply H; reflexivity.
  - apply IHl.
    intros.
    specialize (H (a :: l1) q l2 r l3).
    apply H; rewrite H0; reflexivity.
Qed.

Lemma ccw_convex_forall3: forall l,
  (forall l1 p l2 q l3 r l4,
     l = l1 ++ p :: l2 ++ q :: l3 ++ r :: l4 -> ccw p q r) ->
  ccw_convex l.
Proof.
  intros.
  induction l; [simpl; tauto |].
  simpl.
  split.
  + clear IHl.
    apply ccw_list_forall2.
    intros.
    specialize (H nil a l1 q l2 r l3).
    apply H; rewrite H0; reflexivity.
  + apply IHl.
    intros.
    specialize (H (a :: l1) p l2 q l3 r l4).
    apply H; rewrite H0; reflexivity.
Qed.

Fixpoint consec_ccw (l: list point): Prop :=
  match l with
  | p :: _l =>
    match _l with
    | q :: r :: _ => ccw p q r
    | _ => True
    end /\ consec_ccw _l
  | _ => True
  end.

Lemma consec_ccw_cons_iff: forall a l,
  consec_ccw (a :: l) <->
  consec_ccw l /\ (forall b c l0, l = b :: c :: l0 -> ccw a b c).
Proof.
  intros.
  split; intros.
  + destruct H.
    split; [tauto |].
    intros.
    subst l.
    tauto.
  + destruct H.
    split; [| tauto].
    destruct l as [| ? [|]]; try tauto.
    specialize (H0 _ _ _ ltac:(reflexivity)).
    tauto.
Qed.

Lemma consec_ccw_cons3_iff: forall a b c l,
  consec_ccw (a :: b :: c :: l) <->
  consec_ccw (b :: c :: l) /\ ccw a b c.
Proof.
  intros.
  rewrite (consec_ccw_cons_iff a).
  assert ((forall b0 c0 l0, b :: c :: l = b0 :: c0 :: l0 -> ccw a b0 c0)
          <-> ccw a b c); [| tauto].
  split; intros.
  + eapply H; reflexivity.
  + injection H0 as ? ? _.
    subst.
    tauto.
Qed.

Lemma consec_ccw_spec: forall l,
  consec_ccw l <->
  (forall l1 p q r l2, l = l1 ++ p :: q :: r :: l2 -> ccw p q r).
Proof.
  intros.
  induction l.
  + simpl.
    split; [intros _ ? ? ? ? ? ? | tauto].
    destruct l1; discriminate H.
  + rewrite consec_ccw_cons_iff.
    rewrite IHl; clear IHl.
    split; [intros [? ?]; intros | intros; split].
    - destruct l1.
      * injection H1 as ? ?.
        subst.
        eapply H0.
        reflexivity.
      * injection H1 as ? ?.
        subst.
        eapply (H l1).
        reflexivity.
    - intros.
      eapply (H (a :: l1)).
      rewrite H0.
      reflexivity.
    - intros.
      eapply (H nil).
      rewrite H0.
      simpl.
      reflexivity.
Qed.

Lemma consec_ccw_snoc_iff: forall a l,
  consec_ccw (l ++ a :: nil) <->
  consec_ccw l /\ (forall b c l0, l = l0 ++ c :: b :: nil -> ccw c b a).
Proof.
  intros.
  destruct l as [| ? [|]].
  + simpl.
    assert (forall b c l0, [] = l0 ++ [c; b] -> ccw c b a); [| tauto].
    intros.
    destruct l0; discriminate H.
  + simpl.
    assert (forall b c l0, [p] = l0 ++ [c; b] -> ccw c b a); [| tauto].
    intros.
    destruct l0 as [| ? [|]]; discriminate H.
  + simpl app.
    revert p p0; induction l; intros.
    - simpl.
      assert (ccw p p0 a <->
              forall b c l0, [p; p0] = l0 ++ [c; b] -> ccw c b a); [| tauto].
      split.
      * intros.
        destruct l0 as [| ? [| ? [|]]]; [| discriminate H0 ..].
        injection H0 as ? ?.
        subst; tauto.
      * intros.
        apply (H _ _ nil).
        reflexivity.
    - simpl app.
      do 2 rewrite (consec_ccw_cons_iff p).
      rewrite IHl.
      clear IHl.
      split; intros [[? ?] ?]; (split; [split |]); try tauto.
      * intros.
        injection H2 as ? ? ?; subst.
        apply (H1 _ _ (l0 ++ [a])).
        reflexivity.
      * intros.
        destruct l0; [discriminate H2 | simpl in H2].
        injection H2 as ? ?.
        subst.
        apply (H0 _ _ l0); tauto.
      * intros.
        apply (H1 _ _ (p :: l0)).
        rewrite H2; reflexivity.
      * intros.
        injection H2 as ? ? ?; subst.
        eapply H0.
        reflexivity.
Qed.

Lemma consec_ccw_snoc3_iff: forall a b c l,
  consec_ccw (l ++ c :: b :: a :: nil) <->
  consec_ccw (l ++ c :: b :: nil) /\ ccw c b a.
Proof.
  intros.
  change (c :: b :: a :: nil) with ((c :: b :: nil) ++ (a :: nil)).
  rewrite app_assoc.
  rewrite consec_ccw_snoc_iff.
  assert ((forall b0 c0 l0, l ++ [c; b] = l0 ++ [c0; b0] -> ccw c0 b0 a) <->
          ccw c b a); [| tauto].
  split; intros.
  + eapply H; reflexivity.
  + change (c :: b :: nil) with ((c :: nil) ++ (b :: nil)) in H0.
    change (c0 :: b0 :: nil) with ((c0 :: nil) ++ (b0 :: nil)) in H0.
    rewrite !app_assoc in H0.
    rewrite !app_inj_tail_iff in H0.
    destruct H0 as [[? ?] ?]; subst.
    tauto.
Qed.

Lemma consec_ccw_app_inv1: forall l1 l2,
  consec_ccw (l1 ++ l2) ->
  consec_ccw l1.
Proof.
  intros.
  induction l1.
  + simpl; tauto.
  + destruct H.
    split; [| apply IHl1; tauto].
    clear H0 IHl1.
    destruct l1 as [| ? [|]]; simpl in *; tauto.
Qed.

Lemma consec_ccw_app_inv2: forall l1 l2,
  consec_ccw (l1 ++ l2) ->
  consec_ccw l2.
Proof.
  intros.
  induction l1.
  + exact H.
  + apply IHl1.
    destruct H; tauto.
Qed.

Lemma consec_ccw_head_elim1: forall s p0 p1 l,
  g_ccw_list s (p0 :: p1 :: l) ->
  consec_ccw (p0 :: p1 :: l) ->
  consec_ccw (p0 :: l).
Proof.
  intros.
  destruct l as [| p2 [| p3 ?]]; try (simpl; tauto).
  rewrite !consec_ccw_cons3_iff in *.
  split; [tauto |].
  simpl in H.
  destruct H as [? [? [? ?]]], H0 as [[? ?] ?].
  rewrite !Forall_cons_iff in H.
  rewrite !Forall_cons_iff in H1.
  rewrite !Forall_cons_iff in H2.
  apply (ccw_skip_head s p0 p1 p2 p3); try tauto.
Qed.

Lemma consec_ccw_head_elim: forall s p l1 l2,
  g_ccw_list s (p :: l1 ++ l2) ->
  consec_ccw (p :: l1 ++ l2) ->
  consec_ccw (p :: l2).
Proof.
  intros.
  induction l1 as [| p0 l1 IHl1].
  + simpl app in H0.
    tauto.
  + simpl in H.
    apply IHl1.
    - rewrite Forall_cons_iff in H.
      simpl. tauto.
    - simpl app in H0.
      revert H0; apply (consec_ccw_head_elim1 s).
      simpl.
      tauto.
Qed.

Lemma destruct_tail: forall {A: Type} (l: list A),
  {l = nil} + {exists a l', l = l' ++ a :: nil}.
Proof.
  induction l.
  + left.
    reflexivity.
  + right.
    destruct IHl.
    - exists a, nil.
      subst; reflexivity.
    - destruct e as [a0 [l' ?]].
      exists a0, (a :: l').
      subst.
      reflexivity.
Qed.

Lemma consec_ccw_tail_elim: forall s p l1 l2,
  g_ccw_list s ((l1 ++ l2) ++ p :: nil) ->
  consec_ccw ((l1 ++ l2) ++ p :: nil) ->
  consec_ccw (l1 ++ p :: nil).
Proof.
  intros s p l1.
  refine (rev_ind _ _ _).
  + intros.
    rewrite <- app_assoc in H0.
    simpl app in H0.
    tauto.
  + intros p0 ? IHl2 ? ?.
    rewrite app_assoc in H, H0.
    rewrite !g_ccw_list_snoc_iff in H.
    destruct H as [[? ?] ?].
    rewrite Forall_app, Forall_cons_iff in H2.
    destruct H2 as [? [? _]].
    apply IHl2.
    1: { rewrite g_ccw_list_snoc_iff. tauto. }
    clear IHl2.
    destruct (destruct_tail (l1 ++ l)) as [| [p1 [? ?l]]];
      try (rewrite e in *; simpl; tauto).
    rewrite l0 in *; clear l1 l l0.
    destruct (destruct_tail x) as [| [p2 [? ?l]]];
      try (rewrite e in *; simpl; tauto).
    subst x.
    rewrite <- !app_assoc; simpl.
    rewrite consec_ccw_snoc3_iff.
    do 2 rewrite <- app_assoc in H0; simpl  in H0.
    rewrite consec_ccw_snoc3_iff in H0.
    rewrite <- app_assoc in H0; simpl  in H0.
    rewrite consec_ccw_snoc3_iff in H0.
    split; [tauto |].
    rewrite !g_ccw_list_snoc_iff in H.
    rewrite !Forall_app, !Forall_cons_iff, !Forall_nil_iff in H1.
    rewrite !Forall_app, !Forall_cons_iff, !Forall_nil_iff in H2.
    rewrite !Forall_app, !Forall_cons_iff, !Forall_nil_iff in H.
    apply (ccw_skip_tail s p2 p1 p0 p);
    try tauto;
    try (apply ccw_cyclicity; tauto).
Qed.

Fixpoint ccw_list_consec (p: point) (l: list point): Prop :=
  match l with
  | nil => True
  | p0 :: l0 =>
    match l0 with
    | nil => True
    | p1 :: l1 => ccw p p0 p1
    end /\ ccw_list_consec p l0
  end.

Lemma ccw_list_consec_Forall_g_ccw_ccw: forall p q l,
  Forall (g_ccw p q) l ->
  ccw_list_consec p (q :: l) ->
  Forall_ccw p q l.
Proof.
  intros.
  induction l as [| r l IHl]; intros.
  + rewrite Forall_ccw_nil_iff.
    tauto.
  + rewrite Forall_ccw_cons_iff.
    change (ccw p q r /\ ccw_list_consec p (r :: l)) in H0.
    rewrite Forall_cons_iff in H.
    destruct H, H0.
    split; [tauto |].
    apply IHl; try tauto.
    destruct l as [| s l].
    1: { simpl; tauto. }
    change (ccw p r s /\ ccw_list_consec p (s :: l)) in H2.
    change (ccw p q s /\ ccw_list_consec p (s :: l)).
    destruct H2.
    split; [| tauto].
    rewrite Forall_cons_iff in H1.
    destruct H1.
    destruct H1 as [? | [? ?]]; [tauto |].
    pose proof ccw_ccw_colinear_shorter_impossible p q r s.
    tauto.
Qed.

Theorem ccw_convex_spec_origin: forall p l,
  g_ccw_list p l ->
  consec_ccw (p :: l) ->
  ccw_list p l.
Proof.
  intros.
  assert (ccw_list_consec p l).
  + destruct l as [| p0 [| p1 l]].
    1: { simpl; tauto. }
    1: { simpl; tauto. }
    rewrite consec_ccw_cons3_iff in H0.
    destruct H0.
    destruct H as [_ ?].
    change (ccw p p0 p1 /\ ccw_list_consec p (p1 :: l)).
    split; [tauto |].
    revert p0 p1 H H0 H1; induction l as [| p2 l IHl]; intros.
    1: { simpl; tauto. }
    rewrite consec_ccw_cons3_iff in H0.
    destruct H, H0.
    change (ccw p p1 p2 /\ ccw_list_consec p (p2 :: l)).
    assert (ccw p p1 p2).
    - rewrite Forall_cons_iff in H.
      destruct H as [? _].
      unfold g_ccw in H.
      destruct H; [tauto |].
      pose proof ccw_colinear_shorter_impossible p p0 p1 p2.
      tauto.
    - split; [tauto |].
      apply (IHl p1 p2); try tauto.
  + clear H0.
    induction l as [| p0 l IHl]; [simpl; tauto |].
    simpl in H |- *.
    destruct H.
    split.
    - clear - H H1.
      apply ccw_list_consec_Forall_g_ccw_ccw; tauto.
    - destruct H1.
      apply IHl; tauto.
Qed.

Theorem ccw_convex_spec_others: forall p l,
  g_ccw_list p l ->
  consec_ccw l ->
  ccw_convex l.
Proof.
  intros.
  apply ccw_convex_forall3.
  intros l1 q l2 r l3 s l4 ?.
  subst l.
  rewrite g_ccw_list_app_iff in H.
  destruct H as [_ [? _]].
  apply consec_ccw_app_inv2 in H0.
  clear l1.
  change (s :: l4) with (s :: nil ++ l4) in H, H0.
  rewrite !app_comm_cons in H, H0.
  change (r :: l3) with (r :: nil ++ l3) in H, H0.
  rewrite !app_comm_cons in H, H0.
  rewrite !app_assoc in H, H0.
  rewrite g_ccw_list_app_iff in H.
  destruct H as [? [_ _]].
  apply consec_ccw_app_inv1 in H0.
  pose proof consec_ccw_tail_elim _ _ _ _ H H0.
  clear H0.
  rewrite <- app_assoc in H.
  apply g_ccw_list_remove_middle in H.
  rewrite <- app_assoc in H, H1.
  simpl app in H, H1.
  revert H H1; apply consec_ccw_head_elim.
Qed.

Theorem ccw_convex_spec_simple: forall p l,
  ccw_list p l ->
  consec_ccw l ->
  ccw_convex (p :: l).
Proof.
  intros.
  simpl.
  split; [tauto |].
  apply g_ccw_ccw_list in H.
  revert H H0; apply ccw_convex_spec_others.
Qed.

Theorem ccw_convex_spec: forall p l,
  g_ccw_list p l ->
  consec_ccw (p :: l) ->
  ccw_convex (p :: l).
Proof.
  intros.
  simpl.
  split.
  + apply ccw_convex_spec_origin; tauto.
  + apply (ccw_convex_spec_others p).
    - tauto.
    - rewrite consec_ccw_cons_iff in H0.
      tauto.
Qed.

Theorem g_ccw_rep : forall p q ,
  g_ccw p p q /\ g_ccw q p p.
Proof.
  intros; repeat split.
  - unfold g_ccw; right.
    split.
    + unfold colinear, parallel, build_vec, cross_prod. simpl.
      lia.
    + unfold at_mid, backward_or_perp, build_vec, dot_prod. simpl.
      nia.
  - unfold g_ccw; right.
    split.
    + unfold colinear, parallel, build_vec, cross_prod. simpl.
      lia.
    + unfold at_mid, backward_or_perp, build_vec, dot_prod. simpl.
      nia.
Qed.

Lemma forall_inr_true : forall (A: Type) (P: Prop) (l: list A),
  Forall (fun q => P \/ True) l.
Proof.
  intros.
  induction l as [ | x l' IHl'].
  - apply Forall_nil.
  - apply Forall_cons.
    + tauto.
    + apply IHl'.
Qed.

(** ccw_list with reverse order *)
Fixpoint rev_ccw_list (p: point) (l: list point): Prop :=
  match l with
  | cons q l0 => Forall_ccw q p l0 /\ rev_ccw_list p l0
  | nil => True
  end.

Lemma rev_ccw_list_app_iff: forall p l1 l2,
  rev_ccw_list p (l1 ++ l2) <->
    rev_ccw_list p l1 /\
    rev_ccw_list p l2 /\
    (forall q r, In q l1 -> In r l2 -> ccw q p r).
Proof.
  intros.
  split; induction l1; simpl.
  + tauto.
  + intros.
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_ccw_app in H.
    destruct IHl1 as [? [? ?]], H as [[? ?] ?].
    repeat split; try tauto.
    intros.
    destruct H5; [| apply H2; tauto].
    subst q.
    rewrite Forall_ccw_forall in H3.
    apply H3; tauto.
  + tauto.
  + intros [[? ?] [? ?]].
    assert (forall q r, In q l1 -> In r l2 -> ccw q p r)
      by (intros; apply H2; tauto).
    specialize (IHl1 ltac:(tauto)).
    rewrite Forall_ccw_app.
    repeat split; try tauto.
    rewrite Forall_ccw_forall.
    intros; apply H2; tauto.
Qed.

Lemma rev_ccw_list_remove_middle: forall p l1 l2 l3,
  rev_ccw_list p (l1 ++ l2 ++ l3) ->
  rev_ccw_list p (l1 ++ l3).
Proof.
  intros.
  rewrite rev_ccw_list_app_iff.
  rewrite !rev_ccw_list_app_iff in H.
  destruct H as [? [? ?]].
  destruct H0 as [? [? ?]].
  split; [| split]; try tauto.
  intros.
  apply H1; try tauto.
  rewrite in_app_iff.
  tauto.
Qed.

Fixpoint rev_consec_ccw (l: list point) : Prop :=
  match l with
  | p :: _l =>
    match _l with
    | q :: r :: _ => ccw q p r
    | _ => True
    end /\ rev_consec_ccw _l
  | _ => True
  end.

Lemma rev_consec_ccw_cons_iff: forall a l,
  rev_consec_ccw (a :: l) <->
  rev_consec_ccw l /\ (forall b c l0, l = b :: c :: l0 -> ccw b a c).
Proof.
  intros.
  split; intros.
  + destruct H.
    split; [tauto |].
    intros.
    subst l.
    tauto.
  + destruct H.
    split; [| tauto].
    destruct l as [| ? [|]]; try tauto.
    specialize (H0 _ _ _ ltac:(reflexivity)).
    tauto.
Qed.

Lemma rev_consec_ccw_snoc_iff: forall a l,
  rev_consec_ccw (l ++ a :: nil) <->
  rev_consec_ccw l /\ (forall b c l0, l = l0 ++ c :: b :: nil -> ccw a b c).
Proof.
  intros.
  destruct l as [| ? [|]].
  + simpl.
    assert (forall b c l0, [] = l0 ++ [c; b] -> ccw a b c); [| tauto].
    intros.
    destruct l0; discriminate H.
  + simpl.
    assert (forall b c l0, [p] = l0 ++ [c; b] -> ccw a b c); [| tauto].
    intros.
    destruct l0 as [| ? [|]]; discriminate H.
  + simpl app.
    revert p p0; induction l; intros.
    - simpl.
      assert (ccw p0 p a <->
              forall b c l0, [p; p0] = l0 ++ [c; b] -> ccw b c a);
      split.
      * intros.
        destruct l0 as [| ? [| ? [|]]]; [| discriminate H0 ..].
        injection H0 as ? ?.
        subst; tauto.
      * intros.
        apply (H _ _ nil).
        reflexivity.
      * intros _H; destruct _H as [_H _].
        split; [tauto|].
        intros.
        destruct l0 as [| ? [| ? [|]]]; [| discriminate H0 ..].
        injection H0 as ? ?.
        subst; apply ccw_cyclicity_2; tauto.
      * intros _H; destruct _H as [_ _H].
        split; [|tauto].
        destruct H as [_ ?].
        apply H.
        intros; specialize (_H _ _ _ H0).
        apply ccw_cyclicity; tauto.
    - simpl app.
      do 2 rewrite (rev_consec_ccw_cons_iff p).
      rewrite IHl.
      clear IHl.
      split; intros [[? ?] ?]; (split; [split |]); try tauto.
      * intros.
        injection H2 as ? ? ?; subst.
        apply (H1 _ _ (l0 ++ [a])).
        reflexivity.
      * intros.
        destruct l0; [discriminate H2 | simpl in H2].
        injection H2 as ? ?.
        subst.
        apply (H0 _ _ l0); tauto.
      * intros.
        apply (H1 _ _ (p :: l0)).
        rewrite H2; reflexivity.
      * intros.
        injection H2 as ? ? ?; subst.
        eapply H0.
        reflexivity.
Qed.

Lemma rev_consec_ccw_snoc3_iff: forall a b c l,
  rev_consec_ccw (l ++ c :: b :: a :: nil) <->
  rev_consec_ccw (l ++ c :: b :: nil) /\ ccw a b c.
Proof.
  intros.
  change (c :: b :: a :: nil) with ((c :: b :: nil) ++ (a :: nil)).
  rewrite app_assoc.
  rewrite rev_consec_ccw_snoc_iff.
  assert ((forall b0 c0 l0, l ++ [c; b] = l0 ++ [c0; b0] -> ccw a b0 c0) <->
          ccw a b c); [| split; tauto].
  split; intros.
  + eapply H; reflexivity.
  + change (c :: b :: nil) with ((c :: nil) ++ (b :: nil)) in H0.
    change (c0 :: b0 :: nil) with ((c0 :: nil) ++ (b0 :: nil)) in H0.
    rewrite !app_assoc in H0.
    rewrite !app_inj_tail_iff in H0.
    destruct H0 as [[? ?] ?]; subst.
    tauto.
Qed.

(* ========================== *)
(*      Sort Definition       *)
(* ========================== *)

Definition leftmost (p: point) (P: list point) : Prop :=
  Forall (fun (q: point) => p.(x) < q.(x) \/ (p.(x) = q.(x) /\ p.(y) < q.(y))) P.

(* split the first point p with P *)
Definition sort (p: point) (P: list point) : Prop :=
  leftmost p P /\ rev_ccw_list p P.

(* Gift-wrapping / Jarvis' march *)
(* 每步查找最外侧点
   leftmost point, -y orientation =>
   append the point with minimum polar angle =>
   exit until the initial point *)
(*
Jarvis(x[1..n], y[1..n]):
  // find leftmost point
  l = 1
  for i from 2 to n:
    if x[i] < x[l]:
      l = i
  p = l
  // search next point
  // p := endpoint in convex hull
  // q := next point (different from p, cross_prodermined by ccw)
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


(* split first point p with tail T *)
Fixpoint is_convex (p : point) (T : list point) : Prop :=
  match T with
  (* p3 := last point in stack *)
  | p3 :: T' =>
    match T' with
    | p2 :: p1 :: _ => ccw p1 p2 p3 /\ ccw p2 p3 p /\ is_convex p T'
    | _ => True
    end
  | _ => True
  end.

Lemma convex_ind : forall (p q : point) (T : list point),
  is_convex p (q :: T) -> is_convex p T.
Proof.
  destruct T; intros; try eauto.
  destruct T; intros; try eauto.
  destruct H as [_ [_ H]]. assumption.
Qed.

(** Lemma for assistance **)
Lemma rev_ccw_list_ind : forall (p q : point) (P P' : list point),
  rev_ccw_list p (P ++ q :: P') -> rev_ccw_list p (P ++ P').
Proof.
  induction P; simpl; intros.
  - destruct H. assumption.
  - destruct H as [Hr H];
    pose proof Forall_ccw_ind as IHr.
    specialize (IHr a p q P P' Hr).
    specialize (IHP P' H).
    tauto.
Qed.

Lemma rev_ccw_list_ind' : forall (p : point) (T0 T : list point),
  rev_ccw_list p (T0 ++ T) -> rev_ccw_list p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T). destruct H. apply (IHT0 H0).
Qed.

Lemma leftmost_ind : forall p T0 T,
  leftmost p (T0 ++ T) -> leftmost p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T).
  simpl in H. unfold leftmost in *.
  pose proof Forall_app (fun (q : point) => p.(x) < q.(x) \/ (p.(x) = q.(x) /\ p.(y) < q.(y))) [a] (T0 ++ T).
  destruct H0 as [H0 _]. specialize (H0 H).
  destruct H0 as [_ H0]. specialize (IHT0 H0).
  tauto.
Qed.

Lemma sort_ind : forall p T0 T,
  sort p (T0 ++ T) -> sort p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T). destruct H.
  pose proof leftmost_ind p [a] (T0 ++ T) H.
  pose proof rev_ccw_list_ind' p [a] (T0 ++ T) H0.
  assert (sort p (T0 ++ T)). { split; tauto.  }
  tauto.
Qed.

(* Check if point p is inside or on the convex polygon CH *)
Fixpoint point_in_or_on (p : point) (CH : list point) : Prop :=
  match CH with
  | nil => True
  | cons r CH' =>
    match CH' with
    | nil => True
    | cons s _ => ccw r p s /\ point_in_or_on p CH'
    end
  end.

(* Convex hull algorithm ensures that CH is subset of l. *)
Definition is_max_hull (CH l: list point) :=
  (* ? In p T \/ *)
  Forall (fun p => point_in_or_on p CH) l.

(* Print left_equal. *)

(* Check if p is in triangle p1-p2-p3 *)
(** requires `~ ccw p1 p2 p3` *)
Definition point_in_triangle (p p1 p2 p3: point) : Prop :=
  (
    ccw p3 p2 p1 /\
    left_equal (build_vec p1 p2) (build_vec p1 p) /\
    left_equal (build_vec p2 p3) (build_vec p2 p) /\
    left_equal (build_vec p3 p1) (build_vec p3 p)
  ) \/
  (
    colinear p1 p2 p3 /\
    (
      colinear p p1 p2 /\ at_mid p p1 p2 \/
      colinear p p2 p3 /\ at_mid p p2 p3 \/
      colinear p p3 p1 /\ at_mid p p3 p1
    )
  ).

Lemma point_in_tri_1 : forall p1 p2 p3,
  ~ ccw p1 p2 p3 -> point_in_triangle p1 p1 p2 p3.
Proof.
  intros.
  destruct (ccw_trichotomy p1 p2 p3) as [[? | ?] | ?].
  - (** ccw p1 p2 p3 *)
    contradiction.
  - (** colinear p1 p2 p3 *)
    clear H.
    right. split; [tauto|].
    left.
    unfold colinear, parallel, at_mid, backward_or_perp in *.
    unfold cross_prod, dot_prod in *.
    simpl in *. nia.
  - (** ccw p2 p1 p3 *)
    clear H.
    left. split; [apply ccw_cyclicity; tauto|].
    unfold ccw, left_equal, left_than in *.
    unfold cross_prod in *. simpl in *.
    repeat split; nia.
Qed.

Lemma point_in_tri_2 : forall p1 p2 p3,
  ~ ccw p1 p2 p3 -> point_in_triangle p2 p1 p2 p3.
Proof.
  intros.
  destruct (ccw_trichotomy p1 p2 p3) as [[? | ?] | ?].
  - (** ccw p1 p2 p3 *)
    contradiction.
  - (** colinear p1 p2 p3 *)
    clear H.
    right. split; [tauto|].
    right; left.
    unfold colinear, parallel, at_mid, backward_or_perp in *.
    unfold cross_prod, dot_prod in *.
    simpl in *. nia.
  - (** ccw p2 p1 p3 *)
    clear H.
    left. split; [apply ccw_cyclicity; tauto|].
    unfold ccw, left_equal, left_than in *.
    unfold cross_prod in *. simpl in *.
    repeat split; nia.
Qed.

Lemma point_in_tri_3 : forall p1 p2 p3,
  ~ ccw p1 p2 p3 -> point_in_triangle p3 p1 p2 p3.
Proof.
  intros.
  destruct (ccw_trichotomy p1 p2 p3) as [[? | ?] | ?].
  - (** ccw p1 p2 p3 *)
    contradiction.
  - (** colinear p1 p2 p3 *)
    clear H.
    right. split; [tauto|].
    right.
    unfold colinear, parallel, at_mid, backward_or_perp in *.
    unfold cross_prod, dot_prod in *.
    simpl in *. nia.
  - (** ccw p2 p1 p3 *)
    clear H.
    left. split; [apply ccw_cyclicity; tauto|].
    unfold ccw, left_equal, left_than in *.
    unfold cross_prod in *. simpl in *.
    repeat split; nia.
Qed.

Lemma point_in_tri_general : forall p a b c,
  ccw c p b ->
  ccw b p a ->
  ccw c p a ->
  ~ ccw a b c ->
  point_in_triangle b p c a.
Proof.
  unfold point_in_triangle, ccw, left_equal, left_than, cross_prod, build_vec;
  simpl in *. intros.
  nia.
Qed.

Lemma point_in_tri_cyclicity : forall p a b c,
  point_in_triangle p a b c <-> point_in_triangle p b c a.
Proof.
  unfold point_in_triangle, ccw, left_equal, left_than, colinear, parallel, at_mid, backward_or_perp, cross_prod, build_vec;
  simpl in *. intros.
  nia.
Qed.

Definition strict_point_in_triangle (p a b c : point) :=
  ccw c p a /\ ccw b p c /\ ccw a p b.

(** Construct a method to seperate situation on the edges of triangle. *)
Lemma point_in_tri_col : forall p a b c,
  colinear a b c ->
  point_in_triangle p a b c ->
  at_mid p c a \/ at_mid p b c \/ at_mid p a b.
Proof.
  intros.
  unfold point_in_triangle, colinear, parallel, at_mid, backward_or_perp, ccw, left_equal, left_than in *.
  unfold cross_prod, dot_prod in *.
  simpl in *. nia.
Qed.

Lemma point_in_tri_split_weak : forall p a b c,
  ~ ccw c a p ->
  strict_point_in_triangle b c a p ->
  forall q,
  strict_point_in_triangle q b a p ->
  point_in_triangle q c a p.
Proof.
  unfold strict_point_in_triangle, point_in_triangle, ccw, left_equal, left_than, cross_prod, build_vec;
  simpl in *. intros.
  nia.
Qed.

Lemma Z_ge_dec : forall (a b : Z),
  a >= b -> {a > b} + {a = b}.
Proof.
  intros.
  apply Z.ge_le in H.
  apply Z_le_lt_eq_dec in H.
  destruct H.
  - left; nia.
  - right; lia.
Qed.

Lemma dot_prod_squared_zero_dec : forall a b,
  dot_prod (build_vec a b) (build_vec a b) = 0 ->
  a = b.
Proof.
  unfold dot_prod; simpl; intros.
  destruct a, b; simpl in H.
  remember (point_x1 - point_x0) as x;
  remember (point_y1 - point_y0) as y.
  assert (x = 0 /\ y = 0). { nia. }
  assert (point_x0 = point_x1 /\ point_y0 = point_y1). { lia. }
  destruct H1; subst. tauto.
Qed.

Lemma dot_prod_squared_dec : forall a b,
  {a = b} + {dot_prod (build_vec a b) (build_vec a b) > 0}.
Proof.
  intros;
  pose proof metric_nonneg (build_vec a b);
  remember (dot_prod (build_vec a b) (build_vec a b)).
  apply Z_ge_dec in H; destruct H.
  - right; tauto.
  - left; apply dot_prod_squared_zero_dec; lia.
Qed.

Lemma dot_prod_squared_non_neg : forall a b,
  dot_prod (build_vec a b) (build_vec a b) <= 0 ->
  a = b.
Proof.
  intros.
  pose proof metric_nonneg (build_vec a b).
  assert (dot_prod (build_vec a b) (build_vec a b) = 0). { nia. }
  apply dot_prod_squared_zero_dec; tauto.
Qed.

(** =========================================== *)

(* Print colinear_perm132. *) (** p q r -> p r q *)
(* Print colinear_perm213. *) (** p q r -> q p r *)
(* Print colinear_perm231. *) (** p q r -> q r p *)
(* Print colinear_perm312. *) (** p q r -> r p q *)
(* Print colinear_perm321. *) (** p q r -> r q p *)

(** double colinear, one with at_mid => 4-point colinear ? *)
Lemma mid_colinear_4point : forall a b c d,
  colinear c a b ->
  colinear d a b ->
  at_mid d a b ->
  colinear c a d /\ colinear b c d.
Proof.
  intros ? ? ? ? Hcab Hdab ?;
  pose proof colinear_perm213 _ _ _ Hcab as Hacb;
  pose proof colinear_perm213 _ _ _ Hdab as Hadb;
  unfold colinear, parallel, at_mid, backward_or_perp in *.
  assert (cross_prod (build_vec c a) (build_vec a b) = 0) as Hcab_.
  {
    unfold cross_prod in Hcab; unfold cross_prod; simpl in *; nia.
  }
  assert (cross_prod (build_vec c d) (build_vec a b) = 0) as Hdab_.
  {
    assert (cross_prod (build_vec c d) (build_vec a b) =
            - cross_prod (build_vec a c) (build_vec a b) +
            cross_prod (build_vec a d) (build_vec a b)) as _Hc.
            { unfold cross_prod; simpl; nia. }
    lia.
  }
  assert (cross_prod (build_vec c a) (build_vec c d) = 0).
  {
    pose proof aux2 (build_vec a b) (build_vec c a) (build_vec c d) as H_aux.
    pose proof dot_prod_squared_dec a b as [? | ?].
    * (** A = B *)
      subst.
      pose proof dot_prod_squared_non_neg _ _ H; subst.
      apply cross_prod_self.
    * (** A != B *)
      remember (cross_prod (build_vec c a) (build_vec c d)) as z0;
      remember (dot_prod (build_vec a b) (build_vec a b)) as z1.
      rewrite Hcab_ in H_aux; rewrite Hdab_ in H_aux; simpl in H_aux.
      nia.
  }
  assert (cross_prod (build_vec a d) (build_vec c a) = 0) as Hdca_.
  {
    assert (cross_prod (build_vec a d) (build_vec c a) =
          - cross_prod (build_vec c a) (build_vec c d) +
            cross_prod (build_vec c a) (build_vec c a)). { unfold cross_prod; simpl; nia. }
    pose proof cross_prod_self (build_vec c a).
    lia.
  }
  assert (cross_prod (build_vec c b) (build_vec c a) = 0) as Hbca_.
  {
    unfold cross_prod in Hcab; unfold cross_prod. simpl in *; nia.
  }
  assert (cross_prod (build_vec b c) (build_vec b d) = 0).
  {
    pose proof aux2 (build_vec c a) (build_vec a d) (build_vec c b) as H_aux.
    pose proof dot_prod_squared_dec c a as [? | ?].
    * (** C = A *)
      subst.
      assert (cross_prod (build_vec b a) (build_vec b d) =
              cross_prod (build_vec b d) (build_vec b d) -
              cross_prod (build_vec d a)(build_vec d b)). { unfold cross_prod; simpl; nia. }
      pose proof cross_prod_self (build_vec b d).
      lia.
    * (** C != A *)
      rewrite Hbca_ in H_aux; rewrite Hdca_ in H_aux.
      simpl in H_aux.
      remember (cross_prod (build_vec a d) (build_vec c b)) as z0;
      remember (dot_prod (build_vec c a) (build_vec c a)) as z1.
      assert (z0 = 0). { nia. }
      assert (cross_prod (build_vec b c) (build_vec b d) =
              cross_prod (build_vec b c) (build_vec b c) +
              cross_prod (build_vec c a) (build_vec c b) +
              cross_prod (build_vec a d) (build_vec c b)). { unfold cross_prod; simpl; nia. }
      pose proof cross_prod_self (build_vec b c).
      lia.
  }
  split; tauto.
Qed.

(** Print aux. *)
(* forall v v1 v2 : vec,
dot_prod v1 v2 * dot_prod v v =
dot_prod v1 v * dot_prod v2 v + cross_prod v1 v * cross_prod v2 v *)
(** Print aux2. *)
(* forall v v1 v2 : vec,
cross_prod v1 v2 * dot_prod v v =
cross_prod v1 v * dot_prod v2 v - cross_prod v2 v * dot_prod v1 v *)

Lemma point_in_tri_col_mid : forall p a b c,
  ~ ccw a b c ->
  colinear p b c ->
  at_mid p b c ->
  point_in_triangle p a b c.
Proof.
  intros.
  pose proof (ccw_trichotomy c b a) as [[? | ?] | ?].
  - clear H. left. split; [tauto|].
    repeat split.
    + (** LE a->b a->p *)
      into_vec_prod.
      pose proof aux2 (build_vec c b) (build_vec b a) (build_vec p b).
      assert (cross_prod (build_vec b a) (build_vec c b) < 0) as _H1.
      {
        assert (cross_prod (build_vec c a) (build_vec c b) =
                cross_prod (build_vec c b) (build_vec c b) +
                cross_prod (build_vec b a) (build_vec c b)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c b).
        nia.
      }
      assert (dot_prod (build_vec p b) (build_vec c b) >= 0) as _H2.
      {
        assert (dot_prod (build_vec p b) (build_vec c b) =
                dot_prod (build_vec p b) (build_vec p b) -
                dot_prod (build_vec p b) (build_vec p c)).
        { unfold dot_prod; simpl; nia. }
        pose proof metric_nonneg (build_vec p b).
        nia.
      }
      assert (cross_prod (build_vec p b) (build_vec c b) = 0) as _H3.
      {
        assert (cross_prod (build_vec p b) (build_vec c b) =
                cross_prod (build_vec p b) (build_vec p b) -
                cross_prod (build_vec p b) (build_vec p c)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec p b).
        nia.
      }
      assert (cross_prod (build_vec b a) (build_vec p b) *
              dot_prod (build_vec c b) (build_vec c b) <= 0) as _H.
      { nia. }
      clear H; rename _H into H.
      assert (cross_prod (build_vec a b) (build_vec a p) =
              cross_prod (build_vec b a) (build_vec p b)) as _H.
      {
        assert (cross_prod (build_vec a b) (build_vec a p) =
                cross_prod (build_vec b a) (build_vec b a) +
                cross_prod (build_vec b a) (build_vec p b)) as _H.
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec b a).
        nia.
      }
      rewrite _H.
      pose proof dot_prod_squared_dec c b as [? | ?].
      * (** c = b *)
        subst.
        pose proof dot_prod_squared_non_neg p b H1.
        subst.
        unfold cross_prod; simpl; nia.
      * (** c != b *)
        nia.
    + (** LE b->c b->p *)
      pose proof cross_prod_self (build_vec p b).
      into_vec_prod.
      assert (cross_prod (build_vec b c) (build_vec b p) =
              cross_prod (build_vec p b) (build_vec p b) +
              cross_prod (build_vec p b) (build_vec p c)).
      { unfold cross_prod; simpl; nia. }
      rewrite H0, H in H2; simpl; nia.

    + (** LE c->a c->p *)
      into_vec_prod.
      pose proof aux2 (build_vec c b) (build_vec b a) (build_vec c p).
      assert (cross_prod (build_vec b a) (build_vec c b) < 0) as _H1.
      {
        assert (cross_prod (build_vec c a) (build_vec c b) =
                cross_prod (build_vec c b) (build_vec c b) +
                cross_prod (build_vec b a) (build_vec c b)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c b).
        nia.
      }
      assert (dot_prod (build_vec c p) (build_vec c b) >= 0) as _H2.
      {
        assert (dot_prod (build_vec c p) (build_vec c b) =
                dot_prod (build_vec c p) (build_vec c p) -
                dot_prod (build_vec p b) (build_vec p c)).
        { unfold dot_prod; simpl; nia. }
        pose proof metric_nonneg (build_vec c p).
        nia.
      }
      assert (cross_prod (build_vec c p) (build_vec c b) = 0) as _H3.
      {
        assert (cross_prod (build_vec c p) (build_vec c b) =
                cross_prod (build_vec c p) (build_vec c p) +
                cross_prod (build_vec p b) (build_vec p c)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c p).
        nia.
      }
      assert (cross_prod (build_vec b a) (build_vec c p) *
              dot_prod (build_vec c b) (build_vec c b) <= 0) as _H.
      { nia. }
      clear H; rename _H into H.
      assert (cross_prod (build_vec c a) (build_vec c p) =
              cross_prod (build_vec b a) (build_vec c p)) as _H.
      {
        assert (cross_prod (build_vec c a) (build_vec c p) =
                cross_prod (build_vec c p) (build_vec c p) -
                cross_prod (build_vec p b) (build_vec p c) +
                cross_prod (build_vec b a) (build_vec c p)).
        { unfold cross_prod; simpl; nia. }
        pose proof cross_prod_self (build_vec c p).
        nia.
      }
      rewrite _H; clear _H.
      pose proof dot_prod_squared_dec c b as [? | ?].
      * (** c = b *)
        subst.
        pose proof dot_prod_squared_non_neg p b H1.
        subst.
        unfold cross_prod; simpl; nia.
      * (** c != b *)
        nia.
  - clear H. right. split; [apply colinear_perm321; tauto|].
    right; left. split; tauto.
  - apply ccw_cyclicity in c0; contradiction.
Qed.

(*
ccw r p0 q
H0: colinear p p0 q /\ at_mid p p0 q
-------------------------------------
p in Δp0_r_q = Δr_q_p0
*)
Lemma point_in_tri_col_mid' : forall p a b c,
  ccw a c b ->
  colinear p b c ->
  at_mid p b c ->
  point_in_triangle p a b c.
Proof.
  intros.
  pose proof point_in_tri_col_mid p a b c as _H.
  assert (~ ccw a b c) as Hn_ccw.
  { unfold ccw, left_than, cross_prod in *; simpl in *; nia. }
  specialize (_H Hn_ccw H0 H1); clear Hn_ccw.
  tauto.
Qed.

(** dot_prod *)

(** =========================================== *)

(** Remove strict is non-trivial ... *)
Lemma point_in_tri_incl : forall p a b c,
  point_in_triangle b c a p ->
  forall q,
  point_in_triangle q b a p ->
  point_in_triangle q c a p.
Proof.
  intros.
  destruct H.
  - (** ccw p a c *)
    left.
    destruct H0.
    + (** ccw p a b *)
      unfold ccw, left_than, left_equal in *.
      unfold cross_prod in *.
      simpl in *; nia.
    + (** colinear b a p *)
      split; [tauto|].
      destruct H0.
      destruct H as [? [? [? ?]]].
      destruct H1 as [[? ?] | [[? ?] | [? ?]]].
      (** Below proofs may have to use `Lemma aux` to convert between `cross_prod` and `dot_prod`, currently cannot be auto-solved. *)
      * (** colinear_at_mid q b a *)
        unfold left_equal in *;
        unfold colinear, parallel in *;
        unfold at_mid, backward_or_perp in *.
        (** e × (b + c) >= 0 *)
        assert (cross_prod (build_vec c a) (build_vec b a) >= 0) as Hc_e_bc.
        {
          unfold cross_prod in H2; unfold cross_prod.
          simpl in *; nia.
        }
        (** e × a >= 0 *)
        assert (cross_prod (build_vec c a) (build_vec p b) >= 0) as Hc_e_a.
        {
          unfold cross_prod in H0, H4; unfold cross_prod.
          simpl in *; nia.
        }
        (** a × (b + c) = 0 *)
        assert (cross_prod (build_vec p b) (build_vec b a) = 0) as Hc_a_bc.
        {
          unfold cross_prod in H0; unfold cross_prod.
          simpl in *; nia.
        }
        (** c × (b + c) = 0 *)
        assert (cross_prod (build_vec q a) (build_vec b a) = 0) as Hc_c_bc.
        {
          unfold cross_prod in H1; unfold cross_prod.
          simpl in *; nia.
        }
        (** c ⋅ (b + c) >= 0 *)
        assert (dot_prod (build_vec q a) (build_vec b a) >= 0) as Hd_c_bc.
        {
          assert (dot_prod (build_vec q a) (build_vec b a) =
                  dot_prod (build_vec q a) (build_vec b q) +
                  dot_prod (build_vec q a) (build_vec q a)) as _Hd1.
          { unfold dot_prod; simpl; nia. }
          assert (dot_prod (build_vec q a) (build_vec b a) >=
                  dot_prod (build_vec q a) (build_vec b q)) as _Hd2.
          { pose proof metric_nonneg (build_vec q a) as _H.
            unfold dot_prod in _Hd1, _H; unfold dot_prod.
            simpl in *; nia. } clear _Hd1.
          assert (dot_prod (build_vec q a) (build_vec b q) >= 0) as _Hd3.
          { unfold dot_prod in H5; unfold dot_prod.
            simpl in *; nia. }
          unfold dot_prod in _Hd2, _Hd3; unfold dot_prod.
          simpl in *; nia.
        }
        (** c × (a + b) = 0 *)
        assert (cross_prod (build_vec q a) (build_vec p q) = 0) as Hc_c_ab.
        {
          pose proof aux2 (build_vec b a) (build_vec q a) (build_vec p b) as H1_aux.
          rewrite Hc_c_bc, Hc_a_bc in H1_aux; simpl in H1_aux.
          pose proof metric_nonneg (build_vec b a) as Hmet.
          pose proof dot_prod_squared_dec b a as [? | ?].
          - (** B = A *)
            subst.
            pose proof dot_prod_squared_non_neg _ _ H5. subst.
            unfold cross_prod. simpl; lia.
          - (** B != A, *)
            clear Hmet.
            remember (dot_prod (build_vec b a) (build_vec b a)).
            assert (cross_prod (build_vec q a) (build_vec p b) = 0). { lia. }
            assert (
              cross_prod (build_vec q a) (build_vec p q) =
              cross_prod (build_vec q a) (build_vec p b) +
              cross_prod (build_vec q b) (build_vec q a)
            ). { unfold cross_prod; simpl; lia. }
            lia.
        }
        (** e × c >= 0 *)
        assert (cross_prod (build_vec c a) (build_vec q a) >= 0) as Hc_e_c.
        {
          pose proof aux2 (build_vec b a) (build_vec c a) (build_vec q a) as Hc_e_c_aux2.
          rewrite Hc_c_bc in Hc_e_c_aux2; simpl in Hc_e_c_aux2.
          pose proof metric_nonneg (build_vec b a) as _Hd_bc_bc.
          remember (cross_prod (build_vec c a) (build_vec q a)) as z0;
          remember (dot_prod (build_vec b a) (build_vec b a)) as z1;
          remember (cross_prod (build_vec c a) (build_vec b a)) as z2;
          remember (dot_prod (build_vec q a) (build_vec b a)) as z3.
          assert (z0 * z1 >= 0). { rewrite Hc_e_c_aux2; nia. }
          rewrite Heqz1 in _Hd_bc_bc.
          (** destruct on `B =? A` *)
          pose proof dot_prod_squared_dec b a as [? | ?].
          - (** B = A *)
            subst.
            pose proof dot_prod_squared_non_neg q a H5; subst.
            assert (cross_prod (build_vec c a) (build_vec c a) = 0). { apply cross_prod_self. } tauto.
          - (** B != A *)
            assert (z1 > 0) as Hz1. { rewrite Heqz1; tauto. }
            nia.
        }
        (** e × b >= 0 *)
        assert (cross_prod (build_vec c a) (build_vec b q) >= 0) as Hc_e_b.
        {
          pose proof aux2 (build_vec q a) (build_vec c a) (build_vec b q) as H1_aux.
          pose proof metric_nonneg (build_vec q a) as Hd_c_c.
          assert (cross_prod (build_vec b q) (build_vec q a) = 0). { unfold cross_prod in H1; unfold cross_prod. simpl in *; lia. } rewrite H6 in H1_aux; simpl in H1_aux.
          assert (dot_prod (build_vec b q) (build_vec q a) >= 0). { unfold dot_prod in H5; unfold dot_prod. simpl in *; nia. }
          remember (cross_prod (build_vec c a) (build_vec b q)) as z0;
          remember (dot_prod (build_vec q a) (build_vec q a)) as z1;
          remember (cross_prod (build_vec c a) (build_vec q a)) as z2;
          remember (dot_prod (build_vec b q) (build_vec q a)) as z3.
          assert (z0 * z1 >= 0). { nia. }
          rewrite Heqz1 in Hd_c_c.
          (** destruct Q =? A *)
          pose proof dot_prod_squared_dec q a as [? | ?].
          - (** Q = A *)
            subst; tauto.
          - (** Q != A *)
            nia.
        }
        repeat split.
        --(** Prove that `e × (e + c) >= 0` *)
          (** It suffices to prove that `e × c >= 0` *)
          assert (
            cross_prod (build_vec c a) (build_vec c q) =
            cross_prod (build_vec c a) (build_vec c a) -
            cross_prod (build_vec c a) (build_vec q a)
          ). { unfold cross_prod; simpl; nia. }
          pose proof cross_prod_self (build_vec c a) as Hc_e_e.
          nia.
        --(** Prove that `(a + b + c) × c >= 0` *)
          (** It suffices to prove that `c × (a + b) = 0` *)
          assert (
            cross_prod (build_vec a p) (build_vec a q) =
            cross_prod (build_vec q a) (build_vec q a) -
            cross_prod (build_vec q a) (build_vec p q)
          ). { unfold cross_prod; simpl; nia. }
          pose proof cross_prod_self (build_vec q a) as Hc_c_c.
          nia.
        --(** Prove that `(a + b + c - e) × (a + b) <= 0` *)
          (** It suffice to prove that `e × (a + b) >= 0` *)
          assert (
            cross_prod (build_vec p c) (build_vec p q) =
            cross_prod (build_vec p q) (build_vec p q) +
            cross_prod (build_vec q a) (build_vec p q) -
            cross_prod (build_vec c a) (build_vec p b) -
            cross_prod (build_vec c a) (build_vec b q)
          ). { unfold cross_prod; simpl; lia. }
          pose proof cross_prod_self (build_vec p q) as Hc_ab_ab.
          nia.
      * (** colinear_at_mid q a p *)
        pose proof mid_colinear_4point a p b q H0 H1 H5 as [? ?].
        pose proof point_in_tri_col_mid' q c a p
          ltac:(do 2 apply ccw_cyclicity; eassumption) H1 H5
          as [[_ ?] | [? _]].
        -- assumption.
        -- exfalso. into_vec_prod. unfold cross_prod, build_vec in *; simpl in *; lia.
      * (** colinear_at_mid q p b *)
        into_vec_prod.
        admit.
  - (** colinear c a p *)
    admit.
Admitted.

Lemma point_in_tri_incl' : forall p a b c,
  point_in_triangle b c a p ->
  forall q,
  point_in_triangle q c b p ->
  point_in_triangle q c a p.
Proof.
  intros p a b c H q Hq.
  rewrite point_in_tri_cyclicity in H.
  rewrite point_in_tri_cyclicity in Hq.
  rewrite point_in_tri_cyclicity.
  exact (point_in_tri_incl c p b a H q Hq).
Qed.

(* split first point p0 with convex hull CH *)
Fixpoint point_in_hull_aux (p p0 p1: point) (CH: list point) :=
  match CH with
  (** hull is not empty, proceed from `p1` to `p2` *)
  | p2 :: l => point_in_triangle p p1 p2 p0 \/
               point_in_hull_aux p p0 p2 l
  | nil => False
  end.

Definition point_in_hull (p: point) (CH: list point) :=
  match CH with
  | p0 :: p1 :: p2 :: l => point_in_hull_aux p p0 p1 (p2 :: l)
  | p0 :: p1 :: nil => colinear p p0 p1 /\ at_mid p p0 p1
  | _ => False
  end.

(* Deprecated *)
(* Fixpoint point_in_hull (p p0: point) (CH: list point) :=
  match CH with
  | p1 :: l' =>
    match l' with
    | p2 :: _ => point_in_triangle p p1 p2 p0 \/ point_in_hull p p0 l'
    | _ => colinear p p0 p1 /\ at_mid p p0 p1
    end
  | _ => False
  end. *)

(** l ⊆ (p :: CH) *)
Definition is_max_hull' (p: point) (CH l: list point) :=
  Forall (fun q => point_in_hull q (p :: CH)) l.

Lemma point_in_hull_last_tri : forall p p0 p1 p2,
  point_in_triangle p p1 p2 p0 ->
  forall CH,
  point_in_hull p (p0 :: p1 :: p2 :: CH).
Proof.
  induction CH; simpl; left; tauto.
Qed.

Lemma forall_false_elim : forall a l,
  Forall (fun _ : point => False) (a :: l) -> False.
Proof.
  intros.
  pose proof Forall_inv as H0.
  specialize (H0 _ (fun _ : point => False) a l H).
  tauto.
Qed.

Lemma point_in_hull_cons_iff : forall q p a b l,
  rev_ccw_list p (b :: a :: l) ->
  (
    point_in_hull q (p :: b :: a :: l) <->
    point_in_hull q (p :: a :: l) \/
    point_in_triangle q b a p
  ).
Proof.
  intros. induction l; intros.
  - simpl; split; intros.
    + right. tauto.
    + destruct H as [? _];
      rewrite Forall_ccw_cons_iff in H;
      destruct H as [? _].
      destruct H0; [|tauto].
      left. apply (point_in_tri_col_mid' q b a p).
      * tauto.
      * apply colinear_perm132. tauto.
      * apply at_mid_comm; tauto.
  - split; intros.
    + pose proof rev_ccw_list_remove_middle p [b; a] [a0] l H as _H.
      specialize (IHl _H); clear _H.
      simpl in H0. simpl. tauto.
    + simpl in H0. simpl. tauto.
Qed.

Lemma point_in_hull_cons : forall p q p0 T,
  rev_ccw_list p (p0 :: T) ->
  point_in_hull q (p :: T) ->
  point_in_hull q (p :: p0 :: T).
Proof.
  intros; revert p0 H.
  induction T.
  - intros. simpl in H0; tauto.
  - intros.
    destruct T.
    + simpl. simpl in H0.
      left.
      simpl in H; destruct H as [H _]; apply Forall_ccw_cons_iff in H as [H _].
      pose proof point_in_tri_col_mid' q p0 a p H.
      destruct H0 as [Hcol Hmid]; rewrite colinear_comm in Hcol; rewrite at_mid_comm in Hmid.
      tauto.
    + pose proof point_in_hull_cons_iff q p a p0 (p1 :: T) H as [_ H1].
      apply H1. left; tauto.
Qed.

(* Lemma is_max_hull'_cons : forall p q T l,
  is_max_hull' p T l ->
  is_max_hull' p (q :: T) l.
Proof.
  unfold is_max_hull' in *. intros p q T l.
  apply Forall_impl. intros.
  apply point_in_hull_cons.
  tauto.
Qed. *)

Lemma is_max_hull'_cons_iff : forall p a b l T,
  rev_ccw_list p (b :: a :: l) ->
  (
    is_max_hull' p (b :: a :: l) T <->
    Forall (fun q : point => point_in_hull q (p :: a :: l) \/
                             point_in_triangle q b a p) T
  ).
Proof.
  unfold is_max_hull'. intros.
  induction T.
  - rewrite !Forall_nil_iff. tauto.
  - rewrite !Forall_cons_iff.
    pose proof point_in_hull_cons_iff a0 p a b l H.
    tauto.
Qed.

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

(*** ========== Proof ========== ***)

Lemma point_in_hull_le_aux : forall p p0 p1 p2 CH,
  rev_ccw_list p0 (p1 :: p2 :: CH) ->
  rev_consec_ccw (p0 :: p1 :: p2 :: CH) ->
  point_in_hull p (p0 :: p1 :: p2 :: CH) ->
  left_equal (build_vec p0 p1) (build_vec p0 p) /\
  left_equal (build_vec p1 p2) (build_vec p1 p).
Proof.
  intros; revert p0 p1 p2 H H0 H1;
  induction CH; intros.
  - clear H; destruct H0 as [? _].
    destruct H1.
    + (** point_in_tri *)
      destruct H0 as [[_ ?] | [? _]].
      * (** ccw p0 p2 p1 *)
        tauto.
      * (** colinear p1 p2 p0 *)
        into_vec_prod; nia.
    + (** col_at_mid *)
      destruct H0.
  - destruct H1.
    * (** point_in_tri *)
      destruct H1 as [[_ ?] | [? _]].
      --(** le *)
        tauto.
      --(** col_at_mid *)
        destruct H0.
        into_vec_prod; nia.
    * (* unfold Forall_ccw in *.
      do 2 rewrite Forall_cons_iff in Hc1; destruct Hc1 as [_ [Hc_p1_p0_a _]].
      rewrite Forall_cons_iff in Hc2; destruct Hc2 as [Hc_p2_p0_a _]. *)
      apply IHCH.
      -- (** rew_ccw_lits p0 (p1 :: p2 :: CH) *)
        apply (rev_ccw_list_remove_middle p0 [p1; p2] [a] CH H).
      -- (** rew_consec_ccw (p0 :: p1 :: p2 :: CH) *)
        (* Print rev_consec_ccw_cons_iff.
        Print rev_consec_ccw_snoc_iff. *)
        admit.
      -- (** point_in_hull p (p0 :: p1 :: p2 :: CH) *)
        simpl.
        admit.

Admitted.

Lemma point_in_tri_pop' : forall p a b c l T,
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
  (* ΔBAP ⊆ ΔCAP *)
  assert (forall q, point_in_triangle q b a p ->
                    point_in_triangle q c a p).
  {
    intros.
    pose proof rev_ccw_list_remove_middle p [c] [b] (a :: l) H as [Hac _].
    destruct H as [Hbc [Hab _]]. unfold Forall_ccw in Hbc, Hab, Hac. simpl in Hac.
    rewrite !Forall_cons_iff in Hbc, Hab, Hac. destruct Hbc, Hab, Hac.
    assert (~ ccw c a p). { apply ccw_anti_symmetry in H8. tauto. }
    pose proof point_in_tri_incl _ _ _ _ H3 _ H4.
    tauto.
  }
  (** ΔCBP ⊆ ΔCAP, can be somehow inferred from previous proof *)
  assert (forall q, point_in_triangle q c b p ->
                    point_in_triangle q c a p).
  {
    intros.
    pose proof rev_ccw_list_remove_middle p [c] [] (b :: a :: l) H as [Hac _].
    destruct H as [Hbc [Hab _]]. unfold Forall_ccw in Hbc, Hab, Hac. simpl in Hac.
    rewrite !Forall_cons_iff in Hbc, Hab, Hac. destruct Hbc, Hab, Hac.
    assert (~ ccw c b p). { apply ccw_anti_symmetry in H9. tauto. }
    apply H4.
    admit.
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
Admitted.

(** Prove that convex hull triangulation implies inclusion by edges *)
(** Splitting head `p0` with tail `CH` *)
Theorem point_in_hull_equiv_aux : forall p p0 p1 CH,
  rev_ccw_list p0 (p1 :: CH) ->
  rev_consec_ccw (p0 :: p1 :: CH) ->
  point_in_hull p (p0 :: p1 :: CH) ->
  point_in_hull_edges_aux_ p p0 p1 CH.
Proof.
  intros; revert p0 p1 H H0 H1.
  induction CH.
  - simpl; intros.
    destruct H1.
    into_vec_prod.
    assert (cross_prod (build_vec p1 p0) (build_vec p1 p) =
            - cross_prod (build_vec p p0) (build_vec p p1) +
            cross_prod (build_vec p p1) (build_vec p p1)).
    { unfold cross_prod; simpl; nia. }
    pose proof cross_prod_self (build_vec p p1).
    nia.
  - intros. split.
    + apply (IHCH p0 a).
      *
        pose proof rev_ccw_list_app_iff p0 [p1] (a :: CH) as [Hccw _].
        apply Hccw in H as [_ [? _]]; tauto.
      *
        destruct H0 as [? [? ?]].
        split; [|tauto].
        destruct CH; [tauto|].
        destruct H as [_ [? _]].
        apply Forall_ccw_cons_iff in H. tauto.
      *
        specialize (IHCH p0 a).
        destruct H.
        (*? should be able to reuse
        is_max_hull'_pop' in Graham_Scan.v *)
        (* TODO: point_in_hull_le_aux *)
        admit.
    + pose proof point_in_hull_le_aux _ _ _ _ _ H H0 H1;
      tauto.
Admitted.

Theorem point_in_hull_equiv : forall p p0 CH,
  rev_ccw_list p0 CH ->
  rev_consec_ccw (p0 :: CH) ->
  point_in_hull p (p0 :: CH) ->
  point_in_hull_edges p (p0 :: CH).
Proof.
  intros.
  destruct CH; [simpl; tauto|].
  destruct CH; [simpl in *; tauto|].
  split.
  - admit.
    (* pose proof point_in_hull_le_aux _ _ _ _ _ H H0 H1;
    tauto. *)
  - apply point_in_hull_equiv_aux; tauto.
Abort.
