Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import ZPoints.
Local Open Scope Z.

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

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Algorithm *)
Fixpoint succ (p : point) (T : list point) : list point :=
  match T with
  | cons t T' =>
    match T' with
    (* T = t :: s :: T'' *)
    | cons s T'' =>
      match (ccw_dec s t p) with
      (* ccw s t p, push stack *)
      | left _ => cons p T
      (* ~ ccw s t p, pop stack & recursion *)
      | right _ => succ p T'
      end
    (* T = [t], push stack *)
    | _ => cons p T
    end
  (* T = [], untouched *)
  | _ => cons p T
  end.

(* Stack (T): [q ; ... ; p] *)
Fixpoint convex_hull (T : list point) : list point :=
  match T with
  | cons q T' => succ q (convex_hull T')
  | _ => T
  end.

(** Properties *)
(* all point in P are right to p->q *)
Fixpoint rightward (p q : point) (P : list point) : Prop :=
  match P with
  | cons r P' => ccw p r q /\ rightward p q P'
  | nil => True
  end.

(* Stack (T) : [s ; r ; q ; ... ; p] *)
Fixpoint sort (p : point) (P : list point) : Prop :=
  match P with
  | cons q P' => rightward p q P' /\ sort p P'
  | nil => True
  end.

Lemma rightward_ind : forall (p q r : point) (P P' : list point),
  rightward p q (P ++ r :: P') -> rightward p q (P ++ P').
Proof.
  induction P; simpl; intros.
  - destruct H. assumption.
  - destruct H as [H IH]. specialize (IHP P' IH).
    split; assumption.
Qed.

Lemma sort_ind : forall (p q : point) (P P' : list point),
  sort p (P ++ q :: P') -> sort p (P ++ P').
Proof.
  induction P; simpl; intros.
  - destruct H. assumption.
  - split; destruct H as [Hr H];
    pose proof rightward_ind as IHr;
    specialize (IHr p a q P P' Hr);
    specialize (IHP P' H);
    assumption.
Qed.

(* Stack (T) : [ s ; r ; q ; ... ; p ] *)
(* ccw q r s /\ ccw r s p *)
(* p := last T *)
Fixpoint convex (p : point) (T : list point) : Prop :=
  match T with
  | cons s T' =>
    match T' with
    | cons r (cons q _) => ccw q r s /\ ccw r s p /\ convex p T'
    | _ => True
    end
  | _ => True
  end.

Lemma convex_ind : forall (p q : point) (T : list point),
  convex p (q :: T) -> convex p T.
Proof.
  destruct T; intros; try eauto.
  destruct T; intros; try eauto.
  destruct H as [_ [_ H]]. assumption.
Qed.

(** Simple case *)
(*  After init,
the vertices on T are the vertices of C_2
in clockwise order. *)
Theorem convex_0 : forall (p q r : point),
  sort p [r ; q ; p] -> convex p [q ; p] ->
  convex p [r ; q ; p].
Proof.
  simpl; intros.
  destruct H. destruct H.
  repeat split; try assumption;
  try (apply ccw_cyclicity; assumption).
Qed.

Theorem graham_convex_0 : forall (p q r : point),
  sort p [r ; q ; p] -> convex p (convex_hull [r ; q ; p]).
Proof.
  simpl; intros.
  destruct H as [[H _] [_ _]].
  destruct (ccw_dec p q r);
  try (unfold not, ccw, det in *; nia).
  repeat split; try eauto.
  apply ccw_cyclicity; assumption.
Qed.

(** Proof *)
(*  After the i’th iteration,
the vertices on the stack are the vertices of C_i
in clockwise order.  *)
(* Prove that [convex_hull T] is subset of T retaining order *)
Lemma succ_stack : forall (a : point) (T : list point),
  exists T0 T', T = T0 ++ T' /\ succ a T = a :: T'.
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

Lemma rightward_ind' : forall (p q : point) (T0 T : list point),
  rightward p q (T0 ++ T) -> rightward p q T.
Proof.
  induction T0; intros; try assumption.
  destruct H. apply (IHT0 T H0).
Qed.

Theorem rightward_conv : forall (p q : point) (T : list point),
  rightward p q T -> rightward p q (convex_hull T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof rightward_ind p q a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (convex_hull T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; rewrite H1 in *; rewrite H2.
  - destruct H; split; assumption. 
  - destruct H. split; try assumption.
    destruct IHT.
    pose proof rightward_ind' p q T0 T'.
    apply (H6 H5).
Qed.

Lemma sort_ind' : forall (p : point) (T0 T : list point),
  sort p (T0 ++ T) -> sort p T.
Proof.
  induction T0; intros; try assumption.
  specialize (IHT0 T). destruct H. apply (IHT0 H0).
Qed.

Theorem sort_conv : forall (p : point) (T : list point),
  sort p T -> sort p (convex_hull T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof sort_ind p a [] T H.
  specialize (IHT H0).
  pose proof succ_stack a (convex_hull T).
  destruct H1 as [T0 [T' [H1 H2]]].
  induction T0; simpl in H1; rewrite H1 in *; rewrite H2;
  destruct H; split.
  - pose proof rightward_conv p a T H.
    rewrite <- H1. assumption.
  - assumption.
  - pose proof rightward_conv p a T H.
    rewrite H1 in H4.
    pose proof rightward_ind' p a (a0 :: T0) T'.
    apply (H5 H4).
  - destruct IHT.
    pose proof sort_ind' p T0 T'.
    apply (H6 H5).
Qed.

Theorem sort_convex_ind : forall (p q : point) (T : list point),
  sort p (q :: T) -> convex p T -> convex p (succ q T).
Proof.
  intros. destruct H.
  destruct T; try eauto.
  generalize dependent p0.
  induction T; intros; simpl; try eauto.
  destruct (ccw_dec a p0 q).
  - destruct H as [H _].
    repeat split; try assumption;
    try (apply ccw_cyclicity; assumption).
  - pose proof IHT a.
    pose proof rightward_ind p q p0 [] (a :: T) H.
    pose proof sort_ind p p0 [] (a :: T) H1.
    pose proof convex_ind p p0 (a :: T) H0.
    specialize (H2 H3 H4 H5). assumption.
Qed.

Theorem graham_convex_1 : forall (p : point) (T : list point),
  sort p T -> convex p (convex_hull T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof sort_ind p a [] T H. specialize (IHT H0).
  pose proof sort_convex_ind p a (convex_hull T).
  apply H1; try assumption. clear H0 H1.
  simpl in *. destruct H. split.
  - apply rightward_conv. assumption.
  - apply sort_conv. assumption.
Qed.