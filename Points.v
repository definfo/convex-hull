From HighSchoolGeometry Require Export Rutile.

Inductive point :=
  | pair (x : R) (y : R).

Notation "( x , y )" := (pair x y).

Definition fst (p : point) :=
  match p with
  | (x, y) => x
  end.

Definition snd (p : point) :=
  match p with
  | (x, y) => y
  end.

Definition det (p q r : point) : R :=
  (fst p * snd q) - (fst q * snd p) - (fst p * snd r) +
  (fst r * snd p) + (fst q * snd r) - (fst r * snd q).

(* counter-clockwise *)
Definition ccw (p q r : point) : Prop := (det p q r > 0).

Definition colinear (p q r : point) : Prop := (det p q r = 0).

Theorem real_excluded_middle: forall (x y : R),
  {x < y} + {x = y} + {y < x}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [[H|H]|H].
  - left. left. exact H.
  - left. right. exact H.
  - right. exact H.
Qed.

Lemma ccw_dec : forall (p q r : point),
  {ccw p q r} + {~ ccw p q r}.
Proof.
  unfold ccw. intros.
  remember (det p q r) as a.
  pose proof (real_excluded_middle 0 a).
  destruct H as [[H | H] | H];
  try (left; exact H);
  try (right; intros H').
  - rewrite H in H'.
    apply (Rlt_irrefl a H').
  - apply (Rlt_irrefl a).
    apply (Rlt_trans a 0 a H H').
Qed.

Lemma ccw_cyclicity : forall (p q r : point),
  ccw p q r -> ccw q r p.
Proof.
  unfold ccw, det; intros.
  remember (fst p * snd q) as a.
  remember (fst q * snd p) as b.
  remember (fst p * snd r) as c.
  remember (fst r * snd p) as d.
  remember (fst q * snd r) as e.
  remember (fst r * snd q) as f.
  assert ( a - b - c + d + e - f = e - f - b + a + d - c ) as E. { ring. }
  rewrite E in H. auto.
Qed.

Lemma ccw_anti_symmetry : forall (p q r : point),
  ccw p q r -> ~ ccw p r q.
Proof.
  unfold ccw, det, not; intros.
  remember (fst p * snd q) as a.
  remember (fst q * snd p) as b.
  remember (fst p * snd r) as c.
  remember (fst r * snd p) as d.
  remember (fst q * snd r) as e.
  remember (fst r * snd q) as f.
  assert ( a - b - c + d + e - f = - (c - d - a + b + f - e) ) as E. { ring. }
  rewrite E in H.
  remember (c - d - a + b + f - e) as g.
  assert (0 > 0) as contra.
  { apply (Rplus_gt_compat_l g) in H.
    rewrite Rplus_opp_r in H.
    rewrite Rplus_0_r in H.
    pose proof (Rgt_trans 0 g 0 H H0).
    exact H1. }
  apply (Rlt_irrefl 0 contra).
Qed.

Lemma ccw_non_degeneracy : forall (p q r : point),
  ~ colinear p q r -> ccw p q r \/ ccw p r q.
Proof.
  unfold ccw, colinear, det, not; intros.
  remember (fst p * snd q) as a.
  remember (fst q * snd p) as b.
  remember (fst p * snd r) as c.
  remember (fst r * snd p) as d.
  remember (fst q * snd r) as e.
  remember (fst r * snd q) as f.
  assert ( - (a - b - c + d + e - f) = c - d - a + b + f - e ) as E. { ring. }
  remember (a - b - c + d + e - f) as g.
  rewrite <- E.
  pose proof (real_excluded_middle g 0) as [[H0 | H0] | H0].
  - right. unfold Rgt.
    pose proof (Ropp_lt_contravar _ _ H0).
    rewrite Ropp_0 in H1. exact H1.
  - exfalso. apply H; apply H0.
  - left. exact H0.
Qed.

Lemma ccw_interiority : forall (p q r t : point),
  ccw t q r -> ccw p t r -> ccw p q t -> ccw p q r.
Proof.
  unfold ccw, det; intros.

  remember (fst t * snd q) as a1.
  remember (fst q * snd t) as b1.
  remember (fst t * snd r) as c1.
  remember (fst r * snd t) as d1.
  remember (fst q * snd r) as e1.
  remember (fst r * snd q) as f1.

  remember (fst p * snd t) as a2.
  remember (fst t * snd p) as b2.
  remember (fst p * snd q) as c2.
  remember (fst q * snd p) as d2.
  remember (fst p * snd r) as e2.
  remember (fst r * snd p) as f2.
  
  clear Heqa1 Heqb1 Heqc1 Heqd1 Heqe1 Heqf1.
  clear Heqa2 Heqb2 Heqc2 Heqd2 Heqe2 Heqf2.

  assert (c2 - d2 - e2 + f2 + e1 - f1 = 
    (a1 - b1 - c1 + d1 + e1 - f1) +
    (a2 - b2 - e2 + f2 + c1 - d1) +
    (c2 - d2 - a2 + b2 + b1 - a1) ) as H2. { ring. }
  rewrite H2.

  remember (a1 - b1 - c1 + d1 + e1 - f1) as a.
  remember (a2 - b2 - e2 + f2 + c1 - d1) as b.
  remember (c2 - d2 - a2 + b2 + b1 - a1) as c.

  assert (a + b > 0) as Hab. { apply Rplus_lt_0_compat; assumption. }
  apply Rplus_lt_0_compat; assumption.
Qed.

Theorem det_id : forall (p q r s : point),
  det p q r = det s q r + det p s r + det p q s.
Proof.
  unfold det; intros. ring. Qed.

Axiom non_colinear : forall (p q r : point),
  ~ colinear p q r.

Lemma ccw_transitivity : forall (p q r s t : point),
  ccw t s p -> ccw t s q -> ccw t s r -> ccw t p q -> ccw t q r ->
  ccw t p r.
Proof.
  intros p q r s t H1 H2 H3 H4 H5.
  (* Excluded middle *)
  pose proof (ccw_dec t p r) as [H | H]; try assumption.
  (* Hint: [~ ccw t p r] implies [ccw t r p] *)
  (* Is non-colinear axiom necessary here ? *)
  pose proof non_colinear t r p as Htrp.
  pose proof ccw_non_degeneracy t r p Htrp as [H0 | H0]; try assumption.
  Abort.
  
  

(* 点集有序？维护边集？ *)

(* Construction method *)

(* Incremental algorithm *)
(* （排序）从最小凸包递归更新边 *)
(** init : entry point *)
(** args : total_set (P) *)
(*
  size P <= 2 ? P
              : main (drop 2 P) (p1_p2 ; p2_p1)
*)

(** main : main function *)
(** args : unvisited_point_set (R) ; convex_hull (T) *)
(*
  match R with
  | nil => T
  | p' :: R' => main R' (succ p' T)
  end
*)

(** v2e : convert vertices to oriented edge (vector) *)

(** succ : update the convex hull according to ccw predicates *)
(** args : point (p) ; convex_hull (T) *)
(*
  (** INFORMAL *)
  for t_i-t_j in T :
    if ccw t_i p t_j
    then delete t_i-t_j
  insert p
*)



(* Gift-wrapping / Jarvis' march *)
(* 每步查找最外侧点
   leftmost point, -y orientation =>
   append the point with minimum polar angle =>
   exit until the initial point *)
(*
algorithm jarvis(S) is
  // S is the set of points
  // P will be the set of points which form the convex hull. Final set size is i.
  pointOnHull := leftmost point in S // which is guaranteed to be part of the CH(S)
  i := 0
  repeat
    P[i] := pointOnHull
    endpoint := S[0]      // initial endpoint for a candidate edge on the hull
    for j from 0 to |S| do
      // endpoint == pointOnHull is a rare case and can happen only when j == 1 and a better endpoint has not yet been set for the loop
      if (endpoint == pointOnHull) or (S[j] is on left of line from P[i] to endpoint)
      then endpoint := S[j]   // found greater left turn, update endpoint
    i := i + 1
    pointOnHull := endpoint
  until endpoint == P[0]      // wrapped around to first hull point *)



(* Graham's Scan*)
(* （排序）回溯维护边栈
   lowest point =>
   sorted in increasing order with initial point and x-axis =>
   backtrace until ccw with previous point *)

(*
let points be the list of points
let stack = empty_stack()

find the lowest y-coordinate and leftmost point, called P0
sort points by polar angle with P0,
if several points have the same polar angle
then only keep the farthest

for point in points:
    # pop the last point from the stack if we turn clockwise to reach this point
    while count stack > 1 and ccw(next_to_top(stack), top(stack), point) <= 0:
        pop stack
    push point to stack
end *)