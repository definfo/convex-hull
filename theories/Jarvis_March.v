Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
From ConvexHull Require Import ZPoints.
Local Open Scope Z.

Check ccw_dec.
Check ccw_cyclicity.
Check ccw_anti_symmetry.
Check ccw_non_degeneracy.
Check ccw_interiority.
Check ccw_transitivity.
Check ccw_dual_transitivity.
Check ccw_trichotomy.

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

(* p : current point *)
(* T : stack *)
(* Fixpoint succ (p : point) (T : list point) : list point :=
  match T with
  | t :: T' =>
    match T' with
    (* T = t :: s :: T'' *)
    | s :: T'' =>
      match (ccw_dec s t p) with
      (* ccw s t p, push stack *)
      | left _ => p :: T
      (* ~ ccw s t p, pop stack & recursion *)
      | right _ => succ p T'
      end
    (* T = [s], push stack *)
    | [] => [p ; t]
    end
  (* T = [], push stack *)
  (* assume that the first point in P is leftmost *)
  | [] => [p]
  end. *)

(* Fixpoint convex_hull_assist (P T : list point) : list point :=
  match P with
  | p :: P' => convex_hull_assist P' (succ p T)
  | [] => T
  end. *)

(* Definition convex_hull (P : list point) : list point := convex_hull_assist P []. *)

Fixpoint succ (p : point) (T : list point) : list point :=
  match T with
  | t :: T' =>
    match T' with
    (* T = t :: s :: T'' *)
    | s :: T'' =>
      match (ccw_dec s t p) with
      (* ccw s t p, push stack *)
      | left _ => p :: T
      (* ~ ccw s t p, pop stack & recursion *)
      | right _ => succ p T'
      end
    (* T = [t], push stack *)
    | [] => [p ; t]
    end
  (* untouched *)
  | [] => []
  end.

(* TODO : refactor to maintain stack order after each iter *)
Fixpoint convex_hull_assist (P T : list point) : list point :=
  match P with
  | p :: P' => convex_hull_assist P' (succ p T)
  | [] => T
  end.

(** assume that `pre_sorted_set P` holds *)
Definition convex_hull (P : list point) : list point :=
  match P with
  | p :: P' =>
    match P' with
    | q :: P'' =>
      match P'' with
      | r :: P''' => convex_hull_assist P''' [r ; q ; p]
      | [] => [q ; p]
      end
    | [] => [p]
    end
  | [] => []
  end.

(** Verification *)

(* leftmost point *)
(*
  P = s :: t :: P' ->
  forall (p : point), In p P' -> ccw s t p.
*)

Fixpoint weak_leftward (p : point) (T : list point) : Prop :=
  match T with
  | t :: T' =>
    match T' with
    (* T = t :: s :: T'' *)
    | s :: T'' => (ccw s t p \/ colinear s t p) /\ weak_leftward p T'
    | [] => True
    end
  (* untouched *)
  | [] => False
  end.

(* verify last edge *)
Definition weak_interior (p : point) (T : list point) : Prop :=
  weak_leftward p T /\
  match rev T with
  | t :: T' =>
    match T with
    | s :: T'' => ccw s t p \/ colinear s t p
    | [] => False
    end
  | [] => False
  end.

Fixpoint is_convex_hull (P T : list point) : Prop :=
  match P with
  | p :: P' => (In p T \/ weak_interior p T) /\ is_convex_hull P' T
  | [] => True
  end.

(** (ccw p0 p1 p \/ ...) \/ (p = t \/ In p T') *)

(* Next point satisfies [ccw ? ? ?] *)

Example pa := {| x := 3; y := 2|}.
Example pb := {| x := 5; y := 3|}.
Example pc := {| x := 6; y := 7|}.
Example pd := {| x := 2; y := 3|}.

Compute convex_hull [pa ; pb ; pc].
Compute convex_hull [pa ; pb ; pc ; pd].

Theorem is_convex_hull_2 : forall (p q : point),
  is_convex_hull [p ; q] (convex_hull [p ; q]).
Proof.
  simpl; intros.
  repeat split; simpl;
  left; auto.
Qed.

Theorem is_convex_hull_2r : forall (p q : point),
  is_convex_hull [p ; q] (convex_hull [q ; p]).
Proof.
  simpl; intros.
  repeat split; simpl;
  left; auto.
Qed.

Theorem is_convex_hull_jarvis_march_3 : forall (p q r : point),
  ccw p q r -> is_convex_hull [p ; q ; r] (convex_hull [p ; q ; r]).
Proof.
  simpl; intros.
  repeat split; unfold convex_hull, convex_hull_assist, succ;
  destruct (ccw_dec p q r); simpl; repeat split;
  left; auto.
Qed.

Theorem is_convex_hull_interior : forall (P T : list point) (p : point),
  is_convex_hull P T -> weak_interior p T -> is_convex_hull (p :: P) T.
Proof.
  simpl; intros; split; auto. Qed.

Lemma succ_ccw : forall (T : list point) (p q r : point),
  ccw r q p -> succ p (q :: r :: T) = p :: q :: r :: T.
Proof.
  simpl; intros.
  destruct (ccw_dec r q p); auto.
  unfold not, ccw, det in *. nia.
Qed.

Lemma succ_non_ccw : forall (T : list point) (p q r : point),
  ~ ccw r q p -> succ p (q :: r :: T) = succ p (r :: T).
Proof.
  simpl; intros.
  destruct (ccw_dec r q p).
  - unfold not, ccw, det in *. nia.
  - auto.
Qed.

Check ccw_dec.
(* ccw_dec
: forall p q r : point, {ccw p q r} + {~ ccw p q r} *)

Compute convex_hull [].
Compute convex_hull [pa].
Compute convex_hull [pa ; pb ; pc].

(* TODO *)

Compute convex_hull_assist [] [].
Compute convex_hull_assist [pa] [].
Compute convex_hull_assist [pa ; pb] [].
Compute convex_hull_assist [pa ; pb ; pc ; pd] [].

(* will fail without `ccw p q r` *)
Theorem ch_0_fail : forall (P : list point) (p q r : point),
  is_convex_hull [p ; q ; r] (convex_hull [p ; q ; r]).
Proof.
  intros; repeat split;
  unfold convex_hull, convex_hull_assist, succ;
  destruct (ccw_dec p q r); simpl; repeat split;
  try (left; apply ccw_cyclicity; apply ccw_cyclicity; assumption);
  try (left; apply ccw_cyclicity; assumption);
  try (left; assumption);
  try (right; unfold colinear, det; nia);
  try (unfold not, ccw, colinear, det in *; nia).
  Abort.


Compute convex_hull [pa ; pb].
Compute convex_hull_assist [pb] [pa].
Compute convex_hull_assist [] [pb ; pa].

Compute convex_hull [pa ; pb ; pc].

(* The point set should be sorted
   so that the first two points
   constitutes the starting edge of convex hull *)
Definition pre_sorted_set (P : list point) :=
  match P with
  | p :: P' =>
    match P' with
    (* P = p :: q :: P'' *)
    (* ? `In` *)
    | q :: P'' => forall (r : point), In r P'' -> ccw p q r
    | [] => True
    end
  | [] => True
  end.

(* Theorem ch_interior : forall (P : list point) (p : point),
  weak_interior p (convex_hull P) -> convex_hull P = convex_hull (p :: P) *)

Theorem ch_0: forall (P : list point) (p q r : point),
  P = [p ; q ; r] -> pre_sorted_set P ->
  is_convex_hull P (convex_hull P).
Proof.
  intros; subst; simpl.
  assert (ccw p q r) as H. { simpl in H0. specialize (H0 r). apply H0. auto. }
  repeat split;
  destruct (ccw_dec p q r); try contradiction;
  left; simpl; auto.
Qed.