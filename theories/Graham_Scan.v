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

(* Fixpoint convex_hull_assist (P T : list point) : list point :=
  match P with
  (* call `succ` for each point *)
  | cons p P' => convex_hull_assist P' (succ p T)
  | _ => T
  end.

(** assume that `sort p P'` holds *)
Definition convex_hull (P : list point) : list point :=
  match P with
  | cons p P' => convex_hull_assist P' [p]
  | _ => P
  end. *)

(* Stack (T): [q ; ... ; p] *)
Fixpoint convex_hull' (T : list point) : list point :=
  match T with
  | cons q T' => succ q (convex_hull' T')
  | _ => T
  end.

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

(* ? *)
(* Definition sort' (P : list point) : Prop :=
  match P with
  | cons p P' => sort p P'
  | nil => True
  end. *)

Lemma sort_rec : forall (p q : point) (P : list point),
  sort p (q :: P) -> sort p P.
Proof.
  simpl; intros. destruct H. assumption. Qed.

(* Stack (T) : [ s ; r ; q ; ... ; p ], check recursively from s. *)
(* ccw q r s /\ ccw r s p *)
(* p := last T *)
Fixpoint convex (p : point) (T : list point) : Prop :=
  match T with
  | cons s (cons r (cons q T')) => ccw q r s /\ ccw r s p /\ convex p T'
  | _ => True
  end.

(* ? *)
(* Definition convex' (T : list point) : Prop :=
  match rev T with
  | cons p _ => convex p T
  | nil => True
  end. *)

(** Verification *)
Definition point_In_dec := In_dec point_dec.
Check point_In_dec.

Theorem succ_in : forall (p : point) (T : list point),
  In p (succ p T).
Proof.
  induction T; simpl; intros.
  - left. auto.
  - destruct T.
    + left. auto.
    + destruct (ccw_dec p0 a p).
      * left. auto.
      * auto.
Qed.

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
  sort p [r ; q ; p] -> convex p (convex_hull' [r ; q ; p]).
Proof.
  simpl; intros.
  destruct H as [[H _] [_ _]].
  destruct (ccw_dec p q r);
  try (unfold not, ccw, det in *; nia).
  repeat split; try eauto.
  apply ccw_cyclicity; assumption.
Qed.

(** Proof: *)
(*  After the i’th iteration,
the vertices on the stack are the vertices of C_i
in clockwise order.  *)

(*  Prove several properties of [convex_hull']. *)
(*? partial_ord *)
Lemma ch'_partial_ord : forall (T : list point),
  True.

Theorem rightward_conv : forall (p q : point) (T : list point),
  rightward p q T -> rightward p q (convex_hull' T).
Proof.
  induction T; simpl; intros; try eauto.
  destruct H. specialize (IHT H0).
  Abort.
  

Theorem convex_1 : forall (p q : point) (T : list point),
  sort p (q :: T) -> convex p T -> convex p (succ q T).
Proof.
  intros. destruct H.
  destruct T; try eauto.
  destruct T; try eauto.
  revert p0 p1 H H0 H1.
  induction T; simpl; intros; destruct (ccw_dec p1 p0 q);
  try (simpl; eauto);
  try (destruct H;
    repeat split; simpl; try assumption;
    try (apply ccw_cyclicity; assumption)).
  

  Admitted.

Theorem graham_convex_1 : forall (p : point) (T : list point),
  sort p T -> convex p (convex_hull' T).
Proof.
  intros.
  induction T; simpl; try eauto.
  pose proof sort_rec p a T H. specialize (IHT H0).
  pose proof convex_1 p a (convex_hull' T).
  apply H1; try assumption. clear H0 H1.
  simpl in *. Abort.

(*
  sort p P' -> convex p (convex_hull_assist P' [p])
*)
(* Indprinciple ? *)

Example pa := {| x := 3; y := 2|}.
Example pb := {| x := 5; y := 3|}.
Example pc := {| x := 6; y := 7|}.
Example pd := {| x := 2; y := 3|}.

Compute convex_hull' [pa ; pb ; pc].
Compute convex_hull' [pa ; pb ; pc ; pd].
Check convex pa [pa ; pb ; pc ; pd].