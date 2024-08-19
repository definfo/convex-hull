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

Fixpoint convex_hull_assist (P T : list point) : list point :=
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
  end.



Fixpoint _sort (p : point) (P : list point) : Prop :=
  match P with
  | cons q P' =>
    match P' with
    | cons r _ => ccw p r q /\ _sort p P'
    | nil => True
    end
  | nil => False
  end.

(* all point in P is left to p->q *)
Fixpoint leftward (p q : point) (P : list point) : Prop :=
  match P with
  | cons r P' => ccw p q r /\ leftward p q P'
  | nil => True
  end.

(* Set (P) : [ q ; r ; ... ] *)
Fixpoint sort (p : point) (P : list point) : Prop :=
  match P with
  | cons q P' => leftward p q P' /\ sort p P'
  | nil => True
  end.

(* all point in P is right to p->q *)
Fixpoint rightward (p q : point) (P : list point) : Prop :=
  match P with
  | cons r P' => ccw p r q /\ rightward p q P'
  | nil => True
  end.

(* ? for recursion *)
Fixpoint sort' (p : point) (P : list point) : Prop :=
  match P with
  | cons q P' => rightward p q P' /\ sort' p P'
  | nil => True
  end.

(* Stack (T) : [ s ; r ; q ; ... ; p ], check recursively from s. *)
(* ccw q r s /\ ccw r s p *)
(* p = last T *)
Fixpoint convex (p : point) (T : list point) : Prop :=
  match T with
  | cons s (cons r (cons q T')) => ccw q r s /\ ccw r s p /\ convex p T'
  | _ => True
  end.

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

(* After ___,
the vertices on T are the vertices of C2
in clockwise order. *)
Theorem convex_0 : forall (p q r : point),
  sort' p [r ; q ; p] -> convex p [q ; p] ->
  convex p [r ; q ; p].
Proof.
  simpl; intros.
  destruct H. destruct H.
  repeat split; try assumption.
  apply ccw_cyclicity. assumption.
Qed.

(** Proof: *)
(* After the i’th iteration,
the vertices on T are the vertices of Ci
in clockwise order.  *)

(*
  sort p P' -> convex p (convex_hull_assist P' [p])
*)
(* Indprinciple ? *)

Example pa := {| x := 3; y := 2|}.
Example pb := {| x := 5; y := 3|}.
Example pc := {| x := 6; y := 7|}.
Example pd := {| x := 2; y := 3|}.

Compute convex_hull [pa ; pb ; pc].
Compute convex_hull [pa ; pb ; pc ; pd].