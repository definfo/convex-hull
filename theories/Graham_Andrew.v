Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point.
Local Open Scope Z.
Import GeoNotations.

(* Graham-Andrew / Andrew's Monotone Chain Algorithm *)
(*
AndrewMono(x[1..n], y[1..n]):
  // Sort points by x then y
  ? different from gift-wrapping
  
  // Step 2: Build l_hull
  l_hall = nil
  for i from 1 to n:
    (* Remove non-left turns *)
    while size(lower) >= 2 and ~ g_ccw lower[-2], lower[-1], points[i]:
      pop lower
    push points[i] to lower
  
  // Step 3: Build u_hull
  u_hall = nil
  for i from n to 1:
    (* Remove non-right turns *)
    while size(upper) >= 2 and g_ccw upper[-2] upper[-1] points[i] :
      pop u_hall
    push points[i] to u_hall
  
  // Step 4: Merge
  (* Remove duplicate endpoints *)
  pop l_hall[-1]  // overlaps with upper[0]
  pop u_hall[-1]  // overlaps with lower[0]
  convex_hull = l_hall ⋃ u_hall
  
  return convex_hull
*)

Fixpoint sort_mono (l: list point) :=
  match l with
  | nil => True
  | p :: l' =>
    match l' with
    | nil => True
    | q :: _ => p.(x) < q.(x) \/ (p.(x) = q.(x) \/ p.(y) <= q.(y)) /\ sort_mono l'
    end
  end.

(* TODO: Lemma sort_mono_totalOrder *)

Fixpoint l_hall_inc (p: point) (T: list point) :=
  match T with
  | q :: T' =>
    match T' with
    | r :: T'' =>
      match (ccw_dec p q r) with
      | left _ => p :: T
      | right _ => l_hall_inc p T'
      end
    | _ => p :: T
    end
  | _ => p :: T
  end.

(* l should ensure [sort_mono_l l] *)
Definition l_hall (l: list point) :=
  fold_right l_hall_inc nil l.

Fixpoint u_hall_inc (p: point) (T: list point) :=
  match T with
  | q :: T' =>
    match T' with
    | r :: T'' =>
      match (ccw_dec p q r) with
      | left _ => u_hall_inc p T'
      | right _ => p :: T
      end
    | _ => p :: T
    end
  | _ => p :: T
  end.

(* l should ensure [sort_mono l] *)
Definition u_hall (l: list point) :=
  fold_right u_hall_inc nil (rev l).

(** Proof **)
(** Final := forall l, is_semi_hall u_hall l /\ is_semi_hall l_hall l *)

Fixpoint in_semi_hall (p: point) (l: list point) :=
  match l with
  | nil => True
  | p0 :: l' =>
    match l' with
    | nil => True
    | p1 :: _ => g_ccw p0 p1 p /\ in_semi_hall p l'
    end
  end.

Definition is_semi_hall (CH: list point) (l: list point) :=
  Forall (fun p => in_semi_hall p CH) l.

Lemma l_hall_pre: forall l,
  sort_mono l -> is_semi_hall (l_hall l) l.
Proof.
  destruct l; intros;
  try unfold is_semi_hall; eauto.
  induction l; intros;
  try unfold is_semi_hall; eauto.
  
Abort.

Theorem graham_andrew_1: forall l,
  sort_mono l ->
  is_semi_hall (l_hall l) l /\ is_semi_hall (u_hall l) l.
  (** l := [a ; ... ; b] ->
    l_hall l = [a ; ... ; b] /\ u_hall l = [b ; ... ; a] *)
Proof.
  
Abort.
