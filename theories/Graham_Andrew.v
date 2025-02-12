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

(* l should ensure [sort_mono l] *)
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

(* Definition point_in_list_b (p: point) (l: list point) : bool := . *)
Parameter point_in_list_b : point -> list point -> bool.

(* l should ensure [sort_mono l] *)
(* ! extensionality on point for `In p ...` to work *)
Definition graham_andrew (l: list point) :=
  filter (fun p => orb (point_in_list_b p (l_hall l)) (point_in_list_b p (u_hall l))) l.

