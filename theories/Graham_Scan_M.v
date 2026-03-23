(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point Graham_Scan.
From SetsClass Require Import SetsClass.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad StateRelHoare.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad StateRelHoare.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
(* /COQ-HEAD *)

(** Program state (T: list point) := a stack containing sorted points *)
Section GrahamScanRel.

  (** acr. foldl, adopted from MonadHoare.v *)
  Fixpoint prog_list_iter
             {A B: Type}
             (f: A -> B -> program (list A) B)
             (l: list A)
             (b: B):
    program (list A) B :=
    match l with
    | nil => ret b
    | a :: l0 =>
      b0 <- f a b ;;
      prog_list_iter f l0 b0
    end.

  (** =================================================== *)

  (** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) **)
  Definition pop_cond (p: point) : program (list point) bool :=
    T <- get' (fun s => s) ;;
    match T with
    | t :: s_pt :: _ =>
        ret (negb (ccw_b s_pt t p))
    | _ =>
        ret false
    end.

  (** pop(&T); **)
  Definition pop_stack : program (list point) unit :=
    T <- get' (fun s => s) ;;
    match T with
    | _ :: T' => update' (fun _ => T')
    | nil => skip
    end.

  (** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) { pop(&T); }; push(p);  **)
  Definition step_point (p : point) : program (list point) unit :=
    (** replace with repeat_break *)
    whileb (pop_cond p) pop_stack ;;
    T <- get' (fun s => s) ;;
    update' (fun _ => p :: T).

  Definition step_point' (p : point) (_ : unit) : program (list point) unit :=
    step_point p.


  (** init with one point -> iter *)
  (** Assume that l is sorted *)
  Definition build_hull (l : list point) : program (list point) unit :=
    (** append first point, or start iteration from beginning ? *)
    prog_list_iter step_point' l tt.

End GrahamScanRel.








Section GrahamScan.

  Example build_hull_3_points_left_turn :
    forall p1 p2 p3,
    ccw p1 p2 p3 ->
    build_hull [p3; p2; p1]   [] tt [p3; p2; p1].
  Proof.
    intros p1 p2 p3 Hccw.
    simpl.

    unfold build_hull, step_point'.

    (* State transition 1: skip (s =[]) *)
    eexists tt, []. split.
    - unfold step_point.
      unfold pop_cond.


    (* State transition 2: step_point p1 (s = [p1]) *)
    (* eexists tt, [p1]. split. *)

    (* State transition 3: step_point p2 (s = [p2; p1]) *)
    (* eexists tt, [p2; p1]. split. *)

    (* State transition 4: step_point p3 (state-dependent) *)
    (* eexists [p2; p1],[p2; p1]. split. *)


  Abort.

End GrahamScan.

