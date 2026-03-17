(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point Graham_Scan.
From SetsClass Require Import SetsClass.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
(* /COQ-HEAD *)

(** Program state (T: list point) := a stack containing sorted points *)
Section GrahamScanRel.

  Definition State := list point.

  Fixpoint graham_scan_inc_rel (p : point) (T : list point) : program State unit :=
    match T with
    | t :: T' =>
      match T' with
      | s :: _ =>
        (* We branch on the pure Prop `ccw s t p`.
           The relational monad will handle this non-deterministically via `choice` and `test` *)
        if_else (fun _ => ccw s t p)
          (update' (fun _ => p :: T))
          (graham_scan_inc_rel p T')
      | _ =>
        update' (fun _ => p :: T)
      end
    | _ =>
      update' (fun _ => p :: T)
    end.

  Definition step_point (p : point) : program State unit :=
    T <- get' (fun s => s) ;;
    graham_scan_inc_rel p T.

  Fixpoint build_hull (l : list point) : program State unit :=
    match l with
    | p :: l' =>
      (** stack order ? *)
      build_hull l' ;;
      step_point p
    | _ =>
      skip
    end.

End GrahamScanRel.

Section GrahamScan.

  Example build_hull_3_points_left_turn :
    forall p1 p2 p3,
    ccw p1 p2 p3 ->
    build_hull [p3; p2; p1] [] tt[p3; p2; p1].
  Proof.
    intros p1 p2 p3 Hccw.
    simpl.

    unfold step_point, graham_scan_inc_rel.

    (* State transition 1: skip (s =[]) *)
    eexists tt, []. split; eauto.

    (* State transition 2: step_point p1 (s = [p1]) *)
    (* eexists tt, [p1]. split. *)

    (* State transition 3: step_point p2 (s = [p2; p1]) *)
    (* eexists tt, [p2; p1]. split. *)

    (* State transition 4: step_point p3 (state-dependent) *)
    (* eexists [p2; p1],[p2; p1]. split. *)


  Abort.

  Lemma graham_scan_inc_equiv :
    forall T p s,
    (graham_scan_inc_rel p T) s tt (graham_scan_inc p T).
  Proof.
  Abort.

End GrahamScan.

