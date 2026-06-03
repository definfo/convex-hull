(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point Graham_Scan Hull_Equiv.
From SetsClass Require Import SetsClass.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad StateRelHoare FixpointLib.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad StateRelHoare FixpointLib.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
(* /COQ-HEAD *)

Definition rev_ccw_convex (T : list point) : Prop :=
  forall l1 q l2 r l3 s l4,
    T = l1 ++ q :: l2 ++ r :: l3 ++ s :: l4 ->
    ccw s r q.

Definition is_convex_hull (base T : list point) : Prop :=
  rev_ccw_convex T /\
  is_max_hull'_edges T base.




Fixpoint iter
           {A B: Type}
           (f: A -> B -> program (list A) B)
           (l: list A)
           (b: B): program (list A) B :=
  match l with
  | nil => ret b
  | a :: l0 =>
    b0 <- f a b ;;
    iter f l0 b0
  end.


(** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) **)
Definition pop_fun (p: point) : program (list point) (CntOrBrk unit unit) :=
  T <- get' id ;;
  match T with
  | t :: s :: T' =>
      choice
        (assume!! (ccw s t p) ;;
         ret (by_break tt))
        (assume!! (~ ccw s t p) ;;
         update' (fun _ => s :: T') ;;
         ret (by_continue tt))
  (* Less than 2 elements in stack: break out of the loop *)
  | _ =>
      ret (by_break tt)
  end.
  
(** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) { pop(&T); }; push(p);  **)
Definition step_fun (p : point) : program (list point) unit :=
  repeat_break (fun _ => pop_fun p) tt ;;
  T <- get' id ;;
  update' (fun _ => p :: T).

Definition step_p (p: point) (_: unit) : program (list point) unit :=
  step_fun p.

Definition build_hull (p: point) (l: list point) : program (list point) unit :=
  update' (fun _ => (p :: nil)) ;;
  iter step_p l tt.


Theorem build_hull_hoare_final : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull p l)
        (fun _ T' => is_convex_hull l T').
Proof.
Abort.
