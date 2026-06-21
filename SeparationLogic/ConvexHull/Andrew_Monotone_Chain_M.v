(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Point Graham_Scan Graham_Scan_M.
Require Import MonadLib.Monad.
From MonadLib.StateRelMonad Require StateRelBasic StateRelMonad StateRelHoare.
Import ListNotations.
Import Monad MonadNotation.
Import StateRelBasic StateRelMonad StateRelHoare.
Local Open Scope Z_scope.
Local Open Scope monad_scope.
(* /COQ-HEAD *)

(** Andrew's monotone chain uses the same stack update as [build_hull]:
    repeatedly pop the stack while the next point would make a non-left turn,
    then push the point.  The state is the stack with its top at the head. *)
Definition andrew_scan_stack (l : list point) : list point :=
  fold_left (fun T p => graham_scan_inc p T) l [].

Definition andrew_chain (l : list point) : list point :=
  rev (andrew_scan_stack l).

Definition andrew_lower_chain (sorted : list point) : list point :=
  andrew_chain sorted.

Definition andrew_upper_chain (sorted : list point) : list point :=
  andrew_chain (rev sorted).

(** [lower] runs from left to right; [upper] runs from right to left.
    For lists with at least two input points, the last vertex of each chain is
    duplicated by the other chain, so [removelast] opens both chains before
    concatenation. *)
Definition andrew_merge
    (sorted lower upper : list point) : list point :=
  match sorted with
  | [] => []
  | [_] => sorted
  | _ => removelast lower ++ removelast upper
  end.

Definition andrew_hull (sorted : list point) : list point :=
  andrew_merge
    sorted
    (andrew_lower_chain sorted)
    (andrew_upper_chain sorted).

Definition build_chain (l : list point) : program (list point) unit :=
  update' (fun _ => []) ;;
  iter step_p l tt.

Definition build_lower_chain
    (sorted : list point) : program (list point) (list point) :=
  build_chain sorted ;;
  T <- get' id ;;
  ret (rev T).

Definition build_upper_chain
    (sorted : list point) : program (list point) (list point) :=
  build_chain (rev sorted) ;;
  T <- get' id ;;
  ret (rev T).

Definition build_andrew_hull
    (sorted : list point) : program (list point) unit :=
  lower <- build_lower_chain sorted ;;
  upper <- build_upper_chain sorted ;;
  update' (fun _ => andrew_merge sorted lower upper).

Definition andrew_monotone_chain
    (sorted : list point) : program (list point) unit :=
  build_andrew_hull sorted.

Lemma build_chain_stack_correct : forall l,
  Hoare
    (fun _ : list point => True)
    (build_chain l)
    (fun _ T => T = andrew_scan_stack l).
Proof.
  intros l.
  unfold build_chain, andrew_scan_stack.
  eapply Hoare_state_intro.
  intros T0 _.
  eapply Hoare_bind with (Q := fun _ T => T = []).
  - apply (@Hoare_update' (list point) T0 (fun _ => @nil point)).
  - intros [].
    eapply Hoare_conseq_pre.
    2: apply iter_step_p_correct.
    simpl.
    intros T ->.
    reflexivity.
Qed.

Lemma build_lower_chain_correct : forall sorted,
  Hoare
    (fun _ : list point => True)
    (build_lower_chain sorted)
    (fun lower _ => lower = andrew_lower_chain sorted).
Proof.
  intros sorted.
  unfold build_lower_chain, andrew_lower_chain, andrew_chain.
  eapply Hoare_bind.
  - apply build_chain_stack_correct.
  - intros [].
    eapply Hoare_bind.
    + eapply Hoare_conseq_pre.
      2: apply (@Hoare_get' (list point) (list point)
                  (andrew_scan_stack sorted) id).
      intros T HT.
      exact HT.
    + intros T.
      apply Hoare_ret'.
      intros T' [HT' HT].
      subst T' T.
      reflexivity.
Qed.

Lemma build_upper_chain_correct : forall sorted,
  Hoare
    (fun _ : list point => True)
    (build_upper_chain sorted)
    (fun upper _ => upper = andrew_upper_chain sorted).
Proof.
  intros sorted.
  unfold build_upper_chain, andrew_upper_chain, andrew_chain.
  eapply Hoare_bind.
  - apply build_chain_stack_correct.
  - intros [].
    eapply Hoare_bind.
    + eapply Hoare_conseq_pre.
      2: apply (@Hoare_get' (list point) (list point)
                  (andrew_scan_stack (rev sorted)) id).
      intros T HT.
      exact HT.
    + intros T.
      apply Hoare_ret'.
      intros T' [HT' HT].
      subst T' T.
      reflexivity.
Qed.

Theorem build_andrew_hull_correct : forall sorted,
  Hoare
    (fun _ : list point => True)
    (build_andrew_hull sorted)
    (fun _ T => T = andrew_hull sorted).
Proof.
  intros sorted.
  unfold build_andrew_hull, andrew_hull.
  eapply Hoare_bind.
  - apply build_lower_chain_correct.
  - intros lower.
    eapply Hoare_bind with
      (Q := fun upper _ =>
              lower = andrew_lower_chain sorted /\
              upper = andrew_upper_chain sorted).
    + assert (Hupper :
          Hoare
            (fun _ : list point => lower = andrew_lower_chain sorted)
            (build_upper_chain sorted)
            (fun upper _ => upper = andrew_upper_chain sorted)).
      {
        eapply Hoare_conseq_pre.
        2: apply build_upper_chain_correct.
        intros T Hlower.
        exact I.
      }
      assert (Hlower_preserved :
          Hoare
            (fun _ : list point => lower = andrew_lower_chain sorted)
            (build_upper_chain sorted)
            (fun _ _ => lower = andrew_lower_chain sorted)).
      {
        unfold Hoare.
        intros s1 upper s2 Hlower _.
        exact Hlower.
      }
      eapply Hoare_conj.
      * exact Hlower_preserved.
      * exact Hupper.
    + intros upper.
      eapply Hoare_state_intro.
      intros T0 [Hlower Hupper].
      subst lower upper.
      apply (@Hoare_update' (list point) T0
              (fun _ =>
                 andrew_merge
                   sorted
                   (andrew_lower_chain sorted)
                   (andrew_upper_chain sorted))).
Qed.

Theorem andrew_monotone_chain_correct : forall sorted,
  Hoare
    (fun _ : list point => True)
    (andrew_monotone_chain sorted)
    (fun _ T => T = andrew_hull sorted).
Proof.
  intros sorted.
  unfold andrew_monotone_chain.
  apply build_andrew_hull_correct.
Qed.
