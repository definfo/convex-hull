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


(** Program state (T: list point) := a stack containing sorted points *)
Section GrahamScanRel.

(** Step 1: Sort points by x-coordinate (and y-coordinate as tie-breaker) *)
(* Here we assume that l is already sorted *)

(** Step 2: Build hull *)
(* for point in points:
     while size(lower_stack) >= 2 and not ccw lower_stack[-1] lower_stack[-2] point:
       pop lower_stack
     push_back lower_stack point *)

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
  Definition pop_cond (p: point) : program (list point) (CntOrBrk unit unit) :=
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

  (** pop(&T); **)
  Definition pop_stack : program (list point) unit :=
    T <- get' id ;;
    match T with
    | _ :: T' => update' (fun _ => T')
    | nil => skip
    end.

  (** while ( length(T) >= 2 && ¬ccw(T[1], T[0], p) ) { pop(&T); }; push(p);  **)
  Definition step_point (p : point) : program (list point) unit :=
    repeat_break (fun _ => pop_cond p) tt ;;
    T <- get' id ;;
    update' (fun _ => p :: T).

  Definition step_point' (p : point) (_ : unit) : program (list point) unit :=
    step_point p.

  (** init with one point -> iter *)
  Definition build_hull_init (p : point) (_ : list point) : program (list point) unit :=
    update' (fun _ => [p]).

  (** Assume that l is sorted *)
  Definition build_hull_next (l : list point) : program (list point) unit :=
    prog_list_iter step_point' (rev l) tt.

  Definition reverse_stack : program (list point) unit :=
    T <- get' id ;;
    update' (fun _ => rev T).

  Definition normalize_stack_fun (T : list point) : list point :=
    match rev T with
    | [] => []
    | p :: T' => p :: rev T'
    end.

  Definition normalize_stack : program (list point) unit :=
    T <- get' id ;;
    update' (fun _ => normalize_stack_fun T).

  Definition build_hull_tail (l : list point) : program (list point) unit :=
    build_hull_next l ;;
    reverse_stack.

  Definition build_hull (p : point) (l : list point) : program (list point) unit :=
    build_hull_init p l ;;
    build_hull_next l ;;
    normalize_stack.

End GrahamScanRel.


Section GrahamScanExecution.

  Inductive exec_steps : list point -> list point -> list point -> Prop :=
  | exec_steps_nil : forall T,
      exec_steps [] T T
  | exec_steps_cons : forall p l T T1 T2,
      step_point p T tt T1 ->
      exec_steps l T1 T2 ->
      exec_steps (p :: l) T T2.

  Lemma prog_list_iter_step_point_exec_steps :
    forall l T T',
      prog_list_iter step_point' l tt T tt T' <->
      exec_steps l T T'.
  Proof.
    induction l as [| p l IH]; intros T T'.
    - simpl.
      split.
      + intros H.
        unfold ret, StateRelMonad.ret in H.
        simpl in H.
        destruct H as [_ Heq].
        subst.
        constructor.
      + intros H.
        inversion H; subst.
        unfold ret, StateRelMonad.ret.
        simpl.
        split; reflexivity.
    - simpl.
      split.
      + intros H.
        unfold bind, StateRelMonad.bind in H.
        simpl in H.
        destruct H as [u [T1 [Hstep Hrest]]].
        destruct u.
        apply exec_steps_cons with (T1 := T1).
        * exact Hstep.
        * apply (IH T1 T'). exact Hrest.
      + intros H.
        inversion H as [| p' l' T0 T1 T2 Hstep Hexec Hpeq]; subst.
        unfold bind, StateRelMonad.bind.
        simpl.
        exists tt, T1.
        split.
        * exact Hstep.
        * apply (IH T1 T').
          exact Hexec.
  Qed.

  Lemma build_hull_next_exec_steps :
    forall l T T',
      build_hull_next l T tt T' <->
      exec_steps (rev l) T T'.
  Proof.
    intros l T T'.
    unfold build_hull_next.
    apply prog_list_iter_step_point_exec_steps.
  Qed.

  Lemma build_hull_tail_exec_steps :
    forall l T',
      build_hull_tail l [] tt T' <->
      exists Tmid,
        exec_steps (rev l) [] Tmid /\
        T' = rev Tmid.
  Proof.
    intros l T'.
    unfold build_hull_tail.
    split.
    - intros H.
      unfold bind, StateRelMonad.bind in H.
      simpl in H.
      destruct H as [u [Tmid [Hnext Hrev]]].
      destruct u.
      exists Tmid.
      split.
      + apply (build_hull_next_exec_steps l [] Tmid).
        exact Hnext.
      + unfold reverse_stack in Hrev.
        unfold bind, StateRelMonad.bind in Hrev.
        simpl in Hrev.
        destruct Hrev as [T0 [s1 [Hget Hupd]]].
        unfold get', get in Hget.
        simpl in Hget.
        destruct Hget as [HeqT0 Heqs1].
        subst T0 s1.
        unfold update', update in Hupd.
        simpl in Hupd.
        sets_unfold in Hupd.
        subst T'.
        reflexivity.
    - intros [Tmid [Hexec ->]].
      unfold bind, StateRelMonad.bind.
      simpl.
      exists tt, Tmid.
      split.
      + apply (build_hull_next_exec_steps l [] Tmid).
        exact Hexec.
      + unfold reverse_stack, bind, StateRelMonad.bind.
        simpl.
        exists Tmid, Tmid.
        split.
        * unfold get', get.
          simpl.
          split; reflexivity.
        * unfold update', update.
          simpl.
          sets_unfold.
          reflexivity.
  Qed.

  Lemma build_hull_exec_steps :
    forall p l T',
      build_hull p l [] tt T' <->
      exists Tmid,
        exec_steps (rev l) [p] Tmid /\
        T' = normalize_stack_fun Tmid.
  Proof.
    intros p l T'.
    unfold build_hull.
    split.
    - intros H.
      unfold bind, StateRelMonad.bind in H.
      simpl in H.
      destruct H as [u [T1 [Hinit Hrest]]].
      destruct u.
      unfold build_hull_init, update', update in Hinit.
      simpl in Hinit.
      inversion Hinit; subst T1; clear Hinit.
      unfold bind, StateRelMonad.bind in Hrest.
      simpl in Hrest.
      destruct Hrest as [u [Tmid [Hnext Hrev]]].
      destruct u.
      exists Tmid.
      split.
      + apply (build_hull_next_exec_steps l [p] Tmid).
        exact Hnext.
      + unfold normalize_stack in Hrev.
        unfold bind, StateRelMonad.bind in Hrev.
        simpl in Hrev.
        destruct Hrev as [T0 [s1 [Hget Hupd]]].
        unfold get', get in Hget.
        simpl in Hget.
        destruct Hget as [HeqT0 Heqs1].
        subst T0 s1.
        unfold update', update in Hupd.
        simpl in Hupd.
        sets_unfold in Hupd.
        subst T'.
        reflexivity.
    - intros [Tmid [Hexec ->]].
      unfold bind, StateRelMonad.bind.
      simpl.
      exists tt, [p].
      split.
      + unfold build_hull_init, update', update.
        simpl.
        reflexivity.
      + unfold bind, StateRelMonad.bind.
        simpl.
        exists tt, Tmid.
        split.
        * apply (build_hull_next_exec_steps l [p] Tmid).
          exact Hexec.
        * unfold normalize_stack, bind, StateRelMonad.bind.
          simpl.
          exists Tmid, Tmid.
          split.
          -- unfold get', get.
             simpl.
             split; reflexivity.
          -- unfold update', update.
             simpl.
             sets_unfold.
             reflexivity.
  Qed.

End GrahamScanExecution.


Section Subsequence.

  Inductive subseq {A : Type} : list A -> list A -> Prop :=
  | subseq_nil : forall l,
      subseq [] l
  | subseq_cons : forall x l1 l2,
      subseq l1 l2 ->
      subseq (x :: l1) (x :: l2)
  | subseq_skip : forall x l1 l2,
      subseq l1 l2 ->
      subseq l1 (x :: l2).

  Lemma subseq_refl : forall (A : Type) (l : list A),
    subseq l l.
  Proof.
    intros A l.
    induction l as [| x l IH].
    - constructor.
    - constructor.
      exact IH.
  Qed.

  Lemma subseq_trans : forall (A : Type) (l1 l2 l3 : list A),
    subseq l1 l2 ->
    subseq l2 l3 ->
    subseq l1 l3.
  Proof.
    intros A l1 l2 l3 H12 H23.
    revert l1 H12.
    induction H23 as [l3|x l2 l3 H23 IH|x l2 l3 H23 IH]; intros l1 H12.
    - inversion H12.
      constructor.
    - inversion H12; subst.
      + constructor.
      + constructor.
        apply IH.
        assumption.
      + apply subseq_skip.
        apply IH.
        assumption.
    - apply subseq_skip.
      apply IH.
      assumption.
  Qed.

  Lemma subseq_Forall : forall (A : Type) (P : A -> Prop) (l1 l2 : list A),
    subseq l1 l2 ->
    Forall P l2 ->
    Forall P l1.
  Proof.
    intros A P l1 l2 Hsub.
    induction Hsub; intros Hall.
    - constructor.
    - inversion Hall; subst.
      constructor; auto.
    - inversion Hall; subst.
      auto.
  Qed.

  Lemma subseq_app_left : forall (A : Type) (l1 l2 : list A),
    subseq l1 (l1 ++ l2).
  Proof.
    intros A l1 l2.
    induction l1 as [| x l1 IH].
    - constructor.
    - simpl.
      constructor.
      exact IH.
  Qed.

  Lemma subseq_last : forall (A : Type) (l : list A) (x : A),
    subseq [x] (l ++ [x]).
  Proof.
    intros A l x.
    induction l as [| y l IH].
    - simpl.
      constructor.
      constructor.
    - simpl.
      apply subseq_skip.
      exact IH.
  Qed.

  Lemma subseq_snoc : forall (A : Type) (l1 l2 : list A) (x : A),
    subseq l1 l2 ->
    subseq (l1 ++ [x]) (l2 ++ [x]).
  Proof.
    intros A l1 l2 x Hsub.
    induction Hsub.
    - simpl.
      apply subseq_last.
    - simpl.
      constructor.
      exact IHHsub.
    - simpl.
      apply subseq_skip.
      exact IHHsub.
  Qed.

  Lemma subseq_suffix : forall (A : Type) (l1 l2 : list A),
    subseq l2 (l1 ++ l2).
  Proof.
    intros A l1 l2.
    induction l1 as [| x l1 IH].
    - simpl.
      apply subseq_refl.
    - simpl.
      apply subseq_skip.
      exact IH.
  Qed.

End Subsequence.

Lemma leftmost_subseq : forall p l1 l2,
  subseq l1 l2 ->
  leftmost p l2 ->
  leftmost p l1.
Proof.
  intros p l1 l2 Hsub Hleft.
  unfold leftmost in *.
  eapply subseq_Forall; eauto.
Qed.


Section GrahamScanInvariant.

  Definition stack_subset (base : list point) (T : list point) : Prop :=
    forall q, In q T -> In q base.

  Lemma pop_cond_preserve_subset : forall base p T x T',
    stack_subset base T ->
    pop_cond p T x T' ->
    stack_subset base T'.
  Proof.
    intros base p T x T' Hsub Hrun.
    unfold pop_cond in Hrun.
    unfold bind, StateRelMonad.bind in Hrun.
    simpl in Hrun.
    destruct Hrun as [T0 [smid [Hget Hmatch]]].
    unfold get', get in Hget.
    simpl in Hget.
    destruct Hget as [Hid Hss].
    subst T0 smid.
    destruct T as [| t [| s T0]]; simpl in Hmatch.
    - unfold ret, StateRelMonad.ret in Hmatch.
      simpl in Hmatch.
      destruct Hmatch as [_ HT].
      subst T'.
      exact Hsub.
    - unfold ret, StateRelMonad.ret in Hmatch.
      simpl in Hmatch.
      destruct Hmatch as [_ HT].
      subst T'.
      exact Hsub.
    - unfold choice in Hmatch.
      simpl in Hmatch.
      destruct Hmatch as [Hmatch | Hmatch].
      + unfold bind, StateRelMonad.bind in Hmatch.
        simpl in Hmatch.
        destruct Hmatch as [uu [s1 [Hassume Hret]]].
        unfold test' in Hassume.
        simpl in Hassume.
        destruct Hassume as [_ Hs1].
        subst s1.
        unfold ret, StateRelMonad.ret in Hret.
        simpl in Hret.
        destruct Hret as [_ HT].
        subst T'.
        exact Hsub.
      + unfold bind, StateRelMonad.bind in Hmatch.
        simpl in Hmatch.
        destruct Hmatch as [uu [s1 [Hassume Hrest]]].
        unfold test' in Hassume.
        simpl in Hassume.
        destruct Hassume as [_ Hs1].
        subst s1.
        unfold bind, StateRelMonad.bind in Hrest.
        simpl in Hrest.
        destruct Hrest as [u0 [s2 [Hupd Hret]]].
        destruct u0.
        unfold update', update in Hupd.
        simpl in Hupd.
        sets_unfold in Hupd.
        subst s2.
        unfold ret, StateRelMonad.ret in Hret.
        simpl in Hret.
        destruct Hret as [_ HT].
        subst T'.
        intros q Hinq.
        apply Hsub.
        simpl.
        tauto.
  Qed.

  Lemma Hoare_pop_cond_subset : forall base p,
    Hoare (stack_subset base) (pop_cond p)
      (fun _ T' => stack_subset base T').
  Proof.
    intros base p.
    exact (fun s1 x s2 Hpre Hrun => pop_cond_preserve_subset base p s1 x s2 Hpre Hrun).
  Qed.

  Lemma repeat_break_preserve_subset : forall base p T T',
    stack_subset base T ->
    repeat_break (fun _ : unit => pop_cond p) tt T tt T' ->
    stack_subset base T'.
  Proof.
    intros base p T T' Hsub Hrun.
    assert (Hbody :
      forall a : unit,
        Hoare (fun T0 : list point => stack_subset base T0)
              (pop_cond p)
              (fun (x : CntOrBrk unit unit) (s : list point) =>
                 match x with
                 | by_continue _ => stack_subset base s
                 | by_break _ => stack_subset base s
                 end)).
    {
      intros a.
      eapply Hoare_conseq_post.
      2: apply Hoare_pop_cond_subset.
      intros b s H. destruct b; simpl in *; tauto.
    }
    pose proof (Hoare_repeat_break
                  (Σ := list point) (A := unit) (B := unit)
                  (fun _ : unit => pop_cond p)
                  (fun _ T0 => stack_subset base T0)
                  (fun _ T0 => stack_subset base T0)
                  Hbody
                  tt) as Hrb.
    exact (Hrb T tt T' Hsub Hrun).
  Qed.

  Lemma step_point_preserve_subset : forall base p T T',
    stack_subset base T ->
    step_point p T tt T' ->
    stack_subset (p :: base) T'.
  Proof.
    intros base p T T' Hsub Hrun.
    unfold step_point in Hrun.
    unfold bind, StateRelMonad.bind in Hrun.
    simpl in Hrun.
    destruct Hrun as [u [Tmid [Hrep Htail]]].
    destruct u.
    unfold bind, StateRelMonad.bind in Htail.
    simpl in Htail.
    destruct Htail as [T0 [s1 [Hget Hupd]]].
    unfold get', get in Hget.
    simpl in Hget.
    destruct Hget as [Heq Hss].
    subst T0 s1.
    unfold update', update in Hupd.
    simpl in Hupd.
    sets_unfold in Hupd.
    subst T'.
    intros q Hinq.
    simpl in Hinq.
    destruct Hinq as [<- | Hinq].
    - left; reflexivity.
    - right.
      pose proof (repeat_break_preserve_subset base p T (id Tmid) Hsub Hrep) as Hmid.
      apply Hmid.
      exact Hinq.
  Qed.

  Lemma step_point_result_shape : forall p T T',
    step_point p T tt T' ->
    exists T0, T' = p :: T0.
  Proof.
    intros p T T' Hrun.
    unfold step_point in Hrun.
    unfold bind, StateRelMonad.bind in Hrun.
    simpl in Hrun.
    destruct Hrun as [u [Tmid [Hrep Htail]]].
    destruct u.
    unfold bind, StateRelMonad.bind in Htail.
    simpl in Htail.
    destruct Htail as [T0 [s1 [Hget Hupd]]].
    unfold get', get in Hget.
    simpl in Hget.
    destruct Hget as [Heq Hss].
    subst T0 s1.
    unfold update', update in Hupd.
    simpl in Hupd.
    sets_unfold in Hupd.
    subst T'.
    eauto.
  Qed.

  Lemma exec_steps_preserve_subset : forall l base T T',
    exec_steps l T T' ->
    stack_subset base T ->
    stack_subset (l ++ base) T'.
  Proof.
    intros l base T T' Hexec.
    revert base.
    induction Hexec as [T|p l T T1 T2 Hstep Hexec IH]; intros base Hsub.
    - simpl. exact Hsub.
    - simpl.
      assert (Hsub1 : stack_subset (p :: base) T1).
      { eapply step_point_preserve_subset; eauto using Hstep. }
      specialize (IH (p :: base) Hsub1).
      intros q Hinq.
      specialize (IH q Hinq).
      apply in_app_iff in IH as [Hinl | Hinpb].
      + simpl.
        right.
        apply in_or_app.
        left.
        exact Hinl.
      + simpl in Hinpb.
        simpl.
        destruct Hinpb as [Heq | Hinb].
        * left. exact Heq.
        * right.
          apply in_or_app.
          right.
          exact Hinb.
  Qed.

  Lemma exec_steps_nonempty : forall l T T',
    exec_steps l T T' ->
    T <> [] ->
    T' <> [].
  Proof.
    induction 1 as [T|p l T T1 T2 Hstep Hexec IH]; intros Hne.
    - exact Hne.
    - apply IH.
      intro HeqT1.
      pose proof (step_point_result_shape p T T1 Hstep) as [Tx HT1].
      rewrite HT1 in HeqT1.
      discriminate.
  Qed.

  Lemma build_hull_tail_subset : forall l T',
    build_hull_tail l [] tt T' ->
    stack_subset l T'.
  Proof.
    intros l T' Hrun.
    apply build_hull_tail_exec_steps in Hrun.
    destruct Hrun as [Tmid [Hexec ->]].
    assert (Hbase : stack_subset [] []).
    {
      intros q Hinq.
      inversion Hinq.
    }
    pose proof (exec_steps_preserve_subset (rev l) [] [] Tmid Hexec Hbase) as Hsub.
    intros q Hinq.
    assert (Hinmid : In q Tmid).
    { apply in_rev. exact Hinq. }
    specialize (Hsub q Hinmid).
    rewrite app_nil_r in Hsub.
    apply in_rev.
    exact Hsub.
  Qed.

End GrahamScanInvariant.

Section GrahamScanRefinement.

  Definition stack_subseq (base : list point) (T : list point) : Prop :=
    subseq (rev T) base.

  Definition rev_ccw_convex (T : list point) : Prop :=
    forall l1 q l2 r l3 s l4,
      T = l1 ++ q :: l2 ++ r :: l3 ++ s :: l4 ->
      ccw s r q.

  Definition is_convex_hull (base T : list point) : Prop :=
    rev_ccw_convex T /\
    is_max_hull'_edges T base.

  Fixpoint pop_fun (p : point) (T : list point) : list point :=
    match T with
    | t :: T' =>
        match T' with
        | s :: T'' =>
            match ccw_dec s t p with
            | left _ => T
            | right _ => pop_fun p T'
            end
        | _ => T
        end
    | _ => T
    end.

  Definition step_fun (p : point) (T : list point) : list point :=
    p :: pop_fun p T.

  Fixpoint run_tail (T : list point) (l : list point) : list point :=
    match l with
    | [] => T
    | p :: l' => run_tail (step_fun p T) l'
    end.

  Definition run_fun_tail (l : list point) : list point :=
    rev (run_tail [] (rev l)).

  Definition run_fun (p : point) (l : list point) : list point :=
    normalize_stack_fun (run_tail [p] (rev l)).

  Lemma step_fun_eq_graham_scan_inc : forall p T,
    step_fun p T = graham_scan_inc p T.
  Proof.
    intros p T.
    unfold step_fun.
    induction T as [| t T IH]; simpl.
    - reflexivity.
    - destruct T as [| s T'].
      + reflexivity.
      + destruct (ccw_dec s t p).
        * reflexivity.
        * exact IH.
  Qed.

  Lemma run_tail_app : forall T l1 l2,
    run_tail T (l1 ++ l2) = run_tail (run_tail T l1) l2.
  Proof.
    intros T l1.
    induction l1 as [| x l1 IH] in T |- *; intros l2; simpl.
    - reflexivity.
    - rewrite IH.
      reflexivity.
  Qed.

  Lemma run_tail_rev_graham_scan : forall l,
    run_tail [] (rev l) = graham_scan l.
  Proof.
    induction l as [| a l IH]; simpl.
    - reflexivity.
    - simpl.
      rewrite run_tail_app.
      rewrite IH.
      simpl.
      rewrite step_fun_eq_graham_scan_inc.
      reflexivity.
  Qed.

  Lemma run_fun_tail_graham_scan : forall l,
    run_fun_tail l = rev (graham_scan l).
  Proof.
    intros l.
    unfold run_fun_tail.
    rewrite run_tail_rev_graham_scan.
    reflexivity.
  Qed.

  Lemma rev_run_fun_tail_graham_scan : forall l,
    rev (run_fun_tail l) = graham_scan l.
  Proof.
    intros l.
    rewrite run_fun_tail_graham_scan.
    rewrite rev_involutive.
    reflexivity.
  Qed.

  Lemma repeat_break_pop_fun : forall p T,
    repeat_break (fun _ : unit => pop_cond p) tt T tt (pop_fun p T).
  Proof.
    intros p T.
    induction T as [| t T IH].
    - simpl.
      pose proof (repeat_break_unfold (fun _ : unit => pop_cond p) tt [] tt []) as Hrb.
      apply Hrb.
      unfold_monad.
      simpl.
      exists (by_break tt), [].
      split.
      + unfold pop_cond.
        unfold get', get.
        unfold_monad.
        simpl.
        exists [], [].
        now repeat split.
      + split; reflexivity.
    - destruct T as [| s T'].
      + simpl.
        pose proof (repeat_break_unfold (fun _ : unit => pop_cond p) tt [t] tt [t]) as Hrb.
        apply Hrb.
        unfold_monad.
        simpl.
        exists (by_break tt), [t].
        split.
        * unfold pop_cond.
          unfold get', get.
          unfold_monad.
          simpl.
          exists [t], [t].
          now repeat split.
        * split; reflexivity.
      + simpl.
        destruct (ccw_dec s t p) as [Hccw | Hnccw].
        * pose proof (repeat_break_unfold (fun _ : unit => pop_cond p) tt (t :: s :: T') tt (t :: s :: T')) as Hrb.
          apply Hrb.
          unfold_monad.
          simpl.
          exists (by_break tt), (t :: s :: T').
          split.
          -- unfold pop_cond.
             unfold choice, get', get.
             unfold_monad.
             simpl.
             exists (t :: s :: T'), (t :: s :: T').
             split.
             ++ split; reflexivity.
             ++ left.
                exists tt, (t :: s :: T').
                split.
                ** split; [exact Hccw | reflexivity].
                ** split; reflexivity.
          -- split; reflexivity.
        * pose proof (repeat_break_unfold (fun _ : unit => pop_cond p) tt (t :: s :: T') tt (pop_fun p (s :: T'))) as Hrb.
          apply Hrb.
          unfold_monad.
          simpl.
          exists (by_continue tt), (s :: T').
          split.
          -- unfold pop_cond.
             unfold choice, get', get, update', update.
             unfold_monad.
             simpl.
             exists (t :: s :: T'), (t :: s :: T').
             split.
             ++ split; reflexivity.
             ++ right.
                exists tt, (t :: s :: T').
                split.
                ** split; [exact Hnccw | reflexivity].
                ** exists tt, (s :: T').
                   split; [reflexivity | split; reflexivity].
          -- apply IH.
  Qed.

  Lemma step_point_spec : forall p T,
    step_point p T tt (step_fun p T).
  Proof.
    intros p T.
    unfold step_fun, step_point.
    unfold bind, StateRelMonad.bind.
    simpl.
    exists tt, (pop_fun p T).
    split.
    - apply repeat_break_pop_fun.
    - unfold bind, StateRelMonad.bind.
      simpl.
      exists (pop_fun p T), (pop_fun p T).
      split.
      + unfold get', get.
        simpl.
        split; reflexivity.
      + unfold update', update.
        simpl.
        sets_unfold.
        reflexivity.
  Qed.

  Lemma prog_list_iter_spec : forall l T,
    prog_list_iter step_point' l tt T tt (run_tail T l).
  Proof.
    induction l as [| p l IH]; intros T.
    - simpl.
      unfold ret, StateRelMonad.ret.
      simpl.
      split; reflexivity.
    - simpl.
      unfold bind, StateRelMonad.bind.
      simpl.
      exists tt, (step_fun p T).
      split.
      + unfold step_point'.
        apply step_point_spec.
      + apply IH.
  Qed.

  Lemma build_hull_tail_spec : forall l,
    build_hull_tail l [] tt (run_fun_tail l).
  Proof.
    intros l.
    apply build_hull_tail_exec_steps.
    exists (run_tail [] (rev l)).
    split.
    - apply (proj1 (prog_list_iter_step_point_exec_steps (rev l) [] (run_tail [] (rev l)))).
      apply prog_list_iter_spec.
    - unfold run_fun_tail.
      reflexivity.
  Qed.

  Lemma pop_cond_outcome : forall p T x T',
    pop_cond p T x T' ->
    match T with
    | t :: s :: T0 =>
        (x = by_break tt /\ T' = t :: s :: T0 /\ ccw s t p) \/
        (x = by_continue tt /\ T' = s :: T0 /\ ~ ccw s t p)
    | _ =>
        x = by_break tt /\ T' = T
    end.
  Proof.
    intros p T x T' Hrun.
    unfold pop_cond in Hrun.
    unfold bind, StateRelMonad.bind in Hrun.
    simpl in Hrun.
    destruct Hrun as [T0 [smid [Hget Hmatch]]].
    unfold get', get in Hget.
    simpl in Hget.
    destruct Hget as [Hid Hss].
    subst T0 smid.
    destruct T as [| t [| s T0]]; simpl in Hmatch.
    - unfold ret, StateRelMonad.ret in Hmatch.
      simpl in Hmatch.
      destruct Hmatch as [Hx HT].
      subst x T'.
      split; reflexivity.
    - unfold ret, StateRelMonad.ret in Hmatch.
      simpl in Hmatch.
      destruct Hmatch as [Hx HT].
      subst x T'.
      split; reflexivity.
    - unfold choice in Hmatch.
      simpl in Hmatch.
      destruct Hmatch as [Hmatch | Hmatch].
      + unfold bind, StateRelMonad.bind in Hmatch.
        simpl in Hmatch.
        destruct Hmatch as [uu [s1 [Hassume Hret]]].
        unfold test' in Hassume.
        simpl in Hassume.
        destruct Hassume as [Hccw Hs1].
        subst s1.
        unfold ret, StateRelMonad.ret in Hret.
        simpl in Hret.
        destruct Hret as [Hx HT].
        subst x T'.
        left.
        repeat split; auto.
      + unfold bind, StateRelMonad.bind in Hmatch.
        simpl in Hmatch.
        destruct Hmatch as [uu [s1 [Hassume Hrest]]].
        unfold test' in Hassume.
        simpl in Hassume.
        destruct Hassume as [Hnccw Hs1].
        subst s1.
        unfold bind, StateRelMonad.bind in Hrest.
        simpl in Hrest.
        destruct Hrest as [u0 [s2 [Hupd Hret]]].
        destruct u0.
        unfold update', update in Hupd.
        simpl in Hupd.
        sets_unfold in Hupd.
        subst s2.
        unfold ret, StateRelMonad.ret in Hret.
        simpl in Hret.
        destruct Hret as [Hx HT].
        subst x T'.
        right.
        repeat split; auto.
  Qed.

  Lemma repeat_break_pop_fun_unique : forall p T T',
    repeat_break (fun _ : unit => pop_cond p) tt T tt T' ->
    T' = pop_fun p T.
  Proof.
    intros p T.
    induction T as [| t T IH]; intros T' Hrun.
    - simpl in *.
      pose proof (repeat_break_unfold (fun _ : unit => pop_cond p)) as Hunf.
      specialize (Hunf tt [] tt T').
      destruct Hunf as [Hto _].
      apply Hto in Hrun.
      unfold bind, StateRelMonad.bind in Hrun.
      simpl in Hrun.
      destruct Hrun as [x [smid [Hbody Hnext]]].
      pose proof (pop_cond_outcome p [] x smid Hbody) as Hout.
      simpl in Hout.
      destruct Hout as [Hx Hsmid].
      subst x smid.
      unfold ret, StateRelMonad.ret in Hnext.
      simpl in Hnext.
      destruct Hnext as [_ Heq].
      symmetry; exact Heq.
    - destruct T as [| s T0].
      + simpl in *.
        pose proof (repeat_break_unfold (fun _ : unit => pop_cond p)) as Hunf.
        specialize (Hunf tt [t] tt T').
        destruct Hunf as [Hto _].
        apply Hto in Hrun.
        unfold bind, StateRelMonad.bind in Hrun.
        simpl in Hrun.
        destruct Hrun as [x [smid [Hbody Hnext]]].
        pose proof (pop_cond_outcome p [t] x smid Hbody) as Hout.
        simpl in Hout.
        destruct Hout as [Hx Hsmid].
        subst x smid.
        unfold ret, StateRelMonad.ret in Hnext.
        simpl in Hnext.
        destruct Hnext as [_ Heq].
        symmetry; exact Heq.
      + simpl in *.
        pose proof (repeat_break_unfold (fun _ : unit => pop_cond p)) as Hunf.
        specialize (Hunf tt (t :: s :: T0) tt T').
        destruct Hunf as [Hto _].
        apply Hto in Hrun.
        unfold bind, StateRelMonad.bind in Hrun.
        simpl in Hrun.
        destruct Hrun as [x [smid [Hbody Hnext]]].
        pose proof (pop_cond_outcome p (t :: s :: T0) x smid Hbody) as Hout.
        simpl in Hout.
        destruct Hout as [[Hx [Hsmid Hccw]] | [Hx [Hsmid Hnccw]]].
        * subst x smid.
          unfold ret, StateRelMonad.ret in Hnext.
          simpl in Hnext.
          destruct Hnext as [_ Heq].
          subst T'.
          destruct (ccw_dec s t p) as [Hccw' | Hnccw']; [reflexivity | contradiction].
        * subst x smid.
          specialize (IH T' Hnext).
          destruct (ccw_dec s t p) as [Hccw' | Hnccw']; [contradiction | exact IH].
  Qed.

  Lemma step_point_unique_run : forall p T T',
    step_point p T tt T' ->
    T' = step_fun p T.
  Proof.
    intros p T T' Hrun.
    unfold step_point in Hrun.
    unfold bind, StateRelMonad.bind in Hrun.
    simpl in Hrun.
    destruct Hrun as [u [Tmid [Hrep Htail]]].
    destruct u.
    unfold bind, StateRelMonad.bind in Htail.
    simpl in Htail.
    destruct Htail as [T0 [s1 [Hget Hupd]]].
    unfold get', get in Hget.
    simpl in Hget.
    destruct Hget as [Heq Hss].
    subst T0 s1.
    unfold update', update in Hupd.
    simpl in Hupd.
    sets_unfold in Hupd.
    subst T'.
    unfold step_fun.
    f_equal.
    eapply repeat_break_pop_fun_unique.
    exact Hrep.
  Qed.

  Lemma exec_steps_unique_run_tail : forall l T T',
    exec_steps l T T' ->
    T' = run_tail T l.
  Proof.
    intros l T T' Hexec.
    induction Hexec as [T0|p l0 T0 T1 T2 Hstep Hrest IH].
    - reflexivity.
    - simpl.
      apply step_point_unique_run in Hstep.
      subst T1.
      exact IH.
  Qed.

  Lemma build_hull_tail_unique_run_fun : forall l T',
    build_hull_tail l [] tt T' ->
    T' = run_fun_tail l.
  Proof.
    intros l T' Hrun.
    apply build_hull_tail_exec_steps in Hrun.
    destruct Hrun as [Tmid [Hexec ->]].
    apply exec_steps_unique_run_tail in Hexec.
    unfold run_fun_tail.
    now rewrite Hexec.
  Qed.

  Lemma run_fun_tail_subset : forall l,
    stack_subset l (run_fun_tail l).
  Proof.
    intros l.
    apply build_hull_tail_subset.
    apply build_hull_tail_spec.
  Qed.

  Lemma step_fun_succ_stack : forall a T,
    exists T0 T', T = T0 ++ T' /\ step_fun a T = a :: T'.
  Proof.
    intros a T.
    unfold step_fun.
    induction T as [| t T IH].
    - exists [], [].
      split; reflexivity.
    - destruct T as [| s T'].
      + exists [], [t].
        split; reflexivity.
      + simpl.
        destruct (ccw_dec s t a).
        * exists [], (t :: s :: T').
          split; reflexivity.
        * destruct IH as [T0 [T1 [HT Hstep]]].
          exists (t :: T0), T1.
          split.
          -- simpl.
             rewrite HT.
             reflexivity.
          -- simpl.
             exact Hstep.
  Qed.

  Lemma run_tail_stack_subseq : forall l base T,
    stack_subseq base T ->
    stack_subseq (base ++ l) (run_tail T l).
  Proof.
    intros l.
    induction l as [| a l IH]; intros base T Hsub.
    - simpl.
      rewrite app_nil_r.
      exact Hsub.
    - simpl.
      destruct (step_fun_succ_stack a T) as [T0 [T' [HT Hstep]]].
      subst T.
      replace (base ++ (a :: l)) with ((base ++ [a]) ++ l).
      2: {
        rewrite <- app_assoc.
        reflexivity.
      }
      apply IH.
      unfold stack_subseq in *.
      rewrite Hstep.
      simpl.
      apply subseq_snoc.
      rewrite rev_app_distr in Hsub.
      eapply subseq_trans.
      + apply subseq_app_left.
      + exact Hsub.
  Qed.

  Lemma point_in_hull_head : forall p a l,
    rev_ccw_list p (a :: l) ->
    point_in_hull a (p :: a :: l).
  Proof.
    intros p a l Hccw.
    destruct l as [| b l'].
    - simpl.
      unfold colinear, parallel, at_mid, backward_or_perp.
      unfold dot_prod, cross_prod, build_vec.
      simpl.
      split.
      + lia.
      + lia.
    - simpl.
      left.
      unfold point_in_triangle.
      left.
      destruct Hccw as [Hfor _].
      apply Forall_ccw_cons_iff in Hfor as [Hab _].
      repeat split.
      + apply ccw_cyclicity.
        exact Hab.
      + unfold left_equal, cross_prod, build_vec.
        simpl.
        lia.
      + unfold left_equal, cross_prod, build_vec.
        unfold ccw, left_than in Hab.
        simpl in *.
        replace ((point_x p - point_x b) * (point_y a - point_y b) -
                 (point_x a - point_x b) * (point_y p - point_y b))
          with ((point_x b - point_x a) * (point_y p - point_y a) -
                (point_x p - point_x a) * (point_y b - point_y a)) by nia.
        apply Z.lt_le_incl.
        exact Hab.
      + unfold left_equal, cross_prod, build_vec.
        simpl.
        lia.
  Qed.

  Lemma rev_ccw_list_self_max_hull : forall p CH,
    rev_ccw_list p CH ->
    is_max_hull' p CH CH.
  Proof.
    intros p CH Hccw.
    induction CH as [| a CH IH].
    - unfold is_max_hull'.
      apply Forall_nil.
    - unfold is_max_hull'.
      apply Forall_cons.
      + apply point_in_hull_head.
        exact Hccw.
      + destruct CH as [| b CH'].
        * apply Forall_nil.
        * apply Forall_impl with
            (P := fun q : point => point_in_hull q (p :: b :: CH')).
          -- intros q Hq.
             eapply point_in_hull_cons.
             ++ exact Hccw.
             ++ exact Hq.
          -- apply IH.
             destruct Hccw as [_ Htail].
             exact Htail.
  Qed.

  Lemma point_in_hull_snoc : forall p q a CH,
    rev_ccw_list p (CH ++ [a]) ->
    point_in_hull q (p :: CH) ->
    point_in_hull q (p :: CH ++ [a]).
  Proof.
    intros p q a CH.
    induction CH as [| b CH IH]; intros Hccw Hinh.
    - simpl in Hinh.
      contradiction.
    - destruct CH as [| c CH'].
      + simpl in *.
        destruct Hccw as [Hfor _].
        apply Forall_ccw_cons_iff in Hfor as [Hba _].
        destruct Hinh as [Hcol Hmid].
        left.
        rewrite point_in_tri_cyclicity.
        assert (Htri : point_in_triangle q a p b).
        {
          eapply point_in_tri_col_mid'.
          - exact (ccw_cyclicity_2 _ _ _ Hba).
          - exact Hcol.
          - exact Hmid.
        }
        exact Htri.
      + change (p :: b :: c :: CH' ++ [a]) with (p :: b :: (c :: CH' ++ [a])).
        pose proof (point_in_hull_cons_iff q p c b (CH' ++ [a]) Hccw) as [_ Hto].
        apply Hto.
        assert (Hsmall_ccw : rev_ccw_list p (b :: c :: CH')).
        {
          assert (Hccw' : rev_ccw_list p ((b :: c :: CH') ++ [a] ++ []%list)).
          {
            rewrite app_nil_r.
            exact Hccw.
          }
          pose proof (rev_ccw_list_remove_middle p (b :: c :: CH') [a] [] Hccw') as Htmp.
          rewrite app_nil_r in Htmp.
          exact Htmp.
        }
        pose proof (point_in_hull_cons_iff q p c b CH' Hsmall_ccw) as [Hfrom _].
        destruct (Hfrom Hinh) as [Hsmall | Htri].
        * left.
          destruct Hccw as [_ Htail_ccw].
          apply (IH Htail_ccw Hsmall).
        * right.
          exact Htri.
  Qed.

  Lemma point_in_hull_last : forall p CH a,
    rev_ccw_list p (CH ++ [a]) ->
    point_in_hull a (p :: CH ++ [a]).
  Proof.
    intros p CH a Hccw.
    induction CH as [| b CH IH].
    - simpl.
      unfold colinear, parallel, at_mid, backward_or_perp.
      unfold dot_prod, cross_prod, build_vec.
      simpl.
      split; lia.
    - change (p :: b :: CH ++ [a]) with (p :: b :: (CH ++ [a])).
      eapply point_in_hull_cons.
      + exact Hccw.
      + apply IH.
        destruct Hccw as [_ Htail_ccw].
        exact Htail_ccw.
  Qed.

  Lemma is_max_hull'_snoc : forall p a CH l,
    rev_ccw_list p (CH ++ [a]) ->
    is_max_hull' p CH l ->
    is_max_hull' p (CH ++ [a]) l.
  Proof.
    intros p a CH l Hccw Hmax.
    unfold is_max_hull' in *.
    eapply Forall_impl.
    - intros q Hinh.
      eapply point_in_hull_snoc.
      + exact Hccw.
      + exact Hinh.
    - exact Hmax.
  Qed.

  Lemma is_max_hull'_snoc_self : forall p a CH l,
    rev_ccw_list p (CH ++ [a]) ->
    is_max_hull' p CH l ->
    is_max_hull' p (CH ++ [a]) (l ++ [a]).
  Proof.
    intros p a CH l Hccw Hmax.
    unfold is_max_hull' in *.
    rewrite Forall_app.
    split.
    - apply is_max_hull'_snoc; assumption.
    - apply Forall_cons.
      + apply point_in_hull_last.
        exact Hccw.
      + apply Forall_nil.
  Qed.

  Lemma pop_fun_preserve_rev_consec : forall p T,
    rev_consec_ccw T ->
    rev_consec_ccw (pop_fun p T).
  Proof.
    intros p T.
    induction T as [| t T IH]; intros Hcon.
    - simpl; exact Hcon.
    - destruct T as [| s T'].
      + simpl; exact Hcon.
      + simpl.
        destruct (ccw_dec s t p).
        * exact Hcon.
        * apply IH.
          apply rev_consec_ccw_cons_iff in Hcon as [Hs _].
          exact Hs.
  Qed.

  Lemma pop_fun_result_ccw : forall p T t s T',
    pop_fun p T = t :: s :: T' ->
    ccw s t p.
  Proof.
    intros p T.
    induction T as [| x T IH]; intros t s T' Hpop; simpl in Hpop.
    - discriminate.
    - destruct T as [| y T0].
      + discriminate.
      + destruct (ccw_dec y x p) as [Hccw | Hnccw].
        * inversion Hpop; subst.
          exact Hccw.
        * eapply IH.
          exact Hpop.
  Qed.

  Lemma step_fun_preserve_rev_consec : forall p T,
    rev_consec_ccw T ->
    rev_consec_ccw (step_fun p T).
  Proof.
    intros p T Hcon.
    unfold step_fun.
    pose proof (pop_fun_preserve_rev_consec p T Hcon) as Hpopcon.
    destruct (pop_fun p T) as [| t [| s T']] eqn:Hpop; simpl.
    - tauto.
    - tauto.
    - split.
      + apply ccw_cyclicity.
        eapply pop_fun_result_ccw.
        exact Hpop.
      + exact Hpopcon.
  Qed.

  Lemma run_tail_rev_consec : forall l T,
    rev_consec_ccw T ->
    rev_consec_ccw (run_tail T l).
  Proof.
    induction l as [| a l IH]; intros T Hcon.
    - simpl.
      exact Hcon.
    - simpl.
      apply IH.
      apply step_fun_preserve_rev_consec.
      exact Hcon.
  Qed.

  Lemma run_tail_rev_ccw : forall p l T,
    rev_ccw_list p (rev T ++ l) ->
    rev_ccw_list p (rev (run_tail T l)).
  Proof.
    intros p l.
    induction l as [| a l IH]; intros T Hccw.
    - simpl in *.
      rewrite app_nil_r in Hccw.
      exact Hccw.
    - simpl in Hccw.
      destruct (step_fun_succ_stack a T) as [T0 [T' [HT Hstep]]].
      subst T.
      simpl in Hccw.
      rewrite rev_app_distr in Hccw.
      simpl in Hccw.
      rewrite <- app_assoc in Hccw.
      pose proof (rev_ccw_list_remove_middle p (rev T') (rev T0) (a :: l) Hccw) as Htrim.
      simpl.
      replace (rev (run_tail (step_fun a (T0 ++ T')) l))
        with (rev (run_tail (a :: T') l)).
      2: { now rewrite Hstep. }
      apply (IH (a :: T')).
      simpl.
      replace (rev T' ++ a :: l) with (rev T' ++ [a] ++ l) in Htrim by reflexivity.
      rewrite app_assoc in Htrim.
      exact Htrim.
  Qed.

  Lemma graham_scan_subseq : forall l,
    subseq (graham_scan l) l.
  Proof.
    induction l as [| a l IH]; simpl.
    - constructor.
    - destruct (succ_stack a (graham_scan l)) as [T0 [T' [Hscan HT]]].
      rewrite HT.
      apply subseq_cons.
      eapply subseq_trans.
      + apply subseq_suffix.
      + rewrite <- Hscan.
        exact IH.
  Qed.

  Theorem run_fun_tail_rev_ccw : forall p l,
    sort p l ->
    rev_ccw_list p (rev (run_fun_tail l)).
  Proof.
    intros p l Hsort.
    rewrite rev_run_fun_tail_graham_scan.
    apply sort_gs_ccw_list.
    exact Hsort.
  Qed.

  Theorem run_fun_tail_rev_consec : forall p l,
    sort p l ->
    rev_consec_ccw (rev (run_fun_tail l)).
  Proof.
    intros p l Hsort.
    rewrite rev_run_fun_tail_graham_scan.
    apply (sort_gs_consec_ccw p).
    exact Hsort.
  Qed.

  Lemma rev_ccw_consec_is_convex : forall p T,
    rev_ccw_list p T ->
    rev_consec_ccw T ->
    is_convex p T.
  Proof.
    intros p T.
    induction T as [| p3 T IH]; intros Hccw Hcon; simpl in *; auto.
    destruct T as [| p2 T']; simpl in *; auto.
    destruct T' as [| p1 T'']; simpl in *; auto.
    destruct Hcon as [Hturn Hcon'].
    destruct Hccw as [Hfor Hccw'].
    rewrite Forall_ccw_cons_iff in Hfor.
    destruct Hfor as [Hedge _].
    split.
    - apply ccw_cyclicity_2.
      exact Hturn.
    - split.
      + apply ccw_cyclicity_2.
        exact Hedge.
      + apply IH; assumption.
  Qed.

  Lemma rev_ccw_list_ccw_list_rev : forall p T,
    rev_ccw_list p T ->
    ccw_list p (rev T).
  Proof.
    intros p T.
    induction T using rev_ind; intros Hrev.
    - simpl.
      tauto.
    - rewrite rev_ccw_list_app_iff in Hrev.
      destruct Hrev as [Hrev [_ Hbetween]].
      rewrite rev_app_distr.
      simpl.
      split.
      + rewrite Forall_ccw_forall.
        intros q HIn.
        apply ccw_cyclicity.
        apply Hbetween.
        * apply in_rev.
          exact HIn.
        * simpl.
          tauto.
      + apply IHT.
        exact Hrev.
  Qed.

  Lemma rev_consec_ccw_consec_ccw_rev : forall T,
    rev_consec_ccw T ->
    consec_ccw (rev T).
  Proof.
    induction T using rev_ind; intros Hrev.
    - simpl.
      tauto.
    - rewrite rev_consec_ccw_snoc_iff in Hrev.
      destruct Hrev as [Hrev Hlast].
      replace (rev (T ++ [x])) with (x :: rev T).
      2: {
        rewrite rev_app_distr.
        simpl.
        reflexivity.
      }
      rewrite consec_ccw_cons_iff.
      split.
      + apply IHT.
        exact Hrev.
      + intros b c l0 Heq.
        apply Hlast with (l0 := rev l0).
        apply (f_equal (@rev point)) in Heq.
        rewrite rev_involutive in Heq.
        simpl in Heq.
        rewrite <- app_assoc in Heq.
        exact Heq.
  Qed.

  Lemma ccw_list_forall2_inv : forall p l,
    ccw_list p l ->
    forall l1 q l2 r l3,
      l = l1 ++ q :: l2 ++ r :: l3 ->
      ccw p q r.
  Proof.
    intros p l Hccw.
    induction l as [| a l IH]; intros l1 q l2 r l3 Heq.
    - destruct l1; discriminate Heq.
    - simpl in Hccw.
      destruct Hccw as [Hfor Hccw].
      destruct l1 as [| x l1].
      + simpl in Heq.
        injection Heq as <- Heq.
        rewrite Forall_ccw_forall in Hfor.
        apply Hfor.
        rewrite Heq.
        apply in_or_app.
        right.
        simpl.
        tauto.
      + simpl in Heq.
        injection Heq as <- Heq.
        eapply IH.
        * exact Hccw.
        * exact Heq.
  Qed.

  Lemma ccw_convex_forall3_inv : forall l,
    ccw_convex l ->
    forall l1 q l2 r l3 s l4,
      l = l1 ++ q :: l2 ++ r :: l3 ++ s :: l4 ->
      ccw q r s.
  Proof.
    intros l Hconv.
    induction l as [| a l IH]; intros l1 q l2 r l3 s l4 Heq.
    - destruct l1; discriminate Heq.
    - simpl in Hconv.
      destruct Hconv as [Hccw Hconv].
      destruct l1 as [| x l1].
      + simpl in Heq.
        injection Heq as <- Heq.
        eapply ccw_list_forall2_inv.
        * exact Hccw.
        * exact Heq.
      + simpl in Heq.
        injection Heq as <- Heq.
        eapply IH.
        * exact Hconv.
        * exact Heq.
  Qed.

  Lemma rev_ccw_consec_rev_ccw_convex : forall p T,
    rev_ccw_list p T ->
    rev_consec_ccw T ->
    rev_ccw_convex (p :: T).
  Proof.
    intros p T Hrev Hcon.
    unfold rev_ccw_convex.
    assert (Hccw_rev : ccw_list p (rev T)).
    { apply rev_ccw_list_ccw_list_rev. exact Hrev. }
    assert (Hcon_rev : consec_ccw (rev T)).
    { apply rev_consec_ccw_consec_ccw_rev. exact Hcon. }
    assert (Hconv_rev : ccw_convex (p :: rev T)).
    { apply (ccw_convex_spec_simple p (rev T)).
      - exact Hccw_rev.
      - exact Hcon_rev. }
    assert (Hconv_rot : ccw_convex (rev (p :: T))).
    { simpl.
      apply ccw_convex_rotate1.
      exact Hconv_rev. }
    intros l1 q l2 r l3 s l4 Heq.
    eapply (ccw_convex_forall3_inv (rev (p :: T)) Hconv_rot
              (rev l4) s (rev l3) r (rev l2) q (rev l1)).
    rewrite Heq.
    replace (rev l4 ++ s :: rev l3 ++ r :: rev l2 ++ q :: rev l1)
      with (rev (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)).
    - reflexivity.
    - change (l1 ++ q :: l2 ++ r :: l3 ++ s :: l4)
        with (l1 ++ [q] ++ l2 ++ [r] ++ l3 ++ [s] ++ l4).
      repeat rewrite rev_app_distr.
      simpl.
      repeat rewrite <- app_assoc.
      reflexivity.
  Qed.

  Theorem run_fun_tail_convex : forall p l,
    sort p l ->
    is_convex p (rev (run_fun_tail l)).
  Proof.
    intros p l Hsort.
    apply (rev_ccw_consec_is_convex p).
    - apply run_fun_tail_rev_ccw.
      exact Hsort.
    - apply (run_fun_tail_rev_consec p).
      exact Hsort.
  Qed.

  Lemma run_fun_tail_hull_properties : forall p l,
    sort p l ->
    build_hull_tail l [] tt (run_fun_tail l) /\
    rev_ccw_list p (rev (run_fun_tail l)).
  Proof.
    intros p l Hsort.
    split.
    - apply build_hull_tail_spec.
    - apply run_fun_tail_rev_ccw.
      exact Hsort.
  Qed.

  Theorem run_fun_tail_max_hull : forall p l,
    sort p l ->
    is_max_hull' p (rev (run_fun_tail l)) l.
  Proof.
    intros p l Hsort.
    rewrite rev_run_fun_tail_graham_scan.
    apply graham_convex_2.
    exact Hsort.
  Qed.

  Lemma run_fun_tail_stack_subseq : forall l,
    stack_subseq l (run_fun_tail l).
  Proof.
    intros l.
    unfold stack_subseq.
    rewrite rev_run_fun_tail_graham_scan.
    apply graham_scan_subseq.
  Qed.

  Theorem run_fun_tail_sort : forall p l,
    sort p l ->
    sort p (rev (run_fun_tail l)).
  Proof.
    intros p l Hsort.
    destruct Hsort as [Hleft Hrev].
    split.
    - apply leftmost_subseq with (l2 := l).
      + unfold stack_subseq.
        apply run_fun_tail_stack_subseq.
      + exact Hleft.
    - apply run_fun_tail_rev_ccw.
      split; assumption.
  Qed.

  Theorem run_fun_tail_max_hull_edges : forall p l,
    sort p l ->
    is_max_hull'_edges (p :: rev (run_fun_tail l)) l.
  Proof.
    intros p l Hsort.
    apply is_max_hull'_edges_of_max_hull.
    - apply run_fun_tail_sort.
      exact Hsort.
    - apply (run_fun_tail_rev_consec p).
      exact Hsort.
    - apply run_fun_tail_max_hull.
      exact Hsort.
  Qed.

  Lemma build_hull_tail_stack_subseq : forall l T',
    build_hull_tail l [] tt T' ->
    stack_subseq l T'.
  Proof.
    intros l T' Hrun.
    apply build_hull_tail_unique_run_fun in Hrun.
    subst T'.
    apply run_fun_tail_stack_subseq.
  Qed.

  Theorem build_hull_tail_assert_hull_max : forall p l,
    sort p l ->
    exists T',
      build_hull_tail l [] tt T' /\
      rev_ccw_list p (rev T') /\
      is_max_hull' p (rev T') l.
  Proof.
    intros p l Hsort.
    destruct (run_fun_tail_hull_properties p l Hsort) as [Hbuild Hccw].
    exists (run_fun_tail l).
    repeat split; try exact Hbuild; try exact Hccw.
    apply run_fun_tail_max_hull.
    exact Hsort.
  Qed.

  Theorem build_hull_tail_assert_hull : forall p l,
    sort p l ->
    exists T',
      build_hull_tail l [] tt T' /\
      rev_ccw_list p (rev T').
  Proof.
    intros p l Hsort.
    destruct (run_fun_tail_hull_properties p l Hsort) as [Hbuild Hccw].
    exists (run_fun_tail l).
    split.
    - exact Hbuild.
    - exact Hccw.
  Qed.

  Lemma pop_fun_anchor : forall p a T,
    rev_ccw_list p (a :: T) ->
    pop_fun a (T ++ [p]) = pop_fun a T ++ [p].
  Proof.
    intros p a T Hccw.
    induction T as [| t T IH].
    - simpl.
      reflexivity.
    - destruct T as [| s T'].
      + simpl in *.
        destruct Hccw as [Hfor _].
        apply Forall_ccw_cons_iff in Hfor as [Hat _].
        destruct (ccw_dec p t a) as [Hpta | Hnpta].
        * reflexivity.
        * exfalso.
          apply Hnpta.
          apply ccw_cyclicity.
          exact Hat.
      + simpl in *.
        destruct (ccw_dec s t a) as [Hsta | Hnsta].
        * reflexivity.
        * rewrite IH.
          2: {
            destruct Hccw as [Hfor Htail].
            apply Forall_ccw_cons_iff in Hfor as [_ Has].
            destruct Htail as [_ Htail'].
            split; assumption.
          }
          reflexivity.
  Qed.

  Lemma step_fun_anchor : forall p a T,
    rev_ccw_list p (a :: T) ->
    step_fun a (T ++ [p]) = step_fun a T ++ [p].
  Proof.
    intros p a T Hccw.
    unfold step_fun.
    rewrite pop_fun_anchor; auto.
  Qed.

  Lemma run_tail_with_anchor : forall p l,
    sort p l ->
    run_tail [p] (rev l) = run_tail [] (rev l) ++ [p].
  Proof.
    intros p l Hsort.
    induction l as [| a l IH].
    - simpl.
      reflexivity.
    - simpl.
      rewrite !run_tail_app.
      rewrite (IH (sort_ind p [a] l Hsort)).
      simpl.
      rewrite step_fun_anchor.
      + reflexivity.
      + rewrite run_tail_rev_graham_scan.
        apply sort_gs_ccw_list'.
        exact Hsort.
  Qed.

  Lemma normalize_stack_fun_snoc : forall T p,
    normalize_stack_fun (T ++ [p]) = p :: T.
  Proof.
    intros T p.
    unfold normalize_stack_fun.
    rewrite rev_app_distr.
    simpl.
    rewrite rev_involutive.
    reflexivity.
  Qed.

  Lemma run_fun_eq_graham_scan : forall p l,
    sort p l ->
    run_fun p l = p :: graham_scan l.
  Proof.
    intros p l Hsort.
    unfold run_fun.
    rewrite run_tail_with_anchor by exact Hsort.
    rewrite normalize_stack_fun_snoc.
    rewrite run_tail_rev_graham_scan.
    reflexivity.
  Qed.

  Lemma build_hull_spec : forall p l,
    build_hull p l [] tt (run_fun p l).
  Proof.
    intros p l.
    apply build_hull_exec_steps.
    exists (run_tail [p] (rev l)).
    split.
    - apply (proj1 (prog_list_iter_step_point_exec_steps (rev l) [p] (run_tail [p] (rev l)))).
      apply prog_list_iter_spec.
    - unfold run_fun.
      reflexivity.
  Qed.

  Lemma build_hull_unique_run_fun : forall p l T',
    build_hull p l [] tt T' ->
    T' = run_fun p l.
  Proof.
    intros p l T' Hrun.
    apply build_hull_exec_steps in Hrun.
    destruct Hrun as [Tmid [Hexec ->]].
    apply exec_steps_unique_run_tail in Hexec.
    unfold run_fun.
    now rewrite Hexec.
  Qed.

  Theorem run_fun_convex_hull : forall p l,
    sort p l ->
    is_convex_hull l (run_fun p l).
  Proof.
    intros p l Hsort.
    rewrite run_fun_eq_graham_scan by exact Hsort.
    unfold is_convex_hull.
    split.
    - eapply rev_ccw_consec_rev_ccw_convex.
      + apply sort_gs_ccw_list.
        exact Hsort.
      + apply (sort_gs_consec_ccw p).
        exact Hsort.
    - eapply is_max_hull'_edges_of_max_hull.
      + rewrite <- rev_run_fun_tail_graham_scan.
        apply run_fun_tail_sort.
        exact Hsort.
      + apply (sort_gs_consec_ccw p).
        exact Hsort.
      + apply graham_convex_2.
        exact Hsort.
  Qed.

End GrahamScanRefinement.







Section GrahamScanExample.

  Lemma pop_cond_singleton_break : forall p q,
    pop_cond p [q] (by_break tt) [q].
  Proof.
    intros p q.
    unfold pop_cond.
    unfold get', get, update', update.
    unfold_monad.
    simpl.
    exists [q], [q].
    split; [split; reflexivity | split; reflexivity].
  Qed.

  Lemma pop_cond_double_break : forall p p1 p2,
    ccw p1 p2 p ->
    pop_cond p [p2; p1] (by_break tt) [p2; p1].
  Proof.
    intros p p1 p2 Hccw.
    unfold pop_cond.
    unfold choice, get', get, update', update.
    unfold_monad.
    simpl.
    exists [p2; p1], [p2; p1].
    split.
    - split; reflexivity.
    - left.
      exists tt, [p2; p1].
      split.
      + split; [exact Hccw | reflexivity].
      + split; reflexivity.
  Qed.

  Lemma pop_cond_double_continue : forall p p1 p2,
    ~ ccw p1 p2 p ->
    pop_cond p [p2; p1] (by_continue tt) [p1].
  Proof.
    intros p p1 p2 Hnccw.
    unfold pop_cond.
    unfold choice, get', get, update', update.
    unfold_monad.
    simpl.
    exists [p2; p1], [p2; p1].
    split.
    - split; reflexivity.
    - right.
      exists tt, [p2; p1].
      split.
      + split; [exact Hnccw | reflexivity].
      + exists tt, [p1].
        split; [reflexivity | split; reflexivity].
  Qed.

  Lemma pop_cond_triple_break : forall p1 p2 p3 p4,
    ccw p2 p3 p4 ->
    pop_cond p4 [p3; p2; p1] (by_break tt) [p3; p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hccw.
    unfold pop_cond.
    unfold choice, get', get, update', update.
    unfold_monad.
    simpl.
    exists [p3; p2; p1], [p3; p2; p1].
    split.
    - split; reflexivity.
    - left.
      exists tt, [p3; p2; p1].
      split.
      + split; [exact Hccw | reflexivity].
      + split; reflexivity.
  Qed.

  Lemma pop_cond_triple_continue : forall p1 p2 p3 p4,
    ~ ccw p2 p3 p4 ->
    pop_cond p4 [p3; p2; p1] (by_continue tt) [p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hnccw.
    unfold pop_cond.
    unfold choice, get', get, update', update.
    unfold_monad.
    simpl.
    exists [p3; p2; p1], [p3; p2; p1].
    split.
    - split; reflexivity.
    - right.
      exists tt, [p3; p2; p1].
      split.
      + split; [exact Hnccw | reflexivity].
      + exists tt, [p2; p1].
        split.
        * reflexivity.
        * split; reflexivity.
  Qed.

  Lemma repeat_break_singleton_break : forall p q,
    repeat_break (fun _ : unit => pop_cond p) tt [q] tt [q].
  Proof.
    intros p q.
    pose proof (repeat_break_unfold (fun _ : unit => pop_cond p) tt [q] tt [q]) as Hrb.
    apply Hrb.
    unfold_monad.
    simpl.
    exists (by_break tt), [q].
    split.
    - apply pop_cond_singleton_break.
    - split; reflexivity.
  Qed.

  Lemma repeat_break_double_break : forall p p1 p2,
    ccw p1 p2 p ->
    repeat_break (fun _ : unit => pop_cond p) tt [p2; p1] tt [p2; p1].
  Proof.
    intros p p1 p2 Hccw.
    pose proof (repeat_break_unfold (fun _ : unit => pop_cond p) tt [p2; p1] tt [p2; p1]) as Hrb.
    apply Hrb.
    unfold_monad.
    simpl.
    exists (by_break tt), [p2; p1].
    split.
    - apply pop_cond_double_break; exact Hccw.
    - split; reflexivity.
  Qed.

  Lemma repeat_break_triple_break : forall p1 p2 p3 p4,
    ccw p2 p3 p4 ->
    repeat_break (fun _ : unit => pop_cond p4) tt [p3; p2; p1] tt [p3; p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hccw.
    pose proof (repeat_break_unfold (fun _ : unit => pop_cond p4) tt [p3; p2; p1] tt [p3; p2; p1]) as Hrb.
    apply Hrb.
    unfold_monad.
    simpl.
    exists (by_break tt), [p3; p2; p1].
    split.
    - apply pop_cond_triple_break; assumption.
    - split; reflexivity.
  Qed.

  Lemma repeat_break_triple_pop_once : forall p1 p2 p3 p4,
    ~ ccw p2 p3 p4 ->
    ccw p1 p2 p4 ->
    repeat_break (fun _ : unit => pop_cond p4) tt [p3; p2; p1] tt [p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hnccw Hccw.
    pose proof (repeat_break_unfold (fun _ : unit => pop_cond p4) tt [p3; p2; p1] tt [p2; p1]) as Hrb.
    apply Hrb.
    unfold_monad.
    simpl.
    exists (by_continue tt), [p2; p1].
    split.
    - apply pop_cond_triple_continue; assumption.
    - apply repeat_break_double_break; assumption.
  Qed.

  Lemma get_update_push : forall (p : point) (T : list point),
    (T0 <- get' id;; update' (fun _ => p :: T0)) T tt (p :: T).
  Proof.
    intros p T.
    unfold get', get, update', update.
    unfold_monad.
    simpl.
    exists T, T.
    split.
    - split; reflexivity.
    - reflexivity.
  Qed.

  Lemma step_point_of_repeat : forall p T T',
    repeat_break (fun _ : unit => pop_cond p) tt T tt T' ->
    step_point p T tt (p :: T').
  Proof.
    intros p T T' Hrep.
    unfold step_point.
    unfold_monad.
    simpl.
    exists tt, T'.
    split.
    - exact Hrep.
    - apply get_update_push.
  Qed.

  Lemma step_point_singleton : forall p q,
    step_point p [q] tt [p; q].
  Proof.
    intros p q.
    apply step_point_of_repeat.
    apply repeat_break_singleton_break.
  Qed.

  Lemma step_point_two_no_pop : forall p p1 p2,
    ccw p1 p2 p ->
    step_point p [p2; p1] tt [p; p2; p1].
  Proof.
    intros p p1 p2 Hccw.
    apply step_point_of_repeat.
    apply repeat_break_double_break.
    exact Hccw.
  Qed.

  Lemma step_point_three_break_now : forall p1 p2 p3 p4,
    ccw p2 p3 p4 ->
    step_point p4 [p3; p2; p1] tt [p4; p3; p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hccw.
    apply step_point_of_repeat.
    apply repeat_break_triple_break; assumption.
  Qed.

  Lemma step_point_three_pop_once : forall p1 p2 p3 p4,
    ~ ccw p2 p3 p4 ->
    ccw p1 p2 p4 ->
    step_point p4 [p3; p2; p1] tt [p4; p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hnccw Hccw.
    apply step_point_of_repeat.
    apply repeat_break_triple_pop_once; assumption.
  Qed.

End GrahamScanExample.


Lemma build_hull_tail_hoare_subseq : forall l,
  Hoare (fun T0 => T0 = [])
        (build_hull_tail l)
        (fun _ T' => stack_subseq l T').
Proof.
  intros l s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  eapply build_hull_tail_stack_subseq. exact Hrun.
Qed.

Lemma build_hull_tail_hoare_ccw : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull_tail l)
        (fun _ T' => rev_ccw_list p (rev T')).
Proof.
  intros p l Hsort s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  assert (Heq : s2 = run_fun_tail l).
  { eapply build_hull_tail_unique_run_fun. exact Hrun. }
  subst s2.
  apply run_fun_tail_rev_ccw. exact Hsort.
Qed.

Lemma build_hull_tail_hoare_max : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull_tail l)
        (fun _ T' => is_max_hull' p (rev T') l).
Proof.
  intros p l Hsort s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  assert (Heq : s2 = run_fun_tail l).
  { eapply build_hull_tail_unique_run_fun. exact Hrun. }
  subst s2.
  apply run_fun_tail_max_hull.
  exact Hsort.
Qed.

Lemma build_hull_tail_hoare_max_edges : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull_tail l)
        (fun _ T' => is_max_hull'_edges (p :: rev T') l).
Proof.
  intros p l Hsort s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  assert (Heq : s2 = run_fun_tail l).
  { eapply build_hull_tail_unique_run_fun. exact Hrun. }
  subst s2.
  apply run_fun_tail_max_hull_edges.
  exact Hsort.
Qed.

Lemma build_hull_tail_hoare_consec : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull_tail l)
        (fun _ T' => rev_consec_ccw (rev T')).
Proof.
  intros p l Hsort s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  assert (Heq : s2 = run_fun_tail l).
  { eapply build_hull_tail_unique_run_fun. exact Hrun. }
  subst s2.
  apply (run_fun_tail_rev_consec p).
  exact Hsort.
Qed.

Lemma build_hull_tail_hoare_convex : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull_tail l)
        (fun _ T' => is_convex p (rev T')).
Proof.
  intros p l Hsort s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  assert (Heq : s2 = run_fun_tail l).
  { eapply build_hull_tail_unique_run_fun. exact Hrun. }
  subst s2.
  apply run_fun_tail_convex.
  exact Hsort.
Qed.

Theorem build_hull_hoare_final : forall p l,
  sort p l ->
  Hoare (fun T0 => T0 = [])
        (build_hull p l)
        (fun _ T' => is_convex_hull l T').
Proof.
  intros p l Hsort s1 x s2 Hpre Hrun.
  subst s1. destruct x.
  assert (Heq : s2 = run_fun p l).
  { eapply build_hull_unique_run_fun. exact Hrun. }
  subst s2.
  apply run_fun_convex_hull.
  exact Hsort.
Qed.
