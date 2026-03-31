(* COQ-HEAD *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List.
From ConvexHull Require Import Record_Geo_Vec Record_Geo_Point Graham_Scan.
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
  Definition build_hull_init (l : list point) : program (list point) unit :=
    match l with
    | nil => skip
    | p :: _ => update' (fun _ => [p])
    end.

  (** Assume that l is sorted *)
  Definition build_hull_next (l : list point) : program (list point) unit :=
    (** iterate from tail since build_hull_init has inserted the head *)
    match l with
    | _ :: l' => prog_list_iter step_point' l' tt
    | nil => skip
    end.

  Definition build_hull (l : list point) : program (list point) unit :=
    build_hull_init l ;;
    build_hull_next l.

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
      match l with
      | [] => T = T'
      | _ :: l' => exec_steps l' T T'
      end.
  Proof.
    intros l T T'.
    unfold build_hull_next.
    destruct l as [| p l']; simpl.
    - split.
      + intros H.
        unfold ret, StateRelMonad.ret in H.
        simpl in H.
        destruct H as [_ Heq].
        exact Heq.
      + intros H.
        unfold ret, StateRelMonad.ret.
        simpl. split; [reflexivity | exact H].
    - apply prog_list_iter_step_point_exec_steps.
  Qed.

  Lemma build_hull_exec_steps :
    forall l T',
      build_hull l [] tt T' <->
      match l with
      | [] => T' = []
      | p1 :: l' => exec_steps l' [p1] T'
      end.
  Proof.
    intros l T'.
    unfold build_hull, build_hull_init.
    destruct l as [| p1 l']; simpl.
    - split.
      + intros H.
        unfold bind, StateRelMonad.bind in H.
        simpl in H.
        destruct H as [u [T1 [Hret Hnext]]].
        destruct u.
        unfold ret, StateRelMonad.ret in Hret.
        simpl in Hret.
        destruct Hret as [_ Heq].
        subst T1.
        unfold ret, StateRelMonad.ret in Hnext.
        simpl in Hnext.
        destruct Hnext as [_ Heq].
        subst T'.
        reflexivity.
      + intros H.
        subst T'.
        unfold bind, StateRelMonad.bind.
        simpl.
        exists tt, [].
        split.
        * unfold ret, StateRelMonad.ret. simpl. split; reflexivity.
        * unfold ret, StateRelMonad.ret. simpl. split; reflexivity.
    - split.
      + intros H.
        unfold bind, StateRelMonad.bind in H.
        simpl in H.
        destruct H as [u [T1 [Hinit Hnext]]].
        destruct u.
        unfold update', update in Hinit.
        simpl in Hinit.
        sets_unfold in Hinit.
        subst T1.
        apply (build_hull_next_exec_steps (p1 :: l') [p1] T').
        exact Hnext.
      + intros H.
        unfold bind, StateRelMonad.bind.
        simpl.
        exists tt, [p1].
        split.
        * unfold update', update. simpl. sets_unfold. reflexivity.
        * apply (build_hull_next_exec_steps (p1 :: l') [p1] T').
          exact H.
  Qed.

End GrahamScanExecution.


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
    unfold Hoare.
    intros s1 x s2 Hpre Hrun.
    eapply (pop_cond_preserve_subset base p s1 x s2); eauto.
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
      unfold Hoare.
      intros s1 x s2 Hpre Hpc.
      destruct x as [a0 | b0]; simpl.
      - exact (pop_cond_preserve_subset base p s1 (by_continue a0) s2 Hpre Hpc).
      - exact (pop_cond_preserve_subset base p s1 (by_break b0) s2 Hpre Hpc).
    }
    pose proof (Hoare_repeat_break
                  (Σ := list point) (A := unit) (B := unit)
                  (fun _ : unit => pop_cond p)
                  (fun _ T0 => stack_subset base T0)
                  (fun _ T0 => stack_subset base T0)
                  Hbody
                  tt) as Hrb.
    unfold Hoare in Hrb.
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

  Lemma build_hull_subset : forall l T',
    build_hull l [] tt T' ->
    stack_subset l T'.
  Proof.
    intros l T' Hrun.
    apply build_hull_exec_steps in Hrun.
    destruct l as [| p1 l'].
    - subst T'.
      intros q Hinq.
      inversion Hinq.
    - assert (Hbase : stack_subset [p1] [p1]).
      {
        intros q Hinq.
        simpl in Hinq.
        destruct Hinq as [Heq | Hfalse].
        + left. exact Heq.
        + inversion Hfalse.
      }
      pose proof (exec_steps_preserve_subset l' [p1] [p1] T' Hrun Hbase) as Hsub'.
      intros q Hinq.
      specialize (Hsub' q Hinq).
      apply in_app_iff in Hsub' as [Hinl' | Hin1].
      + right. exact Hinl'.
      + simpl in Hin1.
        destruct Hin1 as [Heq | Hfalse].
        * left. exact Heq.
        * inversion Hfalse.
  Qed.

End GrahamScanInvariant.

Section GrahamScanRefinement.

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

  Definition run_fun (l : list point) : list point :=
    match l with
    | [] => []
    | p1 :: l' => run_tail [p1] l'
    end.

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

  Lemma build_hull_spec : forall l,
    build_hull l  [] tt (run_fun l).
  Proof.
    intros l.
    unfold run_fun.
    destruct l as [| p1 l']; simpl.
    - unfold build_hull, build_hull_init, build_hull_next.
      unfold bind, StateRelMonad.bind.
      simpl.
      exists tt, [].
      split.
      + unfold ret, StateRelMonad.ret.
        simpl.
        split; reflexivity.
      + unfold ret, StateRelMonad.ret.
        simpl.
        split; reflexivity.
    - unfold build_hull, build_hull_init, build_hull_next.
      unfold bind, StateRelMonad.bind.
      simpl.
      exists tt, [p1].
      split.
      + unfold update', update.
        simpl.
        sets_unfold.
        reflexivity.
      + apply prog_list_iter_spec.
  Qed.

  Lemma run_fun_subset : forall l,
    stack_subset l (run_fun l).
  Proof.
    intros l.
    apply build_hull_subset.
    apply build_hull_spec.
  Qed.

  Lemma run_fun_nonempty : forall p l,
    run_fun (p :: l) <> [].
  Proof.
    intros p l Heq.
    assert (Hrun : build_hull (p :: l) [] tt (run_fun (p :: l))).
    { apply build_hull_spec. }
    apply build_hull_exec_steps in Hrun.
    simpl in Hrun.
    eapply exec_steps_nonempty.
    - exact Hrun.
    - discriminate.
    - exact Heq.
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

  Theorem run_fun_rev_ccw : forall p l,
    sort p l ->
    rev_ccw_list p (rev (run_fun l)).
  Proof.
    intros p l Hsort.
    destruct Hsort as [_ Hrev].
    destruct l as [| a l']; simpl.
    - exact I.
    - apply (run_tail_rev_ccw p l' [a]).
      simpl.
      exact Hrev.
  Qed.

  Theorem run_fun_rev_consec : forall l,
    rev_consec_ccw (run_fun l).
  Proof.
    intros l.
    unfold run_fun.
    destruct l as [| a l']; simpl.
    - tauto.
    - apply run_tail_rev_consec.
      simpl.
      tauto.
  Qed.

  Lemma run_fun_hull_properties : forall p l,
    sort p l ->
    build_hull l [] tt (run_fun l) /\
    rev_ccw_list p (rev (run_fun l)) /\
    rev_consec_ccw (run_fun l).
  Proof.
    intros p l Hsort.
    split.
    - apply build_hull_spec.
    - split.
      + apply run_fun_rev_ccw.
        exact Hsort.
      + apply run_fun_rev_consec.
  Qed.

  Theorem build_hull_assert_hull : forall p l,
    sort p l ->
    exists T',
      build_hull l [] tt T' /\
      rev_ccw_list p (rev T').
  Proof.
    intros p l Hsort.
    destruct (run_fun_hull_properties p l Hsort) as [Hbuild [Hccw _]].
    exists (run_fun l).
    split.
    - exact Hbuild.
    - exact Hccw.
  Qed.

  Theorem build_hull_assert_hull_convex : forall p l,
    sort p l ->
    exists T',
      build_hull l [] tt T' /\
      rev_ccw_list p (rev T') /\
      rev_consec_ccw T'.
  Proof.
    intros p l Hsort.
    destruct (run_fun_hull_properties p l Hsort) as [Hbuild [Hccw Hcon]].
    exists (run_fun l).
    split.
    - exact Hbuild.
    - split.
      + exact Hccw.
      + exact Hcon.
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

  Example build_hull_3_points_no_pop :
    forall p1 p2 p3,
    ccw p1 p2 p3 ->
    build_hull [p1; p2; p3] [] tt [p3; p2; p1].
  Proof.
    intros p1 p2 p3 Hccw.
    unfold build_hull, build_hull_init, build_hull_next, step_point, step_point'.
    simpl.
    unfold_monad.
    simpl.
    exists tt, [p1].
    split.
    - reflexivity.
    - exists tt, [p2; p1].
      split.
      + apply step_point_singleton.
      + exists tt, [p3; p2; p1].
        split.
        * apply step_point_two_no_pop.
          exact Hccw.
        * split; reflexivity.
  Qed.

  Example build_hull_4_points_left_turn :
    forall p1 p2 p3 p4,
    sort p1 [p2; p3; p4] ->
    ccw p1 p2 p3 ->
    ccw p2 p3 p4 ->
    build_hull [p1; p2; p3; p4] [] tt [p4; p3; p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hsort Hccw12 Hccw.
    unfold build_hull, build_hull_init, build_hull_next, step_point, step_point'.
    simpl.
    unfold_monad.
    simpl.
    exists tt, [p1].
    split.
    - reflexivity.
    - exists tt, [p2; p1].
      split.
      + apply step_point_singleton.
      + exists tt, [p3; p2; p1].
        split.
        * apply step_point_two_no_pop.
          exact Hccw12.
        * exists tt, [p4; p3; p2; p1].
          split.
          -- apply step_point_three_break_now.
             exact Hccw.
          -- split; reflexivity.
  Qed.

  Example build_hull_4_points_pop_once :
    forall p1 p2 p3 p4,
    sort p1 [p2; p3; p4] ->
    ccw p1 p2 p3 ->
    ~ ccw p2 p3 p4 ->
    ccw p1 p2 p4 ->
    build_hull [p1; p2; p3; p4] [] tt [p4; p2; p1].
  Proof.
    intros p1 p2 p3 p4 Hsort Hccw12 Hnccw Hccw14.
    unfold build_hull, build_hull_init, build_hull_next, step_point, step_point'.
    simpl.
    unfold_monad.
    simpl.
    exists tt, [p1].
    split.
    - reflexivity.
    - exists tt, [p2; p1].
      split.
      + apply step_point_singleton.
      + exists tt, [p3; p2; p1].
        split.
        * apply step_point_two_no_pop.
          exact Hccw12.
        * exists tt, [p4; p2; p1].
          split.
          -- apply step_point_three_pop_once; [exact Hnccw | exact Hccw14].
          -- split; reflexivity.
  Qed.


End GrahamScanExample.
