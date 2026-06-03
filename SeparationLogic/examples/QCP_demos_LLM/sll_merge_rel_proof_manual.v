Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sll_lib.
From SimpleC.EE.QCP_demos_LLM Require Import sll_merge_rel_lib.
Local Open Scope monad.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof.
  pre_process.
  Exists s1. Exists s2. Exists (@nil Z).
  repeat (split_pure_spatial || split_pures).
  + cancel (sll x_pre s1).
    cancel (sll y_pre s2).
    cancel (((&( "ret" ))) # Ptr |->_).
    simpl.
    split_pure_spatial.
    - cancel.
    - dump_pre_spatial. reflexivity.
  + dump_pre_spatial.
    unfold merge_rel, merge_from_mid_rel.
    exact H.
Qed.

Lemma proof_of_merge_entail_wit_2 : merge_entail_wit_2.
Proof.
  pre_process.
  sep_apply_l_atomic (sll_not_zero x l1_2).
  * dump_pre_spatial. exact H0.
  * Intros x_next. Intros x_data. Intros l1_new.
    sep_apply_l_atomic (sll_not_zero y l2_2).
    - dump_pre_spatial. exact H.
    - Intros y_next. Intros y_data. Intros l2_new.
      Exists y_next. Exists x_next. Exists y_data. Exists l2_new.
      Exists x_data. Exists l1_new. Exists l1_2. Exists l2_2. Exists l3_2.
      repeat (split_pure_spatial || split_pures).
      + cancel (&((x) # "list" ->ₛ "data") # Int |-> x_data).
        cancel (&((y) # "list" ->ₛ "data") # Int |-> y_data).
        cancel (&((x) # "list" ->ₛ "next") # Ptr |-> x_next).
        cancel (sll x_next l1_new).
        cancel (&((y) # "list" ->ₛ "next") # Ptr |-> y_next).
        cancel (sll y_next l2_new).
        cancel (t # Ptr |->_).
        cancel (sllbseg (&( "ret")) t l3_2).
      + dump_pre_spatial. exact H1.
      + dump_pre_spatial. exact H0.
      + dump_pre_spatial. exact H.
      + dump_pre_spatial. exact H2.
      + dump_pre_spatial. exact H3.
Qed.

Lemma proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Proof.
  pre_process.
  Exists l1_new. Exists (y_data :: l2_new). Exists (l3_2 ++ (x_data :: nil))%list.
  simpl sll. Exists y_next.
  repeat (split_pure_spatial || split_pures).
  + cancel (&((y) # "list" ->ₛ "data") # Int |-> y_data).
    cancel (&((y) # "list" ->ₛ "next") # Ptr |-> y_next).
    cancel (sll y_next l2_new).
    cancel (sll x_next l1_new).
    sep_apply_l_atomic (sllbseg_len1 t x x_data).
    * dump_pre_spatial. exact H1.
    * sep_apply_l_atomic (store_ptr_undef_store_ptr (&((x) # "list" ->ₛ "next")) x_next).
      cancel (&((x) # "list" ->ₛ "next") # Ptr |->_).
      sep_apply_l_atomic (sllbseg_sllbseg (&( "ret")) t (&((x) # "list" ->ₛ "next")) l3_2 (x_data :: nil)).
      cancel (sllbseg (&( "ret")) (&((x) # "list" ->ₛ "next")) (l3_2 ++ (x_data :: nil))%list).
  + dump_pre_spatial.
    rewrite H3 in H0.
    rewrite H4 in H0.
    unfold merge_from_mid_rel in H0 at 1.
    prog_nf in H0.
    unfold_loop in H0.
    prog_nf in H0.
    unfold merge_body in H0 at 1.
    prog_nf in H0.
    safe_choice_l H0; try lia.
    exact H0.
  + dump_pre_spatial. exact H2.
Qed.

Lemma proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Proof.
  pre_process.
  Exists (x_data :: l1_new). Exists l2_new. Exists (l3_2 ++ (y_data :: nil))%list.
  simpl sll. Exists x_next.
  repeat (split_pure_spatial || split_pures).
  + cancel (&((x) # "list" ->ₛ "data") # Int |-> x_data).
    cancel (&((x) # "list" ->ₛ "next") # Ptr |-> x_next).
    cancel (sll x_next l1_new).
    cancel (sll y_next l2_new).
    sep_apply_l_atomic (sllbseg_len1 t y y_data).
    * dump_pre_spatial. exact H2.
    * sep_apply_l_atomic (store_ptr_undef_store_ptr (&((y) # "list" ->ₛ "next")) y_next).
      cancel (&((y) # "list" ->ₛ "next") # Ptr |->_).
      sep_apply_l_atomic (sllbseg_sllbseg (&( "ret")) t (&((y) # "list" ->ₛ "next")) l3_2 (y_data :: nil)).
      cancel (sllbseg (&( "ret")) (&((y) # "list" ->ₛ "next")) (l3_2 ++ (y_data :: nil))%list).
  + dump_pre_spatial.
    rewrite H3 in H0.
    rewrite H4 in H0.
    unfold merge_from_mid_rel in H0 at 1.
    prog_nf in H0.
    unfold_loop in H0.
    prog_nf in H0.
    unfold merge_body in H0 at 1.
    prog_nf in H0.
    safe_choice_r H0; try lia.
    exact H0.
  + dump_pre_spatial. exact H1.
Qed.

Lemma proof_of_merge_entail_wit_4_1 : merge_entail_wit_4_1.
Proof.
  pre_process.
  subst x.
  sep_apply_l_atomic (sll_zero 0 l1).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hl1nil.
    subst l1.
    sep_apply_l_atomic (sllbseg_2_sllseg (&( "ret")) t y l3).
    Intros ret.
    Exists ret. Exists (l3 ++ l2).
    repeat (split_pure_spatial || split_pures).
    + cancel (&( "ret") # Ptr |-> ret).
      sep_apply_l_atomic (sllseg_sll ret y l3 l2).
      cancel (sll ret (l3 ++ l2)).
    + dump_pre_spatial.
      unfold merge_from_mid_rel in H0 at 1.
      prog_nf in H0.
      unfold_loop in H0.
      prog_nf in H0.
      unfold merge_body in H0 at 1.
      prog_nf in H0.
      exact H0.
Qed.

Lemma proof_of_merge_entail_wit_4_2 : merge_entail_wit_4_2.
Proof.
  pre_process.
  subst y.
  sep_apply_l_atomic (sll_zero 0 l2).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hl2nil.
    subst l2.
    sep_apply_l_atomic (sllbseg_2_sllseg (&( "ret")) t x l3).
    Intros ret.
    Exists ret. Exists (l3 ++ l1).
    repeat (split_pure_spatial || split_pures).
    + cancel (&( "ret") # Ptr |-> ret).
      sep_apply_l_atomic (sllseg_sll ret x l3 l1).
      cancel (sll ret (l3 ++ l1)).
    + dump_pre_spatial.
      unfold merge_from_mid_rel in H1 at 1.
      prog_nf in H1.
      unfold_loop in H1.
      prog_nf in H1.
      unfold merge_body in H1 at 1.
      destruct l1 as [|h tl]; prog_nf in H1; exact H1.
Qed.

Lemma proof_of_merge_return_wit_1_manual : merge_return_wit_1.
Proof.
  pre_process.
  Exists s3_2.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll ret s3_2).
  + dump_pre_spatial. exact H.
Qed.

Lemma proof_of_split_rec_return_wit_2 : split_rec_return_wit_2.
Proof.
  pre_process.
  Exists p_callee_v. Exists q_callee_v. Exists s2_2. Exists s1_2.
  repeat (split_pure_spatial || split_pures).
  + cancel ((q_pre) # Ptr |-> p_callee_v).
    cancel (sll p_callee_v s1_2).
    cancel ((p_pre) # Ptr |-> q_callee_v).
    cancel (sll q_callee_v s2_2).
  + dump_pre_spatial.
    unfold reversepair, applyf.
    exact H.
Qed.

Lemma proof_of_split_rec_return_wit_1 : split_rec_return_wit_1.
Proof.
  pre_process.
  subst x_pre.
  sep_apply_l_atomic (sll_zero 0 l_low_level_spec).
  * dump_pre_spatial. reflexivity.
  * Intros_p Hlnil.
    subst l_low_level_spec.
    Exists q_pre_v_2. Exists p_pre_v_2. Exists l1_low_level_spec. Exists l2_low_level_spec.
    repeat (split_pure_spatial || split_pures).
    + cancel ((p_pre) # Ptr |-> p_pre_v_2).
      cancel (sll p_pre_v_2 l1_low_level_spec).
      cancel ((q_pre) # Ptr |-> q_pre_v_2).
      cancel (sll q_pre_v_2 l2_low_level_spec).
    + dump_pre_spatial.
      unfold split_rec_rel in H0.
      rewrite (split_rec_rel_unfold (nil, l1_low_level_spec, l2_low_level_spec)) in H0.
      simpl in H0.
      exact H0.
Qed.

Lemma proof_of_split_rec_entail_wit_2 : split_rec_entail_wit_2.
Proof.
  pre_process.
  Exists q_v_2. Exists x_pre. Exists l_new_2. Exists x_data_2.
  repeat (split_pure_spatial || split_pures).
  + cancel ((q_pre) # Ptr |-> q_v_2).
    cancel (sll q_v_2 l2_low_level_spec).
    cancel (sll x_next l_new_2).
    cancel ((p_pre) # Ptr |-> x_pre).
    simpl sll.
    Exists p_v_2.
    split_pure_spatial.
    - cancel (&((x_pre) # "list" ->ₛ "data") # Int |-> x_data_2).
      cancel (&((x_pre) # "list" ->ₛ "next") # Ptr |-> p_v_2).
      cancel (sll p_v_2 l1_low_level_spec).
    - dump_pre_spatial. exact H.
  + dump_pre_spatial. exact H.
  + dump_pre_spatial.
    rewrite H1 in H0.
    unfold split_rec_rel in H0.
    rewrite (split_rec_rel_unfold (x_data_2 :: l_new_2, l1_low_level_spec, l2_low_level_spec)) in H0.
    simpl in H0.
    exact H0.
  + dump_pre_spatial. exact H1.
Qed.

Lemma proof_of_split_rec_partial_solve_wit_1_pure_manual : split_rec_partial_solve_wit_1_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort_partial_solve_wit_1_pure : merge_sort_partial_solve_wit_1_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort_entail_wit_3 : merge_sort_entail_wit_3.
Proof.
  pre_process.
  subst p. subst q.
  simpl sll.
  repeat (split_pure_spatial || split_pures).
  + Intros_p Hp0. Intros_p Hq0. cancel.
  + dump_pre_spatial.
    unfold mergesortrec in H1 at 1.
    erewrite (program_para_equiv (mergesortrec_unfold)) in H1.
    unfold mergesortrec_f, mergesortrec_loc0 in H1.
    exact H1.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
  + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_merge_sort_entail_wit_4 : merge_sort_entail_wit_4.
Proof.
  pre_process.
  sep_apply_l_atomic (sll_not_zero q_callee_v s2).
  - dump_pre_spatial. exact H.
  - Intros q_next. Intros h. Intros t.
    Exists s1. Exists (h :: t).
    repeat (split_pure_spatial || split_pures).
    + cancel (sll p_callee_v s1).
      simpl.
      Exists q_next.
      repeat (split_pure_spatial || split_pures).
      * cancel (&(q_callee_v # "list" ->ₛ "data") # Int |-> h).
        cancel (&(q_callee_v # "list" ->ₛ "next") # Ptr |-> q_next).
        cancel (sll q_next t).
      * dump_pre_spatial. exact H.
    + dump_pre_spatial.
      unfold applyf, maketuple, mergesortrec_loc0 in H0.
      rewrite H5 in H0.
      simpl in H0. exact H0.
    + dump_pre_spatial. exact H.
    + dump_pre_spatial. exact H1.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H2.
    + dump_pre_spatial. exact H1.
Qed.

Lemma proof_of_merge_sort_entail_wit_5 : merge_sort_entail_wit_5.
Proof.
  pre_process.
  Exists l2_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0).
    cancel (sll q_callee_v l2_2).
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc1 in H.
    unfold mergesortrec_loc2.
    exact H.
  + dump_pre_spatial. exact H0.
  + dump_pre_spatial. exact H1.
  + dump_pre_spatial. exact H2.
  + dump_pre_spatial. exact H2.
  + dump_pre_spatial. exact H1.
Qed.

Lemma proof_of_merge_sort_entail_wit_6 : merge_sort_entail_wit_6.
Proof.
  pre_process.
  Exists l1_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval_2 l0).
    cancel (sll retval l1_2).
  + dump_pre_spatial.
    unfold applyf in H at 1.
    unfold mergesortrec_loc2 in H at 1.
    prog_nf in H.
    exact H.
  + dump_pre_spatial. exact H0.
  + dump_pre_spatial. exact H1.
  + dump_pre_spatial. exact H2.
  + dump_pre_spatial. exact H2.
  + dump_pre_spatial. exact H1.
Qed.

Lemma proof_of_merge_sort_return_wit_2 : merge_sort_return_wit_2.
Proof.
  pre_process.
  sep_apply_l_atomic (sll_zero q_callee_v s2).
  * dump_pre_spatial. rewrite H. reflexivity.
  * Intros_p Hs2nil.
    subst s2.
    Exists s1.
    repeat (split_pure_spatial || split_pures).
    + cancel (sll p_callee_v s1).
    + dump_pre_spatial.
      unfold applyf, maketuple, mergesortrec_loc0.
      simpl.
      exact H0.
Qed.

Lemma proof_of_merge_sort_partial_solve_wit_3_pure_manual : merge_sort_partial_solve_wit_3_pure.
Proof.
  pre_process.
Qed.


Lemma proof_of_merge_sort3_entail_wit_1 : merge_sort3_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (sll_zero 0 nil).
  + dump_pre_spatial. reflexivity.
  + Intros_p Hnil.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll x_pre l_low_level_spec).
    - dump_pre_spatial.
      rewrite (gmergesortrec_unfold l_low_level_spec) in H2.
      unfold gmergesortrec_f in H2.
      apply safeExec_choice_r in H2.
      unfold seq in H2.
      rewrite (split_rel_refine_ext_split l_low_level_spec).
      prove_by_one_abs_step tt.
      abs_test_step.
      lia.
    - dump_pre_spatial. exact H.
    - dump_pre_spatial. exact H0.
    - dump_pre_spatial. exact H1.
Qed.

Lemma proof_of_merge_sort3_entail_wit_2 : merge_sort3_entail_wit_2.
Proof.
  pre_process.
  Exists s1. Exists s2.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll p_callee_v s1).
    cancel (sll q_callee_v s2).
  + dump_pre_spatial.
    unfold applyf in H at 1.
    unfold maketuple in H at 1.
    unfold gmergesortrec_loc0 in H at 1.
    prog_nf in H.
    exact H.
  + dump_pre_spatial. exact H0.
  + dump_pre_spatial. exact H1.
  + dump_pre_spatial. exact H2.
Qed.

Lemma proof_of_merge_sort3_entail_wit_3 : merge_sort3_entail_wit_3.
Proof.
  pre_process.
  Exists l2_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval_2 l0).
    cancel (sll q_callee_v l2_2).
  + dump_pre_spatial.
    unfold applyf, gmergesortrec_loc1.
    exact H.
  + dump_pre_spatial. exact H0.
  + dump_pre_spatial. exact H1.
  + dump_pre_spatial. exact H2.
Qed.

Lemma proof_of_merge_sort3_entail_wit_4 : merge_sort3_entail_wit_4.
Proof.
  pre_process.
  Exists l1_2. Exists l0.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval_3 l0).
    cancel (sll retval_2 l1_2).
  + dump_pre_spatial.
    unfold applyf, mergesortrec_loc2.
    exact H.
  + dump_pre_spatial. exact H0.
  + dump_pre_spatial. exact H1.
  + dump_pre_spatial. exact H2.
Qed.

Lemma proof_of_merge_sort3_return_wit_2 : merge_sort3_return_wit_2.
Proof.
  pre_process.
  Exists l0_2.
  repeat (split_pure_spatial || split_pures).
  + cancel (sll retval l0_2).
  + dump_pre_spatial.
    rewrite (gmergesortrec_unfold l_low_level_spec) in H4.
    unfold gmergesortrec_f in H4.
    apply safeExec_choice_l in H4.
    eapply (safeExec_prorefine (ext_sort l_low_level_spec) (return l0_2)).
    - unfold StateRelMonad.ret, ext_sort.
      sets_unfold.
      intros s a s' [Ha Hs].
      subst.
      split; assumption.
    - exact H4.
Qed.

Lemma proof_of_merge_sort3_partial_solve_wit_5_pure : merge_sort3_partial_solve_wit_5_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort3_partial_solve_wit_6_pure : merge_sort3_partial_solve_wit_6_pure.
Proof.
  pre_process.
Qed.

Lemma proof_of_merge_sort3_derive_low_level_spec_aux_by_low_level_spec : merge_sort3_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  apply safeExec_bind in H0 as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux.
  Exists X_low_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply (Hsafe_cont ATrue l0_2).
      exact H0.
  + repeat (split_pure_spatial || split_pures).
    - dump_pre_spatial. exact H.
    - dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_merge_sort3_derive_high_level_spec_by_low_level_spec : merge_sort3_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l_high_level_spec.
  Exists (fun l0 _ => Permutation l_high_level_spec l0 /\ incr l0).
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply safeExec_ret in H0 as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj1 Hret).
    - dump_pre_spatial.
      apply safeExec_ret in H0 as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj2 Hret).
  + repeat (split_pure_spatial || split_pures).
    - dump_pre_spatial. exact H.
    - dump_pre_spatial.
      eapply safeExec_X_subset.
      * apply Hoare_result_state.
        apply functional_correctness_gmergesort.
      * apply safeExec_result_state.
        exists tt. exact I.
Qed.

Lemma proof_of_merge_sort2_derive_low_level_spec_aux_by_low_level_spec : merge_sort2_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux.
  Exists X_low_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply (Hsafe_cont ATrue l0_2).
      exact H.
  + dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_merge_sort2_derive_high_level_spec_by_low_level_spec : merge_sort2_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l_high_level_spec.
  Exists (fun l0 _ => Permutation l_high_level_spec l0 /\ incr l0).
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj1 Hret).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj2 Hret).
  + dump_pre_spatial.
    eapply safeExec_X_subset.
    - apply Hoare_result_state.
      apply functional_correctness_gmergesort.
    - apply safeExec_result_state.
      exists tt. exact I.
Qed.

Lemma proof_of_merge_sort_derive_low_level_spec_aux_by_low_level_spec : merge_sort_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux.
  Exists X_low_level_spec.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply (Hsafe_cont ATrue l0_2).
      exact H.
  + dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_merge_sort_derive_high_level_spec_by_low_level_spec : merge_sort_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Exists l_high_level_spec.
  Exists (fun l0 _ => Permutation l_high_level_spec l0 /\ incr l0).
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    apply derivable1_wand_sepcon_adjoint.
    Intros l0_2. Intros retval_2.
    Exists l0_2. Exists retval_2.
    repeat (split_pure_spatial || split_pures).
    - cancel (sll retval_2 l0_2).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj1 Hret).
    - dump_pre_spatial.
      apply safeExec_ret in H as (? & _ & Hret).
      sets_unfold in Hret.
      exact (proj2 Hret).
  + dump_pre_spatial.
    eapply safeExec_X_subset.
    - apply Hoare_result_state.
      apply functional_correctness_mergesort.
    - apply safeExec_result_state.
      exists tt. exact I.
Qed.

Lemma proof_of_split_rec_derive_low_level_spec_aux_by_low_level_spec : split_rec_derive_low_level_spec_aux_by_low_level_spec.
Proof.
  pre_process.
  Intros q_pre_v'. Intros p_pre_v'.
  apply safeExec_bind in H as (X_low_level_spec & Hsafe_first & Hsafe_cont).
  Exists l_low_level_spec_aux. Exists l1_low_level_spec_aux. Exists l2_low_level_spec_aux.
  Exists X_low_level_spec.
  Exists q_pre_v'. Exists p_pre_v'.
  split_pure_spatial.
  + cancel (sll x_pre l_low_level_spec_aux).
    cancel ((p_pre) # Ptr |-> p_pre_v').
    cancel (sll p_pre_v' l1_low_level_spec_aux).
    cancel ((q_pre) # Ptr |-> q_pre_v').
    cancel (sll q_pre_v' l2_low_level_spec_aux).
    apply derivable1_wand_sepcon_adjoint.
    Intros q_callee_v_2. Intros p_callee_v_2. Intros s1_2. Intros s2_2.
    Exists q_callee_v_2. Exists p_callee_v_2. Exists s1_2. Exists s2_2.
    repeat (split_pure_spatial || split_pures).
    - cancel ((p_pre) # Ptr |-> p_callee_v_2).
      cancel (sll p_callee_v_2 s1_2).
      cancel ((q_pre) # Ptr |-> q_callee_v_2).
      cancel (sll q_callee_v_2 s2_2).
    - dump_pre_spatial.
      unfold applyf, maketuple.
      apply (Hsafe_cont ATrue (s1_2, s2_2)).
      exact H.
  + dump_pre_spatial. exact Hsafe_first.
Qed.

Lemma proof_of_split_rec_derive_high_level_spec_by_low_level_spec : split_rec_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  Intros q_pre_v'. Intros p_pre_v'.
  Exists l_high_level_spec. Exists (@nil Z). Exists (@nil Z).
  Exists X_high_level_spec.
  Exists q_pre_v'. Exists p_pre_v'.
  split_pure_spatial.
  + cancel (sll x_pre l_high_level_spec).
    cancel ((p_pre) # Ptr |-> p_pre_v').
    cancel (sll p_pre_v' (@nil Z)).
    cancel ((q_pre) # Ptr |-> q_pre_v').
    cancel (sll q_pre_v' (@nil Z)).
    apply derivable1_wand_sepcon_adjoint.
    Intros q_callee_v_2. Intros p_callee_v_2. Intros s1_2. Intros s2_2.
    Exists q_callee_v_2. Exists p_callee_v_2. Exists s1_2. Exists s2_2.
    repeat (split_pure_spatial || split_pures).
    - cancel ((p_pre) # Ptr |-> p_callee_v_2).
      cancel (sll p_callee_v_2 s1_2).
      cancel ((q_pre) # Ptr |-> q_callee_v_2).
      cancel (sll q_callee_v_2 s2_2).
    - dump_pre_spatial. exact H0.
  + dump_pre_spatial.
    unfold split_rel in H.
    unfold split_rec_rel.
    exact H.
Qed. 
