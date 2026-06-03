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
From SimpleC.EE.QCP_demos_LLM Require Import sll_split_while_goal.
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

Lemma proof_of_split_while_entail_wit_2 : split_while_entail_wit_2.
Proof.
	pre_process.
	Exists q_v_2.
	Exists p_v_2.
	sep_apply_l_atomic (sll_not_zero x l_2).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros x_next x_data l1_new.
		Exists x_next.
		Exists x_data.
		Exists l1_new.
		Exists l_2.
		Exists l1_2.
		Exists l2_2.
		repeat split_pure_spatial.
		+ cancel (&(x # "list" ->ₛ "data") # Int |-> x_data).
			cancel (&(x # "list" ->ₛ "next") # Ptr |-> x_next).
			cancel (sll x_next l1_new).
			cancel (p_pre # Ptr |-> p_v_2).
			cancel (sll p_v_2 l1_2).
			cancel (q_pre # Ptr |-> q_v_2).
			cancel (sll q_v_2 l2_2).
		+ repeat split_pures.
			* dump_pre_spatial.
			  exact H0.
			* dump_pre_spatial.
			  exact H.
			* dump_pre_spatial.
			  exact H1.
Qed.

Lemma proof_of_split_while_entail_wit_3 : split_while_entail_wit_3.
Proof.
	pre_process.
	Exists q_v_2.
	Exists p_v_2.
	Exists x.
	Exists l_2.
	Exists l1_new.
	Exists l2_2.
	Exists x_data_2.
	Exists l1_2.
	repeat split_pure_spatial.
	- cancel (p_pre # Ptr |-> x).
		cancel (&(x # "list" ->ₛ "data") # Int |-> x_data_2).
		cancel (&(x # "list" ->ₛ "next") # Ptr |-> p_v_2).
		cancel (sll p_v_2 l1_2).
		cancel (sll x_next l1_new).
		cancel (q_pre # Ptr |-> q_v_2).
		cancel (sll q_v_2 l2_2).
		sep_apply store_ptr_undef_store_ptr.
		cancel (&( "t") # Ptr |->_).
	- repeat split_pures.
		+ dump_pre_spatial.
		  rewrite H1 in H.
		  unfold split_rec_rel in *.
		  apply split_rel_eval_xnotnil in H.
		  exact H.
		+ dump_pre_spatial.
		  exact H1.
		+ dump_pre_spatial.
		  exact H0.
Qed.

Lemma proof_of_split_while_entail_wit_4 : split_while_entail_wit_4.
Proof.
	pre_process.
	sep_apply_l_atomic (sll_not_zero x l_new).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros x_next x_data_2 l1_new.
		Exists x_next.
		Exists q_v_2.
		Exists p_v_2.
		Exists x_data_2.
		Exists l1_new.
		Exists l_new.
		Exists l2_2.
		Exists x_data_3.
		Exists l1_2.
		repeat split_pure_spatial.
		+ cancel (&(x # "list" ->ₛ "data") # Int |-> x_data_2).
		  cancel (&(x # "list" ->ₛ "next") # Ptr |-> x_next).
		  cancel (sll x_next l1_new).
		  cancel (q_pre # Ptr |-> q_v_2).
		  cancel (sll q_v_2 l2_2).
		  cancel (p_pre # Ptr |-> p_v_2).
		  simpl sll.
          Exists p_v_next.
		  split_pure_spatial.
		  * cancel.
		    cancel.
          * dump_pre_spatial.
		    exact H2.
		+ repeat split_pures.
		  * dump_pre_spatial.
		    exact H0.
		  * dump_pre_spatial.
		    exact H.
		  * dump_pre_spatial.
		    exact H3.
Qed.

Lemma proof_of_split_while_entail_wit_5 : split_while_entail_wit_5.
Proof.
	pre_process.
	Exists p_v_2.
	Exists q_v_2.
	Exists x.
	Exists l_2.
	Exists l1_new.
	Exists x_data_2.
	Exists l1_2.
	Exists x_data_3.
	Exists l2_2.
	repeat split_pure_spatial.
	- cancel (&(x # "list" ->ₛ "data") # Int |-> x_data_3).
		cancel (p_pre # Ptr |-> p_v_2).
		cancel (sll p_v_2 (x_data_2 :: l1_2)).
		cancel (q_pre # Ptr |-> x).
		cancel (sll q_v_2 l2_2).
		cancel (&(x # "list" ->ₛ "next") # Ptr |-> q_v_2).
		cancel (sll x_next l1_new).
		apply store_ptr_undef_store_ptr.
	- repeat split_pures.
		+ dump_pre_spatial.
		  rewrite H1 in H.
		  unfold split_rec_rel in *.
		  erewrite (program_para_equiv (split_rec_rel_unfold)) in H.
		  unfold split_rec_rel_f in H.
		  rewrite bind_assoc in H.
		  change (safeExec ATrue
		    (x0 <- split_rec_rel' (l1_new, x_data_2 :: l1_2, x_data_3 :: l2_2) ;;
		     (fun p => z <- reversepair p ;; reversepair z) x0)
		    X_low_level_spec) in H.
		  setoid_rewrite bind_2_reversepair_equiv_Id in H.
		  rewrite bind_ret_right in H.
		  exact H.
		+ dump_pre_spatial.
		  exact H1.
		+ dump_pre_spatial.
		  exact H0.
Qed.

Lemma proof_of_split_while_entail_wit_6_1 : split_while_entail_wit_6_1.
Proof.
	pre_process.
	sep_apply_l_atomic (sll_zero x l_new).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros_p Hl.
		Exists q_v_2.
		Exists p_v_2.
		Exists nil.
		Exists (x_data :: l1_2).
		Exists l2_2.
		repeat split_pure_spatial.
		+ rewrite Hp.
		  cancel (q_pre # Ptr |-> q_v_2).
		  cancel (sll q_v_2 l2_2).
		  cancel (p_pre # Ptr |-> p_v_2).
		  simpl sll.
		  rewrite logic_equiv_coq_prop_andp_sepcon.
          Exists p_v_next.
          split_pure_spatial.
		  * cancel.
            cancel.
          * split_pures; dump_pre_spatial.
		    reflexivity.
            auto.
		+ dump_pre_spatial.
			rewrite Hl in H0.
			unfold split_rec_rel in *.
			erewrite (program_para_equiv (split_rec_rel_unfold)) in H0.
			unfold split_rec_rel_f in H0.
			unfold reversepair in H0.
			prog_nf in H0.
			unfold split_rec_rel'.
			erewrite (program_para_equiv (split_rec_rel_unfold)).
			unfold split_rec_rel_f.
			exact H0.
Qed.

Lemma proof_of_split_while_return_wit_1 : split_while_return_wit_1.
Proof.
	pre_process.
	sep_apply_l_atomic (sll_zero x l).
	- dump_pre_spatial.
		unfold NULL.
		lia.
	- Intros_p Hl.
		Exists q_v.
		Exists p_v.
		Exists l1.
		Exists l2.
		repeat split_pure_spatial.
		+ cancel (p_pre # Ptr |-> p_v).
			cancel (sll p_v l1).
			cancel (q_pre # Ptr |-> q_v).
			cancel (sll q_v l2).
		+ dump_pre_spatial.
			rewrite Hl in H0.
			unfold split_rec_rel in H0.
			erewrite (program_para_equiv (split_rec_rel_unfold)) in H0.
			unfold split_rec_rel_f in H0.
			unfold maketuple in H0.
			exact H0.
Qed.

