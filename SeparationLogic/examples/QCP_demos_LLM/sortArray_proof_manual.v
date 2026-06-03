Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.micromega.Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import sortArray_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import ListNotations.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import sortArray_lib.
Local Open Scope sac.

Lemma proof_of_sortArray_entail_wit_1 : sortArray_entail_wit_1.
Proof.
	pre_process.
	Exists (sublist 0 1 l).
	Exists l.
	Exists (sublist 0 1 l).
	Exists (sublist 1 numsSize_pre l).
	split_pure_spatial.
	- cancel.
	- split_pures.
		+ dump_pre_spatial. exact H0.
		+ dump_pre_spatial. exact H1.
		+ dump_pre_spatial.
			rewrite <- (sublist_self l numsSize_pre) at 1 by lia.
			rewrite (sublist_split 0 numsSize_pre 1 l) by lia.
			reflexivity.
		+ dump_pre_spatial.
			rewrite <- (sublist_self l numsSize_pre) at 1 by lia.
			rewrite (sublist_split 0 numsSize_pre 1 l) by lia.
			reflexivity.
		+ dump_pre_spatial. symmetry. exact H.
		+ dump_pre_spatial.
			rewrite Zlength_sublist by lia.
			lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. exact H0.
		+ dump_pre_spatial. apply Permutation_refl.
		+ dump_pre_spatial.
			change 1 with (0 + 1).
			rewrite (sublist_single 0 0 l) by lia.
			simpl.
			exact I.
Qed.

Lemma proof_of_sortArray_entail_wit_2 : sortArray_entail_wit_2.
Proof.
	pre_process.
	destruct l2_2 as [|z l_tail].
	- rewrite H2 in H4.
		rewrite Zlength_app in H4.
		rewrite Zlength_nil in H4.
		rewrite <- H5 in H4.
		lia.
	- assert (Hlen_l0 : Zlength l0_2 = i).
		{
			pose proof (Permutation_length H8) as Hperm.
			apply f_equal with (f := Z.of_nat) in Hperm.
			repeat rewrite <- Zlength_correct in Hperm.
			rewrite <- H5 in Hperm.
			symmetry.
			exact Hperm.
		}
		assert (Hz : Znth i l3 0 = z).
		{
			rewrite H3.
			rewrite app_Znth2 by (rewrite Hlen_l0; lia).
			rewrite Hlen_l0.
			replace (i - i) with 0 by lia.
			rewrite Znth0_cons.
			reflexivity.
		}
		assert (Hz0 : Znth i l0_2 z = z).
		{
			unfold Znth.
			apply nth_overflow.
			rewrite <- Hlen_l0.
			rewrite Zlength_correct.
			rewrite Nat2Z.id.
			lia.
		}
		Exists l3.
		Exists l0_2.
		Exists nil.
		Exists l0_2.
		Exists l1_2.
		Exists l_tail.
		split_pure_spatial.
		+ cancel ((returnSize_pre) # Int |-> numsSize_pre).
			cancel (IntArray.full nums_pre numsSize_pre l3).
		+ split_pures.
			* dump_pre_spatial. exact H0.
			* dump_pre_spatial. exact H1.
			* dump_pre_spatial. rewrite H2. rewrite Hz. reflexivity.
			* dump_pre_spatial. exact H4.
			* dump_pre_spatial. exact H5.
			* dump_pre_spatial. exact H6.
			* dump_pre_spatial. exact H.
			* dump_pre_spatial. exact H8.
			* dump_pre_spatial. exact H9.
			* dump_pre_spatial. rewrite app_nil_r. reflexivity.
			* dump_pre_spatial.
				replace (i - 1 + 1) with i by lia.
				rewrite Hz.
				rewrite H3.
				rewrite Hz0.
				rewrite <- app_assoc.
				simpl.
				reflexivity.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. rewrite Hlen_l0. lia.
			* dump_pre_spatial. lia.
			* dump_pre_spatial. lia.
Qed.

Lemma proof_of_sortArray_entail_wit_3 : sortArray_entail_wit_3.
Proof.
	pre_process.
	assert (Hjrange : 0 <= j < Zlength l2_2) by (rewrite <- H13; lia).
	assert (Hsplit : l2_2 = sublist 0 j l2_2 ++ [Znth j l2_2 key]).
	{
		rewrite <- (sublist_self l2_2 (j + 1)) at 1 by (rewrite H13; lia).
		rewrite (sublist_split 0 (j + 1) j l2_2) by lia.
		rewrite (sublist_single key j l2_2) by lia.
		simpl.
		reflexivity.
	}
	assert (Hj : Znth j l5_2 0 = Znth j l2_2 key).
	{
		pose proof (Zlength_nonneg l3_2) as Hl3_nonneg.
		rewrite H11.
		rewrite app_Znth1 by (rewrite Zlength_app; rewrite Zlength_cons; lia).
		rewrite app_Znth1 by exact Hjrange.
		rewrite (Znth_indep l2_2 j 0 key) by exact Hjrange.
		reflexivity.
	}
	assert (Hl0j : Znth j l0_2 key = Znth j l2_2 key).
	{
		rewrite H10.
		rewrite app_Znth1 by exact Hjrange.
		reflexivity.
	}
	assert (Hpref_len : Zlength (sublist 0 j l2_2 ++ [Znth j l2_2 key]) = j + 1).
	{
		rewrite Zlength_app.
		rewrite Zlength_cons.
		rewrite Zlength_nil.
		rewrite Zlength_sublist by lia.
		lia.
	}
	assert (Harray :
		replace_Znth (j + 1) (Znth j l5_2 0) l5_2 =
		(l2_2 ++ Znth j l2_2 key :: l3_2) ++ l4_2).
	{
		assert (Houter_nonneg : 0 <= j + 1) by lia.
		assert (Houter_lt : j + 1 < Zlength (l2_2 ++ Znth (j + 1) l0_2 key :: l3_2)).
		{
			pose proof (Zlength_nonneg l3_2) as Hl3_nonneg.
			rewrite Zlength_app.
			rewrite Zlength_cons.
			lia.
		}
		rewrite Hj.
		rewrite H11.
		rewrite (replace_Znth_app_l (j + 1) (Znth j l2_2 key)
			(l2_2 ++ Znth (j + 1) l0_2 key :: l3_2) l4_2 Houter_nonneg Houter_lt).
		rewrite (replace_Znth_app_r (j + 1) (Znth j l2_2 key)
			l2_2 (Znth (j + 1) l0_2 key :: l3_2)) by (rewrite H13; lia).
		rewrite (replace_Znth_nothing (j + 1) l2_2 (Znth j l2_2 key)) by (rewrite H13; lia).
		replace (j + 1 - Zlength l2_2) with 0 by (rewrite H13; lia).
		unfold replace_Znth.
		simpl.
		reflexivity.
	}
	Exists (replace_Znth (j + 1) (Znth j l5_2 0) l5_2).
	Exists (sublist 0 j l2_2).
	Exists (Znth j l2_2 key :: l3_2).
	Exists l0_2.
	Exists l1_2.
	Exists l4_2.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre (replace_Znth (j + 1) (Znth j l5_2 0) l5_2)).
		cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
		+ dump_pre_spatial. exact H1.
		+ dump_pre_spatial. exact H2.
		+ dump_pre_spatial. exact H3.
		+ dump_pre_spatial. exact H4.
		+ dump_pre_spatial. exact H5.
		+ dump_pre_spatial. exact H6.
		+ dump_pre_spatial. exact H7.
		+ dump_pre_spatial. exact H8.
		+ dump_pre_spatial. exact H9.
		+ dump_pre_spatial.
			rewrite H10.
			rewrite Hsplit at 1.
			replace ((sublist 0 j l2_2 ++ [Znth j l2_2 key]) ++ l3_2)
				with (sublist 0 j l2_2 ++ [Znth j l2_2 key] ++ l3_2)
				by (rewrite app_assoc; reflexivity).
			simpl.
			reflexivity.
		+ dump_pre_spatial.
			replace (j - 1 + 1) with j by lia.
			rewrite Hl0j.
			rewrite Harray.
			rewrite Hsplit at 1.
			replace (((sublist 0 j l2_2 ++ [Znth j l2_2 key]) ++ Znth j l2_2 key :: l3_2) ++ l4_2)
				with ((sublist 0 j l2_2 ++ [Znth j l2_2 key] ++ Znth j l2_2 key :: l3_2) ++ l4_2)
				by (rewrite app_assoc; reflexivity).
			simpl.
			reflexivity.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial.
			rewrite Zlength_sublist by lia.
			lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial. lia.
		+ dump_pre_spatial.
			assert (Hgt : key < Znth j l2_2 key) by (rewrite <- Hj; lia).
			simpl.
			split; [exact Hgt | exact H16].
Qed.

Lemma proof_of_sortArray_entail_wit_4_1 : sortArray_entail_wit_4_1.
Proof.
	pre_process.
	destruct l2_2 as [|z l2] using rev_ind.
	- rewrite Zlength_nil in H13.
	  lia.
	- assert (Hj : j = Zlength l2).
	  {
	    rewrite Zlength_app in H13.
	    rewrite Zlength_cons in H13.
	    rewrite Zlength_nil in H13.
	    simpl in H13.
	    lia.
	  }
	  assert (Hznth : Znth j l5 0 = z).
	  {
	    rewrite H11.
	    rewrite app_Znth1.
	    2: {
	      pose proof (Zlength_nonneg l3_2) as Hl3.
	      rewrite Zlength_app.
	      rewrite Zlength_cons.
	      rewrite Zlength_app.
	      rewrite Zlength_cons.
	      rewrite Zlength_nil.
	      simpl.
	      rewrite Hj.
	      lia.
	    }
	    rewrite app_Znth1.
	    2: {
	      rewrite Zlength_app.
	      rewrite Zlength_cons.
	      rewrite Zlength_nil.
	      simpl.
	      rewrite Hj.
	      lia.
	    }
	    rewrite app_Znth2 by (rewrite Hj; lia).
	    replace (j - Zlength l2) with 0 by (rewrite Hj; lia).
	    simpl.
	    reflexivity.
	  }
	  assert (Hz : z <= key).
	  {
	    rewrite Hznth in H.
	    lia.
	  }
	  assert (Harray : replace_Znth (j + 1) key l5 = (((l2 ++ [z]) ++ key :: l3_2) ++ l4)).
	  {
	    assert (Houter_nonneg : 0 <= j + 1) by lia.
	    assert (Houter_lt : j + 1 < Zlength ((l2 ++ [z]) ++ Znth (j + 1) l0_2 key :: l3_2)).
	    {
	      pose proof (Zlength_nonneg l3_2) as Hl3_nonneg.
	      rewrite Zlength_app.
	      rewrite Zlength_cons.
	      lia.
	    }
	    rewrite H11.
	    rewrite (replace_Znth_app_l (j + 1) key
	      ((l2 ++ [z]) ++ Znth (j + 1) l0_2 key :: l3_2) l4 Houter_nonneg Houter_lt).
	    rewrite (replace_Znth_app_r (j + 1) key (l2 ++ [z]) (Znth (j + 1) l0_2 key :: l3_2)) by (rewrite H13; lia).
	    rewrite replace_Znth_nothing by (rewrite H13; lia).
	    replace (j + 1 - Zlength (l2 ++ [z])) with 0 by (rewrite H13; lia).
	    unfold replace_Znth.
	    simpl.
	    rewrite <- app_assoc.
	    reflexivity.
	  }
	  Exists ((l2 ++ [z]) ++ key :: l3_2).
	  Exists ((((l2 ++ [z]) ++ key :: l3_2) ++ l4)).
	  Exists (l1_2 ++ [key]).
	  Exists l4.
	  split_pure_spatial.
	  + rewrite Harray.
	    cancel (IntArray.full nums_pre numsSize_pre ((((l2 ++ [z]) ++ key :: l3_2) ++ l4))).
	    cancel ((returnSize_pre) # Int |-> numsSize_pre).
	  + split_pures.
	    * dump_pre_spatial. exact H1.
	    * dump_pre_spatial. exact H2.
	    * dump_pre_spatial.
	      rewrite H3.
	      simpl.
	      rewrite <- app_assoc.
	      reflexivity.
	    * dump_pre_spatial. reflexivity.
	    * dump_pre_spatial. exact H4.
	    * dump_pre_spatial.
	      rewrite Zlength_app.
	      rewrite Zlength_cons.
	      rewrite Zlength_nil.
	      simpl.
	      lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial. lia.
	    * dump_pre_spatial.
	      transitivity (l0_2 ++ [key]).
	      { apply Permutation_app_tail. exact H8. }
	      { rewrite H10.
	        replace (((l2 ++ [z]) ++ l3_2) ++ [key]) with ((l2 ++ [z]) ++ (l3_2 ++ [key])) by (rewrite app_assoc; reflexivity).
	        apply Permutation_app_head.
	        apply Permutation_sym.
	        apply Permutation_cons_append. }
	    * dump_pre_spatial.
	      assert (Hinc_old : increasing (l2 ++ z :: l3_2)).
	      {
	        replace (l2 ++ z :: l3_2) with ((l2 ++ [z]) ++ l3_2) by (simpl; rewrite <- app_assoc; reflexivity).
	        rewrite <- H10.
	        exact H9.
	      }
	      replace (((l2 ++ [z]) ++ key :: l3_2)) with (l2 ++ z :: key :: l3_2) by (simpl; rewrite <- app_assoc; reflexivity).
	      eapply increasing_middle.
	      { exact Hinc_old. }
	      { exact Hz. }
	      { exact H16. }
Qed.

Lemma proof_of_sortArray_entail_wit_4_2 : sortArray_entail_wit_4_2.
Proof.
	pre_process.
	assert (Hj0 : j + 1 = 0) by lia.
	assert (Hl2 : Zlength l2_2 = 0) by (rewrite <- H12; lia).
	apply Zlength_nil_inv in Hl2.
	subst l2_2.
	assert (Hl0 : l0_2 = l3_2) by (rewrite H9; simpl; reflexivity).
	assert (Harray : replace_Znth (j + 1) key l5 = (key :: l0_2) ++ l4).
	{
		rewrite Hj0.
		rewrite H10.
		rewrite Hl0.
		unfold replace_Znth.
		simpl.
		reflexivity.
	}
	Exists (key :: l0_2).
	Exists ((key :: l0_2) ++ l4).
	Exists (l1_2 ++ [key]).
	Exists l4.
	split_pure_spatial.
	- rewrite Harray.
	  cancel (IntArray.full nums_pre numsSize_pre ((key :: l0_2) ++ l4)).
	  cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
	  + dump_pre_spatial. exact H0.
	  + dump_pre_spatial. exact H1.
	  + dump_pre_spatial. rewrite H2. simpl. rewrite <- app_assoc. reflexivity.
	  + dump_pre_spatial. reflexivity.
	  + dump_pre_spatial. exact H3.
	  + dump_pre_spatial.
	    rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil. simpl. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial. lia.
	  + dump_pre_spatial.
	    transitivity (l0_2 ++ [key]).
	    * apply Permutation_app_tail. exact H7.
	    * apply Permutation_sym.
	      apply Permutation_cons_append.
	  + dump_pre_spatial.
	    rewrite <- Hl0 in H15.
	    destruct l0_2 as [|x xs].
	    * simpl. exact I.
	    * simpl in H8, H15.
	      destruct H15 as [Hkx _].
	      split; [lia | exact H8].
Qed.

Lemma proof_of_sortArray_return_wit_1 : sortArray_return_wit_1.
Proof.
	pre_process.
	assert (Hi : i = numsSize_pre) by lia.
	subst i.
	assert (Hlen1 : Zlength l1_2 = numsSize_pre) by lia.
	assert (Hl2 : Zlength l2 = 0).
	{
		rewrite H2 in H4.
		rewrite Zlength_app in H4.
		rewrite Hlen1 in H4.
		lia.
	}
	apply Zlength_nil_inv in Hl2.
	subst l2.
	assert (Hlen0 : Zlength l0 = numsSize_pre).
	{
		pose proof (Permutation_length H8) as Hperm.
		apply f_equal with (f := Z.of_nat) in Hperm.
		repeat rewrite <- Zlength_correct in Hperm.
		rewrite Hlen1 in Hperm.
		symmetry.
		exact Hperm.
	}
	subst l3.
	rewrite app_nil_r.
	Exists l0.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l0).
		cancel ((returnSize_pre) # Int |-> numsSize_pre).
	- split_pures.
		+ dump_pre_spatial.
			rewrite H2.
			rewrite app_nil_r.
			exact H8.
		+ dump_pre_spatial. exact H9.
		+ dump_pre_spatial. exact Hlen0.
Qed.

