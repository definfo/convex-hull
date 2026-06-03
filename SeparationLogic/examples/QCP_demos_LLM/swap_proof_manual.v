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
From SimpleC.EE.QCP_demos_LLM Require Import swap_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import swap_lib.
Local Open Scope sac.

Lemma proof_of_swap_entail_wit_1 : swap_entail_wit_1.
Proof.
	pre_process.
	destruct para_all as [x | x y].
	- Left.
		Exists x.
		simpl.
		split_pure_spatial.
		+ Intros_p Hpxeq.
		  cancel (px_pre # Int |-> x).
		+ split_pures.
		  * Intros_p Hpxeq1.
		    dump_pre_spatial.
		    exact Hpxeq1.
		  * Intros_p Hpxeq2.
		    dump_pre_spatial.
		    exact Hpxeq2.
		  * dump_pre_spatial.
		    reflexivity.
	- Right.
		Exists y.
		Exists x.
		simpl.
		split_pure_spatial.
		+ cancel (px_pre # Int |-> x).
		  cancel (py_pre # Int |-> y).
		+ split_pures.
		  * dump_pre_spatial.
		    reflexivity.
Qed.

Lemma proof_of_swap_return_wit_1 : swap_return_wit_1.
Proof.
	pre_process.
	subst py.
	subst para_all.
	simpl.
	split_pure_spatial.
	- cancel (px_pre # Int |-> x).
	- dump_pre_spatial.
	  exact H0.
Qed.

Lemma proof_of_swap_return_wit_2 : swap_return_wit_2.
Proof.
	pre_process.
	subst para_all.
	simpl.
	cancel (px_pre # Int |-> y).
	cancel (py_pre # Int |-> x).
Qed.

Lemma proof_of_swap_derive_eq_by_all : swap_derive_eq_by_all.
Proof.
	pre_process.
	Exists (swap_eq_para x_eq).
	simpl.
	asrt_complex_simpl.
	apply _derivable1_andp_intros.
	- dump_pre_spatial.
	  exact H.
	- cancel (px_pre # Int |-> x_eq).
	apply_sepcon_adjoint.
	elim_emp.
	Intros_p H0.
	subst py_pre.
	cancel (px_pre # Int |-> x_eq).
Qed.

Lemma proof_of_swap_derive_neq_by_all : swap_derive_neq_by_all.
Proof.
	pre_process.
	Exists (swap_neq_para x_neq y_neq).
	simpl.
	cancel (px_pre # Int |-> x_neq).
	cancel (py_pre # Int |-> y_neq).
	apply_sepcon_adjoint.
	elim_emp.
	cancel (px_pre # Int |-> y_neq).
	cancel (py_pre # Int |-> x_neq).
Qed.
