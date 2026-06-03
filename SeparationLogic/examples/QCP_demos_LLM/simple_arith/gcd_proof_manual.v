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
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import gcd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_gcd_return_wit_1 : gcd_return_wit_1.
Proof.
	intros y_pre x_pre retval.
	repeat (split_pure_spatial || split_pures).
	- Intros_p Hret.
		Intros_p Hy.
		Intros_p Hxmax.
		Intros_p Hymax.
		Intros_p Hymin.
		Intros_p Hxmin.
		Intros_p Hygt.
		cancel.
	-
		Intros_p Hret.
		Intros_p Hy.
		Intros_p Hxmax.
		Intros_p Hymax.
		Intros_p Hymin.
		Intros_p Hxmin.
		Intros_p Hygt.
		dump_pre_spatial.
		change (retval = Z.gcd x_pre y_pre).
		change (retval = Z.gcd y_pre (Z.rem x_pre y_pre)) in Hret.
		rewrite Z.gcd_comm in Hret.
		rewrite Z.gcd_rem in Hret by exact Hy.
		rewrite Z.gcd_comm.
		exact Hret.
Qed.

Lemma proof_of_gcd_return_wit_2 : gcd_return_wit_2.
Proof.
	intros y_pre x_pre retval.
	repeat (split_pure_spatial || split_pures).
	- Intros_p Hret.
		Intros_p Hy0.
		Intros_p Hxmax.
		Intros_p Hymax.
		Intros_p Hymin.
		Intros_p Hxmin.
		Intros_p Hygt.
		cancel.
	-
		Intros_p Hret.
		Intros_p Hy0.
		Intros_p Hxmax.
		Intros_p Hymax.
		Intros_p Hymin.
		Intros_p Hxmin.
		Intros_p Hygt.
		dump_pre_spatial.
		change (retval = Z.gcd x_pre y_pre).
		change (retval = Z.abs x_pre) in Hret.
		rewrite Hy0.
		rewrite Z.gcd_0_r.
		exact Hret.
Qed.

Lemma proof_of_gcd_partial_solve_wit_2_pure : gcd_partial_solve_wit_2_pure.
Proof.
	intros y_pre x_pre.
	repeat (split_pure_spatial || split_pures).
	- Intros_p Hy.
		Intros_p Hxmax.
		Intros_p Hymax.
		Intros_p Hymin.
		Intros_p Hxmin.
		Intros_p Hygt.
		dump_pre_spatial.
		exact Hygt.
	-
		Intros_p Hy.
		Intros_p Hxmax.
		Intros_p Hymax.
		Intros_p Hymin.
		Intros_p Hxmin.
		Intros_p Hygt.
		dump_pre_spatial.
		pose proof (Z.rem_bound_abs x_pre y_pre Hy) as Hrem.
		apply Z.abs_lt in Hrem.
		assert (Z.abs y_pre <= 2147483647) by (apply Z.abs_le; lia).
		lia.
Qed.
