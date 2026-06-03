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
From SimpleC.EE.QCP_demos_LLM.simple_arith Require Import abs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
	intros x_pre.
	repeat (split_pure_spatial || split_pures).
	- Intros_p Hge.
		Intros_p Hmin.
		Intros_p Hmax.
		cancel.
	-
		Intros_p Hge.
		Intros_p Hmin.
		Intros_p Hmax.
		dump_pre_spatial.
		change (x_pre = Z.abs x_pre).
		symmetry.
		apply Z.abs_eq.
		lia.
Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
	intros x_pre.
	repeat (split_pure_spatial || split_pures).
	- Intros_p Hlt.
		Intros_p Hmin.
		Intros_p Hmax.
		cancel.
	-
		Intros_p Hlt.
		Intros_p Hmin.
		Intros_p Hmax.
		dump_pre_spatial.
		change (- x_pre = Z.abs x_pre).
		symmetry.
		apply Z.abs_neq.
		lia.
Qed.
