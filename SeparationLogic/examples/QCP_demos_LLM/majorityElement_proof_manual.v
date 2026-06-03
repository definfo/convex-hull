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
From SimpleC.EE.QCP_demos_LLM Require Import majorityElement_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import majorityElement_lib.
Local Open Scope sac.

Ltac grab H pat :=
	match goal with
	| H0 : pat |- _ => pose proof H0 as H
	end.

Lemma proof_of_majorityElement_entail_wit_1 : majorityElement_entail_wit_1.
Proof.
	pre_process.
	Exists x_2.
	Exists nil.
	Exists l.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite app_nil_l.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_nil.
	    reflexivity.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H0.
	  + dump_pre_spatial.
	    exact H1.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H.
	  + dump_pre_spatial.
	    apply majority_on_reduced_init.
	    exact H.
Qed.

Lemma proof_of_majorityElement_entail_wit_2_1 : majorityElement_entail_wit_2_1.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hlt : i < Zlength (l1_2 ++ l2_2)).
	{ rewrite <- H2. rewrite Hlen. exact H1. }
	destruct (app_Znth_suffix_cons l1_2 l2_2 i 0 H3 Hlt) as [a [rest [Hl2 Hz]]].
	rewrite H2 in H.
	rewrite Hz in H.
	subst a.
	unfold MajorityOnReduced in H11.
	destruct H11 as [Hvote Hmajor].
	Exists x_2.
	Exists ((l1_2 ++ candidate :: nil)%list).
	Exists rest.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite H2.
	    rewrite Hl2.
	    rewrite <- app_assoc.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite H3.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H6.
	  + dump_pre_spatial.
	    exact H7.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H10.
	  + dump_pre_spatial.
	    rewrite Hl2 in Hmajor.
	    apply majority_on_reduced_same; [lia | exact Hmajor].
Qed.

Lemma proof_of_majorityElement_entail_wit_2_2 : majorityElement_entail_wit_2_2.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hlt : i < Zlength (l1_2 ++ l2_2)).
	{ rewrite <- H2. rewrite Hlen. exact H1. }
	destruct (app_Znth_suffix_cons l1_2 l2_2 i 0 H3 Hlt) as [a [rest [Hl2 Hz]]].
	rewrite H2 in H.
	rewrite Hz in H.
	unfold MajorityOnReduced in H11.
	destruct H11 as [Hvote Hmajor].
	assert (0 < vote) by lia.
	Exists x_2.
	Exists ((l1_2 ++ a :: nil)%list).
	Exists rest.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite H2.
	    rewrite Hl2.
	    rewrite <- app_assoc.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite H3.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H6.
	  + dump_pre_spatial.
	    exact H7.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H10.
	  + dump_pre_spatial.
	    rewrite Hl2 in Hmajor.
	    apply majority_on_reduced_cancel with (a := a); [lia | exact H | exact Hmajor].
Qed.

Lemma proof_of_majorityElement_entail_wit_2_3 : majorityElement_entail_wit_2_3.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	assert (Hlt : i < Zlength (l1_2 ++ l2_2)).
	{ rewrite <- H1. rewrite Hlen. exact H0. }
	destruct (app_Znth_suffix_cons l1_2 l2_2 i 0 H2 Hlt) as [a [rest [Hl2 Hz]]].
	assert (Hzl : Znth i l 0 = a).
	{ rewrite H1. exact Hz. }
	unfold MajorityOnReduced in H10.
	destruct H10 as [Hvote Hmajor].
	Exists x_2.
	Exists ((l1_2 ++ a :: nil)%list).
	Exists rest.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- split_pures.
	  + dump_pre_spatial.
	    rewrite H1.
	    rewrite Hl2.
	    rewrite <- app_assoc.
	    reflexivity.
	  + dump_pre_spatial.
	    rewrite Zlength_app, Zlength_cons, Zlength_nil.
	    rewrite H2.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H5.
	  + dump_pre_spatial.
	    exact H6.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    lia.
	  + dump_pre_spatial.
	    exact H9.
	  + dump_pre_spatial.
	    rewrite Hl2 in Hmajor.
	    rewrite <- Hzl in Hmajor.
	    rewrite H.
	    rewrite H in Hmajor.
	    apply (majority_on_reduced_reset x_2 candidate (Znth i l 0) rest).
	    exact Hmajor.
Qed.

Lemma proof_of_majorityElement_return_wit_1 : majorityElement_return_wit_1.
Proof.
	pre_process.
	prop_apply IntArray.full_Zlength.
	Intros_p Hlen.
	split_pure_spatial.
	- cancel (IntArray.full nums_pre numsSize_pre l).
	- dump_pre_spatial.
	  unfold MajorityOnReduced in H9.
	  destruct H9 as [Hvote Hmajor].
	  assert (Hi : i = numsSize_pre) by lia.
	  assert (Hl1len : Zlength l1 = numsSize_pre) by lia.
	  assert (Hl2len : Zlength l2 = 0).
	  { rewrite H0 in Hlen.
	    rewrite Zlength_app in Hlen.
	    rewrite Hl1len in Hlen.
	    lia. }
	  apply Zlength_nil_inv in Hl2len.
	  subst l2.
	  rewrite app_nil_r in H0.
	  subst l.
	  rewrite app_nil_r in Hmajor.
	  pose proof (majority_of_repeated_eq x candidate vote Hvote Hmajor) as Hxc.
	  subst candidate.
	  exact H8.
Qed.

