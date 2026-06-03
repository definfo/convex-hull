Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
From SimpleC.EE.QCP_demos_LLM Require Import safeexecE_strategy_goal.
Import naive_C_Rules.
From SimpleC.EE.QCP_demos_LLM Require Import kmp_rel_lib.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Lemma safeexecE_strategy3_correctness : safeexecE_strategy3.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    eapply bind_equiv.
    + exact H.
    + exact H0.
Qed.

Lemma safeexecE_strategy4_correctness : safeexecE_strategy4.
  pre_process_default.
Qed.

Lemma safeexecE_strategy5_correctness : safeexecE_strategy5.
  pre_process_default.
Qed.

Lemma safeexecE_strategy1_correctness : safeexecE_strategy1.
  pre_process_default.
Qed.

Lemma safeexecE_strategy6_correctness : safeexecE_strategy6.
  pre_process_default.
Qed.

Lemma safeexecE_strategy7_correctness : safeexecE_strategy7.
  pre_process_default.
Qed.

Lemma safeexecE_strategy8_correctness : safeexecE_strategy8.
Proof.
  pre_process_default.
  Intros_p H0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    eapply safeExec_proequiv.
    + eapply MonadErrBasic.common_step_equiv.
      intro b.
      apply H0.
    + exact H.
Qed.

Lemma safeexecE_strategy9_correctness : safeexecE_strategy9.
Proof.
  pre_process_default.
  Intros_p H.
  Intros_p H0.
  Intros_p H1.
  Intros_p H2.
  Intros_p H3.
  subst a0 b0 c0 d0 e0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    reflexivity.
Qed.

Lemma safeexecE_strategy2_correctness : safeexecE_strategy2.
Proof.
  pre_process_default.
  Intros_p H0.
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    eapply safeExec_proequiv.
    + exact H0.
    + exact H.
Qed.
